/*
 * The Qubes OS Project, https://www.qubes-os.org
 *
 * Copyright (C) 2022  Demi Marie Obenour <demi@invisiblethingslab.com>
 *
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License
 * as published by the Free Software Foundation; either version 2
 * of the License, or (at your option) any later version.
 *
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
 * GNU General Public License for more details.
 *
 * You should have received a copy of the GNU General Public License
 * along with this program; if not, write to the Free Software
 * Foundation, Inc., 51 Franklin Street, Fifth Floor, Boston, MA  02110-1301, USA.
 */
#include <unistd.h>
#include <err.h>
#include <string.h>
#include <errno.h>
#include <stdlib.h>
#include <stdbool.h>
#include <fcntl.h>
#include <sys/wait.h>
#include <stdint.h>
#include <assert.h>
#include <limits.h>
#include <pthread.h>
#include <stdarg.h>

/* Workaround for C language misdesign: calling exit(3) more than once is undefined behavior,
 * so serialize all calls to it via err() or errx() */
static pthread_mutex_t exit_mutex = PTHREAD_MUTEX_INITIALIZER;

static __attribute__((noreturn, format(printf, 2, 3))) void fail(int status, const char *fmt, ...)
{
    va_list list;
    int i = errno;
    pthread_mutex_lock(&exit_mutex);
    va_start(list, fmt);
    errno = i;
    verr(status, fmt, list);
}

static __attribute__((noreturn, format(printf, 2, 3))) void failx(int status, const char *fmt, ...)
{
    va_list list;
    pthread_mutex_lock(&exit_mutex);
    va_start(list, fmt);
    verrx(status, fmt, list);
}

struct ValidatorState {
    uint16_t line_length;
    uint8_t last, tails_count;
};

static void validate_data(const uint8_t *p, size_t len, struct ValidatorState *state) {
    for (size_t i = 0; i < len; state->last = p[i], ++i) {
        const uint8_t untrusted_c = p[i];
        state->line_length++;
        // GnuPG cannot handle lines this long and will sign incorrect data
        if (state->line_length >= 19995)
            failx(1, "Line too long");
        if (state->tails_count) {
            uint8_t min, max;
            state->tails_count--;
            if (state->last == 0xE0)
                (void)(min = 0xA0), (void)(max = 0xBF);
            else if (state->last == 0xED)
                (void)(min = 0x80), (void)(max = 0x9F);
            else if (state->last == 0xF0)
                (void)(min = 0x90), (void)(max = 0xBF);
            else if (state->last == 0xF4)
                (void)(min = 0x80), (void)(max = 0x8F);
            else
                (void)(min = 0x80), (void)(max = 0xBF);
            if (untrusted_c < min || untrusted_c > max)
                failx(1, "data to be clearsigned must be valid UTF-8");
        } else {
            switch (untrusted_c) {
            case 0x00:
                failx(1, "NUL not allowed in data to be clearsigned");
            case 0x01 ... 0x08:
            case 0x0B ... 0x0C:
            case 0x0E ... 0x1F:
            case 0x7F:
                failx(1, "Control character %d not allowed in data to be clearsigned", untrusted_c);
            case 0x0A: // newline
                if (state->last == ' ' || state->last == '\t')
                    failx(1, "trailing whitespace in data to be clearsigned");
                state->line_length = 0;
                break;
            case 0x0D: // carriage return
                failx(1, "Carriage return (0x0D) not allowed");
            case 0x09: // tab
            case 0x20 ... 0x7E:
                break;
            case 0xC2 ... 0xDF:
                state->tails_count = 1;
                break;
            case 0xE0 ... 0xEF:
                state->tails_count = 2;
                break;
            case 0xF0 ... 0xF4:
                state->tails_count = 3;
                break;
            case 0x80 ... 0xBF:
                failx(1, "unexpected continuation byte 0x%X", untrusted_c);
            default:
                failx(1, "byte 0x%x cannot occur in UTF-8", untrusted_c);
            }
        }
    }
}
enum {
    ARGUMENT_LENGTH = 40,
    BAD_ARG_EXIT_STATUS = 16,
};

static void validate_argv0(const char *progname, bool *cleartext, const char **flag)
{
    if (!strcmp(progname, "qubes.GpgArmorSign"))
        (void)(*cleartext = false), *flag = "--armor";
    else if (!strcmp(progname, "qubes.GpgClearSign"))
        (void)(*cleartext = true), *flag = "--clearsign";
    else if (!strcmp(progname, "qubes.GpgBinarySign"))
        (void)(*cleartext = false), *flag = "--no-armor";
    else
        errx(BAD_ARG_EXIT_STATUS, "Must be invoked as qubes.GpgBinarySign, qubes.GpgArmorSign, or qubes.GpgClearSign, not %s.\n\
\n\
qubes.GpgBinarySign: create binary OpenPGP signatures\n\
qubes.GpgArmorSign: create ASCII-armored OpenPGP signatures\n\
qubes.GpgClearSign: create cleartext OpenPGP signatures", progname);
}

static char *get_prog_name(char *str)
{
    char *const res = strrchr(str, '/');
    return res ? res + 1 : str;
}

static pid_t child_pid;

/* Kill GPG at exit, to avoid leaving it running */
static void kill_gpg(void)
{
    if (child_pid > 0) {
        int status;
        kill(child_pid, SIGTERM);
        waitpid(child_pid, &status, 0); /* ignore error */
    }
}

struct QubesGpgIoBuf {
    unsigned char buf[8192];
    size_t cursor, space, len;
    struct ValidatorState state;
    int read_fd, write_fd;
    bool validate, read_socket, write_socket, _pad;
};

static void *copy_data(void *raw_buf)
{
    struct QubesGpgIoBuf *buf = raw_buf;
    /* Your standard *nix copying loop, with optional validation */
    for (;;) {
        if (buf->read_fd != -1 && buf->space < buf->len) {
            size_t const to_read = buf->len - buf->space;
            uint8_t *const read_ptr = buf->buf + buf->space;
            ssize_t res = read(buf->read_fd, read_ptr, to_read);
            if (res > 0) {
                size_t const bytes_read = (size_t)res;
                assert(bytes_read <= to_read && "kernel wrote too many bytes");
                if (buf->validate)
                    validate_data(read_ptr, bytes_read, &buf->state);
                buf->space += bytes_read;
            } else if (res == -1 && errno != ECONNRESET) {
                if (errno != EINTR)
                    fail(1, "reading from fd %d", buf->write_fd);
            } else {
                if (res < -1)
                    abort();
                if (buf->validate && buf->state.last != '\n')
                    failx(1, "missing newline at EOF (last byte %02X)", buf->state.last);
                if (close(buf->read_fd))
                    fail(1, "close(%d)", buf->read_fd);
                buf->read_fd = -1;
            }
        }

        if (buf->cursor < buf->space) {
            size_t const to_write = buf->space - buf->cursor;
            uint8_t *const write_ptr = buf->buf + buf->cursor;
            ssize_t const res = write(buf->write_fd, write_ptr, to_write);
            if (res <= 0)
                fail(1, "write(%d, %zu)", buf->write_fd, to_write);
            size_t const bytes_written = (size_t)res;
            assert(bytes_written <= to_write && "kernel read too many bytes");
            buf->cursor += bytes_written;
            if (buf->cursor == buf->len)
                buf->cursor = buf->space = 0;
        } else if (buf->read_fd == -1) {
            if (close(buf->write_fd))
                fail(1, "close(%d)", buf->write_fd);
            return NULL;
        }
    }
}

static void event_loop(int gpg_out_fd, int gpg_stdin_fd)
{
    int poll_res;
    static struct QubesGpgIoBuf in_buffer = {
        .cursor = 0,
        .space = 0,
        .len = sizeof in_buffer.buf,
        .state = { 0, '\n', 0 },
        .validate = true,
    };
    in_buffer.read_fd = 0;
    in_buffer.write_fd = gpg_stdin_fd;

    static struct QubesGpgIoBuf out_buffer = {
        .cursor = 0,
        .space = 0,
        .len = sizeof out_buffer.buf,
        .state = { 0, 0, 0 },
        .validate = false,
    };
    out_buffer.read_fd = gpg_out_fd;
    out_buffer.write_fd = 1;
    out_buffer.write_socket = out_buffer.write_fd == 1;
    in_buffer.read_socket = in_buffer.read_fd == 0;

    pthread_t thread_in;
    if ((poll_res = pthread_create(&thread_in, NULL, copy_data, &in_buffer))) {
        errno = poll_res > 0 ? poll_res : -poll_res;
        err(1, "pthread_create");
    }
    copy_data(&out_buffer);
    void *retval;
    if (pthread_join(thread_in, &retval) || retval)
        abort();
}

static void sigpipe_handler(int signal __attribute__((unused))) { return; }

int main(int argc, char **argv) {
    if (argc != 2)
        errx(BAD_ARG_EXIT_STATUS, "Wrong number of arguments (expected 2, got %d)", argc);

    /*
     * Argument already somewhat sanitized by qrexec: it cannot be passed
     * directly to GnuPG, but it *is* safe to print.
     */
    const char *const untrusted_arg = argv[1];
    const char *flag, *const progname = get_prog_name(argv[0]);
    bool cleartext;
    char untrusted_uid[ARGUMENT_LENGTH + 2] = { 0 };

    validate_argv0(progname, &cleartext, &flag);

    struct sigaction act = {
        .sa_handler = sigpipe_handler,
    };
    if (sigaction(SIGPIPE, &act, NULL))
        err(1, "sigaction");

    /*
     * Sanitize the fingerprint and convert it to uppercase.  The argument is
     * already somewhat sanitized by qrexec.  It cannot be passed directly
     * to GnuPG, but it *is* safe to print.
     */
    /* sanitize start */
    size_t const arg_len = strlen(untrusted_arg);

    /* Check that the length is correct */
    if (arg_len != ARGUMENT_LENGTH)
        errx(BAD_ARG_EXIT_STATUS, "Invalid length of service argument \"%s\" (expected %d, got %zu)",
             untrusted_arg, ARGUMENT_LENGTH, arg_len);

    /* Copy from the argument to the UID array */
    memcpy(untrusted_uid, untrusted_arg, arg_len);

    /*
     * Add a trailing ! to the key fingerprint.  This tells GnuPG to use the
     * exact key requested.  Also add the NUL terminator.
     */
    memcpy(untrusted_uid + arg_len, "!", 2);

    /* Sanitize and uppercase the user ID */
    for (size_t i = 0; i < arg_len; ++i) {
        switch (untrusted_uid[i]) {
        case '0' ... '9':
        case 'A' ... 'F':
            break;
        case 'a' ... 'f':
            untrusted_uid[i] -= 0x20;
            break;
        default:
            errx(BAD_ARG_EXIT_STATUS, "Invalid character '%c' at position %zu in argument \"%s\"",
                 untrusted_uid[i], i + 1, untrusted_arg);
        }
    }
    const char *const uid = untrusted_uid;
    /* sanitize end */

    /* Ensure that GnuPG's locale is reasonable */
    if (putenv("LC_ALL=C.UTF-8"))
        err(127, "putenv(\"LC_ALL=C.UTF-8\")");
    const char *const args[] = {
        "gpg",
        "--batch",
        "--no-tty",
        "--sign",
        "--disable-dirmngr",
        "--quiet",
        "--utf8-strings",
        "--display-charset=UTF-8",
        "--status-fd=2",
        "--with-colons",
        "--logger-file=/dev/null",
        /* Select detached or cleartext signatures */
        cleartext ? "--clearsign" : "--detach-sign",
        /* In case the user has --textmode or --no-textmode in gpg.conf */
        cleartext ? "--textmode" : "--no-textmode",
        "--local-user",
        uid,
        flag,
        NULL,
    };

    if (!cleartext)
        goto exec;

    if (atexit(kill_gpg))
        errx(1, "atexit() failed");

    int in_pipes[2], out_pipes[2];

    if (pipe2(in_pipes, O_CLOEXEC) || pipe2(out_pipes, O_CLOEXEC))
        err(126, "pipe");

    /* FORK HERE */
    switch ((child_pid = fork())) {
    case -1:
        err(126, "fork()");
    case 0:
        if (dup2(in_pipes[0], 0) != 0 || dup2(out_pipes[1], 1) != 1)
            err(126, "dup2");
        goto exec;
    default:
        if (close(in_pipes[0]) || close(out_pipes[1]))
            err(126, "close");
        event_loop(out_pipes[0], in_pipes[1]);
        siginfo_t info;
        if (waitid(P_PID, (unsigned int)child_pid, &info, WEXITED))
            err(126, "waitid");
        child_pid = 0;
        switch (info.si_code) {
        case CLD_EXITED:
            return info.si_status;
        case CLD_KILLED:
        case CLD_DUMPED:
            if (info.si_status > INT_MAX - 128)
                abort();
            return 128 + info.si_status;
        }
    }
    abort(); /* NOT REACHED */
exec:
    execvp(args[0], (char *const *)args);
    err(126, "execvp(%s)", args[0]);
}
