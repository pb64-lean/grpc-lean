/*
 * Thin single-operation POSIX adapters for descriptor-owned file reads.
 * Every declaration is one syscall wide: validation, retries, sequencing,
 * classification, and cleanup live in Lean.
 */
#define _GNU_SOURCE
#define _DARWIN_C_SOURCE
#define _POSIX_C_SOURCE 200809L

#include "grpc_posix.h"

#include <errno.h>
#include <fcntl.h>
#include <stdint.h>
#include <string.h>
#include <sys/stat.h>
#include <sys/types.h>
#include <unistd.h>

_Static_assert(sizeof(int) == sizeof(int32_t), "Lean Int32 requires a 32-bit int");
/* Keep the hard-coded Lean ABI constants tied to each supported system header. */
#ifdef __APPLE__
_Static_assert(O_NONBLOCK == 0x00000004, "Darwin O_NONBLOCK ABI changed");
_Static_assert(O_CLOEXEC == 0x01000000, "Darwin O_CLOEXEC ABI changed");
#elif defined(__linux__)
_Static_assert(O_NONBLOCK == 0x00000800, "Linux O_NONBLOCK ABI changed");
_Static_assert(O_CLOEXEC == 0x00080000, "Linux O_CLOEXEC ABI changed");
#endif

static lean_obj_res raw_except_error(int error_number) {
    lean_object *result = lean_alloc_ctor(0, 1, 0);
    lean_ctor_set(result, 0, lean_box_uint32((uint32_t)error_number));
    return result;
}

static lean_obj_res raw_except_ok(lean_obj_arg value) {
    lean_object *result = lean_alloc_ctor(1, 1, 0);
    lean_ctor_set(result, 0, value);
    return result;
}

static lean_obj_res raw_sys_error(int error_number) {
    return lean_io_result_mk_ok(raw_except_error(error_number));
}

static lean_obj_res raw_sys_ok(lean_obj_arg value) {
    return lean_io_result_mk_ok(raw_except_ok(value));
}

LEAN_EXPORT lean_obj_res lean_grpc_posix_strerror_raw(uint32_t error) {
    return lean_mk_string(strerror((int32_t)error));
}

LEAN_EXPORT lean_obj_res lean_grpc_posix_open_raw(
    b_lean_obj_arg path,
    uint32_t flags,
    uint32_t mode
) {
    int result = open(
        lean_string_cstr(path),
        (int)(int32_t)flags,
        (mode_t)mode
    );
    return result == -1
        ? raw_sys_error(errno)
        : raw_sys_ok(lean_box_uint32((uint32_t)result));
}

LEAN_EXPORT lean_obj_res lean_grpc_posix_read_raw(
    uint32_t descriptor,
    uint32_t maximum_bytes
) {
    size_t capacity = (size_t)maximum_bytes;
    lean_object *bytes = lean_alloc_sarray(1, capacity, capacity);
    ssize_t result = read((int32_t)descriptor, lean_sarray_cptr(bytes), capacity);
    if (result == -1) {
        int error_number = errno;
        lean_dec(bytes);
        return raw_sys_error(error_number);
    }
    lean_sarray_set_size(bytes, (size_t)result);
    return raw_sys_ok(bytes);
}

LEAN_EXPORT lean_obj_res lean_grpc_posix_close_raw(uint32_t descriptor) {
    int result = close((int32_t)descriptor);
    return result == -1 ? raw_sys_error(errno) : raw_sys_ok(lean_box(0));
}

LEAN_EXPORT lean_obj_res lean_grpc_posix_fstat_raw(uint32_t descriptor) {
    struct stat information;
    int result = fstat((int32_t)descriptor, &information);
    if (result == -1) {
        return raw_sys_error(errno);
    }
    lean_object *fields = lean_alloc_array(3, 3);
    lean_array_set_core(fields, 0, lean_box_uint64((uint64_t)information.st_mode));
    lean_array_set_core(fields, 1, lean_box_uint64((uint64_t)information.st_nlink));
    lean_array_set_core(fields, 2, lean_box_uint64((uint64_t)information.st_size));
    return raw_sys_ok(fields);
}
