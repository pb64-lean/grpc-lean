#ifndef LEAN_GRPC_POSIX_H
#define LEAN_GRPC_POSIX_H

#include <lean/lean.h>
#include <stddef.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Lean erases IO's world token at an extern call. */
LEAN_EXPORT lean_obj_res lean_grpc_posix_strerror_raw(uint32_t error);
LEAN_EXPORT lean_obj_res lean_grpc_posix_open_raw(
    b_lean_obj_arg path,
    uint32_t flags,
    uint32_t mode
);
LEAN_EXPORT lean_obj_res lean_grpc_posix_read_raw(
    uint32_t descriptor,
    uint32_t maximum_bytes
);
LEAN_EXPORT lean_obj_res lean_grpc_posix_close_raw(uint32_t descriptor);
LEAN_EXPORT lean_obj_res lean_grpc_posix_fstat_raw(uint32_t descriptor);

#ifdef __cplusplus
}
#endif

#endif
