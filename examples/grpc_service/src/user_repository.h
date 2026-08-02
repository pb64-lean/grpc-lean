#ifndef USER_REPOSITORY_H
#define USER_REPOSITORY_H

#include <lean/lean.h>
#include <stdint.h>

#ifdef __cplusplus
extern "C" {
#endif

/*
 * PostgreSQL repository FFI.
 *
 * These functions are called from Lean as IO functions and return Lean IO
 * results containing encoded String payloads. String fields inside those
 * payloads are base64 tokens; Lean decodes them and constructs generated
 * protobuf records.
 */

lean_object* user_repository_create_user(lean_object* username, lean_object* email);

lean_object* user_repository_get_user(uint64_t user_id);

lean_object* user_repository_get_user_with_email_matches(uint64_t user_id);

lean_object* user_repository_update_user(
    uint64_t user_id,
    uint8_t has_username, lean_object* username,
    uint8_t has_email, lean_object* email,
    uint8_t has_status, uint32_t status);

lean_object* user_repository_delete_user(uint64_t user_id);

lean_object* user_repository_list_users(
    uint32_t limit, uint32_t offset,
    uint8_t has_status_filter, uint32_t status_filter);

#ifdef __cplusplus
}
#endif

#endif
