/**
 * PostgreSQL repository FFI for the Lean grpc_service example.
 *
 * This file intentionally returns only plain encoded strings to Lean. The
 * generated protobuf records and the gRPC server are constructed in Lean.
 */

#include "user_repository.h"

#include <lean/lean.h>
#include <pqxx/pqxx>

#include <cstdint>
#include <exception>
#include <iostream>
#include <sstream>
#include <string>
#include <vector>

extern "C" void lean_initialize_thread();

static void ensure_lean_thread() {
    thread_local bool initialized = (lean_initialize_thread(), true);
    (void)initialized;
}

static const char* CONNECTION_STRING =
    "host=localhost port=5433 dbname=userservice user=postgres";

namespace {

std::string base64_encode(const std::string& input) {
    static constexpr char alphabet[] =
        "ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/";

    std::string out;
    out.reserve(((input.size() + 2) / 3) * 4);

    for (std::size_t i = 0; i < input.size(); i += 3) {
        const std::uint32_t b0 = static_cast<unsigned char>(input[i]);
        const std::uint32_t b1 =
            (i + 1 < input.size()) ? static_cast<unsigned char>(input[i + 1]) : 0;
        const std::uint32_t b2 =
            (i + 2 < input.size()) ? static_cast<unsigned char>(input[i + 2]) : 0;
        const std::uint32_t value = (b0 << 16) | (b1 << 8) | b2;

        out.push_back(alphabet[(value >> 18) & 0x3f]);
        out.push_back(alphabet[(value >> 12) & 0x3f]);
        out.push_back((i + 1 < input.size()) ? alphabet[(value >> 6) & 0x3f] : '=');
        out.push_back((i + 2 < input.size()) ? alphabet[value & 0x3f] : '=');
    }

    return out.empty() ? "-" : out;
}

void add_token(std::vector<std::string>& tokens, const std::string& token) {
    tokens.push_back(token);
}

void add_string(std::vector<std::string>& tokens, const std::string& value) {
    add_token(tokens, base64_encode(value));
}

template <typename T>
void add_number(std::vector<std::string>& tokens, T value) {
    add_token(tokens, std::to_string(value));
}

void add_bool(std::vector<std::string>& tokens, bool value) {
    add_token(tokens, value ? "1" : "0");
}

void add_user(std::vector<std::string>& tokens, const pqxx::row& row) {
    add_number(tokens, row["id"].as<std::uint64_t>());
    add_string(tokens, row["username"].as<std::string>());
    add_string(tokens, row["email"].as<std::string>());
    add_number(tokens, row["status"].as<std::uint32_t>());
}

void add_empty_user(std::vector<std::string>& tokens) {
    add_number(tokens, 0);
    add_string(tokens, "");
    add_string(tokens, "");
    add_number(tokens, 0);
}

std::string join_tokens(const std::vector<std::string>& tokens) {
    std::ostringstream out;
    for (std::size_t i = 0; i < tokens.size(); ++i) {
        if (i != 0) {
            out << ' ';
        }
        out << tokens[i];
    }
    return out.str();
}

lean_object* ok_string(const std::string& value) {
    return lean_io_result_mk_ok(lean_mk_string(value.c_str()));
}

lean_object* error_string(const std::exception& e, const char* operation) {
    std::cerr << "[user_repository] " << operation << " error: " << e.what() << std::endl;
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(e.what())));
}

std::string lean_string_to_std(lean_object* value) {
    const char* data = lean_string_cstr(value);
    const std::size_t size = lean_string_size(value);
    return std::string(data, size == 0 ? 0 : size - 1);
}

}  // namespace

extern "C" {

lean_object* user_repository_get_user(std::uint64_t user_id) {
    ensure_lean_thread();
    try {
        pqxx::connection conn(CONNECTION_STRING);
        pqxx::work txn(conn);
        pqxx::result rows = txn.exec_params(
            "SELECT id, username, email, status FROM users WHERE id = $1",
            user_id);

        std::vector<std::string> tokens;
        if (rows.empty()) {
            add_bool(tokens, false);
            add_empty_user(tokens);
        } else {
            add_bool(tokens, true);
            add_user(tokens, rows[0]);
        }
        return ok_string(join_tokens(tokens));
    } catch (const std::exception& e) {
        return error_string(e, "GetUser");
    }
}

lean_object* user_repository_get_user_with_email_matches(std::uint64_t user_id) {
    ensure_lean_thread();
    try {
        pqxx::connection conn(CONNECTION_STRING);
        pqxx::work txn(conn);

        pqxx::result rows = txn.exec_params(
            "SELECT id, username, email, status FROM users WHERE id = $1",
            user_id);

        std::vector<std::string> tokens;
        if (rows.empty()) {
            add_bool(tokens, false);
            add_empty_user(tokens);
            add_number(tokens, 0);
            return ok_string(join_tokens(tokens));
        }

        const auto user = rows[0];
        const std::string user_email = user["email"].as<std::string>();
        pqxx::result matches = txn.exec_params(
            "SELECT id, username, email, status FROM users "
            "WHERE email = $1 AND id != $2 ORDER BY id",
            user_email, user_id);

        add_bool(tokens, true);
        add_user(tokens, user);
        add_number(tokens, matches.size());
        for (const auto& match : matches) {
            add_user(tokens, match);
        }
        return ok_string(join_tokens(tokens));
    } catch (const std::exception& e) {
        return error_string(e, "GetUserWithEmailMatches");
    }
}

lean_object* user_repository_create_user(lean_object* username, lean_object* email) {
    ensure_lean_thread();
    try {
        const std::string username_str = lean_string_to_std(username);
        const std::string email_str = lean_string_to_std(email);

        pqxx::connection conn(CONNECTION_STRING);
        pqxx::work txn(conn);

        std::vector<std::string> tokens;
        pqxx::result check = txn.exec_params(
            "SELECT 1 FROM users WHERE username = $1",
            username_str);
        if (!check.empty()) {
            add_bool(tokens, false);
            add_empty_user(tokens);
            add_string(tokens, "Username already exists");
            return ok_string(join_tokens(tokens));
        }

        check = txn.exec_params(
            "SELECT 1 FROM users WHERE email = $1",
            email_str);
        if (!check.empty()) {
            add_bool(tokens, false);
            add_empty_user(tokens);
            add_string(tokens, "Email already exists");
            return ok_string(join_tokens(tokens));
        }

        pqxx::result inserted = txn.exec_params(
            "INSERT INTO users (username, email, status) VALUES ($1, $2, 1) "
            "RETURNING id, username, email, status",
            username_str, email_str);
        txn.commit();

        add_bool(tokens, true);
        add_user(tokens, inserted[0]);
        add_string(tokens, "");
        return ok_string(join_tokens(tokens));
    } catch (const std::exception& e) {
        return error_string(e, "CreateUser");
    }
}

lean_object* user_repository_update_user(
    std::uint64_t user_id,
    std::uint8_t has_username, lean_object* username,
    std::uint8_t has_email, lean_object* email,
    std::uint8_t has_status, std::uint32_t status) {
    ensure_lean_thread();
    try {
        pqxx::connection conn(CONNECTION_STRING);
        pqxx::work txn(conn);

        pqxx::result existing = txn.exec_params(
            "SELECT id, username, email, status FROM users WHERE id = $1",
            user_id);

        std::vector<std::string> tokens;
        if (existing.empty()) {
            add_bool(tokens, false);
            add_empty_user(tokens);
            add_string(tokens, "User not found");
            return ok_string(join_tokens(tokens));
        }

        std::string query = "UPDATE users SET ";
        bool first = true;

        if (has_username) {
            const std::string username_str = lean_string_to_std(username);
            pqxx::result check = txn.exec_params(
                "SELECT 1 FROM users WHERE username = $1 AND id != $2",
                username_str, user_id);
            if (!check.empty()) {
                add_bool(tokens, false);
                add_empty_user(tokens);
                add_string(tokens, "Username already taken");
                return ok_string(join_tokens(tokens));
            }
            query += "username = " + txn.quote(username_str);
            first = false;
        }

        if (has_email) {
            const std::string email_str = lean_string_to_std(email);
            pqxx::result check = txn.exec_params(
                "SELECT 1 FROM users WHERE email = $1 AND id != $2",
                email_str, user_id);
            if (!check.empty()) {
                add_bool(tokens, false);
                add_empty_user(tokens);
                add_string(tokens, "Email already taken");
                return ok_string(join_tokens(tokens));
            }
            if (!first) {
                query += ", ";
            }
            query += "email = " + txn.quote(email_str);
            first = false;
        }

        if (has_status) {
            if (!first) {
                query += ", ";
            }
            query += "status = " + txn.quote(status);
            first = false;
        }

        add_bool(tokens, true);
        if (first) {
            add_user(tokens, existing[0]);
            add_string(tokens, "");
            return ok_string(join_tokens(tokens));
        }

        query += " WHERE id = " + txn.quote(user_id) +
                 " RETURNING id, username, email, status";
        pqxx::result updated = txn.exec(query);
        txn.commit();

        add_user(tokens, updated[0]);
        add_string(tokens, "");
        return ok_string(join_tokens(tokens));
    } catch (const std::exception& e) {
        return error_string(e, "UpdateUser");
    }
}

lean_object* user_repository_delete_user(std::uint64_t user_id) {
    ensure_lean_thread();
    try {
        pqxx::connection conn(CONNECTION_STRING);
        pqxx::work txn(conn);

        pqxx::result check = txn.exec_params(
            "SELECT 1 FROM users WHERE id = $1",
            user_id);

        std::vector<std::string> tokens;
        if (check.empty()) {
            add_bool(tokens, false);
            add_string(tokens, "User not found");
            return ok_string(join_tokens(tokens));
        }

        txn.exec_params("DELETE FROM users WHERE id = $1", user_id);
        txn.commit();

        add_bool(tokens, true);
        add_string(tokens, "");
        return ok_string(join_tokens(tokens));
    } catch (const std::exception& e) {
        return error_string(e, "DeleteUser");
    }
}

lean_object* user_repository_list_users(
    std::uint32_t limit, std::uint32_t offset,
    std::uint8_t has_status_filter, std::uint32_t status_filter) {
    ensure_lean_thread();
    try {
        pqxx::connection conn(CONNECTION_STRING);
        pqxx::work txn(conn);

        std::string base_query = "SELECT id, username, email, status FROM users";
        std::string count_query = "SELECT COUNT(*) FROM users";

        if (has_status_filter) {
            const std::string filter = " WHERE status = " + txn.quote(status_filter);
            base_query += filter;
            count_query += filter;
        }

        pqxx::result count_result = txn.exec(count_query);
        const std::uint32_t total_count = count_result[0][0].as<std::uint32_t>();

        base_query += " ORDER BY id";
        if (limit > 0) {
            base_query += " LIMIT " + std::to_string(limit);
        }
        if (offset > 0) {
            base_query += " OFFSET " + std::to_string(offset);
        }

        pqxx::result rows = txn.exec(base_query);
        std::vector<std::string> tokens;
        add_number(tokens, total_count);
        add_number(tokens, rows.size());
        for (const auto& row : rows) {
            add_user(tokens, row);
        }
        return ok_string(join_tokens(tokens));
    } catch (const std::exception& e) {
        return error_string(e, "ListUsers");
    }
}

}  // extern "C"
