#!/usr/bin/env bash
set -euo pipefail

server="${1:?missing note_server path}"
proto="${2:?missing note.proto path}"
proto_dir="$(dirname "${proto}")"
proto_file="$(basename "${proto}")"
port="${TEST_GRPC_PORT:-50053}"
log="${TEST_TMPDIR:-/tmp}/note_server.log"

cleanup() {
  if [[ -n "${server_pid:-}" ]]; then
    kill "${server_pid}" 2>/dev/null || true
    wait "${server_pid}" 2>/dev/null || true
  fi
}
trap cleanup EXIT

rm -f "${log}"
"${server}" "${port}" >"${log}" 2>&1 &
server_pid="$!"

for _ in $(seq 1 100); do
  if nc -z 127.0.0.1 "${port}" >/dev/null 2>&1; then
    break
  fi
  sleep 0.1
done

if ! nc -z 127.0.0.1 "${port}" >/dev/null 2>&1; then
  cat "${log}" >&2 || true
  echo "note_server did not start on port ${port}" >&2
  exit 1
fi

services="$(
  grpcurl -plaintext -connect-timeout 3 -max-time 5 \
    "127.0.0.1:${port}" list
)"

grep -q '^lean\.example\.proto\.NoteService$' <<<"${services}"
grep -q '^grpc\.reflection\.v1\.ServerReflection$' <<<"${services}"
grep -q '^grpc\.reflection\.v1alpha\.ServerReflection$' <<<"${services}"

# --- Reflection-only interop: no -proto/-import-path flags below this block.
# grpcurl resolves the schema entirely from the server's embedded descriptors
# (ServerReflectionInfo FileContainingSymbol / FileByFilename).

# Describe the service via reflection.
describe_service="$(
  grpcurl -plaintext -connect-timeout 3 -max-time 5 \
    "127.0.0.1:${port}" describe lean.example.proto.NoteService
)"
grep -q 'rpc Echo ( .lean.example.proto.Note ) returns ( .lean.example.proto.Note )' <<<"${describe_service}"
grep -q 'rpc Chat ( stream .lean.example.proto.Note ) returns ( stream .lean.example.proto.Note )' <<<"${describe_service}"

# Describe a message that lives in the imported common/note_common.proto; the
# server must return the transitive descriptor closure for this to resolve.
describe_meta="$(
  grpcurl -plaintext -connect-timeout 3 -max-time 5 \
    "127.0.0.1:${port}" describe lean.example.proto.NoteMeta
)"
grep -q 'created_at_unix' <<<"${describe_meta}"

# Invoke Echo purely via reflection.
reflection_echo="$(
  grpcurl -plaintext -connect-timeout 3 -max-time 5 \
    -d '{"title":"via reflection","priority":9,"color":"RED"}' \
    "127.0.0.1:${port}" lean.example.proto.NoteService/Echo
)"
grep -q '"title": "via reflection echoed"' <<<"${reflection_echo}"
grep -q '"priority": 9' <<<"${reflection_echo}"
grep -q '"color": "RED"' <<<"${reflection_echo}"

# Invoke Meta purely via reflection; request/response types come from the
# imported dependency file.
reflection_meta="$(
  grpcurl -plaintext -connect-timeout 3 -max-time 5 \
    -d '{"owner":"reflection rpc","createdAtUnix":"1700000400"}' \
    "127.0.0.1:${port}" lean.example.proto.NoteService/Meta
)"
grep -q '"owner": "reflection rpc echoed"' <<<"${reflection_meta}"
grep -q '"createdAtUnix": "1700000400"' <<<"${reflection_meta}"

response="$(
  grpcurl -plaintext -connect-timeout 3 -max-time 5 \
    -import-path "${proto_dir}" \
    -proto "${proto_file}" \
    -d '{"title":"lean proto","priority":3,"tags":["grpcurl"],"color":"BLUE","meta":"grpcurl keyword"}' \
    "127.0.0.1:${port}" lean.example.proto.NoteService/Echo
)"

echo "${response}"
grep -q '"title": "lean proto echoed"' <<<"${response}"
grep -q '"priority": 3' <<<"${response}"
grep -q '"color": "BLUE"' <<<"${response}"
grep -q '"meta": "grpcurl keyword"' <<<"${response}"

meta_response="$(
  grpcurl -plaintext -connect-timeout 3 -max-time 5 \
    -import-path "${proto_dir}" \
    -proto "${proto_file}" \
    -d '{"owner":"grpcurl imported rpc","createdAtUnix":"1700000300"}' \
    "127.0.0.1:${port}" lean.example.proto.NoteService/Meta
)"

grep -q '"owner": "grpcurl imported rpc echoed"' <<<"${meta_response}"
grep -q '"createdAtUnix": "1700000300"' <<<"${meta_response}"

set +e
deadline_response="$(
  grpcurl -plaintext -connect-timeout 3 -max-time 0.005 \
    -import-path "${proto_dir}" \
    -proto "${proto_file}" \
    -d '{"title":"deadline","priority":1}' \
    "127.0.0.1:${port}" lean.example.proto.NoteService/Slow 2>&1
)"
deadline_status=$?
set -e

if [[ "${deadline_status}" -eq 0 ]]; then
  echo "expected Slow RPC with grpcurl deadline to fail" >&2
  echo "${deadline_response}" >&2
  exit 1
fi
grep -Eqi 'deadline|DeadlineExceeded|DEADLINE_EXCEEDED' <<<"${deadline_response}"

set +e
fail_response="$(
  grpcurl -plaintext -connect-timeout 3 -max-time 5 \
    -import-path "${proto_dir}" \
    -proto "${proto_file}" \
    -d '{"title":"bad","priority":1}' \
    "127.0.0.1:${port}" lean.example.proto.NoteService/Fail 2>&1
)"
fail_status=$?
set -e

if [[ "${fail_status}" -eq 0 ]]; then
  echo "expected Fail RPC to return a non-OK gRPC status" >&2
  echo "${fail_response}" >&2
  exit 1
fi
grep -Eqi 'InvalidArgument|INVALID_ARGUMENT|Code: InvalidArgument' <<<"${fail_response}"
grep -q 'invalid note from generated service' <<<"${fail_response}"

large_memo="$(printf '%90000s' '' | tr ' ' x)"
large_response="$(
  grpcurl -plaintext -connect-timeout 3 -max-time 5 \
    -import-path "${proto_dir}" \
    -proto "${proto_file}" \
    -d "{\"title\":\"large\",\"memo\":\"${large_memo}\"}" \
    "127.0.0.1:${port}" lean.example.proto.NoteService/Echo
)"

grep -q '"title": "large echoed"' <<<"${large_response}"
grep -q '"memo": "' <<<"${large_response}"

stream_response="$(
  grpcurl -plaintext -connect-timeout 3 -max-time 5 \
    -import-path "${proto_dir}" \
    -proto "${proto_file}" \
    -d '{"title":"streamed","priority":5}' \
    "127.0.0.1:${port}" lean.example.proto.NoteService/List
)"

grep -q '"title": "streamed one"' <<<"${stream_response}"
grep -q '"title": "streamed two"' <<<"${stream_response}"

collect_requests="${TEST_TMPDIR:-/tmp}/collect_requests.json"
cat >"${collect_requests}" <<'EOF'
{"title":"left","priority":2}
{"title":"right","priority":4}
EOF

collect_response="$(
  grpcurl -plaintext -connect-timeout 3 -max-time 5 \
    -import-path "${proto_dir}" \
    -proto "${proto_file}" \
    -d @ \
    "127.0.0.1:${port}" lean.example.proto.NoteService/Collect <"${collect_requests}"
)"

grep -q '"title": "left,right collected"' <<<"${collect_response}"
grep -q '"priority": 6' <<<"${collect_response}"

chat_requests="${TEST_TMPDIR:-/tmp}/chat_requests.json"
cat >"${chat_requests}" <<'EOF'
{"title":"alpha","priority":7}
{"title":"beta","priority":8}
EOF

chat_response="$(
  grpcurl -plaintext -connect-timeout 3 -max-time 5 \
    -import-path "${proto_dir}" \
    -proto "${proto_file}" \
    -d @ \
    "127.0.0.1:${port}" lean.example.proto.NoteService/Chat <"${chat_requests}"
)"

grep -q '"title": "alpha chat"' <<<"${chat_response}"
grep -q '"title": "beta chat"' <<<"${chat_response}"
