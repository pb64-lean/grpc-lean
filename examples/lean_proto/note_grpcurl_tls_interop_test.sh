#!/usr/bin/env bash
# gRPC-over-TLS interoperability gate: drives the Lean `serveTls` server with
# grpcurl (grpc-go) and openssl s_client. Everything below the TCP socket --
# TLS 1.3, ALPN "h2", HTTP/2 and gRPC -- is Lean code from this repo and
# ../tls13-lean; the client is an independent implementation.
#
# Tagged manual/local: it binds a loopback port and shells out to host tools,
# so `bazel test //...` skips it. Run it with grpcurl and openssl on PATH:
#
#   nix shell nixpkgs#grpcurl nixpkgs#openssl -c \
#     bazel test //examples/lean_proto:note_grpcurl_tls_interop_test \
#     --test_output=streamed
set -euo pipefail

server="${1:?missing note_server path}"
proto="${2:?missing note.proto path}"
cert_der="${3:?missing server_cert.der path}"
key_raw="${4:?missing server_key.raw path}"
cert_pem="${5:?missing server_cert.pem path}"
proto_dir="$(dirname "${proto}")"
proto_file="$(basename "${proto}")"
port="${TEST_GRPC_TLS_PORT:-50054}"
log="${TEST_TMPDIR:-/tmp}/note_tls_server.log"

cleanup() {
  status=$?
  if [[ "${status}" -ne 0 && -f "${log}" ]]; then
    echo "--- note_server log (test exit ${status}):" >&2
    cat "${log}" >&2 || true
  fi
  if [[ -n "${server_pid:-}" ]]; then
    kill "${server_pid}" 2>/dev/null || true
    wait "${server_pid}" 2>/dev/null || true
  fi
}
trap cleanup EXIT

rm -f "${log}"
"${server}" "${port}" --tls "${cert_der}" "${key_raw}" >"${log}" 2>&1 &
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

grpcurl_tls() {
  grpcurl -cacert "${cert_pem}" -servername localhost \
    -connect-timeout 5 -max-time 15 "$@"
}

# --- TLS layer: the handshake completes and ALPN selects "h2". Isolating this
# first means a later gRPC failure cannot be blamed on TLS or ALPN.
alpn="$(
  openssl s_client -connect "127.0.0.1:${port}" -tls1_3 -alpn h2 \
    -CAfile "${cert_pem}" -servername localhost -verify_return_error \
    </dev/null 2>&1
)"
grep -q '^ALPN protocol: h2$' <<<"${alpn}"
grep -q 'Verify return code: 0 (ok)' <<<"${alpn}"
grep -q 'Peer certificate: CN=localhost' <<<"${alpn}" \
  || grep -q 'subject=CN *= *localhost' <<<"${alpn}"

# --- Certificate validation is real: the wrong SNI/hostname must be rejected.
set +e
badname="$(
  grpcurl -cacert "${cert_pem}" -servername not-localhost.invalid \
    -connect-timeout 5 -max-time 15 "127.0.0.1:${port}" list 2>&1
)"
badname_status=$?
set -e
if [[ "${badname_status}" -eq 0 ]]; then
  echo "expected grpcurl to reject the wrong server name" >&2
  echo "${badname}" >&2
  exit 1
fi

# --- Reflection-only interop over TLS: no -proto/-import-path flags.
services="$(grpcurl_tls "127.0.0.1:${port}" list)"
grep -q '^lean\.example\.proto\.NoteService$' <<<"${services}"
grep -q '^grpc\.reflection\.v1\.ServerReflection$' <<<"${services}"

describe_service="$(
  grpcurl_tls "127.0.0.1:${port}" describe lean.example.proto.NoteService
)"
grep -q 'rpc Echo ( .lean.example.proto.Note ) returns ( .lean.example.proto.Note )' \
  <<<"${describe_service}"
grep -q 'rpc Chat ( stream .lean.example.proto.Note ) returns ( stream .lean.example.proto.Note )' \
  <<<"${describe_service}"

reflection_echo="$(
  grpcurl_tls -d '{"title":"via reflection","priority":9,"color":"RED"}' \
    "127.0.0.1:${port}" lean.example.proto.NoteService/Echo
)"
grep -q '"title": "via reflection echoed"' <<<"${reflection_echo}"
grep -q '"color": "RED"' <<<"${reflection_echo}"

# --- Unary call with the schema supplied by the client instead.
response="$(
  grpcurl_tls -import-path "${proto_dir}" -proto "${proto_file}" \
    -d '{"title":"lean proto","priority":3,"tags":["grpcurl"],"color":"BLUE","meta":"grpcurl keyword"}' \
    "127.0.0.1:${port}" lean.example.proto.NoteService/Echo
)"
grep -q '"title": "lean proto echoed"' <<<"${response}"
grep -q '"meta": "grpcurl keyword"' <<<"${response}"

# --- Error mapping survives the TLS record layer.
set +e
fail_response="$(
  grpcurl_tls -d '{"title":"bad","priority":1}' \
    "127.0.0.1:${port}" lean.example.proto.NoteService/Fail 2>&1
)"
fail_status=$?
set -e
if [[ "${fail_status}" -eq 0 ]]; then
  echo "expected Fail RPC to return a non-OK gRPC status" >&2
  echo "${fail_response}" >&2
  exit 1
fi
grep -Eqi 'InvalidArgument' <<<"${fail_response}"
grep -q 'invalid note from generated service' <<<"${fail_response}"

# --- A payload far larger than one TLS record (16 kB) and one HTTP/2 frame.
large_memo="$(printf '%90000s' '' | tr ' ' x)"
large_response="$(
  grpcurl_tls -d "{\"title\":\"large\",\"memo\":\"${large_memo}\"}" \
    "127.0.0.1:${port}" lean.example.proto.NoteService/Echo
)"
grep -q '"title": "large echoed"' <<<"${large_response}"

# --- Server-, client- and bidi-streaming over the same encrypted connection.
stream_response="$(
  grpcurl_tls -d '{"title":"streamed","priority":5}' \
    "127.0.0.1:${port}" lean.example.proto.NoteService/List
)"
grep -q '"title": "streamed one"' <<<"${stream_response}"
grep -q '"title": "streamed two"' <<<"${stream_response}"

stream_requests="${TEST_TMPDIR:-/tmp}/tls_stream_requests.json"
cat >"${stream_requests}" <<'EOF'
{"title":"alpha","priority":7}
{"title":"beta","priority":8}
EOF

collect_response="$(
  grpcurl_tls -d @ "127.0.0.1:${port}" \
    lean.example.proto.NoteService/Collect <"${stream_requests}"
)"
grep -q '"title": "alpha,beta collected"' <<<"${collect_response}"
grep -q '"priority": 15' <<<"${collect_response}"

chat_response="$(
  grpcurl_tls -d @ "127.0.0.1:${port}" \
    lean.example.proto.NoteService/Chat <"${stream_requests}"
)"
grep -q '"title": "alpha chat"' <<<"${chat_response}"
grep -q '"title": "beta chat"' <<<"${chat_response}"

echo "grpcurl over TLS 1.3 (ALPN h2) interop: all cases passed"
