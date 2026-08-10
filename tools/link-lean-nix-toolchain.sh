#!/usr/bin/env bash
set -euo pipefail

ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
TOOLCHAIN_NAME="${1:-rules-lean-grpc-nix-4.31}"
NIX_ATTR="${LEAN_NIX_ATTR:-lean4_upstream_std}"
NIX_FILE="${LEAN_NIX_FILE:-${ROOT}/third_party/Lean-zh/protobuf/nixpkgs.nix}"

if ! command -v nix >/dev/null 2>&1; then
  echo "nix is required to resolve ${NIX_ATTR}" >&2
  exit 1
fi

if [[ "${TOOLCHAIN_NAME}" == *['/:']* ]]; then
  echo "${TOOLCHAIN_NAME} is not a local Nix toolchain name" >&2
  echo "Pass a plain local alias (no '/' or ':')." >&2
  exit 1
fi

toolchain_path="$(
  nix build --no-link --print-out-paths -f "${NIX_FILE}" "${NIX_ATTR}"
)"

# lean4ij 0.2.8 resolves local toolchains from this exact location and does
# not consult ELAN_HOME.  An Elan installation is not required: `toolchain
# link` is represented by this symlink on disk.
toolchains_dir="${HOME}/.elan/toolchains"
existing_path="${toolchains_dir}/${TOOLCHAIN_NAME}"

for executable in lean lake; do
  if [[ ! -x "${toolchain_path}/bin/${executable}" ]]; then
    echo "${toolchain_path}/bin/${executable} is missing or not executable" >&2
    exit 1
  fi
done

if [[ ! -d "${toolchain_path}/src/lean" ]]; then
  echo "${toolchain_path}/src/lean is missing (lean4ij needs Lean sources)" >&2
  exit 1
fi

mkdir -p "${toolchains_dir}"

if [[ -e "${existing_path}" || -L "${existing_path}" ]]; then
  if [[ -L "${existing_path}" ]]; then
    existing_target="$(readlink "${existing_path}")"
  else
    existing_target="$(cd "${existing_path}" && pwd -P)"
  fi

  if [[ "${existing_target}" != "${toolchain_path}" ]]; then
    echo "${TOOLCHAIN_NAME} already points to ${existing_target}" >&2
    echo "Remove or rename it before linking ${toolchain_path}" >&2
    exit 1
  fi
else
  ln -s "${toolchain_path}" "${existing_path}"
fi

echo "Linked ${TOOLCHAIN_NAME} -> ${toolchain_path}"
"${existing_path}/bin/lean" --version
"${existing_path}/bin/lake" --version
