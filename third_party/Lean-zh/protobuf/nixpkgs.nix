{ config ? {}, overlays ? [], ... }@args:

let
  spec = builtins.fromJSON (builtins.readFile ./nixpkgs.json);
  nixpkgs = fetchTarball {
    url = "https://github.com/${spec.owner}/${spec.repo}/archive/${spec.rev}.tar.gz";
    sha256 = spec.sha256;
  };

  # The pinned nixos-24.11 lean4 package is 4.10.0 and only installs a
  # top-level Std module. This source revision includes the newer Std.Http
  # modules and builds them as part of the same compiler derivation, keeping
  # the compiler and .olean ABI aligned.
  leanUpstreamStdRev = "24bef91f9a20a45f074729e869461d374687de1c";
  leanUpstreamStdSrcSha256 = "1fsj6zws1amgnzw8nl14iqb0gbq2l8cq5vldixgr1c9awm7ybxvn";

  leanUpstreamStdOverlay = final: prev:
    let
      leantarVersion = "0.1.19";
      leantarPlatform =
        {
          x86_64-linux = {
            target = "x86_64-unknown-linux-musl";
            sha256 = "0fx1i9nn25hm65nhiiwq087qrc0pyhskdj09yyhcqmk5mhsfkkhk";
          };
          aarch64-linux = {
            target = "aarch64-unknown-linux-musl";
            sha256 = "0kg9ckm870h232s94m4721r3ch82kranba14xyyrai191l9agxrw";
          };
          x86_64-darwin = {
            target = "x86_64-apple-darwin";
            sha256 = "0m8dwj8viqmvxrkl0595s5h1njhkmh7g4bgfgw4r5zqms3x419k3";
          };
          aarch64-darwin = {
            target = "aarch64-apple-darwin";
            sha256 = "08bffz3yy6mjyhc7l4503cq6ri3lwsgvpq8y8y5rl8k035gnnc5l";
          };
        }.${prev.stdenv.hostPlatform.system}
          or (throw "Unsupported leantar platform: ${prev.stdenv.hostPlatform.system}");
      leantar = prev.runCommand "leantar-${leantarVersion}" {
        src = prev.fetchzip {
          url = "https://github.com/digama0/leangz/releases/download/v${leantarVersion}/leantar-v${leantarVersion}-${leantarPlatform.target}.tar.gz";
          inherit (leantarPlatform) sha256;
        };
      } ''
        install -Dm755 "$src/leantar" "$out/bin/leantar"
      '';
    in {
      lean4_upstream_std = prev.lean4.overrideAttrs (old: rec {
        version = "4.31.0-pre-24bef91";
        src = prev.fetchFromGitHub {
          owner = "leanprover";
          repo = "lean4";
          rev = leanUpstreamStdRev;
          sha256 = leanUpstreamStdSrcSha256;
        };

        postPatch = "substituteInPlace src/CMakeLists.txt --replace-fail 'set(GIT_SHA1 \"\")' 'set(GIT_SHA1 \"${src.rev}\")'\nrm -rf src/lake/examples/git/\n";

        nativeBuildInputs =
          old.nativeBuildInputs
          ++ [ prev.pkg-config leantar ]
          ++ prev.lib.optionals prev.stdenv.isDarwin [ prev.darwin.cctools ];

        buildInputs = old.buildInputs ++ [ prev.libuv prev.cadical ];

        cmakeFlags = old.cmakeFlags ++ [
          "-DUSE_MIMALLOC=OFF"
          "-DLEANTAR=${leantar}/bin/leantar"
        ];
      });
    };
in
import nixpkgs (args // {
  inherit config;
  overlays = overlays ++ [ leanUpstreamStdOverlay ];
})
