#/bin/bash

LEAN_ROOT="$(cd $1 && lean --print-prefix)"
LEAN_PATH="$(cd $1 && lake env printenv LEAN_PATH)"
GLIBC_PATH="$(nix-store --query "$(patchelf --print-interpreter "$LEAN_ROOT/bin/lean")")"

set -x

(exec bwrap\
  --ro-bind "$1" /project \
  --ro-bind "$LEAN_ROOT" /lean \
  --ro-bind "$GLIBC_PATH" "$GLIBC_PATH" `# only dep of bin/lean` \
  --dev /dev \
  --proc /proc \
  --clearenv \
  --setenv PATH "/lean/bin" \
  --setenv LAKE "/no" `# tries to invoke git otherwise` \
  --setenv LEAN_PATH "$LEAN_PATH" \
  --unshare-user \
  --unshare-pid  \
  --unshare-net  \
  --unshare-uts  \
  --unshare-cgroup \
  --die-with-parent \
  --chdir "/project" \
  lean --server
)
