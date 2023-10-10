#/bin/bash

LEAN_ROOT=$(cd LeanProject; lean --print-prefix)
LEAN_PATH=$(cd LeanProject; lake env printenv LEAN_PATH)

(exec bwrap\
  --ro-bind ./LeanProject /LeanProject \
  --ro-bind $LEAN_ROOT /lean \
  --ro-bind $GLIBC $GLIBC `# only dep of bin/lean` \
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
  --chdir "/LeanProject/" \
  lean --server
)
