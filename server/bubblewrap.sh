#/bin/bash

ELAN_HOME=/home/lean4web/.elan

(exec bwrap\
  --ro-bind ./LeanProject /LeanProject \
  --ro-bind $ELAN_HOME /elan \
  --ro-bind /nix /nix \
  --dev /dev \
  --proc /proc \
  --clearenv \
  --setenv PATH "/elan/bin:$PATH" \
  --setenv ELAN_HOME "/elan" \
  --unshare-user \
  --unshare-pid  \
  --unshare-net  \
  --unshare-uts  \
  --unshare-cgroup \
  --die-with-parent \
  --chdir "/LeanProject/" \
  lean --server
)
