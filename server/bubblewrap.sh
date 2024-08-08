#/bin/bash

ELAN_HOME=$(cd $1 && lake env printenv ELAN_HOME)

if command -v bwrap >/dev/null 2>&1; then
  (exec bwrap\
    --ro-bind $1 /project \
    --ro-bind $ELAN_HOME /elan \
    --ro-bind /usr /usr \
    --dev /dev \
    --proc /proc \
    --symlink usr/lib /lib\
    --symlink usr/lib64 /lib64\
    --symlink usr/bin /bin\
    --symlink usr/sbin /sbin\
    --clearenv \
    --setenv PATH "/elan/bin:/bin" \
    --setenv ELAN_HOME "/elan" \
    --unshare-user \
    --unshare-pid  \
    --unshare-net  \
    --unshare-uts  \
    --unshare-cgroup \
    --die-with-parent \
    --chdir "/project/" \
    lean --server
  )
else
  echo "bwrap is not installed. Running without container." >&2
  (exec
    cd $1
    lean --server
  )
fi
