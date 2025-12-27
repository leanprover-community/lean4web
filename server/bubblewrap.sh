#!/bin/bash

# Limit CPU time per process to 1h
ulimit -t 3600
# NB: The RSS limit (ulimit -m) is not supported by modern linux!

PROJECT_NAME="$(realpath $1)"
LEAN_ROOT="$(cd $1 && lean --print-prefix)"
LEAN_SRC_PATH=$(cd $1 && lake env printenv LEAN_SRC_PATH)

# # print commands as they are executed
# set -x

exec bwrap\
  --ro-bind "$1" "/$PROJECT_NAME" \
  --ro-bind "$LEAN_ROOT" /lean \
  --ro-bind /usr /usr \
  --ro-bind /etc/localtime /etc/localtime \
  --dev /dev \
  --tmpfs /tmp \
  --proc /proc \
  --symlink usr/lib /lib\
  --symlink usr/lib64 /lib64\
  --symlink usr/bin /bin\
  --symlink usr/sbin /sbin\
  --clearenv \
  --setenv PATH "/bin:/usr/bin:/lean/bin" \
  --setenv LEAN_SRC_PATH "$LEAN_SRC_PATH" \
  --unshare-user \
  --unshare-pid  \
  --unshare-net  \
  --unshare-uts  \
  --unshare-cgroup \
  --die-with-parent \
  --chdir "/$PROJECT_NAME/" \
  lake serve --
