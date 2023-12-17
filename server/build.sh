#!/usr/bin/env bash

cd "$(dirname $0)/../Projects"

# Iterate over subfolders in Projects and look for a build file `build.sh`
for folder in "."/*; do
  if [ -d "$folder" ]; then
    build_script="$folder/build.sh"
    if [ -f "$build_script" ]; then
      SECONDS=0
      echo "Start building $folder"
      echo "Start building $folder" | logger -t lean4web

      "$build_script"

      duration=$SECONDS
      echo "Finished $folder in $(($duration / 60)):$(($duration % 60)) min"
      echo "Finished $folder in $(($duration / 60)):$(($duration % 60)) min" | logger -t lean4web
    else
      echo "Skipping $folder: build.sh missing"
    fi

  fi
done
