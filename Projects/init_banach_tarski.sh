#!/usr/bin/bash
# only if banach-tarski is not already cloned
if [ ! -d "banach-tarski" ]; then
    git clone git@github.com:Bergschaf/banach-tarski.git
fi
# else update the repo
cd banach-tarski || exit
git checkout development
git pull
# initialize the lean project
#lake update -R
#lake build
