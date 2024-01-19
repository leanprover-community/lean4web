#!/usr/bin/bash
# only if banach-tarski is not already cloned
if [ ! -d "banach-tarski" ]; then
    git clone https://github.com/Bergschaf/banach-tarski.git
fi
# else update the repo
cd banach-tarski || exit
git pull
# initialize the lean project
lake update mathlib
lake build