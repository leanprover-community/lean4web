[![GitHub license](https://img.shields.io/badge/License-Apache_2.0-blue.svg)](https://github.com/leanprover-community/lean4web/blob/main/LICENSE)
[![(Runtime) Build and Test](https://github.com/leanprover-community/lean4web/actions/workflows/build.yml/badge.svg)](https://github.com/leanprover-community/lean4web/actions/workflows/build.yml)


# Lean 4 Web

This is a web version of Lean 4. The official lean playground is hosted at [live.lean-lang.org](https://live.lean-lang.org), while [lean.math.hhu.de](https://lean.math.hhu.de) hosts a development server testing newer features.

In contrast to the [Lean 3 web editor](https://github.com/leanprover-community/lean-web-editor), in this web editor, the Lean server is
running on a web server, and not in the browser.

## Contribution

If you experience any problems, or have feature requests, please open an issue here!
PRs are welcome as well.

## Security
Providing the use access to a Lean instance running on the server is a severe security risk.
That is why we start the Lean server using [Bubblewrap](https://github.com/containers/bubblewrap).

If bubblewrap is not installed, the server will start without a container and produce a warning.
You can also opt-out of using bubblewrap by setting `NODE_ENV=development`.

## Documentation

### URL arguments

The website parses arguments of the form `https://myserver.com/#arg1=value1&arg2=value2`.
The recognised arguments are:

- `code=`: plain text code.
  (overwrites `codez`)
- `codez=`: compressed code using [LZ-string](https://www.npmjs.com/package/lz-string).
- `url=`: a URL where the content is loaded from.
  (overwrites `code` and `codez`).
- `project=`: the Lean project used by the server to evaluate the code. This has the be the name
  of one of the projects the server defines in their config.

The server will automatically only write one of `code`, `codez`, and `url` based on the following
logic:

1. if the code matches the one from the loaded URL, use `url`
2. if the preferences say no comression, use `code`
3. otherwise use `codez` or `code` depending on which results in a shorter URL.

## Build Instructions

We have set up the project on a Ubuntu Server 22.10.
Here are the installation instructions:

Install NPM (don't use `apt-get` since it will give you an outdated version of npm):
```
curl -o- https://raw.githubusercontent.com/nvm-sh/nvm/v0.39.2/install.sh | bash
source ~/.bashrc
nvm install node npm
```

Now, install `git` and clone this repository:
```
sudo apt-get install git
git clone --recurse-submodules https://github.com/leanprover-community/lean4web.git
```

note that `--recurse-submodules` is needed to load the predefined projects in `Projects/`. (on an existing clone, you can call `git submodule init` and `git submodule update`)

Install Bubblewrap:
```
sudo apt-get install bubblewrap
```

Navigate into the cloned repository, install, and
compile:
```
cd lean4web
npm install
npm run build
```

Now the server can be started using
```
PORT=8080 npm run production
```

To set the locations of SSL certificates, use the following environment variables:
```
SSL_CRT_FILE=/path/to/crt_file.cer SSL_KEY_FILE=/path/to/private_ssl_key.pem PORT=8080 npm run production
```

### Cronjob

Optionally, you can set up a cronjob to regularly update the mathlib version.
To do so, run
```
crontab -e
```
and add the following lines, where all paths must be adjusted appropriately:
```
# Need to set PATH manually:
SHELL=/usr/bin/bash
PATH=/usr/local/sbin:/usr/local/bin:/sbin:/bin:/usr/sbin:/usr/bin:/home/USER/.elan/bin:/home/USER/.nvm/versions/node/v20.8.0/bin/

# Update server (i.e. mathlib) of lean4web and delete mathlib cache
*  */6 * * * cd /home/USER/lean4web && npm run build_server 2>&1 1>/dev/null | logger -t lean4web
40 2   * * * rm -rf /home/USER/.cache/mathlib/
```

Note that with this setup, you will still have to manage the lean toolchains manually, as they will slowly fill up your space (~0.9GB per new toolchain): see `elan toolchain --help` for infos.

In addition, we use Nginx and pm2 to manage our server.

#### Managing toolchains

Running and updating the server periodically might accumulate Lean toolchains.

To delete unused toolchains automatically, you can use the
[elan-cleanup tool](https://github.com/JLimperg/elan-cleanup) and set up a
cron-job with `crontab -e` and adding the following line, which runs once a month and
deletes any unused toolchains:

```
30 2 1 * * /PATH/TO/elan-cleanup/build/bin/elan-cleanup | logger -t lean-cleanup
```

You can see installed lean toolchains with `elan toolchain list`
and check the size of `~/.elan`.

### Legal information
For legal purposes, we need to display contact details. When setting up your own server,
you will need to modify the following files:

- `client/src/config/text.tsx`: Update contact information & server location. (set them to
  `null` if you don't need to display them in your country)
- `client/public/index.html`: Update the `noscript` page with the correct contact details.

## Development Instructions

Install [npm](https://www.npmjs.com/) and clone this repository. Inside the repository, run:

1. `npm install`, to install dependencies
2. `npm run build_server`, to build contained lean projects under `Projects/` (or run `lake build` manually inside any lean project)
3. `npm start`, to start the server.

The project can be accessed via http://localhost:3000. (Internally, websocket requests to `ws://localhost:3000/`websockets will be forwarded to a Lean server running on port 8080.)

## Running different projects
You can run any lean project through the webeditor by cloning them to the `Projects/` folder. See [Adding Projects](Projects/README.md) for further instructions.
