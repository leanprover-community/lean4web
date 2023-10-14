# Lean 4 Web

This is a web version of Lean 4. In contrast to the [Lean 3 web editor](https://github.com/leanprover-community/lean-web-editor), in this web editor, the Lean server is
running on a web server, and not in the browser.

## Contribution

If you experience any problems, or have feature requests, please open an issue here!
PRs are welcome as well.

## Security
Providing the use access to a Lean instance running on the server is a severe security risk. That is why we start the Lean server
using [Bubblewrap](https://github.com/containers/bubblewrap).

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
git clone https://github.com/leanprover-community/lean4web.git
```

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

### Legal information
For legal purposes, we need to display contact details. When setting up your own server,
you will need to modify the following files:

- `client/src/config/text.tsx`: Update contact information & server location. (set them to `null` if you don't need to display them in your country)
- `client/public/index.html`: Update the `noscript` page with the correct contact details.

## Development Instructions

Install [npm](https://www.npmjs.com/) and clone this repository. Inside the repository, run
`npm install` to install dependencies, and
then `npm start`.
The project can be accessed via http://localhost:3000. (Internally, websocket requests to `ws://localhost:3000/`websockets will be forwarded to a Lean server running on port 8080.)
