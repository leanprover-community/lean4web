- [Back to README](../README.md)
- [User Manual](./Usage.md)
- Installation
- [Development](./Development.md)
- [Troubleshoot](./Troubleshoot.md)

## Security

Running a Lean instance on a server is always a potential security risk.

Therefore, this project uses [Bubblewrap](https://github.com/containers/bubblewrap) to run the instance in a container.

You can avoid using bubblewrap by using development mode or by providing `ALLOW_NO_BUBBLEWRAP=true` to production mode. In that case, the Lean server will
run without any container on your server.

## Legal information

Depending on the GDPR and laws applying to your server, you will need to provide the following
information:

- `client/config/config.tsx`, `serverCountry`: where your server is located.
- `client/config/config.tsx`, `contactDetails`: used in privacy policy & impressum
- `client/config/config.tsx`, `impressum`: further legal notes

if `contactDetails` or `impressum` are not `null`, you will see an item `Impressum` in
the dropdown menu containing that information.

Further, you might need to add the impressum manually to `index.html`
for people with javascript disabled!

## Build Instructions

The project is initially designed to run on Ubuntu 22 LTS.

Other OS or distributions have not been tested.
PRs to the repo to improve the installation on other distributions
are always welcome!

### Prerequisites

On a running system, you might already have these installed, if not:

- Install NPM: [official instructions](https://docs.npmjs.com/downloading-and-installing-node-js-and-npm)
- Install Git: `sudo apt-get install git`
- (optional) Install Bubblewrap: `sudo apt-get install bubblewrap`

### Installation

- Clone this repo:
  ```
  git clone --recurse-submodules https://github.com/leanprover-community/lean4web.git
  ```
  note that `--recurse-submodules` is needed to load the predefined projects in `Projects/`. (on an existing clone, you can call `git submodule init` and `git submodule update`)
- Navigate into the cloned repository
  ```
  cd lean4web
  ```
- Install dependencies
  ```
  npm install
  ```

### Development mode

- Start the project in development mode
  ```
  npm start
  ```
- Go to http://localhost:3000

### Production mode

- Compile the project
  ```
  npm run build
  ```
- Start the server
  ```
  npm run production
  ```
- To disable the bubblewrap containers, start the server with
  ```
  ALLOW_NO_BUBBLEWRAP=true npm run production
  ```
- Start the client seperately, for example with
  ```
  npm run start:client
  ```
  and open http://localhost:3000
- To set the locations of SSL certificates, use the following environment variables:
  ```
  SSL_CRT_FILE=/path/to/crt_file.cer SSL_KEY_FILE=/path/to/private_ssl_key.pem npm run production
  ```

### Adding different Lean projects

You can run any lean project through the webeditor by cloning them to the `Projects/` folder. See [Adding Projects](../Projects/README.md) for further instructions.

### Others

In addition, we use `Nginx` and `pm2` to manage our server.

(TODO: details)

### Maintenance

#### Cronjob: updating Lean projects

Optionally, you can set up a cronjob to regularly update the Lean projects.
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
*  */6 * * * cd /home/USER/lean4web && npm run build:server 2>&1 1>/dev/null | logger -t lean4web
40 2   * * * rm -rf /home/USER/.cache/mathlib/
```

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
