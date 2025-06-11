- [Back to README](../README.md)
- [User Manual](./Usage.md)
- Installation
- [Development](./Development.md)


## Security
Providing the use access to a Lean instance running on the server is a severe security risk.
That is why we start the Lean server using [Bubblewrap](https://github.com/containers/bubblewrap).

If bubblewrap is not installed, the server will start without a container and produce a warning.
You can also opt-out of using bubblewrap by setting `NODE_ENV=development`.

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

If you get the following error:
```
bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted
bwrap: setting up uid map: Permission denied
```
follow these instructions:
https://etbe.coker.com.au/2024/04/24/ubuntu-24-04-bubblewrap/

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
*  */6 * * * cd /home/USER/lean4web && npm run build:server 2>&1 1>/dev/null | logger -t lean4web
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

Depending on the GDPR and laws applying to your server, you will need to provide the following
information:

- `client/config/config.tsx`, `serverCountry`: where your server is located.
- `client/config/config.tsx`, `contactDetails`: used in privacy policy & impressum
- `client/config/config.tsx`, `impressum`: further legal notes

if `contactDetails` or `impressum` are not `null`, you will see an item `Impressum` in
the dropdown menu containing that information.

Further, you might need to add the impressum manually to `index.html`
for people with javascript disabled!

### Running different projects
You can run any lean project through the webeditor by cloning them to the `Projects/` folder. See [Adding Projects](Projects/README.md) for further instructions.
