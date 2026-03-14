- [Back to README](../README.md)
- [User Manual](./Usage.md)
- Installation
- [Development](./Development.md)
- [Troubleshoot](./Troubleshoot.md)

## Security

Running a Lean instance on a server is always a potential security risk.

Therefore, this project uses [Bubblewrap](https://github.com/containers/bubblewrap) to run the instance in a container.

You can avoid using bubblewrap by using development mode or by providing `NO_BWRAP=true` to production mode. In that case, the Lean server will
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
  npm run prod
  ```
- To disable the bubblewrap containers, start the server with
  ```
  NO_BWRAP=true npm run prod
  ```
- Start the client seperately, for example with
  ```
  npm run start:client
  ```
  and open http://localhost:3000
- To set the locations of SSL certificates, use the following environment variables:
  ```
  SSL_CRT_FILE=/path/to/crt_file.cer SSL_KEY_FILE=/path/to/private_ssl_key.pem npm run prod
  ```

### Adding different Lean projects

You can run any lean project through the webeditor by cloning them to the `Projects/` folder. See [Adding Projects](./Projects.md) for further instructions.

### Environment variables

The following environment variables can be used to modify the server

#### Client

For example for `npm start`, `npm start:client`.

| name   | values | default | description |
| ------ | ------ | ------- | ----------- |
| (none) |        |         |             |

#### Server

For example for `npm start`, `npm run production`, `npm run start:server`.

| name                 | values                      | default         | description                                                                                                                                       |
| -------------------- | --------------------------- | --------------- | ------------------------------------------------------------------------------------------------------------------------------------------------- |
| `NO_BWRAP`           | `true`, `false`             | `false`         | to disable to use of `bubblewrap` in production mode. This means `Lean` runs without any container on your system, which imposes a security risk! |
| `GITHUB_ACTIONS`     | `true` ,`false`             | `false`         | is set by github actions to change the verbosity of some server output                                                                            |
| `NODE_ENV`           | `development`, `production` |                 |                                                                                                                                                   |
| `PROJECTS_BASE_PATH` | string                      | `Projects`      | **relative path** from the root of this repo to the folder where the Lean projects are located.                                                   |
| `PORT`               | number                      | `8080` or `443` | sets the port for the backend server                                                                                                              |
| `SSL_CRT_FILE`       | string                      | `""`            | recuired to serve https                                                                                                                           |
| `SSL_KEY_FILE`       | string                      | `""`            | recuired to serve https                                                                                                                           |

### Others

See [Server Maintenance Notes](./Maintenance.md).
