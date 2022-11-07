# Lean 4 Web

This is a web version of Lean 4. In contrast to the [Lean 3 web editor](https://github.com/leanprover-community/lean-web-editor), in this web editor, the Lean server is
running on a web server, and not in the browser.

## Security
Providing the use access to a Lean instance running on the server is a severe security risk. That is why we start the Lean server in a Docker container secured by gVisor.

## Build Instructions

We have set up the project on a Ubuntu Server 22.10.
Here are the installation instructions:

Install Docker:
```
sudo apt-get update
sudo apt-get install ca-certificates curl gnupg lsb-release -y
sudo mkdir -p /etc/apt/keyrings
curl -fsSL https://download.docker.com/linux/ubuntu/gpg | sudo gpg --dearmor -o /etc/apt/keyrings/docker.gpg
echo \
  "deb [arch=$(dpkg --print-architecture) signed-by=/etc/apt/keyrings/docker.gpg] https://download.docker.com/linux/ubuntu \
  $(lsb_release -cs) stable" | sudo tee /etc/apt/sources.list.d/docker.list > /dev/null
sudo apt-get update
sudo apt-get install docker-ce docker-ce-cli containerd.io docker-compose-plugin -y
```
(copied from https://docs.docker.com/engine/install/ubuntu/)

To be able to run docker containers as a regular user,
add yourself to the `docker` group:
```
sudo groupadd docker
sudo usermod -aG docker ${USER}
newgrp docker
```
Install gVisor:
```
sudo apt-get update && \
sudo apt-get install -y \
    apt-transport-https \
    ca-certificates \
    curl \
    gnupg
curl -fsSL https://gvisor.dev/archive.key | sudo gpg --dearmor -o /usr/share/keyrings/gvisor-archive-keyring.gpg
echo "deb [arch=$(dpkg --print-architecture) signed-by=/usr/share/keyrings/gvisor-archive-keyring.gpg] https://storage.googleapis.com/gvisor/releases release main" | sudo tee /etc/apt/sources.list.d/gvisor.list > /dev/null
sudo apt-get update && sudo apt-get install -y runsc
```
(copied from https://gvisor.dev/docs/user_guide/install/#install-from-an-apt-repository)

To make sure that docker knows about gVisor, run these commands:
```
sudo runsc install
sudo systemctl reload docker
```

Install NPM (don't use `apt-get` since it will give you an outdated version of npm):
```
curl -o- https://raw.githubusercontent.com/nvm-sh/nvm/v0.39.2/install.sh | bash
source ~/.bashrc
nvm install node npm
```

Now, install `git` and clone this repository.
Navigate into the cloned repository and
run
```
npm install
npm run build
```

Now the server can be started using
```
PORT=8080 npm run production
```

To set the locations of SSL certificates, run
```
SSL_CRT_FILE=/path/to/crt_file.cer SSL_KEY_FILE=/path/to/private_ssl_key.pem npm run production
```

## Development Instructions

Install [npm](https://www.npmjs.com/) and clone this repository. Inside the repository, run
`npm install` to install dependencies, and
then `npm start`.
The project can be accessed via http://localhost:3000. (Internally, websocket requests to `ws://localhost:3000/`websockets will be forwarded to a Lean server running on port 8080.)
