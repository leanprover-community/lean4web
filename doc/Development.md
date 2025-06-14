- [Back to README](../README.md)
- [User Manual](./Usage.md)
- [Installation](./Installation.md)
- Development


## Development Instructions

Install [npm](https://www.npmjs.com/) and clone this repository. Inside the repository, run:

1. `npm install`, to install dependencies
2. `npm run build:server`, to build contained lean projects under `Projects/` (or run `lake build` manually inside any lean project)
3. `npm start`, to start the server.

The project can be accessed via http://localhost:3000. (Internally, websocket requests to `ws://localhost:3000/`websockets will be forwarded to a Lean server running on port 8080.)
