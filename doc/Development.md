- [Back to README](../README.md)
- [User Manual](./Usage.md)
- [Installation](./Installation.md)
- [Adding Projects](./Projects.md)
- Development
- [Server Maintenance](./Maintenance.md)
- [Troubleshoot](./Troubleshoot.md)

## Development Instructions

Install [npm](https://www.npmjs.com/) and clone this repository. Inside the repository, run:

1. `npm install`, to install dependencies
2. `npm run build:server`, to build contained lean projects under `Projects/` (or run `lake build` manually inside any lean project)
3. `npm start`, to start the server.

The project can be accessed via http://localhost:3000. (Internally, websocket requests to `ws://localhost:3000/`websockets will be forwarded to a Lean server running on port `8080`.)

### Testing

Automated integration tests using `cypress`.

- Headless tests:
  ```
  npm test
  ```
- Cypress also has an interactive UI. Run both of these commands simultaneously:
  ```
  npm start
  npx cypress open
  ```

The tests produce screenshots on failure. In the Github-CI, failing tests will produce screenshots and videos which will be attached as artifacts for inspection.

### Application Design

#### Atom structure

The project uses various jotai atoms to describe the internal state. Below is an overview. Downwards-arrows mean the lower atom depends on the upper one, upwards arrows (red) mean the setter of the lower atom writes the upper one. Dotted lines are "setter-only".

The colors symbolise outside influence: queries (blue), the page url (orange) or browser storage (green). Red atoms are "setter-only".

Atoms which are considered "prinicipal input" are in a rhomboid.

```mermaid
graph TD;

  %% getter
  urlArgsAtom-->urlArgsStableAtom;
  urlArgsStableAtom-->importUrlAtom;
  importUrlAtom-->importedCodeQueryAtom;
  importedCodeQueryAtom-->importedCodeAtom;
  projectsQueryAtom-->projectsAtom
  projectsAtom-->defaultProjectAtom;
  projectsAtom-->currentProjectAtom;
  defaultProjectAtom-->currentProjectAtom;
  projectsAtom-->visibleProjectsAtom;
  currentProjectAtom-->visibleProjectsAtom;
  codeAtom[/codeAtom/]
  urlArgsStableAtom-->codeAtom;
  importedCodeAtom-->codeAtom;
  locationAtom-->settingsUrlAtom;
  settingsUrlAtom-->settingsUrlStableAtom;
  settingsAtom[/settingsAtom/]
  settingsUrlStableAtom-->settingsAtom;
  settingsAtom-->mobileAtom;

  %% getter and setter
  locationAtom<-->urlArgsAtom;
  importUrlBaseAtom<-->importUrlAtom;
  urlArgsAtom<-->currentProjectAtom;
  settingsBaseAtom<-->settingsAtom;
  settingsStoreAtom<-->settingsAtom;

  %% setter
  importUrlAtom -.-> urlArgsAtom;
  codeAtom -.-> urlArgsAtom;
  settingsAtom -.-> locationAtom;

  setImportUrlAndProjectAtom[/setImportUrlAndProjectAtom/]
  importUrlAtom <-.-> setImportUrlAndProjectAtom
  currentProjectAtom <-.-> setImportUrlAndProjectAtom

  %% Styles

  linkStyle 16 stroke: red;
  linkStyle 17 stroke: red;
  linkStyle 18 stroke: red;
  linkStyle 19 stroke: red;
  linkStyle 20 stroke: red;
  linkStyle 21 stroke: red;
  linkStyle 22 stroke: red;
  linkStyle 23 stroke: red;
  linkStyle 24 stroke: red;
  linkStyle 25 stroke: red;

  classDef query fill:#d0ebff,stroke:#1c7ed6,stroke-width:2px;
  classDef storage fill:#d3f9d8,stroke:#2b8a3e,stroke-width:2px;
  classDef location fill:#ffe8cc,stroke:#e8590c,stroke-width:2px;
  classDef setter fill:#fff5f5,stroke:#e03131,stroke-width:2px;

  %% Location atoms
  class locationAtom location;

  %% Query atoms
  class importedCodeQueryAtom query;
  class projectsQueryAtom query;

  %% Storage atoms
  class settingsStoreAtom storage;

  %% Setter
  class setImportUrlAndProjectAtom setter;
  class applySettingsAtom setter;
```
