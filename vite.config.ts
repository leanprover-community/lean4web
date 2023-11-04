import { defineConfig } from 'vite'
import react from '@vitejs/plugin-react-swc'
import { viteStaticCopy } from 'vite-plugin-static-copy'
import svgr from "vite-plugin-svgr"

// https://vitejs.dev/config/
export default defineConfig({
  plugins: [
    react(),
    svgr({
      svgrOptions: {
        // svgr options
      },
    }),
    {
      name: "configure-response-headers",
      configureServer: (server) => {
        server.middlewares.use((_req, res, next) => {
          res.setHeader("Cross-Origin-Embedder-Policy", "require-corp");
          res.setHeader("Cross-Origin-Opener-Policy", "same-origin");
          next();
        });
      },
    },
    viteStaticCopy({
      targets: [
        {
          src: 'node_modules/@leanprover/infoview/dist/*.production.min.js',
          dest: '.'
        },
        {
          src: 'node_modules/coi-serviceworker/coi-serviceworker.js',
          dest: '.'
        }
      ]
    })],
  publicDir: "client/public",
  server: {
    watch: {
      ignored: "**/bin/**'"
    },
    port: 3000,
    proxy: {
      '/websocket': {
        target: 'ws://localhost:8080',
        ws: true
      },
    }
  },
  resolve: {
    alias: {
      path: "path-browserify",
    },
  },
})
