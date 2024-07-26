import { defineConfig } from 'vite'
import react from '@vitejs/plugin-react-swc'
import { nodePolyfills } from 'vite-plugin-node-polyfills'
import importMetaUrlPlugin from '@codingame/esbuild-import-meta-url-plugin'
import { viteStaticCopy } from 'vite-plugin-static-copy'
import { normalizePath } from 'vite'
import path from 'node:path'
import svgr from "vite-plugin-svgr"


// https://vitejs.dev/config/
export default defineConfig({
  optimizeDeps: {
    esbuildOptions: {
      plugins: [importMetaUrlPlugin]
    }
  },
  build: {
    // Relative to the root
    // Note: This has to match the path in `server/index.mjs` and in `tsconfig.json`
    outDir: 'client/dist',
  },
  plugins: [
    react(),
    svgr({
      // svgr options: https://react-svgr.com/docs/options/
      svgrOptions: { exportType: "default", ref: true, svgo: false, titleProp: true },
       include: "**/*.svg",
      }),
    nodePolyfills({
      overrides: {
        fs: 'memfs',
      },
    }),
    viteStaticCopy({
      targets: [
        {
          src: normalizePath(path.resolve(__dirname, './node_modules/@leanprover/infoview/dist/*.production.min.js')),
          dest: 'infoview'
        }
      ]
    })
  ],
  publicDir: "client/public",
  server: {
    port: 3000,
    proxy: {
      '/websocket': {
        target: 'ws://localhost:8080',
        ws: true
      },
      '/examples': {
        target: 'http://localhost:8080',
      },
    }
  },
  resolve: {
    alias: {
      path: "path-browserify",
      '@leanprover/infoview/loader': path.resolve(__dirname, './node_modules/@leanprover/infoview/dist/loader.production.min.js')
    },
  },
})
