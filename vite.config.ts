import { defineConfig } from 'vite'
import react from '@vitejs/plugin-react-swc'
import { viteStaticCopy } from 'vite-plugin-static-copy'
import path from "path-browserify"

// https://vitejs.dev/config/
export default defineConfig({
  plugins: [
    react(),
    viteStaticCopy({
      targets: [
        {
          src: 'node_modules/@leanprover/infoview/dist/*.production.min.js',
          dest: '.'
        }
      ]
    })],
  publicDir: "client/public",
  server: {
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
