import { defineConfig } from 'oxfmt'

export default defineConfig({
  ignorePatterns: ['dist/**', '*.min.js', '**/lake-manifest.json'],
  printWidth: 80,
  semi: false,
  singleQuote: true,
})
