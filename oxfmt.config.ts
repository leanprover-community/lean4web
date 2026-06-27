import { defineConfig } from 'oxfmt'

export default defineConfig({
  ignorePatterns: ['**/lake-manifest.json'],
  printWidth: 80,
  semi: false,
  singleQuote: true,
})
