import { defineConfig } from 'oxlint'

export default defineConfig({
  plugins: ['react', 'react-perf', 'jsx-a11y'],
  categories: {
    correctness: 'warn',
    perf: 'off',
    style: 'off',
    restriction: 'off',
    pedantic: 'off',
    suspicious: 'off',
  },
  rules: {},
})
