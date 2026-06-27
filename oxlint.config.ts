import { defineConfig } from "oxlint";

export default defineConfig({
  categories: {
    correctness: "warn",
    perf: "off",
    style: "off",
    restriction: "off",
    pedantic: "off",
    suspicious: "off",
  },
  rules: {},
});
