import { defineConfig } from "cypress";

// default timeout was 4000.
// Infoview loading is slow on Windows…

export default defineConfig({
    defaultCommandTimeout: 40000,
    e2e: {
        video: true,
        baseUrl: "http://localhost:3000",
        setupNodeEvents(on, config) {
            // implement node event listeners here
        },
    },
});