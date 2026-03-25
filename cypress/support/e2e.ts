import "./assertions";
import "./commands";
import "cypress-iframe";
import "cypress-real-events";

Cypress.on("uncaught:exception", (err, runnable) => {
  // returning false here prevents Cypress from
  // failing the test
  return false;
});
