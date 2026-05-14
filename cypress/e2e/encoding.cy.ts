describe("", () => {
  it("changing projects with uncompressed code should preserve the code", () => {
    const payload = "def foo := 1 + 2";
    cy.visit("/");

    // disable compression in the settings
    cy.get(".dropdown>.nav-link>.fa-bars").click();
    cy.contains(".nav-link", "Settings").click();
    cy.get("input#compress")
      .should("be.checked")
      .click()
      .should("not.be.checked");
    cy.get("input#saveSettings").click();

    // type payload
    cy.get("div.view-lines").type(payload);

    // change project
    cy.get("nav>*>select[name='leanVersion']").select("Stable Lean");
    cy.url().should("include", "project=Stable");

    // test
    cy.contains("div.view-line", payload).should("exist");
  });
});
