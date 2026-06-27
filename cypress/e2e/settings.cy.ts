describe("The Settings can be changed for", () => {
  it("custom lead characters", () => {
    cy.visit("/");
    cy.iframe().contains("All Messages (0)").should("exist");
    cy.get(".cgmr.codicon").should("not.exist");
    cy.get(".dropdown>.nav-link>.fa-bars").click();
    cy.contains(".nav-link", "Settings").click();
    cy.get("input#abbreviationCharacter")
      .type("{backspace}$")
      .should("have.value", "$");
    cy.get("button#resetSettings").should("exist");
    cy.get("input#saveSettings").click();

    cy.iframe().contains("All Messages (0)").should("exist");
    cy.get(".cgmr.codicon").should("not.exist");
    cy.get("div.view-line").type(
      "example ($tau) : $tau $or $not $tau := by exact Classical.em $tau ",
    );
    cy.contains(
      "div.view-line",
      "example (τ) : τ ∨ ¬ τ := by exact Classical.em τ",
    ).should("exist");
    cy.iframe()
      .contains("No goals")
      .should("exist")
      .then(() => {
        cy.contains("div.view-line span", "τ").realHover({
          position: "center",
        });
        cy.contains(
          "div.monaco-hover-content",
          "Type τ using $ta or $tau",
        ).should("be.visible");
      });
  });

  it("switching themes", () => {
    cy.visit("/");
    cy.iframe().contains("All Messages (0)").should("exist");
    cy.get(".monaco-editor")
      .should("exist")
      .invoke("css", "background-color")
      .then((oldBg) => {
        cy.get(".dropdown>.nav-link>.fa-bars").click();
        cy.contains(".nav-link", "Settings").click();
        cy.get("select#theme")
          .find("option:last")
          .invoke("val")
          .then((lastVal) => {
            cy.get("select#theme").select(lastVal);
          });
        cy.get("input#saveSettings").click();
        cy.get(".monaco-editor")
          .invoke("css", "background-color")
          .should("not.eq", oldBg);
      });
  });
});
