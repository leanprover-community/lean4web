describe("The Editor", () => {
  it("displays the version selection", () => {
    cy.visit("/");
    cy.get("nav>*>select[name='leanVersion']").select("MathlibDemo");
    cy.iframe().contains("MathlibDemo.lean").should("exist");
    cy.get(".dropdown>.nav-link>.fa-bars").click();
    cy.contains(".nav-link", "Lean Info").click();
    cy.containsAll(".modal", [
      "MathlibDemo",
      "leanprover/lean4",
      "mathlib",
      "aesop",
    ])
      .find(".modal-close")
      .click();

    cy.get("nav>*>select[name='leanVersion']").select("Stable");
    cy.iframe().contains("Stable.lean").should("exist");
    cy.get(".dropdown>.nav-link>.fa-bars").click();
    cy.contains(".nav-link", "Lean Info").click();
    cy.containsAll(".modal", ["leanprover/lean4:stable", "(no dependencies)"])
      .find(".modal-close")
      .click();
  });

  it("handles unicode correctly", () => {
    cy.visit("/");
    cy.get("div.view-lines").type("\\Omega = \\sum");
    cy.contains("div.view-lines", "Ω = ∑")
      .should("have.attr", "style")
      .and("include", "JuliaMono");
    cy.get(".squiggly-error").should("exist");
    cy.iframe()
      .contains("unexpected identifier; expected command")
      .should("exist");
  });

  it("handles input from url", () => {
    cy.visit("/#codez=pXAAILwoiERA");
    cy.contains("div.view-line", "Ω = ∑").should("exist");
    cy.get(".squiggly-error").should("exist");
    cy.iframe()
      .contains("unexpected identifier; expected command")
      .should("exist");
  });

  it("loads example correctly on mobile", () => {
    cy.viewport(550, 750);
    cy.visit("/");
    cy.get(".dropdown>.nav-link>.fa-bars").click();
    cy.contains(".dropdown .dropdown", "Examples").click();
    cy.contains(".nav-link", "Logic").click();
    cy.containsAll([
      "import Mathlib.Logic.Basic",
      "variable (P Q : Prop)",
    ]).should("exist");
  });

  it("loads example correctly on desktop", () => {
    cy.visit("/");
    cy.contains(".nav-link", "Examples").click();
    cy.contains(".nav-link", "Logic").click();
    cy.containsAll([
      "import Mathlib.Logic.Basic",
      "variable (P Q : Prop)",
    ]).should("exist");
  });

  it("displays correct infoview state", () => {
    cy.visit("/");
    cy.get("div.view-lines").type("example (P: Prop) : P \\or \\not P := by ");

    cy.iframe()
      .containsAll([
        "Tactic state",
        "1 goal",
        "P : Prop",
        "⊢ P ∨ ¬P",
        "unexpected end of input",
      ])
      .should("exist");

    cy.contains("div.view-lines", "P := by").type("exact Classical.em P");
    cy.iframe()
      .containsAll("details", ["Tactic state", "No goals"])
      .should("exist");
    cy.iframe()
      .contains("details", "Expected type")
      .should("not.be.open")
      .click();
    cy.iframe()
      .containsAll("details", ["P : Prop", "⊢ Prop"])
      .should("be.open");
  });

  it("displays correct hover tooltips", () => {
    cy.visit(
      "/#codez=KYDwhgtgDgNsAEAKACgLnsgTgeygSnnWXkAoieAGo0IF54AjAT3lDAGMAXeAYRjAGc+AS1ZgYAOmAQMQA",
    );
    cy.iframe().contains("Expected type").should("exist");
    cy.get(".cgmr.codicon").should("not.exist");
    cy.get("div.view-lines").realClick();
    cy.iframe().contains("No goals").should("exist");

    cy.contains("div.view-line span", "example")
      .should("exist")
      .then(($el) => cy.wrap($el).realHover());
    cy.contains(
      "div.monaco-hover-content",
      "_example (P : Prop) : P ∨ ¬P",
    ).should("be.visible");

    cy.contains("div.view-line span", "by")
      .should("exist")
      .then(($el) => cy.wrap($el).realHover());
    cy.contains(
      "div.monaco-hover-content",
      "by tac constructs a term of the expected type by running the tactic(s) tac.",
    ).should("be.visible");
  });

  it("displays and handles code completion", () => {
    cy.visit("/");
    cy.iframe().contains("All Messages (0)").should("exist");
    cy.get(".cgmr.codicon").should("not.exist");
    cy.get("div.view-line").type(
      "example (P: Prop) : P \\or \\not P := by appl",
      { delay: 100 },
    );
    cy.containsAll("div.monaco-editor", ["by appl", "apply?"])
      .should("exist")
      .then(() => {
        cy.contains("div.view-line", "by appl").type(
          "{downArrow}{shift+enter}",
          { delay: 100 },
        );
        cy.contains("div.view-line", "apply?").should("exist");
      });
    cy.get(".squiggly-info").should("exist");
  });

  it("displays and accepts quickfixes inline", () => {
    const modBtn = Cypress.platform === "darwin" ? "Meta" : "Control";
    cy.visit("/");
    cy.get("div.view-line").type(
      "example (P: Prop) : P \\or \\not P := by apply?",
    );
    cy.contains("div.view-line", "apply?").should("exist");
    cy.get(".squiggly-info").should("exist");
    cy.get(".codicon-gutter-lightbulb").should("be.visible");
    cy.realPress([modBtn, "."]);
    cy.contains(".action-widget", "Try this: exact Classical.em P").should(
      "exist",
    );
    cy.realPress([modBtn, "."]);
    cy.contains("div.view-line", "exact Classical.em P").should("exist");
  });

  it("displays and accepts suggestions from infoview", () => {
    cy.visit("/");
    cy.get("div.view-line").type(
      "example (P: Prop) : P \\or \\not P := by apply?",
    );
    cy.iframe().contains("span[title='Apply suggestion']", "[apply]").click();
    cy.contains("div.view-line", "exact Classical.em P").should("exist");
  });

  it("loads from Zulip message on desktop", () => {
    cy.fixture("zulip-msg-1.txt").as("zulipMsg");
    cy.visit("/");
    cy.frameLoaded();
    cy.contains(".nav-link", "Load").click();
    cy.contains(".nav-link", "Load Zulip Message").click();
    cy.get("@zulipMsg")
      .should("include", "An example snippet")
      .then(($msg) => {
        cy.get(".modal>form>textarea")
          .invoke("val", $msg)
          .then(() => {
            cy.get(".modal>form>input[value='Parse message']")
              .should("exist")
              .click();
          });
      });
    cy.containsAll(".view-lines", [
      "#eval Lean.toolchain",
      "#check Classical.em",
    ]).should("exist");
    cy.iframe().contains("Restart File").should("exist").click();
    cy.iframe().contains("details", "All Messages (2)").should("exist").click();
    cy.iframe()
      .containsAll("body", [
        "All Messages (2)",
        "leanprover/lean4",
        "Classical.em (p : Prop) : p ∨ ¬p",
      ])
      .should("exist");
  });

  it("shows correct go-to definitions", () => {
    const isOnDarwin = Cypress.platform === "darwin";
    const alertShown = cy.stub().as("alertShown");
    cy.on("window:confirm", alertShown);
    cy.visit("/");
    cy.get("div.view-line").type(
      "import Mathlib.Logic.Basic #check Classical.em",
    );
    cy.get(".squiggly-info");

    // Click on theorem
    cy.contains("div.view-line span", "Classical.em").realClick({
      ctrlKey: !isOnDarwin,
      metaKey: isOnDarwin,
    });
    cy.get("@alertShown")
      .should("have.been.calledOnce")
      .and(
        "have.been.calledWithMatch",
        /Do you want to open the docs\?\s+\/Init\/Classical/gm,
      );

    // Click on import
    cy.contains("div.view-line span", "Mathlib.Logic.Basic").realClick({
      ctrlKey: !isOnDarwin,
      metaKey: isOnDarwin,
    });
    cy.get("@alertShown").should("have.been.calledTwice");
  });
});
