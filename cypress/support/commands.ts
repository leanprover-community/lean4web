Cypress.Commands.add(
  "map",
  { prevSubject: true },
  (subject: unknown[], iteratee) => {
    return cy.wrap(Cypress._.map(subject, iteratee), { log: false });
  },
);

const containsAllFn: Cypress.ContainsAllFn = (
  subject,
  selector,
  contents,
  options,
) => {
  if (Cypress._.isArray(selector)) {
    options = contents as Cypress.ContainsAllOptions;
    contents = selector;
    selector = "body";
  }
  subject = subject || cy.$$(selector);

  return contents.reduce(
    (chain, content) => {
      return chain.contains(selector, content, options);
    },
    cy.wrap(subject, options),
  );
};

Cypress.Commands.add(
  "containsAll",
  { prevSubject: ["optional", "element"] },
  containsAllFn,
);
