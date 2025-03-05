describe('The Editor', () => {
  it('displays the version selection', () => {
    cy.visit('/')
    cy.get("nav>div.menu>select[name='leanVersion']").select('stable')
    cy.iframe().contains('stable.lean').should('exist')
    cy.get("nav>*>select[name='leanVersion']").select('mathlib-demo')
    cy.iframe().contains('mathlib-demo.lean').should('exist')
  })

  it('handles unicode correctly', () => {
    cy.visit('/')
    cy.get('div.view-lines').type('\\Omega = \\sum')
    cy.contains('div.view-lines', 'Ω = ∑').should('have.attr', 'style').and('include', 'JuliaMono')
    cy.get('.squiggly-error').should('exist')
    cy.iframe().contains('unexpected identifier; expected command').should('exist')
  })

  it('handles input from url', () => {
    cy.visit('/#codez=pXAAILwoiERA')
    cy.contains('div.view-line', 'Ω = ∑').should('exist')
    cy.get('.squiggly-error').should('exist')
    cy.iframe().contains('unexpected identifier; expected command').should('exist')
  })

  it('loads example correctly on mobile', () => {
    cy.viewport(550, 750)
    cy.visit('/')
    cy.get('.dropdown>.nav-link>.fa-bars').click()
    cy.contains('.dropdown .dropdown', 'Examples').click()
    cy.contains('.nav-link', 'Logic').click()
    cy.containsAll(['import Mathlib.Logic.Basic', 'variable (P Q : Prop)']).should('exist')
  })

  it('loads example correctly on desktop', () => {
    cy.visit('/')
    cy.contains('.nav-link', 'Examples').click()
    cy.contains('.nav-link', 'Logic').click()
    cy.containsAll(['import Mathlib.Logic.Basic', 'variable (P Q : Prop)']).should('exist')
  })

  it('displays correct infoview state', () => {
    cy.visit('/')
    cy.get('div.view-lines').type('example (P: Prop) : P \\or \\not P := by')

    cy.iframe().containsAll([
      'Tactic state',
      '1 goal',
      'P : Prop',
      '⊢ P ∨ ¬P',
      'unexpected end of input'
    ]).should('exist')

    cy.contains('div.view-lines', 'P := by').type('{enter}  exact Classical.em P')
    cy.iframe().containsAll('details', ['Tactic state', 'No goals']).should('exist')
    cy.iframe().contains('details', 'Expected type').should('not.be.open').click()
    cy.iframe().containsAll('details', ['P : Prop', '⊢ Prop']).should('be.open')
  })

  it('displays correct hover tooltips', () => {
    cy.visit('/')
    cy.get('div.view-line').type('example (P: Prop) : P \\or \\not P := by')
    cy.contains('div.view-line span', 'by').realHover()
    cy.contains(
        'div.monaco-hover-content',
        'by tac constructs a term of the expected type by running the tactic(s) tac.'
    ).should('be.visible')
  })

  it('displays and handles code completion', () => {
    cy.visit('/')
    cy.get('div.view-line').type('example (P: Prop) : P \\or \\not P := by appl')
    cy.containsAll('div.monaco-editor', ['by appl', 'apply?']).should('exist')
        .then(() => {
          cy.contains('div.view-line', 'by appl').type('{downArrow}{shift+enter}')
          cy.contains('div.view-line', 'apply?').should('exist')
        })
    cy.get('.squiggly-info').should('exist')
  })

  it('displays and accetps quickfixes inline', () => {
    cy.visit('/')
    cy.get('div.view-line').type('example (P: Prop) : P \\or \\not P := by{enter}  apply?')
    cy.get('.squiggly-info').should('exist').then(() => {
      cy.contains('div.view-line', 'apply?').type('{shift}{alt}.')
    })
    cy.contains('div.view-line', 'exact Classical.em P').should('exist')
  })

  it('displays and accetps suggestions from infoview', () => {
    cy.visit('/')
    cy.get('div.view-line').type('example (P: Prop) : P \\or \\not P := by{enter}  apply?')
    cy.iframe().contains("span[title='Apply suggestion']", 'exact Classical.em P').click()
    cy.contains('div.view-line', 'exact Classical.em P').should('exist')
  })
})
