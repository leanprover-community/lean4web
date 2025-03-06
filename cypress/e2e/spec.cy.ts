describe('The Editor', () => {
  it('displays the version selection', () => {
    cy.visit('/')
    cy.get("nav>*>select[name='leanVersion']").select('mathlib-demo')
    cy.iframe().contains('mathlib-demo.lean').should('exist')
    cy.get('.dropdown>.nav-link>.fa-bars').click()
    cy.contains('.nav-link', 'Lean Info').click()
    cy.containsAll('.modal', [
      'mathlibLatest',
      'leanprover/lean4',
      'mathlib',
      'aesop'
    ]).find('.modal-close').click()

    cy.get("nav>*>select[name='leanVersion']").select('stable')
    cy.iframe().contains('stable.lean').should('exist')
    cy.get('.dropdown>.nav-link>.fa-bars').click()
    cy.contains('.nav-link', 'Lean Info').click()
    cy.containsAll('.modal', [
      'leanprover/lean4:stable',
      '(no dependencies)'
    ]).find('.modal-close').click()
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
    cy.get('div.view-line').type('example (P: Prop) : P \\or \\not P := by appl', { delay: 100 })
    cy.containsAll('div.monaco-editor', ['by appl', 'apply?']).should('exist')
        .then(() => {
          cy.contains('div.view-line', 'by appl').type('{downArrow}{shift+enter}', { delay: 100 })
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

  it('loads from Zulip message on desktop', () => {
    cy.fixture('zulip-msg-1.txt').as('zulipMsg')
    cy.visit('/')
    cy.frameLoaded()
    cy.contains('.nav-link', 'Load').click()
    cy.contains('.nav-link', 'Load Zulip Message').click()
    cy.get('@zulipMsg').should('include', 'An example snippet').then(($msg) => {
      cy.get('.modal>form>textarea').invoke('val', $msg).then(() => {
        cy.get(".modal>form>input[value='Parse message']").should('exist').click()
      })
    })
    cy.containsAll('.view-lines', ['#eval Lean.toolchain', '#check Classical.em']).should('exist')
    cy.iframe().contains('Restart File').should('exist').click()
    cy.iframe().contains('details', 'All Messages (2)').should('exist').click()
    cy.iframe().containsAll('body', [
      'All Messages (2)',
      'leanprover/lean4',
      'Classical.em (p : Prop) : p ∨ ¬p'
    ]).should('exist')
  })

  it('shows correct go-to definitions', () => {
    const alertShown = cy.stub().as("alertShown")
    cy.on('window:confirm', alertShown)
    cy.visit('/')
    cy.get('div.view-line').type('#check Classical.em')
    cy.contains('div.view-line span', 'Classical.em').as('defToCheck').should('exist')
    cy.get('@defToCheck').click({ctrlKey: true})
    cy.get("@alertShown").should("have.been.calledOnce")
        .and('have.been.calledWithMatch', /Do you want to open the docs\?\s+\/Init\/Classical/gm)
  })

  it('handles custom lead character', () => {
    cy.visit('/')
    cy.get('.cgmr.codicon').as('glyphWarnings').should('not.exist')
    cy.iframe().contains('All Messages (0)').should('exist')
    cy.get('.dropdown>.nav-link>.fa-bars').click()
    cy.contains('.nav-link', 'Settings').click()
    cy.get('input#abbreviationCharacter').type(`{backspace}\${enter}`)
    cy.get('@glyphWarnings').should('not.exist')
    cy.iframe().contains('All Messages (0)').should('exist')
    cy.get('div.view-line').type('example ($tau) : $tau $or $not $tau := by exact Classical.em $tau ')
    cy.contains('div.view-line', 'example (τ) : τ ∨ ¬ τ := by exact Classical.em τ').should('exist')
    cy.iframe().contains('No goals').should('exist').then(() => {
      cy.contains('div.view-line span', 'τ').realHover({ position: "center" })
      cy.contains(
          'div.monaco-hover-content',
          'Type τ using $ta or $tau'
      ).should('be.visible')
    })
  })

  it('can switch themes', () => {
    cy.visit('/')
    cy.iframe().contains('All Messages (0)').should('exist')
    cy.get('.monaco-editor').should('exist').then(($editor) => {
      const oldBg = $editor.css('background-color')
      cy.get('.dropdown>.nav-link>.fa-bars').click()
      cy.contains('.nav-link', 'Settings').click()
      cy.get("select#theme option").not(':selected').first().invoke('val').then(($newVal) => {
        cy.get("select#theme").select($newVal).should(() => {
          const newBg = $editor.css('background-color')
          expect(newBg).to.not.eq(oldBg)
        })
      })
    })
  })
})
