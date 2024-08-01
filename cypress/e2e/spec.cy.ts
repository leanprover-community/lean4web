describe('Editor Test', () => {
  it('displays the editor', () => {
    cy.visit('http://localhost:5173/')
    cy.contains('#check 0')
      .should(($p) => {
        // ...
        expect(getComputedStyle($p.get(0)).fontFamily).to.match(/^JuliaMono/)
      })
  })

  it('displays the infoview', () => {
    cy.visit('http://localhost:5173/')
    cy.get('.squiggly-info')
    cy.iframe().contains('0 : Nat')
  })

  it('changes themes', () => {
    cy.visit('http://localhost:5173/')
    cy.get('[data-cy="theme-light"]').click()
    cy.contains('#check 0')
      .should(($p) => {
        expect(getComputedStyle($p.get(0)).getPropertyValue('--vscode-editor-background')).to.equal("#ffffff")
      })
    cy.get('[data-cy="theme-dark"]').click()
    cy.contains('#check 0')
      .should(($p) => {
        expect(getComputedStyle($p.get(0)).getPropertyValue('--vscode-editor-background')).to.equal("#1e1e1e")
      })

    cy.get('iframe').should('have.length', 1)
  })

  it('inputs unicode', () => {
    cy.visit('http://localhost:5173/')
    cy.get('[data-cy="leader-backslash"]').click()
    cy.contains('#check 0').click("left")
    cy.get('body').type('\\alpha')
    cy.contains('α')
    cy.get('[data-cy="leader-comma"]').click()
    cy.contains('α#check 0').click("left")
    cy.get('body').type(',beta')
    cy.contains('βα#check 0')
  })

  it('allows for multiple editors', () => {
    cy.visit('http://localhost:5173/')
    cy.contains('#check 0')
    cy.get('[data-cy="number-editors"]').type('{selectall}').type('2')
    cy.contains('#check 1')
    cy.contains('#check 0')
    cy.get('.squiggly-info')
    cy.contains('#check 1').click()
    cy.iframe().contains('1 : Nat')
    cy.contains('#check 0').click()
    cy.iframe().contains('0 : Nat')
  })
})