const NBSP = String.fromCharCode(160)
const norm = (s: string | null | undefined) => (s ?? '').replace(new RegExp(NBSP, 'g'), ' ')

/** Load the editor with vim mode enabled and `foo foo foo` as content,
 * and wait until the vim keybindings are attached. */
function setupVim() {
  cy.visit('/?vimMode=true#code=foo%20foo%20foo')
  cy.get('.monaco-editor', { timeout: 30000 }).should('exist')
  cy.contains('div.view-line', 'foo foo foo').should('exist')
  cy.get('.vim-status-bar', { timeout: 30000 }).should('be.visible')
  cy.wait(1500)
  // Round-trip through insert mode: proves vim handles keys before we test
  cy.get('.monaco-editor textarea.inputarea').type('i', { force: true })
  cy.get('.vim-status-bar').should('contain.text', '--INSERT--')
  cy.get('.monaco-editor textarea.inputarea').type('{esc}', { force: true })
  cy.get('.vim-status-bar').should('contain.text', '--NORMAL--')
  cy.get('.monaco-editor textarea.inputarea').type('0', { force: true })
}

function firstLine() {
  return cy
    .get('div.view-line')
    .first()
    .then(($el) => norm($el.text()))
}

function openExPrompt(command: string) {
  cy.get('.monaco-editor textarea.inputarea').type(':', { force: true })
  cy.get('.vim-status-bar input').should('exist').type(command, { delay: 50 })
}

describe('Vim mode', () => {
  it('substitutes on the current line with :s', () => {
    setupVim()
    openExPrompt('s/foo/bar/{enter}')
    firstLine().should('eq', 'bar foo foo')
  })

  it('substitutes everywhere with :%s//g', () => {
    setupVim()
    openExPrompt('%s/foo/bar/g{enter}')
    firstLine().should('eq', 'bar bar bar')
  })

  it('supports the confirm flag :%s//gc, answering y, n and a', () => {
    setupVim()
    openExPrompt('%s/foo/bar/gc{enter}')
    cy.get('.vim-status-bar').should('contain.text', 'replace with')
    cy.get('.vim-status-bar input').type('y', { force: true })
    cy.get('.vim-status-bar input').type('n', { force: true })
    cy.get('.vim-status-bar input').type('a', { force: true })
    firstLine().should('eq', 'bar foo bar')
    cy.get('.vim-status-bar').should('not.contain.text', 'replace with')
  })

  it('closes the confirm prompt with Escape', () => {
    setupVim()
    openExPrompt('%s/foo/bar/gc{enter}')
    cy.get('.vim-status-bar').should('contain.text', 'replace with')
    cy.get('.vim-status-bar input').type('{esc}', { force: true })
    cy.get('.vim-status-bar').should('not.contain.text', 'replace with')
    firstLine().should('eq', 'foo foo foo')
  })

  it('replaces a single character with r', () => {
    setupVim()
    cy.get('.monaco-editor textarea.inputarea').type('rX', {
      force: true,
      delay: 100,
    })
    firstLine().should('eq', 'Xoo foo foo')
  })

  it('overwrites text in replace mode (R)', () => {
    setupVim()
    cy.get('.monaco-editor textarea.inputarea').type('R', { force: true })
    cy.get('.vim-status-bar').should('contain.text', '--REPLACE--')
    cy.get('.monaco-editor textarea.inputarea').type('xyz', {
      force: true,
      delay: 100,
    })
    cy.get('.monaco-editor textarea.inputarea').type('{esc}', { force: true })
    firstLine().should('eq', 'xyz foo foo')
  })
})
