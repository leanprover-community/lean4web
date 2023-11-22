# Themes

You can use monaco themes to style the lean webeditor. Take a look at these
[sample monaco themes](https://github.com/brijeshb42/monaco-themes/tree/master/themes).

You can directly load custom themes in the settings. The upload expects a valid JSON monaco theme.

To add a theme to the editor permanently, you need two steps:

1. Add the json file here (in the `themes` folder)
2. Add an `option` to the `select` in `Settings.tsx`. Make sure that the `value` of the `option` matches the filename (without '.json')!

Now you can select the theme from the Settings.

## Used variables

Here is a list of some variables from the theme which are used for the editor interface:

* The top bar and menu use the `--vscode-menu-XXX` variables.
* The pop-ups (loading, settings, etc.) use `--vscode-input-XXX` and `--vscode-button-XXX`
* `--vscode-textPreformat-foreground` is used for code in pop-ups.
* `--vscode-textLink-foreground` is used for links in pop-ups.
* `--vscode-editorError-foreground` is used for error message in pop-ups.
* `--vscode-background` is used for the website's background.
* `--vscode-inputOption-activeForeground` and `--vscode-widget-shadow` are also used.
