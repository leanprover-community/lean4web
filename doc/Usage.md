- [Back to README](../README.md)
- User Manual
- [Installation](./Installation.md)
- [Development](./Development.md)
- [Troubleshoot](./Troubleshoot.md)

## Lean4Web Documentation

### URL arguments

The website parses arguments of the form `https://myserver.com/#arg1=value1&arg2=value2`.
The recognised arguments are:

- `code=`: plain text code.
  _(overwrites `codez`; note this argument does accept unescaped code, but the browser will always display certain characters escaped, like `%20` for a space)_
- `codez=`: compressed code using [LZ-string](https://www.npmjs.com/package/lz-string).
- `url=`: a URL where the content is loaded from.
  _(overwrites `code` and `codez`)_.
- `project=`: the Lean project used by the server to evaluate the code. This has to be the name
  of one of the projects defined in the server's config.

The server will automatically only write one of `code`, `codez`, and `url` based on the following
logic:

1. if the code matches the one from the loaded URL, use `url`
2. if the preferences say no comression, use `code`
3. otherwise use `codez` or `code` depending on which results in a shorter URL.

### URL parameters (TODO: restore behaviour)

Besides storing the settings in a cookie through the settings interface, there is an option to specify them in the form `https://myserver.com/?setting1=value1&setting2=value2#[arguments as above]`
When a setting is not provided as URL parameter, the value from the browser store (or the default) is used.

The recognised settings are:

- Boolean settings (`true` or `false`):
  - `acceptSuggestionOnEnter`: accept code editors suggestions on `Enter`. default: `false`
  - `compress`: compress code in URL. default: `true`
  - `mobile`: display code editor and infoview in narrow, vertically stacked, mobile-friendly mode. default: not set, i.e. inferred
  - `showGoalNames`: show goal names in Lean infoview box. default: `true`
  - `showExpectedType`: expected type in Lean infoview opened by default. default: `false`
  - `wordWrap`: wrap code in editor box. default: `true`
- Non-boolean settings:
- `abbreviationCharacter`: lead character for unicode abbreviations. values: a character. default: `\`
- `theme`: selection between one light and dark theme. More themes are available in the settings, but they cannot be set through the URL. values: `light` or `dark`. default: `light` (TODO: infererred from browser)
