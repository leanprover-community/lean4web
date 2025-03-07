- [Back to README](../README.md)
- User Manual
- [Installation](./Installation.md)
- [Development](./Development.md)

## Lean4Web Documentation

### URL arguments

The website parses arguments of the form `https://myserver.com/#arg1=value1&arg2=value2`.
The recognised arguments are:

- `code=`: plain text code.
  *(overwrites `codez`; note this argument does accept unescaped code, but the browser will always display certain characters escaped, like `%20` for a space)*
- `codez=`: compressed code using [LZ-string](https://www.npmjs.com/package/lz-string).
- `url=`: a URL where the content is loaded from.
  *(overwrites `code` and `codez`)*.
- `project=`: the Lean project used by the server to evaluate the code. This has to be the name
  of one of the projects defined in the server's config.

The server will automatically only write one of `code`, `codez`, and `url` based on the following
logic:

1. if the code matches the one from the loaded URL, use `url`
2. if the preferences say no comression, use `code`
3. otherwise use `codez` or `code` depending on which results in a shorter URL.
