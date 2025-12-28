- [Back to README](../README.md)
- [User Manual](./Usage.md)
- [Installation](./Installation.md)
- [Development](./Development.md)
- [Troubleshoot](./Troubleshoot.md)

## Troubleshoot

This is a (not well-maintained) collection of issues which have been reported.

- If you get the following error:
  ```
  bwrap: loopback: Failed RTM_NEWADDR: Operation not permitted
  bwrap: setting up uid map: Permission denied
  ```
  follow these instructions:
  https://etbe.coker.com.au/2024/04/24/ubuntu-24-04-bubblewrap/
- It seems the project cannot be run using bubblewrap from inside `/tmp`. This issue has not been investigated further as the solution seems to be to just move the project anywhere else.
