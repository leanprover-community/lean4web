- [Back to README](../README.md)
- [User Manual](./Usage.md)
- [Installation](./Installation.md)
- Server Maintenance
- [Adding Projects](./Projects.md)
- [Development](./Development.md)
- [Troubleshoot](./Troubleshoot.md)

# Notes for server maintenance

We use `Nginx` and `pm2` to manage our server.

(TODO: details)

## Cronjob: updating Lean projects

Optionally, you can set up a cronjob to regularly update the Lean projects.
To do so, run

```
crontab -e
```

and add the following lines, where all paths must be adjusted appropriately:

```
# Need to set PATH manually:
SHELL=/usr/bin/bash
PATH=/usr/local/sbin:/usr/local/bin:/sbin:/bin:/usr/sbin:/usr/bin:/home/USER/.elan/bin:/home/USER/.nvm/versions/node/v20.8.0/bin/

# Update server (i.e. mathlib) of lean4web and delete mathlib cache
*  */6 * * * cd /home/USER/lean4web && npm run build:server 2>&1 1>/dev/null | logger -t lean4web
40 2   * * * rm -rf /home/USER/.cache/mathlib/
```

## Managing toolchains

Running and updating the server periodically might accumulate Lean toolchains.

To delete unused toolchains automatically, you can use the
[elan-cleanup tool](https://github.com/JLimperg/elan-cleanup) and set up a
cron-job with `crontab -e` and adding the following line, which runs once a month and
deletes any unused toolchains:

```
30 2 1 * * /PATH/TO/elan-cleanup/build/bin/elan-cleanup | logger -t lean-cleanup
```

You can see installed lean toolchains with `elan toolchain list`
and check the size of `~/.elan`.
