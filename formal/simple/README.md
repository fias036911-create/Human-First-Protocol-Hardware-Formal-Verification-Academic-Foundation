Formal example — tiny NuSMV model

This folder contains a minimal NuSMV model (`model.smv`) and a short guide to run it with `nusmv`.

Files

- `model.smv` — a small state machine with an LTL/CTL property.

Run with NuSMV

```sh
# install on Ubuntu: sudo apt install nusmv
nusmv model.smv
```

The model and property are intentionally tiny; use this folder as a template for adding formal properties and scripts.
