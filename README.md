# hashcloak_lean_tutorial

This repository contains the Lean code from HashCloak's [Tutorial: Introduction
to Formal Verification with Lean (Part
1)](https://hashcloak.com/blog/tutorial-introduction-to-formal-verification-with-lean-(part-1)),
with minor explanatory comments.

## Getting started

Requires [`elan`](https://github.com/leanprover/elan).

Initialise the project and include the `mathlib4` library:

```bash
lake +leanprover-community/mathlib4:lean-toolchain new hashcloak_lean_tutorial math
cd hashcloak_lean_tutorial
lake exe cache get
```

Build the code:

```bash
lake build
```
