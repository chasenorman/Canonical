# Canonical

[Canonical](https://chasenorman.com) exhaustively searches for terms in dependent type theory. 

https://github.com/user-attachments/assets/ec13ad85-7d09-4a32-9c73-3b5b501722a4

This respository contains the Rust source code for Canonical. A pre-built version of Canonical is packaged with the [`canonical` Lean tactic](https://github.com/chasenorman/CanonicalLean)

## Project Structure

- `canonical-compat` — The compatiblity layer for Canonical, defining the intermediate representation (IR) of the input format.
- `canonical-core`
    - `core.rs` — The type theory of Canonical, with terms, types, metavariables, and explicit substitutions.
    - `heuristic.rs` — Functions for calculating the entropy metric and metavariable refinement ordering.
    - `prover.rs` — Parallelized iterative-deepening DFS.
    - `search.rs` — Utilities for computing entropy, selecting the next metavariable, and testing assignments.
- `canonical-lean` — Bindings for interfacing with the Lean FFI.

## Build Lean dynlib

Build the Lean project in the `lean` directory by opening it in VSCode. This downloads the pre-built [`Canonical` Lean package](https://github.com/chasenorman/CanonicalLean).

Run `python3 build_lean.py` to update the dynlib for your platform with a newly compiled version. 

For more detailed information about compiling on different platforms, check `.github/workflows`.