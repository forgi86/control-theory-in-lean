# CLAUDE.md

This file provides guidance to Claude Code (claude.ai/code) when working with code in this repository.

## What this is

A Lean 4 + Mathlib formalization of control theory, currently focused on discrete-time Lyapunov stability. Toolchain and Mathlib are pinned (`lean-toolchain`, `lakefile.toml`: Mathlib `v4.34.1`). Lake options enforce `relaxedAutoImplicit = false` and the Mathlib standard linter set, so all variables must be declared explicitly.

## Commands

```bash
lake exe cache get                          # fetch precompiled Mathlib (once, or after a Mathlib bump)
lake build                                  # builds the default target: the ControlTheory library
lake build ControlTheory.LyapunovStability  # build a single library module
lake env lean Examples/DTLyapunov.lean      # check a standalone file (Examples/ is NOT a lake target)
```

There is no test suite: "passing" means the file compiles with no errors and no `sorry`. CI (`.github/workflows`) runs `lean-action` (i.e. `lake build`) plus docgen on every push/PR.

## Layout and architecture

- `ControlTheory/` — the reusable library (the only lake `lean_lib`). The root `ControlTheory.lean` (repo top level, as Lake requires) imports every module; **add new modules there** or they won't be built.
  - `ComparisonFunctions.lean` (namespace `Comparison`) — foundation layer: `ClassK`, `ClassKInfty` (which `extends ClassK`) as `Prop`-valued structures on `ℝ → ℝ`, with order/positivity lemmas and `ClassKInfty.exists_inverse`. Depends only on Mathlib.
  - `LyapunovStability.lean` (namespace `Lyapunov`) — Theorem B.13 (Lyapunov ⇒ classical GAS) with `X = E`.
  - `LyapunovStabilityConstrained.lean` (namespace `Lyapunov`) — the same theorem restricted to a positive-invariant set `X`, with `…On`-suffixed definitions/theorems. Deliberately does **not** import the unconstrained file; the two developments are parallel, not layered, and share a namespace (so names must not collide).
- `Examples/` — self-contained didactic proofs (each defines its own `ClassK`, `IsStableEpsDelta`, etc. and imports only Mathlib, so they are copy-pasteable into the Lean web playground). Don't refactor them to depend on `ControlTheory/`.
- `doc/AppendixB.md` — the authoritative, self-contained transcription of Rawlings, Mayne & Diehl, *Model Predictive Control* (2nd ed.), Appendix B (Defs B.3–B.12, Thms B.13/B.15, Lemma B.14). Formalize library results from the statements there; Lean docstrings cite these B-numbers. (`doc/` also holds the book PDF; `doc/` and `tmp/` are untracked.)
- `sketch.lean`, `tmp/` — scratch files, not part of the build.

### Key design choice: abstract distance `dA`

Stability notions and `IsLyapunov` are parameterized by an abstract nonnegative `dA : E → ℝ` ("distance to the target set") instead of `‖x‖` or `Metric.infDist x A`. Consequently the core theorems need no topology on `E` (`E : Type*`); all analysis happens in `ℝ` on values of `V` and `dA`. Concrete cases are thin corollaries at the bottom of each file (`*_origin` with `dA := ‖·‖`, `*_set` with `dA := Metric.infDist · A`). Follow this pattern for new stability results.

Conventions visible in the code: trajectories are `f^[i] x` (`Function.iterate`); Lyapunov hypotheses are bundled in a `structure … : Prop` with fields named after the book equations (`lower` (B.8), `upper` (B.9), `decrease` (B.10)); the decrease rate `α₃` is continuous positive-definite, not class 𝒦.

## Planned work (from README)

More discrete-time variants (local/global/asymptotic, 𝒦ℒ form — Theorem B.15 / Lemma B.14), and completing the continuous-time proof in `Examples/CTLyapunov.lean`, which currently *assumes* ODE solution existence.
