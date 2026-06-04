# Control Theory in Lean

Formal proof assistants like [Lean](https://lean-lang.org/learn/) are reshaping mathematics: a proof is accepted
only when every step is verified, so nothing informal survives. The payoff is twofold:
* Humans get a single, unambiguous, fully-proved reference.
* AI agents can search for proofs without hallucinating

Control theory has barely started. Even foundational concepts like Lyapunov stability 
are absent from formal verification libraries.


> *Ever read a control paper, reached a theorem, and suspected a hypothesis was
> quietly missing? In Lean a proof won't compile until every step is spelled out, so the truth
> is on the table. Gaps have nowhere to hide.*

> *Ever looked for the discrete-time version of a theorem and found only "left as
> an exercise"? If you feel lazy, ask an AI to fill the gap and give you the Lean code. But whether the
> proof is right or wrong, you will know it. No hiding.*

## What's in this repo

A few Lyapunov stability theorems verified in Lean.

| Theorem | Notes | File |
|---------|-------|------|
| Continuous-time Lyapunov stability | After Khalil (2002), Theorem 4.1; ODE-solution existence is *assumed*, not yet proved. | `CTLyapunov.lean` |
| Discrete-time Lyapunov stability | Based on Khalil (2002) Theorem 4.1, adapted to discrete time with an additional sublevel-trapping hypothesis | `DTLyapunov.lean` |
| Discrete-time Lyapunov stability | Modern class-𝒦 comparison-function formulation | `DTLyapunovComparisonFunctions.lean` |


## TODO 

- Prove more discrete-time Lyapunov theorem variants - local, global, asymptotic stability...
- Complete the continuous-time Lyapunov stability proof. Requires Khalil (2002)'s Theorem 3.3
  - May not be easy, ODE theory is not yet fully developed in Lean.
- ...


## Build

For a quick look without installing anything, try the
[Lean 4 online playground](https://live.lean-lang.org). Copy-paste any `.lean`
file there and see the proofs compile (Mathlib version may differ slightly from
this repo - minor compatibility issues are possible).

For local development, follow the [Mathlib setup guide](https://leanprover-community.github.io/get_started.html),
then in the project folder run:

```bash
lake exe cache get # fetch precompiled Mathlib — do this once
lake build
```
## References

- H. K. Khalil, *Nonlinear Systems*, 3rd ed. Prentice Hall, 2002.

*Early research prototype — corrections and work on the gaps above are welcome.*
