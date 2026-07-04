import Mathlib

open Set Filter

/-!
# Comparison functions (class 𝒦 and 𝒦∞)

Reusable foundation for discrete-time Lyapunov stability, following
Definition B.3 of Rawlings, Mayne & Diehl, *Model Predictive Control*, 2nd ed.

This module is **self-contained**: it depends only on Mathlib, and both the
classical (Theorem B.13) and 𝒦ℒ (Theorem B.15) developments import it.

Scope is deliberately limited to what Theorem B.13 consumes: the two structures,
their basic order/positivity properties, and the 𝒦∞ inverse. The general
composition / min / max closure lemmas (appendix B.1–B.5) are intentionally
omitted here.

Everything substantive is `sorry`-stubbed. `monotoneOn`, `lt_iff`, and
`apply_nonneg` are proved as worked examples to fix the calling conventions;
prove the rest one lemma at a time.
-/

namespace Comparison

/-- A comparison function of class 𝒦: zero at zero, continuous and strictly
increasing on `[0, ∞)`. -/
structure ClassK (α : ℝ → ℝ) : Prop where
  zero : α 0 = 0
  cont : ContinuousOn α (Ici 0)
  mono : StrictMonoOn α (Ici 0)

/-- A comparison function of class 𝒦∞: class 𝒦 and radially unbounded
(`α s → ∞` as `s → ∞`).

Encoded with an explicit `toClassK` field rather than `extends` to keep the
skeleton unambiguous; feel free to refactor to `extends ClassK α` for nicer
projection ergonomics once things compile. -/
structure ClassKInfty (α : ℝ → ℝ) : Prop where
  toClassK : ClassK α
  unbounded : Tendsto α atTop atTop

namespace ClassK

variable {α : ℝ → ℝ}

/-- On `[0, ∞)`, a class-𝒦 function is (nonstrictly) monotone.
*Worked example — fixes the `StrictMonoOn.monotoneOn` idiom.* -/
theorem monotoneOn (h : ClassK α) : MonotoneOn α (Ici 0) :=
  h.mono.monotoneOn

/-- Order-reflecting (strict): on `[0, ∞)`, `α a < α b ↔ a < b`.
*Worked example — fixes the `mem_Ici.mpr` argument pattern.* -/
theorem lt_iff (h : ClassK α) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    α a < α b ↔ a < b :=
  h.mono.lt_iff_lt (mem_Ici.mpr ha) (mem_Ici.mpr hb)

/-- A class-𝒦 function is nonnegative on `[0, ∞)`.
*Worked example — monotone from `0` plus `α 0 = 0`.* -/
theorem apply_nonneg (h : ClassK α) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ α s := by
  have h0 : α 0 ≤ α s := h.monotoneOn (mem_Ici.mpr le_rfl) (mem_Ici.mpr hs) hs
  rwa [h.zero] at h0

/-- Order-reflecting (nonstrict): on `[0, ∞)`, `α a ≤ α b ↔ a ≤ b`.
Hint: `StrictMonoOn.le_iff_le`. -/
theorem le_iff (h : ClassK α) {a b : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) :
    α a ≤ α b ↔ a ≤ b :=
  h.mono.le_iff_le (mem_Ici.mpr ha) (mem_Ici.mpr hb)

/-- A class-𝒦 function is strictly positive on `(0, ∞)`. -/
theorem apply_pos (h : ClassK α) {s : ℝ} (hs : 0 < s) : 0 < α s := by
  sorry

/-- Near `0`, a class-𝒦 function takes values below any positive target.
Used both for the stability `δ` and for the final squeeze in B.13.
Hint: `ContinuousWithinAt` of `α` at `0` within `Ici 0`, via `h.cont`. -/
theorem exists_pos_lt (h : ClassK α) {t : ℝ} (ht : 0 < t) :
    ∃ δ > 0, α δ < t := by
  sorry

end ClassK

namespace ClassKInfty

variable {α : ℝ → ℝ}

/-- Convenience re-exports so 𝒦∞ facts read directly off a `ClassKInfty`. -/
theorem zero (h : ClassKInfty α) : α 0 = 0 := h.toClassK.zero

theorem mono (h : ClassKInfty α) : StrictMonoOn α (Ici 0) := h.toClassK.mono

theorem apply_nonneg (h : ClassKInfty α) {s : ℝ} (hs : 0 ≤ s) : 0 ≤ α s :=
  h.toClassK.apply_nonneg hs

/-- **The 𝒦∞ inverse.** A class-𝒦∞ function, restricted to `[0, ∞)`, is a
continuous strictly-increasing bijection of `[0, ∞)` onto itself, so it has a
class-𝒦∞ inverse that is a genuine two-sided inverse on `[0, ∞)`.

This is the one substantial construction in the module: it underlies every
appearance of `α₁⁻¹` and `α₂⁻¹` in the B.13 / B.15 proofs.

Proof outline:
* strict mono + `α 0 = 0` + `Tendsto α atTop atTop` ⇒ `α '' Ici 0 = Ici 0`
  (surjectivity onto `[0, ∞)`; needs `intermediate_value_Ici`-style continuity);
* build `β` via the monotone inverse on `Ici 0`
  (`StrictMonoOn.orderIsoOfSurjective` / `Set.InjOn.invFunOn`);
* transport continuity of the inverse and the `Tendsto ... atTop atTop`
  property to land back in `ClassKInfty`.
Leave `sorry` gaps at the individual Mathlib-lemma joints; the surjectivity
step is the one worth proving by hand. -/
theorem exists_inverse (h : ClassKInfty α) :
    ∃ β : ℝ → ℝ, ClassKInfty β ∧
      (∀ s, 0 ≤ s → β (α s) = s) ∧
      (∀ t, 0 ≤ t → α (β t) = t) := by
  sorry

end ClassKInfty

end Comparison
