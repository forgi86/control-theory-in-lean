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

All lemmas in this module are proved (no `sorry`s remain).
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
theorem apply_pos (h : ClassK α) {s : ℝ} (hs : 0 < s) : 0 < α s :=
  h.zero ▸ h.mono (mem_Ici.mpr le_rfl) (mem_Ici.mpr hs.le) hs

/-- Near `0`, a class-𝒦 function takes values below any positive target.
Used both for the stability `δ` and for the final squeeze in B.13.
Hint: `ContinuousWithinAt` of `α` at `0` within `Ici 0`, via `h.cont`. -/
theorem exists_pos_lt (h : ClassK α) {t : ℝ} (ht : 0 < t) :
    ∃ δ > 0, α δ < t := by
  obtain ⟨δ, hδpos, hδ⟩ :=
    Metric.continuousWithinAt_iff.mp (h.cont.continuousWithinAt (mem_Ici.mpr le_rfl)) t ht
  refine ⟨δ / 2, by linarith, ?_⟩
  have hmem : (0 : ℝ) ≤ δ / 2 := by linarith
  have hdist : dist (δ / 2 : ℝ) 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith
  have hlt := hδ (mem_Ici.mpr hmem) hdist
  rw [h.zero, Real.dist_eq, sub_zero] at hlt
  exact lt_of_le_of_lt (le_abs_self _) hlt

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
  (surjectivity onto `[0, ∞)`, via `IsPreconnected.intermediate_value_Ici`);
* `StrictMonoOn.orderIso` + `OrderIso.setCongr` turn that surjectivity into an
  order isomorphism `e : ↥(Ici 0) ≃o ↥(Ici 0)` agreeing with `α`;
* `β` is `e.symm` (extended by the identity below `0`); continuity and
  monotonicity of `β` on `Ici 0` come for free from `OrderIso.continuous` and
  `OrderIso.strictMono`, and `Tendsto β atTop atTop` follows from monotonicity
  plus the right-inverse property. -/
theorem exists_inverse (h : ClassKInfty α) :
    ∃ β : ℝ → ℝ, ClassKInfty β ∧
      (∀ s, 0 ≤ s → β (α s) = s) ∧
      (∀ t, 0 ≤ t → α (β t) = t) := by
  have himg : α '' Ici (0 : ℝ) = Ici (0 : ℝ) := by
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨s, hs, rfl⟩
      exact h.apply_nonneg hs
    · have hIVT :=
        IsPreconnected.intermediate_value_Ici isPreconnected_Ici (mem_Ici.mpr le_rfl)
          (le_principal_iff.mpr (Ici_mem_atTop 0)) h.toClassK.cont h.unbounded
      rwa [h.zero] at hIVT
  set e : ↥(Ici (0 : ℝ)) ≃o ↥(Ici (0 : ℝ)) :=
    (StrictMonoOn.orderIso α (Ici 0) h.mono).trans (OrderIso.setCongr _ _ himg)
  have he_apply : ∀ s (hs : 0 ≤ s), (e ⟨s, mem_Ici.mpr hs⟩ : ℝ) = α s := fun s hs => rfl
  set β : ℝ → ℝ := fun t => if ht : 0 ≤ t then (e.symm ⟨t, mem_Ici.mpr ht⟩ : ℝ) else t
  have hβα : ∀ s, 0 ≤ s → β (α s) = s := by
    intro s hs
    have hmem : 0 ≤ α s := h.apply_nonneg hs
    change (if ht : 0 ≤ α s then (e.symm ⟨α s, mem_Ici.mpr ht⟩ : ℝ) else α s) = s
    rw [dif_pos hmem]
    have hpoint : (⟨α s, mem_Ici.mpr hmem⟩ : ↥(Ici (0 : ℝ))) = e ⟨s, mem_Ici.mpr hs⟩ :=
      Subtype.ext (he_apply s hs).symm
    rw [hpoint, e.symm_apply_apply]
  have hαβ : ∀ t, 0 ≤ t → α (β t) = t := by
    intro t ht
    change α (if ht' : 0 ≤ t then (e.symm ⟨t, mem_Ici.mpr ht'⟩ : ℝ) else t) = t
    rw [dif_pos ht]
    set y : ↥(Ici (0 : ℝ)) := e.symm ⟨t, mem_Ici.mpr ht⟩ with hy
    change α (y : ℝ) = t
    have hey : (e y : ℝ) = α (y : ℝ) := he_apply (y : ℝ) (mem_Ici.mp y.2)
    have hey' : e y = (⟨t, mem_Ici.mpr ht⟩ : ↥(Ici (0 : ℝ))) := by
      rw [hy]; exact e.apply_symm_apply _
    rw [← hey, hey']
  have hmono : Monotone β := by
    intro x y hxy
    change (if ht : 0 ≤ x then (e.symm ⟨x, mem_Ici.mpr ht⟩ : ℝ) else x) ≤
        (if ht : 0 ≤ y then (e.symm ⟨y, mem_Ici.mpr ht⟩ : ℝ) else y)
    by_cases hx : 0 ≤ x
    · have hy : 0 ≤ y := hx.trans hxy
      rw [dif_pos hx, dif_pos hy]
      exact e.symm.monotone hxy
    · rw [dif_neg hx]
      by_cases hy : 0 ≤ y
      · rw [dif_pos hy]
        have hnn : 0 ≤ (e.symm ⟨y, mem_Ici.mpr hy⟩ : ℝ) := mem_Ici.mp (e.symm ⟨y, mem_Ici.mpr hy⟩).2
        linarith [not_le.mp hx]
      · rw [dif_neg hy]; exact hxy
  refine ⟨β, ⟨⟨?_, ?_, ?_⟩, ?_⟩, hβα, hαβ⟩
  · -- β 0 = 0
    change (if ht : (0:ℝ) ≤ 0 then (e.symm ⟨(0:ℝ), mem_Ici.mpr ht⟩ : ℝ) else (0:ℝ)) = 0
    rw [dif_pos le_rfl]
    have hzero_fixed : e (⟨(0:ℝ), mem_Ici.mpr le_rfl⟩ : ↥(Ici (0 : ℝ))) =
        ⟨(0:ℝ), mem_Ici.mpr le_rfl⟩ := Subtype.ext (by rw [he_apply 0 le_rfl, h.zero])
    have hsymm_fixed : e.symm (⟨(0:ℝ), mem_Ici.mpr le_rfl⟩ : ↥(Ici (0 : ℝ))) =
        ⟨(0:ℝ), mem_Ici.mpr le_rfl⟩ := by
      conv_lhs => rw [← hzero_fixed]
      exact e.symm_apply_apply _
    rw [hsymm_fixed]
  · -- ContinuousOn β (Ici 0)
    rw [continuousOn_iff_continuous_restrict]
    have hrestrict : (Ici (0:ℝ)).restrict β = fun x : ↥(Ici (0 : ℝ)) => (e.symm x : ℝ) := by
      funext x
      change (if ht : 0 ≤ (x:ℝ) then (e.symm ⟨(x:ℝ), mem_Ici.mpr ht⟩ : ℝ) else (x:ℝ)) =
          (e.symm x : ℝ)
      rw [dif_pos (mem_Ici.mp x.2)]
    rw [hrestrict]
    exact continuous_subtype_val.comp (OrderIso.continuous e.symm)
  · -- StrictMonoOn β (Ici 0)
    intro x hx y hy hxy
    change (if ht : 0 ≤ x then (e.symm ⟨x, mem_Ici.mpr ht⟩ : ℝ) else x) <
        (if ht : 0 ≤ y then (e.symm ⟨y, mem_Ici.mpr ht⟩ : ℝ) else y)
    rw [dif_pos (mem_Ici.mp hx), dif_pos (mem_Ici.mp hy)]
    exact e.symm.strictMono hxy
  · -- Tendsto β atTop atTop
    refine hmono.tendsto_atTop_atTop (fun b => ⟨α (max b 0), ?_⟩)
    rw [hβα _ (le_max_right b 0)]
    exact le_max_left b 0

end ClassKInfty

end Comparison
