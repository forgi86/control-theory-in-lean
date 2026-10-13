import Mathlib.Topology.MetricSpace.HausdorffDistance
import ControlTheory.ComparisonFunctions

open Set Filter Comparison

/-!
# Classical Lyapunov stability, constrained to an invariant set `X` (Theorem B.13, full form)

`ControlTheory/LyapunovStability.lean` proves Theorem B.13 in the special case
`X = E` (the book's own simplification: "If `X = ℝⁿ`, drop the phrase 'in
X'"). This file proves the theorem **as stated**, with an arbitrary
positive-invariant `X : Set E` and the Lyapunov sandwich (B.8)–(B.10) required
only on `X`.

## What changes relative to the unconstrained file

* An explicit `X : Set E` and hypothesis `hX_inv : ∀ x ∈ X, f x ∈ X` are
  threaded through everything — `X`'s invariance is **not** derivable (unlike
  the target set `A`'s invariance in the unconstrained case: there, the
  sandwich holding on *all* of `E` forces `dA x = 0 → dA (f x) = 0` for free;
  here the sandwich only holds on `X`, so nothing pins down invariance of `X`
  itself).
* `IsLyapunovOn`'s `lower`/`upper`/`decrease` fields, and the stability /
  attractivity notions `LocallyStableOn`/`GloballyAttractiveOn`, quantify over
  `x ∈ X` rather than all of `E`.
* The proof is otherwise identical in structure (antitone-bounded
  convergence, compactness contradiction, ε-N squeeze); the only new
  ingredient is a single membership lemma `∀ x ∈ X, ∀ i, f^[i] x ∈ X`
  (immediate induction from `hX_inv`), inserted wherever a trajectory point is
  fed into `lower`/`upper`/`decrease`.

This file is self-contained: it does **not** import `LyapunovStability.lean`,
so the two developments coexist without one being defined in terms of the
other.
-/

namespace Lyapunov

variable {E : Type*}

/-! ## Classical stability notions (Definitions B.4–B.6), restricted to `X` -/

/-- Local (ε-δ) stability on `X`: trajectories starting in `X` and `dA`-close
to the target stay `dA`-close. -/
def LocallyStableOn (f : E → E) (dA : E → ℝ) (X : Set E) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x ∈ X, dA x < δ → ∀ i : ℕ, dA (f^[i] x) < ε

/-- Global attractivity on `X`: every trajectory starting in `X` has its
distance to the target tend to `0`. -/
def GloballyAttractiveOn (f : E → E) (dA : E → ℝ) (X : Set E) : Prop :=
  ∀ x ∈ X, Tendsto (fun i => dA (f^[i] x)) atTop (nhds (0 : ℝ))

/-- Classical global asymptotic stability on `X` = locally stable + globally
attractive, both restricted to trajectories starting in `X`. -/
def IsGAS_classicalOn (f : E → E) (dA : E → ℝ) (X : Set E) : Prop :=
  LocallyStableOn f dA X ∧ GloballyAttractiveOn f dA X

/-! ## Lyapunov function (Definition B.12), in `X` -/

/-- A Lyapunov function for `f` w.r.t. the distance `dA`, **in `X`**: the
sandwich bounds and decrease condition (B.8)–(B.10) are required only for
`x ∈ X`. -/
structure IsLyapunovOn (f : E → E) (dA : E → ℝ) (V : E → ℝ) (X : Set E)
    (α₁ α₂ α₃ : ℝ → ℝ) : Prop where
  k₁ : ClassKInfty α₁
  k₂ : ClassKInfty α₂
  cont₃ : ContinuousOn α₃ (Ici 0)
  pd₃_zero : α₃ 0 = 0
  pd₃_pos : ∀ s, 0 < s → 0 < α₃ s
  lower : ∀ x ∈ X, α₁ (dA x) ≤ V x           -- (B.8)
  upper : ∀ x ∈ X, V x ≤ α₂ (dA x)           -- (B.9)
  decrease : ∀ x ∈ X, V (f x) - V x ≤ -α₃ (dA x)  -- (B.10)

/-! ## Theorem B.13 (full form) -/

/-- **Theorem B.13 (classical GAS, constrained form).** Suppose `X` is
positive invariant for `x⁺ = f x` and `V` is a Lyapunov function for `f`
w.r.t. `dA`, **in `X`** (Definition B.12). Then `f` is classically globally
asymptotically stable on `X`.

Proof structure mirrors the unconstrained case exactly (see
`LyapunovStability.lean`), with every use of `lower`/`upper`/`decrease` at a
trajectory point `f^[i] x` preceded by `hmem x hx i : f^[i] x ∈ X`, supplied
by induction from `hX_inv`. -/
theorem lyapunov_gas_classical_on
    (f : E → E) (dA : E → ℝ) (V : E → ℝ) (X : Set E) (α₁ α₂ α₃ : ℝ → ℝ)
    (hdA : ∀ x, 0 ≤ dA x)
    (hX_inv : ∀ x ∈ X, f x ∈ X)
    (hlyap : IsLyapunovOn f dA V X α₁ α₂ α₃) :
    IsGAS_classicalOn f dA X := by
  obtain ⟨k₁, k₂, cont₃, pd₃0, pd₃pos, lower, upper, dec⟩ := hlyap
  -- α₃ ≥ 0 everywhere (PD: zero at zero, positive beyond) — no X needed.
  have hα₃nonneg : ∀ x, 0 ≤ α₃ (dA x) := by
    intro x
    rcases (hdA x).eq_or_lt with h | h
    · rw [← h]; exact pd₃0.ge
    · exact (pd₃pos _ h).le
  -- Trajectories starting in X stay in X.
  have hmem : ∀ x ∈ X, ∀ i : ℕ, f^[i] x ∈ X := by
    intro x hx i
    induction i with
    | zero => simpa using hx
    | succ i ih => rw [Function.iterate_succ_apply']; exact hX_inv _ ih
  -- One-step nonincrease of V, on X.
  have hstep : ∀ x ∈ X, V (f x) ≤ V x := by
    intro x hx
    have h1 := dec x hx
    have h2 := hα₃nonneg x
    linarith
  -- Nonincrease of V along the whole trajectory, from a start in X.
  have htraj : ∀ x ∈ X, ∀ i : ℕ, V (f^[i] x) ≤ V x := by
    intro x hx i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [Function.iterate_succ_apply']
      exact le_trans (hstep _ (hmem x hx i)) ih
  -- V ≥ 0 on X (from the lower 𝒦∞ bound).
  have hVnonneg : ∀ x ∈ X, 0 ≤ V x := fun x hx =>
    le_trans (k₁.apply_nonneg (hdA x)) (lower x hx)
  constructor
  · --------------------------------------------------------------------------
    -- (a) Local stability.  δ := α₂⁻¹(α₁ ε).
    --------------------------------------------------------------------------
    intro ε hε
    obtain ⟨β₂, hβ₂ki, _hβ₂left, hβ₂right⟩ := k₂.exists_inverse
    have hα₁ε : 0 < α₁ ε := k₁.toClassK.apply_pos hε
    refine ⟨β₂ (α₁ ε), hβ₂ki.toClassK.apply_pos hα₁ε, ?_⟩
    intro x hx hxδ i
    -- V x < α₁ ε, because α₂(dA x) < α₂(δ) = α₁ ε.
    have hVx : V x < α₁ ε := by
      have hmono : α₂ (dA x) < α₂ (β₂ (α₁ ε)) :=
        k₂.mono (mem_Ici.mpr (hdA x)) (mem_Ici.mpr (hβ₂ki.apply_nonneg hα₁ε.le)) hxδ
      have hδeq : α₂ (β₂ (α₁ ε)) = α₁ ε := hβ₂right (α₁ ε) hα₁ε.le
      have := upper x hx
      linarith [hmono, hδeq]
    -- Carry along the trajectory (staying in X) and reflect through α₁.
    have hVi : V (f^[i] x) < α₁ ε := lt_of_le_of_lt (htraj x hx i) hVx
    have hchain : α₁ (dA (f^[i] x)) < α₁ ε :=
      lt_of_le_of_lt (lower _ (hmem x hx i)) hVi
    exact (k₁.toClassK.lt_iff (hdA _) hε.le).mp hchain
  · --------------------------------------------------------------------------
    -- (b) Global attractivity.
    --------------------------------------------------------------------------
    intro x hx
    -- Abbreviate the trajectory and its V-values.
    set w : ℕ → ℝ := fun i => V (f^[i] x) with hw
    -- w is antitone and bounded below by 0, hence converges to some V̄ ≥ 0.
    have hw_anti : Antitone w := by
      apply antitone_nat_of_succ_le
      intro n
      change V (f^[n + 1] x) ≤ V (f^[n] x)
      rw [Function.iterate_succ_apply']
      exact hstep _ (hmem x hx n)
    have hw_nonneg : ∀ i, 0 ≤ w i := fun i => hVnonneg _ (hmem x hx i)
    -- Telescoped decrease:  w i ≤ w 0 - ∑_{j<i} α₃ (dA (f^[j] x)).
    have htele : ∀ i, w i ≤ w 0 - ∑ j ∈ Finset.range i, α₃ (dA (f^[j] x)) := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
        change V (f^[i + 1] x) ≤ w 0 - ∑ j ∈ Finset.range (i + 1), α₃ (dA (f^[j] x))
        rw [Finset.sum_range_succ, Function.iterate_succ_apply']
        have hd := dec (f^[i] x) (hmem x hx i)
        have ihw : V (f^[i] x) ≤ w 0 - ∑ j ∈ Finset.range i, α₃ (dA (f^[j] x)) := ih
        linarith
    -- The V-limit is 0.  (Contradiction from a positive minimum of α₃ on the
    -- compact interval [α₂⁻¹ V̄, α₁⁻¹ (w 0)] when V̄ > 0.)
    have hVbar : Tendsto w atTop (nhds (0 : ℝ)) := by
      have hbdd : BddBelow (Set.range w) := ⟨0, by rintro _ ⟨i, rfl⟩; exact hw_nonneg i⟩
      have hconv : Tendsto w atTop (nhds (⨅ i, w i)) := tendsto_atTop_ciInf hw_anti hbdd
      have hLnonneg : (0 : ℝ) ≤ ⨅ i, w i := le_ciInf hw_nonneg
      have hLle : ∀ i, (⨅ i, w i) ≤ w i := fun i => ciInf_le hbdd i
      have hLeq : (⨅ i, w i) = 0 := by
        by_contra hLne
        have hLpos : (0 : ℝ) < ⨅ i, w i := hLnonneg.lt_of_ne (Ne.symm hLne)
        set L := ⨅ i, w i with hLdef
        obtain ⟨β₁, hβ₁ki, hβ₁left, _⟩ := k₁.exists_inverse
        obtain ⟨β₂, hβ₂ki, hβ₂left, _⟩ := k₂.exists_inverse
        have hlo : ∀ i, β₂ L ≤ dA (f^[i] x) := by
          intro i
          have h3 : L ≤ α₂ (dA (f^[i] x)) := (hLle i).trans (upper _ (hmem x hx i))
          have h4 : β₂ L ≤ β₂ (α₂ (dA (f^[i] x))) :=
            hβ₂ki.toClassK.monotoneOn (mem_Ici.mpr hLpos.le)
              (mem_Ici.mpr (k₂.apply_nonneg (hdA _))) h3
          rwa [hβ₂left _ (hdA _)] at h4
        have hhi : ∀ i, dA (f^[i] x) ≤ β₁ (w 0) := by
          intro i
          have h3 : α₁ (dA (f^[i] x)) ≤ w 0 :=
            (lower _ (hmem x hx i)).trans (hw_anti (Nat.zero_le i))
          have h4 : β₁ (α₁ (dA (f^[i] x))) ≤ β₁ (w 0) :=
            hβ₁ki.toClassK.monotoneOn (mem_Ici.mpr (k₁.apply_nonneg (hdA _)))
              (mem_Ici.mpr (hw_nonneg 0)) h3
          rwa [hβ₁left _ (hdA _)] at h4
        have ha_pos : 0 < β₂ L := hβ₂ki.toClassK.apply_pos hLpos
        have hab : β₂ L ≤ β₁ (w 0) := (hlo 0).trans (hhi 0)
        have hIcc_sub : Set.Icc (β₂ L) (β₁ (w 0)) ⊆ Set.Ici (0 : ℝ) :=
          fun y hy => mem_Ici.mpr (ha_pos.le.trans hy.1)
        have hcont : ContinuousOn α₃ (Set.Icc (β₂ L) (β₁ (w 0))) := cont₃.mono hIcc_sub
        have hne : (Set.Icc (β₂ L) (β₁ (w 0))).Nonempty :=
          ⟨β₂ L, Set.mem_Icc.mpr ⟨le_rfl, hab⟩⟩
        obtain ⟨ρx, hρx_mem, hρx_min⟩ := isCompact_Icc.exists_isMinOn hne hcont
        have hρpos : 0 < α₃ ρx := pd₃pos ρx (lt_of_lt_of_le ha_pos hρx_mem.1)
        have hρmin : ∀ y ∈ Set.Icc (β₂ L) (β₁ (w 0)), α₃ ρx ≤ α₃ y := isMinOn_iff.mp hρx_min
        have hterm : ∀ j, α₃ ρx ≤ α₃ (dA (f^[j] x)) := fun j => hρmin _ ⟨hlo j, hhi j⟩
        have hsum_ge :
            ∀ i : ℕ, (i : ℝ) * α₃ ρx ≤ ∑ j ∈ Finset.range i, α₃ (dA (f^[j] x)) := by
          intro i
          calc (i : ℝ) * α₃ ρx = ∑ _j ∈ Finset.range i, α₃ ρx := by
                rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
            _ ≤ ∑ j ∈ Finset.range i, α₃ (dA (f^[j] x)) :=
                Finset.sum_le_sum (fun j _ => hterm j)
        obtain ⟨n, hn⟩ := exists_nat_gt (w 0 / α₃ ρx)
        have hn' : w 0 < (n : ℝ) * α₃ ρx := (div_lt_iff₀ hρpos).mp hn
        have h1 := htele n
        have h2 := hsum_ge n
        have h3 := hw_nonneg n
        linarith
      rw [hLeq] at hconv
      exact hconv
    -- Squeeze:  α₁ (dA (f^[i] x)) ≤ w i → 0  and  0 ≤ dA,  with α₁⁻¹ continuous
    -- at 0 (α₁⁻¹ 0 = 0), give dA (f^[i] x) → 0.
    have hsqueeze : Tendsto (fun i => dA (f^[i] x)) atTop (nhds (0 : ℝ)) := by
      rw [Metric.tendsto_atTop]
      intro ε hε
      rw [Metric.tendsto_atTop] at hVbar
      obtain ⟨N, hN⟩ := hVbar (α₁ ε) (k₁.toClassK.apply_pos hε)
      refine ⟨N, fun n hn => ?_⟩
      have hwn := hN n hn
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (hw_nonneg n)] at hwn
      rw [Real.dist_eq, sub_zero, abs_of_nonneg (hdA _)]
      have h1 : α₁ (dA (f^[n] x)) ≤ w n := lower _ (hmem x hx n)
      have h2 : α₁ (dA (f^[n] x)) < α₁ ε := lt_of_le_of_lt h1 hwn
      exact (k₁.toClassK.lt_iff (hdA _) hε.le).mp h2
    exact hsqueeze

/-! ## Didactic specializations -/

/-- **Origin case, constrained.** For a normed group `E` and a positive
invariant `X`, a Lyapunov function w.r.t. `‖·‖` in `X` implies classical GAS
of the origin on `X`. -/
theorem lyapunov_gas_classical_origin_on
    {E : Type*} [NormedAddCommGroup E] (X : Set E)
    (f : E → E) (V : E → ℝ) (α₁ α₂ α₃ : ℝ → ℝ)
    (hX_inv : ∀ x ∈ X, f x ∈ X)
    (hlyap : IsLyapunovOn f (fun x => ‖x‖) V X α₁ α₂ α₃) :
    IsGAS_classicalOn f (fun x => ‖x‖) X :=
  lyapunov_gas_classical_on f (fun x => ‖x‖) V X α₁ α₂ α₃
    (fun x => norm_nonneg x) hX_inv hlyap

/-- **General-set case, constrained.** For a pseudometric space `E`, a set
`A`, and a positive invariant `X`, a Lyapunov function w.r.t. distance-to-`A`
in `X` implies classical GAS of `A` on `X`. -/
theorem lyapunov_gas_classical_set_on
    {E : Type*} [PseudoMetricSpace E] (A X : Set E)
    (f : E → E) (V : E → ℝ) (α₁ α₂ α₃ : ℝ → ℝ)
    (hX_inv : ∀ x ∈ X, f x ∈ X)
    (hlyap : IsLyapunovOn f (fun x => Metric.infDist x A) V X α₁ α₂ α₃) :
    IsGAS_classicalOn f (fun x => Metric.infDist x A) X :=
  lyapunov_gas_classical_on f (fun x => Metric.infDist x A) V X α₁ α₂ α₃
    (fun _ => Metric.infDist_nonneg) hX_inv hlyap

/-! ## Bonus: `A`'s positive invariance is derivable, not assumed

The book (Def B.12 / Thm B.13) states "`A ⊆ X` closed and positive invariant"
as a standing hypothesis. It isn't needed as one here: given the Lyapunov
sandwich on `X`, `X`'s own invariance, and `A ⊆ X`, invariance of `A` falls
out for free. -/

/-- If `A ⊆ X` is closed and nonempty and `V` is a Lyapunov function w.r.t.
distance-to-`A` in `X`, then `A` is positive invariant for `f` — this is a
consequence of `IsLyapunovOn`, not an extra hypothesis of `Theorem B.13`. -/
theorem IsLyapunovOn.mapsTo_of_isClosed
    {E : Type*} [PseudoMetricSpace E] {A X : Set E} {f : E → E} {V : E → ℝ}
    {α₁ α₂ α₃ : ℝ → ℝ} (hA_closed : IsClosed A) (hA_ne : A.Nonempty)
    (hA_sub : A ⊆ X) (hX_inv : ∀ x ∈ X, f x ∈ X)
    (hlyap : IsLyapunovOn f (fun x => Metric.infDist x A) V X α₁ α₂ α₃) :
    Set.MapsTo f A A := by
  intro x hxA
  have hxX : x ∈ X := hA_sub hxA
  have hfxX : f x ∈ X := hX_inv x hxX
  have hdAx : Metric.infDist x A = 0 := (hA_closed.mem_iff_infDist_zero hA_ne).mp hxA
  -- V x = 0, from the sandwich at x ∈ X.
  have hVx0 : V x = 0 := by
    have h1 := hlyap.upper x hxX
    have h2 := hlyap.lower x hxX
    rw [hdAx, hlyap.k₂.zero] at h1
    rw [hdAx, hlyap.k₁.zero] at h2
    linarith
  -- V (f x) = 0, from the decrease condition and nonnegativity at f x ∈ X.
  have hVfx0 : V (f x) = 0 := by
    have hdec := hlyap.decrease x hxX
    rw [hdAx, hlyap.pd₃_zero] at hdec
    have hlow := hlyap.lower (f x) hfxX
    have hnn : 0 ≤ V (f x) := le_trans (hlyap.k₁.apply_nonneg Metric.infDist_nonneg) hlow
    linarith
  -- Hence dA (f x) = 0, i.e. f x ∈ A.
  have hα1fx0 : α₁ (Metric.infDist (f x) A) = 0 := by
    have hlow := hlyap.lower (f x) hfxX
    rw [hVfx0] at hlow
    have hnn : 0 ≤ α₁ (Metric.infDist (f x) A) :=
      hlyap.k₁.apply_nonneg Metric.infDist_nonneg
    linarith
  have hdAfx0 : Metric.infDist (f x) A = 0 := by
    by_contra hne
    have hpos : 0 < Metric.infDist (f x) A :=
      lt_of_le_of_ne Metric.infDist_nonneg (Ne.symm hne)
    have := hlyap.k₁.toClassK.apply_pos hpos
    linarith
  exact (hA_closed.mem_iff_infDist_zero hA_ne).mpr hdAfx0

end Lyapunov
