import Mathlib.Topology.MetricSpace.HausdorffDistance
import ControlTheory.ComparisonFunctions

open Set Filter Comparison

/-!
# Classical Lyapunov stability (Theorem B.13)

Discrete-time Lyapunov theorem for global asymptotic stability in the
**classical** (ε-δ + attractivity) sense, following Theorem B.13 of Rawlings,
Mayne & Diehl, *Model Predictive Control*, 2nd ed.

## Design: abstract distance `dA`

Instead of hardwiring the origin (`‖x‖`) or committing to `Metric.infDist x A`,
the development is parameterized by an abstract nonnegative "distance to the
target set" function `dA : E → ℝ`. Intended instantiations:

* `dA := (‖·‖)`            — stability of the origin `A = {0}` (see the didactic
                             corollary at the bottom);
* `dA := (Metric.infDist · A)` — stability of a general closed set `A`.

A pleasant consequence: the core theorem needs **no** norm/topology on `E` — all
the analysis lives in `ℝ`, on the values of `V` and `dA`. So `E : Type*`.

`GloballyAttractive` says `dA (xᵢ) → 0`; when `dA = infDist · A` with `A` closed
this is exactly convergence of the trajectory to `A`.

This layer sits above `Comparison` (which it `open`s): the comparison-function
algebra is the foundation; these stability results are the core built on it.
-/

namespace Lyapunov

variable {E : Type*}

/-! ## Classical stability notions (Definitions B.4–B.6) -/

/-- Local (ε-δ) stability: trajectories starting `dA`-close to the target stay
`dA`-close. -/
def LocallyStable (f : E → E) (dA : E → ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x, dA x < δ → ∀ i : ℕ, dA (f^[i] x) < ε

/-- Global attractivity: every trajectory's distance to the target tends to 0. -/
def GloballyAttractive (f : E → E) (dA : E → ℝ) : Prop :=
  ∀ x, Tendsto (fun i => dA (f^[i] x)) atTop (nhds (0 : ℝ))

/-- Classical global asymptotic stability = locally stable + globally
attractive. -/
def IsGAS_classical (f : E → E) (dA : E → ℝ) : Prop :=
  LocallyStable f dA ∧ GloballyAttractive f dA

/-! ## Lyapunov function (Definition B.12)

`α₁, α₂ ∈ 𝒦∞` sandwich `V`; `α₃` is a **continuous positive-definite** decrease
rate (PD, *not* 𝒦 — see the B.3 note on why continuity of `α₃` is load-bearing).
-/

/-- A Lyapunov function for `f` w.r.t. the distance `dA`, in the sense of
Definition B.12: `𝒦∞` sandwich bounds plus a continuous-PD strict decrease. -/
structure IsLyapunov (f : E → E) (dA : E → ℝ) (V : E → ℝ) (α₁ α₂ α₃ : ℝ → ℝ) :
    Prop where
  k₁ : ClassKInfty α₁
  k₂ : ClassKInfty α₂
  cont₃ : ContinuousOn α₃ (Ici 0)
  pd₃_zero : α₃ 0 = 0
  pd₃_pos : ∀ s, 0 < s → 0 < α₃ s
  lower : ∀ x, α₁ (dA x) ≤ V x           -- (B.8)
  upper : ∀ x, V x ≤ α₂ (dA x)           -- (B.9)
  decrease : ∀ x, V (f x) - V x ≤ -α₃ (dA x)  -- (B.10)

/-! ## Theorem B.13 -/

/-- **Theorem B.13 (classical GAS).** A Lyapunov function (Definition B.12) for
`f` w.r.t. a nonnegative distance `dA` implies classical global asymptotic
stability of the target for `x⁺ = f x`.

Proof structure (see `docs/appendixB_notes.md`):
* **(a) stability** — with `δ := α₂⁻¹(α₁ ε)`, the sublevel bound traps the
  trajectory; uses `ClassKInfty.exists_inverse` for `α₂` and order-reflection.
* **(b) attractivity** — `V(xᵢ)` is antitone and bounded below, so converges to
  some `V̄ ≥ 0`; if `V̄ > 0` then `dA(xᵢ)` stays in a compact interval bounded
  away from `0` where the continuous PD `α₃` has a positive minimum `ρ`,
  telescoping to `V(xᵢ) ≤ V(x) - i·ρ → -∞`, a contradiction. Hence `V̄ = 0`,
  and the squeeze `α₂⁻¹(V) ≤ dA ≤ α₁⁻¹(V)` forces `dA(xᵢ) → 0`. -/
theorem lyapunov_gas_classical
    (f : E → E) (dA : E → ℝ) (V : E → ℝ) (α₁ α₂ α₃ : ℝ → ℝ)
    (hdA : ∀ x, 0 ≤ dA x)
    (hlyap : IsLyapunov f dA V α₁ α₂ α₃) :
    IsGAS_classical f dA := by
  obtain ⟨k₁, k₂, cont₃, pd₃0, pd₃pos, lower, upper, dec⟩ := hlyap
  -- α₃ ≥ 0 on the range of dA (PD: zero at zero, positive beyond).
  have hα₃nonneg : ∀ x, 0 ≤ α₃ (dA x) := by
    intro x
    rcases (hdA x).eq_or_lt with h | h
    · rw [← h]; exact pd₃0.ge
    · exact (pd₃pos _ h).le
  -- One-step nonincrease of V (from decrease + α₃ ≥ 0).
  have hstep : ∀ x, V (f x) ≤ V x := by
    intro x; have h1 := dec x; have h2 := hα₃nonneg x; linarith
  -- Nonincrease of V along the whole trajectory (cf. V_nonincrease_traj).
  have htraj : ∀ x, ∀ i : ℕ, V (f^[i] x) ≤ V x := by
    intro x i
    induction i with
    | zero => simp
    | succ i ih => rw [Function.iterate_succ_apply']; exact le_trans (hstep _) ih
  -- V ≥ 0 (from the lower 𝒦∞ bound).
  have hVnonneg : ∀ x, 0 ≤ V x := fun x =>
    le_trans (k₁.apply_nonneg (hdA x)) (lower x)
  constructor
  · --------------------------------------------------------------------------
    -- (a) Local stability.  δ := α₂⁻¹(α₁ ε).
    --------------------------------------------------------------------------
    intro ε hε
    obtain ⟨β₂, hβ₂ki, _hβ₂left, hβ₂right⟩ := k₂.exists_inverse
    have hα₁ε : 0 < α₁ ε := k₁.toClassK.apply_pos hε
    refine ⟨β₂ (α₁ ε), hβ₂ki.toClassK.apply_pos hα₁ε, ?_⟩
    intro x hxδ i
    -- V x < α₁ ε, because α₂(dA x) < α₂(δ) = α₁ ε.
    have hVx : V x < α₁ ε := by
      have hmono : α₂ (dA x) < α₂ (β₂ (α₁ ε)) :=
        k₂.mono (mem_Ici.mpr (hdA x)) (mem_Ici.mpr (hβ₂ki.apply_nonneg hα₁ε.le)) hxδ
      have hδeq : α₂ (β₂ (α₁ ε)) = α₁ ε := hβ₂right (α₁ ε) hα₁ε.le
      have := upper x
      linarith [hmono, hδeq]
    -- Carry along the trajectory and reflect through α₁.
    have hVi : V (f^[i] x) < α₁ ε := lt_of_le_of_lt (htraj x i) hVx
    have hchain : α₁ (dA (f^[i] x)) < α₁ ε := lt_of_le_of_lt (lower _) hVi
    exact (k₁.toClassK.lt_iff (hdA _) hε.le).mp hchain
  · --------------------------------------------------------------------------
    -- (b) Global attractivity.
    --------------------------------------------------------------------------
    intro x
    -- Abbreviate the trajectory and its V-values.
    set w : ℕ → ℝ := fun i => V (f^[i] x) with hw
    -- w is antitone and bounded below by 0, hence converges to some V̄ ≥ 0.
    have hw_anti : Antitone w := by
      apply antitone_nat_of_succ_le
      intro n
      change V (f^[n + 1] x) ≤ V (f^[n] x)
      rw [Function.iterate_succ_apply']
      exact hstep _
    have hw_nonneg : ∀ i, 0 ≤ w i := fun i => hVnonneg _
    -- Telescoped decrease:  w i ≤ w 0 - ∑_{j<i} α₃ (dA (f^[j] x)).
    have htele : ∀ i, w i ≤ w 0 - ∑ j ∈ Finset.range i, α₃ (dA (f^[j] x)) := by
      intro i
      induction i with
      | zero => simp
      | succ i ih =>
        change V (f^[i + 1] x) ≤ w 0 - ∑ j ∈ Finset.range (i + 1), α₃ (dA (f^[j] x))
        rw [Finset.sum_range_succ, Function.iterate_succ_apply']
        have hd := dec (f^[i] x)
        have ihw : V (f^[i] x) ≤ w 0 - ∑ j ∈ Finset.range i, α₃ (dA (f^[j] x)) := ih
        linarith
    -- The V-limit is 0.  (Contradiction from a positive minimum of α₃ on the
    -- compact interval [α₂⁻¹ V̄, α₁⁻¹ (w 0)] when V̄ > 0; key Mathlib step is
    -- `IsCompact.exists_isMinOn` / `IsCompact.exists_forall_le` on `Set.Icc`.)
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
          have h3 : L ≤ α₂ (dA (f^[i] x)) := (hLle i).trans (upper _)
          have h4 : β₂ L ≤ β₂ (α₂ (dA (f^[i] x))) :=
            hβ₂ki.toClassK.monotoneOn (mem_Ici.mpr hLpos.le)
              (mem_Ici.mpr (k₂.apply_nonneg (hdA _))) h3
          rwa [hβ₂left _ (hdA _)] at h4
        have hhi : ∀ i, dA (f^[i] x) ≤ β₁ (w 0) := by
          intro i
          have h3 : α₁ (dA (f^[i] x)) ≤ w 0 := (lower _).trans (hw_anti (Nat.zero_le i))
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
      have h1 : α₁ (dA (f^[n] x)) ≤ w n := lower _
      have h2 : α₁ (dA (f^[n] x)) < α₁ ε := lt_of_le_of_lt h1 hwn
      exact (k₁.toClassK.lt_iff (hdA _) hε.le).mp h2
    exact hsqueeze

/-! ## Didactic specialization: stability of the origin

The origin case is *not* a separate theorem — it is `lyapunov_gas_classical`
instantiated at `dA := ‖·‖`, with `norm_nonneg` supplying the nonnegativity
hypothesis. This is the "bridge" corollary: it reads simply, yet visibly derives
from the general result. -/

/-- **Origin case of B.13.** For a normed group `E`, a Lyapunov function w.r.t.
`‖·‖` implies classical GAS of the origin. -/
theorem lyapunov_gas_classical_origin
    {E : Type*} [NormedAddCommGroup E]
    (f : E → E) (V : E → ℝ) (α₁ α₂ α₃ : ℝ → ℝ)
    (hlyap : IsLyapunov f (fun x => ‖x‖) V α₁ α₂ α₃) :
    IsGAS_classical f (fun x => ‖x‖) :=
  lyapunov_gas_classical f (fun x => ‖x‖) V α₁ α₂ α₃ (fun x => norm_nonneg x) hlyap

/-! ## Didactic specialization: stability of a general set A

Likewise, `lyapunov_gas_classical` instantiated at `dA := Metric.infDist · A`
is the "bridge" corollary for stability of a general target set `A`: it reads
simply, yet visibly derives from the general result. -/

/-- **General-set case of B.13.** For a pseudometric space `E` and a set `A`,
a Lyapunov function w.r.t. distance-to-`A` implies classical GAS of `A`. -/
theorem lyapunov_gas_classical_set
    {E : Type*} [PseudoMetricSpace E] (A : Set E)
    (f : E → E) (V : E → ℝ) (α₁ α₂ α₃ : ℝ → ℝ)
    (hlyap : IsLyapunov f (fun x => Metric.infDist x A) V α₁ α₂ α₃) :
    IsGAS_classical f (fun x => Metric.infDist x A) :=
  lyapunov_gas_classical f (fun x => Metric.infDist x A) V α₁ α₂ α₃
    (fun _ => Metric.infDist_nonneg) hlyap

end Lyapunov
