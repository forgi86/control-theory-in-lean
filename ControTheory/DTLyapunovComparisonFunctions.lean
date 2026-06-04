import Mathlib

open Set

/-- A comparison function of class 𝒦: vanishing at 0, continuous and strictly
increasing on `[0, ∞)`. -/
structure ClassK (α : ℝ → ℝ) : Prop where
  zero : α 0 = 0
  cont : ContinuousOn α (Ici 0)
  mono : StrictMonoOn α (Ici 0)

variable {E : Type*} [NormedAddCommGroup E]

/-- The origin is an equilibrium (fixed point) of `f`. -/
def IsZeroEquilibrium
    (f : E → E) : Prop :=
  f 0 = 0

/-- ε-δ Lyapunov stability of `x_{k+1} = f x_k`. -/
def IsStableEpsDelta (f : E → E) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x₀ : E, ‖x₀‖ < δ → ∀ k : ℕ, ‖f^[k] x₀‖ < ε

/-- `V` does not increase under one step. -/
def LyapunovNonincrease (V : E → ℝ) (f : E → E) : Prop :=
  ∀ x, V (f x) ≤ V x

/-- A 𝒦 function takes values below any positive target near 0. -/
lemma exists_pos_lt_of_classK {α : ℝ → ℝ} (h : ClassK α) {t : ℝ} (ht : 0 < t) :
    ∃ δ > 0, α δ < t := by
  have hcwa : ContinuousWithinAt α (Ici 0) 0 := h.cont 0 self_mem_Ici
  rw [Metric.continuousWithinAt_iff] at hcwa
  obtain ⟨δ, hδ, hδ'⟩ := hcwa t ht
  refine ⟨δ / 2, by linarith, ?_⟩
  have hmem : (δ / 2) ∈ Ici (0 : ℝ) := mem_Ici.mpr (by linarith)
  have hdist : dist (δ / 2) 0 < δ := by
    rw [Real.dist_eq, sub_zero, abs_of_pos (by linarith)]; linarith
  have := hδ' hmem hdist
  rw [Real.dist_eq, h.zero, sub_zero] at this
  exact lt_of_abs_lt this

omit [NormedAddCommGroup E] in
/-- `V` is nonincreasing along the whole trajectory. -/
lemma V_nonincrease_traj {V : E → ℝ} {f : E → E}
    (hdec : LyapunovNonincrease V f) (x₀ : E) :
    ∀ k, V (f^[k] x₀) ≤ V x₀ := by
  intro k
  induction k with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply']; exact le_trans (hdec _) ih

/-- **Discrete-time Lyapunov stability via comparison functions.**
If `V` is sandwiched between two class-𝒦 functions of the norm (positive
definite and decrescent) and is nonincreasing under `f`, the origin is stable.
No continuity of `V` or `f`, no compactness, and no dimension assumption. -/
theorem stability_via_comparison
    (f : E → E) (V : E → ℝ) (α₁ α₂ : ℝ → ℝ)
    (hα₁ : ClassK α₁) (hα₂ : ClassK α₂)
    (hlb : ∀ x, α₁ ‖x‖ ≤ V x) -- positive definite
    (hub : ∀ x, V x ≤ α₂ ‖x‖) -- decrescent
    (hdec : LyapunovNonincrease V f) :
    IsStableEpsDelta f := by
  intro ε hε
  have ht : 0 < α₁ ε := by
    have := hα₁.mono self_mem_Ici (mem_Ici.mpr hε.le) hε
    simpa [hα₁.zero] using this
  obtain ⟨δ, hδ, hδlt⟩ := exists_pos_lt_of_classK hα₂ ht
  refine ⟨δ, hδ, ?_⟩
  intro x₀ hx₀ k
  have hVx₀ : V x₀ < α₁ ε :=
    calc V x₀ ≤ α₂ ‖x₀‖ := hub x₀
      _ ≤ α₂ δ := hα₂.mono.monotoneOn (mem_Ici.mpr (norm_nonneg x₀))
                    (mem_Ici.mpr hδ.le) hx₀.le
      _ < α₁ ε := hδlt
  have hchain : α₁ ‖f^[k] x₀‖ < α₁ ε :=
    lt_of_le_of_lt (hlb _) (lt_of_le_of_lt (V_nonincrease_traj hdec x₀ k) hVx₀)
  exact (hα₁.mono.lt_iff_lt (mem_Ici.mpr (norm_nonneg _)) (mem_Ici.mpr hε.le)).mp hchain



/-! ## A concrete worked example: `f₀(x) = 0.9·x` with `V(x) = ‖x‖²`

We instantiate the comparison-function theorem on the linear contraction
`x ↦ 0.9·x`, using the squared Euclidean norm as the Lyapunov function. Here
`V(x) = ‖x‖²` is exactly bracketed by the single class-𝒦 function `s ↦ s²`
on both sides, so the positive-definite and decrescent bounds hold with
equality. No dimension assumption, no sphere minimum, and no trapping condition
are needed. -/

def n : Nat := 10

/-- The contraction `f₀(x) = 0.9·x`. -/
noncomputable def f₀ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
  fun x => (0.9 : ℝ) • x

/-- The candidate Lyapunov function `V(x) = ‖x‖²`. -/
noncomputable def squared_l2 : EuclideanSpace ℝ (Fin n) → ℝ :=
  fun x => ‖x‖ ^ 2

-- lemma: f₀(0) = 0, ie 0 is a fixed point of f₀
lemma f₀_zero_equilibrium : IsZeroEquilibrium f₀ := by
  simp[IsZeroEquilibrium, f₀]

/-- `s ↦ s²` is a comparison function of class 𝒦: it vanishes at 0 and is
continuous and strictly increasing on `[0, ∞)`. -/
lemma classK_sq : ClassK (fun s : ℝ => s ^ 2) where
  zero := by norm_num
  cont := (continuous_pow 2).continuousOn
  mono := by
    intro a ha b hb hab
    rw [Set.mem_Ici] at ha hb
    have hbpos : 0 < b := lt_of_le_of_lt ha hab
    change a ^ 2 < b ^ 2
    nlinarith [mul_pos (sub_pos.2 hab) (add_pos_of_nonneg_of_pos ha hbpos)]

/-- `‖·‖²` does not increase under `f₀`: `‖0.9·x‖² = 0.81·‖x‖² ≤ ‖x‖²`. -/
lemma squared_l2_nonincrease : LyapunovNonincrease squared_l2 f₀ := by
  intro x
  unfold squared_l2 f₀
  rw [norm_smul]
  have h09 : ‖(0.9 : ℝ)‖ = 0.9 := by norm_num
  rw [h09]
  nlinarith [norm_nonneg x, sq_nonneg ‖x‖]

/-- **The concrete system is stable.**
`f₀(x) = 0.9·x` is Lyapunov stable, certified by `V(x) = ‖x‖²` through the
comparison-function theorem. Both comparison bounds are the identity `s ↦ s²`,
held with equality. -/
theorem f₀_is_stable : IsStableEpsDelta f₀ :=
  stability_via_comparison f₀ squared_l2 (fun s => s ^ 2) (fun s => s ^ 2)
    classK_sq classK_sq
    (fun x => by simp [squared_l2])   -- α₁ ‖x‖ = ‖x‖² ≤ V x
    (fun x => by simp [squared_l2])   -- V x ≤ ‖x‖² = α₂ ‖x‖
    squared_l2_nonincrease
