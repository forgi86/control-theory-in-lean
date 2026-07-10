import Mathlib

/-!
# Continuous-Time Lyapunov Stability

Formalization of the direct method of Lyapunov for stability of an equilibrium
at the origin of a continuous-time system, following Khalil, *Nonlinear Systems*
(3rd ed.), Theorem 4.1.

The dynamics are abstracted into a flow `traj x₀ t` (state at time `t ≥ 0`
starting from `x₀`). The only structural hypothesis is that trajectories are
*continuous in time*; this is what lets the intermediate value theorem trap a
trajectory inside a ball, so no separate containment hypothesis is required.
-/

-- Fixed (but arbitrary) state-space dimension.
def n : Nat := 10

/-- `V` is positive definite: zero at the origin, strictly positive elsewhere. -/
def IsPositiveDefiniteFunction
    (V : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  V 0 = 0 ∧ ∀ x : EuclideanSpace ℝ (Fin n), x ≠ 0 → 0 < V x

/-- ε-δ Lyapunov stability for a flow `traj`, where `traj x₀ t` is the state at
time `t ≥ 0` starting from `x₀`. -/
def IsStableEpsDeltaCont
    (traj : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x₀ : EuclideanSpace ℝ (Fin n),
    ‖x₀‖ < δ → ∀ t ≥ 0, ‖traj x₀ t‖ < ε

/-- **Sphere minimum is positive.**
On any sphere of radius `r > 0`, a continuous positive-definite `V` has a
strictly positive lower bound `α` (its minimum on the sphere). -/
lemma min_on_sphere_pos
    (V : EuclideanSpace ℝ (Fin n) → ℝ)
    (hVc : Continuous V)
    (hVpd : IsPositiveDefiniteFunction V)
    (r : ℝ) (hr : 0 < r) :
    ∃ α > 0, ∀ x, ‖x‖ = r → α ≤ V x := by
  have hcompact : IsCompact (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) r) :=
    isCompact_sphere 0 r
  have hne : (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) r).Nonempty := by
    have hn : 0 < n := by norm_num [n]
    refine ⟨r • EuclideanSpace.single (⟨0, hn⟩ : Fin n) 1, ?_⟩
    rw [Metric.mem_sphere, dist_zero_right, norm_smul]
    simp [abs_of_pos hr]
  obtain ⟨x_min, hx_mem, hx_min⟩ :=
    hcompact.exists_isMinOn hne hVc.continuousOn
  refine ⟨V x_min, ?_, ?_⟩
  · apply hVpd.2
    intro h
    rw [Metric.mem_sphere, h] at hx_mem
    simp at hx_mem
    linarith
  · intro x hx
    exact hx_min (by rwa [Metric.mem_sphere, dist_zero_right])

/-- **Continuity at the origin.**
If `V` is continuous and `V 0 = 0`, then near the origin `V` is below any
positive threshold. Supplies the `δ` from `ε` in the stability proof. -/
lemma V_small_near_origin
    (V : EuclideanSpace ℝ (Fin n) → ℝ)
    (hVc : Continuous V)
    (hV0 : V 0 = 0)
    (c : ℝ) (hc : 0 < c) :
    ∃ δ > 0, ∀ x : EuclideanSpace ℝ (Fin n),
      ‖x‖ < δ → V x < c := by
  have hcont := hVc.continuousAt (x := 0)
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ, hδ, hball⟩ := hcont c hc
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  have hdist : dist x 0 < δ := by rwa [dist_zero_right]
  have hVx := hball hdist
  simp only [hV0, Real.dist_eq] at hVx
  rw [sub_zero] at hVx
  exact lt_of_abs_lt hVx

/-- ε-δ Lyapunov stability for a flow `traj`, where `traj x₀ t` is the state at
time `t ≥ 0` starting from `x₀`. -/
theorem continuous_lyapunov_stability
    (traj : EuclideanSpace ℝ (Fin n) → ℝ → EuclideanSpace ℝ (Fin n))
    (V : EuclideanSpace ℝ (Fin n) → ℝ)
    (hVc : Continuous V)
    (hVpd : IsPositiveDefiniteFunction V)
    (htraj0 : ∀ x₀, traj x₀ 0 = x₀)
    (htraj_cont : ∀ x₀, Continuous (traj x₀))
    (hV_noninc : ∀ x₀, ∀ t, 0 ≤ t → V (traj x₀ t) ≤ V x₀) :
    IsStableEpsDeltaCont traj := by
  intro ε hε
  obtain ⟨α, hα, hαmin⟩ := min_on_sphere_pos V hVc hVpd ε hε
  obtain ⟨δ, hδ, hδV⟩ := V_small_near_origin V hVc hVpd.1 α hα
  -- shrink δ to also be ≤ ε, so the initial point is already inside the ε-ball
  refine ⟨min δ ε, lt_min hδ hε, ?_⟩
  intro x₀ hx₀ t ht
  -- from ‖x₀‖ < min δ ε we get both ‖x₀‖ < δ and ‖x₀‖ < ε
  have hx₀δ : ‖x₀‖ < δ := lt_of_lt_of_le hx₀ (min_le_left _ _)
  have hx₀ε : ‖x₀‖ < ε := lt_of_lt_of_le hx₀ (min_le_right _ _)
  have hVx₀ : V x₀ < α := hδV x₀ hx₀δ
  by_contra hcon
  push Not at hcon
  have hcont_norm : ContinuousOn (fun s => ‖traj x₀ s‖) (Set.Icc 0 t) :=
    (continuous_norm.comp (htraj_cont x₀)).continuousOn
  have hmem : ε ∈ Set.Icc (‖traj x₀ 0‖) (‖traj x₀ t‖) :=
    ⟨le_of_lt (by rw [htraj0]; exact hx₀ε), hcon⟩
  obtain ⟨t₀, ht₀_mem, ht₀_eq⟩ := intermediate_value_Icc ht hcont_norm hmem
  have hα_le : α ≤ V (traj x₀ t₀) := hαmin (traj x₀ t₀) ht₀_eq
  have hle : V (traj x₀ t₀) ≤ V x₀ := hV_noninc x₀ t₀ ht₀_mem.1
  linarith
