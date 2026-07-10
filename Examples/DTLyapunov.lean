import Mathlib

/-!
# Discrete-Time Lyapunov Stability (ε-δ formulation)

A machine-checked formalization of the direct method of Lyapunov for stability
of an equilibrium at the origin of a discrete-time system `x_{k+1} = f(x_k)`,
following the ε-δ argument of Khalil, *Nonlinear Systems* (3rd ed.), Theorem 4.1,
adapted to discrete time.

The central observation is that the discrete-time theorem requires one extra
hypothesis absent from the continuous-time statement: `SublevelTrapped`. In
continuous time, a trajectory cannot leave a ball without crossing its boundary
sphere (intermediate value theorem); in discrete time, a single step
`x_k ↦ f(x_k)` can jump across the sphere, so containment of sublevel sets must
be assumed explicitly.

More modern formulations of Lyapunov stability based on comparison functions may
be applied instead...
-/

/-- The (fixed, but arbitrary) state-space dimension. Could be made generic (TODO) -/
def n : Nat := 10

/-- **ε-δ Lyapunov stability** of the discrete system `x_{k+1} = f(x_k)`.
For every `ε > 0` there is a `δ > 0` such that every trajectory
starting within `δ` of the origin stays within `ε` of it for all time steps. -/
def IsStableEpsDelta
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x₀ : EuclideanSpace ℝ (Fin n),
    ‖x₀‖ < δ → ∀ k : ℕ, ‖f^[k] x₀‖ < ε

/-- **Positive-definite function.** `V` vanishes at the origin and is strictly
positive elsewhere: `V 0 = 0` and `V x > 0` for `x ≠ 0`. Such a `V` plays the
role of an abstract "energy" of the system. -/
def IsPositiveDefiniteFunction
    (V : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  V 0 = 0 ∧ ∀ x : EuclideanSpace ℝ (Fin n), x ≠ 0 → 0 < V x

/-- **Lyapunov non-increase condition.** The energy `V` does not increase under
one application of the dynamics: `V (f x) ≤ V x` for every state `x`. This is
the discrete-time analogue of the continuous-time condition `V̇ ≤ 0`. -/
def LyapunovNonincrease
    (V : EuclideanSpace ℝ (Fin n) → ℝ)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : Prop :=
  ∀ x : EuclideanSpace ℝ (Fin n), V (f x) ≤ V x

/-- **Sublevel-trapping condition.**
For every radius `ε` and every positive lower bound `α` of `V` on the sphere
`‖x‖ = ε`, the strict sublevel set `{x | V x < α}` lies inside the open ball of
radius `ε`.

This is a property of `V` alone: it speaks only of the geometry of the sublevel
sets of `V`, with no reference to `f`, to trajectories, or to time. Concretely it
says that `V` never dips below its sphere-minimum farther out — the infimum of
`V` over the exterior `{‖x‖ ≥ ε}` is attained on the boundary sphere
`{‖x‖ = ε}`. It holds whenever `V` is bounded below by a strictly increasing
function of the norm that is tight on spheres: for `V x = ‖x‖²`, whose sublevel
sets are balls, and for every positive-definite quadratic form `V x = xᵀ P x`,
whose sublevel sets are ellipsoids (here `V x ≥ lam_min(P) · ‖x‖²`).

The condition is what the discrete-time theorem requires in place of trajectory
continuity. In continuous time the corresponding step is free: `V` is
nonincreasing along the trajectory, and by the intermediate value theorem a
continuous path cannot leave `B_ε` without first meeting the sphere `‖·‖ = ε`,
where `V ≥ α > V x₀` — so escape is ruled out even when `{V < α}` has components
far from the origin, which the path cannot reach. A discrete step `x ↦ f x` can
jump across the sphere directly, so containment of the sublevel set is assumed
here to supply what continuity would otherwise guarantee. -/
def SublevelTrapped
    (V : EuclideanSpace ℝ (Fin n) → ℝ) : Prop :=
  ∀ ε > 0, ∀ α > 0,
    (∀ x, ‖x‖ = ε → α ≤ V x) →
    (∀ x, V x < α → ‖x‖ < ε)

/-- The origin is an equilibrium (fixed point) of `f`. -/
def IsZeroEquilibrium
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) : Prop :=
  f 0 = 0

/-- **The equilibrium condition is implied, not assumed.**
A positive-definite `V` that is nonincreasing under `f` forces the origin to be
a fixed point. Indeed `V (f 0) ≤ V 0 = 0` by nonincrease, while `V (f 0) ≥ 0`
by positive-definiteness, so `V (f 0) = 0`, hence `f 0 = 0`.

This shows that the standard hypothesis `f 0 = 0` of Lyapunov's theorem is
*derivable* from the other hypotheses — specifically from the *strict* positive-
definiteness of `V` (`V x > 0` for `x ≠ 0`) together with nonincrease. It is a
consequence, not an independent assumption. -/
lemma zeroEquilibrium_of_lyapunov
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (V : EuclideanSpace ℝ (Fin n) → ℝ)
    (hVpd : IsPositiveDefiniteFunction V)
    (hdec : LyapunovNonincrease V f) :
    IsZeroEquilibrium f := by
  change f 0 = 0
  have h1 : V (f 0) ≤ 0 := by
    have := hdec 0
    rwa [hVpd.1] at this
  by_contra hf0
  have h2 : 0 < V (f 0) := hVpd.2 (f 0) hf0
  linarith


/-- **Positivity of the sphere minimum.**
On the sphere `‖x‖ = r` of radius `r > 0`, a continuous positive-definite `V`
admits a strictly positive lower bound `α` (its minimum on the sphere).

Proof outline: the sphere is compact and nonempty, so the continuous `V` attains
a minimum on it at some `x_min`. Since `x_min` lies on a sphere of positive
radius it is nonzero, hence `V x_min > 0` by positive-definiteness; and being a
minimizer, `V x_min` lower-bounds `V` on the whole sphere. -/
lemma min_on_sphere_pos
    (V : EuclideanSpace ℝ (Fin n) → ℝ)
    (hVc : Continuous V)
    (hVpd : IsPositiveDefiniteFunction V)
    (r : ℝ) (hr : 0 < r) :
    ∃ α > 0, ∀ x, ‖x‖ = r → α ≤ V x := by
  -- the sphere of radius r is compact
  have hcompact : IsCompact (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) r) :=
    isCompact_sphere 0 r
  -- and nonempty: scale the first basis vector to radius r
  have hne : (Metric.sphere (0 : EuclideanSpace ℝ (Fin n)) r).Nonempty := by
    have hn : 0 < n := by norm_num [n]
    refine ⟨r • EuclideanSpace.single (⟨0, hn⟩ : Fin n) 1, ?_⟩
    rw [Metric.mem_sphere, dist_zero_right, norm_smul]
    simp [EuclideanSpace.norm_single, abs_of_pos hr]
  -- a continuous function on a compact nonempty set attains its minimum
  obtain ⟨x_min, hx_mem, hx_min⟩ :=
    hcompact.exists_isMinOn hne hVc.continuousOn
  refine ⟨V x_min, ?_, ?_⟩
  · -- the minimum value is positive: x_min ≠ 0 since it lies on the sphere
    apply hVpd.2
    intro h
    rw [Metric.mem_sphere, h] at hx_mem
    simp at hx_mem
    linarith
  · -- the minimum value lower-bounds V on the sphere
    intro x hx
    exact hx_min (by rwa [Metric.mem_sphere, dist_zero_right])

/-- **Non-increase along trajectories.**
If `V` does not increase under one step (`hdec`), then `V` along the whole
trajectory is bounded by its initial value: `V (f^[k] x₀) ≤ V x₀` for all `k`.
Proved by induction on `k`, using the one-step bound at each successor. -/
lemma V_nonincrease_traj
    (V : EuclideanSpace ℝ (Fin n) → ℝ)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hdec : LyapunovNonincrease V f)
    (x₀ : EuclideanSpace ℝ (Fin n)) :
    ∀ k : ℕ, V (f^[k] x₀) ≤ V x₀ := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    -- f^[k+1] x₀ = f (f^[k] x₀); apply the one-step bound, then the IH
    rw [Function.iterate_succ_apply']
    exact le_trans (hdec (f^[k] x₀)) ih

/-- **Discrete trajectory invariance.**
Suppose the sublevel set `{x | V x < α}` is contained in the open ball of radius
`r` (`htrap_local`), and `V` does not increase under `f` (`hdec`). Then a
trajectory starting at a point `x₀` with `V x₀ < α` remains in the open ball for
all time steps.

The argument is purely algebraic: `V` is nonincreasing along the trajectory, so
`V (f^[k] x₀) ≤ V x₀ < α` at every step `k`; containment then places each iterate
inside the ball. Note no continuity or "no-jump" condition is needed here — the
containment hypothesis `htrap_local` already rules out escape, which is exactly
what the continuous-time intermediate value theorem would otherwise provide. -/
lemma trajectory_stays_in_ball
    (V : EuclideanSpace ℝ (Fin n) → ℝ)
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hdec : LyapunovNonincrease V f)
    (r α : ℝ)
    (htrap_local : ∀ x, V x < α → ‖x‖ < r)
    (x₀ : EuclideanSpace ℝ (Fin n))
    (hx₀_V : V x₀ < α) :
    ∀ k : ℕ, ‖f^[k] x₀‖ < r := by
  intro k
  -- V along the trajectory stays below α (nonincrease), then containment
  -- places the iterate inside the open ball.
  apply htrap_local
  calc V (f^[k] x₀)
      ≤ V x₀ := V_nonincrease_traj V f hdec x₀ k
    _ < α    := hx₀_V

/-- **Continuity of `V` at the origin.**
If `V` is continuous and `V 0 = 0`, then for any positive threshold `c` there is
a neighbourhood `‖x‖ < δ` of the origin on which `V x < c`. This is the step that
converts the tolerance `ε` (via the threshold `α`) into the initial-condition
radius `δ` in the stability proof. Proved by unfolding continuity at `0`. -/
lemma V_small_near_origin
    (V : EuclideanSpace ℝ (Fin n) → ℝ)
    (hVc : Continuous V)
    (hV0 : V 0 = 0)
    (c : ℝ) (hc : 0 < c) :
    ∃ δ > 0, ∀ x : EuclideanSpace ℝ (Fin n),
      ‖x‖ < δ → V x < c := by
  -- unfold continuity of V at the origin into its ε-δ form
  have hcont := hVc.continuousAt (x := 0)
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨δ, hδ, hball⟩ := hcont c hc
  refine ⟨δ, hδ, ?_⟩
  intro x hx
  -- ‖x‖ < δ is the same as dist x 0 < δ
  have hdist : dist x 0 < δ := by rwa [dist_zero_right]
  have hVx := hball hdist
  -- |V x - V 0| < c with V 0 = 0 gives V x < c
  simp only [hV0, Real.dist_eq] at hVx
  rw [sub_zero] at hVx
  exact lt_of_abs_lt hVx

/-- **Discrete-time Lyapunov stability theorem (ε-δ).**
Let `f` describe a discrete-time system with a continuous, positive-definite
Lyapunov function `V` that is nonincreasing under `f` and satisfies the
sublevel-trapping condition. Then the origin is stable in the sense of Lyapunov.

The proof realizes Khalil's ε-δ construction in discrete time:
1. `min_on_sphere_pos` gives a positive lower bound `α` for `V` on the sphere of
   radius `ε`;
2. `SublevelTrapped` specializes to "`V x < α ⟹ ‖x‖ < ε`" at this `ε`, `α`;
3. `V_small_near_origin` produces `δ` with `‖x₀‖ < δ ⟹ V x₀ < α`;
4. `trajectory_stays_in_ball` then keeps the whole trajectory inside the
   `ε`-ball, since `V` only decreases.

The `htrap : SublevelTrapped V` hypothesis is the one feature absent from the
continuous-time statement; it is what the discrete dynamics require in lieu of
trajectory continuity. -/
theorem discrete_lyapunov_stability_epsdelta
    (f : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (V : EuclideanSpace ℝ (Fin n) → ℝ)
    (hVc  : Continuous V)
    (hVpd : IsPositiveDefiniteFunction V)
    (hdec : LyapunovNonincrease V f)
    (htrap : SublevelTrapped V) :
    IsStableEpsDelta f := by
  intro ε hε
  -- 1. positive sphere-minimum α at radius ε
  obtain ⟨α, hα, hαmin⟩ := min_on_sphere_pos V hVc hVpd ε hε
  -- 2. sublevel containment specialized to this ε and α
  have hcont : ∀ x, V x < α → ‖x‖ < ε := htrap ε hε α hα hαmin
  -- 3. continuity at the origin yields δ with ‖x₀‖ < δ ⟹ V x₀ < α
  obtain ⟨δ, hδ, hδV⟩ := V_small_near_origin V hVc hVpd.1 α hα
  -- 4. this δ witnesses stability
  refine ⟨δ, hδ, ?_⟩
  intro x₀ hx₀ k
  have hVx₀ : V x₀ < α := hδV x₀ hx₀
  exact trajectory_stays_in_ball V f hdec ε α hcont x₀ hVx₀ k



/-! ## A concrete worked example: `f₀(x) = 0.9·x` with `V(x) = ‖x‖²`

We instantiate the general theorem on the linear contraction `x ↦ 0.9·x`, using
the squared Euclidean norm as the Lyapunov function. This demonstrates that the
hypotheses, including the discrete-time-specific `SublevelTrapped`, are
satisfiable and natural: for `V = ‖·‖²` the sublevel sets are exactly balls, so
`SublevelTrapped` holds trivially. -/

/-- The contraction `f₀(x) = 0.9·x`. -/
noncomputable def f₀ : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n) :=
  fun x => (0.9 : ℝ) • x

/-- The candidate Lyapunov function `V(x) = ‖x‖²`. -/
noncomputable def squared_l2 : EuclideanSpace ℝ (Fin n) → ℝ :=
  fun x => ‖x‖^2

-- lemma: f₀(0) = 0, fixed point
-- We prove it explicitly because it's very easy in this case, but in fact it
-- follows from other lemmas that we would need to prove anyway
lemma f₀_zero_equilibrium : IsZeroEquilibrium f₀ := by
  simp[IsZeroEquilibrium, f₀]


/-- `‖·‖²` is continuous. -/
lemma squared_l2_continuous : Continuous squared_l2 := by
  unfold squared_l2
  fun_prop

/-- `‖·‖²` is positive definite. -/
lemma squared_l2_is_pd : IsPositiveDefiniteFunction squared_l2 := by
  constructor
  · simp [squared_l2]
  · intro x hx
    simp only [squared_l2]
    exact pow_pos (norm_pos_iff.mpr hx) 2

/-- `‖·‖²` does not increase under `f₀`: `‖0.9·x‖² = 0.81·‖x‖² ≤ ‖x‖²`. -/
lemma squared_l2_nonincrease : LyapunovNonincrease squared_l2 f₀ := by
  intro x
  unfold squared_l2 f₀
  rw [norm_smul]
  have h09 : ‖(0.9 : ℝ)‖ = 0.9 := by norm_num
  rw [h09]
  nlinarith [norm_nonneg x, sq_nonneg ‖x‖]

/-- The origin is a fixed point of `f₀` — obtained for free from the Lyapunov
certificate via `zeroEquilibrium_of_lyapunov`, with no direct computation. -/
lemma f₀_zero_equilibrium_v2' : IsZeroEquilibrium f₀ :=
  zeroEquilibrium_of_lyapunov f₀ squared_l2 squared_l2_is_pd squared_l2_nonincrease


/-- `‖·‖²` satisfies the sublevel-trapping condition.
Because `V x = ‖x‖²`, the sphere bound forces `α ≤ ε²`, and then
`V x < α ≤ ε²` gives `‖x‖² < ε²`, hence `‖x‖ < ε`. The sublevel sets are balls,
so trapping is automatic — exactly the radially-unbounded case. -/
lemma squared_l2_sublevel_trapped : SublevelTrapped squared_l2 := by
  intro ε hε α _ hsphere x hVx
  unfold squared_l2 at hVx hsphere
  -- extract α ≤ ε² by evaluating the sphere bound at a concrete sphere point
  have hn : 0 < n := by norm_num [n]
  have hp_norm : ‖ε • EuclideanSpace.single (⟨0, hn⟩ : Fin n) (1 : ℝ)‖ = ε := by
    rw [norm_smul]
    simp [abs_of_pos hε]
  have hα_le : α ≤ ε^2 := by
    have h := hsphere _ hp_norm
    rwa [hp_norm] at h
  -- ‖x‖² < α ≤ ε², so ‖x‖ < ε
  have hx_sq : ‖x‖^2 < ε^2 := lt_of_lt_of_le hVx hα_le
  nlinarith [hx_sq, norm_nonneg x, hε]

/-- **The concrete system is stable.**
`f₀(x) = 0.9·x` is Lyapunov stable, certified by `V(x) = ‖x‖²` via the general
theorem. All four hypotheses are discharged by the lemmas above. -/
theorem f₀_is_stable : IsStableEpsDelta f₀ :=
  discrete_lyapunov_stability_epsdelta f₀ squared_l2
    squared_l2_continuous
    squared_l2_is_pd
    squared_l2_nonincrease
    squared_l2_sublevel_trapped
