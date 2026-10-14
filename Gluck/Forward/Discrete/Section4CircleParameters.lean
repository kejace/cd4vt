import Gluck.Discrete.CircleParameterGeometry

/-!
# Circle parameters for Dahlberg's Section 4 construction

This file turns boundary points of a Euclidean circle into honest real angle
lifts.  Besides the standard `[0, 2π)` window, the main API allows an
arbitrary base angle `β`; this is the form needed to order a finite family of
minimal-circle contacts relative to a chosen endpoint of the positive chain.
-/

namespace Gluck.Forward

open Gluck.Discrete

/-- The polar formula for a point whose distance from `O` is `R`. -/
theorem circlePoint_arg_of_dist_eq
    {O P : ℂ} {R : ℝ} (hP : dist O P = R) :
    P = circlePoint O R (Complex.arg (P - O)) := by
  change P = circleMap O R (Complex.arg (P - O))
  rw [circleMap]
  have hnorm : ‖P - O‖ = R := by
    rw [← hP, dist_comm, dist_eq_norm]
  rw [← hnorm, Complex.norm_mul_exp_arg_mul_I]
  ring

/-- Every point satisfying the circle equation has an angle in the standard
half-open window `[0, 2π)`. -/
theorem exists_circlePoint_eq_of_dist_eq
    {O P : ℂ} {R : ℝ} (hP : dist O P = R) :
    ∃ θ : ℝ, θ ∈ Set.Ico 0 (2 * Real.pi) ∧ P = circlePoint O R θ := by
  by_cases harg : 0 ≤ Complex.arg (P - O)
  · refine ⟨Complex.arg (P - O), ⟨harg, ?_⟩, circlePoint_arg_of_dist_eq hP⟩
    linarith [Complex.arg_le_pi (P - O), Real.pi_pos]
  · refine ⟨Complex.arg (P - O) + 2 * Real.pi, ⟨?_, ?_⟩, ?_⟩
    · have hlower := Complex.neg_pi_lt_arg (P - O)
      linarith [Real.pi_pos]
    · have hneg : Complex.arg (P - O) < 0 := lt_of_not_ge harg
      linarith [Real.pi_pos]
    · rw [circlePoint_add_two_pi]
      exact circlePoint_arg_of_dist_eq hP

/-- Every circle point has an angle lift in the half-open window based at an
arbitrary real angle `β`. -/
theorem exists_circlePoint_eq_mem_angleWindow
    {O P : ℂ} {R : ℝ} (hP : dist O P = R) (β : ℝ) :
    ∃ θ : ℝ, θ ∈ Set.Ico β (β + 2 * Real.pi) ∧ P = circlePoint O R θ := by
  obtain ⟨α, -, hPα⟩ := exists_circlePoint_eq_of_dist_eq hP
  obtain ⟨θ, hθ, hαθ⟩ :=
    (periodic_circleMap O R).exists_mem_Ico Real.two_pi_pos α β
  exact ⟨θ, hθ, hPα.trans hαθ⟩





end Gluck.Forward
