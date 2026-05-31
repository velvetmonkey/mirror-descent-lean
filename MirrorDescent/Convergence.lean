/-
Copyright (c) 2025 Mirror Descent Library. All rights reserved.
Released under the MIT license.

# Mirror Descent Convergence

This file proves the O(1/√K) convergence rate for mirror descent
with appropriate step size selection.
-/
import MirrorDescent.MirrorStep

open Finset

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ## Mirror Descent Trajectory -/

/-- A mirror descent trajectory packages all the data for K steps. -/
structure MirrorDescentTrajectory (E : Type*) [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [CompleteSpace E] where
  /-- Number of steps -/
  K : ℕ
  /-- At least one step -/
  hK : 0 < K
  /-- The mirror map -/
  M : MirrorMap E
  /-- The objective function -/
  f : E → ℝ
  /-- Iterates x_0, x_1, ..., x_K -/
  x : ℕ → E
  /-- Optimal point -/
  xstar : E
  /-- Subgradients -/
  g : ℕ → E
  /-- Step sizes -/
  α : ℕ → ℝ
  /-- All iterates are in C -/
  hx_mem : ∀ k, x k ∈ M.C
  /-- Optimal point is in C -/
  hxstar : xstar ∈ M.C
  /-- Step sizes are positive -/
  hα_pos : ∀ k, 0 < α k
  /-- Subgradient condition at each step -/
  hg : ∀ k, k < K → IsSubgradientAt f (g k) M.C (x k)
  /-- Mirror update condition at each step -/
  hupdate : ∀ k, k < K → ∀ u ∈ M.C,
    0 ≤ @inner ℝ E _ (M.gradφ (x (k + 1)) - M.gradφ (x k) + α k • g k) (u - x (k + 1))
  /-- Uniform bound on subgradient norms -/
  G : ℝ
  hG_pos : 0 < G
  hG : ∀ k, k < K → ‖g k‖ ≤ G
  /-- x* is optimal -/
  hopt : ∀ y ∈ M.C, f xstar ≤ f y

namespace MirrorDescentTrajectory

variable (traj : MirrorDescentTrajectory E)

/-
The per-step bound holds at each step k < K.
-/
theorem step_bound (k : ℕ) (hk : k < traj.K) :
    traj.f (traj.x k) - traj.f traj.xstar ≤
      (BregmanDiv traj.M.φ traj.M.gradφ traj.xstar (traj.x k) -
        BregmanDiv traj.M.φ traj.M.gradφ traj.xstar (traj.x (k + 1))) / traj.α k +
      traj.α k / (2 * traj.M.σ) * ‖traj.g k‖ ^ 2 := by
  by_contra h_contra;
  convert mirror_descent_step_bound ( MirrorDescentStep.mk traj.M traj.f ( traj.x k ) ( traj.x ( k + 1 ) ) traj.xstar ( traj.g k ) ( traj.α k ) ( traj.hx_mem k ) ( traj.hx_mem ( k + 1 ) ) traj.hxstar ( traj.hα_pos k ) ( traj.hg k hk ) ( traj.hupdate k hk ) ) using 1;
  grind +qlia

/-
Telescoping: the sum of per-step bounds.
-/
theorem telescoping_sum :
    ∑ k ∈ range traj.K, (traj.f (traj.x k) - traj.f traj.xstar) ≤
      ∑ k ∈ range traj.K,
        ((BregmanDiv traj.M.φ traj.M.gradφ traj.xstar (traj.x k) -
          BregmanDiv traj.M.φ traj.M.gradφ traj.xstar (traj.x (k + 1))) / traj.α k +
        traj.α k / (2 * traj.M.σ) * ‖traj.g k‖ ^ 2) := by
  exact Finset.sum_le_sum fun k hk => traj.step_bound k ( Finset.mem_range.mp hk )

/-
**Mirror descent convergence with constant step size.**
  If α_k = α for all k, then the averaged regret satisfies:
  (1/K) ∑ₖ (f(xₖ) - f(x*)) ≤ D_φ(x*, x₀) / (K·α) + α·G² / (2σ)

  Setting α = √(2σ D₀ / (G² K)) gives the optimal O(1/√K) rate.
-/
theorem convergence_constant_step
    (α : ℝ) (hα : 0 < α) (hαk : ∀ k, traj.α k = α)
    (D₀ : ℝ) (_hD₀_pos : 0 ≤ D₀)
    (hD₀ : BregmanDiv traj.M.φ traj.M.gradφ traj.xstar (traj.x 0) = D₀) :
    (∑ k ∈ range traj.K, (traj.f (traj.x k) - traj.f traj.xstar)) / traj.K ≤
      D₀ / (traj.K * α) + α * traj.G ^ 2 / (2 * traj.M.σ) := by
  rw [ ← hD₀, div_le_iff₀ ];
  · refine' le_trans _ ( le_trans ( traj.telescoping_sum ) _ );
    · rfl;
    · simp +decide only [hαk, sum_add_distrib];
      rw [ ← Finset.sum_div _ _ _, Finset.sum_range_sub' ];
      rw [ add_mul ];
      refine' add_le_add _ _;
      · rw [ div_mul_eq_mul_div, div_le_div_iff₀ ] <;> try positivity;
        · nlinarith [ show 0 ≤ BregmanDiv traj.M.φ traj.M.gradφ traj.xstar ( traj.x traj.K ) from BregmanDiv.nonneg ( traj.M.firstOrderConvex ) traj.hxstar ( traj.hx_mem _ ), show 0 ≤ ( traj.K : ℝ ) * α by positivity ];
        · exact mul_pos ( Nat.cast_pos.mpr traj.hK ) hα;
      · refine' le_trans ( Finset.sum_le_sum fun i hi => mul_le_mul_of_nonneg_left ( pow_le_pow_left₀ ( norm_nonneg _ ) ( traj.hG i ( Finset.mem_range.mp hi ) ) 2 ) ( by exact div_nonneg hα.le ( mul_nonneg zero_le_two ( le_of_lt ( traj.M.σ_pos ) ) ) ) ) _ ; norm_num ; ring_nf ; norm_num;
  · exact Nat.cast_pos.mpr traj.hK

/-
**O(1/√K) convergence rate.**
  With optimal constant step size α = √(2σ D₀ / (G² K)), the averaged regret is bounded by
  G · √(2 D₀ / (σ K)), which is O(1/√K).
-/
theorem convergence_rate
    (D₀ : ℝ) (hD₀ : 0 < D₀)
    (hD₀_eq : BregmanDiv traj.M.φ traj.M.gradφ traj.xstar (traj.x 0) = D₀)
    (hαk : ∀ k, traj.α k = Real.sqrt (2 * traj.M.σ * D₀ / (traj.G ^ 2 * traj.K))) :
    (∑ k ∈ range traj.K, (traj.f (traj.x k) - traj.f traj.xstar)) / traj.K ≤
      traj.G * Real.sqrt (2 * D₀ / (traj.M.σ * traj.K)) := by
  convert MirrorDescentTrajectory.convergence_constant_step traj _ _ hαk D₀ hD₀.le hD₀_eq using 1;
  · rw [ div_add_div, mul_comm, eq_div_iff ];
    · ring;
      rw [ Real.sq_sqrt ];
      · have := traj.M.σ_pos; ( have := traj.hG_pos; ( have := traj.hK; ( norm_num [ mul_assoc, mul_comm, mul_left_comm, ne_of_gt, * ] at *; ) ) );
        field_simp;
        rw [ Real.sq_sqrt ( by positivity ), Real.sq_sqrt ( by positivity ), Real.sqrt_sq ( by positivity ) ] ; ring;
      · exact mul_nonneg ( mul_nonneg ( mul_nonneg ( mul_nonneg hD₀.le ( le_of_lt traj.M.σ_pos ) ) ( inv_nonneg.2 ( Nat.cast_nonneg _ ) ) ) ( sq_nonneg _ ) ) zero_le_two;
    · exact mul_ne_zero ( mul_ne_zero ( Nat.cast_ne_zero.mpr traj.hK.ne' ) ( Real.sqrt_ne_zero'.mpr ( div_pos ( mul_pos ( mul_pos two_pos traj.M.σ_pos ) hD₀ ) ( mul_pos ( sq_pos_of_pos traj.hG_pos ) ( Nat.cast_pos.mpr traj.hK ) ) ) ) ) ( mul_ne_zero two_ne_zero traj.M.σ_pos.ne' );
    · exact mul_ne_zero ( Nat.cast_ne_zero.mpr traj.hK.ne' ) ( Real.sqrt_ne_zero'.mpr ( div_pos ( mul_pos ( mul_pos two_pos ( traj.M.σ_pos ) ) hD₀ ) ( mul_pos ( sq_pos_of_pos traj.hG_pos ) ( Nat.cast_pos.mpr traj.hK ) ) ) );
    · exact mul_ne_zero two_ne_zero ( ne_of_gt traj.M.σ_pos );
  · exact Real.sqrt_pos.mpr ( div_pos ( mul_pos ( mul_pos two_pos traj.M.σ_pos ) hD₀ ) ( mul_pos ( sq_pos_of_pos traj.hG_pos ) ( Nat.cast_pos.mpr traj.hK ) ) )

end MirrorDescentTrajectory

end