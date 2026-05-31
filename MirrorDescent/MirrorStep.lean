/-
Copyright (c) 2025 Mirror Descent Library. All rights reserved.
Released under the MIT license.

# Mirror Descent Per-Step Bound

This file proves the per-step bound for mirror descent:
  f(x_k) - f(x*) ≤ (D_φ(x*, x_k) - D_φ(x*, x_{k+1})) / α_k + (α_k / (2σ)) ‖g_k‖²
-/
import MirrorDescent.BregmanDivergence

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ## Auxiliary lemmas -/

/-
Strong convexity gives a lower bound on Bregman divergence.
-/
omit [CompleteSpace E] in
theorem bregman_strong_convex_lower_bound {φ : E → ℝ} {gradφ : E → E} {C : Set E} {σ : ℝ}
    (hsc : FOStrongConvex φ gradφ C σ) {x y : E} (hx : x ∈ C) (hy : y ∈ C) :
    σ / 2 * ‖x - y‖ ^ 2 ≤ BregmanDiv φ gradφ x y := by
  unfold BregmanDiv; linarith [ hsc.2 x hx y hy ] ;

/-
From the mirror update optimality condition:
  ⟨∇φ(x_{k+1}) - ∇φ(x_k), u - x_{k+1}⟩ ≥ α_k⟨g_k, x_{k+1} - u⟩
-/
theorem mirror_update_gradient_bound (step : MirrorDescentStep E) (u : E) (hu : u ∈ step.M.C) :
    step.αk * @inner ℝ E _ step.gk (step.xk₁ - u) ≤
      @inner ℝ E _ (step.M.gradφ step.xk₁ - step.M.gradφ step.xk) (u - step.xk₁) := by
  have := step.hupdate u hu;
  simp_all +decide [ inner_add_left, inner_smul_left ];
  rw [ show step.xk₁ - u = - ( u - step.xk₁ ) by abel1, inner_neg_right ] ; linarith

/-
Young's inequality / AM-GM: a⟨g, v⟩ ≤ a²/(2σ)‖g‖² + σ/2‖v‖²
-/
omit [CompleteSpace E] in
theorem inner_le_young {g v : E} {a σ : ℝ} (hσ : 0 < σ) :
    a * @inner ℝ E _ g v ≤ a ^ 2 / (2 * σ) * ‖g‖ ^ 2 + σ / 2 * ‖v‖ ^ 2 := by
  by_contra! H;
  have := norm_sub_sq_real ( ( a / Real.sqrt σ ) • g ) ( Real.sqrt σ • v );
  norm_num [ norm_smul, inner_smul_left, inner_smul_right ] at *;
  ring_nf at *; norm_num [ hσ.le, hσ.ne' ] at *; nlinarith;

/-
The core estimate: α_k⟨g_k, x_k - u⟩ ≤ D(u,x_k) - D(u,x_{k+1}) + α_k²/(2σ)‖g_k‖²

  Proof outline:
  1. Split: α_k⟨g_k, x_k - u⟩ = α_k⟨g_k, x_k - x_{k+1}⟩ + α_k⟨g_k, x_{k+1} - u⟩
  2. From update: α_k⟨g_k, x_{k+1} - u⟩ ≤ ⟨∇φ(x_{k+1}) - ∇φ(x_k), u - x_{k+1}⟩
  3. Three-point: D(u,x_k) - D(u,x_{k+1}) = D(x_{k+1},x_k) + ⟨∇φ(x_{k+1}) - ∇φ(x_k), u - x_{k+1}⟩
  4. Young: α_k⟨g_k, x_k - x_{k+1}⟩ ≤ α_k²/(2σ)‖g_k‖² + σ/2‖x_k - x_{k+1}‖²
  5. Strong convexity: D(x_{k+1},x_k) ≥ σ/2‖x_{k+1} - x_k‖²
  Combining: α_k⟨g_k, x_k - u⟩ ≤ D(u,x_k) - D(u,x_{k+1}) + α_k²/(2σ)‖g_k‖²
-/
theorem mirror_update_inner_bound (step : MirrorDescentStep E) (u : E) (hu : u ∈ step.M.C) :
    step.αk * @inner ℝ E _ step.gk (step.xk - u) ≤
      BregmanDiv step.M.φ step.M.gradφ u step.xk -
        BregmanDiv step.M.φ step.M.gradφ u step.xk₁ +
      step.αk ^ 2 / (2 * step.M.σ) * ‖step.gk‖ ^ 2 := by
  have := bregman_strong_convex_lower_bound step.M.hφ_strong step.hxk₁ step.hxk;
  -- Apply the inner_le_young lemma with g = step.gk, v = step.xk - step.xk₁, a = step.αk, and σ = step.M.σ.
  have h_young : step.αk * inner ℝ step.gk (step.xk - step.xk₁) ≤ (step.αk ^ 2 / (2 * step.M.σ)) * ‖step.gk‖ ^ 2 + (step.M.σ / 2) * ‖step.xk - step.xk₁‖ ^ 2 := by
    exact inner_le_young step.M.hφ_strong.1;
  have := BregmanDiv.three_point step.M.φ step.M.gradφ u step.xk₁ step.xk;
  have := mirror_update_gradient_bound step u hu;
  norm_num [ norm_sub_rev ] at *;
  rw [ show step.xk - u = ( step.xk - step.xk₁ ) + ( step.xk₁ - u ) by abel1, inner_add_right ] ; linarith

/-
**Mirror descent per-step bound.**
  `f(x_k) - f(x*) ≤ (D_φ(x*, x_k) - D_φ(x*, x_{k+1})) / α_k + (α_k/(2σ)) ‖g_k‖²`
  where σ is the strong convexity modulus of the mirror map φ.
-/
theorem mirror_descent_step_bound (step : MirrorDescentStep E) :
    step.f step.xk - step.f step.xstar ≤
      (BregmanDiv step.M.φ step.M.gradφ step.xstar step.xk -
        BregmanDiv step.M.φ step.M.gradφ step.xstar step.xk₁) / step.αk +
      step.αk / (2 * step.M.σ) * ‖step.gk‖ ^ 2 := by
  rw [ div_add', le_div_iff₀ ];
  · have := mirror_update_inner_bound step step.xstar step.hxstar;
    convert this.trans' _ using 1;
    · ring;
    · have := step.hgk.2 step.xstar step.hxstar;
      rw [ inner_sub_right ] at * ; nlinarith [ step.hαk ];
  · exact step.hαk;
  · exact ne_of_gt step.hαk

end