/-
Copyright (c) 2025 Mirror Descent Library. All rights reserved.
Released under the MIT license.

# Bregman Divergence Properties

This file proves fundamental properties of the Bregman divergence:
- `bregman_nonneg`: D_φ(x, y) ≥ 0, with equality iff x = y
- `bregman_three_point`: the three-point identity
-/
import MirrorDescent.Defs

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

namespace BregmanDiv

/-! ## Non-negativity of Bregman Divergence -/

/-- The Bregman divergence is non-negative when φ satisfies the first-order
  convexity condition. -/
theorem nonneg {φ : E → ℝ} {gradφ : E → E} {C : Set E}
    (hconv : FirstOrderConvex φ gradφ C) {x y : E} (hx : x ∈ C) (hy : y ∈ C) :
    0 ≤ BregmanDiv φ gradφ x y := by
  exact sub_nonneg_of_le (by linarith [hconv x hx y hy])

/-- If φ is strictly first-order convex, then D_φ(x, y) = 0 implies x = y. -/
theorem eq_of_div_eq_zero {φ : E → ℝ} {gradφ : E → E} {C : Set E}
    (hconv : StrictFirstOrderConvex φ gradφ C) {x y : E} (hx : x ∈ C) (hy : y ∈ C)
    (h : BregmanDiv φ gradφ x y = 0) : x = y := by
  unfold BregmanDiv at h
  exact Classical.not_not.1 fun hxy => by linarith [hconv x hx y hy hxy]

/-- If x = y then D_φ(x, y) = 0. -/
theorem div_eq_zero_of_eq {φ : E → ℝ} {gradφ : E → E} (x : E) :
    BregmanDiv φ gradφ x x = 0 := by
  unfold BregmanDiv; simp +decide

/-- **Bregman non-negativity with equality characterization.**
  D_φ(x, y) ≥ 0 with equality if and only if x = y,
  when φ is strictly first-order convex. -/
theorem nonneg_iff_eq {φ : E → ℝ} {gradφ : E → E} {C : Set E}
    (hfoc : FirstOrderConvex φ gradφ C)
    (hstrict : StrictFirstOrderConvex φ gradφ C)
    {x y : E} (hx : x ∈ C) (hy : y ∈ C) :
    0 ≤ BregmanDiv φ gradφ x y ∧ (BregmanDiv φ gradφ x y = 0 ↔ x = y) :=
  ⟨nonneg hfoc hx hy,
    ⟨eq_of_div_eq_zero hstrict hx hy, fun h => h ▸ div_eq_zero_of_eq _⟩⟩

/-! ## Three-Point Identity -/

/-- **Bregman three-point identity.**
  `D_φ(x, z) = D_φ(x, y) + D_φ(y, z) + ⟨∇φ(y) - ∇φ(z), x - y⟩`
  This is a purely algebraic identity. -/
theorem three_point (φ : E → ℝ) (gradφ : E → E) (x y z : E) :
    BregmanDiv φ gradφ x z =
      BregmanDiv φ gradφ x y + BregmanDiv φ gradφ y z +
        @inner ℝ E _ (gradφ y - gradφ z) (x - y) := by
  unfold BregmanDiv
  simp +decide [inner_sub_left, inner_sub_right]; ring

end BregmanDiv

end
