/-
Copyright (c) 2025 Mirror Descent Library. All rights reserved.
Released under the MIT license.

# Core Definitions for Mirror Descent

This file defines the Bregman divergence, mirror maps, subgradients,
and strong convexity conditions used throughout the library.
-/
import Mathlib

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ## Bregman Divergence -/

/-- The Bregman divergence associated with a function `φ` and a choice of gradient `∇φ`.
  `BregmanDiv φ gradφ x y = φ(x) - φ(y) - ⟨∇φ(y), x - y⟩` -/
def BregmanDiv (φ : E → ℝ) (gradφ : E → E) (x y : E) : ℝ :=
  φ x - φ y - @inner ℝ E _ (gradφ y) (x - y)

/-! ## Subgradient -/

/-- `g` is a subgradient of `f` at `x` over convex set `C` if
  `∀ y ∈ C, f(y) ≥ f(x) + ⟨g, y - x⟩`. -/
def IsSubgradientAt (f : E → ℝ) (g : E) (C : Set E) (x : E) : Prop :=
  x ∈ C ∧ ∀ y ∈ C, f x + @inner ℝ E _ g (y - x) ≤ f y

/-! ## First-Order Convexity Conditions -/

/-- A function `φ` with gradient `gradφ` satisfies the first-order convexity condition
  on set `C` if `φ(x) ≥ φ(y) + ⟨∇φ(y), x - y⟩` for all `x, y ∈ C`. -/
def FirstOrderConvex (φ : E → ℝ) (gradφ : E → E) (C : Set E) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, φ y + @inner ℝ E _ (gradφ y) (x - y) ≤ φ x

/-- A function `φ` with gradient `gradφ` satisfies the strict first-order convexity condition
  on set `C` if `φ(x) > φ(y) + ⟨∇φ(y), x - y⟩` for all distinct `x, y ∈ C`. -/
def StrictFirstOrderConvex (φ : E → ℝ) (gradφ : E → E) (C : Set E) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, x ≠ y → φ y + @inner ℝ E _ (gradφ y) (x - y) < φ x

/-- A function `φ` with gradient `gradφ` is `σ`-strongly convex in the first-order sense on `C`:
  `φ(x) ≥ φ(y) + ⟨∇φ(y), x - y⟩ + (σ/2)‖x - y‖²` for all `x, y ∈ C`. -/
def FOStrongConvex (φ : E → ℝ) (gradφ : E → E) (C : Set E) (σ : ℝ) : Prop :=
  0 < σ ∧ ∀ x ∈ C, ∀ y ∈ C,
    φ y + @inner ℝ E _ (gradφ y) (x - y) + σ / 2 * ‖x - y‖ ^ 2 ≤ φ x

/-! ## Mirror Map -/

/-- A mirror map packages a strictly convex differentiable function `φ` on a convex set `C`,
  together with its gradient and strong convexity modulus `σ`. -/
structure MirrorMap (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] where
  /-- The convex domain -/
  C : Set E
  /-- Convexity of the domain -/
  hC : Convex ℝ C
  /-- The mirror map / distance-generating function -/
  φ : E → ℝ
  /-- The gradient of φ -/
  gradφ : E → E
  /-- φ is differentiable with gradient gradφ on C -/
  hφ_grad : ∀ x ∈ C, HasGradientAt φ (gradφ x) x
  /-- The strict first-order convexity condition (follows from strict convexity + differentiability) -/
  hφ_strict_convex : StrictFirstOrderConvex φ gradφ C
  /-- Strong convexity modulus -/
  σ : ℝ
  /-- First-order strong convexity (follows from σ-strong convexity + differentiability) -/
  hφ_strong : FOStrongConvex φ gradφ C σ

namespace MirrorMap

variable (M : MirrorMap E)

/-- A mirror map satisfies the (non-strict) first-order convexity condition. -/
theorem firstOrderConvex : FirstOrderConvex M.φ M.gradφ M.C := by
  intro x hx y hy
  have h := M.hφ_strong.2 x hx y hy
  have hσ := M.hφ_strong.1
  have : 0 ≤ M.σ / 2 * ‖x - y‖ ^ 2 := by positivity
  linarith

/-- The strong convexity modulus is positive. -/
theorem σ_pos : 0 < M.σ := M.hφ_strong.1

end MirrorMap

/-! ## Mirror Descent Step -/

/-- The data for a single step of mirror descent. -/
structure MirrorDescentStep (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] where
  /-- The mirror map -/
  M : MirrorMap E
  /-- The objective function -/
  f : E → ℝ
  /-- Current iterate -/
  xk : E
  /-- Next iterate -/
  xk₁ : E
  /-- Optimal point -/
  xstar : E
  /-- Subgradient at xk -/
  gk : E
  /-- Step size -/
  αk : ℝ
  /-- Membership conditions -/
  hxk : xk ∈ M.C
  hxk₁ : xk₁ ∈ M.C
  hxstar : xstar ∈ M.C
  /-- Step size is positive -/
  hαk : 0 < αk
  /-- Subgradient condition -/
  hgk : IsSubgradientAt f gk M.C xk
  /-- Mirror descent update: the Bregman projection optimality condition.
      x_{k+1} = argmin_{x ∈ C} {α_k ⟨g_k, x⟩ + D_φ(x, x_k)} gives:
      ∀ u ∈ C: ⟨∇φ(x_{k+1}) - ∇φ(x_k) + α_k · g_k, u - x_{k+1}⟩ ≥ 0 -/
  hupdate : ∀ u ∈ M.C,
    0 ≤ @inner ℝ E _ (M.gradφ xk₁ - M.gradφ xk + αk • gk) (u - xk₁)

end
