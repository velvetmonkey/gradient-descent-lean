/-
Copyright (c) 2025 gradient-descent-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: gradient-descent-lean contributors
-/
import Mathlib

/-!
# Gradient Descent — Core Definitions

This module defines the key concepts for the convergence analysis of gradient descent
on smooth (strongly) convex functions over a real inner product space `E`:

* `IsLSmooth`: a function `f : E → ℝ` is *L-smooth* if it is everywhere differentiable
  and its gradient is L-Lipschitz.
* `IsStronglyConvex`: a function `f : E → ℝ` is *μ-strongly convex* if the first-order
  Taylor lower bound holds with curvature parameter μ.
* `gdSeq`: the gradient-descent iterates `x_{k+1} = x_k − α ∇f(x_k)`.
-/

open InnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ## L-Smoothness -/

/-- A function `f : E → ℝ` is **L-smooth** (with `L : NNReal`) when
    1. `f` is Fréchet differentiable everywhere, and
    2. its gradient `∇f` is `L`-Lipschitz.

This is equivalent to saying the Fréchet derivative is L-Lipschitz as an operator,
but using the gradient (Riesz representative) is more natural in the inner-product
space setting used for optimisation. -/
structure IsLSmooth (L : NNReal) (f : E → ℝ) : Prop where
  /-- `f` has a gradient at every point. -/
  hasGradientAt : ∀ x : E, HasGradientAt f (gradient f x) x
  /-- The gradient map is `L`-Lipschitz. -/
  grad_lipschitz : LipschitzWith L (gradient f)

/-- Unfolding lemma: `IsLSmooth L f` iff `f` is differentiable and `∇f` is
    `L`-Lipschitz.  This is `isLSmooth_def` requested in the task specification. -/
theorem isLSmooth_def (L : NNReal) (f : E → ℝ) :
    IsLSmooth L f ↔
      (∀ x, HasGradientAt f (gradient f x) x) ∧ LipschitzWith L (gradient f) :=
  ⟨fun h => ⟨h.hasGradientAt, h.grad_lipschitz⟩, fun ⟨hd, hl⟩ => ⟨hd, hl⟩⟩

/-! ## Strong Convexity -/

/-- A function `f : E → ℝ` is **μ-strongly convex** (with `μ ≥ 0`) when it is
    everywhere differentiable and, for all `x y`,
    `f(y) ≥ f(x) + ⟪∇f(x), y − x⟫ + μ/2 ‖y − x‖²`. -/
structure IsStronglyConvex (μ : ℝ) (f : E → ℝ) : Prop where
  /-- `f` has a gradient at every point. -/
  hasGradientAt : ∀ x : E, HasGradientAt f (gradient f x) x
  /-- First-order strong-convexity condition. -/
  lower_bound : ∀ x y : E,
    f y ≥ f x + @inner ℝ E _ (gradient f x) (y - x) + μ / 2 * ‖y - x‖ ^ 2

/-- Unfolding lemma for `IsStronglyConvex`. -/
theorem stronglyConvex_def (μ : ℝ) (f : E → ℝ) :
    IsStronglyConvex μ f ↔
      (∀ x, HasGradientAt f (gradient f x) x) ∧
      ∀ x y : E, f y ≥ f x + @inner ℝ E _ (gradient f x) (y - x) + μ / 2 * ‖y - x‖ ^ 2 :=
  ⟨fun h => ⟨h.hasGradientAt, h.lower_bound⟩, fun ⟨hd, hl⟩ => ⟨hd, hl⟩⟩

/-- Convexity is the special case `μ = 0`. -/
def IsConvex (f : E → ℝ) : Prop := IsStronglyConvex 0 f

/-- A convex function satisfies `f(y) ≥ f(x) + ⟪∇f(x), y − x⟫` for all `x y`. -/
theorem isConvex_lower_bound {f : E → ℝ} (hf : IsConvex f) (x y : E) :
    f y ≥ f x + @inner ℝ E _ (gradient f x) (y - x) := by
  have h := hf.lower_bound x y
  simp only [zero_div, zero_mul, add_zero] at h
  exact h

/-! ## Gradient Descent Sequence -/

/-- The gradient descent sequence with step size `α` starting from `x₀`:
    `x_{k+1} = x_k − α • ∇f(x_k)`. -/
def gdSeq (f : E → ℝ) (α : ℝ) (x₀ : E) : ℕ → E
  | 0     => x₀
  | n + 1 => gdSeq f α x₀ n - α • gradient f (gdSeq f α x₀ n)

@[simp]
theorem gdSeq_zero (f : E → ℝ) (α : ℝ) (x₀ : E) :
    gdSeq f α x₀ 0 = x₀ := rfl

@[simp]
theorem gdSeq_succ (f : E → ℝ) (α : ℝ) (x₀ : E) (n : ℕ) :
    gdSeq f α x₀ (n + 1) = gdSeq f α x₀ n - α • gradient f (gdSeq f α x₀ n) := rfl

/-! ## Minimiser -/

/-- `x*` is a (global) minimiser of `f`. -/
def IsMinimiser (f : E → ℝ) (xstar : E) : Prop :=
  ∀ y : E, f xstar ≤ f y

end
