/-
Copyright (c) 2025 gradient-descent-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: gradient-descent-lean contributors
-/
import Mathlib
import GradientDescent.Defs
import GradientDescent.Smooth
import GradientDescent.Convex

/-!
# Gradient Descent Convergence Theorems

This module proves the two headline convergence rates for gradient descent:

1. **Sublinear O(1/k) convergence** for convex L-smooth functions
   (`gd_convex_convergence`).
2. **Linear (geometric) convergence** for μ-strongly convex L-smooth functions
   (`gd_strongly_convex_convergence`).

## Strategy

Both proofs proceed by establishing a per-step progress bound and then
telescoping (or iterating) it across `k` steps.
-/

open InnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ## Norm expansion helper -/

/-
Pure norm expansion: `‖(a - r•g) - b‖² = ‖a-b‖² - 2r⟪g, a-b⟫ + r²‖g‖²`.
-/
theorem norm_sq_gd_expand (a b g : E) (r : ℝ) :
    ‖(a - r • g) - b‖ ^ 2 =
      ‖a - b‖ ^ 2 - 2 * r * @inner ℝ E _ g (a - b) + r ^ 2 * ‖g‖ ^ 2 := by
  rw [ show a - r • g - b = ( a - b ) - r • g by abel1, @norm_sub_sq ℝ ] ; simp +decide [ inner_smul_right, real_inner_comm ] ; ring;
  simp +decide [ norm_smul, mul_pow ]

/-! ## Per-step distance bound -/

/-- After one gradient step with step size `α ≥ 0`, the distance to any `x*` satisfies:
    `‖x_{k+1} - x*‖² ≤ ‖x_k - x*‖² - 2α⟪∇f(x_k), x_k - x*⟫ + α²‖∇f(x_k)‖²`. -/
theorem gd_step_distance_sq (xk xstar g : E) (α : ℝ) :
    ‖(xk - α • g) - xstar‖ ^ 2 =
      ‖xk - xstar‖ ^ 2 - 2 * α * @inner ℝ E _ g (xk - xstar) + α ^ 2 * ‖g‖ ^ 2 := by
  exact norm_sq_gd_expand xk xstar g α

/-! ## Convex convergence: O(1/k) rate -/

/-
**Correct per-step distance bound** for convex L-smooth functions.
    For `α = 1/L`:
    `‖x_{k+1} - x*‖² ≤ ‖x_k - x*‖² - 2α(f(x_{k+1}) - f(x*))`.

    Proof: combine norm expansion, convexity, and descent lemma.
    The α²‖g‖² term cancels with 2α(f(xk) - f(x_{k+1})) from the descent lemma.
-/
theorem gd_convex_step_bound {L : NNReal} {f : E → ℝ}
    (hf : IsLSmooth L f) (hconv : IsConvex f)
    {xstar : E} (hmin : IsMinimiser f xstar)
    (hL_pos : (0 : ℝ) < L) (xk : E) :
    let α := 1 / (L : ℝ)
    let xk₁ := xk - α • gradient f xk
    ‖xk₁ - xstar‖ ^ 2 ≤ ‖xk - xstar‖ ^ 2 - 2 * α * (f xk₁ - f xstar) := by
  have := norm_sq_gd_expand xk xstar ( gradient f xk ) ( 1 / L );
  -- By convexity, we have:
  have h_convex : ⟪gradient f xk, xk - xstar⟫_ℝ ≥ f xk - f xstar := by
    have := isConvex_lower_bound hconv xk xstar;
    rw [ inner_sub_right ] at * ; linarith;
  have := descent_lemma hf xk ( 1 / L ) ( by positivity ) ( by simp +decide [ hL_pos.le ] ) hL_pos; simp_all +decide [ sq, mul_assoc, mul_comm, mul_left_comm ] ;
  nlinarith [ inv_pos.2 ( show 0 < ( L : ℝ ) by positivity ), mul_inv_cancel₀ ( ne_of_gt ( show 0 < ( L : ℝ ) by positivity ) ) ]

/-
The descent lemma implies the function values are non-increasing along
    the gradient descent sequence (with `α = 1/L`).
-/
theorem gd_descent_nonincreasing {L : NNReal} {f : E → ℝ}
    (hf : IsLSmooth L f) (hL_pos : (0 : ℝ) < L) (x₀ : E) (k : ℕ) :
    let x := gdSeq f (1 / (L : ℝ)) x₀
    f (x (k + 1)) ≤ f (x k) := by
  convert descent_lemma hf ( gdSeq f ( 1 / ( L : ℝ ) ) x₀ k ) ( 1 / ( L : ℝ ) ) ( by positivity ) ( by simp +decide [ hL_pos ] ) hL_pos |> le_trans <| sub_le_self _ <| by positivity using 1

/-
**Telescoping lemma**: summing the per-step distance decrease over `k` steps.
    `2α * ∑_{i=0}^{k-1} (f(x_{i+1}) - f(x*)) ≤ ‖x₀ - x*‖²`.
-/
theorem gd_convex_telescope {L : NNReal} {f : E → ℝ}
    (hf : IsLSmooth L f) (hconv : IsConvex f)
    {xstar : E} (hmin : IsMinimiser f xstar)
    (hL_pos : (0 : ℝ) < L) (x₀ : E) (k : ℕ) :
    let α := 1 / (L : ℝ)
    let x := gdSeq f α x₀
    2 * α * (∑ i ∈ Finset.range k, (f (x (i + 1)) - f xstar)) ≤ ‖x₀ - xstar‖ ^ 2 := by
  -- Apply the convex step bound to each term in the sum.
  have h_sum : ∀ k, let α := 1 / (L : ℝ);
    let x := gdSeq f α x₀;
    2 * α * ∑ i ∈ Finset.range k, (f (x (i + 1)) - f xstar) + ‖x k - xstar‖ ^ 2 ≤ ‖x 0 - xstar‖ ^ 2 := by
      intro k
      induction' k with k ih;
      · simp +decide;
      · simp_all +decide [ Finset.sum_range_succ ];
        have := gd_convex_step_bound hf hconv hmin hL_pos ( gdSeq f ( L : ℝ ) ⁻¹ x₀ k );
        norm_num at * ; linarith;
  simpa using le_trans ( le_add_of_nonneg_right ( sq_nonneg _ ) ) ( h_sum k )

/-
**O(1/k) convergence for convex gradient descent**.
    For a convex L-smooth `f` with minimiser `x*` and step size `α = 1/L`:

    `f(x_k) - f(x*) ≤ L * ‖x₀ - x*‖² / (2 * k)`

    Proof: by telescoping, `k * (f(x_k) - f(x*)) ≤ Σ (f(x_{i+1}) - f(x*))` since
    the function values are non-increasing, and this sum is bounded by
    `‖x₀ - x*‖² / (2α) = L * ‖x₀ - x*‖² / 2`.
-/
theorem gd_convex_convergence {L : NNReal} {f : E → ℝ}
    (hf : IsLSmooth L f) (hconv : IsConvex f)
    {xstar : E} (hmin : IsMinimiser f xstar)
    (hL_pos : (0 : ℝ) < L) (x₀ : E) (k : ℕ) (hk : 0 < k) :
    let x := gdSeq f (1 / (L : ℝ)) x₀
    f (x k) - f xstar ≤ (L : ℝ) * ‖x₀ - xstar‖ ^ 2 / (2 * k) := by
  have := gd_convex_telescope hf hconv hmin hL_pos x₀ k;
  -- By the properties of the gradient descent sequence, we know that $f(x_k) \leq f(x_i)$ for all $i < k$.
  have h_monotone : ∀ i < k, f (gdSeq f (1 / (L : ℝ)) x₀ k) ≤ f (gdSeq f (1 / (L : ℝ)) x₀ (i + 1)) := by
    intro i hi;
    exact Nat.le_induction ( by rfl ) ( fun n hn ih => by simpa using le_trans ( gd_descent_nonincreasing hf hL_pos x₀ n ) ih ) k ( show i + 1 ≤ k from by linarith );
  rw [ le_div_iff₀ ( by positivity ) ];
  norm_num at *;
  have := Finset.sum_le_sum fun i ( hi : i ∈ Finset.range k ) => h_monotone i ( Finset.mem_range.mp hi );
  simp_all +decide [ mul_comm, mul_assoc, mul_left_comm ];
  rw [ inv_mul_le_iff₀ ( by positivity ) ] at * ; linarith

/-! ## Strongly convex convergence: geometric rate -/

/-
**Per-step contraction** for strongly convex gradient descent.
    For a μ-strongly convex L-smooth function with step size `α ≤ 1/L`:
    `‖x_{k+1} - x*‖² ≤ (1 - αμ) * ‖x_k - x*‖²`

    Proof: expand `‖x_{k+1} - x*‖²` using the norm identity, use strong convexity
    `⟪∇f(x_k), x_k - x*⟫ ≥ μ/2 ‖x_k - x*‖² + (f(x_k) - f(x*))`,
    and descent lemma `α‖∇f(x_k)‖² ≤ 2(f(x_k) - f(x_{k+1})) ≤ 2(f(x_k) - f(x*))`.
-/
theorem gd_strongly_convex_step {L : NNReal} {μ : ℝ} {f : E → ℝ}
    (hf : IsLSmooth L f) (hsc : IsStronglyConvex μ f)
    {xstar : E} (hmin : IsMinimiser f xstar)
    (hgrad : gradient f xstar = 0)
    (hL_pos : (0 : ℝ) < L)
    (_hμ_pos : 0 < μ)
    (α : ℝ) (hα_pos : 0 < α) (hα_le : α ≤ 1 / (L : ℝ))
    (xk : E) :
    ‖(xk - α • gradient f xk) - xstar‖ ^ 2 ≤ (1 - α * μ) * ‖xk - xstar‖ ^ 2 := by
  -- By the descent lemma, we have $α‖g‖² ≤ 2(f(xk) - f(x_{k+1}))$.
  have h_desc : α * ‖gradient f xk‖ ^ 2 ≤ 2 * (f xk - f (xk - α • gradient f xk)) := by
    have := descent_lemma hf xk α hα_pos hα_le hL_pos;
    linarith;
  have := norm_sq_gd_expand xk xstar ( gradient f xk ) α;
  have := stronglyConvex_inner_gradient_bound hsc hgrad xk;
  nlinarith [ hmin ( xk - α • gradient f xk ) ]

/-
**Geometric convergence for strongly convex gradient descent**.
    For a μ-strongly convex L-smooth `f` with minimiser `x*` and step size `α`:

    `‖x_k - x*‖² ≤ (1 - αμ)^k * ‖x₀ - x*‖²`

    This is proved by induction, applying `gd_strongly_convex_step` at each step.
-/
theorem gd_strongly_convex_convergence {L : NNReal} {μ : ℝ} {f : E → ℝ}
    (hf : IsLSmooth L f) (hsc : IsStronglyConvex μ f)
    {xstar : E} (hmin : IsMinimiser f xstar)
    (hgrad : gradient f xstar = 0)
    (hL_pos : (0 : ℝ) < L)
    (hμ_pos : 0 < μ)
    (α : ℝ) (hα_pos : 0 < α) (hα_le : α ≤ 1 / (L : ℝ))
    (x₀ : E) (k : ℕ) :
    let x := gdSeq f α x₀
    ‖x k - xstar‖ ^ 2 ≤ (1 - α * μ) ^ k * ‖x₀ - xstar‖ ^ 2 := by
  by_cases h₂ : 1 - α * μ ≥ 0;
  · exact Nat.recOn k ( by simp +decide ) fun n ihn => by simpa only [ pow_succ', mul_assoc, mul_left_comm, gdSeq_succ ] using le_trans ( gd_strongly_convex_step hf hsc hmin hgrad hL_pos hμ_pos α hα_pos hα_le _ ) ( mul_le_mul_of_nonneg_left ihn ( by positivity ) ) ;
  · have := gd_strongly_convex_step hf hsc hmin hgrad hL_pos hμ_pos α hα_pos hα_le;
    have h_zero : ∀ k ≥ 1, gdSeq f α x₀ k = xstar := by
      intro k hk
      induction' hk with k hk ih;
      · specialize this x₀;
        contrapose! this;
        exact lt_of_lt_of_le ( mul_neg_of_neg_of_pos ( not_le.mp h₂ ) ( sq_pos_of_pos ( norm_pos_iff.mpr ( sub_ne_zero.mpr ( by aesop ) ) ) ) ) ( sq_nonneg _ );
      · simp +decide [ *, gdSeq ];
    by_cases hk : 1 ≤ k <;> simp_all +decide;
    specialize this x₀;
    contrapose! this;
    exact lt_of_lt_of_le ( mul_neg_of_neg_of_pos ( by linarith ) ( sq_pos_of_pos ( norm_pos_iff.mpr ( sub_ne_zero.mpr ( by aesop_cat ) ) ) ) ) ( sq_nonneg _ )

end