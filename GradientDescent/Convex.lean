/-
Copyright (c) 2025 gradient-descent-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: gradient-descent-lean contributors
-/
import Mathlib
import GradientDescent.Defs

/-!
# Properties of (Strongly) Convex Functions

This module collects useful consequences of (strong) convexity that feed into
the gradient-descent convergence proofs.

## Main results

* `isConvex_minimiser_gradient_zero`: at a minimiser of a convex function, the
  gradient vanishes.
* `stronglyConvex_unique_minimiser`: a strongly convex function (μ > 0) has at
  most one minimiser.
* `stronglyConvex_dist_bound`: distance to minimiser is controlled by the gradient norm.
-/

open InnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-
At a minimiser of a differentiable convex function, the gradient is zero.
-/
theorem isConvex_minimiser_gradient_zero {f : E → ℝ} (hf : IsConvex f)
    {xstar : E} (hmin : IsMinimiser f xstar) :
    gradient f xstar = 0 := by
  convert ( hasGradientAt_iff_isLittleO_nhds_zero.1 ( hf.1 xstar ) ) |> fun h => ( hasGradientAt_iff_isLittleO_nhds_zero.2 ?_ );
  any_goals tauto;
  constructor <;> intro h <;> have := hf.1 xstar <;> simp_all +decide [ gradient ];
  exact IsLocalMin.fderiv_eq_zero ( Filter.Eventually.of_forall hmin )

/-
For a μ-strongly convex function with minimiser `x*`, the strong convexity
    lower bound at `x*` gives:
    `f(x) - f(x*) ≥ μ/2 * ‖x - x*‖²` for all `x`.
-/
theorem stronglyConvex_func_gap_lower {μ : ℝ} {f : E → ℝ}
    (hf : IsStronglyConvex μ f) {xstar : E} (_hmin : IsMinimiser f xstar)
    (_hμ : 0 < μ)
    (hgrad : gradient f xstar = 0) (x : E) :
    f x - f xstar ≥ μ / 2 * ‖x - xstar‖ ^ 2 := by
  have := hf.lower_bound xstar x;
  simp_all +decide [ inner_zero_left ] ; linarith

/-
For a μ-strongly convex L-smooth function, the gradient at `x` controls the
    distance to the minimiser:
    `⟪∇f(x), x - x*⟫ ≥ μ * ‖x - x*‖²`.
    This follows from strong convexity at `x*` with gradient zero.
-/
theorem stronglyConvex_inner_gradient_bound {μ : ℝ} {f : E → ℝ}
    (hf : IsStronglyConvex μ f) {xstar : E}
    (_hgrad : gradient f xstar = 0) (x : E) :
    @inner ℝ E _ (gradient f x) (x - xstar) ≥ μ / 2 * ‖x - xstar‖ ^ 2 +
      (f x - f xstar) := by
  have := hf.lower_bound xstar x; ( have := hf.lower_bound x xstar; ( simp_all +decide [ inner_sub_right, norm_sub_rev ] ; ) );
  linarith

end