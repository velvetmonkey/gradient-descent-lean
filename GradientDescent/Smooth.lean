/-
Copyright (c) 2025 gradient-descent-lean contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: gradient-descent-lean contributors
-/
import Mathlib
import GradientDescent.Defs

/-!
# L-Smooth functions — Descent Lemma

The key result in this file is the **descent lemma**: for an L-smooth function `f`,
one gradient step with step size `α ≤ 1/L` gives

  `f(x − α • ∇f(x)) ≤ f(x) − α/2 * ‖∇f(x)‖²`

## Proof strategy

The classical proof goes through two ingredients:
1. **Quadratic upper bound** (from L-smoothness):
   `f(y) ≤ f(x) + ⟪∇f(x), y − x⟫ + L/2 ‖y − x‖²` for all `x y`.
2. Substituting `y = x − α • ∇f(x)` and simplifying yields the descent lemma.

We formalise the quadratic upper bound as a separate lemma (`lsmooth_upper_bound`),
then derive the descent lemma from it.
-/

open InnerProductSpace

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-! ### Quadratic upper bound -/

/-- **Quadratic upper bound** for L-smooth functions:
    `f(y) ≤ f(x) + ⟪∇f(x), y − x⟫ + L/2 * ‖y − x‖²`.

    This is proved by integrating `⟪∇f(x + t(y−x)) − ∇f(x), y − x⟫` over `t ∈ [0,1]`
    and bounding with Cauchy–Schwarz + L-Lipschitz on the gradient. -/
theorem lsmooth_upper_bound {L : NNReal} {f : E → ℝ} (hf : IsLSmooth L f)
    (x y : E) :
    f y ≤ f x + @inner ℝ E _ (gradient f x) (y - x) + (L : ℝ) / 2 * ‖y - x‖ ^ 2 := by
  cases' hf with h₁ h₂;
  revert x y;
  have h_integral : ∀ x y, ∫ t in (0 : ℝ)..1, ⟪gradient f (x + t • (y - x)) - gradient f x, y - x⟫_ℝ ≤ ∫ t in (0 : ℝ)..1, (L : ℝ) * t * ‖y - x‖ ^ 2 := by
    intro x y;
    refine' intervalIntegral.integral_mono_on _ _ _ _;
    · norm_num;
    · apply_rules [ Continuous.intervalIntegrable ];
      exact Continuous.inner ( Continuous.sub ( h₂.continuous.comp ( continuous_const.add ( continuous_id'.smul continuous_const ) ) ) continuous_const ) continuous_const;
    · exact Continuous.intervalIntegrable ( by continuity ) _ _;
    · intro t ht
      have h_lip : ‖gradient f (x + t • (y - x)) - gradient f x‖ ≤ L * t * ‖y - x‖ := by
        convert h₂.norm_sub_le ( x + t • ( y - x ) ) x using 1 ; simp +decide [ norm_smul, abs_of_nonneg ht.1 ] ; ring;
      exact le_trans ( abs_le.mp ( abs_real_inner_le_norm _ _ ) |>.2 ) ( by nlinarith [ norm_nonneg ( y - x ) ] );
  -- By fundamental theorem of calculus, we know that
  have h_ftc : ∀ x y, ∫ t in (0 : ℝ)..1, ⟪gradient f (x + t • (y - x)), y - x⟫_ℝ = f y - f x := by
    intro x y;
    rw [ intervalIntegral.integral_eq_sub_of_hasDerivAt ];
    rotate_right;
    use fun t => f ( x + t • ( y - x ) );
    · simp +decide;
    · intro t ht;
      have := h₁ ( x + t • ( y - x ) );
      convert this.hasFDerivAt.comp_hasDerivAt t ( HasDerivAt.add ( hasDerivAt_const _ _ ) ( HasDerivAt.smul ( hasDerivAt_id t ) ( hasDerivAt_const _ _ ) ) ) using 1 ; simp +decide [ inner_smul_right ];
    · apply_rules [ Continuous.intervalIntegrable ];
      exact Continuous.inner ( h₂.continuous.comp ( Continuous.add continuous_const ( continuous_id.smul continuous_const ) ) ) continuous_const;
  intro x y; specialize h_integral x y; specialize h_ftc x y; simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
  simp_all +decide [ inner_sub_left ];
  rw [ intervalIntegral.integral_sub ] at h_integral <;> norm_num at *;
  · linarith;
  · apply_rules [ Continuous.intervalIntegrable ];
    exact Continuous.inner ( h₂.continuous.comp ( continuous_const.add ( continuous_id.smul continuous_const ) ) ) continuous_const

/-! ### Descent Lemma -/

/-
**Descent lemma**: For an L-smooth function, a gradient step with
    `0 < α` and `α ≤ 1/L` satisfies
    `f(x − α • ∇f(x)) ≤ f(x) − α/2 * ‖∇f(x)‖²`.

    The proof substitutes `y := x − α • ∇f(x)` into the quadratic upper bound and
    simplifies using `⟪∇f(x), −α • ∇f(x)⟫ = −α ‖∇f(x)‖²` and
    `‖α • ∇f(x)‖² = α² ‖∇f(x)‖²`, then uses `α ≤ 1/L` to close the bound.
-/
theorem descent_lemma {L : NNReal} {f : E → ℝ} (hf : IsLSmooth L f)
    (x : E) (α : ℝ) (hα_pos : 0 < α) (hα_le : α ≤ 1 / (L : ℝ))
    (hL_pos : (0 : ℝ) < L) :
    f (x - α • gradient f x) ≤ f x - α / 2 * ‖gradient f x‖ ^ 2 := by
  refine le_trans ( lsmooth_upper_bound hf x ( x - α • gradient f x ) ) ?_;
  norm_num [ norm_smul ];
  rw [ abs_of_pos hα_pos, inner_smul_right ] ; ring_nf;
  rw [ real_inner_self_eq_norm_sq ] ; rw [ le_div_iff₀ ] at hα_le <;> nlinarith [ mul_le_mul_of_nonneg_left hα_le hα_pos.le ] ;

end