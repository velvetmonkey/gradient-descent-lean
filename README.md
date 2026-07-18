# gradient-descent-lean

[![thread](https://img.shields.io/badge/%F0%9F%A7%B5-how%20it%20works-1DA1F2)](https://x.com/thevelvetmonke)
[![DOI](https://img.shields.io/badge/DOI-10.5281%2Fzenodo.20472996-blue)](https://doi.org/10.5281/zenodo.20472996)

Lean 4 formal proofs of gradient descent convergence for smooth convex optimisation.

**17 theorems. Zero sorry statements.** Works over arbitrary real Hilbert spaces.

## What this is, and why it matters

This library formalizes classical gradient-descent convergence over arbitrary real Hilbert spaces. Its headline theorem, `gd_strongly_convex_convergence`, proves the geometric squared-distance bound `(1-alpha*mu)^k * ||x0-xstar||^2` for a positive step size at most `1/L`.

The proof spine is machine checked from calculus through iteration. The library derives the quadratic upper bound for smooth functions using the fundamental theorem of calculus, obtains descent for a gradient step, combines descent with strong convexity to prove one-step contraction, and then iterates it. It also proves the standard O(1/k) function-value rate in the convex case.

The results assume exact gradients, global smoothness and convexity conditions, and a supplied global minimizer. The strongly convex theorem also takes the minimizer's zero-gradient fact as a hypothesis. It does not model numerical error, automatic differentiation, stochastic gradients, or a concrete training implementation.

## Background and motivation

Gradient descent is the engine of modern machine learning. Its convergence guarantees -- smoothness implies quadratic upper bounds, convexity turns local information into global bounds, strong convexity gives geometric contraction -- are treated as elementary in textbooks, but the details (differentiability hypotheses, step-size conditions, telescoping estimates) are non-trivial to state precisely.

This library machine-checks those details in Lean 4. It provides a compact, importable proof spine for the O(1/k) convex rate and geometric strongly convex rate, over **arbitrary real Hilbert spaces**, not just finite-dimensional ℝⁿ. Future formal work on optimisation, machine learning, or AI safety can import these results rather than re-formalising them.

At the time of writing, Mathlib contains no standalone Lean 4 library packaging the classical gradient descent convergence proof in this form. This fills that gap.

## Project structure

```
GradientDescent/
├── Defs.lean          — Core definitions (100 lines)
├── Smooth.lean        — Quadratic upper bound & descent lemma (95 lines)
├── Convex.lean        — Convexity properties (67 lines)
└── Convergence.lean   — O(1/k) and geometric convergence (198 lines)
```

## Theorem inventory

### Layer 1 — Foundations

| # | Theorem | Statement |
|---|---------|-----------|
| 1 | `isLSmooth_def` | L-smoothness ↔ differentiable + gradient L-Lipschitz |
| 2 | `lsmooth_upper_bound` | Quadratic upper bound: f(y) ≤ f(x) + ⟪∇f(x), y−x⟫ + L/2‖y−x‖² |
| 3 | `descent_lemma` | f(x − α∇f(x)) ≤ f(x) − α/2‖∇f(x)‖² for α ≤ 1/L |
| 4 | `stronglyConvex_def` | μ-strong convexity characterisation |
| 5 | `isConvex_lower_bound` | First-order convexity condition |
| 6 | `isConvex_minimiser_gradient_zero` | Gradient vanishes at minimiser |
| 7 | `stronglyConvex_func_gap_lower` | f(x) − f(x*) ≥ μ/2‖x−x*‖² |
| 8 | `stronglyConvex_inner_gradient_bound` | Inner product lower bound |

### Layer 2 — Convergence

| # | Theorem | Statement |
|---|---------|-----------|
| 9  | `gdSeq` | Gradient descent sequence definition |
| 10 | `norm_sq_gd_expand` | Norm-squared expansion identity |
| 11 | `gd_step_distance_sq` | Distance identity after one step |
| 12 | `gd_convex_step_bound` | Per-step distance decrease (convex case) |
| 13 | `gd_descent_nonincreasing` | Function values are non-increasing |
| 14 | `gd_convex_telescope` | Telescoping sum bound |
| 15 | `gd_convex_convergence` | **f(xₖ) − f(x*) ≤ L‖x₀−x*‖² / (2k)** — O(1/k) rate |
| 16 | `gd_strongly_convex_step` | Per-step contraction |
| 17 | `gd_strongly_convex_convergence` | **‖xₖ−x*‖² ≤ (1−αμ)ᵏ‖x₀−x*‖²** — geometric rate |

## Key technical highlights

- `lsmooth_upper_bound` proved from first principles via the fundamental theorem of calculus -- not assumed as an axiom
- Hilbert space generality: proofs hold over any `[NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]`, not just ℝⁿ
- Standard axioms only: `propext`, `Classical.choice`, `Quot.sound` -- no project-specific axioms
- Zero `sorry`, zero `admit`

## Usage

Add to your `lakefile.toml`:

```toml
[[require]]
name = "GradientDescent"
scope = "velvetmonkey"
rev = "main"
```

Then import what you need:

```lean
import GradientDescent.Convergence  -- O(1/k) and geometric rates
import GradientDescent.Smooth       -- descent lemma, quadratic upper bound
import GradientDescent.Convex       -- convexity inequalities
import GradientDescent.Defs         -- core definitions
```

## Dependencies

- Lean 4.28.0
- Mathlib v4.28.0

## Paper

A companion paper is available in this repository: [`paper.md`](paper.md) / [`paper.pdf`](paper.pdf)

Zenodo preprint: [10.5281/zenodo.20472996](https://doi.org/10.5281/zenodo.20472996)

## Cite

```bibtex
@software{cassie2026gradientdescentlean,
  author    = {Cassie, Ben},
  title     = {gradient-descent-lean: Formal Proofs of Gradient Descent Convergence in Lean 4},
  year      = {2026},
  publisher = {Zenodo},
  doi       = {10.5281/zenodo.20472996},
  url       = {https://doi.org/10.5281/zenodo.20472996}
}
```

## Related work

- [kuramoto-lean](https://github.com/velvetmonkey/kuramoto-lean) -- Lean 4 formalisation of Kuramoto synchronisation
- [hopfield-lean](https://github.com/velvetmonkey/hopfield-lean) -- Lean 4 Hopfield network energy descent and attractor convergence
- [flywheel-universe](https://zenodo.org/doi/10.5281/zenodo.20469680) -- companion Zenodo paper (v2)

## Acknowledgements

Proofs in this library were generated using [Aristotle](https://aristotle.harmonic.fun), an AI proof assistant for Lean 4 and Mathlib. The proof discipline -- zero sorry, every Mathlib lemma name `#check`ed before use -- was specified by the author and enforced by the Lean type checker.

## Author

Ben Cassie · [@thevelvetmonke](https://x.com/thevelvetmonke)
## Part of the Lean proof corpus

One of a family of small, machine-checked Lean 4 developments. Index: [velvetmonkey/lean](https://github.com/velvetmonkey/lean) ([live index](https://velvetmonkey.github.io/lean)).
