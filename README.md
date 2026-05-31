# gradient-descent-lean

Lean 4 formal proofs of gradient descent convergence for smooth convex optimisation.

**18 theorems. Zero sorry statements.** Works over arbitrary real Hilbert spaces.

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

- `lsmooth_upper_bound` proved from first principles via the fundamental theorem of calculus and interval integration — not assumed as an axiom
- All proofs use only standard axioms: `propext`, `Classical.choice`, `Quot.sound`
- Uses Mathlib's `HasGradientAt`, `LipschitzWith`, and `InnerProductSpace` infrastructure
- Works over **arbitrary real Hilbert spaces**, not just ℝⁿ

## Dependencies

- Lean 4.28.0
- Mathlib v4.28.0

## Related work

- [kuramoto-lean](https://github.com/velvetmonkey/kuramoto-lean) — Lean 4 formalisation of Kuramoto synchronisation
- [flywheel-universe](https://zenodo.org/doi/10.5281/zenodo.20469680) — companion paper (Zenodo v2)

## Author

Ben Cassie · [@thevelvetmonke](https://x.com/thevelvetmonke)
