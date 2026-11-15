# Equivariant isometric embeddings via Günther's method

A proof, by Günther's method, of the Moore–Schlafly equivariant isometric embedding theorem
(Math. Z. 173, 1980), together with a Lean 4 / Mathlib formalization of its algebraic and
functional-analytic core.

> **Theorem (Moore–Schlafly).** Let *(M, g)* be a compact Riemannian manifold and *G* a compact
> Lie group acting on *M* by isometries. There are an orthogonal representation
> *ρ : G → O(N)* and an isometric embedding *X : M → ℝᴺ* with *X(σp) = ρ(σ) X(p)*.

The paper also proves, by the same method, results that are not in the 1980 article:

- **Finite regularity.** A *G*-invariant metric of class *C^{k,α}* (*k ≥ 2*, *0 < α < 1*) is
  induced by an equivariant embedding of the same class *C^{k,α}*.
- **Equivariant analytic right inverse.** At a free equivariant embedding *u*, the induced
  metric map has a real-analytic local right inverse that commutes with every symmetry of *u*,
  so the perturbed embedding inherits every symmetry shared by *u* and the perturbation.
- **Families.** A compact family of invariant metrics is induced by a continuous family of
  equivariant embeddings for one fixed representation; in particular *N* is bounded on compact
  sets of invariant metrics.

These three results are proved in the paper only; they are not formalized in general.

One case is formalized completely, with no analytic hypotheses: the equivariant perturbation
theorem on the flat torus `ℝⁿ / 2π ℤⁿ` (paper, Section 11). It is treated separately because
Mathlib does not yet have the analysis on manifolds (Hölder spaces of sections, the
Laplace–Beltrami operator, Schauder estimates) that the general theorem needs. On the torus,
Günther's operators are explicit convolution operators on Fourier coefficients, and their bounds
are elementary.

## Contents

- `paper/equivariant-gunther.tex`, `paper/equivariant-gunther.pdf`: the paper (amsart,
  self-contained bibliography; it compiles with pdflatex, xelatex or tectonic).
- `Challenge.lean`: the advertised statements, to be audited (proofs are `sorry`).
- `Solution.lean`: the same statements, proved.
- `EquivEmbed/`: the proof development.
  - `FixedPoint.lean`: the equivariant Günther fixed point theorem.
  - `RightInverse.lean`: the pointwise Nash–Günther right inverse and its equivariance.
  - `Veronese.lean`: freeness of the Veronese map.
  - `Averaging.lean`: the Haar-averaged invariant inner product.
  - `Defs.lean`, `Assembly.lean`: the conditional main theorem.
  - `Torus/`: the unconditional theorem on the flat torus (`Conv.lean`: weighted `ℓ¹`
    kernel convolutions; `Kernels.lean`: Günther's kernels and their bounds; `Operators.lean`:
    the operators and Günther's identity on Fourier coefficients; `Fourier.lean`: absolutely
    convergent Fourier series, termwise differentiation, products; `Main.lean`: the theorem;
    `Example.lean`: the circle, showing that the hypotheses of the theorem are satisfiable).
- `comparator.json`, `formalization.yaml`: metadata for the
  [Palomar registry](https://palomar-registry.org/); submissions go through
  https://submit.palomar-registry.org/.
- `scripts/gen_challenge.py`: regenerates `Challenge.lean`, `Solution.lean` and
  `comparator.json` from one statement list.

## What is proved

Unconditional, using only the axioms `propext`, `Classical.choice` and `Quot.sound`:

| Lean | Statement |
|---|---|
| `EquivEmbed.gunther_fixed_point_equivariant` | Banach space with isometric linear `G`-action, bounded equivariant bilinear `B`, `G`-fixed `m` with `4‖B‖‖m‖ < 1`: `v = m + B(v,v)` has a unique solution with `‖v‖ ≤ 2‖m‖`, and it is `G`-fixed |
| `EquivEmbed.flat_torus_equivariant_perturbation` | on the flat torus: for a map `u` with a dual frame of its first and second derivatives (all with Fourier coefficients in the weighted Wiener algebra), every small symmetric `h` is realized, `⟨∂ᵢ(u+v), ∂ⱼ(u+v)⟩ = ⟨∂ᵢu, ∂ⱼu⟩ + hᵢⱼ` pointwise, with `‖v‖ ≤ C‖h‖`; `u + v` inherits every translation-and-rotation symmetry of the data, and is real if the data are real. No analytic hypothesis |
| `EquivEmbed.gunther_solution_map_equivariant` | for `m` not necessarily `G`-fixed, the small solution for `g • m` is `g • v`: the solution operator commutes with the action |
| `EquivEmbed.gunther_solution_map_lipschitz` | `(1 − 2‖B‖(‖m‖ + ‖m'‖)) ‖v − v'‖ ≤ ‖m − m'‖` for the small solutions `v`, `v'` |
| `EquivEmbed.nash_gunther_right_inverse` | for injective `A`, `A(A†A)⁻¹b` is the unique solution of `A†x = b` in `range A`, and has least norm |
| `EquivEmbed.nash_gunther_right_inverse_equivariant` | if `A' = R ∘ A ∘ P` with `R` orthogonal, the solutions correspond: `x' = R x` |
| `EquivEmbed.veronese_map_free` | `(X, X ⊙ X)` is free at points where `X` is an immersion |
| `EquivEmbed.haar_averaged_inner_product` | `∫ φ(σ⁻¹x) φ(σ⁻¹y) dμ` is a `G`-invariant inner product |

The torus theorem does not include the construction of the dual frame from freeness, the
embedding property of `u + v`, or the approximation step; see Remark 11.5 of the paper.

Conditional: `EquivEmbed.equivariant_isometric_embedding_conditional` derives the main theorem
from four named hypotheses on an abstract `EmbeddingProblem`: a free equivariant embedding
exists, realizable metrics are dense, the cone condition, and Günther's non-equivariant
analytic package. Mathlib does not yet have Hölder spaces on manifolds, the Laplace–Beltrami
operator or elliptic regularity, so these enter as hypotheses. No hypothesis asserts the
existence of an equivariant solution of the nonlinear problem; Lean produces it from the
fixed point theorem.

Equivariance is enforced by the types: maps are `EquivariantMap`s (a function `Pt → ℝᴺ`, an
orthogonal representation `ρ`, and a proof of `X (σ • p) = ρ σ (X p)`), and the conclusions restate
it. The cone condition assumes positivity of `g − c F(X)` for some `c > 0` (one `c` suffices). The
geometric meaning of the metric space `Met`, the positive cone `pos`, the induced metric `F`,
freeness, and being an embedding (beyond injectivity, which is required) is not encoded in Lean:
the theorem holds for every instantiation of `EmbeddingProblem`, and its reading as a statement
about Riemannian manifolds depends on an instantiation for an actual manifold, which the paper
describes but which is not formalized.

## Building

```
lake exe cache get
lake build
```

Toolchain `leanprover/lean4:v4.35.0`, Mathlib `v4.35.0`. To check axioms:

```
echo 'import Solution
#print axioms EquivEmbed.equivariant_isometric_embedding_conditional' > /tmp/ax.lean
lake env lean /tmp/ax.lean
```

`scripts/verify-comparator.sh` runs `lake comparator` the way Palomar does. It needs Linux with
`bubblewrap`, and the GitHub Actions workflow runs it on every push.

## License

Apache-2.0 (see `LICENSE`).
