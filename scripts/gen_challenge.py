#!/usr/bin/env python3
"""Generate Challenge.lean, Solution.lean and comparator.json from one list of statements.

The statements are written once below, so Challenge and Solution cannot drift apart.
Challenge.lean also receives a verbatim copy of the definitions in EquivEmbed/Defs.lean.
Run from anywhere:  python3 scripts/gen_challenge.py
"""
import json
from pathlib import Path

root = Path(__file__).resolve().parent.parent
defs_src = (root / "EquivEmbed" / "Defs.lean").read_text(encoding="utf-8")
a = defs_src.index("namespace EquivEmbed\n") + len("namespace EquivEmbed\n")
b = defs_src.rindex("end EquivEmbed")
defs_body = defs_src[a:b].strip("\n")

STATEMENTS = [
    (
        "gunther_fixed_point_equivariant",
        r"""/-- **Equivariant Günther fixed point theorem.**  Let `E` be a real Banach space on which a
monoid `G` acts by isometric linear maps, let `B` be a bounded `G`-equivariant bilinear map and
`m` a `G`-fixed vector with `4 ‖B‖ ‖m‖ < 1`.  Then Günther's equation `v = m + B(v, v)` has a
solution `v` with `‖v‖ ≤ 2 ‖m‖`, it is the only solution in that ball, and it is `G`-fixed. -/
theorem EquivEmbed.gunther_fixed_point_equivariant
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [Monoid G] [DistribMulAction G E] [IsIsometricSMul G E]
    (B : E →L[ℝ] E →L[ℝ] E) (m : E) (hm : 4 * ‖B‖ * ‖m‖ < 1)
    (hmG : ∀ g : G, g • m = m)
    (hBG : ∀ (g : G) (v w : E), B (g • v) (g • w) = g • B v w) :
    ∃ v : E, ‖v‖ ≤ 2 * ‖m‖ ∧ v = m + B v v ∧ (∀ g : G, g • v = v) ∧
      ∀ w : E, ‖w‖ ≤ 2 * ‖m‖ → w = m + B w w → w = v""",
        r"""by
  obtain ⟨v, hvn, hvf, hvG⟩ := EquivEmbed.exists_fixedPoint_bilinear_invariant B hm hmG hBG
  obtain ⟨v', -, huniq⟩ := EquivEmbed.exists_unique_fixedPoint_bilinear B hm
  have hv : v = v' := huniq v ⟨hvn, hvf⟩
  exact ⟨v, hvn, hvf, hvG, fun w hwn hwf => (huniq w ⟨hwn, hwf⟩).trans hv.symm⟩""",
    ),
    (
        "nash_gunther_right_inverse",
        r"""/-- **The pointwise Nash–Günther right inverse.**  If `A : W → V` is injective (the map is
*free* at a point: first and second derivatives are linearly independent), then for every `b`
the system `A† x = b` has a unique solution in the range of `A`, and it is the solution of least
norm.  (It is `x = A (A† A)⁻¹ b`.) -/
theorem EquivEmbed.nash_gunther_right_inverse
    {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (A : W →ₗ[ℝ] V) (hA : Function.Injective A) (b : W) :
    ∃ x : V, x ∈ LinearMap.range A ∧ LinearMap.adjoint A x = b ∧
      (∀ y : V, LinearMap.adjoint A y = b → ‖x‖ ≤ ‖y‖) ∧
      ∀ x' : V, x' ∈ LinearMap.range A → LinearMap.adjoint A x' = b → x' = x""",
        r"""⟨EquivEmbed.rightInv A hA b, EquivEmbed.rightInv_mem_range A hA b,
    EquivEmbed.adjoint_rightInv A hA b, fun _ hy => EquivEmbed.norm_rightInv_le hA hy,
    fun _ hx' hx'b => EquivEmbed.eq_rightInv_of_mem_range hA hx' hx'b⟩""",
    ),
    (
        "nash_gunther_right_inverse_equivariant",
        r"""/-- **Equivariance of the Nash–Günther correction.**  Suppose the frame at `σ p` is
`A' = R ∘ A ∘ P`, where `A` is the frame at `p`, `R = ρ(σ)` is orthogonal, and `P` is the
change of coordinates induced by `σ`, and suppose the right-hand sides correspond by
`b' = P† b`.  Then the pointwise solutions correspond: `x' = R x`. -/
theorem EquivEmbed.nash_gunther_right_inverse_equivariant
    {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    {A A' : W →ₗ[ℝ] V} (hA : Function.Injective A) (R : V ≃ₗᵢ[ℝ] V) (P : W ≃ₗ[ℝ] W)
    (hframe : A' = R.toLinearEquiv.toLinearMap ∘ₗ A ∘ₗ P.toLinearMap) (b : W) {x x' : V}
    (hx : x ∈ LinearMap.range A) (hxb : LinearMap.adjoint A x = b)
    (hx' : x' ∈ LinearMap.range A')
    (hx'b : LinearMap.adjoint A' x' = LinearMap.adjoint P.toLinearMap b) :
    x' = R x""",
        r"""by
  have hA' : Function.Injective A' := by
    rw [hframe]
    exact R.injective.comp (hA.comp P.injective)
  rw [EquivEmbed.eq_rightInv_of_mem_range hA hx hxb,
    EquivEmbed.eq_rightInv_of_mem_range hA' hx' hx'b]
  exact EquivEmbed.rightInv_equivariant hA hA' R P hframe rfl""",
    ),
    (
        "veronese_map_free",
        r"""/-- **Freeness of the Veronese map `X ↦ (X, X ⊙ X)` (pointwise).**  At a point write
`x = X(p)`, `x₁ i = ∂ᵢX(p)` (linearly independent: `X` is an immersion) and
`x₂ i j = ∂ᵢ∂ⱼX(p)`.  If `∑ cᵢ ∂ᵢX̃ + ∑ dᵢⱼ ∂ᵢ∂ⱼX̃ = 0` with `d` symmetric, where the
`V`-component is `∑ cᵢ x₁ i + ∑ dᵢⱼ x₂ i j` and the `Sym² V`-component is tested against all
`φ ⊗ ψ`, then `c = 0` and `d = 0`. -/
theorem EquivEmbed.veronese_map_free
    {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ}
    (x : V) (x₁ : Fin n → V) (hli : LinearIndependent ℝ x₁) (x₂ : Fin n → Fin n → V)
    (c : Fin n → ℝ) (d : Fin n → Fin n → ℝ) (hd : ∀ i j, d i j = d j i)
    (hvec : ∑ i, c i • x₁ i + ∑ i, ∑ j, d i j • x₂ i j = 0)
    (hsym : ∀ φ ψ : Module.Dual ℝ V,
      ∑ i, c i * (φ (x₁ i) * ψ x + φ x * ψ (x₁ i)) +
        ∑ i, ∑ j, d i j * (φ (x₂ i j) * ψ x + φ x * ψ (x₂ i j) +
          φ (x₁ i) * ψ (x₁ j) + φ (x₁ j) * ψ (x₁ i)) = 0) :
    c = 0 ∧ d = 0""",
        r"""EquivEmbed.veronese_free x x₁ hli x₂ c d hd hvec hsym""",
    ),
    (
        "haar_averaged_inner_product",
        r"""/-- **The averaged inner product of Step 2.**  Let a compact group `G` act linearly and
continuously on a finite-dimensional real space `W`, let `μ` be a finite left-invariant measure
on `G` that is positive on open sets (e.g. Haar measure), and let `φ` be a functional whose
translates separate points.  Then `q x y = ∫ φ(σ⁻¹ x) φ(σ⁻¹ y) dμ(σ)` is a symmetric bilinear
`G`-invariant positive definite form, i.e. a `G`-invariant inner product on `W`. -/
theorem EquivEmbed.haar_averaged_inner_product
    {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
    [MeasurableSpace G] [BorelSpace G]
    (μ : MeasureTheory.Measure G) [μ.IsMulLeftInvariant] [MeasureTheory.IsFiniteMeasure μ]
    [μ.IsOpenPosMeasure]
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]
    (ρ : Representation ℝ G W) (hcont : ∀ x : W, Continuous fun σ : G => ρ σ x)
    (φ : Module.Dual ℝ W) (hsep : ∀ x : W, (∀ σ : G, φ (ρ σ x) = 0) → x = 0) :
    let q : W → W → ℝ := fun x y => ∫ σ, φ (ρ σ⁻¹ x) * φ (ρ σ⁻¹ y) ∂μ
    (∀ x y, q x y = q y x) ∧ (∀ x x' y, q (x + x') y = q x y + q x' y) ∧
      (∀ (a : ℝ) x y, q (a • x) y = a * q x y) ∧
      (∀ (τ : G) x y, q (ρ τ x) (ρ τ y) = q x y) ∧ (∀ x, x ≠ 0 → 0 < q x x)""",
        r"""⟨EquivEmbed.avgForm_symm μ ρ φ, EquivEmbed.avgForm_add_left μ ρ φ hcont,
    EquivEmbed.avgForm_smul_left μ ρ φ, EquivEmbed.avgForm_invariant μ ρ φ,
    fun _ hx => EquivEmbed.avgForm_self_pos μ ρ φ hcont hsep hx⟩""",
    ),
    (
        "equivariant_gunther_perturbation",
        r"""/-- **Equivariant Günther perturbation theorem.**  At an embedding `u` admitting Günther's
analytic package, every sufficiently small `G`-invariant metric perturbation `h` is realized by
an equivariant embedding: `F(X) = F(u) + h`. -/
theorem EquivEmbed.equivariant_gunther_perturbation {G : Type} [Group G]
    {P : EquivEmbed.EmbeddingProblem G} {u : P.Map} (D : EquivEmbed.GuntherPackage P u) :
    ∃ ε > 0, ∀ h : P.Met, ‖h‖ < ε → ∃ X : P.Map, P.IsEmbedding X ∧ P.F X = P.F u + h""",
        r"""EquivEmbed.equivariant_perturbation D""",
    ),
    (
        "equivariant_isometric_embedding_conditional",
        r"""/-- **Moore–Schlafly equivariant isometric embedding theorem, via Günther's method
(conditional form).**  Given (1) a free equivariant embedding, (2) density of realizable
invariant metrics, (3) the cone condition, and (4) Günther's non-equivariant analytic package at
free embeddings, every positive definite `G`-invariant metric is induced by a `G`-equivariant
embedding. -/
theorem EquivEmbed.equivariant_isometric_embedding_conditional {G : Type} [Group G]
    (P : EquivEmbed.EmbeddingProblem G) (h1 : EquivEmbed.HasFreeEmbedding P)
    (h2 : EquivEmbed.RealizableDense P) (h3 : EquivEmbed.ConeCondition P)
    (h4 : EquivEmbed.HasGuntherPackages P) :
    ∀ g ∈ P.pos, ∃ X : P.Map, P.IsEmbedding X ∧ P.F X = g""",
        r"""EquivEmbed.equivariant_isometric_embedding P h1 h2 h3 h4""",
    ),
]

DEF_NAMES = [
    "EquivEmbed.HasFreeEmbedding",
    "EquivEmbed.RealizableDense",
    "EquivEmbed.ConeCondition",
    "EquivEmbed.HasGuntherPackages",
]

IMPORTS = """public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Topology.MetricSpace.IsometricSMul
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.RepresentationTheory.Basic"""

CHALLENGE_DOC = """/-!
# Equivariant isometric embeddings via Günther's method: advertised statements

This is the statement surface to audit.  It has two parts.

**Unconditional theorems.**  These are the new equivariant ingredients of the proof, stated with
ordinary Mathlib notions only:

* `EquivEmbed.gunther_fixed_point_equivariant`: Günther's contraction argument yields a
  `G`-fixed solution, with no averaging of nonlinear solutions;
* `EquivEmbed.nash_gunther_right_inverse` and
  `EquivEmbed.nash_gunther_right_inverse_equivariant`: the pointwise right inverse used by Nash
  and Günther is well defined, coordinate independent and equivariant;
* `EquivEmbed.veronese_map_free`: the Veronese trick gives a free starting embedding;
* `EquivEmbed.haar_averaged_inner_product`: the averaged inner product of Step 2.

**Conditional theorem.**  `EquivEmbed.equivariant_isometric_embedding_conditional` derives the
main theorem from four named hypotheses on an abstract `EmbeddingProblem`.  Mathlib does not
yet have Hölder spaces on manifolds, the Laplace–Beltrami operator or elliptic regularity, so
those analytic inputs are hypotheses here: Mostow–Palais, Step 2 density, compactness, and
Günther's non-equivariant analytic package.  No hypothesis asserts that an equivariant solution
of the nonlinear problem exists.
-/"""


def main() -> None:
    challenge = (
        "module\n\n" + IMPORTS + "\n\n" + CHALLENGE_DOC + "\n\n@[expose] public section\n\n"
        "namespace EquivEmbed\n\n" + defs_body + "\n\nend EquivEmbed\n\n"
    )
    solution = (
        "module\n\npublic import EquivEmbed\n\n"
        "/-!\n# Proofs of the advertised statements\n\n"
        "Each declaration below has exactly the statement of its counterpart in "
        "`Challenge.lean`.\nThe definitions named in `comparator.json` come from "
        "`EquivEmbed.Defs`.\n-/\n\n@[expose] public section\n\n"
    )
    for _name, stmt, proof in STATEMENTS:
        challenge += stmt + " := by\n  sorry\n\n"
        if proof.startswith("by"):
            solution += stmt + " := " + proof + "\n\n"
        else:
            solution += stmt + " :=\n  " + proof + "\n\n"
    (root / "Challenge.lean").write_text(challenge.rstrip() + "\n", encoding="utf-8")
    (root / "Solution.lean").write_text(solution.rstrip() + "\n", encoding="utf-8")
    config = {
        "challenge_module": "Challenge",
        "solution_module": "Solution",
        "theorem_names": ["EquivEmbed." + n for n, _, _ in STATEMENTS],
        "definition_names": DEF_NAMES,
        "permitted_axioms": ["propext", "Quot.sound", "Classical.choice"],
        "enable_nanoda": True,
    }
    (root / "comparator.json").write_text(json.dumps(config, indent=2) + "\n", encoding="utf-8")
    print("wrote Challenge.lean, Solution.lean, comparator.json")


if __name__ == "__main__":
    main()
