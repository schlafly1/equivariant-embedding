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
        "gunther_solution_map_equivariant",
        r"""/-- **The Günther solution map is equivariant.**  Let `G` act on `E` by isometric linear
maps and let `B` be `G`-equivariant; `m` need not be `G`-fixed.  If `v` is the solution of
`v = m + B(v, v)` with `‖v‖ ≤ 2 ‖m‖`, then `g • v` is the solution for the data `g • m`: it
solves `w = g • m + B(w, w)`, has `‖g • v‖ ≤ 2 ‖g • m‖`, and is the only such solution.  So the
solution operator commutes with every symmetry of the equation. -/
theorem EquivEmbed.gunther_solution_map_equivariant
    {E G : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [Monoid G] [DistribMulAction G E] [IsIsometricSMul G E]
    (B : E →L[ℝ] E →L[ℝ] E)
    (hBG : ∀ (g : G) (v w : E), B (g • v) (g • w) = g • B v w)
    (m v : E) (hm : 4 * ‖B‖ * ‖m‖ < 1) (hv : ‖v‖ ≤ 2 * ‖m‖) (hvf : v = m + B v v) (g : G) :
    ‖g • v‖ ≤ 2 * ‖g • m‖ ∧ g • v = g • m + B (g • v) (g • v) ∧
      ∀ w : E, ‖w‖ ≤ 2 * ‖g • m‖ → w = g • m + B w w → w = g • v""",
        r"""EquivEmbed.solution_bilinear_smul B hBG hm hv hvf g""",
    ),
    (
        "gunther_solution_map_lipschitz",
        r"""/-- **Lipschitz dependence of the Günther solution on the data.**  If `v`, `v'` are the
small solutions for `m`, `m'`, then `(1 - 2 ‖B‖ (‖m‖ + ‖m'‖)) ‖v - v'‖ ≤ ‖m - m'‖`.  When
`4 ‖B‖ ‖m‖ < 1` and `4 ‖B‖ ‖m'‖ < 1` the first factor is positive. -/
theorem EquivEmbed.gunther_solution_map_lipschitz
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (B : E →L[ℝ] E →L[ℝ] E) (m m' v v' : E)
    (hv : ‖v‖ ≤ 2 * ‖m‖) (hvf : v = m + B v v)
    (hv' : ‖v'‖ ≤ 2 * ‖m'‖) (hvf' : v' = m' + B v' v') :
    (1 - 2 * ‖B‖ * (‖m‖ + ‖m'‖)) * ‖v - v'‖ ≤ ‖m - m'‖""",
        r"""EquivEmbed.solution_bilinear_lipschitz B hv hvf hv' hvf'""",
    ),
    (
        "flat_torus_equivariant_perturbation",
        r"""open EquivEmbed.Torus in
/-- **Equivariant Günther perturbation theorem on the flat torus `ℝⁿ / 2π ℤⁿ`
(unconditional).**

Maps of the torus into a complex Banach space `F` with a symmetric bilinear form `dot` are given
by Fourier coefficients `a : Freq n → F` with `∑ (1 + |k|²) ‖a k‖ < ∞`; then `fsum a` is a map of
class `C²`.  (For `F = ℂᴺ`, `dot z w = ∑ zₐ wₐ` and `cF` the coordinatewise conjugation, the
real maps are the maps into `ℝᴺ` and `dot` is the Euclidean inner product.)

Let `u` be such a map and let `(ℓ1, ℓ2)` be a *dual frame* of its first and second derivatives
(hypotheses `hd1`–`hd4`); this says that `fsum u` is free.  Then there are `ε > 0` and `C` such
that for every symmetric `h` with `∑ (1 + |k|²) ‖h i j k‖ < ε` there is `v` with:

* `∑ (1 + |k|²) ‖v k‖ ≤ C δ` whenever all `∑ (1 + |k|²) ‖h i j k‖ ≤ δ`;
* `⟨∂ᵢ(u + v), ∂ⱼ(u + v)⟩ = ⟨∂ᵢu, ∂ⱼu⟩ + h i j` at every point: the map `u + v` induces the
  metric `F(u) + h`;
* **inheritance of symmetry**: if `t` is a translation of the torus and `R` an isometry of `F`
  preserving `dot` such that `u`, `ℓ1`, `ℓ2` are `(t, R)`-equivariant and `h` is `t`-invariant
  (stated on Fourier coefficients), then `(u + v)(x + t) = R ((u + v)(x))`;
* **reality**: if the data are real for a conjugation `cF`, so is `u + v`.

No elliptic estimate or other analytic input is assumed. -/
theorem EquivEmbed.flat_torus_equivariant_perturbation {n : ℕ} {F : Type*}
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    (dot : F →L[ℂ] F →L[ℂ] ℂ) (hsymm : ∀ x y, dot x y = dot y x)
    (u : Freq n → F) (hu : Summable fun k => W k * ‖u k‖)
    (ℓ1 : Fin n → Freq n → F) (hℓ1 : ∀ j, Summable fun k => W k * ‖ℓ1 j k‖)
    (ℓ2 : Fin n → Fin n → Freq n → F) (hℓ2 : ∀ i j, Summable fun k => W k * ‖ℓ2 i j k‖)
    (hd1 : ∀ x p q, dot (pd p (fsum u) x) (fsum (ℓ1 q) x) = if p = q then 1 else 0)
    (hd2 : ∀ x p q r, dot (pd p (fsum u) x) (fsum (ℓ2 q r) x) = 0)
    (hd3 : ∀ x p q r, dot (pd p (pd q (fsum u)) x) (fsum (ℓ1 r) x) = 0)
    (hd4 : ∀ x p q r s, dot (pd p (pd q (fsum u)) x) (fsum (ℓ2 r s) x)
      = (if p = r then (if q = s then (1 / 2 : ℂ) else 0) else 0)
        + (if p = s then (if q = r then (1 / 2 : ℂ) else 0) else 0)) :
    ∃ ε > 0, ∃ C : ℝ, ∀ h : Fin n → Fin n → Freq n → ℂ,
      (∀ i j, Summable fun k => W k * ‖h i j k‖) → (∀ i j, h i j = h j i) →
      (∀ i j, ∑' k, W k * ‖h i j k‖ < ε) →
      ∃ v : Freq n → F, (Summable fun k => W k * ‖v k‖) ∧
        (∀ δ : ℝ, (∀ i j, ∑' k, W k * ‖h i j k‖ ≤ δ) → ∑' k, W k * ‖v k‖ ≤ C * δ) ∧
        (∀ x i j, dot (pd i (fun y => fsum u y + fsum v y) x)
            (pd j (fun y => fsum u y + fsum v y) x)
          = dot (pd i (fsum u) x) (pd j (fsum u) x) + fsum (h i j) x) ∧
        (∀ (t : Fin n → ℝ) (R : F →ₗᵢ[ℂ] F), (∀ x y, dot (R x) (R y) = dot x y) →
          (∀ k, ef k (-t) • R (u k) = u k) →
          (∀ j k, ef k (-t) • R (ℓ1 j k) = ℓ1 j k) →
          (∀ i j k, ef k (-t) • R (ℓ2 i j k) = ℓ2 i j k) →
          (∀ i j k, ef k (-t) * h i j k = h i j k) →
          (∀ k, ef k (-t) • R (v k) = v k) ∧
            ∀ x, fsum u (x + t) + fsum v (x + t) = R (fsum u x + fsum v x)) ∧
        (∀ cF : F →ₗᵢ[ℝ] F, (∀ (z : ℂ) (y : F), cF (z • y) = starRingEnd ℂ z • cF y) →
          (∀ x y, dot (cF x) (cF y) = starRingEnd ℂ (dot x y)) →
          (∀ k, cF (u (-k)) = u k) →
          (∀ j k, cF (ℓ1 j (-k)) = ℓ1 j k) → (∀ i j k, cF (ℓ2 i j (-k)) = ℓ2 i j k) →
          (∀ i j k, starRingEnd ℂ (h i j (-k)) = h i j k) →
          (∀ k, cF (v (-k)) = v k) ∧ ∀ x, cF (fsum u x + fsum v x) = fsum u x + fsum v x)""",
        r"""EquivEmbed.Torus.torus_perturbation dot hsymm u hu ℓ1 hℓ1 ℓ2 hℓ2 hd1 hd2 hd3 hd4""",
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
an embedding `X` with `F(X) = F(u) + h`, and `X` is `G`-equivariant. -/
theorem EquivEmbed.equivariant_gunther_perturbation {G : Type} [Group G]
    {P : EquivEmbed.EmbeddingProblem G} {u : P.Map} (D : EquivEmbed.GuntherPackage P u) :
    ∃ ε > 0, ∀ h : P.Met, ‖h‖ < ε → ∃ X : P.Map, P.IsEmbedding X ∧ P.F X = P.F u + h ∧
      ∀ (σ : G) (p : P.Pt), X.toFun (σ • p) = X.ρ σ (X.toFun p)""",
        r"""EquivEmbed.equivariant_perturbation D""",
    ),
    (
        "equivariant_isometric_embedding_conditional",
        r"""/-- **Moore–Schlafly equivariant isometric embedding theorem, via Günther's method
(conditional form).**  Given (1) a free equivariant embedding, (2) density of realizable
invariant metrics, (3) the cone condition (for some `c > 0`), and (4) Günther's non-equivariant analytic package at
free embeddings, every positive definite `G`-invariant metric is induced by a `G`-equivariant
embedding. -/
theorem EquivEmbed.equivariant_isometric_embedding_conditional {G : Type} [Group G]
    (P : EquivEmbed.EmbeddingProblem G) (h1 : EquivEmbed.HasFreeEmbedding P)
    (h2 : EquivEmbed.RealizableDense P) (h3 : EquivEmbed.ConeCondition P)
    (h4 : EquivEmbed.HasGuntherPackages P) :
    ∀ g ∈ P.pos, ∃ X : P.Map, P.IsEmbedding X ∧ P.F X = g ∧
      ∀ (σ : G) (p : P.Pt), X.toFun (σ • p) = X.ρ σ (X.toFun p)""",
        r"""EquivEmbed.equivariant_isometric_embedding P h1 h2 h3 h4""",
    ),
]

DEF_NAMES = [
    "EquivEmbed.EquivariantMap.smul",
    "EquivEmbed.EmbeddingProblem.Map",
    "EquivEmbed.HasFreeEmbedding",
    "EquivEmbed.RealizableDense",
    "EquivEmbed.ConeCondition",
    "EquivEmbed.HasGuntherPackages",
    "EquivEmbed.Torus.Freq",
    "EquivEmbed.Torus.sq",
    "EquivEmbed.Torus.W",
    "EquivEmbed.Torus.ef",
    "EquivEmbed.Torus.fsum",
    "EquivEmbed.Torus.pd",
]

IMPORTS = """public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Topology.MetricSpace.IsometricSMul
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Topology.Algebra.InfiniteSum.Module"""

CHALLENGE_DOC = """/-!
# Equivariant isometric embeddings via Günther's method: advertised statements

This is the statement surface to audit.  It has two parts.

**The flat torus (unconditional).**  `EquivEmbed.flat_torus_equivariant_perturbation` is the
equivariant Günther perturbation theorem for the flat torus `ℝⁿ / 2π ℤⁿ`, with no analytic
hypothesis: a free map `u` given by an absolutely convergent Fourier series, every small
perturbation `h` of its induced metric, a map `u + v` inducing the metric `F(u) + h`, and
inheritance by `u + v` of the symmetries of the data.  It uses the definitions of the section
`Torus` below (`Freq`, `W`, `ef`, `fsum`, `pd`).  This special case is formalized separately
because Mathlib does not yet have the analysis on manifolds needed for the general theorem.

**Unconditional abstract theorems.**  These are the new equivariant ingredients of the proof,
stated with ordinary Mathlib notions only:

* `EquivEmbed.gunther_fixed_point_equivariant`: Günther's contraction argument yields a
  `G`-fixed solution, with no averaging of nonlinear solutions;
* `EquivEmbed.gunther_solution_map_equivariant` and
  `EquivEmbed.gunther_solution_map_lipschitz`: the solution operator commutes with the group
  action and depends Lipschitz continuously on the data;
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

Equivariance is enforced by the types: maps are `EquivariantMap`s (a function `Pt → ℝᴺ`, an
orthogonal representation `ρ`, and a proof of `X (σ • p) = ρ σ (X p)`), and the conclusions
restate it.  The geometric meaning of `Met`, `pos`, `F`, `IsFree` and `IsEmbedding` (beyond
injectivity, which is a field) is not encoded: the theorems apply to any instantiation of
`EmbeddingProblem`, and their geometric reading requires an instantiation for an actual compact
Riemannian `G`-manifold.
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
