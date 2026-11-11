module

public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Topology.MetricSpace.IsometricSMul
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.RepresentationTheory.Basic

/-!
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
-/

@[expose] public section

namespace EquivEmbed

/-- Abstract data of the equivariant isometric embedding problem for a compact Riemannian
manifold with an isometric action of `G`. -/
structure EmbeddingProblem (G : Type) [Group G] where
  /-- Smooth `G`-invariant symmetric 2-tensors on `M`, normed by a `C^{2,α}` norm. -/
  Met : Type
  [instNormedAddCommGroup : NormedAddCommGroup Met]
  [instNormedSpace : NormedSpace ℝ Met]
  /-- The positive definite elements of `Met`. -/
  pos : Set Met
  /-- Smooth maps `M → ℝᴺ`, equivariant for some orthogonal representation of `G`. -/
  Map : Type
  /-- The induced metric `F(X) = ∑ₐ dXᵃ ⊗ dXᵃ`. -/
  F : Map → Met
  /-- `X` is an embedding. -/
  IsEmbedding : Map → Prop
  /-- `X` is free: first and second derivatives are linearly independent everywhere. -/
  IsFree : Map → Prop
  /-- The direct sum `(X, Y) : M → ℝ^{N₁} ⊕ ℝ^{N₂}`. -/
  sum : Map → Map → Map
  F_sum : ∀ X Y, F (sum X Y) = F X + F Y
  isEmbedding_sum : ∀ X Y, IsEmbedding X → IsEmbedding (sum X Y)
  /-- Scaling `t X`. -/
  smul : ℝ → Map → Map
  F_smul : ∀ t X, F (smul t X) = (t ^ 2) • F X
  isEmbedding_smul : ∀ t X, t ≠ 0 → IsEmbedding X → IsEmbedding (smul t X)
  isFree_smul : ∀ t X, t ≠ 0 → IsFree X → IsFree (smul t X)

attribute [instance] EmbeddingProblem.instNormedAddCommGroup EmbeddingProblem.instNormedSpace

variable {G : Type} [Group G]

/-- Günther's analytic package at a free embedding `u`. -/
structure GuntherPackage (P : EmbeddingProblem G) (u : P.Map) where
  /-- A Banach space of `C^{2,α}` perturbations `v : M → ℝᴺ`. -/
  E : Type
  [instNormedAddCommGroup : NormedAddCommGroup E]
  [instNormedSpace : NormedSpace ℝ E]
  [instCompleteSpace : CompleteSpace E]
  /-- The action `(σ · v)(x) = ρ(σ) v(σ⁻¹ x)`. -/
  [instAction : DistribMulAction G E]
  [instIsometric : IsIsometricSMul G E]
  /-- The linear part `𝓜 h = L(u)(0, -h/2)`. -/
  M : P.Met →L[ℝ] E
  /-- The quadratic part `𝓑(v, w) = L(u)((Δ - 1)⁻¹ Q(v, w))`. -/
  B : E →L[ℝ] E →L[ℝ] E
  M_fixed : ∀ (σ : G) (h : P.Met), σ • M h = M h
  B_equivariant : ∀ (σ : G) (v w : E), B (σ • v) (σ • w) = σ • B v w
  /-- The set of smooth perturbations. -/
  Smooth : Set E
  /-- `u + v`, for a smooth `G`-fixed perturbation `v`. -/
  perturb : (v : E) → v ∈ Smooth → (∀ σ : G, σ • v = v) → P.Map
  /-- Günther's identity: a solution of the fixed point equation solves the embedding
  equation. -/
  F_perturb : ∀ (h : P.Met) (v : E) (hs : v ∈ Smooth) (hf : ∀ σ : G, σ • v = v),
    v = M h + B v v → P.F (perturb v hs hf) = P.F u + h
  /-- Elliptic regularity: small solutions are smooth. -/
  regularity : ∃ r > 0, ∀ (h : P.Met) (v : E), ‖v‖ < r → v = M h + B v v → v ∈ Smooth
  /-- Small perturbations of the embedding `u` are embeddings. -/
  isEmbedding_perturb : ∃ δ > 0, ∀ (v : E) (hs : v ∈ Smooth) (hf : ∀ σ : G, σ • v = v),
    ‖v‖ < δ → P.IsEmbedding (perturb v hs hf)

attribute [instance] GuntherPackage.instNormedAddCommGroup GuntherPackage.instNormedSpace
  GuntherPackage.instCompleteSpace GuntherPackage.instAction GuntherPackage.instIsometric

/-- Hypothesis 1: there is a free equivariant embedding. -/
def HasFreeEmbedding (P : EmbeddingProblem G) : Prop :=
  ∃ u : P.Map, P.IsEmbedding u ∧ P.IsFree u

/-- Hypothesis 2: realizable metrics are dense in the positive definite invariant metrics. -/
def RealizableDense (P : EmbeddingProblem G) : Prop :=
  ∀ g ∈ P.pos, ∀ ε > 0, ∃ X : P.Map, ‖g - P.F X‖ < ε

/-- Hypothesis 3: `g - c F(X)` is positive definite for small `c > 0`. -/
def ConeCondition (P : EmbeddingProblem G) : Prop :=
  ∀ g ∈ P.pos, ∀ X : P.Map, ∃ c : ℝ, 0 < c ∧ g - c • P.F X ∈ P.pos

/-- Hypothesis 4: Günther's analytic package exists at every free embedding. -/
def HasGuntherPackages (P : EmbeddingProblem G) : Prop :=
  ∀ u : P.Map, P.IsEmbedding u → P.IsFree u → Nonempty (GuntherPackage P u)

end EquivEmbed

/-- **Equivariant Günther fixed point theorem.**  Let `E` be a real Banach space on which a
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
      ∀ w : E, ‖w‖ ≤ 2 * ‖m‖ → w = m + B w w → w = v := by
  sorry

/-- **The pointwise Nash–Günther right inverse.**  If `A : W → V` is injective (the map is
*free* at a point: first and second derivatives are linearly independent), then for every `b`
the system `A† x = b` has a unique solution in the range of `A`, and it is the solution of least
norm.  (It is `x = A (A† A)⁻¹ b`.) -/
theorem EquivEmbed.nash_gunther_right_inverse
    {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
    (A : W →ₗ[ℝ] V) (hA : Function.Injective A) (b : W) :
    ∃ x : V, x ∈ LinearMap.range A ∧ LinearMap.adjoint A x = b ∧
      (∀ y : V, LinearMap.adjoint A y = b → ‖x‖ ≤ ‖y‖) ∧
      ∀ x' : V, x' ∈ LinearMap.range A → LinearMap.adjoint A x' = b → x' = x := by
  sorry

/-- **Equivariance of the Nash–Günther correction.**  Suppose the frame at `σ p` is
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
    x' = R x := by
  sorry

/-- **Freeness of the Veronese map `X ↦ (X, X ⊙ X)` (pointwise).**  At a point write
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
    c = 0 ∧ d = 0 := by
  sorry

/-- **The averaged inner product of Step 2.**  Let a compact group `G` act linearly and
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
      (∀ (τ : G) x y, q (ρ τ x) (ρ τ y) = q x y) ∧ (∀ x, x ≠ 0 → 0 < q x x) := by
  sorry

/-- **Equivariant Günther perturbation theorem.**  At an embedding `u` admitting Günther's
analytic package, every sufficiently small `G`-invariant metric perturbation `h` is realized by
an equivariant embedding: `F(X) = F(u) + h`. -/
theorem EquivEmbed.equivariant_gunther_perturbation {G : Type} [Group G]
    {P : EquivEmbed.EmbeddingProblem G} {u : P.Map} (D : EquivEmbed.GuntherPackage P u) :
    ∃ ε > 0, ∀ h : P.Met, ‖h‖ < ε → ∃ X : P.Map, P.IsEmbedding X ∧ P.F X = P.F u + h := by
  sorry

/-- **Moore–Schlafly equivariant isometric embedding theorem, via Günther's method
(conditional form).**  Given (1) a free equivariant embedding, (2) density of realizable
invariant metrics, (3) the cone condition, and (4) Günther's non-equivariant analytic package at
free embeddings, every positive definite `G`-invariant metric is induced by a `G`-equivariant
embedding. -/
theorem EquivEmbed.equivariant_isometric_embedding_conditional {G : Type} [Group G]
    (P : EquivEmbed.EmbeddingProblem G) (h1 : EquivEmbed.HasFreeEmbedding P)
    (h2 : EquivEmbed.RealizableDense P) (h3 : EquivEmbed.ConeCondition P)
    (h4 : EquivEmbed.HasGuntherPackages P) :
    ∀ g ∈ P.pos, ∃ X : P.Map, P.IsEmbedding X ∧ P.F X = g := by
  sorry
