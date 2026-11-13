/-
Copyright (c) 2026 Roger Schlafly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roger Schlafly
-/
module

public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Topology.MetricSpace.IsometricSMul
public import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Definitions for the conditional equivariant isometric embedding theorem

These definitions are copied verbatim into `Challenge.lean`.  See `EquivEmbed.Assembly` for
their meaning.

**Equivariance is enforced by the types.**  Every map in the theory is an `EquivariantMap`: a
function `X : Pt → ℝᴺ` bundled with an orthogonal representation `ρ` of `G` on `ℝᴺ` and a proof
that `X (σ • p) = ρ σ (X p)`.  So every map the theorems produce is equivariant by construction,
and the conclusions also state it explicitly.

**What is not enforced.**  The geometric meaning of `Met` (invariant `C^{2,α}` symmetric
2-tensors), of `pos` (positive definite tensors), of `F` (the induced metric `∑ dXᵃ ⊗ dXᵃ`), of
`IsFree`, and of `IsEmbedding` beyond injectivity, is not encoded in Lean.  It must be supplied by
an external instantiation of `EmbeddingProblem` for an actual compact Riemannian `G`-manifold;
the theorems apply to any instantiation, and say nothing more about these notions than what the
structure fields require.
-/

@[expose] public section

namespace EquivEmbed

/-- A `G`-equivariant map `Pt → ℝᴺ`: a function `toFun` together with an orthogonal
representation `ρ` of `G` on `ℝᴺ` such that `toFun (σ • p) = ρ σ (toFun p)`. -/
structure EquivariantMap (G : Type) [Group G] (Pt : Type) [MulAction G Pt] where
  /-- The dimension of the target. -/
  N : ℕ
  /-- The orthogonal representation of `G` on `ℝᴺ`. -/
  ρ : G →* (EuclideanSpace ℝ (Fin N) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin N))
  /-- The underlying function. -/
  toFun : Pt → EuclideanSpace ℝ (Fin N)
  /-- Equivariance. -/
  equivariant : ∀ (σ : G) (p : Pt), toFun (σ • p) = ρ σ (toFun p)

/-- The scaled map `t X`, with the same representation. -/
def EquivariantMap.smul {G : Type} [Group G] {Pt : Type} [MulAction G Pt] (t : ℝ)
    (X : EquivariantMap G Pt) : EquivariantMap G Pt where
  N := X.N
  ρ := X.ρ
  toFun p := t • X.toFun p
  equivariant σ p := by rw [X.equivariant, LinearIsometryEquiv.map_smul]

/-- Abstract data of the equivariant isometric embedding problem for a compact Riemannian
manifold with an isometric action of `G`.  The intended meaning of each field is in its
docstring; only the stated properties are enforced. -/
structure EmbeddingProblem (G : Type) [Group G] where
  /-- The points of the manifold `M`. -/
  Pt : Type
  [instMulAction : MulAction G Pt]
  /-- Intended: smooth `G`-invariant symmetric 2-tensors on `M`, with a `C^{2,α}` norm. -/
  Met : Type
  [instNormedAddCommGroup : NormedAddCommGroup Met]
  [instNormedSpace : NormedSpace ℝ Met]
  /-- Intended: the positive definite elements of `Met`. -/
  pos : Set Met
  /-- Intended: the induced metric `F(X) = ∑ₐ dXᵃ ⊗ dXᵃ`. -/
  F : EquivariantMap G Pt → Met
  /-- Intended: `X` is a smooth embedding.  Enforced: `X` is injective. -/
  IsEmbedding : EquivariantMap G Pt → Prop
  injective_of_isEmbedding : ∀ X, IsEmbedding X → Function.Injective X.toFun
  /-- Intended: `X` is free (first and second derivatives linearly independent everywhere). -/
  IsFree : EquivariantMap G Pt → Prop
  /-- Intended: the direct sum `(X, Y) : M → ℝ^{N₁} ⊕ ℝ^{N₂}` with representation `ρ₁ ⊕ ρ₂`. -/
  sum : EquivariantMap G Pt → EquivariantMap G Pt → EquivariantMap G Pt
  F_sum : ∀ X Y, F (sum X Y) = F X + F Y
  isEmbedding_sum : ∀ X Y, IsEmbedding X → IsEmbedding (sum X Y)
  F_smul : ∀ (t : ℝ) (X : EquivariantMap G Pt), F (X.smul t) = (t ^ 2) • F X
  isEmbedding_smul : ∀ (t : ℝ) (X : EquivariantMap G Pt), t ≠ 0 → IsEmbedding X →
    IsEmbedding (X.smul t)
  isFree_smul : ∀ (t : ℝ) (X : EquivariantMap G Pt), t ≠ 0 → IsFree X → IsFree (X.smul t)

attribute [instance] EmbeddingProblem.instMulAction EmbeddingProblem.instNormedAddCommGroup
  EmbeddingProblem.instNormedSpace

variable {G : Type} [Group G]

/-- The equivariant maps of an embedding problem. -/
abbrev EmbeddingProblem.Map (P : EmbeddingProblem G) : Type := EquivariantMap G P.Pt

/-- Günther's analytic package at an embedding `u`. -/
structure GuntherPackage (P : EmbeddingProblem G) (u : P.Map) where
  /-- Intended: a Banach space of `C^{2,α}` perturbations `v : M → ℝᴺ`. -/
  E : Type
  [instNormedAddCommGroup : NormedAddCommGroup E]
  [instNormedSpace : NormedSpace ℝ E]
  [instCompleteSpace : CompleteSpace E]
  /-- Intended: the action `(σ · v)(x) = ρ(σ) v(σ⁻¹ x)`. -/
  [instAction : DistribMulAction G E]
  [instIsometric : IsIsometricSMul G E]
  /-- Intended: the linear part `𝓜 h = L(u)(0, -h/2)`. -/
  M : P.Met →L[ℝ] E
  /-- Intended: the quadratic part `𝓑(v, w) = L(u)((Δ - 1)⁻¹ Q(v, w))`. -/
  B : E →L[ℝ] E →L[ℝ] E
  M_fixed : ∀ (σ : G) (h : P.Met), σ • M h = M h
  B_equivariant : ∀ (σ : G) (v w : E), B (σ • v) (σ • w) = σ • B v w
  /-- Intended: the set of smooth perturbations. -/
  Smooth : Set E
  /-- Intended: `u + v`, for a smooth `G`-fixed perturbation `v`. -/
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

/-- Hypothesis 3 (cone condition): for every positive definite `g` and every map `X`,
`g - c F(X)` is positive definite for *some* `c > 0`.  (Geometrically it holds for all small
`c > 0` by compactness; only the existence of one such `c` is assumed and used.) -/
def ConeCondition (P : EmbeddingProblem G) : Prop :=
  ∀ g ∈ P.pos, ∀ X : P.Map, ∃ c : ℝ, 0 < c ∧ g - c • P.F X ∈ P.pos

/-- Hypothesis 4: Günther's analytic package exists at every free embedding. -/
def HasGuntherPackages (P : EmbeddingProblem G) : Prop :=
  ∀ u : P.Map, P.IsEmbedding u → P.IsFree u → Nonempty (GuntherPackage P u)

end EquivEmbed
