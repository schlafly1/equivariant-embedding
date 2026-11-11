/-
Copyright (c) 2026 Roger Schlafly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roger Schlafly
-/
module

public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Topology.MetricSpace.IsometricSMul

/-!
# Definitions for the conditional equivariant isometric embedding theorem

These definitions are copied verbatim into `Challenge.lean`.  See `EquivEmbed.Assembly` for
their meaning.
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
