/-
Copyright (c) 2026 Roger Schlafly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roger Schlafly
-/
module

public import EquivEmbed.FixedPoint
public import EquivEmbed.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# Assembly of the equivariant isometric embedding theorem (conditional form)

This file proves the *logical structure* of the proof of the Moore–Schlafly theorem via
Günther's method, with the analytic inputs taken as explicit hypotheses.

An `EmbeddingProblem G` packages, for a fixed compact Riemannian `G`-manifold `M`:

* `Met`: the space of smooth `G`-invariant symmetric 2-tensors on `M` with a `C^{2,α}` norm;
* `pos ⊆ Met`: the positive definite ones;
* `Map`: smooth maps `M → ℝᴺ` (any `N`) that are equivariant for some orthogonal
  representation of `G`;
* `F : Map → Met`: the induced metric `F(X) = ∑ dXᵃ ⊗ dXᵃ`;
* the elementary operations: direct sum `(X, Y)` and scaling `t X`, with
  `F(X, Y) = F X + F Y` and `F(t X) = t² F X`.

The hypotheses of `equivariant_isometric_embedding` are:

1. `HasFreeEmbedding`: there is a free equivariant embedding (Mostow–Palais plus the Veronese
   trick; the linear algebra of the latter is `EquivEmbed.veronese_free`);
2. `RealizableDense`: every positive definite invariant metric is approximated by induced
   metrics of equivariant maps (Step 2 of Moore–Schlafly; the invariant inner product used
   there is `EquivEmbed.avgForm`);
3. `ConeCondition`: for `g` positive definite and any `X`, `g - c F(X)` is positive definite for
   some `c > 0` (compactness of `M`);
4. `GuntherPackage`: for every free embedding `u`, Günther's (non-equivariant) analytic
   package: a Banach space `E` of `C^{2,α}` perturbations with an isometric linear `G`-action,
   a bounded linear `𝓜 : Met → E` with `G`-fixed values and a bounded bilinear equivariant
   `𝓑`, such that `v = 𝓜 h + 𝓑(v, v)` implies `F(u + v) = F(u) + h`, small solutions are
   smooth, and small perturbations of an embedding are embeddings.  The equivariance of `𝓜`
   and `𝓑` rests on `EquivEmbed.rightInv_equivariant` and on the fact that `(Δ - 1)⁻¹`
   commutes with isometries.

Nothing in the hypotheses asserts the existence of an equivariant solution of the nonlinear
problem: that is produced here by `EquivEmbed.exists_fixedPoint_bilinear_invariant`.
-/

@[expose] public section

open Metric

namespace EquivEmbed

variable {G : Type} [Group G]

/-- **Equivariant Günther perturbation theorem.**  At a free embedding with a Günther package,
every sufficiently small invariant metric perturbation is realized by an equivariant
embedding. -/
theorem equivariant_perturbation {P : EmbeddingProblem G} {u : P.Map}
    (D : GuntherPackage P u) :
    ∃ ε > 0, ∀ h : P.Met, ‖h‖ < ε → ∃ X : P.Map, P.IsEmbedding X ∧ P.F X = P.F u + h := by
  obtain ⟨r, hr, hreg⟩ := D.regularity
  obtain ⟨δ, hδ, hemb⟩ := D.isEmbedding_perturb
  set η : ℝ := min (min δ r / 2) (1 / (4 * ‖D.B‖ + 1)) with hη
  have hη0 : 0 < η := lt_min (by positivity) (by positivity)
  refine ⟨η / (‖D.M‖ + 1), by positivity, fun h hh => ?_⟩
  set m := D.M h with hm
  have hmη : ‖m‖ < η := by
    calc ‖m‖ ≤ ‖D.M‖ * ‖h‖ := D.M.le_opNorm h
      _ ≤ ‖D.M‖ * (η / (‖D.M‖ + 1)) := by gcongr
      _ < η := by
        rw [mul_div_assoc', div_lt_iff₀ (by positivity)]
        nlinarith
  have hB : 4 * ‖D.B‖ * ‖m‖ < 1 := by
    have h1 : η ≤ 1 / (4 * ‖D.B‖ + 1) := min_le_right _ _
    have h2 : 4 * ‖D.B‖ * ‖m‖ ≤ 4 * ‖D.B‖ * η := by gcongr
    have h3 : 4 * ‖D.B‖ * η ≤ 4 * ‖D.B‖ * (1 / (4 * ‖D.B‖ + 1)) := by gcongr
    have h4 : 4 * ‖D.B‖ * (1 / (4 * ‖D.B‖ + 1)) < 1 := by
      rw [mul_one_div, div_lt_one (by positivity)]
      linarith
    linarith
  obtain ⟨v, hvn, hvf, hvG⟩ :=
    exists_fixedPoint_bilinear_invariant (G := G) D.B hB (fun σ => D.M_fixed σ h)
      D.B_equivariant
  have hv2 : ‖v‖ < min δ r := by
    have : η ≤ min δ r / 2 := min_le_left _ _
    linarith
  have hvs : v ∈ D.Smooth := hreg h v (lt_of_lt_of_le hv2 (min_le_right _ _)) hvf
  exact ⟨D.perturb v hvs hvG, hemb v hvs hvG (lt_of_lt_of_le hv2 (min_le_left _ _)),
    D.F_perturb h v hvs hvG hvf⟩

/-- **Equivariant isometric embedding theorem (conditional form).**  Under the four
hypotheses above, every positive definite invariant metric is induced by an equivariant
embedding. -/
theorem equivariant_isometric_embedding (P : EmbeddingProblem G)
    (h1 : HasFreeEmbedding P) (h2 : RealizableDense P) (h3 : ConeCondition P)
    (h4 : HasGuntherPackages P) :
    ∀ g ∈ P.pos, ∃ X : P.Map, P.IsEmbedding X ∧ P.F X = g := by
  intro g hg
  obtain ⟨u₀, hu₀e, hu₀f⟩ := h1
  obtain ⟨c, hc, hgc⟩ := h3 g hg u₀
  -- rescale the free embedding: `F(√c u₀) = c F(u₀)`
  set t := Real.sqrt c with ht
  have ht0 : t ≠ 0 := (Real.sqrt_pos.mpr hc).ne'
  set u₁ := P.smul t u₀
  have hFu₁ : P.F u₁ = c • P.F u₀ := by
    rw [P.F_smul, ht, Real.sq_sqrt hc.le]
  obtain ⟨D⟩ := h4 u₁ (P.isEmbedding_smul t u₀ ht0 hu₀e) (P.isFree_smul t u₀ ht0 hu₀f)
  obtain ⟨ε, hε, hpert⟩ := equivariant_perturbation D
  -- approximate `g - c F(u₀)` by a realizable metric `F(X₂)`
  obtain ⟨X₂, hX₂⟩ := h2 _ hgc ε hε
  -- realize `g - F(X₂) = F(u₁) + h` by a perturbation of `u₁`
  obtain ⟨X₁, hX₁e, hX₁F⟩ := hpert (g - c • P.F u₀ - P.F X₂) hX₂
  refine ⟨P.sum X₁ X₂, P.isEmbedding_sum X₁ X₂ hX₁e, ?_⟩
  rw [P.F_sum, hX₁F, hFu₁]
  abel

end EquivEmbed
