/-
Copyright (c) 2026 Roger Schlafly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roger Schlafly
-/
module

public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# The pointwise Nash–Günther right inverse and its equivariance

Let `u : M → V` be a map into a Euclidean space.  At a point `p`, with local coordinates
`(x¹,…,xⁿ)`, put `W = ℝⁿ × Sym²(ℝⁿ)` and let `A(p) : W → V` be the linear map whose columns are
`∂ᵢu(p)` and `∂ᵢ∂ⱼu(p)`.  The map `u` is *free* (Nash: *perturbable*) at `p` when `A(p)` is
injective.  Both Nash's and Günther's proofs solve the pointwise linear system
`A(p)ᵀ x = b` by the formula

  `x = A (Aᵀ A)⁻¹ b`.

In this file `A : W →ₗ V` is an injective linear map between finite-dimensional real inner
product spaces and `rightInv A hA b := A ((A† A)⁻¹ b)`.  We prove

* `adjoint_rightInv`: `A† (rightInv A hA b) = b`;
* `eq_rightInv_of_mem_range`: `rightInv A hA b` is the unique solution of `A† x = b` lying in
  `range A`;
* `norm_rightInv_le`: it is the solution of least norm;
* `rightInv_isometry_comp`: `rightInv (R ∘ A) = R ∘ rightInv A` for a linear isometry
  equivalence `R` (equivariance under an orthogonal representation);
* `rightInv_comp_equiv`: invariance under a change of coordinates `P` on `W`;
* `rightInv_equivariant`: the combination used to show that the Nash–Günther correction of an
  equivariant map is equivariant (Moore–Schlafly 1980, §2).
-/

@[expose] public section

open LinearMap Function

namespace EquivEmbed

variable {V V' W W' : Type*}
  [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [NormedAddCommGroup V'] [InnerProductSpace ℝ V'] [FiniteDimensional ℝ V']
  [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [NormedAddCommGroup W'] [InnerProductSpace ℝ W'] [FiniteDimensional ℝ W']

/-- The Gram operator `A† A`. -/
noncomputable def gram (A : W →ₗ[ℝ] V) : W →ₗ[ℝ] W := adjoint A ∘ₗ A

lemma inner_gram_self (A : W →ₗ[ℝ] V) (w : W) :
    inner ℝ (gram A w) w = inner ℝ (A w) (A w) := by
  simp [gram, adjoint_inner_left]

lemma gram_injective {A : W →ₗ[ℝ] V} (hA : Injective A) : Injective (gram A) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro w hw
  have h0 : inner ℝ (A w) (A w) = 0 := by rw [← inner_gram_self, hw, inner_zero_left]
  exact hA (by rw [inner_self_eq_zero.mp h0, map_zero])

/-- The Gram operator of an injective map, as a linear equivalence. -/
noncomputable def gramEquiv {A : W →ₗ[ℝ] V} (hA : Injective A) : W ≃ₗ[ℝ] W :=
  LinearEquiv.ofInjectiveEndo (gram A) (gram_injective hA)

@[simp] lemma gramEquiv_apply {A : W →ₗ[ℝ] V} (hA : Injective A) (w : W) :
    gramEquiv hA w = gram A w := rfl

/-- The Nash–Günther right inverse `b ↦ A (A† A)⁻¹ b` of `A†`. -/
noncomputable def rightInv (A : W →ₗ[ℝ] V) (hA : Injective A) : W →ₗ[ℝ] V :=
  A ∘ₗ (gramEquiv hA).symm.toLinearMap

lemma rightInv_apply (A : W →ₗ[ℝ] V) (hA : Injective A) (b : W) :
    rightInv A hA b = A ((gramEquiv hA).symm b) := rfl

/-- `rightInv A` is a right inverse of `A†`. -/
@[simp] theorem adjoint_rightInv (A : W →ₗ[ℝ] V) (hA : Injective A) (b : W) :
    adjoint A (rightInv A hA b) = b := by
  have := (gramEquiv hA).apply_symm_apply b
  rw [gramEquiv_apply] at this
  simpa [rightInv_apply, gram] using this

theorem rightInv_mem_range (A : W →ₗ[ℝ] V) (hA : Injective A) (b : W) :
    rightInv A hA b ∈ LinearMap.range A :=
  ⟨_, rfl⟩

/-- `rightInv A hA b` is the unique solution of `A† x = b` in the range of `A`. -/
theorem eq_rightInv_of_mem_range {A : W →ₗ[ℝ] V} (hA : Injective A) {b : W} {x : V}
    (hx : x ∈ LinearMap.range A) (hxb : adjoint A x = b) : x = rightInv A hA b := by
  obtain ⟨w, rfl⟩ := hx
  rw [rightInv_apply]
  congr 1
  apply (gramEquiv hA).injective
  rw [LinearEquiv.apply_symm_apply, gramEquiv_apply, ← hxb]
  rfl

/-- `rightInv A hA b` is the solution of `A† x = b` of least norm. -/
theorem norm_rightInv_le {A : W →ₗ[ℝ] V} (hA : Injective A) {b : W} {y : V}
    (hy : adjoint A y = b) : ‖rightInv A hA b‖ ≤ ‖y‖ := by
  have horth : inner ℝ (rightInv A hA b) (y - rightInv A hA b) = 0 := by
    obtain ⟨w, hw⟩ := rightInv_mem_range A hA b
    rw [← hw, ← adjoint_inner_right, map_sub, hy, hw, adjoint_rightInv, sub_self,
      inner_zero_right]
  have hpy := norm_add_sq_eq_norm_sq_add_norm_sq_real horth
  rw [add_sub_cancel] at hpy
  have h2 : ‖rightInv A hA b‖ ^ 2 ≤ ‖y‖ ^ 2 := by nlinarith [sq_nonneg ‖y - rightInv A hA b‖]
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp h2

/-- The adjoint of a linear isometry equivalence is its inverse. -/
lemma adjoint_linearIsometryEquiv (R : V ≃ₗᵢ[ℝ] V') :
    adjoint (R.toLinearEquiv.toLinearMap) = R.symm.toLinearEquiv.toLinearMap := by
  symm
  rw [eq_adjoint_iff]
  intro x y
  simp only [LinearEquiv.coe_coe, LinearIsometryEquiv.coe_toLinearEquiv]
  rw [← R.inner_map_map, LinearIsometryEquiv.apply_symm_apply]

/-- **Equivariance under orthogonal maps:** `rightInv (R ∘ A) = R ∘ rightInv A`. -/
theorem rightInv_isometry_comp (R : V ≃ₗᵢ[ℝ] V') {A : W →ₗ[ℝ] V} (hA : Injective A)
    (hRA : Injective (R.toLinearEquiv.toLinearMap ∘ₗ A)) (b : W) :
    rightInv (R.toLinearEquiv.toLinearMap ∘ₗ A) hRA b = R (rightInv A hA b) := by
  symm
  apply eq_rightInv_of_mem_range
  · obtain ⟨w, hw⟩ := rightInv_mem_range A hA b
    exact ⟨w, by simp [hw]⟩
  · rw [adjoint_comp, adjoint_linearIsometryEquiv]
    simp

/-- **Coordinate independence:** if `P : W' ≃ W` is a change of coordinates, then
`rightInv (A ∘ P) (P† b) = rightInv A b`. -/
theorem rightInv_comp_equiv {A : W →ₗ[ℝ] V} (hA : Injective A) (P : W' ≃ₗ[ℝ] W)
    (hAP : Injective (A ∘ₗ P.toLinearMap)) (b : W) :
    rightInv (A ∘ₗ P.toLinearMap) hAP (adjoint P.toLinearMap b) = rightInv A hA b := by
  symm
  apply eq_rightInv_of_mem_range
  · obtain ⟨w, hw⟩ := rightInv_mem_range A hA b
    exact ⟨P.symm w, by simp [hw]⟩
  · rw [adjoint_comp]
    simp

/-- **Equivariance of the Nash–Günther correction.**  If the "frame" `A'` at `σ p` is
`R ∘ A ∘ P`, where `A` is the frame at `p`, `R = ρ(σ)` is orthogonal and `P` is the induced
change of coordinates, and the right-hand sides correspond via `b' = P† b`, then the pointwise
solutions correspond: `x' = R x`. -/
theorem rightInv_equivariant {A A' : W →ₗ[ℝ] V} (hA : Injective A) (hA' : Injective A')
    (R : V ≃ₗᵢ[ℝ] V) (P : W ≃ₗ[ℝ] W)
    (hframe : A' = R.toLinearEquiv.toLinearMap ∘ₗ A ∘ₗ P.toLinearMap)
    {b b' : W} (hb : b' = adjoint P.toLinearMap b) :
    rightInv A' hA' b' = R (rightInv A hA b) := by
  subst hframe hb
  have hAP : Injective (A ∘ₗ P.toLinearMap) := hA.comp P.injective
  have h1 := rightInv_isometry_comp R hAP hA' (adjoint P.toLinearMap b)
  rw [h1, rightInv_comp_equiv hA P hAP b]

end EquivEmbed
