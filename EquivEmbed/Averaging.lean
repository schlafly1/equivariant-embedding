/-
Copyright (c) 2026 Roger Schlafly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roger Schlafly
-/
module

public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Mathlib.MeasureTheory.Measure.OpenPos
public import Mathlib.RepresentationTheory.Basic
public import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# The averaged inner product of Step 2

In Step 2 of Moore–Schlafly (1980, §3) a function `f` on `M` lies in a finite-dimensional
`G`-invariant space `Vᵢ` of functions (a sum of Laplace eigenspaces).  The evaluation map
`Xᵢ : M → Vᵢ*`, `Xᵢ(p)(f) = f(p)`, is equivariant, and `Vᵢ*` is given the Euclidean structure

  `⟪ξ, η⟫ = ∫_G ξ(σ·f) η(σ·f) dσ`.

With this inner product the induced metric is the Haar average `F(Xᵢ) = ∫_G σ*(df ⊗ df) dσ`.

Abstractly: `W` (playing the role of `Vᵢ*`) is a finite-dimensional real representation of a
compact group `G`, `φ` is a linear functional on `W` (evaluation at `f`), and

  `avgForm μ ρ φ x y = ∫ φ(ρ(σ⁻¹) x) φ(ρ(σ⁻¹) y) dμ(σ)`.

We show that `avgForm` is a symmetric bilinear form that is invariant under `ρ`, positive
semidefinite, and positive definite when the translates of `φ` separate points of `W` (the
1980 paper: "as `σ` ranges throughout `G`, `σ(f)` generates `Vᵢ`").  So `ρ` is orthogonal
for this inner product.
-/

@[expose] public section

set_option linter.unusedSectionVars false

open MeasureTheory

namespace EquivEmbed

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [MeasurableSpace G] [BorelSpace G]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] [FiniteDimensional ℝ W]

/-- The Haar-averaged form `⟪x, y⟫ = ∫ φ(ρ(σ⁻¹)x) φ(ρ(σ⁻¹)y) dμ(σ)`. -/
noncomputable def avgForm (μ : Measure G) (ρ : Representation ℝ G W) (φ : Module.Dual ℝ W)
    (x y : W) : ℝ :=
  ∫ σ, φ (ρ σ⁻¹ x) * φ (ρ σ⁻¹ y) ∂μ

variable (μ : Measure G) (ρ : Representation ℝ G W) (φ : Module.Dual ℝ W)

lemma avgForm_symm (x y : W) : avgForm μ ρ φ x y = avgForm μ ρ φ y x := by
  simp only [avgForm, mul_comm]

lemma avgForm_self_nonneg (x : W) : 0 ≤ avgForm μ ρ φ x x :=
  integral_nonneg fun _ => mul_self_nonneg _

/-- **Invariance.** `ρ(τ)` is orthogonal for the averaged form. -/
theorem avgForm_invariant [μ.IsMulLeftInvariant] (τ : G) (x y : W) :
    avgForm μ ρ φ (ρ τ x) (ρ τ y) = avgForm μ ρ φ x y := by
  unfold avgForm
  have key : ∀ σ : G, φ (ρ σ⁻¹ (ρ τ x)) * φ (ρ σ⁻¹ (ρ τ y)) =
      (fun σ => φ (ρ σ⁻¹ x) * φ (ρ σ⁻¹ y)) (τ⁻¹ * σ) := by
    intro σ
    simp only [mul_inv_rev, inv_inv, map_mul, Module.End.mul_apply]
  simp_rw [key]
  exact integral_mul_left_eq_self (fun σ => φ (ρ σ⁻¹ x) * φ (ρ σ⁻¹ y)) τ⁻¹

section continuity

variable (hcont : ∀ x : W, Continuous fun σ : G => ρ σ x)
include hcont

lemma continuous_translate (x : W) : Continuous fun σ : G => φ (ρ σ⁻¹ x) :=
  (LinearMap.continuous_of_finiteDimensional φ).comp ((hcont x).comp continuous_inv)

lemma integrable_avg [IsFiniteMeasure μ] (x y : W) :
    Integrable (fun σ => φ (ρ σ⁻¹ x) * φ (ρ σ⁻¹ y)) μ :=
  ((continuous_translate ρ φ hcont x).mul
    (continuous_translate ρ φ hcont y)).integrable_of_hasCompactSupport
    (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _))

lemma avgForm_add_left [IsFiniteMeasure μ] (x x' y : W) :
    avgForm μ ρ φ (x + x') y = avgForm μ ρ φ x y + avgForm μ ρ φ x' y := by
  unfold avgForm
  rw [← integral_add (integrable_avg μ ρ φ hcont x y) (integrable_avg μ ρ φ hcont x' y)]
  congr 1
  funext σ
  simp only [map_add, add_mul]

omit hcont in
lemma avgForm_smul_left (a : ℝ) (x y : W) :
    avgForm μ ρ φ (a • x) y = a * avgForm μ ρ φ x y := by
  unfold avgForm
  rw [← integral_const_mul]
  congr 1
  funext σ
  simp only [map_smul, smul_eq_mul, mul_assoc]

/-- **Positive definiteness.** If the translates `φ ∘ ρ(σ)` separate points of `W` and `μ` is
positive on nonempty open sets (e.g. Haar measure), the averaged form is positive definite. -/
theorem avgForm_self_pos [IsFiniteMeasure μ] [μ.IsOpenPosMeasure]
    (hsep : ∀ x : W, (∀ σ : G, φ (ρ σ x) = 0) → x = 0) {x : W} (hx : x ≠ 0) :
    0 < avgForm μ ρ φ x x := by
  by_contra hle
  push Not at hle
  obtain ⟨σ₀, hσ₀⟩ : ∃ σ : G, φ (ρ σ x) ≠ 0 := by
    by_contra h
    push Not at h
    exact hx (hsep x h)
  have hpos : 0 < ∫ σ, φ (ρ σ⁻¹ x) * φ (ρ σ⁻¹ x) ∂μ := by
    refine Continuous.integral_pos_of_hasCompactSupport_nonneg_nonzero (x := σ₀⁻¹)
      ((continuous_translate ρ φ hcont x).mul (continuous_translate ρ φ hcont x))
      (isCompact_univ.of_isClosed_subset (isClosed_tsupport _) (Set.subset_univ _))
      (fun σ => mul_self_nonneg _) ?_
    simpa [inv_inv] using mul_self_ne_zero.mpr hσ₀
  exact absurd hle (not_le.mpr hpos)

end continuity

end EquivEmbed
