/-
Copyright (c) 2026 Roger Schlafly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roger Schlafly
-/
module

public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith

/-!
# Freeness of the Veronese map

If `X : M → V` is an immersion, the map `X̃ = (X, X ⊙ X) : M → V ⊕ Sym²V` is *free*: at every
point the vectors `∂ᵢX̃` and `∂ᵢ∂ⱼX̃ (i ≤ j)` are linearly independent.  This is how Nash and
Moore–Schlafly obtain a free ("perturbable") equivariant starting embedding from an arbitrary
equivariant embedding (Mostow–Palais): `X̃` is equivariant for the representation `V ⊕ Sym²V`.

We formalize the pointwise linear algebra.  Fix a point and write `x = X(p)`,
`x₁ i = ∂ᵢX(p)` (linearly independent, since `X` is an immersion) and `x₂ i j = ∂ᵢ∂ⱼX(p)`.
By the product rule,

* `∂ᵢ (X ⊙ X) = x₁ i ⊙ x + x ⊙ x₁ i`,
* `∂ᵢ∂ⱼ (X ⊙ X) = x₂ i j ⊙ x + x ⊙ x₂ i j + x₁ i ⊙ x₁ j + x₁ j ⊙ x₁ i`.

An element `∑ aₖ ⊗ bₖ` of `V ⊗ V` vanishes iff `∑ φ(aₖ) ψ(bₖ) = 0` for all linear functionals
`φ, ψ`, so we express the `Sym²V` component through such evaluations.  The theorem
`veronese_free` says that a linear relation `∑ cᵢ ∂ᵢX̃ + ∑ dᵢⱼ ∂ᵢ∂ⱼX̃ = 0` with `d` symmetric
forces `c = 0` and `d = 0`.
-/

@[expose] public section

open Finset

namespace EquivEmbed

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- Functionals dual to a linearly independent family. -/
lemma exists_dual_family {n : ℕ} {x₁ : Fin n → V} (hli : LinearIndependent ℝ x₁) :
    ∃ e : Fin n → Module.Dual ℝ V, ∀ k i, e k (x₁ i) = if i = k then 1 else 0 := by
  obtain ⟨g, hg⟩ := LinearMap.exists_extend hli.repr
  refine ⟨fun k => Finsupp.lapply k ∘ₗ g, fun k i => ?_⟩
  have hmem : x₁ i ∈ Submodule.span ℝ (Set.range x₁) := Submodule.subset_span ⟨i, rfl⟩
  have h1 : g (x₁ i) = hli.repr ⟨x₁ i, hmem⟩ := by
    rw [← hg]; rfl
  simp only [LinearMap.coe_comp, Function.comp_apply, Finsupp.lapply_apply, h1,
    hli.repr_eq_single i ⟨x₁ i, hmem⟩ rfl, Finsupp.single_apply]

/-- The `Sym²V`-component of `∑ cᵢ ∂ᵢX̃ + ∑ dᵢⱼ ∂ᵢ∂ⱼX̃`, evaluated on `φ ⊗ ψ`. -/
def veroneseSym {n : ℕ} (x : V) (x₁ : Fin n → V) (x₂ : Fin n → Fin n → V)
    (c : Fin n → ℝ) (d : Fin n → Fin n → ℝ) (φ ψ : Module.Dual ℝ V) : ℝ :=
  ∑ i, c i * (φ (x₁ i) * ψ x + φ x * ψ (x₁ i)) +
    ∑ i, ∑ j, d i j * (φ (x₂ i j) * ψ x + φ x * ψ (x₂ i j) +
      φ (x₁ i) * ψ (x₁ j) + φ (x₁ j) * ψ (x₁ i))

/-- The `V`-component of `∑ cᵢ ∂ᵢX̃ + ∑ dᵢⱼ ∂ᵢ∂ⱼX̃`. -/
def veroneseVec {n : ℕ} (x₁ : Fin n → V) (x₂ : Fin n → Fin n → V)
    (c : Fin n → ℝ) (d : Fin n → Fin n → ℝ) : V :=
  ∑ i, c i • x₁ i + ∑ i, ∑ j, d i j • x₂ i j

lemma veroneseSym_eq {n : ℕ} (x : V) (x₁ : Fin n → V) (x₂ : Fin n → Fin n → V)
    (c : Fin n → ℝ) (d : Fin n → Fin n → ℝ) (φ ψ : Module.Dual ℝ V) :
    veroneseSym x x₁ x₂ c d φ ψ =
      φ (veroneseVec x₁ x₂ c d) * ψ x + φ x * ψ (veroneseVec x₁ x₂ c d) +
        ∑ i, ∑ j, d i j * (φ (x₁ i) * ψ (x₁ j) + φ (x₁ j) * ψ (x₁ i)) := by
  simp only [veroneseSym, veroneseVec, map_add, map_sum, map_smul, smul_eq_mul]
  simp only [add_mul, mul_add, sum_mul, mul_sum, sum_add_distrib]
  have e1 : ∀ i, c i * (φ (x₁ i) * ψ x) = c i * φ (x₁ i) * ψ x := fun i => by ring
  have e2 : ∀ i, c i * (φ x * ψ (x₁ i)) = φ x * (c i * ψ (x₁ i)) := fun i => by ring
  have e3 : ∀ i j, d i j * (φ (x₂ i j) * ψ x) = d i j * φ (x₂ i j) * ψ x := fun i j => by ring
  have e4 : ∀ i j, d i j * (φ x * ψ (x₂ i j)) = φ x * (d i j * ψ (x₂ i j)) :=
    fun i j => by ring
  simp only [e1, e2, e3, e4]
  ring

/-- **Freeness of the Veronese map (pointwise).**  If the first derivatives `x₁ i` are
linearly independent and `∑ cᵢ ∂ᵢX̃ + ∑ dᵢⱼ ∂ᵢ∂ⱼX̃ = 0` with `d` symmetric, then `c = 0` and
`d = 0`. -/
theorem veronese_free {n : ℕ} (x : V) (x₁ : Fin n → V) (hli : LinearIndependent ℝ x₁)
    (x₂ : Fin n → Fin n → V) (c : Fin n → ℝ) (d : Fin n → Fin n → ℝ)
    (hd : ∀ i j, d i j = d j i)
    (hvec : veroneseVec x₁ x₂ c d = 0)
    (hsym : ∀ φ ψ : Module.Dual ℝ V, veroneseSym x x₁ x₂ c d φ ψ = 0) :
    c = 0 ∧ d = 0 := by
  obtain ⟨e, he⟩ := exists_dual_family hli
  have hd0 : d = 0 := by
    funext k l
    have h := hsym (e k) (e l)
    rw [veroneseSym_eq, hvec, map_zero, map_zero, zero_mul, mul_zero, zero_add,
      zero_add] at h
    have h1 : ∑ i, ∑ j, d i j * (e k (x₁ i) * e l (x₁ j)) = d k l := by
      simp only [he, mul_ite, mul_zero, mul_one, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
    have h2 : ∑ i, ∑ j, d i j * (e k (x₁ j) * e l (x₁ i)) = d l k := by
      simp only [he, mul_ite, mul_zero, mul_one, Finset.sum_ite_eq',
        Finset.mem_univ, ite_true, Finset.sum_ite_irrel, Finset.sum_const_zero]
    simp only [mul_add, Finset.sum_add_distrib, h1, h2, hd l k] at h
    simp only [Pi.zero_apply]
    linarith
  refine ⟨?_, hd0⟩
  subst hd0
  have hc : ∑ i, c i • x₁ i = 0 := by
    simpa [veroneseVec] using hvec
  funext i
  exact Fintype.linearIndependent_iff.mp hli c hc i

end EquivEmbed
