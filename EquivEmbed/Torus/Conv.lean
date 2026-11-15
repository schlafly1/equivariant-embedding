/-
Copyright (c) 2026 Roger Schlafly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roger Schlafly
-/
module

public import Mathlib.Analysis.Normed.Lp.lpSpace
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.LinearIsometry
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Topology.Algebra.InfiniteSum.Real

/-!
# Weighted `ℓ¹` convolution with a kernel

Let `ι` be a commutative group (the lattice of frequencies).  For a family of bounded bilinear
maps `β l m : F₁ → F₂ → F₃` we study the *kernel convolution*

  `convFun β a b k = ∑' l, β l (k - l) (a l) (b (k - l))`.

All the operators of Günther's method on a flat torus are of this form on Fourier coefficients:
products, derivatives and the resolvent `(Δ - 1)⁻¹` only change the kernel.

* `EquivEmbed.Torus.kconv`: if `‖β l m‖ ≤ C` the kernel convolution is a bounded bilinear map
  `ℓ¹ × ℓ¹ → ℓ¹` (Young's inequality).
* `EquivEmbed.Torus.wconv`: the weighted version.  For a weight `W` we regard `b : ℓ¹` as the
  coefficient family `tc W b k = (W k)⁻¹ • b k`, whose weighted `ℓ¹` norm is `‖b‖`.  If
  `‖β l m‖ * W (l + m) ≤ C * (W l * W m)` the kernel convolution is bounded bilinear on these
  weighted spaces.
* `EquivEmbed.Torus.wconv_twist`: naturality of the kernel convolution under a symmetry acting
  on coefficients by `(twist θ U b) k = U k (b (θ k))`.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.deprecated false

open scoped ENNReal

namespace EquivEmbed.Torus

variable {ι : Type*} [AddCommGroup ι]

section real

variable {α γ : ι → ℝ}

/-- The change of variables `(k, l) ↦ (l, k - l)`. -/
def shearEquiv (ι : Type*) [AddCommGroup ι] : ι × ι ≃ ι × ι where
  toFun p := (p.2, p.1 - p.2)
  invFun q := (q.1 + q.2, q.1)
  left_inv p := by ext <;> simp
  right_inv q := by ext <;> simp

lemma summable_conv_real (hα : Summable α) (hγ : Summable γ) (hα0 : 0 ≤ α) (hγ0 : 0 ≤ γ) :
    Summable (fun p : ι × ι => α p.2 * γ (p.1 - p.2)) :=
  (shearEquiv ι).summable_iff.mpr (hα.mul_of_nonneg hγ hα0 hγ0)

lemma conv_real_nonneg (hα0 : 0 ≤ α) (hγ0 : 0 ≤ γ) :
    0 ≤ (fun p : ι × ι => α p.2 * γ (p.1 - p.2)) :=
  fun p => mul_nonneg (hα0 _) (hγ0 _)

lemma summable_conv_real_fiber (hα : Summable α) (hγ : Summable γ) (hα0 : 0 ≤ α) (hγ0 : 0 ≤ γ)
    (k : ι) : Summable (fun l => α l * γ (k - l)) :=
  ((summable_prod_of_nonneg (conv_real_nonneg hα0 hγ0)).1
    (summable_conv_real hα hγ hα0 hγ0)).1 k

lemma summable_conv_real_sum (hα : Summable α) (hγ : Summable γ) (hα0 : 0 ≤ α) (hγ0 : 0 ≤ γ) :
    Summable (fun k => ∑' l, α l * γ (k - l)) :=
  ((summable_prod_of_nonneg (conv_real_nonneg hα0 hγ0)).1
    (summable_conv_real hα hγ hα0 hγ0)).2

lemma tsum_conv_real (hα : Summable α) (hγ : Summable γ) (hα0 : 0 ≤ α) (hγ0 : 0 ≤ γ) :
    ∑' k, ∑' l, α l * γ (k - l) = (∑' l, α l) * ∑' m, γ m := by
  have h := hα.mul_of_nonneg hγ hα0 hγ0
  have hS := summable_conv_real hα hγ hα0 hγ0
  calc ∑' k, ∑' l, α l * γ (k - l)
      = ∑' p : ι × ι, α p.2 * γ (p.1 - p.2) := (hS.tsum_prod).symm
    _ = ∑' z : ι × ι, α z.1 * γ z.2 := (shearEquiv ι).tsum_eq (fun z : ι × ι => α z.1 * γ z.2)
    _ = (∑' l, α l) * ∑' m, γ m := (hα.tsum_mul_tsum hγ h).symm

end real

variable {F F₁ F₂ F₃ : Type*}
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [NormedAddCommGroup F₃] [NormedSpace ℝ F₃]

/-- The kernel convolution of two coefficient families. -/
noncomputable def convFun (β : ι → ι → F₁ →L[ℝ] F₂ →L[ℝ] F₃) (a : ι → F₁) (b : ι → F₂)
    (k : ι) : F₃ :=
  ∑' l, β l (k - l) (a l) (b (k - l))

section conv

variable {β : ι → ι → F₁ →L[ℝ] F₂ →L[ℝ] F₃} {C : ℝ} {a : ι → F₁} {b : ι → F₂}

lemma norm_kernel_apply_le (hβ : ∀ l m, ‖β l m‖ ≤ C) (l m : ι) (x : F₁) (y : F₂) :
    ‖β l m x y‖ ≤ C * (‖x‖ * ‖y‖) := by
  have h := (β l m).le_opNorm₂ x y
  have h2 : ‖β l m‖ * ‖x‖ * ‖y‖ ≤ C * ‖x‖ * ‖y‖ := by gcongr; exact hβ l m
  linarith

variable [CompleteSpace F₃]

lemma summable_convFun_term (hβ : ∀ l m, ‖β l m‖ ≤ C) (ha : Summable fun l => ‖a l‖)
    (hb : Summable fun l => ‖b l‖) (k : ι) :
    Summable (fun l => β l (k - l) (a l) (b (k - l))) :=
  Summable.of_norm_bounded
    ((summable_conv_real_fiber ha hb (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) k).mul_left C)
    (fun l => norm_kernel_apply_le hβ _ _ _ _)

lemma norm_convFun_le (hβ : ∀ l m, ‖β l m‖ ≤ C) (ha : Summable fun l => ‖a l‖)
    (hb : Summable fun l => ‖b l‖) (k : ι) :
    ‖convFun β a b k‖ ≤ C * ∑' l, ‖a l‖ * ‖b (k - l)‖ := by
  have hs := summable_conv_real_fiber ha hb (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) k
  have := tsum_of_norm_bounded ((hs.mul_left C).hasSum)
    (fun l => norm_kernel_apply_le hβ l (k - l) (a l) (b (k - l)))
  rwa [hs.tsum_mul_left] at this

lemma summable_norm_convFun (hβ : ∀ l m, ‖β l m‖ ≤ C) (ha : Summable fun l => ‖a l‖)
    (hb : Summable fun l => ‖b l‖) : Summable (fun k => ‖convFun β a b k‖) :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (norm_convFun_le hβ ha hb)
    ((summable_conv_real_sum ha hb (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).mul_left C)

lemma tsum_norm_convFun_le (hβ : ∀ l m, ‖β l m‖ ≤ C) (ha : Summable fun l => ‖a l‖)
    (hb : Summable fun l => ‖b l‖) :
    ∑' k, ‖convFun β a b k‖ ≤ C * ((∑' l, ‖a l‖) * ∑' l, ‖b l‖) := by
  have hs := summable_conv_real_sum ha hb (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
  have h1 := (summable_norm_convFun hβ ha hb).tsum_le_tsum (norm_convFun_le hβ ha hb)
    (hs.mul_left C)
  rw [hs.tsum_mul_left,
    tsum_conv_real ha hb (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)] at h1
  exact h1

/-- Naturality of the kernel convolution under a symmetry of the coefficients. -/
lemma convFun_twist (θ : ι ≃+ ι) (U₁ : ι → F₁ → F₁) (U₂ : ι → F₂ → F₂)
    (U₃ : ι → F₃ →L[ℝ] F₃)
    (h : ∀ l m x y, β l m (U₁ l x) (U₂ m y) = U₃ (l + m) (β (θ l) (θ m) x y))
    (hsum : ∀ k, Summable fun l => β l (k - l) (a l) (b (k - l))) (k : ι) :
    convFun β (fun k => U₁ k (a (θ k))) (fun k => U₂ k (b (θ k))) k
      = U₃ k (convFun β a b (θ k)) := by
  unfold convFun
  rw [(U₃ k).map_tsum (hsum (θ k)),
    ← θ.toEquiv.tsum_eq (fun l' => U₃ k (β l' (θ k - l') (a l') (b (θ k - l'))))]
  refine tsum_congr fun l => ?_
  rw [h]
  simp

end conv

/-! ### Packaging in `ℓ¹` -/

/-- The Banach space `ℓ¹(ι; F)`. -/
abbrev L1 (ι : Type*) (F : Type*) [NormedAddCommGroup F] : Type _ := lp (fun _ : ι => F) 1

namespace L1

lemma summable_norm (f : L1 ι F) : Summable fun k => ‖f k‖ := by
  have := (lp.memℓp f).summable (by simp)
  simpa using this

lemma norm_eq (f : L1 ι F) : ‖f‖ = ∑' k, ‖f k‖ := by
  rw [lp.norm_eq_tsum_rpow (by simp) f]
  simp

/-- An element of `ℓ¹` from a norm-summable family. -/
def mk (a : ι → F) (h : Summable fun k => ‖a k‖) : L1 ι F :=
  ⟨a, memℓp_gen (by simpa using h)⟩

@[simp] lemma mk_apply (a : ι → F) (h : Summable fun k => ‖a k‖) (k : ι) : mk a h k = a k := rfl

lemma ext' {f g : L1 ι F} (h : ∀ k, f k = g k) : f = g := lp.ext (funext h)

end L1

section kconv

variable [CompleteSpace F₃]

/-- **Young's inequality.**  A kernel convolution with a bounded kernel is a bounded bilinear
map `ℓ¹ × ℓ¹ → ℓ¹`. -/
noncomputable def kconv (β : ι → ι → F₁ →L[ℝ] F₂ →L[ℝ] F₃) (C : ℝ) (hβ : ∀ l m, ‖β l m‖ ≤ C) :
    L1 ι F₁ →L[ℝ] L1 ι F₂ →L[ℝ] L1 ι F₃ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ
      (fun a b => L1.mk (convFun β a b) (summable_norm_convFun hβ a.summable_norm b.summable_norm))
      (fun a a' b => by
        refine L1.ext' fun k => ?_
        simp only [L1.mk_apply, lp.coeFn_add, Pi.add_apply, convFun, map_add,
          ContinuousLinearMap.add_apply]
        exact (summable_convFun_term hβ a.summable_norm b.summable_norm k).tsum_add
          (summable_convFun_term hβ a'.summable_norm b.summable_norm k))
      (fun c a b => by
        refine L1.ext' fun k => ?_
        simp only [L1.mk_apply, lp.coeFn_smul, Pi.smul_apply, convFun, map_smul,
          ContinuousLinearMap.smul_apply]
        exact (summable_convFun_term hβ a.summable_norm b.summable_norm k).tsum_const_smul c)
      (fun a b b' => by
        refine L1.ext' fun k => ?_
        simp only [L1.mk_apply, lp.coeFn_add, Pi.add_apply, convFun, map_add]
        exact (summable_convFun_term hβ a.summable_norm b.summable_norm k).tsum_add
          (summable_convFun_term hβ a.summable_norm b'.summable_norm k))
      (fun c a b => by
        refine L1.ext' fun k => ?_
        simp only [L1.mk_apply, lp.coeFn_smul, Pi.smul_apply, convFun, map_smul]
        exact (summable_convFun_term hβ a.summable_norm b.summable_norm k).tsum_const_smul c))
    C
    (fun a b => by
      simp only [LinearMap.mk₂_apply, L1.norm_eq, L1.mk_apply]
      have := tsum_norm_convFun_le hβ a.summable_norm b.summable_norm
      linarith)

@[simp] lemma kconv_apply (β : ι → ι → F₁ →L[ℝ] F₂ →L[ℝ] F₃) (C : ℝ)
    (hβ : ∀ l m, ‖β l m‖ ≤ C) (a : L1 ι F₁) (b : L1 ι F₂) (k : ι) :
    kconv β C hβ a b k = convFun β a b k := rfl

end kconv

/-! ### Weights -/

section weight

variable (W : ι → ℝ)

/-- The coefficient family represented by `b : ℓ¹` for the weight `W`. -/
noncomputable def tc (b : L1 ι F) (k : ι) : F := (W k)⁻¹ • b k

variable {W} (hW : ∀ k, 0 < W k)
include hW

lemma smul_tc (b : L1 ι F) (k : ι) : W k • tc W b k = b k := by
  simp [tc, smul_smul, (hW k).ne']

lemma norm_tc (b : L1 ι F) (k : ι) : W k * ‖tc W b k‖ = ‖b k‖ := by
  have h := congrArg norm (smul_tc hW b k)
  rwa [norm_smul, Real.norm_of_nonneg (hW k).le] at h

lemma summable_tc (b : L1 ι F) : Summable fun k => W k * ‖tc W b k‖ := by
  simpa only [norm_tc hW] using b.summable_norm

lemma norm_eq_tc (b : L1 ι F) : ‖b‖ = ∑' k, W k * ‖tc W b k‖ := by
  simp only [norm_tc hW, L1.norm_eq]

lemma ext_tc {a b : L1 ι F} (h : ∀ k, tc W a k = tc W b k) : a = b := by
  refine L1.ext' fun k => ?_
  rw [← smul_tc hW a k, ← smul_tc hW b k, h]

lemma tc_add (a b : L1 ι F) (k : ι) : tc W (a + b) k = tc W a k + tc W b k := by
  simp [tc]

lemma tc_smul (c : ℝ) (a : L1 ι F) (k : ι) : tc W (c • a) k = c • tc W a k := by
  simp only [tc, lp.coeFn_smul, Pi.smul_apply]
  exact smul_comm _ _ _

/-- The element of `ℓ¹` with given coefficient family. -/
noncomputable def ofTc (a : ι → F) (h : Summable fun k => W k * ‖a k‖) : L1 ι F :=
  L1.mk (fun k => W k • a k) (by
    simpa only [norm_smul, Real.norm_of_nonneg (hW _).le] using h)

lemma tc_ofTc (a : ι → F) (h : Summable fun k => W k * ‖a k‖) (k : ι) :
    tc W (ofTc hW a h) k = a k := by
  simp [tc, ofTc, smul_smul, (hW k).ne']

variable [CompleteSpace F₃]

/-- The stored kernel of a weighted kernel convolution. -/
noncomputable def wkernel (W : ι → ℝ) (β : ι → ι → F₁ →L[ℝ] F₂ →L[ℝ] F₃) (l m : ι) :
    F₁ →L[ℝ] F₂ →L[ℝ] F₃ :=
  (W (l + m) / (W l * W m)) • β l m

omit [CompleteSpace F₃] in
lemma norm_wkernel_le {β : ι → ι → F₁ →L[ℝ] F₂ →L[ℝ] F₃} {C : ℝ}
    (hβ : ∀ l m, ‖β l m‖ * W (l + m) ≤ C * (W l * W m)) (l m : ι) :
    ‖wkernel W β l m‖ ≤ C := by
  have h1 : 0 < W l * W m := mul_pos (hW l) (hW m)
  have hc : 0 ≤ W (l + m) / (W l * W m) := div_nonneg (hW _).le h1.le
  calc ‖wkernel W β l m‖ ≤ W (l + m) / (W l * W m) * ‖β l m‖ := by
        unfold wkernel
        refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
        refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y => ?_
        simp only [ContinuousLinearMap.smul_apply]
        rw [norm_smul, Real.norm_of_nonneg hc]
        have := mul_le_mul_of_nonneg_left ((β l m).le_opNorm₂ x y) hc
        calc W (l + m) / (W l * W m) * ‖β l m x y‖
            ≤ W (l + m) / (W l * W m) * (‖β l m‖ * ‖x‖ * ‖y‖) := this
          _ = W (l + m) / (W l * W m) * ‖β l m‖ * ‖x‖ * ‖y‖ := by ring
    _ ≤ C := by
        rw [div_mul_eq_mul_div, div_le_iff₀ h1, mul_comm]
        exact hβ l m

/-- **Weighted Young's inequality.**  If `‖β l m‖ * W (l + m) ≤ C * (W l * W m)` then the
kernel convolution is a bounded bilinear map of the weighted `ℓ¹` spaces. -/
noncomputable def wconv (β : ι → ι → F₁ →L[ℝ] F₂ →L[ℝ] F₃) (C : ℝ)
    (hβ : ∀ l m, ‖β l m‖ * W (l + m) ≤ C * (W l * W m)) :
    L1 ι F₁ →L[ℝ] L1 ι F₂ →L[ℝ] L1 ι F₃ :=
  kconv (wkernel W β) C (norm_wkernel_le hW hβ)

omit [CompleteSpace F₃] in
lemma wkernel_term (β : ι → ι → F₁ →L[ℝ] F₂ →L[ℝ] F₃) (a : L1 ι F₁) (b : L1 ι F₂) (k l : ι) :
    β l (k - l) (tc W a l) (tc W b (k - l))
      = (W k)⁻¹ • wkernel W β l (k - l) (a l) (b (k - l)) := by
  have h1 := (hW l).ne'
  have h2 := (hW (k - l)).ne'
  have h3 := (hW k).ne'
  simp only [tc, wkernel, map_smul, ContinuousLinearMap.smul_apply, smul_smul,
    add_sub_cancel]
  congr 1
  field_simp

lemma summable_convFun_tc {β : ι → ι → F₁ →L[ℝ] F₂ →L[ℝ] F₃} {C : ℝ}
    (hβ : ∀ l m, ‖β l m‖ * W (l + m) ≤ C * (W l * W m)) (a : L1 ι F₁) (b : L1 ι F₂) (k : ι) :
    Summable fun l => β l (k - l) (tc W a l) (tc W b (k - l)) := by
  simp only [wkernel_term hW]
  exact (summable_convFun_term (norm_wkernel_le hW hβ) a.summable_norm b.summable_norm
    k).const_smul _

lemma tc_wconv {β : ι → ι → F₁ →L[ℝ] F₂ →L[ℝ] F₃} {C : ℝ}
    (hβ : ∀ l m, ‖β l m‖ * W (l + m) ≤ C * (W l * W m)) (a : L1 ι F₁) (b : L1 ι F₂) (k : ι) :
    tc W (wconv hW β C hβ a b) k = convFun β (tc W a) (tc W b) k := by
  simp only [tc, wconv, kconv_apply, convFun]
  rw [← tsum_const_smul'']
  refine tsum_congr fun l => ?_
  exact (wkernel_term hW β a b k l).symm

end weight

/-! ### Symmetries -/

section twist

/-- A symmetry acting on coefficient families: `(twist θ U b) k = U k (b (θ k))`. -/
noncomputable def twist (θ : ι ≃+ ι) (U : ι → F →ₗᵢ[ℝ] F) (b : L1 ι F) : L1 ι F :=
  L1.mk (fun k => U k (b (θ k))) (by
    simp only [LinearIsometry.norm_map]
    exact (θ.toEquiv.summable_iff (f := fun k => ‖b k‖)).mpr b.summable_norm)

@[simp] lemma twist_apply (θ : ι ≃+ ι) (U : ι → F →ₗᵢ[ℝ] F) (b : L1 ι F) (k : ι) :
    twist θ U b k = U k (b (θ k)) := rfl

lemma norm_twist (θ : ι ≃+ ι) (U : ι → F →ₗᵢ[ℝ] F) (b : L1 ι F) : ‖twist θ U b‖ = ‖b‖ := by
  simp only [L1.norm_eq, twist_apply, LinearIsometry.norm_map]
  exact θ.toEquiv.tsum_eq (fun k => ‖b k‖)

lemma twist_add (θ : ι ≃+ ι) (U : ι → F →ₗᵢ[ℝ] F) (a b : L1 ι F) :
    twist θ U (a + b) = twist θ U a + twist θ U b :=
  L1.ext' fun k => by simp

lemma twist_smul (θ : ι ≃+ ι) (U : ι → F →ₗᵢ[ℝ] F) (c : ℝ) (a : L1 ι F) :
    twist θ U (c • a) = c • twist θ U a :=
  L1.ext' fun k => by simp

lemma twist_neg (θ : ι ≃+ ι) (U : ι → F →ₗᵢ[ℝ] F) (a : L1 ι F) :
    twist θ U (-a) = -twist θ U a :=
  L1.ext' fun k => by simp

lemma tc_twist {W : ι → ℝ} (θ : ι ≃+ ι) (hθ : ∀ k, W (θ k) = W k) (U : ι → F →ₗᵢ[ℝ] F)
    (b : L1 ι F) (k : ι) : tc W (twist θ U b) k = U k (tc W b (θ k)) := by
  simp [tc, hθ]

variable [CompleteSpace F₃] {W : ι → ℝ}

/-- Naturality of the weighted kernel convolution. -/
lemma wconv_twist (hW : ∀ k, 0 < W k) {β : ι → ι → F₁ →L[ℝ] F₂ →L[ℝ] F₃} {C : ℝ}
    (hβ : ∀ l m, ‖β l m‖ * W (l + m) ≤ C * (W l * W m))
    (θ : ι ≃+ ι) (hθ : ∀ k, W (θ k) = W k)
    (U₁ : ι → F₁ →ₗᵢ[ℝ] F₁) (U₂ : ι → F₂ →ₗᵢ[ℝ] F₂) (U₃ : ι → F₃ →ₗᵢ[ℝ] F₃)
    (h : ∀ l m x y, β l m (U₁ l x) (U₂ m y) = U₃ (l + m) (β (θ l) (θ m) x y))
    (a : L1 ι F₁) (b : L1 ι F₂) :
    wconv hW β C hβ (twist θ U₁ a) (twist θ U₂ b) = twist θ U₃ (wconv hW β C hβ a b) := by
  refine ext_tc hW fun k => ?_
  rw [tc_wconv hW, tc_twist θ hθ, tc_wconv hW]
  have := convFun_twist (β := β) (a := tc W a) (b := tc W b) θ (fun k => U₁ k) (fun k => U₂ k)
    (fun k => (U₃ k).toContinuousLinearMap) h (summable_convFun_tc hW hβ a b) k
  simp only [LinearIsometry.coe_toContinuousLinearMap] at this
  rw [← this]
  congr 1 <;> funext j <;> exact tc_twist θ hθ _ _ j

end twist

end EquivEmbed.Torus
