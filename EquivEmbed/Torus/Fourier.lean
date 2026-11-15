/-
Copyright (c) 2026 Roger Schlafly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roger Schlafly
-/
module

public import EquivEmbed.Torus.Operators
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.FDeriv.Bilinear

/-!
# Absolutely convergent Fourier series on the torus `ℝⁿ / 2π ℤⁿ`

For a coefficient family `a : Freq n → F` we put `fsum a x = ∑' k, exp(i k·x) • a k`.

* `hasFDerivAt_fsum`, `pd_fsum`: termwise differentiation; the partial derivative `∂_p`
  multiplies the `k`-th coefficient by `i k_p`.
* `fsum_conv`: the Fourier series of a convolution is the product of the Fourier series.
* `fsum_translate`, `fsum_conj`: symmetries of the coefficients give symmetries of the function.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace EquivEmbed.Torus

variable {n : ℕ}

/-- The linear form `x ↦ i k·x`. -/
noncomputable def lin (k : Freq n) : (Fin n → ℝ) →L[ℝ] ℂ :=
  ∑ p, (Complex.I * (k p : ℂ)) •
    (Complex.ofRealCLM.comp (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) p))

lemma lin_apply (k : Freq n) (x : Fin n → ℝ) :
    lin k x = Complex.I * ∑ p, (k p : ℂ) * (x p : ℂ) := by
  simp [lin, Finset.mul_sum, mul_assoc]

lemma lin_add (l m : Freq n) : lin (l + m) = lin l + lin m := by
  ext x
  simp [lin_apply, add_mul, Finset.sum_add_distrib, mul_add]

lemma lin_neg (k : Freq n) (x : Fin n → ℝ) : lin (-k) x = starRingEnd ℂ (lin k x) := by
  simp [lin_apply, Finset.mul_sum]

lemma ef_eq (k : Freq n) (x : Fin n → ℝ) : ef k x = Complex.exp (lin k x) := by
  rw [ef, lin_apply]

lemma norm_ef (k : Freq n) (x : Fin n → ℝ) : ‖ef k x‖ = 1 := by
  have h : lin k x = ((∑ p, (k p : ℝ) * x p : ℝ) : ℂ) * Complex.I := by
    rw [lin_apply]
    push_cast
    ring
  rw [ef_eq, h]
  exact Complex.norm_exp_ofReal_mul_I _

lemma ef_add_freq (l m : Freq n) (x : Fin n → ℝ) : ef (l + m) x = ef l x * ef m x := by
  simp [ef_eq, lin_add, Complex.exp_add]

lemma ef_add_pt (k : Freq n) (x y : Fin n → ℝ) : ef k (x + y) = ef k x * ef k y := by
  simp [ef_eq, Complex.exp_add]

lemma ef_neg_freq (k : Freq n) (x : Fin n → ℝ) : ef (-k) x = starRingEnd ℂ (ef k x) := by
  rw [ef_eq, ef_eq, lin_neg, ← Complex.exp_conj]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

section basic

variable {a b : Freq n → F}

lemma summable_ef_smul (ha : Summable fun k => ‖a k‖) (x : Fin n → ℝ) :
    Summable fun k => ef k x • a k :=
  Summable.of_norm (by simpa [norm_smul, norm_ef] using ha)

lemma fsum_add (ha : Summable fun k => ‖a k‖) (hb : Summable fun k => ‖b k‖) (x : Fin n → ℝ) :
    fsum (fun k => a k + b k) x = fsum a x + fsum b x := by
  simp only [fsum, smul_add]
  exact (summable_ef_smul ha x).tsum_add (summable_ef_smul hb x)

lemma fsum_smul (c : ℂ) (a : Freq n → F) (x : Fin n → ℝ) :
    fsum (fun k => c • a k) x = c • fsum a x := by
  simp only [fsum, smul_comm _ c]
  exact tsum_const_smul'' c

lemma fsum_real_smul (c : ℝ) (a : Freq n → F) (x : Fin n → ℝ) :
    fsum (fun k => c • a k) x = c • fsum a x := by
  simp only [fsum, smul_comm _ c]
  exact tsum_const_smul'' c

lemma fsum_neg (a : Freq n → F) (x : Fin n → ℝ) : fsum (fun k => -a k) x = -fsum a x := by
  simp only [fsum, smul_neg]
  exact tsum_neg

lemma fsum_sum {ι' : Type*} (s : Finset ι') (f : ι' → Freq n → F)
    (h : ∀ i ∈ s, Summable fun k => ‖f i k‖) (x : Fin n → ℝ) :
    fsum (fun k => ∑ i ∈ s, f i k) x = ∑ i ∈ s, fsum (f i) x := by
  simp only [fsum, Finset.smul_sum]
  exact Summable.tsum_finsetSum fun i hi => summable_ef_smul (h i hi) x

end basic

/-! ### Differentiation -/

/-- `|k|₁`. -/
def N1 (k : Freq n) : ℝ := ∑ p, |(k p : ℝ)|

lemma N1_nonneg (k : Freq n) : 0 ≤ N1 k := Finset.sum_nonneg fun _ _ => abs_nonneg _

lemma N1_le (k : Freq n) : N1 k ≤ n * W k := by
  calc N1 k ≤ ∑ _p : Fin n, W k :=
        Finset.sum_le_sum fun p _ => (abs_coord_le k p).trans (sq_le_W k)
    _ = n * W k := by simp

lemma N1_mul_le (k : Freq n) (p : Fin n) : N1 k * |(k p : ℝ)| ≤ n * W k := by
  rw [N1, Finset.sum_mul]
  calc ∑ q, |(k q : ℝ)| * |(k p : ℝ)| ≤ ∑ _q : Fin n, W k :=
        Finset.sum_le_sum fun q _ => by
          rw [← abs_mul]
          exact (abs_coord_mul_le k q p).trans (sq_le_W k)
    _ = n * W k := by simp

lemma norm_lin_le (k : Freq n) : ‖lin k‖ ≤ N1 k := by
  refine ContinuousLinearMap.opNorm_le_bound _ (N1_nonneg k) fun x => ?_
  rw [lin_apply, norm_mul, Complex.norm_I, one_mul, N1, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
  rw [norm_mul, Complex.norm_intCast, Complex.norm_real]
  exact mul_le_mul_of_nonneg_left (norm_le_pi_norm x p) (abs_nonneg _)

/-- Multiplication of the coefficients by `i k_p`: the coefficients of `∂_p`. -/
noncomputable def dc (p : Fin n) (a : Freq n → F) (k : Freq n) : F :=
  (Complex.I * (k p : ℂ)) • a k

lemma norm_dc (p : Fin n) (a : Freq n → F) (k : Freq n) : ‖dc p a k‖ = |(k p : ℝ)| * ‖a k‖ := by
  simp [dc, norm_smul]

lemma norm_term_le (a : Freq n → F) (k : Freq n) (x : Fin n → ℝ) :
    ‖(ef k x • lin k).smulRight (a k)‖ ≤ N1 k * ‖a k‖ := by
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (N1_nonneg k) (norm_nonneg _))
    fun y => ?_
  rw [ContinuousLinearMap.smulRight_apply, norm_smul, ContinuousLinearMap.smul_apply, norm_smul,
    norm_ef, one_mul]
  have h1 := ((lin k).le_opNorm y).trans
    (mul_le_mul_of_nonneg_right (norm_lin_le k) (norm_nonneg _))
  calc ‖lin k y‖ * ‖a k‖ ≤ (N1 k * ‖y‖) * ‖a k‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = N1 k * ‖a k‖ * ‖y‖ := by ring

/-- Termwise differentiation of an absolutely convergent Fourier series. -/
theorem hasFDerivAt_fsum (a : Freq n → F) (h0 : Summable fun k => ‖a k‖)
    (h1 : Summable fun k => N1 k * ‖a k‖) (x : Fin n → ℝ) :
    HasFDerivAt (fsum a) (∑' k, (ef k x • lin k).smulRight (a k)) x := by
  have key := hasFDerivAt_tsum (u := fun k => N1 k * ‖a k‖)
    (f := fun k y => Complex.exp (lin k y) • a k)
    (f' := fun k y => (Complex.exp (lin k y) • lin k).smulRight (a k)) h1
    (fun k y => ((lin k).hasFDerivAt.cexp).smul_const (a k))
    (fun k y => by
      rw [← ef_eq]
      exact norm_term_le a k y) (x₀ := 0)
    (by
      have := summable_ef_smul h0 (0 : Fin n → ℝ)
      simpa only [ef_eq] using this) x
  have e : fsum a = fun y => ∑' k, Complex.exp (lin k y) • a k := by
    funext y
    simp only [fsum, ef_eq]
  rw [e]
  simp only [ef_eq]
  exact key

lemma lin_single (k : Freq n) (p : Fin n) :
    lin k (Pi.single p 1) = Complex.I * (k p : ℂ) := by
  rw [lin_apply, Finset.sum_eq_single p]
  · simp
  · intro q _ hq
    simp [Pi.single_apply, hq]
  · intro h
    exact absurd (Finset.mem_univ p) h

/-- The partial derivative of a Fourier series: `∂_p` multiplies coefficients by `i k_p`. -/
theorem pd_fsum (a : Freq n → F) (h0 : Summable fun k => ‖a k‖)
    (h1 : Summable fun k => N1 k * ‖a k‖) (p : Fin n) (x : Fin n → ℝ) :
    pd p (fsum a) x = fsum (dc p a) x := by
  have hs : Summable fun k => (ef k x • lin k).smulRight (a k) :=
    Summable.of_norm_bounded h1 (fun k => norm_term_le a k x)
  rw [pd, (hasFDerivAt_fsum a h0 h1 x).fderiv]
  have := (ContinuousLinearMap.apply ℝ F (Pi.single p (1 : ℝ))).map_tsum hs
  simp only [ContinuousLinearMap.apply_apply] at this
  rw [this, fsum]
  refine tsum_congr fun k => ?_
  simp [dc, lin_single, mul_smul]

/-- Summability facts for a family in the weighted space. -/
lemma summable_of_W {a : Freq n → F} (h : Summable fun k => W k * ‖a k‖) :
    Summable fun k => ‖a k‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun k => le_mul_of_one_le_left (norm_nonneg _) (one_le_W k)) h

lemma summable_N1_of_W {a : Freq n → F} (h : Summable fun k => W k * ‖a k‖) :
    Summable fun k => N1 k * ‖a k‖ :=
  Summable.of_nonneg_of_le (f := fun k => (n : ℝ) * (W k * ‖a k‖))
    (fun k => mul_nonneg (N1_nonneg k) (norm_nonneg _))
    (fun k => by
      have := mul_le_mul_of_nonneg_right (N1_le k) (norm_nonneg (a k))
      rwa [mul_assoc] at this)
    (h.mul_left (n : ℝ))

lemma summable_dc_of_W {a : Freq n → F} (h : Summable fun k => W k * ‖a k‖) (p : Fin n) :
    Summable fun k => ‖dc p a k‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun k => by
      rw [norm_dc]
      exact mul_le_mul_of_nonneg_right ((abs_coord_le k p).trans (sq_le_W k)) (norm_nonneg _)) h

lemma summable_N1_dc_of_W {a : Freq n → F} (h : Summable fun k => W k * ‖a k‖) (p : Fin n) :
    Summable fun k => N1 k * ‖dc p a k‖ :=
  Summable.of_nonneg_of_le (f := fun k => (n : ℝ) * (W k * ‖a k‖))
    (fun k => mul_nonneg (N1_nonneg k) (norm_nonneg _))
    (fun k => by
      rw [norm_dc, ← mul_assoc]
      have := mul_le_mul_of_nonneg_right (N1_mul_le k p) (norm_nonneg (a k))
      linarith [mul_assoc (n : ℝ) (W k) ‖a k‖])
    (h.mul_left (n : ℝ))

lemma summable_dc_dc_of_W {a : Freq n → F} (h : Summable fun k => W k * ‖a k‖) (p q : Fin n) :
    Summable fun k => ‖dc q (dc p a) k‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun k => by
      rw [norm_dc, norm_dc, ← mul_assoc, ← abs_mul]
      exact mul_le_mul_of_nonneg_right ((abs_coord_mul_le k q p).trans (sq_le_W k))
        (norm_nonneg _)) h

/-- First derivatives of a Fourier series in the weighted space. -/
lemma pd_fsum_of_W {a : Freq n → F} (h : Summable fun k => W k * ‖a k‖) (p : Fin n) :
    pd p (fsum a) = fsum (dc p a) :=
  funext fun x => pd_fsum a (summable_of_W h) (summable_N1_of_W h) p x

/-- Second derivatives of a Fourier series in the weighted space. -/
lemma pd_pd_fsum_of_W {a : Freq n → F} (h : Summable fun k => W k * ‖a k‖) (p q : Fin n) :
    pd q (pd p (fsum a)) = fsum (dc q (dc p a)) := by
  rw [pd_fsum_of_W h p]
  exact funext fun x => pd_fsum _ (summable_dc_of_W h p) (summable_N1_dc_of_W h p) q x

/-! ### Products -/

section product

variable {F₁ F₂ F₃ : Type*}
  [NormedAddCommGroup F₁] [NormedSpace ℂ F₁] [CompleteSpace F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℂ F₂] [CompleteSpace F₂]
  [NormedAddCommGroup F₃] [NormedSpace ℂ F₃] [CompleteSpace F₃]

lemma tsum_convFun_const (β₀ : F₁ →L[ℝ] F₂ →L[ℝ] F₃) (a : Freq n → F₁) (b : Freq n → F₂)
    (ha : Summable fun k => ‖a k‖) (hb : Summable fun k => ‖b k‖) :
    ∑' k, convFun (fun _ _ => β₀) a b k = β₀ (∑' l, a l) (∑' m, b m) := by
  let H : Freq n × Freq n → F₃ := fun z => β₀ (a z.1) (b z.2)
  have hH : Summable H := by
    refine Summable.of_norm_bounded
      ((ha.mul_of_nonneg hb (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)).mul_left ‖β₀‖)
      fun z => ?_
    have := β₀.le_opNorm₂ (a z.1) (b z.2)
    linarith [mul_assoc ‖β₀‖ ‖a z.1‖ ‖b z.2‖]
  have hH' : Summable (H ∘ shearEquiv (Freq n)) := (shearEquiv (Freq n)).summable_iff.mpr hH
  calc ∑' k, convFun (fun _ _ => β₀) a b k
      = ∑' k, ∑' l, (H ∘ shearEquiv (Freq n)) (k, l) := rfl
    _ = ∑' p, (H ∘ shearEquiv (Freq n)) p := (hH'.tsum_prod).symm
    _ = ∑' z, H z := (shearEquiv (Freq n)).tsum_eq H
    _ = ∑' l, ∑' m, β₀ (a l) (b m) := hH.tsum_prod
    _ = ∑' l, β₀ (a l) (∑' m, b m) :=
        tsum_congr fun l => ((β₀ (a l)).map_tsum hb.of_norm).symm
    _ = β₀ (∑' l, a l) (∑' m, b m) := ((β₀.flip (∑' m, b m)).map_tsum ha.of_norm).symm

/-- The Fourier series of a convolution is the product of the Fourier series. -/
theorem fsum_conv (β₀ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (hβ : ∀ (c d : ℂ) x y, β₀ (c • x) (d • y) = (c * d) • β₀ x y)
    (a : Freq n → F₁) (b : Freq n → F₂)
    (ha : Summable fun k => ‖a k‖) (hb : Summable fun k => ‖b k‖) (x : Fin n → ℝ) :
    fsum (convFun (fun _ _ => β₀) a b) x = β₀ (fsum a x) (fsum b x) := by
  have key : ∀ k, ef k x • convFun (fun _ _ => β₀) a b k
      = convFun (fun _ _ => β₀) (fun l => ef l x • a l) (fun l => ef l x • b l) k := by
    intro k
    unfold convFun
    rw [← tsum_const_smul'']
    refine tsum_congr fun l => ?_
    rw [hβ, ← ef_add_freq, add_sub_cancel]
  simp only [fsum, key]
  exact tsum_convFun_const β₀ _ _ (by simpa [norm_smul, norm_ef] using ha)
    (by simpa [norm_smul, norm_ef] using hb)

end product

/-! ### Symmetries -/

/-- If the coefficients satisfy `exp(-i k·t) • R (a k) = a k`, then `f (x + t) = R (f x)`. -/
theorem fsum_translate (R : F →L[ℂ] F) (t : Fin n → ℝ) (a : Freq n → F)
    (ha : Summable fun k => ‖a k‖) (h : ∀ k, ef k (-t) • R (a k) = a k) (x : Fin n → ℝ) :
    fsum a (x + t) = R (fsum a x) := by
  rw [fsum, fsum, R.map_tsum (summable_ef_smul ha x)]
  refine tsum_congr fun k => ?_
  conv_lhs => rw [← h k]
  rw [smul_smul, ← ef_add_pt, add_neg_cancel_right, map_smul]

/-- If the coefficients satisfy `conj (a (-k)) = a k`, the function is real. -/
theorem fsum_conj (cF : F →L[ℝ] F) (hc : ∀ (z : ℂ) (y : F), cF (z • y) = starRingEnd ℂ z • cF y)
    (a : Freq n → F) (ha : Summable fun k => ‖a k‖) (h : ∀ k, cF (a (-k)) = a k)
    (x : Fin n → ℝ) : cF (fsum a x) = fsum a x := by
  rw [fsum, cF.map_tsum (summable_ef_smul ha x)]
  rw [← (Equiv.neg (Freq n)).tsum_eq (fun k => ef k x • a k)]
  refine tsum_congr fun k => ?_
  have h2 : cF (a k) = a (-k) := by
    have := h (-k)
    rwa [neg_neg] at this
  simp only [Equiv.neg_apply]
  rw [hc, h2, ef_neg_freq]

/-! ### The product rule -/

/-- The product rule for a bilinear form and partial derivatives. -/
lemma pd_dot (dot : F →L[ℂ] F →L[ℂ] ℂ) {f g : (Fin n → ℝ) → F}
    {f' g' : (Fin n → ℝ) →L[ℝ] F} {x : Fin n → ℝ} (hf : HasFDerivAt f f' x)
    (hg : HasFDerivAt g g' x) (p : Fin n) :
    pd p (fun y => dot (f y) (g y)) x
      = dot (f' (Pi.single p 1)) (g x) + dot (f x) (g' (Pi.single p 1)) := by
  have h := ((dotR dot).hasFDerivAt_of_bilinear hf hg).fderiv
  have h2 : (fun y => dot (f y) (g y)) = fun y => dotR dot (f y) (g y) := rfl
  rw [pd, h2, h]
  simp [add_comm]

end EquivEmbed.Torus
