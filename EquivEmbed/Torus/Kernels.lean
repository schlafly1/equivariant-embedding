/-
Copyright (c) 2026 Roger Schlafly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roger Schlafly
-/
module

public import EquivEmbed.Torus.Conv
public import EquivEmbed.Defs
public import Mathlib.Analysis.Complex.Basic

/-!
# Günther's operators on a flat torus, on Fourier coefficients

The frequency lattice is `Freq n = Fin n → ℤ` and the weight is `W k = 1 + |k|²`.  A map
`v : ℝⁿ/2πℤⁿ → F` is represented by its Fourier coefficients, an element of the weighted `ℓ¹`
space (a Wiener algebra with two derivatives).

In these coordinates

* `∂_p` multiplies the `k`-th coefficient by `i k_p`,
* `(Δ - 1)⁻¹` multiplies it by `-1 / (1 + |k|²)`,
* products of functions are convolutions.

So Günther's operators are kernel convolutions:

* `Sop j v w` is `(Δ - 1)⁻¹ ⟨Δ v, ∂_j w⟩`, with kernel `kS j`;
* `Top i j v w` is `(Δ - 1)⁻¹ (-2 ⟨Δ v, ∂_i ∂_j w⟩ + 2 ⟨∂_i ∂_p v, ∂_j ∂_p w⟩ - ⟨∂_i v, ∂_j w⟩)`,
  with kernel `kT i j`;
* `mulL y c` is the product of a vector valued and a scalar function.

No elliptic estimate is needed: the bounds are the elementary inequalities `norm_kS_le`,
`norm_kT_le` and `W_add_le` on the kernels.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace EquivEmbed.Torus

variable {n : ℕ}

/-- `l · m`. -/
def ip (l m : Freq n) : ℝ := ∑ p, (l p : ℝ) * (m p : ℝ)

lemma sq_nonneg' (k : Freq n) : 0 ≤ sq k := Finset.sum_nonneg fun _ _ => sq_nonneg _

lemma W_pos (k : Freq n) : 0 < W k := by
  have := sq_nonneg' k
  unfold W
  linarith

lemma sq_le_W (k : Freq n) : sq k ≤ W k := by
  unfold W
  linarith

lemma one_le_W (k : Freq n) : 1 ≤ W k := by
  have := sq_nonneg' k
  unfold W
  linarith

lemma sq_neg (k : Freq n) : sq (-k) = sq k := by simp [sq]

lemma W_neg (k : Freq n) : W (-k) = W k := by simp [W, sq_neg]

lemma sq_add (l m : Freq n) : sq (l + m) = sq l + 2 * ip l m + sq m := by
  simp only [sq, ip, Pi.add_apply, Int.cast_add, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun p _ => by ring

lemma sq_add_le (l m : Freq n) : sq (l + m) ≤ 2 * sq l + 2 * sq m := by
  simp only [sq, Pi.add_apply, Int.cast_add, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun p _ => by nlinarith [sq_nonneg ((l p : ℝ) - m p)]

lemma W_add_le (l m : Freq n) : W (l + m) ≤ 2 * (W l * W m) := by
  have := sq_add_le l m
  have h1 := sq_nonneg' l
  have h2 := sq_nonneg' m
  unfold W
  nlinarith [mul_nonneg h1 h2]

lemma coord_sq_le (k : Freq n) (p : Fin n) : (k p : ℝ) ^ 2 ≤ sq k :=
  Finset.single_le_sum (f := fun p => (k p : ℝ) ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ p)

lemma abs_coord_le (k : Freq n) (p : Fin n) : |(k p : ℝ)| ≤ sq k := by
  have h1 : |(k p : ℝ)| ≤ (k p : ℝ) ^ 2 := by
    have : |k p| ≤ (k p) ^ 2 := by
      have := Int.le_self_sq |k p|
      rwa [sq_abs] at this
    exact_mod_cast this
  exact h1.trans (coord_sq_le k p)

lemma abs_coord_mul_le (k : Freq n) (p q : Fin n) : |(k p : ℝ) * (k q : ℝ)| ≤ sq k := by
  have h1 := coord_sq_le k p
  have h2 := coord_sq_le k q
  rw [abs_le]
  constructor <;> nlinarith [sq_nonneg ((k p : ℝ) + k q), sq_nonneg ((k p : ℝ) - k q)]

lemma abs_coord_ip_le (l m : Freq n) (i j : Fin n) :
    |(l i : ℝ) * (m j : ℝ) * ip l m| ≤ n * (sq l * sq m) := by
  have h : (l i : ℝ) * (m j : ℝ) * ip l m
      = ∑ p, ((l i : ℝ) * (l p : ℝ)) * ((m j : ℝ) * (m p : ℝ)) := by
    simp only [ip, Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [h]
  calc |∑ p, ((l i : ℝ) * (l p : ℝ)) * ((m j : ℝ) * (m p : ℝ))|
      ≤ ∑ p, |((l i : ℝ) * (l p : ℝ)) * ((m j : ℝ) * (m p : ℝ))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _p : Fin n, sq l * sq m := Finset.sum_le_sum fun p _ => by
        rw [abs_mul]
        exact mul_le_mul (abs_coord_mul_le l i p) (abs_coord_mul_le m j p) (abs_nonneg _)
          (sq_nonneg' l)
    _ = n * (sq l * sq m) := by simp

/-! ### The kernels -/

/-- Real part of the kernel of `Sop j`. -/
noncomputable def rS (j : Fin n) (l m : Freq n) : ℝ := sq l * (m j : ℝ) / W (l + m)

/-- The kernel of `(Δ - 1)⁻¹ ⟨Δ v, ∂_j w⟩`. -/
noncomputable def kS (j : Fin n) (l m : Freq n) : ℂ := Complex.I * (rS j l m : ℝ)

/-- The kernel of `Top i j`. -/
noncomputable def rT (i j : Fin n) (l m : Freq n) : ℝ :=
  -(-2 * sq l * (m i : ℝ) * (m j : ℝ) + 2 * (l i : ℝ) * (m j : ℝ) * ip l m
      + (l i : ℝ) * (m j : ℝ)) / W (l + m)

/-- The kernel of `Top i j`, as a complex number. -/
noncomputable def kT (i j : Fin n) (l m : Freq n) : ℂ := (rT i j l m : ℝ)

lemma norm_kS_le (j : Fin n) (l m : Freq n) : ‖kS j l m‖ * W (l + m) ≤ 1 * (W l * W m) := by
  have hW := W_pos (l + m)
  have h1 : ‖kS j l m‖ = sq l * |(m j : ℝ)| / W (l + m) := by
    simp [kS, rS, abs_div, abs_mul, abs_of_nonneg (sq_nonneg' l), abs_of_pos hW]
  rw [h1, div_mul_cancel₀ _ hW.ne', one_mul]
  exact mul_le_mul (sq_le_W l) ((abs_coord_le m j).trans (sq_le_W m)) (abs_nonneg _)
    (W_pos l).le

lemma norm_kT_le (i j : Fin n) (l m : Freq n) :
    ‖kT i j l m‖ * W (l + m) ≤ (2 * n + 3) * (W l * W m) := by
  have hW := W_pos (l + m)
  have h1 : ‖kT i j l m‖ = |(-2 * sq l * (m i : ℝ) * (m j : ℝ) + 2 * (l i : ℝ) * (m j : ℝ) * ip l m
      + (l i : ℝ) * (m j : ℝ))| / W (l + m) := by
    rw [kT, Complex.norm_real, Real.norm_eq_abs, rT, abs_div, abs_neg, abs_of_pos hW]
  rw [h1, div_mul_cancel₀ _ hW.ne']
  have a1 := abs_coord_mul_le m i j
  have a2 := abs_coord_ip_le l m i j
  have a3 := abs_coord_le l i
  have a4 := abs_coord_le m j
  have s1 := sq_nonneg' l
  have s2 := sq_nonneg' m
  have w1 := sq_le_W l
  have w2 := sq_le_W m
  have e1 : |sq l * ((m i : ℝ) * (m j : ℝ))| ≤ sq l * sq m := by
    rw [abs_mul, abs_of_nonneg s1]
    exact mul_le_mul_of_nonneg_left a1 s1
  have e3 : |(l i : ℝ) * (m j : ℝ)| ≤ sq l * sq m := by
    rw [abs_mul]
    exact mul_le_mul a3 a4 (abs_nonneg _) s1
  have hsum : |(-2 * sq l * (m i : ℝ) * (m j : ℝ) + 2 * (l i : ℝ) * (m j : ℝ) * ip l m
      + (l i : ℝ) * (m j : ℝ))| ≤ (2 * n + 3) * (sq l * sq m) := by
    rw [abs_le] at e1 e3 a2 ⊢
    constructor <;> nlinarith [e1.1, e1.2, e3.1, e3.2, a2.1, a2.2]
  have hn : (0 : ℝ) ≤ 2 * n + 3 := by positivity
  calc _ ≤ (2 * n + 3) * (sq l * sq m) := hsum
    _ ≤ (2 * n + 3) * (W l * W m) :=
        mul_le_mul_of_nonneg_left (mul_le_mul w1 w2 s2 (W_pos l).le) hn

lemma norm_one_le (l m : Freq n) : ‖(1 : ℂ)‖ * W (l + m) ≤ 2 * (W l * W m) := by
  simpa using W_add_le l m

/-! ### Bilinear maps -/

variable {F F₁ F₂ F₃ : Type*}
  [NormedAddCommGroup F] [NormedSpace ℂ F]
  [NormedAddCommGroup F₁] [NormedSpace ℝ F₁]
  [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
  [NormedAddCommGroup F₃] [NormedSpace ℂ F₃]

/-- The bilinear map `(x, y) ↦ κ • β₀ x y`. -/
noncomputable def scaled (κ : ℂ) (β₀ : F₁ →L[ℝ] F₂ →L[ℝ] F₃) : F₁ →L[ℝ] F₂ →L[ℝ] F₃ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun x y => κ • β₀ x y)
      (fun x x' y => by simp [smul_add])
      (fun c x y => by simp [smul_comm κ c])
      (fun x y y' => by simp [smul_add])
      (fun c x y => by simp [smul_comm κ c]))
    (‖κ‖ * ‖β₀‖)
    (fun x y => by
      simp only [LinearMap.mk₂_apply]
      rw [norm_smul]
      calc ‖κ‖ * ‖β₀ x y‖ ≤ ‖κ‖ * (‖β₀‖ * ‖x‖ * ‖y‖) :=
            mul_le_mul_of_nonneg_left (β₀.le_opNorm₂ x y) (norm_nonneg _)
        _ = ‖κ‖ * ‖β₀‖ * ‖x‖ * ‖y‖ := by ring)

@[simp] lemma scaled_apply (κ : ℂ) (β₀ : F₁ →L[ℝ] F₂ →L[ℝ] F₃) (x : F₁) (y : F₂) :
    scaled κ β₀ x y = κ • β₀ x y := rfl

lemma norm_scaled_le (κ : ℂ) (β₀ : F₁ →L[ℝ] F₂ →L[ℝ] F₃) : ‖scaled κ β₀‖ ≤ ‖κ‖ * ‖β₀‖ :=
  LinearMap.mkContinuous₂_norm_le _ (by positivity) _

/-- A complex bilinear form, as a real bilinear map. -/
noncomputable def dotR (dot : F →L[ℂ] F →L[ℂ] ℂ) : F →L[ℝ] F →L[ℝ] ℂ :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun x y => dot x y)
      (fun x x' y => by simp)
      (fun c x y => by
        rw [← Complex.coe_smul c x, map_smul, ContinuousLinearMap.smul_apply, Complex.coe_smul])
      (fun x y y' => by simp)
      (fun c x y => by rw [← Complex.coe_smul c y, map_smul, Complex.coe_smul]))
    ‖dot‖ (fun x y => dot.le_opNorm₂ x y)

@[simp] lemma dotR_apply (dot : F →L[ℂ] F →L[ℂ] ℂ) (x y : F) : dotR dot x y = dot x y := rfl

/-- Scalar multiplication `(y, c) ↦ c • y`, as a real bilinear map. -/
noncomputable def smulR (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F] :
    F →L[ℝ] ℂ →L[ℝ] F :=
  LinearMap.mkContinuous₂
    (LinearMap.mk₂ ℝ (fun (y : F) (c : ℂ) => c • y)
      (fun x x' c => by simp [smul_add])
      (fun c' x c => by simp [smul_comm c c'])
      (fun x c c' => by simp [add_smul])
      (fun c' x c => by
        show (c' • c) • x = c' • c • x
        exact smul_assoc c' c x))
    1 (fun y c => by
      simp only [LinearMap.mk₂_apply]
      rw [norm_smul]
      linarith [mul_comm ‖c‖ ‖y‖])

@[simp] lemma smulR_apply (y : F) (c : ℂ) : smulR F y c = c • y := rfl

/-! ### Scalar kernel convolutions -/

section sconv

variable [CompleteSpace F₃]

/-- The kernel convolution with scalar kernel `κ` and bilinear map `β₀`, on the weighted
spaces. -/
noncomputable def sconv (κ : Freq n → Freq n → ℂ) (C₀ : ℝ)
    (hκ : ∀ l m, ‖κ l m‖ * W (l + m) ≤ C₀ * (W l * W m)) (β₀ : F₁ →L[ℝ] F₂ →L[ℝ] F₃) :
    L1 (Freq n) F₁ →L[ℝ] L1 (Freq n) F₂ →L[ℝ] L1 (Freq n) F₃ :=
  wconv W_pos (fun l m => scaled (κ l m) β₀) (C₀ * ‖β₀‖) (fun l m => by
    have h1 := norm_scaled_le (κ l m) β₀
    have hW := (W_pos (l + m)).le
    calc ‖scaled (κ l m) β₀‖ * W (l + m) ≤ ‖κ l m‖ * ‖β₀‖ * W (l + m) :=
          mul_le_mul_of_nonneg_right h1 hW
      _ = ‖κ l m‖ * W (l + m) * ‖β₀‖ := by ring
      _ ≤ C₀ * (W l * W m) * ‖β₀‖ := mul_le_mul_of_nonneg_right (hκ l m) (norm_nonneg β₀)
      _ = C₀ * ‖β₀‖ * (W l * W m) := by ring)

lemma tc_sconv (κ : Freq n → Freq n → ℂ) (C₀ : ℝ)
    (hκ : ∀ l m, ‖κ l m‖ * W (l + m) ≤ C₀ * (W l * W m)) (β₀ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (a : L1 (Freq n) F₁) (b : L1 (Freq n) F₂) (k : Freq n) :
    tc W (sconv κ C₀ hκ β₀ a b) k = ∑' l, κ l (k - l) • β₀ (tc W a l) (tc W b (k - l)) := by
  unfold sconv
  rw [tc_wconv W_pos]
  rfl

/-- Summability of the fibres of a kernel convolution, for a kernel of size `W l * W m`. -/
lemma summable_fiber (κ : Freq n → Freq n → ℂ) (C₀ : ℝ)
    (hκ : ∀ l m, ‖κ l m‖ ≤ C₀ * (W l * W m)) (β₀ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (a : L1 (Freq n) F₁) (b : L1 (Freq n) F₂) (k : Freq n) :
    Summable fun l => κ l (k - l) • β₀ (tc W a l) (tc W b (k - l)) := by
  have hs := summable_conv_real_fiber a.summable_norm b.summable_norm
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) k
  refine Summable.of_norm_bounded (hs.mul_left (C₀ * ‖β₀‖)) fun l => ?_
  rw [norm_smul, ← norm_tc W_pos a l, ← norm_tc W_pos b (k - l)]
  have h1 := β₀.le_opNorm₂ (tc W a l) (tc W b (k - l))
  have h2 := hκ l (k - l)
  have h0 : 0 ≤ ‖β₀‖ * ‖tc W a l‖ * ‖tc W b (k - l)‖ := by positivity
  calc ‖κ l (k - l)‖ * ‖β₀ (tc W a l) (tc W b (k - l))‖
      ≤ ‖κ l (k - l)‖ * (‖β₀‖ * ‖tc W a l‖ * ‖tc W b (k - l)‖) :=
        mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ ≤ C₀ * (W l * W (k - l)) * (‖β₀‖ * ‖tc W a l‖ * ‖tc W b (k - l)‖) :=
        mul_le_mul_of_nonneg_right h2 h0
    _ = C₀ * ‖β₀‖ * (W l * ‖tc W a l‖ * (W (k - l) * ‖tc W b (k - l)‖)) := by ring

end sconv

end EquivEmbed.Torus
