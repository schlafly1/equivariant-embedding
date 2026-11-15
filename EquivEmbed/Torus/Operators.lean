/-
Copyright (c) 2026 Roger Schlafly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roger Schlafly
-/
module

public import EquivEmbed.Torus.Kernels
public import Mathlib.Analysis.SpecialFunctions.Exp
public import Mathlib.Analysis.Complex.Exponential

/-!
# Günther's operators and Günther's identity on Fourier coefficients

* `Sop`, `Top`, `mulL`, `Bop`, `Mop`: the operators of Günther's fixed point equation
  `v = Mop h + Bop v v` on a flat torus.
* `gunther_coeff`: Günther's identity `⟨∂_i v, ∂_j v⟩ = ∂_i S_j + ∂_j S_i + T_ij`, as an identity
  of Fourier coefficients.  It reduces to the antisymmetry of an explicit polynomial under the
  exchange `l ↔ k - l`.
* `Bop_twist`: the operator `Bop` commutes with every symmetry of the coefficients that fixes
  the dual frame.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace EquivEmbed.Torus

variable {n : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- `(Δ - 1)⁻¹ ⟨Δ v, ∂_j w⟩` on coefficients. -/
noncomputable def Sop (dot : F →L[ℂ] F →L[ℂ] ℂ) (j : Fin n) :
    L1 (Freq n) F →L[ℝ] L1 (Freq n) F →L[ℝ] L1 (Freq n) ℂ :=
  sconv (kS j) 1 (norm_kS_le j) (dotR dot)

/-- Günther's operator `T_ij` on coefficients. -/
noncomputable def Top (dot : F →L[ℂ] F →L[ℂ] ℂ) (i j : Fin n) :
    L1 (Freq n) F →L[ℝ] L1 (Freq n) F →L[ℝ] L1 (Freq n) ℂ :=
  sconv (kT i j) (2 * n + 3) (norm_kT_le i j) (dotR dot)

/-- The product of a vector valued function and a scalar function, on coefficients. -/
noncomputable def mulL : L1 (Freq n) F →L[ℝ] L1 (Freq n) ℂ →L[ℝ] L1 (Freq n) F :=
  sconv (fun _ _ => 1) 2 norm_one_le (smulR F)

lemma tc_Sop (dot : F →L[ℂ] F →L[ℂ] ℂ) (j : Fin n) (v w : L1 (Freq n) F) (k : Freq n) :
    tc W (Sop dot j v w) k = ∑' l, kS j l (k - l) * dot (tc W v l) (tc W w (k - l)) := by
  rw [Sop, tc_sconv]
  rfl

lemma tc_Top (dot : F →L[ℂ] F →L[ℂ] ℂ) (i j : Fin n) (v w : L1 (Freq n) F) (k : Freq n) :
    tc W (Top dot i j v w) k = ∑' l, kT i j l (k - l) * dot (tc W v l) (tc W w (k - l)) := by
  rw [Top, tc_sconv]
  rfl

lemma tc_mulL (y : L1 (Freq n) F) (c : L1 (Freq n) ℂ) (k : Freq n) :
    tc W (mulL y c) k = ∑' l, tc W c (k - l) • tc W y l := by
  rw [mulL, tc_sconv]
  simp

lemma le_of_weighted {κ : ℂ} {C₀ : ℝ} {l m : Freq n}
    (h : ‖κ‖ * W (l + m) ≤ C₀ * (W l * W m)) : ‖κ‖ ≤ C₀ * (W l * W m) :=
  (le_mul_of_one_le_right (norm_nonneg _) (one_le_W _)).trans h

/-! ### Günther's identity -/

lemma defect_antisymm {K : Type*} [Field K] (li lj mi mj sl sm lm w d : K)
    (hw : w = 1 + (sl + 2 * lm + sm)) (hw0 : w ≠ 0) :
    (-(mi * lj) + (li + mi) * (sm * lj / w) + (lj + mj) * (sm * li / w)
        - (-(-2 * sm * li * lj + 2 * mi * lj * lm + mi * lj) / w)) * d
      = -((-(li * mj) + (li + mi) * (sl * mj / w) + (lj + mj) * (sl * mi / w)
        - (-(-2 * sl * mi * mj + 2 * li * mj * lm + li * mj) / w)) * d) := by
  subst hw
  field_simp
  ring

lemma I_mul_kS (x d : ℂ) (j : Fin n) (l m : Freq n) :
    (Complex.I * x) * (kS j l m * d) = -(x * (rS j l m : ℂ) * d) := by
  unfold kS
  linear_combination (x * (rS j l m : ℂ) * d) * Complex.I_mul_I

lemma tsum_antisymm {g : Freq n → ℂ} (k : Freq n) (h : ∀ l, g (k - l) = -g l) :
    ∑' l, g l = 0 := by
  have h1 : ∑' l, g (k - l) = ∑' l, g l := (Equiv.subLeft k).tsum_eq g
  simp only [h, tsum_neg] at h1
  exact self_eq_neg.mp h1.symm

/-- **Günther's identity on Fourier coefficients.**  The `k`-th coefficient of
`⟨∂_i v, ∂_j v⟩` equals that of `∂_i S_j + ∂_j S_i + T_ij`. -/
theorem gunther_coeff (dot : F →L[ℂ] F →L[ℂ] ℂ) (hsymm : ∀ x y, dot x y = dot y x)
    (v : L1 (Freq n) F) (i j : Fin n) (k : Freq n) :
    ∑' l, (-((l i : ℂ) * ((k - l) j : ℂ))) * dot (tc W v l) (tc W v (k - l))
      = (Complex.I * (k i : ℂ)) * tc W (Sop dot j v v) k
        + (Complex.I * (k j : ℂ)) * tc W (Sop dot i v v) k + tc W (Top dot i j v v) k := by
  set d : Freq n → ℂ := fun l => dot (tc W v l) (tc W v (k - l)) with hd
  have hdsymm : ∀ l, d (k - l) = d l := fun l => by
    simp only [hd, sub_sub_cancel]
    exact hsymm _ _
  -- summability of the four families
  have sS : ∀ j' : Fin n, Summable fun l => kS j' l (k - l) * d l := fun j' =>
    summable_fiber (kS j') 1 (fun l m => le_of_weighted (norm_kS_le j' l m)) (dotR dot) v v k
  have sT : Summable fun l => kT i j l (k - l) * d l :=
    summable_fiber (kT i j) (2 * n + 3) (fun l m => le_of_weighted (norm_kT_le i j l m))
      (dotR dot) v v k
  have sG : Summable fun l => (-((l i : ℂ) * ((k - l) j : ℂ))) * d l := by
    refine summable_fiber (fun l m => -((l i : ℂ) * (m j : ℂ))) 1 (fun l m => ?_) (dotR dot) v v k
    rw [norm_neg, norm_mul, Complex.norm_intCast, Complex.norm_intCast, one_mul]
    exact mul_le_mul ((abs_coord_le l i).trans (sq_le_W l)) ((abs_coord_le m j).trans (sq_le_W m))
      (abs_nonneg _) (W_pos l).le
  rw [tc_Sop, tc_Sop, tc_Top]
  rw [← tsum_mul_left, ← tsum_mul_left, ← ((sS j).mul_left _).tsum_add ((sS i).mul_left _),
    ← (((sS j).mul_left _).add ((sS i).mul_left _)).tsum_add sT, ← sub_eq_zero,
    ← sG.tsum_sub ((((sS j).mul_left _).add ((sS i).mul_left _)).add sT)]
  refine tsum_antisymm k fun l => ?_
  have e1 : k - l + l = k := sub_add_cancel k l
  have e2 : l + (k - l) = k := add_sub_cancel l k
  have e3 : k - (k - l) = l := sub_sub_cancel k l
  have hWk : (W k : ℂ) = 1 + ((sq l : ℂ) + 2 * (ip l (k - l) : ℂ) + (sq (k - l) : ℂ)) := by
    have := sq_add l (k - l)
    rw [e2] at this
    rw [W, this]
    push_cast
    ring
  have hW0 : (W k : ℂ) ≠ 0 := by
    exact_mod_cast (W_pos k).ne'
  have hip : ip (k - l) l = ip l (k - l) := by
    simp only [ip]
    exact Finset.sum_congr rfl fun p _ => mul_comm _ _
  have H := defect_antisymm (l i : ℂ) (l j : ℂ) ((k i : ℂ) - (l i : ℂ)) ((k j : ℂ) - (l j : ℂ))
    (sq l : ℂ) (sq (k - l) : ℂ) (ip l (k - l) : ℂ) (W k : ℂ) (d l) hWk hW0
  simp only [hdsymm, I_mul_kS, e3]
  simp only [rS, kT, rT, e1, e2, hip, Pi.sub_apply]
  push_cast
  linear_combination H

/-! ### The fixed point operators -/

/-- Günther's quadratic operator on a flat torus, for the dual frame `(L1c, L2c)`:
`Bop v w = L(-S(v, w), T(v, w) / 2)`. -/
noncomputable def Bop (dot : F →L[ℂ] F →L[ℂ] ℂ) (L1c : Fin n → L1 (Freq n) F)
    (L2c : Fin n → Fin n → L1 (Freq n) F) :
    L1 (Freq n) F →L[ℝ] L1 (Freq n) F →L[ℝ] L1 (Freq n) F :=
  (∑ j, -((ContinuousLinearMap.compL ℝ (L1 (Freq n) F) (L1 (Freq n) ℂ) (L1 (Freq n) F)
      (mulL (L1c j))).comp (Sop dot j)))
    + ∑ i, ∑ j, (1 / 2 : ℝ) • ((ContinuousLinearMap.compL ℝ (L1 (Freq n) F) (L1 (Freq n) ℂ)
      (L1 (Freq n) F) (mulL (L2c i j))).comp (Top dot i j))

lemma Bop_apply (dot : F →L[ℂ] F →L[ℂ] ℂ) (L1c : Fin n → L1 (Freq n) F)
    (L2c : Fin n → Fin n → L1 (Freq n) F) (v w : L1 (Freq n) F) :
    Bop dot L1c L2c v w = ∑ j, -(mulL (L1c j) (Sop dot j v w))
      + ∑ i, ∑ j, (1 / 2 : ℝ) • mulL (L2c i j) (Top dot i j v w) := by
  simp [Bop, ContinuousLinearMap.sum_apply]

/-- Günther's linear operator: `Mop h = L(0, -h / 2)`. -/
noncomputable def Mop (L2c : Fin n → Fin n → L1 (Freq n) F)
    (h : Fin n → Fin n → L1 (Freq n) ℂ) : L1 (Freq n) F :=
  ∑ i, ∑ j, (-(1 / 2) : ℝ) • mulL (L2c i j) (h i j)

lemma norm_Mop_le (L2c : Fin n → Fin n → L1 (Freq n) F) (h : Fin n → Fin n → L1 (Freq n) ℂ)
    (ε : ℝ) (hε : ∀ i j, ‖h i j‖ ≤ ε) :
    ‖Mop L2c h‖ ≤ (∑ i, ∑ j, ‖(mulL (L2c i j) : L1 (Freq n) ℂ →L[ℝ] L1 (Freq n) F)‖) * ε := by
  unfold Mop
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
  rw [norm_smul]
  have h1 := (mulL (L2c i j)).le_opNorm (h i j)
  have h2 : ‖(mulL (L2c i j) : L1 (Freq n) ℂ →L[ℝ] L1 (Freq n) F)‖ * ‖h i j‖
      ≤ ‖(mulL (L2c i j) : L1 (Freq n) ℂ →L[ℝ] L1 (Freq n) F)‖ * ε :=
    mul_le_mul_of_nonneg_left (hε i j) (norm_nonneg _)
  have h3 : ‖(-(1 / 2) : ℝ)‖ ≤ 1 := by norm_num
  have h4 := norm_nonneg (mulL (L2c i j) (h i j))
  nlinarith [norm_nonneg (-(1 / 2) : ℝ)]

/-! ### Symmetries -/

/-- `twist` as a linear map. -/
noncomputable def twistL {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (θ : Freq n ≃+ Freq n) (U : Freq n → G →ₗᵢ[ℝ] G) : L1 (Freq n) G →ₗ[ℝ] L1 (Freq n) G where
  toFun := twist θ U
  map_add' := twist_add θ U
  map_smul' := twist_smul θ U

@[simp] lemma twistL_apply {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
    (θ : Freq n ≃+ Freq n) (U : Freq n → G →ₗᵢ[ℝ] G) (b : L1 (Freq n) G) :
    twistL θ U b = twist θ U b := rfl

lemma sconv_twist {F₁ F₂ F₃ : Type*}
    [NormedAddCommGroup F₁] [NormedSpace ℝ F₁] [NormedAddCommGroup F₂] [NormedSpace ℝ F₂]
    [NormedAddCommGroup F₃] [NormedSpace ℂ F₃] [CompleteSpace F₃]
    (κ : Freq n → Freq n → ℂ) (C₀ : ℝ)
    (hκ : ∀ l m, ‖κ l m‖ * W (l + m) ≤ C₀ * (W l * W m)) (β₀ : F₁ →L[ℝ] F₂ →L[ℝ] F₃)
    (θ : Freq n ≃+ Freq n) (hθ : ∀ k, W (θ k) = W k)
    (U₁ : Freq n → F₁ →ₗᵢ[ℝ] F₁) (U₂ : Freq n → F₂ →ₗᵢ[ℝ] F₂) (U₃ : Freq n → F₃ →ₗᵢ[ℝ] F₃)
    (h : ∀ l m x y, κ l m • β₀ (U₁ l x) (U₂ m y) = U₃ (l + m) (κ (θ l) (θ m) • β₀ x y))
    (a : L1 (Freq n) F₁) (b : L1 (Freq n) F₂) :
    sconv κ C₀ hκ β₀ (twist θ U₁ a) (twist θ U₂ b) = twist θ U₃ (sconv κ C₀ hκ β₀ a b) :=
  wconv_twist W_pos _ θ hθ U₁ U₂ U₃ (fun l m x y => by simpa using h l m x y) a b

/-- A symmetry of the coefficient spaces: a frequency automorphism `θ` preserving the weight,
isometries `UF k` of `F` and `UC k` of `ℂ`, compatible with the three kernels and with the
bilinear maps `dot` and scalar multiplication. -/
structure CoeffSymm (n : ℕ) (F : Type*) [NormedAddCommGroup F] [NormedSpace ℂ F]
    (dot : F →L[ℂ] F →L[ℂ] ℂ) where
  /-- The action on frequencies. -/
  θ : Freq n ≃+ Freq n
  /-- The action on vector coefficients. -/
  UF : Freq n → F →ₗᵢ[ℝ] F
  /-- The action on scalar coefficients. -/
  UC : Freq n → ℂ →ₗᵢ[ℝ] ℂ
  W_θ : ∀ k, W (θ k) = W k
  hS : ∀ j l m x y, kS j l m * dot (UF l x) (UF m y) = UC (l + m) (kS j (θ l) (θ m) * dot x y)
  hT : ∀ i j l m x y,
    kT i j l m * dot (UF l x) (UF m y) = UC (l + m) (kT i j (θ l) (θ m) * dot x y)
  hmul : ∀ l m (y : F) (c : ℂ), UC m c • UF l y = UF (l + m) (c • y)

namespace CoeffSymm

variable {dot : F →L[ℂ] F →L[ℂ] ℂ} (σ : CoeffSymm n F dot)

/-- The action on vector valued coefficient families. -/
noncomputable def actF (b : L1 (Freq n) F) : L1 (Freq n) F := twist σ.θ σ.UF b

/-- The action on scalar coefficient families. -/
noncomputable def actC (b : L1 (Freq n) ℂ) : L1 (Freq n) ℂ := twist σ.θ σ.UC b

lemma norm_actF (b : L1 (Freq n) F) : ‖σ.actF b‖ = ‖b‖ := norm_twist _ _ _

lemma Sop_act (j : Fin n) (v w : L1 (Freq n) F) :
    Sop dot j (σ.actF v) (σ.actF w) = σ.actC (Sop dot j v w) :=
  sconv_twist (kS j) 1 (norm_kS_le j) (dotR dot) σ.θ σ.W_θ σ.UF σ.UF σ.UC
    (fun l m x y => by simpa using σ.hS j l m x y) v w

lemma Top_act (i j : Fin n) (v w : L1 (Freq n) F) :
    Top dot i j (σ.actF v) (σ.actF w) = σ.actC (Top dot i j v w) :=
  sconv_twist (kT i j) (2 * n + 3) (norm_kT_le i j) (dotR dot) σ.θ σ.W_θ σ.UF σ.UF σ.UC
    (fun l m x y => by simpa using σ.hT i j l m x y) v w

lemma mulL_act (y : L1 (Freq n) F) (c : L1 (Freq n) ℂ) :
    mulL (σ.actF y) (σ.actC c) = σ.actF (mulL y c) :=
  sconv_twist (fun _ _ => 1) 2 norm_one_le (smulR F) σ.θ σ.W_θ σ.UF σ.UC σ.UF
    (fun l m x y => by simpa using σ.hmul l m x y) y c

lemma actF_add (a b : L1 (Freq n) F) : σ.actF (a + b) = σ.actF a + σ.actF b := twist_add _ _ _ _

lemma actF_sum {ι' : Type*} (s : Finset ι') (f : ι' → L1 (Freq n) F) :
    σ.actF (∑ i ∈ s, f i) = ∑ i ∈ s, σ.actF (f i) :=
  map_sum (twistL σ.θ σ.UF) f s

lemma actF_smul (c : ℝ) (a : L1 (Freq n) F) : σ.actF (c • a) = c • σ.actF a := twist_smul _ _ _ _

lemma actF_neg (a : L1 (Freq n) F) : σ.actF (-a) = -σ.actF a := twist_neg _ _ _

/-- `Bop` commutes with every coefficient symmetry fixing the dual frame. -/
theorem Bop_act (L1c : Fin n → L1 (Freq n) F) (L2c : Fin n → Fin n → L1 (Freq n) F)
    (h1 : ∀ j, σ.actF (L1c j) = L1c j) (h2 : ∀ i j, σ.actF (L2c i j) = L2c i j)
    (v w : L1 (Freq n) F) :
    σ.actF (Bop dot L1c L2c v w) = Bop dot L1c L2c (σ.actF v) (σ.actF w) := by
  simp only [Bop_apply, actF_add, actF_sum, actF_neg, actF_smul, Sop_act, Top_act]
  congr 1
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [← σ.mulL_act, h1]
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [← σ.mulL_act, h2]

/-- `Mop` commutes with every coefficient symmetry fixing the dual frame. -/
theorem Mop_act (L2c : Fin n → Fin n → L1 (Freq n) F) (h2 : ∀ i j, σ.actF (L2c i j) = L2c i j)
    (h : Fin n → Fin n → L1 (Freq n) ℂ) :
    σ.actF (Mop L2c h) = Mop L2c (fun i j => σ.actC (h i j)) := by
  simp only [Mop, actF_sum, actF_smul]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [← σ.mulL_act, h2]

end CoeffSymm

end EquivEmbed.Torus
