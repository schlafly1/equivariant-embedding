/-
Copyright (c) 2026 Roger Schlafly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roger Schlafly
-/
module

public import EquivEmbed.Torus.Fourier
public import EquivEmbed.FixedPoint

/-!
# The equivariant Günther perturbation theorem on a flat torus

This file assembles the unconditional theorem.  The data are a map `u` of the torus
`ℝⁿ / 2π ℤⁿ` and a dual frame `(ℓ1, ℓ2)` of its first and second derivatives, all given by
Fourier coefficients in the weighted Wiener algebra.

* `exists_fixedPoint`: the fixed point of Günther's equation, with its symmetry.
* `metric_identity`: a solution of Günther's equation solves `F(u + v) = F(u) + h`.
* `torus_perturbation`: the perturbation theorem, with inheritance of symmetry and reality.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.deprecated false
set_option linter.unusedSimpArgs false

namespace EquivEmbed.Torus

variable {n : ℕ}

section tc

variable {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]

lemma tcW_add (a b : L1 (Freq n) G) (k : Freq n) : tc W (a + b) k = tc W a k + tc W b k := by
  simp [tc]

lemma tcW_smul (c : ℝ) (a : L1 (Freq n) G) (k : Freq n) : tc W (c • a) k = c • tc W a k := by
  simp only [tc, lp.coeFn_smul, Pi.smul_apply]
  exact smul_comm _ _ _

lemma summable_norm_tc (b : L1 (Freq n) G) : Summable fun k => ‖tc W b k‖ :=
  Summable.of_nonneg_of_le (fun _ => norm_nonneg _)
    (fun k => le_mul_of_one_le_left (norm_nonneg _) (one_le_W k)) (summable_tc W_pos b)

end tc

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]

/-- Evaluation of the Fourier series of an element of the weighted space, as a linear map. -/
noncomputable def fev {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
    (x : Fin n → ℝ) : L1 (Freq n) G →ₗ[ℝ] G where
  toFun b := fsum (tc W b) x
  map_add' a b := by
    have h : tc W (a + b) = fun k => tc W a k + tc W b k := funext (tcW_add a b)
    rw [h]
    exact fsum_add (summable_norm_tc a) (summable_norm_tc b) x
  map_smul' c a := by
    have h : tc W (c • a) = fun k => c • tc W a k := funext (tcW_smul c a)
    rw [h]
    exact fsum_real_smul c _ x

lemma fev_apply {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] [CompleteSpace G]
    (x : Fin n → ℝ) (b : L1 (Freq n) G) : fev x b = fsum (tc W b) x := rfl

/-- The Fourier series of `mulL y c` is the product of the Fourier series. -/
lemma fev_mulL (y : L1 (Freq n) F) (c : L1 (Freq n) ℂ) (x : Fin n → ℝ) :
    fev x (mulL y c) = fev x c • fev x y := by
  have h : tc W (mulL y c) = convFun (fun _ _ => smulR F) (tc W y) (tc W c) :=
    funext fun k => by
      rw [mulL, tc_sconv]
      simp [convFun]
  rw [fev_apply, h, fsum_conv (smulR F) (fun c d x y => by
    simp only [smulR_apply, smul_smul, smul_eq_mul]
    congr 1
    ring) _ _ (summable_norm_tc y) (summable_norm_tc c) x]
  rfl

/-! ### The fixed point -/

/-- **Existence and symmetry of the solution of Günther's equation on a flat torus.** -/
theorem exists_fixedPoint (dot : F →L[ℂ] F →L[ℂ] ℂ) (L1c : Fin n → L1 (Freq n) F)
    (L2c : Fin n → Fin n → L1 (Freq n) F) :
    ∃ ε > 0, ∃ C : ℝ, ∀ h : Fin n → Fin n → L1 (Freq n) ℂ, (∀ i j, ‖h i j‖ < ε) →
      ∃ v : L1 (Freq n) F, v = Mop L2c h + Bop dot L1c L2c v v ∧
        (∀ δ : ℝ, (∀ i j, ‖h i j‖ ≤ δ) → ‖v‖ ≤ C * δ) ∧
        ∀ σ : CoeffSymm n F dot, (∀ j, σ.actF (L1c j) = L1c j) →
          (∀ i j, σ.actF (L2c i j) = L2c i j) → (∀ i j, σ.actC (h i j) = h i j) →
          σ.actF v = v := by
  set b := ‖Bop dot L1c L2c‖ with hb
  set K := ∑ i, ∑ j, ‖(mulL (L2c i j) : L1 (Freq n) ℂ →L[ℝ] L1 (Freq n) F)‖ with hK
  have hb0 : 0 ≤ b := norm_nonneg (Bop dot L1c L2c)
  have hK0 : 0 ≤ K := Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => norm_nonneg _
  have hpos : 0 < (4 * b + 1) * (K + 1) := by positivity
  refine ⟨1 / ((4 * b + 1) * (K + 1)), by positivity, 2 * K, fun h hh => ?_⟩
  have hM : ‖Mop L2c h‖ ≤ K * (1 / ((4 * b + 1) * (K + 1))) :=
    norm_Mop_le L2c h _ (fun i j => (hh i j).le)
  have hm : 4 * ‖Bop dot L1c L2c‖ * ‖Mop L2c h‖ < 1 := by
    have h1 : 4 * b * ‖Mop L2c h‖ ≤ 4 * b * (K * (1 / ((4 * b + 1) * (K + 1)))) :=
      mul_le_mul_of_nonneg_left hM (by positivity)
    have h2 : 4 * b * (K * (1 / ((4 * b + 1) * (K + 1)))) < 1 := by
      rw [← mul_assoc, mul_one_div, div_lt_one hpos]
      nlinarith
    exact lt_of_le_of_lt h1 h2
  obtain ⟨v, ⟨hvn, hvf⟩, -⟩ := exists_unique_fixedPoint_bilinear (Bop dot L1c L2c) hm
  refine ⟨v, hvf, fun δ hδ => ?_, fun σ h1 h2 h3 => ?_⟩
  · have hMδ := norm_Mop_le L2c h δ hδ
    calc ‖v‖ ≤ 2 * ‖Mop L2c h‖ := hvn
      _ ≤ 2 * (K * δ) := by linarith
      _ = 2 * K * δ := by ring
  refine fixedPoint_bilinear_symm (Bop dot L1c L2c) σ.actF σ.norm_actF σ.actF_add
    (fun v w => σ.Bop_act L1c L2c h1 h2 v w) hm ?_ hvn hvf
  rw [σ.Mop_act L2c h2]
  congr 1
  funext i j
  exact h3 i j

/-! ### From Günther's equation to the metric equation -/

lemma sum_delta (c : Fin n → Fin n → ℂ) (p q : Fin n) :
    ∑ i, ∑ j, c i j * ((if p = i then (if q = j then (1 / 2 : ℂ) else 0) else 0)
      + (if p = j then (if q = i then (1 / 2 : ℂ) else 0) else 0))
      = (1 / 2) * (c p q + c q p) := by
  simp only [mul_add, Finset.sum_add_distrib, mul_ite, mul_zero]
  simp [Finset.sum_ite_eq, Finset.sum_ite_eq']
  ring

section metric

variable (dot : F →L[ℂ] F →L[ℂ] ℂ) (hsymm : ∀ x y, dot x y = dot y x)
  (u : Freq n → F) (hu : Summable fun k => W k * ‖u k‖)
  (L1c : Fin n → L1 (Freq n) F) (L2c : Fin n → Fin n → L1 (Freq n) F)
  (h : Fin n → Fin n → L1 (Freq n) ℂ) (v : L1 (Freq n) F)
  (hv : v = Mop L2c h + Bop dot L1c L2c v v)

include hv in
/-- The value of a functional on the solution, in terms of the dual frame. -/
lemma dot_solution (z : F) (x : Fin n → ℝ) :
    dot z (fev x v) = ∑ i, ∑ j, (-(1 / 2 : ℂ)) * (fev x (h i j) * dot z (fev x (L2c i j)))
      + (∑ j, -(fev x (Sop dot j v v) * dot z (fev x (L1c j)))
        + ∑ i, ∑ j, (1 / 2 : ℂ) * (fev x (Top dot i j v v) * dot z (fev x (L2c i j)))) := by
  conv_lhs => rw [hv]
  simp only [Mop, Bop_apply, map_add, map_sum, map_neg, map_smul, fev_mulL]
  simp only [← Complex.coe_smul, map_smul, map_add, map_sum, map_neg, smul_eq_mul]
  push_cast
  rfl

include hsymm in
/-- **Günther's identity**, pointwise on the torus. -/
lemma gunther_pointwise (i j : Fin n) (x : Fin n → ℝ) :
    dot (pd i (fsum (tc W v)) x) (pd j (fsum (tc W v)) x)
      = pd i (fsum (tc W (Sop dot j v v))) x + pd j (fsum (tc W (Sop dot i v v))) x
        + fsum (tc W (Top dot i j v v)) x := by
  have hv' := summable_tc W_pos v
  have hSj := summable_tc W_pos (Sop dot j v v)
  have hSi := summable_tc W_pos (Sop dot i v v)
  rw [pd_fsum_of_W hv', pd_fsum_of_W hv', pd_fsum_of_W hSj, pd_fsum_of_W hSi]
  have hconv := fsum_conv (dotR dot) (fun c d x y => by simp [mul_assoc, mul_left_comm])
    (dc i (tc W v)) (dc j (tc W v)) (summable_dc_of_W hv' i) (summable_dc_of_W hv' j) x
  rw [dotR_apply] at hconv
  rw [← hconv]
  have hcoef : convFun (fun _ _ => dotR dot) (dc i (tc W v)) (dc j (tc W v))
      = fun k => dc i (tc W (Sop dot j v v)) k + dc j (tc W (Sop dot i v v)) k
        + tc W (Top dot i j v v) k := by
    funext k
    have hg := gunther_coeff dot hsymm v i j k
    simp only [dc, smul_eq_mul]
    rw [← hg]
    unfold convFun
    refine tsum_congr fun l => ?_
    simp only [dotR_apply, dc, map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    linear_combination (((l i : ℂ)) * ((k - l) j : ℂ) * dot (tc W v l) (tc W v (k - l)))
      * Complex.I_mul_I
  rw [hcoef]
  rw [fsum_add, fsum_add]
  · exact summable_dc_of_W hSj i
  · exact summable_dc_of_W hSi j
  · exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun k => norm_add_le _ _)
      ((summable_dc_of_W hSj i).add (summable_dc_of_W hSi j))
  · exact summable_norm_tc _

/-! ### Differentiability and the calculus of `pd` -/

lemma differentiableAt_fsum {a : Freq n → F} (h : Summable fun k => W k * ‖a k‖)
    (x : Fin n → ℝ) : DifferentiableAt ℝ (fsum a) x :=
  (hasFDerivAt_fsum a (summable_of_W h) (summable_N1_of_W h) x).differentiableAt

lemma differentiableAt_pd_fsum {a : Freq n → F} (h : Summable fun k => W k * ‖a k‖) (p : Fin n)
    (x : Fin n → ℝ) : DifferentiableAt ℝ (pd p (fsum a)) x := by
  rw [pd_fsum_of_W h p]
  exact (hasFDerivAt_fsum (dc p a) (summable_dc_of_W h p) (summable_N1_dc_of_W h p)
    x).differentiableAt

lemma pd_add {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {f g : (Fin n → ℝ) → G}
    {x : Fin n → ℝ} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (p : Fin n) :
    pd p (fun y => f y + g y) x = pd p f x + pd p g x := by
  rw [pd, fderiv_fun_add hf hg]
  rfl

lemma pd_neg {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] (f : (Fin n → ℝ) → G)
    (x : Fin n → ℝ) (p : Fin n) : pd p (fun y => -f y) x = -pd p f x := by
  rw [pd, fderiv_fun_neg]
  rfl

lemma pd_dot_diff (dot : F →L[ℂ] F →L[ℂ] ℂ) {f g : (Fin n → ℝ) → F} {x : Fin n → ℝ}
    (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) (p : Fin n) :
    pd p (fun y => dot (f y) (g y)) x = dot (pd p f x) (g x) + dot (f x) (pd p g x) :=
  pd_dot dot hf.hasFDerivAt hg.hasFDerivAt p

include hsymm hu hv in
/-- **Günther's reduction on a flat torus.**  If `(L1c, L2c)` is a dual frame of the first and
second derivatives of `u = fsum u`, then every solution `v` of Günther's equation
`v = Mop h + Bop v v` satisfies the isometric embedding equation `F(u + v) = F(u) + h`. -/
theorem metric_identity (hh : ∀ i j, h i j = h j i)
    (hd1 : ∀ x p q, dot (pd p (fsum u) x) (fev x (L1c q)) = if p = q then 1 else 0)
    (hd2 : ∀ x p q r, dot (pd p (fsum u) x) (fev x (L2c q r)) = 0)
    (hd3 : ∀ x p q r, dot (pd p (pd q (fsum u)) x) (fev x (L1c r)) = 0)
    (hd4 : ∀ x p q r s, dot (pd p (pd q (fsum u)) x) (fev x (L2c r s))
      = (if p = r then (if q = s then (1 / 2 : ℂ) else 0) else 0)
        + (if p = s then (if q = r then (1 / 2 : ℂ) else 0) else 0))
    (x : Fin n → ℝ) (i j : Fin n) :
    dot (pd i (fun y => fsum u y + fsum (tc W v) y) x)
        (pd j (fun y => fsum u y + fsum (tc W v) y) x)
      = dot (pd i (fsum u) x) (pd j (fsum u) x) + fsum (tc W (h i j)) x := by
  have hvW := summable_tc W_pos v
  -- the two contractions of the solution with the frame of `u`
  have hV1 : ∀ p y, dot (pd p (fsum u) y) (fev y v) = -(fev y (Sop dot p v v)) := by
    intro p y
    rw [dot_solution dot L1c L2c h v hv]
    simp [hd1, hd2, Finset.sum_ite_eq]
  have hV2 : ∀ p q y, dot (pd p (pd q (fsum u)) y) (fev y v)
      = (1 / 2) * (((1 / 2 : ℂ) * fev y (Top dot p q v v) - (1 / 2) * fev y (h p q))
        + ((1 / 2 : ℂ) * fev y (Top dot q p v v) - (1 / 2) * fev y (h q p))) := by
    intro p q y
    rw [dot_solution dot L1c L2c h v hv]
    simp only [hd3, hd4, mul_zero, neg_zero, Finset.sum_const_zero, zero_add, ← mul_assoc]
    rw [sum_delta (fun i j => -(1 / 2 : ℂ) * fev y (h i j)) p q,
      sum_delta (fun i j => (1 / 2 : ℂ) * fev y (Top dot i j v v)) p q]
    ring
  -- differentiate the first contraction
  have star : ∀ i j, dot (pd j (pd i (fsum u)) x) (fsum (tc W v) x)
      + dot (pd i (fsum u) x) (pd j (fsum (tc W v)) x)
      = -pd j (fsum (tc W (Sop dot i v v))) x := by
    intro i j
    have hfun : (fun y => dot (pd i (fsum u) y) (fsum (tc W v) y))
        = fun y => -(fsum (tc W (Sop dot i v v)) y) := funext (hV1 i)
    have h1 := pd_dot_diff dot (differentiableAt_pd_fsum hu i x) (differentiableAt_fsum hvW x) j
    rw [← h1, hfun, pd_neg]
  have A := star i j
  have B := star j i
  have E1 := hV2 j i x
  have E2 := hV2 i j x
  have G1 := gunther_pointwise dot hsymm v i j x
  have G2 := gunther_pointwise dot hsymm v j i x
  have s1 := hsymm (pd i (fsum (tc W v)) x) (pd j (fsum u) x)
  have s2 := hsymm (pd j (fsum (tc W v)) x) (pd i (fsum (tc W v)) x)
  have hH : fsum (tc W (h j i)) x = fsum (tc W (h i j)) x := by rw [hh j i]
  simp only [fev_apply] at E1 E2
  rw [pd_add (differentiableAt_fsum hu x) (differentiableAt_fsum hvW x),
    pd_add (differentiableAt_fsum hu x) (differentiableAt_fsum hvW x)]
  simp only [map_add, ContinuousLinearMap.add_apply]
  linear_combination A + B - E1 - E2 + s1 + G1 + (1 / 2) * (G2 - G1 - s2) + (1 / 2) * hH

end metric

/-! ### The two kinds of symmetry -/

/-- The real linear isometry `x ↦ c • R x`, for a unimodular `c` and a complex linear
isometry `R`. -/
noncomputable def phaseLI {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] (c : ℂ)
    (hc : ‖c‖ = 1) (R : G →ₗᵢ[ℂ] G) : G →ₗᵢ[ℝ] G where
  toLinearMap := (c • R.toLinearMap).restrictScalars ℝ
  norm_map' x := by simp [norm_smul, hc]

@[simp] lemma phaseLI_apply {G : Type*} [NormedAddCommGroup G] [NormedSpace ℂ G] (c : ℂ)
    (hc : ‖c‖ = 1) (R : G →ₗᵢ[ℂ] G) (x : G) : phaseLI c hc R x = c • R x := rfl

/-- The coefficient symmetry of the translation `x ↦ x + t` combined with the isometry `R`
of the target: it corresponds to `f ↦ R ∘ f ∘ (· - t)`. -/
noncomputable def transSymm (dot : F →L[ℂ] F →L[ℂ] ℂ) (t : Fin n → ℝ) (R : F →ₗᵢ[ℂ] F)
    (hR : ∀ x y, dot (R x) (R y) = dot x y) : CoeffSymm n F dot where
  θ := AddEquiv.refl _
  UF k := phaseLI (ef k (-t)) (norm_ef _ _) R
  UC k := phaseLI (ef k (-t)) (norm_ef _ _) LinearIsometry.id
  W_θ _ := rfl
  hS j l m x y := by
    simp [hR, ef_add_freq]
    ring
  hT i j l m x y := by
    simp [hR, ef_add_freq]
    ring
  hmul l m y c := by
    simp [smul_smul, ef_add_freq]
    congr 1
    ring

lemma rS_neg (j : Fin n) (l m : Freq n) : rS j (-l) (-m) = -rS j l m := by
  unfold rS
  rw [← neg_add, W_neg, sq_neg]
  simp
  ring

lemma ip_neg (l m : Freq n) : ip (-l) (-m) = ip l m := by simp [ip]

lemma rT_neg (i j : Fin n) (l m : Freq n) : rT i j (-l) (-m) = rT i j l m := by
  unfold rT
  rw [← neg_add, W_neg, sq_neg, ip_neg]
  simp

lemma kS_conj (j : Fin n) (l m : Freq n) : starRingEnd ℂ (kS j (-l) (-m)) = kS j l m := by
  simp [kS, rS_neg]

lemma kT_conj (i j : Fin n) (l m : Freq n) : starRingEnd ℂ (kT i j (-l) (-m)) = kT i j l m := by
  simp [kT, rT_neg]

/-- The coefficient symmetry of complex conjugation: it corresponds to `f ↦ conj ∘ f`. -/
noncomputable def conjSymm (dot : F →L[ℂ] F →L[ℂ] ℂ) (cF : F →ₗᵢ[ℝ] F)
    (hc : ∀ (z : ℂ) (y : F), cF (z • y) = starRingEnd ℂ z • cF y)
    (hcd : ∀ x y, dot (cF x) (cF y) = starRingEnd ℂ (dot x y)) : CoeffSymm n F dot where
  θ := AddEquiv.neg (Freq n)
  UF _ := cF
  UC _ := Complex.conjLIE.toLinearIsometry
  W_θ k := W_neg k
  hS j l m x y := by simp [hcd, kS_conj]
  hT i j l m x y := by simp [hcd, kT_conj]
  hmul l m y c := (hc c y).symm

namespace CoeffSymm

variable {dot : F →L[ℂ] F →L[ℂ] ℂ} (σ : CoeffSymm n F dot)

lemma actF_eq_of_tc (b : L1 (Freq n) F) (hb : ∀ k, σ.UF k (tc W b (σ.θ k)) = tc W b k) :
    σ.actF b = b :=
  ext_tc W_pos fun k => by
    rw [CoeffSymm.actF, tc_twist σ.θ σ.W_θ]
    exact hb k

lemma actC_eq_of_tc (b : L1 (Freq n) ℂ) (hb : ∀ k, σ.UC k (tc W b (σ.θ k)) = tc W b k) :
    σ.actC b = b :=
  ext_tc W_pos fun k => by
    rw [CoeffSymm.actC, tc_twist σ.θ σ.W_θ]
    exact hb k

lemma tc_of_actF_eq (b : L1 (Freq n) F) (h : σ.actF b = b) (k : Freq n) :
    σ.UF k (tc W b (σ.θ k)) = tc W b k := by
  have := congrArg (fun c => tc W c k) h
  simp only [CoeffSymm.actF, tc_twist σ.θ σ.W_θ] at this
  exact this

end CoeffSymm

/-! ### The theorem -/

/-- **Equivariant Günther perturbation theorem on the flat torus `ℝⁿ / 2π ℤⁿ`.**

Let `u`, `ℓ1 j`, `ℓ2 i j` be families of Fourier coefficients in the weighted Wiener algebra
(`∑ (1 + |k|²) ‖a k‖ < ∞`), such that `(ℓ1, ℓ2)` is a dual frame of the first and second
derivatives of the map `fsum u` (so `fsum u` is free).  Then there is `ε > 0` such that for every
symmetric `h` with `∑ (1 + |k|²) ‖h i j k‖ < ε` there is `v` in the same algebra with

  `⟨∂_i (u + v), ∂_j (u + v)⟩ = ⟨∂_i u, ∂_j u⟩ + h i j`     pointwise on the torus.

Moreover `v` inherits every symmetry of the data: every translation `t` combined with an
isometry `R` of the target preserving `dot`, and the complex conjugation `cF` (so that `v` is a
real map if the data are real).  No analytic hypothesis is assumed. -/
theorem torus_perturbation (dot : F →L[ℂ] F →L[ℂ] ℂ) (hsymm : ∀ x y, dot x y = dot y x)
    (u : Freq n → F) (hu : Summable fun k => W k * ‖u k‖)
    (ℓ1 : Fin n → Freq n → F) (hℓ1 : ∀ j, Summable fun k => W k * ‖ℓ1 j k‖)
    (ℓ2 : Fin n → Fin n → Freq n → F) (hℓ2 : ∀ i j, Summable fun k => W k * ‖ℓ2 i j k‖)
    (hd1 : ∀ x p q, dot (pd p (fsum u) x) (fsum (ℓ1 q) x) = if p = q then 1 else 0)
    (hd2 : ∀ x p q r, dot (pd p (fsum u) x) (fsum (ℓ2 q r) x) = 0)
    (hd3 : ∀ x p q r, dot (pd p (pd q (fsum u)) x) (fsum (ℓ1 r) x) = 0)
    (hd4 : ∀ x p q r s, dot (pd p (pd q (fsum u)) x) (fsum (ℓ2 r s) x)
      = (if p = r then (if q = s then (1 / 2 : ℂ) else 0) else 0)
        + (if p = s then (if q = r then (1 / 2 : ℂ) else 0) else 0)) :
    ∃ ε > 0, ∃ C : ℝ, ∀ h : Fin n → Fin n → Freq n → ℂ,
      (∀ i j, Summable fun k => W k * ‖h i j k‖) → (∀ i j, h i j = h j i) →
      (∀ i j, ∑' k, W k * ‖h i j k‖ < ε) →
      ∃ v : Freq n → F, (Summable fun k => W k * ‖v k‖) ∧
        (∀ δ : ℝ, (∀ i j, ∑' k, W k * ‖h i j k‖ ≤ δ) → ∑' k, W k * ‖v k‖ ≤ C * δ) ∧
        (∀ x i j, dot (pd i (fun y => fsum u y + fsum v y) x)
            (pd j (fun y => fsum u y + fsum v y) x)
          = dot (pd i (fsum u) x) (pd j (fsum u) x) + fsum (h i j) x) ∧
        (∀ (t : Fin n → ℝ) (R : F →ₗᵢ[ℂ] F), (∀ x y, dot (R x) (R y) = dot x y) →
          (∀ k, ef k (-t) • R (u k) = u k) →
          (∀ j k, ef k (-t) • R (ℓ1 j k) = ℓ1 j k) →
          (∀ i j k, ef k (-t) • R (ℓ2 i j k) = ℓ2 i j k) →
          (∀ i j k, ef k (-t) * h i j k = h i j k) →
          (∀ k, ef k (-t) • R (v k) = v k) ∧
            ∀ x, fsum u (x + t) + fsum v (x + t) = R (fsum u x + fsum v x)) ∧
        (∀ cF : F →ₗᵢ[ℝ] F, (∀ (z : ℂ) (y : F), cF (z • y) = starRingEnd ℂ z • cF y) →
          (∀ x y, dot (cF x) (cF y) = starRingEnd ℂ (dot x y)) →
          (∀ k, cF (u (-k)) = u k) →
          (∀ j k, cF (ℓ1 j (-k)) = ℓ1 j k) → (∀ i j k, cF (ℓ2 i j (-k)) = ℓ2 i j k) →
          (∀ i j k, starRingEnd ℂ (h i j (-k)) = h i j k) →
          (∀ k, cF (v (-k)) = v k) ∧ ∀ x, cF (fsum u x + fsum v x) = fsum u x + fsum v x) := by
  set L1c : Fin n → L1 (Freq n) F := fun j => ofTc W_pos (ℓ1 j) (hℓ1 j) with hL1c
  set L2c : Fin n → Fin n → L1 (Freq n) F := fun i j => ofTc W_pos (ℓ2 i j) (hℓ2 i j) with hL2c
  have e1 : ∀ j, tc W (L1c j) = ℓ1 j := fun j => funext (tc_ofTc W_pos _ _)
  have e2 : ∀ i j, tc W (L2c i j) = ℓ2 i j := fun i j => funext (tc_ofTc W_pos _ _)
  obtain ⟨ε, hε, C, H⟩ := exists_fixedPoint dot L1c L2c
  refine ⟨ε, hε, C, fun h hh hhs hhε => ?_⟩
  set hL : Fin n → Fin n → L1 (Freq n) ℂ := fun i j => ofTc W_pos (h i j) (hh i j) with hhL
  have e3 : ∀ i j, tc W (hL i j) = h i j := fun i j => funext (tc_ofTc W_pos _ _)
  have hLs : ∀ i j, hL i j = hL j i := fun i j =>
    ext_tc W_pos fun k => by rw [e3, e3, hhs i j]
  have hLn : ∀ i j, ‖hL i j‖ < ε := fun i j => by
    rw [norm_eq_tc W_pos, e3]
    exact hhε i j
  obtain ⟨v, hvf, hvC, hvσ⟩ := H hL hLn
  have hvW := summable_tc W_pos v
  refine ⟨tc W v, hvW, fun δ hδ => ?_, fun x i j => ?_, fun t R hR su s1 s2 s3 => ?_,
    fun cF hc hcd su s1 s2 s3 => ?_⟩
  · rw [← norm_eq_tc W_pos]
    refine hvC δ fun i j => ?_
    rw [norm_eq_tc W_pos, e3]
    exact hδ i j
  · have := metric_identity dot hsymm u hu L1c L2c hL v hvf hLs
      (fun x p q => by rw [fev_apply, e1]; exact hd1 x p q)
      (fun x p q r => by rw [fev_apply, e2]; exact hd2 x p q r)
      (fun x p q r => by rw [fev_apply, e1]; exact hd3 x p q r)
      (fun x p q r s => by rw [fev_apply, e2]; exact hd4 x p q r s) x i j
    rw [e3] at this
    exact this
  · have hfix := hvσ (transSymm dot t R hR)
      (fun j => CoeffSymm.actF_eq_of_tc _ _ fun k => by rw [e1]; exact s1 j k)
      (fun i j => CoeffSymm.actF_eq_of_tc _ _ fun k => by rw [e2]; exact s2 i j k)
      (fun i j => CoeffSymm.actC_eq_of_tc _ _ fun k => by rw [e3]; exact s3 i j k)
    have hk : ∀ k, ef k (-t) • R (tc W v k) = tc W v k := fun k =>
      CoeffSymm.tc_of_actF_eq _ v hfix k
    refine ⟨hk, fun x => ?_⟩
    have a1 := fsum_translate R.toContinuousLinearMap t u (summable_of_W hu) su x
    have a2 := fsum_translate R.toContinuousLinearMap t (tc W v) (summable_of_W hvW) hk x
    rw [a1, a2, map_add]
    rfl
  · have hfix := hvσ (conjSymm dot cF hc hcd)
      (fun j => CoeffSymm.actF_eq_of_tc _ _ fun k => by rw [e1]; exact s1 j k)
      (fun i j => CoeffSymm.actF_eq_of_tc _ _ fun k => by rw [e2]; exact s2 i j k)
      (fun i j => CoeffSymm.actC_eq_of_tc _ _ fun k => by rw [e3]; exact s3 i j k)
    have hk : ∀ k, cF (tc W v (-k)) = tc W v k := fun k =>
      CoeffSymm.tc_of_actF_eq _ v hfix k
    refine ⟨hk, fun x => ?_⟩
    have a1 := fsum_conj cF.toContinuousLinearMap hc u (summable_of_W hu) su x
    have a2 := fsum_conj cF.toContinuousLinearMap hc (tc W v) (summable_of_W hvW) hk x
    rw [map_add]
    exact congrArg₂ (· + ·) a1 a2

end EquivEmbed.Torus
