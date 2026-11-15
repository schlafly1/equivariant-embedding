/-
Copyright (c) 2026 Roger Schlafly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roger Schlafly
-/
module

public import EquivEmbed.Torus.Main

/-!
# An example: the circle

The hypotheses of `torus_perturbation` are satisfiable.  For `n = 1` and `F = ℂ × ℂ` with
`dot z w = z.1 * w.1 + z.2 * w.2`, the map

  `u x = (exp(i x), exp(-i x))`

is the unit circle `(cos x, sin x)` written in the basis `(1, i) / √2, (1, -i) / √2` of `ℂ²`.
It has the dual frame

  `ℓ1 x = (-(i/2) exp(-i x), (i/2) exp(i x))`,   `ℓ2 x = (-(1/2) exp(-i x), -(1/2) exp(i x))`.

`circle_dual_frame` checks the hypotheses `hd1`–`hd4`, and `circle_perturbation` is the resulting
instance of the theorem.
-/

@[expose] public section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.deprecated false

namespace EquivEmbed.Torus.Example

open EquivEmbed.Torus

/-- The bilinear form `z.1 * w.1 + z.2 * w.2` on `ℂ × ℂ`. -/
noncomputable def dot2 : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) →L[ℂ] ℂ :=
  (ContinuousLinearMap.mul ℂ ℂ).bilinearComp (ContinuousLinearMap.fst ℂ ℂ ℂ)
      (ContinuousLinearMap.fst ℂ ℂ ℂ)
    + (ContinuousLinearMap.mul ℂ ℂ).bilinearComp (ContinuousLinearMap.snd ℂ ℂ ℂ)
      (ContinuousLinearMap.snd ℂ ℂ ℂ)

lemma dot2_apply (z w : ℂ × ℂ) : dot2 z w = z.1 * w.1 + z.2 * w.2 := by simp [dot2]

lemma dot2_symm (z w : ℂ × ℂ) : dot2 z w = dot2 w z := by
  rw [dot2_apply, dot2_apply]
  ring

/-- The frequency `1`. -/
def k1 : Freq 1 := fun _ => 1

/-- The frequency `-1`. -/
def km : Freq 1 := fun _ => -1

/-- The coefficient family with value `A` at frequency `1` and `B` at frequency `-1`. -/
def pair (A B : ℂ × ℂ) (k : Freq 1) : ℂ × ℂ :=
  if k 0 = 1 then A else if k 0 = -1 then B else 0

lemma pair_support (A B : ℂ × ℂ) (k : Freq 1) (hk : k ∉ ({k1, km} : Finset (Freq 1))) :
    pair A B k = 0 := by
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
  have h1 : k 0 ≠ 1 := fun h => hk.1 (funext fun i => by
    rw [Subsingleton.elim i 0]
    simpa [k1] using h)
  have h2 : k 0 ≠ -1 := fun h => hk.2 (funext fun i => by
    rw [Subsingleton.elim i 0]
    simpa [km] using h)
  simp [pair, h1, h2]

lemma summable_pair (A B : ℂ × ℂ) : Summable fun k => W k * ‖pair A B k‖ :=
  summable_of_ne_finset_zero (s := {k1, km}) fun k hk => by
    rw [pair_support A B k hk]
    simp

lemma ef_k1 (x : Fin 1 → ℝ) : ef k1 x = Complex.exp (Complex.I * x 0) := by simp [ef, k1]

lemma ef_km (x : Fin 1 → ℝ) : ef km x = Complex.exp (-(Complex.I * x 0)) := by simp [ef, km]

lemma fsum_pair (A B : ℂ × ℂ) (x : Fin 1 → ℝ) :
    fsum (pair A B) x
      = Complex.exp (Complex.I * x 0) • A + Complex.exp (-(Complex.I * x 0)) • B := by
  have hne : k1 ≠ km := fun h => by
    have := congrFun h 0
    simp [k1, km] at this
  rw [fsum, tsum_eq_sum (s := {k1, km}) (fun k hk => by rw [pair_support A B k hk, smul_zero]),
    Finset.sum_pair hne, ef_k1, ef_km]
  simp [pair, k1, km]

lemma dc_pair (A B : ℂ × ℂ) : dc 0 (pair A B) = pair (Complex.I • A) ((-Complex.I) • B) := by
  funext k
  unfold dc pair
  split_ifs with h1 h2
  · simp [h1]
  · simp [h2]
  · simp

/-- The Fourier coefficients of `u x = (exp(i x), exp(-i x))`. -/
def u : Freq 1 → ℂ × ℂ := pair (1, 0) (0, 1)

/-- The Fourier coefficients of `ℓ1`. -/
noncomputable def ℓ1 : Freq 1 → ℂ × ℂ := pair (0, Complex.I / 2) (-(Complex.I / 2), 0)

/-- The Fourier coefficients of `ℓ2`. -/
noncomputable def ℓ2 : Freq 1 → ℂ × ℂ := pair (0, -(1 / 2)) (-(1 / 2), 0)

lemma pd_u (p : Fin 1) (x : Fin 1 → ℝ) :
    pd p (fsum u) x = Complex.exp (Complex.I * x 0) • (Complex.I • ((1 : ℂ), (0 : ℂ)))
      + Complex.exp (-(Complex.I * x 0)) • ((-Complex.I) • ((0 : ℂ), (1 : ℂ))) := by
  rw [Subsingleton.elim p 0, u, pd_fsum_of_W (summable_pair _ _) 0, dc_pair, fsum_pair]

lemma pd_pd_u (p q : Fin 1) (x : Fin 1 → ℝ) :
    pd p (pd q (fsum u)) x
      = Complex.exp (Complex.I * x 0) • (Complex.I • Complex.I • ((1 : ℂ), (0 : ℂ)))
        + Complex.exp (-(Complex.I * x 0))
          • ((-Complex.I) • (-Complex.I) • ((0 : ℂ), (1 : ℂ))) := by
  rw [Subsingleton.elim p 0, Subsingleton.elim q 0, u, pd_pd_fsum_of_W (summable_pair _ _) 0 0,
    dc_pair, dc_pair, fsum_pair]

lemma exp_mul_exp_neg (z : ℂ) : Complex.exp z * Complex.exp (-z) = 1 := by
  rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

/-- The circle is free: `(ℓ1, ℓ2)` is a dual frame of the first and second derivatives of `u`. -/
theorem circle_dual_frame :
    (∀ (x : Fin 1 → ℝ) (p q : Fin 1),
      dot2 (pd p (fsum u) x) (fsum ℓ1 x) = if p = q then 1 else 0) ∧
    (∀ (x : Fin 1 → ℝ) (p : Fin 1), dot2 (pd p (fsum u) x) (fsum ℓ2 x) = 0) ∧
    (∀ (x : Fin 1 → ℝ) (p q : Fin 1), dot2 (pd p (pd q (fsum u)) x) (fsum ℓ1 x) = 0) ∧
    (∀ (x : Fin 1 → ℝ) (p q : Fin 1), dot2 (pd p (pd q (fsum u)) x) (fsum ℓ2 x) = 1) := by
  refine ⟨fun x p q => ?_, fun x p => ?_, fun x p q => ?_, fun x p q => ?_⟩
  · have hE := exp_mul_exp_neg (Complex.I * x 0)
    rw [pd_u, ℓ1, fsum_pair, dot2_apply, if_pos (Subsingleton.elim p q)]
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    linear_combination (-(Complex.exp (Complex.I * x 0) * Complex.exp (-(Complex.I * x 0))))
      * Complex.I_sq + hE
  · have hE := exp_mul_exp_neg (Complex.I * x 0)
    rw [pd_u, ℓ2, fsum_pair, dot2_apply]
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  · have hE := exp_mul_exp_neg (Complex.I * x 0)
    rw [pd_pd_u, ℓ1, fsum_pair, dot2_apply]
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    ring
  · have hE := exp_mul_exp_neg (Complex.I * x 0)
    rw [pd_pd_u, ℓ2, fsum_pair, dot2_apply]
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]
    linear_combination (-(Complex.exp (Complex.I * x 0) * Complex.exp (-(Complex.I * x 0))))
      * Complex.I_sq + hE

/-- **The perturbation theorem for the circle.**  An instance of `torus_perturbation` in which
all hypotheses have been checked: every small `h` in the Wiener algebra is realized by a
perturbation `u + v` of the unit circle, `⟨(u + v)', (u + v)'⟩ = ⟨u', u'⟩ + h`. -/
theorem circle_perturbation :
    ∃ ε > 0, ∃ C : ℝ, ∀ h : Freq 1 → ℂ, (Summable fun k => W k * ‖h k‖) →
      (∑' k, W k * ‖h k‖ < ε) →
      ∃ v : Freq 1 → ℂ × ℂ, (Summable fun k => W k * ‖v k‖) ∧
        (∑' k, W k * ‖v k‖ ≤ C * ∑' k, W k * ‖h k‖) ∧
        ∀ x : Fin 1 → ℝ, dot2 (pd 0 (fun y => fsum u y + fsum v y) x)
            (pd 0 (fun y => fsum u y + fsum v y) x)
          = dot2 (pd 0 (fsum u) x) (pd 0 (fsum u) x) + fsum h x := by
  obtain ⟨d1, d2, d3, d4⟩ := circle_dual_frame
  obtain ⟨ε, hε, C, H⟩ := torus_perturbation dot2 dot2_symm u (summable_pair _ _)
    (fun _ => ℓ1) (fun _ => summable_pair _ _) (fun _ _ => ℓ2) (fun _ _ => summable_pair _ _)
    (fun x p q => d1 x p q) (fun x p q r => d2 x p) (fun x p q r => d3 x p q)
    (fun x p q r s => by
      rw [d4 x p q, if_pos (Subsingleton.elim p r), if_pos (Subsingleton.elim q s),
        if_pos (Subsingleton.elim p s), if_pos (Subsingleton.elim q r)]
      norm_num)
  refine ⟨ε, hε, C, fun h hh hε' => ?_⟩
  obtain ⟨v, hv, hvC, hmet, -, -⟩ := H (fun _ _ => h) (fun _ _ => hh) (fun _ _ => rfl)
    (fun _ _ => hε')
  exact ⟨v, hv, hvC _ (fun _ _ => le_refl _), fun x => hmet x 0 0⟩

end EquivEmbed.Torus.Example
