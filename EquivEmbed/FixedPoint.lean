/-
Copyright (c) 2026 Roger Schlafly. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Roger Schlafly
-/
module

public import Mathlib.Topology.MetricSpace.Contracting
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Topology.Algebra.ConstMulAction
public import Mathlib.Topology.MetricSpace.IsometricSMul

/-!
# The equivariant Günther fixed point theorem

Günther's proof of the Nash embedding theorem reduces the isometric embedding equation
`F(u₀ + v) = F(u₀) + h` to a fixed point problem of the form

  `v = m + Q v`,

on a Banach space `E` of Hölder maps, where `m = 𝓜 h` is linear in the metric defect `h`
and `Q` is quadratic (`Q v = 𝓑 (v, v)` for a bounded bilinear `𝓑`).  The key analytic point
of Günther's method is that `Q` loses no derivatives, so the plain contraction mapping
theorem applies.

In this file we prove the abstract statements used in the equivariant version:

* `EquivEmbed.exists_unique_fixedPoint_quadratic`: if `Q 0 = 0` and
  `‖Q v - Q w‖ ≤ C (‖v‖ + ‖w‖) ‖v - w‖`, and `4 C ‖m‖ < 1`, then `v = m + Q v` has a unique
  solution in the closed ball of radius `2 ‖m‖`.
* `EquivEmbed.fixedPoint_quadratic_smul_eq`: if moreover a monoid `G` acts on `E` by
  isometric additive maps, `m` is `G`-fixed and `Q` is `G`-equivariant, then the solution is
  `G`-fixed.  (No averaging of the nonlinear solution is involved.)
* bilinear versions `EquivEmbed.exists_unique_fixedPoint_bilinear` and
  `EquivEmbed.fixedPoint_bilinear_smul_eq`.
-/

@[expose] public section

open Metric Set

namespace EquivEmbed

variable {E : Type*} [NormedAddCommGroup E]

/-- The quadratic estimate used in Günther's method. -/
def QuadraticBound (Q : E → E) (C : ℝ) : Prop :=
  ∀ v w : E, ‖Q v - Q w‖ ≤ C * (‖v‖ + ‖w‖) * ‖v - w‖

section quadratic

variable {Q : E → E} {C : ℝ}

lemma QuadraticBound.norm_le (hQ : QuadraticBound Q C) (hQ0 : Q 0 = 0) (v : E) :
    ‖Q v‖ ≤ C * ‖v‖ * ‖v‖ := by
  simpa [hQ0] using hQ v 0

/-- The map `v ↦ m + Q v` sends the closed ball of radius `2‖m‖` into itself. -/
lemma mapsTo_closedBall (hC : 0 ≤ C) (hQ : QuadraticBound Q C) (hQ0 : Q 0 = 0) {m : E}
    (hm : 4 * C * ‖m‖ ≤ 1) :
    MapsTo (fun v => m + Q v) (closedBall 0 (2 * ‖m‖)) (closedBall 0 (2 * ‖m‖)) := by
  intro v hv
  rw [mem_closedBall_zero_iff] at hv ⊢
  have h1 : ‖Q v‖ ≤ C * ‖v‖ * ‖v‖ := hQ.norm_le hQ0 v
  have hv0 : 0 ≤ ‖v‖ := norm_nonneg v
  have h2 : C * ‖v‖ * ‖v‖ ≤ C * (2 * ‖m‖) * (2 * ‖m‖) := by
    have := mul_le_mul hv hv hv0 (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left this hC]
  calc ‖m + Q v‖ ≤ ‖m‖ + ‖Q v‖ := norm_add_le _ _
    _ ≤ ‖m‖ + C * (2 * ‖m‖) * (2 * ‖m‖) := by linarith
    _ ≤ 2 * ‖m‖ := by nlinarith [norm_nonneg m]

/-- On the closed ball of radius `2‖m‖`, the map `v ↦ m + Q v` is Lipschitz with
constant `4 C ‖m‖`. -/
lemma dist_le_on_closedBall (hC : 0 ≤ C) (hQ : QuadraticBound Q C) {m v w : E}
    (hv : v ∈ closedBall (0 : E) (2 * ‖m‖)) (hw : w ∈ closedBall (0 : E) (2 * ‖m‖)) :
    ‖(m + Q v) - (m + Q w)‖ ≤ 4 * C * ‖m‖ * ‖v - w‖ := by
  rw [mem_closedBall_zero_iff] at hv hw
  have h := hQ v w
  have hsum : C * (‖v‖ + ‖w‖) ≤ 4 * C * ‖m‖ := by nlinarith
  calc ‖(m + Q v) - (m + Q w)‖ = ‖Q v - Q w‖ := by congr 1; abel
    _ ≤ C * (‖v‖ + ‖w‖) * ‖v - w‖ := h
    _ ≤ 4 * C * ‖m‖ * ‖v - w‖ := mul_le_mul_of_nonneg_right hsum (norm_nonneg _)

/-- Uniqueness of small solutions of `v = m + Q v`. -/
lemma fixedPoint_quadratic_unique (hC : 0 ≤ C) (hQ : QuadraticBound Q C) {m : E}
    (hm : 4 * C * ‖m‖ < 1) {v w : E}
    (hv : v ∈ closedBall (0 : E) (2 * ‖m‖)) (hvf : v = m + Q v)
    (hw : w ∈ closedBall (0 : E) (2 * ‖m‖)) (hwf : w = m + Q w) : v = w := by
  have h := dist_le_on_closedBall hC hQ hv hw
  rw [← hvf, ← hwf] at h
  have hn : ‖v - w‖ = 0 := by
    have h0 : 0 ≤ ‖v - w‖ := norm_nonneg _
    nlinarith
  exact sub_eq_zero.mp (norm_eq_zero.mp hn)

variable [CompleteSpace E]

/-- **Abstract Günther lemma.** If `Q 0 = 0`, `Q` satisfies the quadratic estimate with
constant `C ≥ 0`, and `4 C ‖m‖ < 1`, then the equation `v = m + Q v` has a unique solution in
the closed ball of radius `2‖m‖`. -/
theorem exists_unique_fixedPoint_quadratic (hC : 0 ≤ C) (hQ : QuadraticBound Q C)
    (hQ0 : Q 0 = 0) {m : E} (hm : 4 * C * ‖m‖ < 1) :
    ∃! v : E, v ∈ closedBall (0 : E) (2 * ‖m‖) ∧ v = m + Q v := by
  set s := closedBall (0 : E) (2 * ‖m‖) with hs
  have hmaps := mapsTo_closedBall hC hQ hQ0 hm.le
  have : CompleteSpace s := isClosed_closedBall.completeSpace_coe
  have : Nonempty s := ⟨⟨0, by simp [hs]⟩⟩
  set f : s → s := hmaps.restrict _ _ _ with hf
  set K : NNReal := ⟨4 * C * ‖m‖, by positivity⟩ with hK
  have hcontr : ContractingWith K f := by
    refine ⟨by rw [← NNReal.coe_lt_coe]; exact hm, ?_⟩
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    simp only [Subtype.dist_eq, dist_eq_norm, hf, MapsTo.val_restrict_apply, hK]
    exact dist_le_on_closedBall hC hQ x.2 y.2
  obtain ⟨⟨v, hvs⟩, hv⟩ : ∃ x : s, f x = x := ⟨_, hcontr.fixedPoint_isFixedPt⟩
  have hvf : v = m + Q v := by
    have := congrArg Subtype.val hv
    simpa [hf] using this.symm
  exact ⟨v, ⟨hvs, hvf⟩, fun w ⟨hws, hwf⟩ =>
    fixedPoint_quadratic_unique hC hQ hm hws hwf hvs hvf⟩

omit [CompleteSpace E] in
/-- **Equivariant Günther lemma.** Suppose in addition that a monoid `G` acts on `E` by
isometric additive maps, that `m` is `G`-fixed and that `Q` is `G`-equivariant.  Then the
unique small solution of `v = m + Q v` is `G`-fixed. -/
theorem fixedPoint_quadratic_smul_eq {G : Type*} [Monoid G] [DistribMulAction G E]
    [IsIsometricSMul G E] (hC : 0 ≤ C) (hQ : QuadraticBound Q C) {m : E}
    (hm : 4 * C * ‖m‖ < 1) (hmG : ∀ g : G, g • m = m)
    (hQG : ∀ (g : G) (v : E), Q (g • v) = g • Q v) {v : E}
    (hvs : v ∈ closedBall (0 : E) (2 * ‖m‖)) (hvf : v = m + Q v) (g : G) : g • v = v := by
  refine fixedPoint_quadratic_unique hC hQ hm ?_ ?_ hvs hvf
  · rw [mem_closedBall_zero_iff] at hvs ⊢
    have : ‖g • v‖ = ‖v‖ := by
      simpa [dist_zero_right, smul_zero] using dist_smul g v (0 : E)
    rwa [this]
  · conv_lhs => rw [hvf]
    rw [smul_add, hmG, hQG]

/-- Existence of a small `G`-fixed solution, packaged. -/
theorem exists_fixedPoint_quadratic_invariant {G : Type*} [Monoid G] [DistribMulAction G E]
    [IsIsometricSMul G E] (hC : 0 ≤ C) (hQ : QuadraticBound Q C) (hQ0 : Q 0 = 0) {m : E}
    (hm : 4 * C * ‖m‖ < 1) (hmG : ∀ g : G, g • m = m)
    (hQG : ∀ (g : G) (v : E), Q (g • v) = g • Q v) :
    ∃ v : E, ‖v‖ ≤ 2 * ‖m‖ ∧ v = m + Q v ∧ ∀ g : G, g • v = v := by
  obtain ⟨v, ⟨hvs, hvf⟩, -⟩ := exists_unique_fixedPoint_quadratic hC hQ hQ0 hm
  exact ⟨v, mem_closedBall_zero_iff.mp hvs, hvf,
    fixedPoint_quadratic_smul_eq hC hQ hm hmG hQG hvs hvf⟩

end quadratic

section bilinear

variable [NormedSpace ℝ E]

/-- A bounded bilinear map `B` gives a quadratic map `v ↦ B v v` satisfying the
quadratic estimate with constant `‖B‖`. -/
lemma quadraticBound_bilinear (B : E →L[ℝ] E →L[ℝ] E) :
    QuadraticBound (fun v => B v v) ‖B‖ := by
  intro v w
  have hsplit : B v v - B w w = B v (v - w) + B (v - w) w := by
    simp only [map_sub, sub_apply]; abel
  rw [hsplit]
  calc ‖B v (v - w) + B (v - w) w‖ ≤ ‖B v (v - w)‖ + ‖B (v - w) w‖ := norm_add_le _ _
    _ ≤ ‖B‖ * ‖v‖ * ‖v - w‖ + ‖B‖ * ‖v - w‖ * ‖w‖ :=
        add_le_add (B.le_opNorm₂ _ _) (B.le_opNorm₂ _ _)
    _ = ‖B‖ * (‖v‖ + ‖w‖) * ‖v - w‖ := by ring

variable [CompleteSpace E]

/-- Günther's fixed point problem `v = m + B(v, v)` with `B` bounded bilinear and
`4 ‖B‖ ‖m‖ < 1` has a unique solution with `‖v‖ ≤ 2 ‖m‖`. -/
theorem exists_unique_fixedPoint_bilinear (B : E →L[ℝ] E →L[ℝ] E) {m : E}
    (hm : 4 * ‖B‖ * ‖m‖ < 1) :
    ∃! v : E, ‖v‖ ≤ 2 * ‖m‖ ∧ v = m + B v v := by
  simpa only [mem_closedBall_zero_iff] using
    exists_unique_fixedPoint_quadratic (norm_nonneg B) (quadraticBound_bilinear B)
      (by simp) hm

/-- **Equivariant Günther lemma, bilinear form.** If `G` acts on `E` by linear isometries,
`m` is `G`-fixed, `B` is `G`-equivariant and `4 ‖B‖ ‖m‖ < 1`, then there is a `G`-fixed
solution of `v = m + B(v, v)` with `‖v‖ ≤ 2 ‖m‖`, and it is the unique solution in that
ball. -/
theorem exists_fixedPoint_bilinear_invariant {G : Type*} [Monoid G] [DistribMulAction G E]
    [IsIsometricSMul G E] (B : E →L[ℝ] E →L[ℝ] E) {m : E} (hm : 4 * ‖B‖ * ‖m‖ < 1)
    (hmG : ∀ g : G, g • m = m) (hBG : ∀ (g : G) (v w : E), B (g • v) (g • w) = g • B v w) :
    ∃ v : E, ‖v‖ ≤ 2 * ‖m‖ ∧ v = m + B v v ∧ ∀ g : G, g • v = v :=
  exists_fixedPoint_quadratic_invariant (norm_nonneg B) (quadraticBound_bilinear B)
    (by simp) hm hmG (fun g v => hBG g v v)

end bilinear

end EquivEmbed
