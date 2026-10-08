/-
Compatibility modification, 8 October 2026: proof elaboration and unused bound-variable names only.
See provenance/envelope-linter-patches.json for exact source hashes and patches.
-/
/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Fourier.OscillationAlgebra
import Erdos1135Predecessor.Tao.Section6.ConductorProjectivity

open scoped BigOperators

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

theorem taoZModThreeProjection_comp
    {r s n : ℕ} (hrs : r ≤ s) (hsn : s ≤ n) :
    (taoZModThreeProjection hrs).comp (taoZModThreeProjection hsn) =
      taoZModThreeProjection (hrs.trans hsn) := by
  unfold taoZModThreeProjection
  simp

theorem taoZModThreeProjection_comp_apply
    {r s n : ℕ} (hrs : r ≤ s) (hsn : s ≤ n) (y : ZMod (3 ^ n)) :
    taoZModThreeProjection hrs (taoZModThreeProjection hsn y) =
      taoZModThreeProjection (hrs.trans hsn) y := by
  exact DFunLike.congr_fun (taoZModThreeProjection_comp hrs hsn) y

theorem taoZModThreeProjection_refl (n : ℕ) :
    taoZModThreeProjection (le_refl n) = RingHom.id (ZMod (3 ^ n)) := by
  unfold taoZModThreeProjection
  exact ZMod.castHom_self

@[simp] theorem zmodPowFiberAverageScale_self (n : ℕ) :
    zmodPowFiberAverageScale n n = 1 := by
  unfold zmodPowFiberAverageScale
  field_simp

theorem zmodPowFiberAverageScale_comp (r s n : ℕ) :
    zmodPowFiberAverageScale s n * zmodPowFiberAverageScale r s =
      zmodPowFiberAverageScale r n := by
  unfold zmodPowFiberAverageScale
  have hs : ((3 ^ s : ℕ) : ℝ) ≠ 0 := by positivity
  have hn : ((3 ^ n : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hs, hn]

noncomputable def taoZModPowUniformLift
    {r n : ℕ} (hrn : r ≤ n) (c : ZMod (3 ^ r) → ℝ) :
    ZMod (3 ^ n) → ℝ :=
  fun y => zmodPowFiberAverageScale r n *
    c (taoZModThreeProjection hrn y)

@[simp] theorem taoZModPowUniformLift_refl
    (n : ℕ) (c : ZMod (3 ^ n) → ℝ) :
    taoZModPowUniformLift (le_refl n) c = c := by
  funext y
  simp [taoZModPowUniformLift, taoZModThreeProjection_refl]

theorem taoZModPowUniformLift_sub
    {r n : ℕ} (hrn : r ≤ n)
    (c d : ZMod (3 ^ r) → ℝ) :
    taoZModPowUniformLift hrn (fun x => c x - d x) =
      fun y => taoZModPowUniformLift hrn c y -
        taoZModPowUniformLift hrn d y := by
  funext y
  simp [taoZModPowUniformLift, mul_sub]

theorem taoZModPowUniformLift_trans
    {r s n : ℕ} (hrs : r ≤ s) (hsn : s ≤ n)
    (c : ZMod (3 ^ r) → ℝ) :
    taoZModPowUniformLift hsn (taoZModPowUniformLift hrs c) =
      taoZModPowUniformLift (hrs.trans hsn) c := by
  funext y
  unfold taoZModPowUniformLift
  rw [taoZModThreeProjection_comp_apply hrs hsn]
  rw [← zmodPowFiberAverageScale_comp r s n]
  ring

theorem taoZModThreeProjection_fiber_card
    {r n : ℕ} (hrn : r ≤ n) (x : ZMod (3 ^ r)) :
    Fintype.card {y : ZMod (3 ^ n) |
      taoZModThreeProjection hrn y = x} = 3 ^ (n - r) := by
  let f := (taoZModThreeProjection hrn).toAddMonoidHom
  have hsurj : Function.Surjective f :=
    ZMod.ringHom_surjective (taoZModThreeProjection hrn)
  calc
    Fintype.card {y : ZMod (3 ^ n) |
        taoZModThreeProjection hrn y = x} =
        Fintype.card f.ker := by
      exact Fintype.card_congr (f.fiberEquivKerOfSurjective hsurj x)
    _ = 3 ^ (n - r) := by
      rw [← Nat.card_eq_fintype_card]
      exact zmodPowProjectionKer_card hrn

theorem taoZModPowUniformLift_sum_abs
    {r n : ℕ} (hrn : r ≤ n) (c : ZMod (3 ^ r) → ℝ) :
    (∑ y : ZMod (3 ^ n), |taoZModPowUniformLift hrn c y|) =
      ∑ x : ZMod (3 ^ r), |c x| := by
  classical
  let p : ZMod (3 ^ n) → ZMod (3 ^ r) :=
    fun y => taoZModThreeProjection hrn y
  have hscale : 0 ≤ zmodPowFiberAverageScale r n := by
    unfold zmodPowFiberAverageScale
    positivity
  have hcancel :
      zmodPowFiberAverageScale r n * (3 ^ (n - r) : ℝ) = 1 :=
    zmodPowFiberAverageScale_mul_card hrn
  calc
    (∑ y : ZMod (3 ^ n), |taoZModPowUniformLift hrn c y|) =
        ∑ x : ZMod (3 ^ r),
          ∑ y : {y : ZMod (3 ^ n) | p y = x},
            |taoZModPowUniformLift hrn c y.1| := by
      exact (Fintype.sum_fiberwise p
        (fun y => |taoZModPowUniformLift hrn c y|)).symm
    _ = ∑ x : ZMod (3 ^ r),
        ∑ _y : {y : ZMod (3 ^ n) | p y = x},
          zmodPowFiberAverageScale r n * |c x| := by
      apply Finset.sum_congr rfl
      intro x hx
      apply Finset.sum_congr rfl
      intro y hy
      have hproj : taoZModThreeProjection hrn y.1 = x := y.2
      simp only [taoZModPowUniformLift, abs_mul,
        abs_of_nonneg hscale, hproj]
    _ = ∑ x : ZMod (3 ^ r),
        ((Fintype.card {y : ZMod (3 ^ n) | p y = x} : ℕ) : ℝ) *
          (zmodPowFiberAverageScale r n * |c x|) := by
      apply Finset.sum_congr rfl
      intro x hx
      simp
    _ = ∑ x : ZMod (3 ^ r), |c x| := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [show Fintype.card {y : ZMod (3 ^ n) | p y = x} =
          3 ^ (n - r) by
        simpa [p] using taoZModThreeProjection_fiber_card hrn x]
      rw [Nat.cast_pow, Nat.cast_ofNat]
      calc
        (3 : ℝ) ^ (n - r) *
            (zmodPowFiberAverageScale r n * |c x|) =
          (zmodPowFiberAverageScale r n * (3 : ℝ) ^ (n - r)) *
            |c x| := by ring
        _ = |c x| := by rw [hcancel, one_mul]

theorem zmodPowFiberSum_syracPMFMassVector_eq_projection
    {r n : ℕ} (hrn : r ≤ n) (y : ZMod (3 ^ n)) :
    zmodPowFiberSum r n (syracPMFMassVector n) y =
      syracPMFMassVector r (taoZModThreeProjection hrn y) := by
  classical
  have hmap :
      (∑ x : ZMod (3 ^ n),
        if taoZModThreeProjection hrn y =
            taoZModThreeProjection hrn x then
          syracPMFMassVector n x else 0) =
        syracPMFMassVector r (taoZModThreeProjection hrn y) := by
    calc
      (∑ x : ZMod (3 ^ n),
          if taoZModThreeProjection hrn y =
              taoZModThreeProjection hrn x then
            syracPMFMassVector n x else 0) =
          (((syracPMF n).map (taoZModThreeProjection hrn))
            (taoZModThreeProjection hrn y)).toReal := by
        rw [pmf_map_apply_toReal_tsum]
        rw [tsum_fintype]
        rfl
      _ = syracPMFMassVector r (taoZModThreeProjection hrn y) := by
        rw [syracPMF_map_taoZModThreeProjection_eq_of_le hrn]
        rfl
  unfold zmodPowFiberSum
  calc
    (∑ x : ZMod (3 ^ n),
        if zmodSameResidueModPow r n x y then
          syracPMFMassVector n x else 0) =
      ∑ x : ZMod (3 ^ n),
        if taoZModThreeProjection hrn y =
            taoZModThreeProjection hrn x then
          syracPMFMassVector n x else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [zmodSameResidueModPow_iff_projection_eq hrn]
      by_cases hxy : taoZModThreeProjection hrn x =
          taoZModThreeProjection hrn y
      · rw [if_pos hxy, if_pos hxy.symm]
      · have hyx : ¬taoZModThreeProjection hrn y =
            taoZModThreeProjection hrn x := fun h => hxy h.symm
        rw [if_neg hxy, if_neg hyx]
    _ = syracPMFMassVector r (taoZModThreeProjection hrn y) := hmap

theorem zmodPowFiberAverage_syracPMFMassVector_eq_uniformLift
    {r n : ℕ} (hrn : r ≤ n) :
    zmodPowFiberAverage r n (syracPMFMassVector n) =
      taoZModPowUniformLift hrn (syracPMFMassVector r) := by
  funext y
  unfold zmodPowFiberAverage taoZModPowUniformLift
  rw [zmodPowFiberSum_syracPMFMassVector_eq_projection hrn y]

end

end Tao

end Erdos1135Predecessor
