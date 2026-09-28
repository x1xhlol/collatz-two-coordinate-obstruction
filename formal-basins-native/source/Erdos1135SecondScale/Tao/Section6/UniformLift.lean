/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Fourier.OscillationAlgebra
import Erdos1135SecondScale.Tao.Section6.ConductorProjectivity

/-!
# Normalized Cross-Modulus Lifts

This leaf places a mass vector on `ZMod (3^r)` into a larger ambient
`ZMod (3^n)` with the normalization required to preserve its exact L1 norm.
It also identifies the normalized lift of the lower Syracuse law with the
fiber average of the higher Syracuse law.  Adjacent telescoping is left to a
separate consumer.
-/

open scoped BigOperators

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

/-- Projection through an intermediate power of three is the direct
projection. -/
theorem taoZModThreeProjection_comp
    {r s n : ℕ} (hrs : r ≤ s) (hsn : s ≤ n) :
    (taoZModThreeProjection hrs).comp (taoZModThreeProjection hsn) =
      taoZModThreeProjection (hrs.trans hsn) := by
  unfold taoZModThreeProjection
  simpa using ZMod.castHom_comp
    (Nat.pow_dvd_pow 3 hrs) (Nat.pow_dvd_pow 3 hsn)

theorem taoZModThreeProjection_comp_apply
    {r s n : ℕ} (hrs : r ≤ s) (hsn : s ≤ n) (y : ZMod (3 ^ n)) :
    taoZModThreeProjection hrs (taoZModThreeProjection hsn y) =
      taoZModThreeProjection (hrs.trans hsn) y := by
  exact DFunLike.congr_fun (taoZModThreeProjection_comp hrs hsn) y

/-- Projection to the same level is the identity. -/
theorem taoZModThreeProjection_refl (n : ℕ) :
    taoZModThreeProjection (le_refl n) = RingHom.id (ZMod (3 ^ n)) := by
  unfold taoZModThreeProjection
  exact ZMod.castHom_self

/-- The fiber-average scale at one level is one. -/
@[simp] theorem zmodPowFiberAverageScale_self (n : ℕ) :
    zmodPowFiberAverageScale n n = 1 := by
  unfold zmodPowFiberAverageScale
  field_simp

/-- Fiber-average scales compose along a chain of levels. -/
theorem zmodPowFiberAverageScale_comp (r s n : ℕ) :
    zmodPowFiberAverageScale s n * zmodPowFiberAverageScale r s =
      zmodPowFiberAverageScale r n := by
  unfold zmodPowFiberAverageScale
  have hs : ((3 ^ s : ℕ) : ℝ) ≠ 0 := by positivity
  have hn : ((3 ^ n : ℕ) : ℝ) ≠ 0 := by positivity
  field_simp [hs, hn]

/-- Normalized pullback from level `r` to a larger ambient level `n`. -/
noncomputable def taoZModPowUniformLift
    {r n : ℕ} (hrn : r ≤ n) (c : ZMod (3 ^ r) → ℝ) :
    ZMod (3 ^ n) → ℝ :=
  fun y => zmodPowFiberAverageScale r n *
    c (taoZModThreeProjection hrn y)

/-- Same-level lifting is pointwise identity. -/
@[simp] theorem taoZModPowUniformLift_refl
    (n : ℕ) (c : ZMod (3 ^ n) → ℝ) :
    taoZModPowUniformLift (le_refl n) c = c := by
  funext y
  simp [taoZModPowUniformLift, taoZModThreeProjection_refl]

/-- The lift is independent of the proof supplied for the level inequality. -/
theorem taoZModPowUniformLift_proof_irrel
    {r n : ℕ} (h h' : r ≤ n) (c : ZMod (3 ^ r) → ℝ) :
    taoZModPowUniformLift h c = taoZModPowUniformLift h' c := by
  rw [Subsingleton.elim h h']

/-- Any proof of the diagonal order gives the identity lift. -/
theorem taoZModPowUniformLift_self
    {n : ℕ} (h : n ≤ n) (c : ZMod (3 ^ n) → ℝ) :
    taoZModPowUniformLift h c = c := by
  rw [taoZModPowUniformLift_proof_irrel h (le_refl n)]
  exact taoZModPowUniformLift_refl n c

/-- Normalized lift commutes with addition. -/
theorem taoZModPowUniformLift_add
    {r n : ℕ} (hrn : r ≤ n)
    (c d : ZMod (3 ^ r) → ℝ) :
    taoZModPowUniformLift hrn (fun x => c x + d x) =
      fun y => taoZModPowUniformLift hrn c y +
        taoZModPowUniformLift hrn d y := by
  funext y
  simp [taoZModPowUniformLift, mul_add]

/-- Normalized lift commutes with subtraction of signed vectors. -/
theorem taoZModPowUniformLift_sub
    {r n : ℕ} (hrn : r ≤ n)
    (c d : ZMod (3 ^ r) → ℝ) :
    taoZModPowUniformLift hrn (fun x => c x - d x) =
      fun y => taoZModPowUniformLift hrn c y -
        taoZModPowUniformLift hrn d y := by
  funext y
  simp [taoZModPowUniformLift, mul_sub]

/-- Two normalized lifts along a chain equal the direct lift. -/
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

/-- Every projection fiber has the expected power-of-three cardinality. -/
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

/-- Normalized lift preserves the exact L1 norm. -/
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

/-- Normalized lift is an exact L1 distance isometry. -/
theorem taoZModPowUniformLift_l1_isometry
    {r n : ℕ} (hrn : r ≤ n)
    (c d : ZMod (3 ^ r) → ℝ) :
    (∑ y : ZMod (3 ^ n),
      |taoZModPowUniformLift hrn c y -
        taoZModPowUniformLift hrn d y|) =
      ∑ x : ZMod (3 ^ r), |c x - d x| := by
  calc
    (∑ y : ZMod (3 ^ n),
        |taoZModPowUniformLift hrn c y -
          taoZModPowUniformLift hrn d y|) =
        ∑ y : ZMod (3 ^ n),
          |taoZModPowUniformLift hrn (fun x => c x - d x) y| := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [congrFun (taoZModPowUniformLift_sub hrn c d) y]
    _ = ∑ x : ZMod (3 ^ r), |c x - d x| :=
      taoZModPowUniformLift_sum_abs hrn (fun x => c x - d x)

/-- A unit atom retains exact L1 mass under the first nontrivial lift. -/
theorem taoZModPowUniformLift_unitAtom_one_two :
    (∑ y : ZMod (3 ^ 2),
      |taoZModPowUniformLift (show 1 ≤ 2 by omega)
        (fun x : ZMod (3 ^ 1) => if x = 0 then 1 else 0) y|) = 1 := by
  rw [taoZModPowUniformLift_sum_abs]
  calc
    (∑ x : ZMod (3 ^ 1), |if x = 0 then 1 else 0|) =
        ∑ x : ZMod (3 ^ 1), if x = 0 then (1 : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro x hx
      by_cases h : x = 0 <;> simp [h]
    _ = 1 := by
      simpa using
        (Fintype.sum_ite_eq' (0 : ZMod (3 ^ 1)) (fun _ => (1 : ℝ)))

/-- Bottom-level lifting also preserves the exact L1 norm. -/
theorem taoZModPowUniformLift_zero_sum_abs
    (n : ℕ) (c : ZMod (3 ^ 0) → ℝ) :
    (∑ y : ZMod (3 ^ n),
      |taoZModPowUniformLift (Nat.zero_le n) c y|) =
      ∑ x : ZMod (3 ^ 0), |c x| :=
  taoZModPowUniformLift_sum_abs (Nat.zero_le n) c

/-- Concrete three-level transitivity canary. -/
theorem taoZModPowUniformLift_one_two_three
    (c : ZMod (3 ^ 1) → ℝ) :
    taoZModPowUniformLift (show 2 ≤ 3 by omega)
        (taoZModPowUniformLift (show 1 ≤ 2 by omega) c) =
      taoZModPowUniformLift (show 1 ≤ 3 by omega) c := by
  exact taoZModPowUniformLift_trans
    (show 1 ≤ 2 by omega) (show 2 ≤ 3 by omega) c

/-- Projectivity identifies a higher-level Syracuse fiber mass with the
corresponding lower-level atom. -/
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

/-- The repeated-ambient fiber average of the level-`n` Syracuse law is the
normalized lift of its level-`r` marginal. -/
theorem zmodPowFiberAverage_syracPMFMassVector_eq_uniformLift
    {r n : ℕ} (hrn : r ≤ n) :
    zmodPowFiberAverage r n (syracPMFMassVector n) =
      taoZModPowUniformLift hrn (syracPMFMassVector r) := by
  funext y
  unfold zmodPowFiberAverage taoZModPowUniformLift
  rw [zmodPowFiberSum_syracPMFMassVector_eq_projection hrn y]

/-- One-step source-projectivity canary. -/
theorem zmodPowFiberAverage_syracPMFMassVector_one_two :
    zmodPowFiberAverage 1 2 (syracPMFMassVector 2) =
      taoZModPowUniformLift (show 1 ≤ 2 by omega)
        (syracPMFMassVector 1) := by
  exact zmodPowFiberAverage_syracPMFMassVector_eq_uniformLift
    (show 1 ≤ 2 by omega)

end

end Tao
end Erdos1135SecondScale
