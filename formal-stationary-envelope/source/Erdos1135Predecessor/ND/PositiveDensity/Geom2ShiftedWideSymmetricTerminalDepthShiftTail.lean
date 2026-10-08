/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricCoreBackwardMean

namespace Erdos1135Predecessor.ND.PositiveDensity

open scoped BigOperators

noncomputable section

def ndTerminalDepthShiftGood (b a s : ℕ) : Prop :=
  2 * s + ndBalancedTotal (b - s) + ndGeom2ShiftedWideSymmetricShiftRadius b ≤
    2 * b + ndBalancedTotal (s - b) + a + b / 8

theorem terminalDepthShift_firstCrossing_predecessor_lt
    {b a s : ℕ} {word : List ℕ+} (hlen : word.length = s)
    (hfirst : ndGeom2ShiftedWideSymmetricFirstCrossingAt b a s word) :
    Tao.taoTupleWeight (word.take (s - 1)) + ndBalancedTotal (b - s) +
        ndGeom2ShiftedWideSymmetricShiftRadius b <
      2 * b + ndBalancedTotal (s - b) + a := by
  have h := ndGeom2ShiftedWideSymmetric_firstCrossing_overshoot_succ_le_terminal hlen hfirst
  have hw := Tao.taoTupleWeight_eq_dropLast_add_terminalValue word
  rw [List.dropLast_eq_take, hlen] at hw
  omega

theorem terminalDepthShift_bad_firstCrossing_abs_tail
    {b a s : ℕ} (hb : 200 ≤ b) {word : List ℕ+} (hlen : word.length = s)
    (hfirst : ndGeom2ShiftedWideSymmetricFirstCrossingAt b a s word)
    (hbad : ¬ndTerminalDepthShiftGood b a s) :
    (b : ℝ) / 16 < |Tao.taoGeom2CenteredListWeight (word.take (s - 1))| := by
  have hp := terminalDepthShift_firstCrossing_predecessor_lt hlen hfirst
  have hs := (Finset.mem_Icc.mp hfirst.1).1
  unfold ndTerminalDepthShiftGood at hbad
  have hnat : 16 * Tao.taoTupleWeight (word.take (s - 1)) + b < 32 * (s - 1) := by
    omega
  have hreal : (16 : ℝ) * Tao.taoTupleWeight (word.take (s - 1)) + b <
      32 * ((s - 1 : ℕ) : ℝ) := by exact_mod_cast hnat
  apply lt_of_lt_of_le _ (neg_le_abs _)
  unfold Tao.taoGeom2CenteredListWeight
  rw [List.length_take, hlen, Nat.min_eq_left (Nat.sub_le _ _)]
  linarith only [hreal]

private theorem terminalDepthShift_event_ne_top {Ω : Type*} (p : PMF Ω) (E : Set Ω) :
    p.toOuterMeasure E ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (by
    calc
      _ ≤ p.toOuterMeasure Set.univ := p.toOuterMeasure.mono (Set.subset_univ _)
      _ = 1 := (p.toOuterMeasure_apply_eq_one_iff Set.univ).2 (Set.subset_univ _))

theorem terminalDepthShift_prefix_absTailMass_le
    {b t : ℕ} (hb : 0 < b) (ht : 0 < t)
    (htH : t ≤ ndGeom2ShiftedWideSymmetricHorizon b) :
    ((Tao.geom2PNatListPMF (ndGeom2ShiftedWideSymmetricHorizon b)).toOuterMeasure
      {full | (b : ℝ) / 16 < |Tao.taoGeom2CenteredListWeight (full.take t)|}).toReal ≤
      2 * Real.exp (-(b : ℝ) / 16384) := by
  change ((Tao.geom2PNatListPMF (ndGeom2ShiftedWideSymmetricHorizon b)).toOuterMeasure
    ((fun full => full.take t) ⁻¹' {w | (b : ℝ) / 16 < |Tao.taoGeom2CenteredListWeight w|})).toReal ≤ _
  rw [geom2PNatListPMF_take_event_outerMeasure_toReal htH]
  have htail := Tao.geom2PNatListPMF_centeredWeight_absTail_le_min ht
    (by positivity : (0 : ℝ) < (b : ℝ) / 16)
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have htR : (0 : ℝ) < t := by exact_mod_cast ht
  have ht2 : (t : ℝ) ≤ 2 * b := by
    have hh := ndGeom2ShiftedWideSymmetricWidth_le_base b
    unfold ndGeom2ShiftedWideSymmetricHorizon at htH
    exact_mod_cast (show t ≤ 2 * b by omega)
  have hexp : (b : ℝ) / 16384 ≤
      min (((b : ℝ) / 16) ^ 2 / (32 * (t : ℝ))) (((b : ℝ) / 16) / 8) := by
    apply le_min
    · apply (le_div_iff₀ (by positivity : 0 < 32 * (t : ℝ))).2
      have hm := mul_le_mul_of_nonneg_left ht2 hbR.le
      nlinarith only [hm]
    · linarith only [hbR]
  exact htail.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (by linarith only [hexp])) (by norm_num))

def ndTerminalDepthShiftRejectedWords (b a K : ℕ) : Finset (List ℕ+) := by
  classical
  exact (ndShiftedReferenceSelectedWords b a K).filter
    fun w => ¬ndTerminalDepthShiftGood b a w.length

theorem terminalDepthShift_rejected_word_mass_le
    {b : ℕ} (hb : 200 ≤ b) (a K : ℕ) :
    (∑ w : ndTerminalDepthShiftRejectedWords b a K,
      (2 : ℝ) ^ (-(Tao.taoTupleWeight w.val : ℤ))) ≤
      (4 * (b : ℝ) + 4) * Real.exp (-(b : ℝ) / 16384) := by
  classical
  let I := ndTerminalDepthShiftRejectedWords b a K
  let H := ndGeom2ShiftedWideSymmetricHorizon b
  let p := Tao.geom2PNatListPMF H
  let F := fun w : I => {full : List ℕ+ | full.take w.val.length = w.val}
  let T := Finset.Icc 1 H
  let E := fun t => {full : List ℕ+ | (b : ℝ) / 16 <
    |Tao.taoGeom2CenteredListWeight (full.take t)|}
  have hword (w : I) : w.val ∈ ndShiftedReferenceSelectedWords b a K :=
    (Finset.mem_filter.mp w.property).1
  have hlen (w : I) : w.val.length ≤ H :=
    shiftedReferenceSelectedWords_length_le_horizon b a K ⟨w.val, hword w⟩
  have hdis : Set.PairwiseDisjoint (↑(Finset.univ : Finset I)) F := by
    intro w _ v _ hne
    change Disjoint (F w) (F v)
    rw [Set.disjoint_left]
    intro full hw hv
    exact shiftedReferenceSelectedWords_prefix_disjoint b a K
      ⟨w.val, hword w⟩ ⟨v.val, hword v⟩
      (by intro heq; exact hne (Subtype.ext (congrArg (fun z => z.val) heq))) full hw hv
  have hmass (w : I) : (p.toOuterMeasure (F w)).toReal =
      (2 : ℝ) ^ (-(Tao.taoTupleWeight w.val : ℤ)) := by
    change ((Tao.geom2PNatListPMF H).toOuterMeasure
      ((fun full => full.take w.val.length) ⁻¹' {w.val})).toReal = _
    rw [geom2PNatListPMF_take_event_outerMeasure_toReal (hlen w),
      PMF.toOuterMeasure_apply_singleton, referencePrefix_atom_eq]
  have hsum : (∑ w : I, (2 : ℝ) ^ (-(Tao.taoTupleWeight w.val : ℤ))) =
      (p.toOuterMeasure (⋃ w ∈ (Finset.univ : Finset I), F w)).toReal := by
    rw [Tao.taoPMFToOuterMeasure_biUnion_finset_eq_sum p _ _ hdis,
      ENNReal.toReal_sum (fun w _ => terminalDepthShift_event_ne_top p (F w))]
    exact Finset.sum_congr rfl (fun w _ => (hmass w).symm)
  have hsub : (⋃ w ∈ (Finset.univ : Finset I), F w) ⊆ ⋃ t ∈ T, E t := by
    intro full hf
    obtain ⟨w, hf⟩ := Set.mem_iUnion.mp hf
    obtain ⟨_, hw⟩ := Set.mem_iUnion.mp hf
    have he := (mem_shiftedReferenceSelectedWords_iff b a K w.val).mp (hword w)
    have hd := terminalDepthShift_bad_firstCrossing_abs_tail hb rfl he.1
      (Finset.mem_filter.mp w.property).2
    have hs := Finset.mem_Icc.mp he.1.1
    have ht : w.val.length - 1 ∈ T := by
      apply Finset.mem_Icc.mpr
      dsimp [H]
      unfold ndGeom2ShiftedWideSymmetricLower ndGeom2ShiftedWideSymmetricWidth at hs
      constructor <;> omega
    have htake : w.val.take (w.val.length - 1) = full.take (w.val.length - 1) := by
      have h := congrArg (List.take (w.val.length - 1)) hw
      simpa only [List.take_take, Nat.min_eq_left (Nat.sub_le _ _)] using h.symm
    rw [htake] at hd
    exact Set.mem_iUnion.mpr ⟨_, Set.mem_iUnion.mpr ⟨ht, hd⟩⟩
  rw [hsum]
  have hu := ENNReal.toReal_mono
    (ENNReal.sum_ne_top.mpr fun t _ => terminalDepthShift_event_ne_top p (E t))
    (MeasureTheory.measure_biUnion_finset_le (μ := p.toOuterMeasure) T E)
  rw [ENNReal.toReal_sum (fun t _ => terminalDepthShift_event_ne_top p (E t))] at hu
  calc
    _ ≤ (p.toOuterMeasure (⋃ t ∈ T, E t)).toReal :=
      ENNReal.toReal_mono (terminalDepthShift_event_ne_top p _) (p.toOuterMeasure.mono hsub)
    _ ≤ ∑ t ∈ T, (p.toOuterMeasure (E t)).toReal := hu
    _ ≤ ∑ _t ∈ T, 2 * Real.exp (-(b : ℝ) / 16384) := by
      apply Finset.sum_le_sum
      intro t ht
      exact terminalDepthShift_prefix_absTailMass_le (by omega)
        (Finset.mem_Icc.mp ht).1 (Finset.mem_Icc.mp ht).2
    _ ≤ _ := by
      simp only [Finset.sum_const, nsmul_eq_mul]
      have hc : (T.card : ℝ) ≤ 2 * (b : ℝ) + 2 := by
        have hwide := ndGeom2ShiftedWideSymmetricWidth_le_base b
        dsimp [T, H]
        rw [Nat.card_Icc]
        exact_mod_cast (show ndGeom2ShiftedWideSymmetricHorizon b + 1 - 1 ≤ 2 * b + 2 by
          unfold ndGeom2ShiftedWideSymmetricHorizon; omega)
      have hm := mul_le_mul_of_nonneg_right hc
        (by positivity : 0 ≤ 2 * Real.exp (-(b : ℝ) / 16384))
      nlinarith only [hm]

def ndTerminalDepthShiftBadFilter (b a : ℕ) (w : List ℕ+) : ℝ := by
  classical
  exact if ndTerminalDepthShiftGood b a w.length then 0 else 1

theorem terminalDepthShiftBadFilter_nonneg (b a : ℕ) (w : List ℕ+) :
    0 ≤ ndTerminalDepthShiftBadFilter b a w := by
  classical
  unfold ndTerminalDepthShiftBadFilter
  split_ifs <;> norm_num

theorem terminalDepthShiftBadFilter_atom_sum_le
    {b : ℕ} (hb : 200 ≤ b) (a K : ℕ) :
    (∑ w : ndShiftedReferenceSelectedWords b a K,
      ndTerminalDepthShiftBadFilter b a w.val *
        (2 : ℝ) ^ (-(Tao.taoTupleWeight w.val : ℤ))) ≤
      (4 * (b : ℝ) + 4) * Real.exp (-(b : ℝ) / 16384) := by
  classical
  have heq : (∑ w : ndShiftedReferenceSelectedWords b a K,
      ndTerminalDepthShiftBadFilter b a w.val * (2 : ℝ) ^ (-(Tao.taoTupleWeight w.val : ℤ))) =
      ∑ w : ndTerminalDepthShiftRejectedWords b a K,
        (2 : ℝ) ^ (-(Tao.taoTupleWeight w.val : ℤ)) := by
    rw [← Finset.sum_subtype (ndShiftedReferenceSelectedWords b a K) (fun _ => Iff.rfl)
      (fun w => ndTerminalDepthShiftBadFilter b a w * (2 : ℝ) ^ (-(Tao.taoTupleWeight w : ℤ))),
      ← Finset.sum_subtype (ndTerminalDepthShiftRejectedWords b a K) (fun _ => Iff.rfl)
        (fun w => (2 : ℝ) ^ (-(Tao.taoTupleWeight w : ℤ)))]
    simp only [ndTerminalDepthShiftRejectedWords, Finset.sum_filter,
      ndTerminalDepthShiftBadFilter, ite_mul, one_mul, zero_mul, ite_not]
  rw [heq]
  exact terminalDepthShift_rejected_word_mass_le hb a K

theorem terminalDepthShift_badKernel_fullMean_le
    {b : ℕ} (hb : 200 ≤ b) (a K k : ℕ) :
    ndTernaryUniformMean (ndGeom2ShiftedWideSymmetricHorizon b + k)
      (ndRootCoreFilteredKernel b a K k (ndTerminalDepthShiftBadFilter b a)
        (ndSyracuseUnitReferenceDensity k)) ≤
      (2 / 3 : ℝ) * ((4 * (b : ℝ) + 4) * Real.exp (-(b : ℝ) / 16384)) := by
  rw [rootCoreFilteredKernel_fullMean_eq b a K k _ _ (ndSyracuseUnitReferenceDensity_nonneg k),
    unitReferenceDensity_fullMean_eq]
  simpa only [mul_comm] using mul_le_mul_of_nonneg_right
    (terminalDepthShiftBadFilter_atom_sum_le hb a K) (by norm_num : (0 : ℝ) ≤ 2 / 3)

theorem terminalDepthShift_loss_le_inverse_sixth
    {b : ℕ} (hb : 1 ≤ b) :
    (4 * (b : ℝ) + 4) * Real.exp (-(b : ℝ) / 16384) ≤
      (8 * (Nat.factorial 7 : ℝ) * 16384 ^ 7) / (b : ℝ) ^ 6 := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast (by omega : 0 < b)
  have hb1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
  let x := (b : ℝ) / 16384
  have hx : 0 < x := by dsimp [x]; positivity
  have ht := Real.pow_div_factorial_le_exp x hx.le 7
  have he : Real.exp (-x) ≤ (Nat.factorial 7 : ℝ) / x ^ 7 := by
    rw [Real.exp_neg, inv_eq_one_div]
    apply (div_le_div_iff₀ (Real.exp_pos _) (pow_pos hx _)).mpr
    rw [one_mul, mul_comm]
    exact (div_le_iff₀ (by positivity : (0 : ℝ) < Nat.factorial 7)).mp ht
  calc
    _ ≤ (8 * (b : ℝ)) * ((Nat.factorial 7 : ℝ) / x ^ 7) := by
      exact mul_le_mul (by linarith) (by simpa only [x, neg_div] using he)
        (Real.exp_pos _).le (by positivity)
    _ = _ := by dsimp [x]; field_simp

end

end Erdos1135Predecessor.ND.PositiveDensity
