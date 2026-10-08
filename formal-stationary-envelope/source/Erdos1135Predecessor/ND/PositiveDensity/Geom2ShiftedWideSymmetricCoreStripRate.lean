/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricRootUniformCoreCapacity

namespace Erdos1135Predecessor.ND.PositiveDensity

open scoped BigOperators

noncomputable section

def ndRootCoreStripDepths (b m : ℕ) : Finset ℕ :=
  (ndGeom2ShiftedWideSymmetricCrossingSelectedDepths b).filter
    (fun s => b ≤ s + m ∧ s ≤ b + m)

def ndRootCoreStripCrossingProbability (b m : ℕ) : ℝ :=
  ∑ s ∈ ndRootCoreStripDepths b m,
    ndGeom2ShiftedWideSymmetricFirstCrossingAtMass b
      (ndGeom2ShiftedWideSymmetricShiftRadius b) s

def ndRootCoreStripBoundedCrossingProbability (b m K : ℕ) : ℝ :=
  ∑ s ∈ ndRootCoreStripDepths b m,
    ndGeom2ShiftedWideSymmetricFirstCrossingBoundedOvershootAtMass b
      (ndGeom2ShiftedWideSymmetricShiftRadius b) s K

theorem rootCore_early_hit_implies_abs_tail
    {b m s : ℕ} (hm : 16 ≤ m) (hsm : s + m ≤ b)
    {full : List ℕ+} (hlen : s ≤ full.length)
    (hh : ndGeom2ShiftedWideSymmetricHit b (ndGeom2ShiftedWideSymmetricShiftRadius b) s full) :
    (m : ℝ) / 3 < |Tao.taoGeom2CenteredListWeight (full.take s)| := by
  have hc := five_mul_ndBalancedTotal_le_eight_mul_add_five (b - s)
  have hs : s - b = 0 := by omega
  simp only [ndGeom2ShiftedWideSymmetricHit, hs, ndBalancedTotal_zero] at hh
  have hi : m + 6 * s < 3 * Tao.taoTupleWeight (full.take s) := by omega
  have hr : (m : ℝ) + 6 * (s : ℝ) < 3 * (Tao.taoTupleWeight (full.take s) : ℝ) := by
    exact_mod_cast hi
  have htake : (full.take s).length = s := by simp [List.length_take, Nat.min_eq_left hlen]
  apply lt_of_lt_of_le _ (le_abs_self _)
  unfold Tao.taoGeom2CenteredListWeight
  rw [htake]
  linarith only [hr]

theorem rootCore_late_miss_implies_abs_tail
    {b m : ℕ} (hm : 16 ≤ m) {full : List ℕ+} (hlen : b + m ≤ full.length)
    (hh : ¬ ndGeom2ShiftedWideSymmetricHit b (ndGeom2ShiftedWideSymmetricShiftRadius b) (b + m) full) :
    (m : ℝ) / 3 < |Tao.taoGeom2CenteredListWeight (full.take (b + m))| := by
  have hc := five_mul_ndBalancedTotal_le_eight_mul_add_five m
  simp only [ndGeom2ShiftedWideSymmetricHit, Nat.add_sub_cancel_left,
    Nat.sub_add_eq, Nat.sub_self, Nat.zero_sub, ndBalancedTotal_zero] at hh
  have hi : 3 * Tao.taoTupleWeight (full.take (b + m)) + m < 6 * (b + m) := by omega
  have hr : 3 * (Tao.taoTupleWeight (full.take (b + m)) : ℝ) + (m : ℝ) < 6 * ((b + m : ℕ) : ℝ) := by
    exact_mod_cast hi
  have htake : (full.take (b + m)).length = b + m := by simp [List.length_take, Nat.min_eq_left hlen]
  apply lt_of_lt_of_le _ (neg_le_abs _)
  unfold Tao.taoGeom2CenteredListWeight
  rw [htake]
  linarith only [hr]

private theorem rootCore_commonExponent_le
    {b m s : ℕ} (hb : 0 < b) (hm : 0 < m) (hmb : m ≤ b)
    (hs : 0 < s) (hsb : s ≤ 2 * b) :
    (m : ℝ) ^ 2 / (576 * (b : ℝ)) ≤
      min (((m : ℝ) / 3) ^ 2 / (32 * (s : ℝ))) (((m : ℝ) / 3) / 8) := by
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hsR : (0 : ℝ) < s := by exact_mod_cast hs
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmbR : (m : ℝ) ≤ b := by exact_mod_cast hmb
  have hsbR : (s : ℝ) ≤ 2 * b := by exact_mod_cast hsb
  apply le_min
  · apply (div_le_div_iff₀ (by positivity : 0 < 576 * (b : ℝ))
      (by positivity : 0 < 32 * (s : ℝ))).2
    have h := mul_le_mul_of_nonneg_left hsbR (sq_nonneg (m : ℝ))
    nlinarith only [h]
  · apply (div_le_iff₀ (by positivity : 0 < 576 * (b : ℝ))).2
    have h := mul_le_mul_of_nonneg_left hmbR hmR.le
    nlinarith only [h, mul_nonneg hmR.le hbR.le]

theorem rootCore_prefix_absTailMass_le
    {b m s : ℕ} (hb : 0 < b) (hm : 0 < m) (hmb : m ≤ b)
    (hs : 0 < s) (hsH : s ≤ ndGeom2ShiftedWideSymmetricHorizon b) :
    ((Tao.geom2PNatListPMF (ndGeom2ShiftedWideSymmetricHorizon b)).toOuterMeasure
      {full | (m : ℝ) / 3 < |Tao.taoGeom2CenteredListWeight (full.take s)|}).toReal ≤
      2 * Real.exp (-((m : ℝ) ^ 2 / (576 * (b : ℝ)))) := by
  change ((Tao.geom2PNatListPMF (ndGeom2ShiftedWideSymmetricHorizon b)).toOuterMeasure
    ((fun full => full.take s) ⁻¹' {w | (m : ℝ) / 3 < |Tao.taoGeom2CenteredListWeight w|})).toReal ≤ _
  rw [geom2PNatListPMF_take_event_outerMeasure_toReal hsH]
  have ht := Tao.geom2PNatListPMF_centeredWeight_absTail_le_min hs
    (by positivity : (0 : ℝ) < (m : ℝ) / 3)
  have hs2 : s ≤ 2 * b := by
    simp only [ndGeom2ShiftedWideSymmetricHorizon, ndGeom2ShiftedWideSymmetricWidth] at hsH
    omega
  exact ht.trans (mul_le_mul_of_nonneg_left
    (Real.exp_le_exp.mpr (neg_le_neg (rootCore_commonExponent_le hb hm hmb hs hs2))) (by norm_num))

private def rootCoreTestDepths (b m : ℕ) : Finset ℕ :=
  insert (b + m) (Finset.Icc (ndGeom2ShiftedWideSymmetricLower b) (b - m))

private theorem rootCore_testDepth_bounds {b m s : ℕ}
    (hb : 200 ≤ b) (hm : m ≤ ndGeom2ShiftedWideSymmetricWidth b)
    (hs : s ∈ rootCoreTestDepths b m) : 0 < s ∧ s ≤ ndGeom2ShiftedWideSymmetricHorizon b := by
  rcases Finset.mem_insert.mp hs with rfl | hs
  · unfold ndGeom2ShiftedWideSymmetricHorizon
    constructor <;> omega
  · have hsB := Finset.mem_Icc.mp hs
    simp only [ndGeom2ShiftedWideSymmetricLower, ndGeom2ShiftedWideSymmetricHorizon,
      ndGeom2ShiftedWideSymmetricWidth] at hsB ⊢
    constructor <;> omega

private theorem rootCore_testDepth_card_le (b m : ℕ) :
    (rootCoreTestDepths b m).card ≤ 2 * b + 2 := by
  have h := Finset.card_insert_le (b + m) (Finset.Icc (ndGeom2ShiftedWideSymmetricLower b) (b - m))
  rw [Nat.card_Icc] at h
  dsimp [rootCoreTestDepths]
  omega

theorem rootCore_good_tests_imply_strip_firstCrossing
    {b m : ℕ} (hb : 200 ≤ b) (hm : 16 ≤ m) (hmw : m ≤ ndGeom2ShiftedWideSymmetricWidth b)
    {full : List ℕ+} (hlen : full.length = ndGeom2ShiftedWideSymmetricHorizon b)
    (hgood : ∀ s ∈ rootCoreTestDepths b m,
      |Tao.taoGeom2CenteredListWeight (full.take s)| ≤ (m : ℝ) / 3) :
    ∃ s ∈ ndRootCoreStripDepths b m,
      ndGeom2ShiftedWideSymmetricFirstCrossingAt b (ndGeom2ShiftedWideSymmetricShiftRadius b) s full := by
  classical
  let I := ndGeom2ShiftedWideSymmetricCrossingSelectedDepths b
  let Hit := ndGeom2ShiftedWideSymmetricCrossingEligibleHit b (ndGeom2ShiftedWideSymmetricShiftRadius b)
  have hmb : m ≤ b := hmw.trans (ndGeom2ShiftedWideSymmetricWidth_le_base b)
  have hnoEarly : ∀ s ∈ Finset.Icc (ndGeom2ShiftedWideSymmetricLower b) (b - m),
      ¬ndGeom2ShiftedWideSymmetricHit b (ndGeom2ShiftedWideSymmetricShiftRadius b) s full := by
    intro s hs hh
    have hsT : s ∈ rootCoreTestDepths b m := Finset.mem_insert_of_mem hs
    have hsH := (rootCore_testDepth_bounds hb hmw hsT).2
    have htail := rootCore_early_hit_implies_abs_tail hm (by have := (Finset.mem_Icc.mp hs).2; omega)
      (by omega : s ≤ full.length) hh
    exact (not_lt_of_ge (hgood s hsT)) htail
  have hlow : ¬ndGeom2ShiftedWideSymmetricHit b (ndGeom2ShiftedWideSymmetricShiftRadius b)
      (ndGeom2ShiftedWideSymmetricLower b) full := by
    apply hnoEarly
    apply Finset.mem_Icc.mpr
    unfold ndGeom2ShiftedWideSymmetricLower
    constructor <;> omega
  have hlate : ndGeom2ShiftedWideSymmetricHit b (ndGeom2ShiftedWideSymmetricShiftRadius b) (b + m) full := by
    by_contra hh
    have hsT : b + m ∈ rootCoreTestDepths b m := Finset.mem_insert_self _ _
    have hsH := (rootCore_testDepth_bounds hb hmw hsT).2
    have htail := rootCore_late_miss_implies_abs_tail hm (by omega : b + m ≤ full.length) hh
    exact (not_lt_of_ge (hgood (b + m) hsT)) htail
  have hlateI : b + m ∈ I := by
    apply Finset.mem_Icc.mpr
    unfold ndGeom2ShiftedWideSymmetricLower ndGeom2ShiftedWideSymmetricHorizon
    constructor <;> omega
  have hex : ∃ s, s ∈ I ∧ Hit s full := ⟨b + m, hlateI, hlow, hlate⟩
  let s := Nat.find hex
  have hs : s ∈ I ∧ Hit s full := Nat.find_spec hex
  have hsle : s ≤ b + m := Nat.find_min' hex ⟨hlateI, hlow, hlate⟩
  have hfirst : ndGeom2ShiftedWideSymmetricFirstCrossingAt b
      (ndGeom2ShiftedWideSymmetricShiftRadius b) s full := by
    refine ⟨hs.1, hs.2, ?_⟩
    intro j hj hjs hh
    exact Nat.find_min hex hjs ⟨hj, hh⟩
  have hsge : b ≤ s + m := by
    by_contra hh
    have hsB := Finset.mem_Icc.mp hs.1
    have he := hnoEarly s (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
    exact he hs.2.2
  exact ⟨s, Finset.mem_filter.mpr ⟨hs.1, hsge, hsle⟩, hfirst⟩

private theorem rootCore_pmf_finite {Ω : Type*} (p : PMF Ω) (E : Set Ω) :
    p.toOuterMeasure E ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.one_ne_top (by
    calc
      _ ≤ p.toOuterMeasure Set.univ := p.toOuterMeasure.mono (Set.subset_univ _)
      _ = 1 := (p.toOuterMeasure_apply_eq_one_iff Set.univ).2 (Set.subset_univ _))

private theorem rootCore_mass_mono_support {Ω : Type*} (p : PMF Ω) {E F : Set Ω}
    (h : E ∩ p.support ⊆ F) : (p.toOuterMeasure E).toReal ≤ (p.toOuterMeasure F).toReal := by
  have heq : p.toOuterMeasure E = p.toOuterMeasure (E ∩ p.support) := by
    apply p.toOuterMeasure_apply_eq_of_inter_support_eq
    simp only [Set.inter_assoc, Set.inter_self]
  rw [heq]
  exact ENNReal.toReal_mono (rootCore_pmf_finite p F) (p.toOuterMeasure.mono h)

private theorem rootCore_mass_biUnion_le {Ω : Type*} (p : PMF Ω)
    (I : Finset ℕ) (E : ℕ → Set Ω) :
    (p.toOuterMeasure (⋃ s ∈ I, E s)).toReal ≤ ∑ s ∈ I, (p.toOuterMeasure (E s)).toReal := by
  have h := MeasureTheory.measure_biUnion_finset_le (μ := p.toOuterMeasure) I E
  have hfin : (∑ s ∈ I, p.toOuterMeasure (E s)) ≠ ⊤ :=
    ENNReal.sum_ne_top.mpr fun s _ => rootCore_pmf_finite p (E s)
  have hr := ENNReal.toReal_mono hfin h
  simpa only [ENNReal.toReal_sum (fun s _ => rootCore_pmf_finite p (E s))] using hr

private theorem rootCore_one_sub_mass_le_compl {Ω : Type*} (p : PMF Ω) (E : Set Ω) :
    1 - (p.toOuterMeasure E).toReal ≤ (p.toOuterMeasure Eᶜ).toReal := by
  have h := MeasureTheory.measure_union_le (μ := p.toOuterMeasure) E Eᶜ
  have hr := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨rootCore_pmf_finite p E, rootCore_pmf_finite p Eᶜ⟩) h
  rw [Set.union_compl_self,
    (p.toOuterMeasure_apply_eq_one_iff Set.univ).2 (Set.subset_univ _), ENNReal.toReal_one,
    ENNReal.toReal_add (rootCore_pmf_finite p E) (rootCore_pmf_finite p Eᶜ)] at hr
  linarith only [hr]

theorem one_sub_exp_le_rootCoreStripCrossingProbability
    {b m : ℕ} (hb : 200 ≤ b) (hm : 16 ≤ m) (hmw : m ≤ ndGeom2ShiftedWideSymmetricWidth b) :
    1 - (4 * (b : ℝ) + 4) * Real.exp (-((m : ℝ) ^ 2 / (576 * (b : ℝ)))) ≤
      ndRootCoreStripCrossingProbability b m := by
  classical
  let p := Tao.geom2PNatListPMF (ndGeom2ShiftedWideSymmetricHorizon b)
  let E := fun s => {full : List ℕ+ | (m : ℝ) / 3 < |Tao.taoGeom2CenteredListWeight (full.take s)|}
  let bad := ⋃ s ∈ rootCoreTestDepths b m, E s
  let F := fun s => {full : List ℕ+ | ndGeom2ShiftedWideSymmetricFirstCrossingAt b
    (ndGeom2ShiftedWideSymmetricShiftRadius b) s full}
  let e := Real.exp (-((m : ℝ) ^ 2 / (576 * (b : ℝ))))
  have hmb : m ≤ b := hmw.trans (ndGeom2ShiftedWideSymmetricWidth_le_base b)
  have hbad : (p.toOuterMeasure bad).toReal ≤ (4 * (b : ℝ) + 4) * e := by
    calc
      _ ≤ ∑ s ∈ rootCoreTestDepths b m, (p.toOuterMeasure (E s)).toReal :=
        rootCore_mass_biUnion_le p _ E
      _ ≤ ∑ _s ∈ rootCoreTestDepths b m, 2 * e := by
        apply Finset.sum_le_sum
        intro s hs
        have hsB := rootCore_testDepth_bounds hb hmw hs
        exact rootCore_prefix_absTailMass_le (by omega) (by omega) hmb hsB.1 hsB.2
      _ ≤ _ := by
        simp only [Finset.sum_const, nsmul_eq_mul]
        have hc : ((rootCoreTestDepths b m).card : ℝ) ≤ 2 * (b : ℝ) + 2 := by
          exact_mod_cast rootCore_testDepth_card_le b m
        have h := mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ 2 * e)
        nlinarith only [h]
  have hgood : (p.toOuterMeasure badᶜ).toReal ≤ ndRootCoreStripCrossingProbability b m := by
    have hsub : badᶜ ∩ p.support ⊆ ⋃ s ∈ ndRootCoreStripDepths b m, F s := by
      intro full hf
      have hlen := Tao.geom2PNatListPMF_support_length_eq hf.2
      have ht : ∀ s ∈ rootCoreTestDepths b m,
          |Tao.taoGeom2CenteredListWeight (full.take s)| ≤ (m : ℝ) / 3 := by
        intro s hs
        apply le_of_not_gt
        intro hbad
        exact hf.1 (Set.mem_iUnion.mpr ⟨s, Set.mem_iUnion.mpr ⟨hs, hbad⟩⟩)
      obtain ⟨s, hs, hfirst⟩ := rootCore_good_tests_imply_strip_firstCrossing hb hm hmw hlen ht
      exact Set.mem_iUnion.mpr ⟨s, Set.mem_iUnion.mpr ⟨hs, hfirst⟩⟩
    calc
      _ ≤ (p.toOuterMeasure (⋃ s ∈ ndRootCoreStripDepths b m, F s)).toReal :=
        rootCore_mass_mono_support p hsub
      _ ≤ ∑ s ∈ ndRootCoreStripDepths b m, (p.toOuterMeasure (F s)).toReal :=
        rootCore_mass_biUnion_le p _ F
      _ = ndRootCoreStripCrossingProbability b m := by
        apply Finset.sum_congr rfl
        intro s hs
        exact (ndGeom2ShiftedWideSymmetricFirstCrossingAtMass_eq_horizonMass
          (a := ndGeom2ShiftedWideSymmetricShiftRadius b) (Finset.mem_filter.mp hs).1).symm
  have hcompl := rootCore_one_sub_mass_le_compl p bad
  dsimp only [e] at hbad
  linarith only [hbad, hcompl, hgood]

theorem rootCoreStripCrossingProbability_le_one (b m : ℕ) :
    ndRootCoreStripCrossingProbability b m ≤ 1 := by
  have hs : ndRootCoreStripCrossingProbability b m ≤
      ndGeom2ShiftedWideSymmetricCrossingProbability b (ndGeom2ShiftedWideSymmetricShiftRadius b) := by
    rw [← sum_firstCrossingAtMass_eq_shiftedWideSymmetricCrossingProbability]
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => ENNReal.toReal_nonneg)
  have hp : ndGeom2ShiftedWideSymmetricCrossingProbability b (ndGeom2ShiftedWideSymmetricShiftRadius b) ≤ 1 := by
    let p := Tao.geom2PNatListPMF (ndGeom2ShiftedWideSymmetricHorizon b)
    have h : p.toOuterMeasure Set.univ = 1 :=
      (p.toOuterMeasure_apply_eq_one_iff Set.univ).2 (Set.subset_univ _)
    rw [← ENNReal.toReal_one, ← h]
    exact ENNReal.toReal_mono (rootCore_pmf_finite p Set.univ)
      (p.toOuterMeasure.mono (Set.subset_univ _))
  exact hs.trans hp

theorem rootCoreStripBoundedCrossingProbability_eq (b m K : ℕ) :
    ndRootCoreStripBoundedCrossingProbability b m K =
      (1 - (1 / 2 : ℝ) ^ (K + 1)) * ndRootCoreStripCrossingProbability b m := by
  unfold ndRootCoreStripBoundedCrossingProbability ndRootCoreStripCrossingProbability
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  exact ndGeom2ShiftedWideSymmetricFirstCrossingBoundedOvershootAtMass_eq
    (Finset.mem_filter.mp hs).1

theorem one_sub_exp_sub_tail_le_rootCoreStripBoundedCrossingProbability
    {b m K : ℕ} (hb : 200 ≤ b) (hm : 16 ≤ m) (hmw : m ≤ ndGeom2ShiftedWideSymmetricWidth b) :
    1 - (4 * (b : ℝ) + 4) * Real.exp (-((m : ℝ) ^ 2 / (576 * (b : ℝ)))) -
        (1 / 2 : ℝ) ^ (K + 1) ≤ ndRootCoreStripBoundedCrossingProbability b m K := by
  rw [rootCoreStripBoundedCrossingProbability_eq]
  have hr := one_sub_exp_le_rootCoreStripCrossingProbability hb hm hmw
  have ht := mul_le_mul_of_nonneg_left (rootCoreStripCrossingProbability_le_one b m)
    (by positivity : 0 ≤ (1 / 2 : ℝ) ^ (K + 1))
  nlinarith only [hr, ht]

private theorem rootCore_balanced_lt_twice {t : ℕ} (ht : 3 ≤ t) :
    ndBalancedTotal t < 2 * t := by
  have hpow : 2 * 3 ^ t ≤ 4 ^ t := by
    induction t, ht using Nat.le_induction with
    | base => norm_num
    | succ t _ ih =>
        rw [pow_succ, pow_succ]
        calc
          _ = 3 * (2 * 3 ^ t) := by ring
          _ ≤ 3 * 4 ^ t := Nat.mul_le_mul_left 3 ih
          _ ≤ _ := by omega
  have hx : 3 ^ t ≤ 2 ^ (2 * t - 1) := by
    have he : 4 ^ t = 2 * 2 ^ (2 * t - 1) := by
      have he : 2 * t = (2 * t - 1) + 1 := by omega
      calc
        _ = 2 ^ (2 * t) := by rw [show (4 : ℕ) = 2 ^ 2 by norm_num, pow_mul]
        _ = 2 ^ ((2 * t - 1) + 1) := congrArg (fun n : ℕ => 2 ^ n) he
        _ = _ := by rw [pow_succ]; ring
    rw [he] at hpow
    omega
  have hc : ndBalancedTotal t ≤ 2 * t - 1 := Nat.clog_le_of_le_pow hx
  omega

private theorem rootCore_replicate_two_weight (n : ℕ) :
    Tao.taoTupleWeight (List.replicate n (2 : ℕ+)) = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [List.replicate_succ, Tao.taoTupleWeight_cons, ih]
      norm_num
      omega

theorem rootCore_allTwo_firstCrossing {b : ℕ} (hb : 9 ≤ b) :
    ndGeom2ShiftedWideSymmetricFirstCrossingAt b (ndGeom2ShiftedWideSymmetricShiftRadius b)
      (b - 2) (List.replicate (b - 2) (2 : ℕ+)) := by
  let w := List.replicate (b - 2) (2 : ℕ+)
  have hwidth : 3 ≤ ndGeom2ShiftedWideSymmetricWidth b := by
    unfold ndGeom2ShiftedWideSymmetricWidth
    omega
  have hmiss : ∀ s < b - 2,
      ¬ndGeom2ShiftedWideSymmetricHit b (ndGeom2ShiftedWideSymmetricShiftRadius b) s w := by
    intro s hs hh
    have ht : 3 ≤ b - s := by omega
    have hc := rootCore_balanced_lt_twice ht
    have hw : Tao.taoTupleWeight (w.take s) = 2 * s := by
      dsimp only [w]
      rw [List.take_replicate, Nat.min_eq_left (by omega : s ≤ b - 2), rootCore_replicate_two_weight]
    simp only [ndGeom2ShiftedWideSymmetricHit, Nat.sub_eq_zero_of_le (by omega : s ≤ b),
      ndBalancedTotal_zero, hw] at hh
    omega
  have hlow : ¬ndGeom2ShiftedWideSymmetricHit b (ndGeom2ShiftedWideSymmetricShiftRadius b)
      (ndGeom2ShiftedWideSymmetricLower b) w := by
    apply hmiss
    unfold ndGeom2ShiftedWideSymmetricLower
    have := ndGeom2ShiftedWideSymmetricWidth_le_base b
    omega
  have hhit : ndGeom2ShiftedWideSymmetricHit b (ndGeom2ShiftedWideSymmetricShiftRadius b) (b - 2) w := by
    have hbsub : b - (b - 2) = 2 := by omega
    have hw : Tao.taoTupleWeight (w.take (b - 2)) = 2 * (b - 2) := by
      dsimp only [w]
      rw [List.take_replicate, Nat.min_self, rootCore_replicate_two_weight]
    simp only [ndGeom2ShiftedWideSymmetricHit, Nat.sub_eq_zero_of_le (Nat.sub_le b 2),
      ndBalancedTotal_zero, hw, hbsub]
    have hc : ndBalancedTotal 2 = 4 := by norm_num [ndBalancedTotal, Nat.clog]
    rw [hc]
    omega
  refine ⟨?_, ⟨hlow, hhit⟩, ?_⟩
  · apply Finset.mem_Icc.mpr
    unfold ndGeom2ShiftedWideSymmetricLower ndGeom2ShiftedWideSymmetricHorizon
    have := ndGeom2ShiftedWideSymmetricWidth_le_base b
    constructor <;> omega
  · intro s _ hs hhit
    exact hmiss s hs hhit.2

theorem rootCoreStripCrossingProbability_pos {b m : ℕ} (hb : 9 ≤ b) (hm : 2 ≤ m) :
    0 < ndRootCoreStripCrossingProbability b m := by
  let w := List.replicate (b - 2) (2 : ℕ+)
  let p := Tao.geom2PNatListPMF (b - 2)
  have he := rootCore_allTwo_firstCrossing hb
  have hs : b - 2 ∈ ndRootCoreStripDepths b m :=
    Finset.mem_filter.mpr ⟨he.1, by omega, by omega⟩
  have hmass : 0 < ndGeom2ShiftedWideSymmetricFirstCrossingAtMass b
      (ndGeom2ShiftedWideSymmetricShiftRadius b) (b - 2) := by
    have ha : 0 < (p w).toReal := by
      have h := referencePrefix_atom_eq w
      have hw : w.length = b - 2 := List.length_replicate ..
      rw [hw] at h
      change 0 < (Tao.geom2PNatListPMF (b - 2) w).toReal
      rw [h]
      positivity
    have hm : (p.toOuterMeasure {w}).toReal ≤
        ndGeom2ShiftedWideSymmetricFirstCrossingAtMass b
          (ndGeom2ShiftedWideSymmetricShiftRadius b) (b - 2) := by
      apply rootCore_mass_mono_support p
      intro v hv
      have hvw : v = w := Set.mem_singleton_iff.mp hv.1
      simpa only [hvw] using he
    rw [p.toOuterMeasure_apply_singleton] at hm
    exact ha.trans_le hm
  exact hmass.trans_le (Finset.single_le_sum
    (f := fun s => ndGeom2ShiftedWideSymmetricFirstCrossingAtMass b
      (ndGeom2ShiftedWideSymmetricShiftRadius b) s) (fun _ _ => ENNReal.toReal_nonneg) hs)

theorem rootCoreStripBoundedCrossingProbability_pos {b m K : ℕ} (hb : 9 ≤ b) (hm : 2 ≤ m) :
    0 < ndRootCoreStripBoundedCrossingProbability b m K := by
  rw [rootCoreStripBoundedCrossingProbability_eq]
  apply mul_pos _ (rootCoreStripCrossingProbability_pos hb hm)
  apply sub_pos.mpr
  exact pow_lt_one₀ (by norm_num) (by norm_num) (by omega)

def ndRootCoreSelectedWords (b m K : ℕ) : Finset (List ℕ+) :=
  (ndShiftedReferenceSelectedWords b (ndGeom2ShiftedWideSymmetricShiftRadius b) K).filter
    fun w => b ≤ w.length + m ∧ w.length ≤ b + m

theorem mem_rootCoreSelectedWords_iff (b m K : ℕ) (w : List ℕ+) :
    w ∈ ndRootCoreSelectedWords b m K ↔
      ndGeom2ShiftedWideSymmetricFirstCrossingBoundedOvershootAt b
        (ndGeom2ShiftedWideSymmetricShiftRadius b) w.length K w ∧
      b ≤ w.length + m ∧ w.length ≤ b + m := by
  simp only [ndRootCoreSelectedWords, Finset.mem_filter, mem_shiftedReferenceSelectedWords_iff]

theorem rootCore_rejectedMass_eq_one_sub_probability
    (b m K q : ℕ) (hq : ndGeom2ShiftedWideSymmetricHorizon b ≤ q) :
    Tao.taoGatedRejectedMass (Tao.geom2PNatListPMF q)
        (fun full => ∃ i : ndRootCoreSelectedWords b m K,
          full.take i.val.length = i.val) (Tao.taoSection7OffsetZMod q) =
      1 - ndRootCoreStripBoundedCrossingProbability b m K := by
  classical
  let p := Tao.geom2PNatListPMF q
  let I := ndRootCoreStripDepths b m
  let a := ndGeom2ShiftedWideSymmetricShiftRadius b
  let E : List ℕ+ → Prop := fun full => ∃ i : ndRootCoreSelectedWords b m K,
    full.take i.val.length = i.val
  let G : ℕ → List ℕ+ → Prop := fun s full => (full.take s).length = s ∧
    ndGeom2ShiftedWideSymmetricFirstCrossingBoundedOvershootAt b a s K (full.take s)
  have hgate : {full | E full} = ⋃ s ∈ I, {full | G s full} := by
    ext full
    simp only [Set.mem_setOf_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩
      have he := (mem_rootCoreSelectedWords_iff b m K i.val).mp i.property
      refine ⟨i.val.length, Finset.mem_filter.mpr ⟨he.1.1.1, he.2⟩, ?_⟩
      change (full.take i.val.length).length = i.val.length ∧ _
      rw [hi]
      exact ⟨rfl, he.1⟩
    · rintro ⟨s, hs, hl, he⟩
      have hstrip := (Finset.mem_filter.mp hs).2
      have hw : full.take s ∈ ndRootCoreSelectedWords b m K := by
        rw [mem_rootCoreSelectedWords_iff, hl]
        exact ⟨he, hstrip⟩
      exact ⟨⟨full.take s, hw⟩, by simp only [hl]⟩
  have hdis : Set.PairwiseDisjoint (I : Set ℕ) (fun s => {full | G s full}) := by
    intro s _ t _ hne
    change Disjoint {full | G s full} {full | G t full}
    rw [Set.disjoint_left]
    intro full hs ht
    have hs' := (ndFiniteFirstShiftedWideSymmetricCrossing_take_iff b a s full).mp hs.2.1
    have ht' := (ndFiniteFirstShiftedWideSymmetricCrossing_take_iff b a t full).mp ht.2.1
    rcases lt_or_gt_of_ne hne with hst | hts
    · exact ht'.2.2 _ hs'.1 hst hs'.2.1
    · exact hs'.2.2 _ ht'.1 hts ht'.2.1
  have hmass (s : ℕ) (hs : s ∈ I) :
      (p.toOuterMeasure {full | G s full}).toReal =
        ndGeom2ShiftedWideSymmetricFirstCrossingBoundedOvershootAtMass b a s K := by
    have hsq : s ≤ q := (Finset.mem_Icc.mp (Finset.mem_filter.mp hs).1).2.trans hq
    let J : Set (List ℕ+) := {w | w.length = s ∧
      ndGeom2ShiftedWideSymmetricFirstCrossingBoundedOvershootAt b a s K w}
    change (p.toOuterMeasure ((fun full => full.take s) ⁻¹' J)).toReal = _
    rw [geom2PNatListPMF_take_event_outerMeasure_toReal hsq J]
    unfold ndGeom2ShiftedWideSymmetricFirstCrossingBoundedOvershootAtMass
    congr 1
    apply (Tao.geom2PNatListPMF s).toOuterMeasure_apply_eq_of_inter_support_eq
    ext w
    constructor
    · rintro ⟨⟨_, he⟩, hp⟩
      exact ⟨he, hp⟩
    · rintro ⟨he, hp⟩
      exact ⟨⟨Tao.geom2PNatListPMF_support_length_eq hp, he⟩, hp⟩
  have hprob : (p.toOuterMeasure {full | E full}).toReal =
      ndRootCoreStripBoundedCrossingProbability b m K := by
    rw [hgate, Tao.taoPMFToOuterMeasure_biUnion_finset_eq_sum p I _ hdis,
      ENNReal.toReal_sum (fun s _ => rootCore_pmf_finite p {full | G s full})]
    exact Finset.sum_congr rfl hmass
  have htotal := Tao.taoGatedSubmass_sum_add_rejected_eq_one p E (Tao.taoSection7OffsetZMod q)
  rw [sum_taoGatedSubmass_eq_sourceEventProbability p E (Tao.taoSection7OffsetZMod q), hprob] at htotal
  change Tao.taoGatedRejectedMass p E (Tao.taoSection7OffsetZMod q) = _
  linarith only [htotal]

theorem rootCore_rejectedMass_le_exp_add_tail
    {b m K q : ℕ} (hb : 200 ≤ b) (hm : 16 ≤ m) (hmw : m ≤ ndGeom2ShiftedWideSymmetricWidth b)
    (hq : ndGeom2ShiftedWideSymmetricHorizon b ≤ q) :
    Tao.taoGatedRejectedMass (Tao.geom2PNatListPMF q)
        (fun full => ∃ i : ndRootCoreSelectedWords b m K,
          full.take i.val.length = i.val) (Tao.taoSection7OffsetZMod q) ≤
      (4 * (b : ℝ) + 4) * Real.exp (-((m : ℝ) ^ 2 / (576 * (b : ℝ)))) +
        (1 / 2 : ℝ) ^ (K + 1) := by
  rw [rootCore_rejectedMass_eq_one_sub_probability b m K q hq]
  have h := one_sub_exp_sub_tail_le_rootCoreStripBoundedCrossingProbability (K := K) hb hm hmw
  linarith only [h]

end

end Erdos1135Predecessor.ND.PositiveDensity
