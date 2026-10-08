/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Probability.FullL1
import Erdos1135SecondScale.Tao.Syracuse.TruncatedValuationPacking

/-!
# Sharp full-L1 recovery from strict valuation truncation

The strict packer has a finite accepted image and one overflow atom.  This
module uses that exact fiber structure to recover full L1 with only the two
overflow masses, and then retains the mapped overflow difference to obtain the
sharp `2 * min` remainder.
-/

open scoped BigOperators

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

/-- The finite set of exact-length valuation lists accepted below cutoff `M`. -/
noncomputable def shortValuationLists (n M : ℕ) : Finset (List ℕ+) := by
  classical
  exact Finset.univ.image
    (BoundedValuationTuple.toList (n := n) (M := M))

theorem mem_shortValuationLists_iff {n M : ℕ} {as : List ℕ+} :
    as ∈ shortValuationLists n M ↔
      ∃ v : BoundedValuationTuple n M,
        as = BoundedValuationTuple.toList v := by
  classical
  simp [shortValuationLists, eq_comm]

theorem not_mem_shortValuationLists_iff {n M : ℕ} {as : List ℕ+} :
    as ∉ shortValuationLists n M ↔
      truncateValuationList n M as = none := by
  constructor
  · intro hmem
    cases htruncate : truncateValuationList n M as with
    | none => rfl
    | some v =>
        exfalso
        apply hmem
        rw [mem_shortValuationLists_iff]
        exact ⟨v, truncateValuationList_eq_some_iff.mp htruncate⟩
  · intro htruncate hmem
    rw [mem_shortValuationLists_iff] at hmem
    rcases hmem with ⟨v, rfl⟩
    have hsome :
        truncateValuationList n M (BoundedValuationTuple.toList v) = some v :=
      truncateValuationList_eq_some_iff.mpr rfl
    rw [htruncate] at hsome
    contradiction

theorem taoPMF_map_truncateValuationList_apply_some
    (p : PMF (List ℕ+)) {n M : ℕ} (v : BoundedValuationTuple n M) :
    ((p.map (truncateValuationList n M)) (some v)).toReal =
      (p (BoundedValuationTuple.toList v)).toReal := by
  apply congrArg ENNReal.toReal
  rw [PMF.map_apply]
  rw [tsum_eq_single (BoundedValuationTuple.toList v)]
  · rw [if_pos]
    exact (truncateValuationList_eq_some_iff.mpr rfl).symm
  · intro as has
    rw [if_neg]
    intro hsome
    apply has
    exact truncateValuationList_eq_some_iff.mp hsome.symm

theorem taoPMF_tsum_outside_shortValuationLists_eq_map_none
    (p : PMF (List ℕ+)) (n M : ℕ) :
    (∑' as : {as : List ℕ+ // as ∉ shortValuationLists n M},
        (p as).toReal) =
      ((p.map (truncateValuationList n M)) none).toReal := by
  rw [taoPMF_map_apply_toReal_tsum]
  calc
    (∑' as : {as : List ℕ+ // as ∉ shortValuationLists n M},
        (p as).toReal) =
        ∑' as : List ℕ+,
          Set.indicator {as | as ∉ shortValuationLists n M}
            (fun as => (p as).toReal) as :=
      tsum_subtype {as : List ℕ+ | as ∉ shortValuationLists n M}
        (fun as => (p as).toReal)
    _ = ∑' as : List ℕ+,
          if none = truncateValuationList n M as then (p as).toReal else 0 := by
      apply tsum_congr
      intro as
      by_cases hmem : as ∉ shortValuationLists n M
      · rw [Set.indicator_of_mem hmem]
        rw [if_pos]
        exact (not_mem_shortValuationLists_iff.mp hmem).symm
      · simp only [Set.indicator, Set.mem_setOf_eq, hmem, if_false]
        rw [if_neg]
        intro hnone
        exact hmem (not_mem_shortValuationLists_iff.mpr hnone.symm)

theorem sum_shortValuationLists_fullL1_eq_sum_some
    (p q : PMF (List ℕ+)) (n M : ℕ) :
    (∑ as ∈ shortValuationLists n M,
        |(p as).toReal - (q as).toReal|) =
      ∑ v : BoundedValuationTuple n M,
        |((p.map (truncateValuationList n M)) (some v)).toReal -
          ((q.map (truncateValuationList n M)) (some v)).toReal| := by
  classical
  rw [shortValuationLists, Finset.sum_image]
  · apply Finset.sum_congr rfl
    intro v _hv
    rw [taoPMF_map_truncateValuationList_apply_some,
      taoPMF_map_truncateValuationList_apply_some]
  · exact Set.injOn_of_injective BoundedValuationTuple.toList_injective

theorem taoPMFFullL1_outside_shortValuationLists_le
    (p q : PMF (List ℕ+)) (n M : ℕ) :
    (∑' as : {as : List ℕ+ // as ∉ shortValuationLists n M},
        |(p as).toReal - (q as).toReal|) ≤
      ((p.map (truncateValuationList n M)) none).toReal +
        ((q.map (truncateValuationList n M)) none).toReal := by
  let S : Set (List ℕ+) := {as | as ∉ shortValuationLists n M}
  have hdiff := (taoPMFFullL1_summable p q).subtype S
  have hp := (taoPMF_summable_toReal p).subtype S
  have hq := (taoPMF_summable_toReal q).subtype S
  have hadd := hp.add hq
  calc
    (∑' as : S, |(p as).toReal - (q as).toReal|) ≤
        ∑' as : S, ((p as).toReal + (q as).toReal) := by
      apply hdiff.tsum_le_tsum
      · intro as
        simpa [abs_of_nonneg ENNReal.toReal_nonneg] using
          abs_sub (p as).toReal (q as).toReal
      · exact hadd
    _ = (∑' as : S, (p as).toReal) +
          ∑' as : S, (q as).toReal := hp.tsum_add hq
    _ = ((p.map (truncateValuationList n M)) none).toReal +
          ((q.map (truncateValuationList n M)) none).toReal := by
      simpa [S] using congrArg₂ (· + ·)
        (taoPMF_tsum_outside_shortValuationLists_eq_map_none p n M)
        (taoPMF_tsum_outside_shortValuationLists_eq_map_none q n M)

private theorem add_eq_abs_sub_add_two_mul_min {a b : ℝ} :
    a + b = |a - b| + 2 * min a b := by
  by_cases hab : a ≤ b
  · rw [min_eq_left hab, abs_of_nonpos (sub_nonpos.mpr hab)]
    ring
  · have hba : b ≤ a := le_of_not_ge hab
    rw [min_eq_right hba, abs_of_nonneg (sub_nonneg.mpr hba)]
    ring

/-- Sharp recovery of full L1 from strict truncation.  The mapped overflow
difference is retained, leaving exactly twice the smaller overflow mass. -/
theorem taoPMFFullL1_le_truncated_taoTV_add_two_min
    (p q : PMF (List ℕ+)) (n M : ℕ) :
    taoPMFFullL1 p q ≤
      taoTV
          (p.map (truncateValuationList n M))
          (q.map (truncateValuationList n M)) +
        2 * min
          (((p.map (truncateValuationList n M)) none).toReal)
          (((q.map (truncateValuationList n M)) none).toReal) := by
  let T := truncateValuationList n M
  let pNone := ((p.map T) none).toReal
  let qNone := ((q.map T) none).toReal
  have hsplit := (taoPMFFullL1_summable p q).sum_add_tsum_subtype_compl
    (shortValuationLists n M)
  have houtside := taoPMFFullL1_outside_shortValuationLists_le p q n M
  have hmasses : pNone + qNone = |pNone - qNone| + 2 * min pNone qNone :=
    add_eq_abs_sub_add_two_mul_min
  calc
    taoPMFFullL1 p q =
        (∑ as ∈ shortValuationLists n M,
            |(p as).toReal - (q as).toReal|) +
          ∑' as : {as : List ℕ+ // as ∉ shortValuationLists n M},
            |(p as).toReal - (q as).toReal| := by
      exact hsplit.symm
    _ ≤ (∑ v : BoundedValuationTuple n M,
            |((p.map T) (some v)).toReal -
              ((q.map T) (some v)).toReal|) +
          (pNone + qNone) := by
      rw [sum_shortValuationLists_fullL1_eq_sum_some]
      simpa [T, pNone, qNone] using
        add_le_add_right houtside
          (∑ v : BoundedValuationTuple n M,
            |((p.map T) (some v)).toReal -
              ((q.map T) (some v)).toReal|)
    _ = (|pNone - qNone| +
          ∑ v : BoundedValuationTuple n M,
            |((p.map T) (some v)).toReal -
              ((q.map T) (some v)).toReal|) +
          2 * min pNone qNone := by
      rw [hmasses]
      ring
    _ = taoTV (p.map T) (q.map T) + 2 * min pNone qNone := by
      unfold taoTV
      rw [Fintype.sum_option]

/-- Critical-path asymmetric form, charging only the ideal overflow mass. -/
theorem taoPMFFullL1_le_truncated_taoTV_add_two_right_none
    (p q : PMF (List ℕ+)) (n M : ℕ) :
    taoPMFFullL1 p q ≤
      taoTV
          (p.map (truncateValuationList n M))
          (q.map (truncateValuationList n M)) +
        2 * ((q.map (truncateValuationList n M)) none).toReal := by
  refine (taoPMFFullL1_le_truncated_taoTV_add_two_min p q n M).trans ?_
  gcongr
  exact min_le_right _ _

private theorem taoPMFFullL1_pure_two_pure_three_eq_two :
    taoPMFFullL1
        (PMF.pure ([2] : List ℕ+))
        (PMF.pure ([3] : List ℕ+)) = 2 := by
  classical
  unfold taoPMFFullL1
  have hs := taoPMFFullL1_summable
    (PMF.pure ([2] : List ℕ+)) (PMF.pure ([3] : List ℕ+))
  rw [hs.tsum_eq_add_tsum_ite ([2] : List ℕ+)]
  rw [tsum_eq_single ([3] : List ℕ+)]
  · norm_num [PMF.pure_apply]
  · intro as has
    by_cases ha : as = ([2] : List ℕ+)
    · simp [ha]
    · simp [PMF.pure_apply, ha, has]

/-- The coefficient `2` is attained when two distinct source atoms both
overflow: truncation identifies them, while their original full L1 is two. -/
theorem taoPMFFullL1_truncation_coefficient_two_canary :
    taoPMFFullL1
        (PMF.pure ([2] : List ℕ+))
        (PMF.pure ([3] : List ℕ+)) =
      taoTV
          ((PMF.pure ([2] : List ℕ+)).map (truncateValuationList 1 2))
          ((PMF.pure ([3] : List ℕ+)).map (truncateValuationList 1 2)) +
        2 * (((PMF.pure ([3] : List ℕ+)).map
          (truncateValuationList 1 2)) none).toReal := by
  have hthree : truncateValuationList 1 2 ([3] : List ℕ+) = none := by
    rw [truncateValuationList_eq_none_iff_of_length]
    · norm_num [taoTupleWeight]
    · simp
  rw [taoPMFFullL1_pure_two_pure_three_eq_two, PMF.pure_map, PMF.pure_map,
    truncateValuationList_one_two_two_none, hthree, taoTV_self]
  norm_num [PMF.pure_apply]

end

end Tao
end Erdos1135SecondScale
