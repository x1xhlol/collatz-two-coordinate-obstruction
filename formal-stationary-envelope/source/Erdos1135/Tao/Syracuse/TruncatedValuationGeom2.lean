/-
Compatibility modification, 8 October 2026: proof-tactic syntax only.
See provenance/envelope-linter-patches.json for exact source hashes and patches.
-/

import Erdos1135.Tao.Syracuse.TruncatedValuationPacking
import Erdos1135.Tao.Syracuse.ValuationDistribution

/-!
# Ideal Geom(2) law after strict valuation truncation

This leaf identifies the hand-built finite overflow law with the unconditioned
pushforward of the exact-length iid positive `Geom(2)` list law.  In particular,
the `none` atom retains all overflow mass; no conditioning or renormalization is
performed.
-/

namespace Erdos1135
namespace Tao

noncomputable section

theorem geom2PNatListPMF_map_truncateValuationList_apply_some
    {n M : ℕ} (v : BoundedValuationTuple n M) :
    ((geom2PNatListPMF n).map (truncateValuationList n M)) (some v) =
      geom2PNatListPMF n (BoundedValuationTuple.toList v) := by
  classical
  rw [PMF.map_apply]
  rw [tsum_eq_single (BoundedValuationTuple.toList v)]
  · rw [if_pos]
    exact ((truncateValuationList_eq_some_iff).2 rfl).symm
  · intro as has
    by_cases hpack : some v = truncateValuationList n M as
    · have has_eq : as = BoundedValuationTuple.toList v :=
        (truncateValuationList_eq_some_iff.mp hpack.symm)
      exact (has has_eq).elim
    · simp [hpack]

/-- Strict truncation pushes the exact-length iid positive `Geom(2)` law to
the finite tuple law with one unconditioned overflow atom. -/
theorem geom2PNatListPMF_map_truncateValuationList (n M : ℕ) :
    (geom2PNatListPMF n).map (truncateValuationList n M) =
      truncatedValuationTupleGeom2PMF n M := by
  classical
  apply PMF.ext
  intro x
  cases x with
  | some v =>
      rw [geom2PNatListPMF_map_truncateValuationList_apply_some,
        truncatedValuationTupleGeom2PMF_apply_some]
  | none =>
      rw [truncatedValuationTupleGeom2PMF_apply_none]
      apply ENNReal.eq_sub_of_add_eq' ENNReal.one_ne_top
      have hmass :=
        PMF.tsum_coe ((geom2PNatListPMF n).map (truncateValuationList n M))
      rw [tsum_fintype, Fintype.sum_option] at hmass
      have hsome :
          (∑ v : BoundedValuationTuple n M,
            ((geom2PNatListPMF n).map (truncateValuationList n M)) (some v)) =
            boundedValuationTupleGeom2TotalMassENNReal n M := by
        unfold boundedValuationTupleGeom2TotalMassENNReal
        apply Finset.sum_congr rfl
        intro v _hv
        exact geom2PNatListPMF_map_truncateValuationList_apply_some v
      rw [hsome] at hmass
      exact hmass

theorem geom2PNatListPMF_map_truncateValuationList_zero_zero :
    (geom2PNatListPMF 0).map (truncateValuationList 0 0) =
      truncatedValuationTupleGeom2PMF 0 0 :=
  geom2PNatListPMF_map_truncateValuationList 0 0

theorem geom2PNatListPMF_map_truncateValuationList_zero_one :
    (geom2PNatListPMF 0).map (truncateValuationList 0 1) =
      truncatedValuationTupleGeom2PMF 0 1 :=
  geom2PNatListPMF_map_truncateValuationList 0 1

theorem geom2PNatListPMF_map_truncateValuationList_one_one :
    (geom2PNatListPMF 1).map (truncateValuationList 1 1) =
      truncatedValuationTupleGeom2PMF 1 1 :=
  geom2PNatListPMF_map_truncateValuationList 1 1

theorem geom2PNatListPMF_map_truncateValuationList_one_two :
    (geom2PNatListPMF 1).map (truncateValuationList 1 2) =
      truncatedValuationTupleGeom2PMF 1 2 :=
  geom2PNatListPMF_map_truncateValuationList 1 2

theorem geom2PNatListPMF_map_truncateValuationList_zero_zero_apply_none :
    ((geom2PNatListPMF 0).map (truncateValuationList 0 0)) none = 1 := by
  rw [PMF.map_apply, tsum_eq_single []]
  · simp [geom2PNatListPMF, truncateValuationList, taoTupleWeight]
  · intro as has
    simp [geom2PNatListPMF, has]

theorem geom2PNatListPMF_map_truncateValuationList_zero_one_apply_none :
    ((geom2PNatListPMF 0).map (truncateValuationList 0 1)) none = 0 := by
  rw [PMF.map_apply, tsum_eq_single []]
  · simp [truncateValuationList, taoTupleWeight]
  · intro as has
    simp [geom2PNatListPMF, has]

private noncomputable def oneTwoTuple : BoundedValuationTuple 1 2 :=
  BoundedValuationTuple.ofList [1] rfl (by norm_num [taoTupleWeight])

theorem geom2PNatListPMF_map_truncateValuationList_one_two_apply_some_toReal :
    (((geom2PNatListPMF 1).map (truncateValuationList 1 2))
      (some oneTwoTuple)).toReal = 1 / 2 := by
  rw [geom2PNatListPMF_map_truncateValuationList_apply_some]
  simpa [oneTwoTuple, taoTupleWeight] using
    geom2PNatListPMF_apply_length_toReal_eq_weight ([1] : List ℕ+)

end

end Tao
end Erdos1135
