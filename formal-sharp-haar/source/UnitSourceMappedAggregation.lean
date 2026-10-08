import Erdos1135.Tao.Section6.EventAggregation

/-!
# Section 6 aggregation for a mapped geometric source

The exact native length-n geometric source, local gates, and global failure
event are retained. Only the output map is generalized. This leaf charges
the global failure mass once and does not estimate the resulting slices.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Erdos1135.Tao

noncomputable section

/-- Accepted output mass under the unchanged native fixed-ambient gate. -/
def unitSourceMappedSlice
    (CA : ℝ) (n k l : ℕ) (f : List ℕ+ → ZMod (3 ^ n))
    (y : ZMod (3 ^ n)) : ℝ :=
  (taoGatedOptionPMF (geom2PNatListPMF n)
    (taoSection6FixedAmbientGate CA n k l) f (some y)).toReal

def unitSourceMappedLocalUnion
    (CA : ℝ) (n : ℕ) (f : List ℕ+ → ZMod (3 ^ n))
    (y : ZMod (3 ^ n)) : ℝ :=
  taoGatedSubmass (geom2PNatListPMF n)
    (taoSection6LocalUnionGate CA n) f y

theorem unitSourceMappedSlice_eq_gatedSubmass
    (CA : ℝ) (n k l : ℕ) (f : List ℕ+ → ZMod (3 ^ n))
    (y : ZMod (3 ^ n)) :
    unitSourceMappedSlice CA n k l f y =
      taoGatedSubmass (geom2PNatListPMF n)
        (taoSection6FixedAmbientGate CA n k l) f y := rfl

/-- Source-gate disjointness is independent of the chosen output map. -/
theorem unitSourceMappedLocalUnion_eq_sum
    (CA : ℝ) (n : ℕ) (f : List ℕ+ → ZMod (3 ^ n))
    (y : ZMod (3 ^ n)) :
    unitSourceMappedLocalUnion CA n f y =
      ∑ i : taoSection6LocalGateIndex n,
        unitSourceMappedSlice CA n i.1 i.2 f y := by
  have hunion :
      taoSection6LocalUnionGate CA n =
        fun full => ∃ i ∈ (Finset.univ : Finset (taoSection6LocalGateIndex n)),
          taoSection6LocalGate CA n i full := by
    funext full
    apply propext
    simp [taoSection6LocalUnionGate]
  unfold unitSourceMappedLocalUnion
  rw [hunion]
  calc
    taoGatedSubmass (geom2PNatListPMF n)
        (fun full => ∃ i ∈ (Finset.univ : Finset (taoSection6LocalGateIndex n)),
          taoSection6LocalGate CA n i full) f y =
      ∑ i ∈ (Finset.univ : Finset (taoSection6LocalGateIndex n)),
        taoGatedSubmass (geom2PNatListPMF n)
          (taoSection6LocalGate CA n i) f y := by
      apply taoGatedSubmass_finset_union_eq_sum
      intro i hi j hj hij full hifull hjfull
      exact (taoSection6LocalGate_disjoint hij full) ⟨hifull, hjfull⟩
    _ = ∑ i : taoSection6LocalGateIndex n,
        unitSourceMappedSlice CA n i.1 i.2 f y := by
      rfl

theorem unitSourceMappedLocalUnion_eq_sum_sum
    (CA : ℝ) (n : ℕ) (f : List ℕ+ → ZMod (3 ^ n))
    (y : ZMod (3 ^ n)) :
    unitSourceMappedLocalUnion CA n f y =
      ∑ k : Fin n, ∑ l : Fin (2 * n),
        unitSourceMappedSlice CA n k l f y := by
  rw [unitSourceMappedLocalUnion_eq_sum]
  exact Fintype.sum_prod_type _

theorem unitSourceMappedLocalUnionOscillation_le_sum_sum
    (CA : ℝ) (m n : ℕ) (f : List ℕ+ → ZMod (3 ^ n)) :
    taoZModPowOscillation m n (unitSourceMappedLocalUnion CA n f) ≤
      ∑ k : Fin n, ∑ l : Fin (2 * n),
        taoZModPowOscillation m n (unitSourceMappedSlice CA n k l f) := by
  calc
    taoZModPowOscillation m n (unitSourceMappedLocalUnion CA n f) =
        taoZModPowOscillation m n
          (fun y => ∑ i : taoSection6LocalGateIndex n,
            unitSourceMappedSlice CA n i.1 i.2 f y) := by
      congr 1
      funext y
      exact unitSourceMappedLocalUnion_eq_sum CA n f y
    _ ≤ ∑ i : taoSection6LocalGateIndex n,
        taoZModPowOscillation m n (unitSourceMappedSlice CA n i.1 i.2 f) :=
      taoZModPowOscillation_sum_le_sum m n
        (fun i : taoSection6LocalGateIndex n =>
          unitSourceMappedSlice CA n i.1 i.2 f)
    _ = ∑ k : Fin n, ∑ l : Fin (2 * n),
        taoZModPowOscillation m n (unitSourceMappedSlice CA n k l f) :=
      Fintype.sum_prod_type _

/-- Rejected source mass is unchanged when the output map is changed. -/
theorem unitSourceMappedGlobalRejected_eq_failure
    (CA : ℝ) (n : ℕ) (f : List ℕ+ → ZMod (3 ^ n)) :
    taoGatedRejectedMass (geom2PNatListPMF n)
        (taoSection6GlobalTypical CA n) f =
      taoSection6GlobalFailureMass CA n := by
  rw [taoGatedRejectedMass_eq_toOuterMeasure]
  rfl

/-- Symbolic Section 6 aggregation, uniformly in the output map. The native
global exceptional mass is charged once; no concentration or slice-decay
estimate is assumed here. -/
theorem exists_unitSourceMappedOscillation_le_slice_sum_add_globalFailure
    (CA : ℝ) (hCA : 17 ≤ CA) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ n : ℕ, N0 ≤ n → ∀ m : ℕ, m ≤ n →
        ∀ f : List ℕ+ → ZMod (3 ^ n),
          taoZModPowOscillation m n
              (fun y => ((geom2PNatListPMF n).map f y).toReal) ≤
            (∑ k : Fin n, ∑ l : Fin (2 * n),
              taoZModPowOscillation m n (unitSourceMappedSlice CA n k l f)) +
              2 * taoSection6GlobalFailureMass CA n := by
  obtain ⟨N0, hsubset⟩ :=
    exists_taoSection6GlobalTypical_subset_localUnionGate CA hCA
  refine ⟨max N0 2, le_max_right _ _, ?_⟩
  intro n hn m hmn f
  have hn0 : N0 ≤ n := (le_max_left N0 2).trans hn
  have hrejected :
      taoGatedRejectedMass (geom2PNatListPMF n)
          (taoSection6LocalUnionGate CA n) f ≤
        taoGatedRejectedMass (geom2PNatListPMF n)
          (taoSection6GlobalTypical CA n) f :=
    taoGatedRejectedMass_mono (geom2PNatListPMF n) f (hsubset n hn0)
  calc
    taoZModPowOscillation m n
        (fun y => ((geom2PNatListPMF n).map f y).toReal) ≤
      taoZModPowOscillation m n (unitSourceMappedLocalUnion CA n f) +
        2 * taoGatedRejectedMass (geom2PNatListPMF n)
          (taoSection6LocalUnionGate CA n) f :=
      taoZModPowOscillation_map_le_gated_add_two_rejected
        (geom2PNatListPMF n) (taoSection6LocalUnionGate CA n) hmn f
    _ ≤ (∑ k : Fin n, ∑ l : Fin (2 * n),
          taoZModPowOscillation m n (unitSourceMappedSlice CA n k l f)) +
        2 * taoGatedRejectedMass (geom2PNatListPMF n)
          (taoSection6GlobalTypical CA n) f :=
      add_le_add (unitSourceMappedLocalUnionOscillation_le_sum_sum CA m n f)
        (mul_le_mul_of_nonneg_left hrejected (by norm_num))
    _ = (∑ k : Fin n, ∑ l : Fin (2 * n),
          taoZModPowOscillation m n (unitSourceMappedSlice CA n k l f)) +
        2 * taoSection6GlobalFailureMass CA n := by
      rw [unitSourceMappedGlobalRejected_eq_failure]

#print axioms exists_unitSourceMappedOscillation_le_slice_sum_add_globalFailure

end

end Erdos1135.Tao
