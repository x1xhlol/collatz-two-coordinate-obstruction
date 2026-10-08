import Erdos1135.Tao.Fourier.OscillationAlgebra
import Erdos1135.Tao.Fourier.Section7SourceLaw
import Erdos1135.Tao.Section6.GatePartition

/-!
# Section 6 Event Aggregation

This leaf replaces the full Syracuse source law by the enlarged parent local
gate once, charges its complement once, and then applies the exact disjoint
slice partition.  Concentration and polynomial slice summation are separate
later producers.
-/

open scoped BigOperators

namespace Erdos1135
namespace Tao

noncomputable section

/-- Source mass outside the repaired global typical event. -/
noncomputable def taoSection6GlobalFailureMass (CA : ℝ) (n : ℕ) : ℝ :=
  ((geom2PNatListPMF n).toOuterMeasure
    {full | ¬ taoSection6GlobalTypical CA n full}).toReal

theorem taoSection6GlobalFailureMass_eq_rejectedMass
    (CA : ℝ) (n : ℕ) :
    taoSection6GlobalFailureMass CA n =
      taoGatedRejectedMass
        (geom2PNatListPMF n)
        (taoSection6GlobalTypical CA n)
        (taoSection7OffsetZMod n) := by
  unfold taoSection6GlobalFailureMass
  rw [taoGatedRejectedMass_eq_toOuterMeasure]

/-- The full source law is within twice the parent local-union rejection mass
of the enlarged local-union submass. -/
theorem syracFineScaleOscillation_le_localUnion_add_two_rejected
    (CA : ℝ) {m n : ℕ} (hmn : m ≤ n) :
    syracFineScaleOscillation m n ≤
      taoZModPowOscillation m n (taoSection6LocalUnionSubmass CA n) +
        2 * taoGatedRejectedMass
          (geom2PNatListPMF n)
          (taoSection6LocalUnionGate CA n)
          (taoSection7OffsetZMod n) := by
  unfold syracFineScaleOscillation syracPMFMassVector
  rw [syracPMF_eq_geom2PNatListPMF_map_taoSection7OffsetZMod]
  exact taoZModPowOscillation_map_le_gated_add_two_rejected
    (geom2PNatListPMF n) (taoSection6LocalUnionGate CA n) hmn
      (taoSection7OffsetZMod n)

/-- Exact local-union partition followed by finite-sum subadditivity. -/
theorem taoSection6LocalUnionOscillation_le_sum_sum
    (CA : ℝ) (m n : ℕ) :
    taoZModPowOscillation m n (taoSection6LocalUnionSubmass CA n) ≤
      ∑ k : Fin n, ∑ l : Fin (2 * n),
        taoZModPowOscillation m n
          (taoSection6FixedAmbientSubmass CA n k l) := by
  calc
    taoZModPowOscillation m n (taoSection6LocalUnionSubmass CA n) =
        taoZModPowOscillation m n
          (fun y => ∑ i : taoSection6LocalGateIndex n,
            taoSection6FixedAmbientSubmass CA n i.1 i.2 y) := by
              congr 1
              funext y
              exact taoSection6LocalUnionSubmass_eq_sum CA n y
    _ ≤ ∑ i : taoSection6LocalGateIndex n,
        taoZModPowOscillation m n
          (taoSection6FixedAmbientSubmass CA n i.1 i.2) :=
      taoZModPowOscillation_sum_le_sum m n
        (fun i : taoSection6LocalGateIndex n =>
          taoSection6FixedAmbientSubmass CA n i.1 i.2)
    _ = ∑ k : Fin n, ∑ l : Fin (2 * n),
        taoZModPowOscillation m n
          (taoSection6FixedAmbientSubmass CA n k l) :=
      Fintype.sum_prod_type _

/-- Source-facing symbolic Section 6 aggregation: all fixed slices plus one
global exceptional mass.  It assumes no concentration estimate. -/
theorem exists_syracFineScaleOscillation_le_fixedAmbient_sum_add_globalFailure
    (CA : ℝ) (hCA : 17 ≤ CA) :
    ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ n : ℕ, N0 ≤ n →
        ∀ m : ℕ, m ≤ n →
          syracFineScaleOscillation m n ≤
            (∑ k : Fin n, ∑ l : Fin (2 * n),
              taoZModPowOscillation m n
                (taoSection6FixedAmbientSubmass CA n k l)) +
              2 * taoSection6GlobalFailureMass CA n := by
  obtain ⟨N0, hsubset⟩ :=
    exists_taoSection6GlobalTypical_subset_localUnionGate CA hCA
  refine ⟨max N0 2, le_max_right _ _, ?_⟩
  intro n hn m hmn
  have hn0 : N0 ≤ n := (le_max_left N0 2).trans hn
  have hrejected :
      taoGatedRejectedMass
          (geom2PNatListPMF n)
          (taoSection6LocalUnionGate CA n)
          (taoSection7OffsetZMod n) ≤
        taoGatedRejectedMass
          (geom2PNatListPMF n)
          (taoSection6GlobalTypical CA n)
          (taoSection7OffsetZMod n) :=
    taoGatedRejectedMass_mono
      (geom2PNatListPMF n) (taoSection7OffsetZMod n)
        (hsubset n hn0)
  calc
    syracFineScaleOscillation m n ≤
        taoZModPowOscillation m n (taoSection6LocalUnionSubmass CA n) +
          2 * taoGatedRejectedMass
            (geom2PNatListPMF n)
            (taoSection6LocalUnionGate CA n)
            (taoSection7OffsetZMod n) :=
      syracFineScaleOscillation_le_localUnion_add_two_rejected CA hmn
    _ ≤ (∑ k : Fin n, ∑ l : Fin (2 * n),
          taoZModPowOscillation m n
            (taoSection6FixedAmbientSubmass CA n k l)) +
        2 * taoGatedRejectedMass
          (geom2PNatListPMF n)
          (taoSection6GlobalTypical CA n)
          (taoSection7OffsetZMod n) := by
      exact add_le_add
        (taoSection6LocalUnionOscillation_le_sum_sum CA m n)
        (mul_le_mul_of_nonneg_left hrejected (by norm_num))
    _ = (∑ k : Fin n, ∑ l : Fin (2 * n),
          taoZModPowOscillation m n
            (taoSection6FixedAmbientSubmass CA n k l)) +
        2 * taoSection6GlobalFailureMass CA n := by
      rw [taoSection6GlobalFailureMass_eq_rejectedMass]

end

end Tao
end Erdos1135
