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
import Erdos1135Predecessor.Tao.Fourier.Section7SourceLaw
import Erdos1135Predecessor.Tao.Section6.GatePartition

open scoped BigOperators

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

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

end

end Tao

end Erdos1135Predecessor
