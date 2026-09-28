import Erdos1135.ND.Band.A5ReferenceTerminalCap
import Erdos1135.ND.Probability.Geom2FiniteTwoEventTail

/-!
# A5 finite exterior coefficient tail

This route-facing leaf first caps the native endpoint-fiber weight on the
retained exterior carrier and then charges that carrier to the full-list upper
event and predecessor-prefix lower event.  The high-envelope remainder stays
separate with its previously checked power saving.
-/

namespace Erdos1135
namespace ND

open scoped BigOperators

noncomputable section

/-- Normalized positive centered threshold forced by a strict exterior
endpoint. -/
noncomputable def ndA5ReferenceExteriorUpperThreshold
    (B : ℕ) (C : ℝ) : ℝ :=
  ((4 / 25 : ℝ) * ndA5TubeWidth B C) / Real.log 2

/-- Predecessor-prefix threshold after paying the checked first-passage
buffer. -/
noncomputable def ndA5ReferenceExteriorLowerThreshold
    (B : ℕ) (C : ℝ) : ℝ :=
  ndA5ReferenceExteriorUpperThreshold B C - 3

/-- Sum of the two exact-length Bernstein charges used by exterior H. -/
noncomputable def ndA5ReferenceExteriorTwoEventTail
    (B : ℕ) (C : ℝ) : ℝ :=
  2 * Real.exp
      (-min
        ((ndA5ReferenceExteriorUpperThreshold B C) ^ 2 /
          (32 * (Tao.taoSection5M0 B : ℝ)))
        (ndA5ReferenceExteriorUpperThreshold B C / 8)) +
    2 * Real.exp
      (-min
        ((ndA5ReferenceExteriorLowerThreshold B C) ^ 2 /
          (32 * ((Tao.taoSection5M0 B - 1 : ℕ) : ℝ)))
        (ndA5ReferenceExteriorLowerThreshold B C / 8))

set_option maxHeartbeats 400000 in
/-- Conditional finite exterior coefficient estimate.  The two displayed
factors `2` are precisely the two checked absolute Bernstein tails; there is
no additional union factor. -/
theorem ndA5ReferenceExteriorCoefficient_le_twoEventTail_add_three_mul_rpow
    {B : ℕ} {C : ℝ} {E : Set ℕ}
    (facts : Tao.TaoSection5PassLostWindowFacts B)
    (hcap : NDA5EndpointTerminalCapBudget B)
    (hm : 2 ≤ Tao.taoSection5M0 B)
    (htube : 3 < ndA5ReferenceExteriorUpperThreshold B C)
    {q : ℕ} {X : ZMod (3 ^ q)}
    (hindex : Tao.taoSection5M0 B + q ≤ Tao.taoSection5N0 B) :
    Tao.taoSection5PayloadFreeCoefficient q
        (ndA5ReferenceExteriorEndpoints B C E) X ≤
      (Real.log B + 1) *
        ndA5ReferenceExteriorTwoEventTail B C +
        3 * (B : ℝ) ^ (-(4997 / 600000 : ℝ)) := by
  classical
  let S := ndA5ReferenceExteriorEndpointValuationCarrier B C E q X
  have hu : 0 < ndA5ReferenceExteriorUpperThreshold B C := by linarith
  have hv : 0 < ndA5ReferenceExteriorLowerThreshold B C := by
    unfold ndA5ReferenceExteriorLowerThreshold
    linarith
  have hlength : ∀ bs ∈ S, bs.length = Tao.taoSection5M0 B := by
    intro bs hbs
    exact ndA5EndpointValuationFilterCarrier_length
      (P := ndA5ReferenceEndpointExteriorAt B C)
      (by
        simpa only [S, ndA5ReferenceExteriorEndpointValuationCarrier] using
          hbs)
  have htail : ∀ bs ∈ S,
      ndA5ReferenceExteriorUpperThreshold B C <
          Tao.taoGeom2CenteredListWeight bs ∨
        Tao.taoGeom2CenteredListWeight bs.dropLast <
          -ndA5ReferenceExteriorLowerThreshold B C := by
    intro bs hbs
    simpa only [ndA5ReferenceExteriorUpperThreshold,
      ndA5ReferenceExteriorLowerThreshold, S] using
      (ndA5ReferenceExteriorCarrier_centeredTail facts hbs)
  have hmass :
      (∑ bs ∈ S, Tao.geom2PNatListMass bs) ≤
        ndA5ReferenceExteriorTwoEventTail B C := by
    simpa only [ndA5ReferenceExteriorTwoEventTail] using
      (sum_geom2PNatListMass_le_centeredUpper_add_dropLastLower_min
        hm S hu hv hlength htail)
  have hpreterminal :
      2 * 3 ^ (Tao.taoSection5M0 B - 1) ≤ B := by
    exact_mod_cast facts.preterminal_offset_room
  have hB : 1 < B := by
    have hpow : 0 < 3 ^ (Tao.taoSection5M0 B - 1) := by positivity
    omega
  have hfactor : 0 ≤ Real.log B + 1 := by
    have hlog : 0 ≤ Real.log (B : ℝ) :=
      Real.log_nonneg (by exact_mod_cast hB.le)
    linarith
  have hnative :
      (∑ bs ∈ S, Tao.geom2PNatListNativeBase bs) ≤
        (Real.log B + 1) *
          ndA5ReferenceExteriorTwoEventTail B C := by
    calc
      (∑ bs ∈ S, Tao.geom2PNatListNativeBase bs) ≤
          ∑ bs ∈ S, (Real.log B + 1) * Tao.geom2PNatListMass bs := by
        apply Finset.sum_le_sum
        intro bs hbs
        exact ndA5ReferenceExteriorCarrier_nativeBase_le_log_add_one_mul_mass
          facts hcap (by simpa only [S] using hbs)
      _ = (Real.log B + 1) *
          ∑ bs ∈ S, Tao.geom2PNatListMass bs := by
        rw [Finset.mul_sum]
      _ ≤ (Real.log B + 1) *
          ndA5ReferenceExteriorTwoEventTail B C :=
        mul_le_mul_of_nonneg_left hmass hfactor
  calc
    Tao.taoSection5PayloadFreeCoefficient q
        (ndA5ReferenceExteriorEndpoints B C E) X ≤
      (∑ bs ∈ S, Tao.geom2PNatListNativeBase bs) +
        3 * (B : ℝ) ^ (-(4997 / 600000 : ℝ)) := by
      simpa only [S] using
        ndA5ReferenceExteriorCoefficient_le_nativeBase_add_three_mul_rpow
          facts hindex
    _ ≤ (Real.log B + 1) * ndA5ReferenceExteriorTwoEventTail B C +
        3 * (B : ℝ) ^ (-(4997 / 600000 : ℝ)) :=
      add_le_add hnative le_rfl

end
end ND
end Erdos1135
