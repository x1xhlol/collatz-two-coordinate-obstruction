import CanonicalEnvelopeNormalization
import PadicBinaryEnvelopeTransfer
import PadicIntegerEnvelopeIntegral

set_option autoImplicit false

open MeasureTheory
open scoped ENNReal
open Erdos1135.Tao
open CollatzCylinderPacking.Arithmetic

namespace CollatzCanonical.IntegerStationaryEnvelope

theorem canonicalIntegerEnvelope_normalized_withDensity :
    padicThreeHaar.withDensity
      (fun x => (∫⁻ y, canonicalIntegerEnvelope y ∂padicThreeHaar)⁻¹ *
        canonicalIntegerEnvelope x) = canonicalSyracuseMeasure := by
  apply padicBinaryTransfer_normalized_eq_canonical
    canonicalIntegerEnvelope_lowerSemicontinuous.measurable
  · exact ne_of_lt (canonicalIntegerEnvelope_lintegral_le_one.trans_lt (by finiteness))
  · exact ne_of_gt canonicalIntegerEnvelope_lintegral_pos
  · exact canonicalIntegerEnvelope_transfer_le

theorem canonicalIntegerEnvelope_lintegral_eq_one :
    (∫⁻ x, canonicalIntegerEnvelope x ∂padicThreeHaar) = 1 := by
  apply canonicalIntegerEnvelope_normalizing_mass_eq_one
    canonicalIntegerEnvelope_lintegral_pos canonicalIntegerEnvelope_lintegral_le_one
  · obtain ⟨c, hc, _hfin, hfloor⟩ := canonicalIntegerEnvelope_uniform_unit_floor
    exact hc.trans_le (hfloor 1 isUnit_one)
  · exact canonicalIntegerEnvelope_normalized_withDensity

theorem canonicalIntegerEnvelope_withDensity :
    padicThreeHaar.withDensity canonicalIntegerEnvelope = canonicalSyracuseMeasure := by
  have h := canonicalIntegerEnvelope_normalized_withDensity
  simpa only [canonicalIntegerEnvelope_lintegral_eq_one, inv_one, one_mul] using h

theorem canonicalIntegerEnvelope_stationary :
    IsSyracuseStationary (padicThreeHaar.withDensity canonicalIntegerEnvelope) := by
  exact padicWithDensity_stationary_of_transfer_le
    canonicalIntegerEnvelope_lowerSemicontinuous.measurable
    (ne_of_lt (canonicalIntegerEnvelope_lintegral_le_one.trans_lt (by finiteness)))
    canonicalIntegerEnvelope_transfer_le

#print axioms canonicalIntegerEnvelope_lintegral_eq_one
#print axioms canonicalIntegerEnvelope_withDensity
#print axioms canonicalIntegerEnvelope_stationary

end CollatzCanonical.IntegerStationaryEnvelope
