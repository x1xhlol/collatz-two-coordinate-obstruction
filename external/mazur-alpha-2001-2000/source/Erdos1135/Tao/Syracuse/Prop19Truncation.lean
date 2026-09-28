import Erdos1135.Tao.Syracuse.Prop19Laws
import Erdos1135.Tao.Syracuse.TruncatedValuationTV

/-!
# Scale-free truncation kernel for Proposition 1.9

This module composes the checked actual-source and canonical decoder squares
with finite data processing and sharp strict-truncation recovery.  The result
reduces the full valuation-list distance to source residue TV and one ideal
Geom(2) overflow atom, without a scale hypothesis or an actual-tail term.
-/

namespace Erdos1135
namespace Tao

noncomputable section

/-- Full-L1 valuation distance appearing in the conclusion of Proposition 1.9. -/
noncomputable def taoProp19ValuationTV (μ : PMF TaoOddNat) (n : ℕ) : ℝ :=
  taoPMFFullL1 (taoProp19ActualValuationLaw μ n) (geom2PNatListPMF n)

/-- The zero-length actual and ideal valuation laws agree exactly. -/
theorem taoProp19ValuationTV_zero (μ : PMF TaoOddNat) :
    taoProp19ValuationTV μ 0 = 0 := by
  rw [taoProp19ValuationTV, taoProp19ActualValuationLaw_zero]
  simp [taoPMFFullL1]

/-- Scale-free Proposition 1.9 kernel.  Only source residue TV and the ideal
strict-overflow atom remain; no actual valuation tail is charged. -/
theorem taoProp19ValuationTV_le_sourceTV_add_two_overflow
    (μ : PMF TaoOddNat) (n M : ℕ) :
    taoProp19ValuationTV μ n ≤
      taoTV
          (taoProp19SourceResidueLaw μ M)
          (taoCanonicalUniformOddResiduePMF M) +
        2 * (truncatedValuationTupleGeom2PMF n M none).toReal := by
  let T := truncateValuationList n M
  let decoder := taoProp19ResidueDecoder n M
  have hactual :
      (taoProp19SourceResidueLaw μ M).map decoder =
        (taoProp19ActualValuationLaw μ n).map T := by
    simpa [T, decoder] using
      taoProp19SourceResidueLaw_map_decoder μ n M
  have hideal :
      (geom2PNatListPMF n).map T =
        truncatedValuationTupleGeom2PMF n M := by
    simpa [T] using geom2PNatListPMF_map_truncateValuationList n M
  have hcanonical :
      (taoCanonicalUniformOddResiduePMF M).map decoder =
        truncatedValuationTupleGeom2PMF n M := by
    simpa [decoder] using
      taoCanonicalUniformOddResiduePMF_map_decoder n M
  have htv :
      taoTV
          ((taoProp19ActualValuationLaw μ n).map T)
          ((geom2PNatListPMF n).map T) =
        taoTV
          ((taoProp19SourceResidueLaw μ M).map decoder)
          ((taoCanonicalUniformOddResiduePMF M).map decoder) := by
    rw [← hactual, hideal, ← hcanonical]
  unfold taoProp19ValuationTV
  calc
    taoPMFFullL1 (taoProp19ActualValuationLaw μ n) (geom2PNatListPMF n) ≤
        taoTV
            ((taoProp19ActualValuationLaw μ n).map T)
            ((geom2PNatListPMF n).map T) +
          2 * (((geom2PNatListPMF n).map T) none).toReal :=
      taoPMFFullL1_le_truncated_taoTV_add_two_right_none
        (taoProp19ActualValuationLaw μ n) (geom2PNatListPMF n) n M
    _ = taoTV
          ((taoProp19SourceResidueLaw μ M).map decoder)
          ((taoCanonicalUniformOddResiduePMF M).map decoder) +
        2 * (truncatedValuationTupleGeom2PMF n M none).toReal := by
      rw [htv, hideal]
    _ ≤ taoTV
          (taoProp19SourceResidueLaw μ M)
          (taoCanonicalUniformOddResiduePMF M) +
        2 * (truncatedValuationTupleGeom2PMF n M none).toReal := by
      exact add_le_add_left
        (taoTV_map_le
          (taoProp19SourceResidueLaw μ M)
          (taoCanonicalUniformOddResiduePMF M) decoder) _

end

end Tao
end Erdos1135
