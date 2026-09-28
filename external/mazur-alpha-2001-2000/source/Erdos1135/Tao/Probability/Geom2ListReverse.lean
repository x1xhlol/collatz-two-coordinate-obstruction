import Erdos1135.Tao.Probability.Geom2ListProjectivity
import Erdos1135.Tao.Syracuse.AffineReverse

/-!
# Geom(2) List Reversal

The fixed-length iid positive Geom(2) list law is invariant under list
reversal.  The proof is pointwise and includes wrong-length lists.
-/

namespace Erdos1135
namespace Tao

noncomputable section

theorem geom2PNatListMass_reverse (as : List ℕ+) :
    geom2PNatListMass as.reverse = geom2PNatListMass as := by
  simp only [geom2PNatListMass_eq_inv_pow, taoTupleWeight_reverse]

theorem geom2PNatListPMF_apply_reverse (n : ℕ) (as : List ℕ+) :
    geom2PNatListPMF n as.reverse = geom2PNatListPMF n as := by
  by_cases hlen : as.length = n
  · apply (ENNReal.toReal_eq_toReal_iff'
      (PMF.apply_ne_top (geom2PNatListPMF n) as.reverse)
      (PMF.apply_ne_top (geom2PNatListPMF n) as)).mp
    have hlenr : as.reverse.length = n := by simpa using hlen
    calc
      (geom2PNatListPMF n as.reverse).toReal =
          geom2PNatListMass as.reverse := by
        simpa only [hlenr] using
          geom2PNatListPMF_apply_length_toReal as.reverse
      _ = geom2PNatListMass as := geom2PNatListMass_reverse as
      _ = (geom2PNatListPMF n as).toReal := by
        simpa only [hlen] using
          (geom2PNatListPMF_apply_length_toReal as).symm
  · have hlenr : as.reverse.length ≠ n := by simpa using hlen
    rw [geom2PNatListPMF_apply_eq_zero_of_length_ne n as.reverse hlenr,
      geom2PNatListPMF_apply_eq_zero_of_length_ne n as hlen]

/-- Reversal preserves the complete fixed-length iid list PMF. -/
theorem geom2PNatListPMF_map_reverse (n : ℕ) :
    (geom2PNatListPMF n).map List.reverse = geom2PNatListPMF n := by
  classical
  apply PMF.ext
  intro as
  rw [PMF.map_apply]
  rw [tsum_eq_single as.reverse]
  · simp [geom2PNatListPMF_apply_reverse]
  · intro bs hbs
    have hne : ¬ as = bs.reverse := by
      intro h
      apply hbs
      calc
        bs = bs.reverse.reverse := by simp
        _ = as.reverse := by rw [← h]
    simp [hne]

end

end Tao
end Erdos1135
