import Erdos1135.ND.Band.A5HarmonicProp19
import Erdos1135.ND.Band.A5PrefixGood

/-!
# Harmonic FullGood Complement On One Exact Band

This leaf transfers the exact-band Proposition 1.9 valuation estimate to the
literal strict FullGood complement, then applies the positive-prefix Geom(2)
tail.  Project total variation is full L1, so the event transfer has
coefficient one.  The public width-six guard supplies both the positive
valuation horizon and the positive strict integer radius.
-/

namespace Erdos1135
namespace ND

noncomputable section

/-- A supplied full valuation-list L1 bound controls the exact strict
FullGood complement by the matching ideal prefix-bad event plus that error. -/
theorem ndA5HarmonicBandPMF_fullPrefixGoodComplMass_le_ideal_add
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C ε : ℝ}
    (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch)
    (hW : 0 < ndA5TubeWidth B C)
    (hval :
      Tao.taoProp19ValuationTV
        (ndA5HarmonicBandPMF B branch j hB hcount)
        (Tao.taoSection5N0 B) ≤ ε) :
    ((ndA5HarmonicBandPMF B branch j hB hcount).toOuterMeasure
        (ndA5FullPrefixGoodEvent B C)ᶜ).toReal ≤
      ((Tao.geom2PNatListPMF (Tao.taoSection5N0 B)).toOuterMeasure
        (Tao.taoGeom2PrefixBadEvent
          (ndA5TubeRadius (ndA5TubeWidth B C) : ℝ)
          (Tao.taoSection5N0 B))).toReal + ε := by
  let μ := ndA5HarmonicBandPMF B branch j hB hcount
  let n := Tao.taoSection5N0 B
  let Bad := Tao.taoGeom2PrefixBadEvent
    (ndA5TubeRadius (ndA5TubeWidth B C) : ℝ) n
  have hval' :
      Tao.taoPMFFullL1
          (Tao.taoProp19ActualValuationLaw μ n)
          (Tao.geom2PNatListPMF n) ≤ ε := by
    simpa only [Tao.taoProp19ValuationTV, μ, n] using hval
  have hcompare :=
    Tao.pmfOuterMass_le_add_of_taoPMFFullL1_le
      (p := Tao.taoProp19ActualValuationLaw μ n)
      (q := Tao.geom2PNatListPMF n) (E := Bad) hval'
  calc
    ((ndA5HarmonicBandPMF B branch j hB hcount).toOuterMeasure
        (ndA5FullPrefixGoodEvent B C)ᶜ).toReal =
      ((Tao.taoProp19ActualValuationLaw μ n).toOuterMeasure Bad).toReal := by
        rw [ndA5FullPrefixGoodEvent_compl_eq_preimage_prefixBad hW]
        unfold Tao.taoProp19ActualValuationLaw
        rw [PMF.toOuterMeasure_map_apply]
    _ ≤ ((Tao.geom2PNatListPMF n).toOuterMeasure Bad).toReal + ε :=
      hcompare
    _ = ((Tao.geom2PNatListPMF (Tao.taoSection5N0 B)).toOuterMeasure
        (Tao.taoGeom2PrefixBadEvent
          (ndA5TubeRadius (ndA5TubeWidth B C) : ℝ)
          (Tao.taoSection5N0 B))).toReal + ε := by rfl

/-- The exact harmonic band law pays the literal FullGood failure with the
positive-prefix Geom(2) tail plus the checked Proposition 1.9 error. -/
theorem ndA5HarmonicBandPMF_fullPrefixGoodComplMass_le
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C : ℝ}
    (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch)
    (hWlarge : 6 ≤ ndA5TubeWidth B C) :
    ((ndA5HarmonicBandPMF B branch j hB hcount).toOuterMeasure
        (ndA5FullPrefixGoodEvent B C)ᶜ).toReal ≤
      2 * (Tao.taoSection5N0 B : ℝ) *
        Real.exp
          (-min
            ((ndA5TubeRadius (ndA5TubeWidth B C) : ℝ) ^ 2 /
              (32 * (Tao.taoSection5N0 B : ℝ)))
            ((ndA5TubeRadius (ndA5TubeWidth B C) : ℝ) / 8)) +
      4 * (2 : ℝ) ^
        (-((1 / 128 : ℝ) * (Tao.taoSection5N0 B : ℝ))) := by
  let n := Tao.taoSection5N0 B
  let W := ndA5TubeWidth B C
  let Rn := ndA5TubeRadius W
  let R : ℝ := Rn
  have hW : 0 < W := by
    dsimp [W]
    linarith
  have hn : 0 < n := by
    by_contra hn
    have hnzero : n = 0 := Nat.eq_zero_of_not_pos hn
    have hWzero : W = 0 := by
      simp [W, ndA5TubeWidth, n, hnzero]
    linarith
  have hM : 1 ≤ Tao.taoSection5NPrime B := by
    unfold Tao.taoSection5NPrime
    dsimp [n] at hn
    omega
  have hvaluation :=
    taoProp19ValuationTV_ndA5HarmonicBandPMF_le
      hB j hcount hM
  have htransfer :=
    ndA5HarmonicBandPMF_fullPrefixGoodComplMass_le_ideal_add
      hB hcount (by simpa only [W] using hW) hvaluation
  have hceilReal : (6 : ℝ) ≤ (Nat.ceil W : ℕ) :=
    hWlarge.trans (by simpa only [W] using Nat.le_ceil W)
  have hceilNat : 6 ≤ Nat.ceil W := by exact_mod_cast hceilReal
  have hRn : 0 < Rn := by
    dsimp [Rn]
    unfold ndA5TubeRadius
    omega
  have hR : 0 < R := by
    dsimp [R]
    exact_mod_cast hRn
  have htail :=
    Tao.geom2PNatListPMF_prefixBad_le_nat_mul hn hR
  calc
    ((ndA5HarmonicBandPMF B branch j hB hcount).toOuterMeasure
        (ndA5FullPrefixGoodEvent B C)ᶜ).toReal ≤
      ((Tao.geom2PNatListPMF n).toOuterMeasure
        (Tao.taoGeom2PrefixBadEvent R n)).toReal +
          4 * (2 : ℝ) ^ (-((1 / 128 : ℝ) * (n : ℝ))) := by
            simpa only [n, W, Rn, R] using htransfer
    _ ≤ (n : ℝ) *
          (2 * Real.exp
            (-min (R ^ 2 / (32 * (n : ℝ))) (R / 8))) +
        4 * (2 : ℝ) ^ (-((1 / 128 : ℝ) * (n : ℝ))) :=
      add_le_add htail le_rfl
    _ = 2 * (Tao.taoSection5N0 B : ℝ) *
          Real.exp
            (-min
              ((ndA5TubeRadius (ndA5TubeWidth B C) : ℝ) ^ 2 /
                (32 * (Tao.taoSection5N0 B : ℝ)))
              ((ndA5TubeRadius (ndA5TubeWidth B C) : ℝ) / 8)) +
        4 * (2 : ℝ) ^
          (-((1 / 128 : ℝ) * (Tao.taoSection5N0 B : ℝ))) := by
            dsimp [n, W, Rn, R]
            ring

end

end ND
end Erdos1135
