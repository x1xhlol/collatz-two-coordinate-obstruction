import Erdos1135.Tao.Section5.DescentScale
import Erdos1135.Tao.Syracuse.AffineEnvelope
import Erdos1135.Tao.Probability.Geom2LowWeight

/-!
# Section 5 Deterministic Descent

This leaf combines the checked affine envelope with the Section 5 scale
packet.  It contains no PMF comparison, Proposition 1.9 output, or no-hit
probability estimate.
-/

namespace Erdos1135
namespace Tao

open Filter

/-- A scheduled source with inclusive high valuation weight is below the
ambient threshold after the scheduled number of Syracuse steps. -/
theorem TaoSection5DescentScaleFacts.iterate_le_threshold
    {B : ℕ} (facts : TaoSection5DescentScaleFacts B)
    {N : {N : ℕ // Odd N}} {branch : TaoSection5SourceBranch}
    (hmem : N.1 ∈ oddLogWindow
      (taoSection5SourceLo B branch) (taoSection5SourceHi B branch))
    (hweight :
      19 * taoSection5N0 B ≤
        10 * taoTupleWeight
          (syracuseValuationPNatList (taoSection5N0 B) N.1 N.2)) :
    (syracuse^[taoSection5N0 B]) N.1 ≤ B := by
  have hrat := syracuse_iterate_le_affine_envelope
    (taoSection5N0 B) N.1 N.2
  have hcast :
      (((syracuse^[taoSection5N0 B]) N.1 : ℚ) : ℝ) ≤
        (((3 : ℚ) ^ taoSection5N0 B /
            (2 : ℚ) ^ taoTupleWeight
              (syracuseValuationPNatList (taoSection5N0 B) N.1 N.2) *
            (N.1 : ℚ) + (3 : ℚ) ^ taoSection5N0 B : ℚ) : ℝ) :=
    Rat.cast_le.mpr hrat
  have hreal :
      ((syracuse^[taoSection5N0 B]) N.1 : ℝ) ≤
        (((3 : ℚ) ^ taoSection5N0 B /
              (2 : ℚ) ^ taoTupleWeight
                (syracuseValuationPNatList (taoSection5N0 B) N.1 N.2) : ℚ) : ℝ) *
            (N.1 : ℝ) +
          (3 : ℝ) ^ taoSection5N0 B := by
    norm_num only [Rat.cast_add, Rat.cast_mul, Rat.cast_pow,
      Rat.cast_natCast, Rat.cast_ofNat] at hcast ⊢
    exact hcast
  have hscaled := add_le_add (facts.main_term hweight hmem) facts.offset
  have hfinal : ((syracuse^[taoSection5N0 B]) N.1 : ℝ) ≤ (B : ℝ) :=
    hreal.trans (hscaled.trans facts.absorption)
  exact_mod_cast hfinal

/-- The deterministic bound supplies a hit witness at the scheduled time. -/
theorem TaoSection5DescentScaleFacts.hitsAtMost
    {B : ℕ} (facts : TaoSection5DescentScaleFacts B)
    {N : {N : ℕ // Odd N}} {branch : TaoSection5SourceBranch}
    (hmem : N.1 ∈ oddLogWindow
      (taoSection5SourceLo B branch) (taoSection5SourceHi B branch))
    (hweight :
      19 * taoSection5N0 B ≤
        10 * taoTupleWeight
          (syracuseValuationPNatList (taoSection5N0 B) N.1 N.2)) :
    syracuseHitsAtMost N.1 B := by
  exact ⟨taoSection5N0 B, facts.iterate_le_threshold hmem hweight⟩

/-- No hit forces the actual valuation list into the strict low-weight event.
The equality boundary belongs to deterministic descent. -/
theorem TaoSection5DescentScaleFacts.actualValuations_mem_low_of_not_hitsAtMost
    {B : ℕ} (facts : TaoSection5DescentScaleFacts B)
    {N : {N : ℕ // Odd N}} {branch : TaoSection5SourceBranch}
    (hmem : N.1 ∈ oddLogWindow
      (taoSection5SourceLo B branch) (taoSection5SourceHi B branch))
    (hno : ¬ syracuseHitsAtMost N.1 B) :
    syracuseValuationPNatList (taoSection5N0 B) N.1 N.2 ∈
      taoLowValuationWeightEvent (taoSection5N0 B) := by
  change
    10 * taoTupleWeight
        (syracuseValuationPNatList (taoSection5N0 B) N.1 N.2) <
      19 * taoSection5N0 B
  by_contra hlow
  have hweight :
      19 * taoSection5N0 B ≤
        10 * taoTupleWeight
          (syracuseValuationPNatList (taoSection5N0 B) N.1 N.2) := by
    omega
  exact hno (facts.hitsAtMost hmem hweight)

/-- Eventual branch-uniform form consumed by the native no-hit probability
assembly after this deterministic leaf. -/
theorem eventually_taoSection5_actualValuations_mem_low_of_not_hitsAtMost :
    ∀ᶠ B : ℕ in atTop,
      ∀ branch : TaoSection5SourceBranch, ∀ N : {N : ℕ // Odd N},
        N.1 ∈ oddLogWindow
            (taoSection5SourceLo B branch) (taoSection5SourceHi B branch) →
          ¬ syracuseHitsAtMost N.1 B →
            syracuseValuationPNatList (taoSection5N0 B) N.1 N.2 ∈
              taoLowValuationWeightEvent (taoSection5N0 B) := by
  filter_upwards [eventually_taoSection5DescentScaleFacts] with B facts
  intro branch N hmem hno
  exact facts.actualValuations_mem_low_of_not_hitsAtMost hmem hno

end Tao
end Erdos1135
