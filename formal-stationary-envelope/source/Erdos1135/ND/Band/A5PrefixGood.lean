import Erdos1135.ND.Band.A5Physical
import Erdos1135.Tao.Probability.Geom2PrefixTypical
import Erdos1135.Tao.Section5.PassTypicalEvent
import Erdos1135.Tao.Syracuse.AffineTrajectory

/-!
# A5 Strict Full-Prefix Good Event

This leaf freezes the literal frozen-v10 prefix tube and identifies its
complement with one positive-prefix Geom(2) bad event.  The tube width is the
physical `C * sqrt (n0 * log n0)` width, not Tao's wider `log(B)^0.6` slack.
-/

namespace Erdos1135
namespace ND

noncomputable section

/-- Strict frozen-v10 prefix typicality at an arbitrary horizon. -/
def ndA5PrefixGood
    (B : ℕ) (C : ℝ) (r : ℕ) (as : List ℕ+) : Prop :=
  as.length = r ∧
    ∀ k ≤ r,
      |(Tao.taoTupleWeight (as.take k) : ℝ) - 2 * (k : ℝ)| <
        ndA5TubeWidth B C

/-- The strict full-prefix event through the common horizon `n0`. -/
def ndA5FullPrefixGoodEvent (B : ℕ) (C : ℝ) : Set Tao.TaoOddNat :=
  {N | ndA5PrefixGood B C (Tao.taoSection5N0 B)
    (Tao.syracuseValuationPNatList
      (Tao.taoSection5N0 B) N.1 N.2)}

/-- Strict prefix typicality restricts to every earlier horizon. -/
theorem NDA5PrefixGood.take
    {B r : ℕ} {C : ℝ} {as : List ℕ+}
    (hgood : ndA5PrefixGood B C r as) {j : ℕ} (hj : j ≤ r) :
    ndA5PrefixGood B C j (as.take j) := by
  constructor
  · rw [List.length_take, hgood.1, Nat.min_eq_left hj]
  · intro k hk
    rw [List.take_take, Nat.min_eq_left hk]
    exact hgood.2 k (hk.trans hj)

/-- Full-prefix Good gives the literal actual valuation prefix at every
shorter horizon. -/
theorem ndA5FullPrefixGoodEvent_prefix
    {B : ℕ} {C : ℝ} {N : Tao.TaoOddNat} {r : ℕ}
    (hgood : N ∈ ndA5FullPrefixGoodEvent B C)
    (hr : r ≤ Tao.taoSection5N0 B) :
    ndA5PrefixGood B C r
      (Tao.syracuseValuationPNatList r N.1 N.2) := by
  have htake := NDA5PrefixGood.take hgood hr
  simpa only [Tao.syracuseValuationPNatList_take_of_le N.2 hr] using htake

/-- The strict ND tube embeds in Tao's strict typicality predicate whenever
its physical width is no larger than the inherited slack. -/
theorem NDA5PrefixGood.to_taoSection5SourceTypicalTuple
    {B r : ℕ} {C : ℝ} {as : List ℕ+}
    (hwidth : ndA5TubeWidth B C ≤ Tao.taoSection5TypicalSlack B)
    (hgood : ndA5PrefixGood B C r as) :
    Tao.taoSection5SourceTypicalTuple B r as := by
  refine ⟨hgood.1, ?_⟩
  intro k hk
  exact (hgood.2 k hk).trans_le hwidth

/-- Actual-prefix specialization of the strict-to-Tao typicality adapter. -/
theorem ndA5FullPrefixGoodEvent_sourceTypicalPrefix
    {B : ℕ} {C : ℝ} {N : Tao.TaoOddNat} {r : ℕ}
    (hwidth : ndA5TubeWidth B C ≤ Tao.taoSection5TypicalSlack B)
    (hgood : N ∈ ndA5FullPrefixGoodEvent B C)
    (hr : r ≤ Tao.taoSection5N0 B) :
    Tao.taoSection5SourceTypicalTuple B r
      (Tao.syracuseValuationPNatList r N.1 N.2) :=
  NDA5PrefixGood.to_taoSection5SourceTypicalTuple hwidth
    (ndA5FullPrefixGoodEvent_prefix hgood hr)

/-- The deterministic bridge to Tao's closed Good event.  Its direction is
deliberate: it does not transfer Tao's complement estimate to the smaller ND
Good event. -/
theorem ndA5FullPrefixGoodEvent_subset_taoSection5ClosedGoodEvent
    {B : ℕ} {C : ℝ}
    (hwidth : ndA5TubeWidth B C ≤ Tao.taoSection5TypicalSlack B) :
    ndA5FullPrefixGoodEvent B C ⊆ Tao.taoSection5ClosedGoodEvent B := by
  intro N hgood
  exact Tao.TaoSection5SourceTypicalTuple.to_closed
    (ndA5FullPrefixGoodEvent_sourceTypicalPrefix hwidth hgood le_rfl)

/-- Integer absolute values strictly inside a real width are exactly bounded
by the strict radius `ceil(W)-1`.  Integral widths retain the strict endpoint. -/
theorem intCast_abs_lt_iff_natAbs_le_ndA5TubeRadius
    {W : ℝ} (hW : 0 < W) (d : ℤ) :
    |(d : ℝ)| < W ↔ Int.natAbs d ≤ ndA5TubeRadius W := by
  have hceil : 0 < Nat.ceil W := Nat.ceil_pos.mpr hW
  have hradius : ndA5TubeRadius W + 1 = Nat.ceil W := by
    unfold ndA5TubeRadius
    omega
  calc
    |(d : ℝ)| < W ↔ (Int.natAbs d : ℝ) < W := by
      rw [Nat.cast_natAbs]
      norm_cast
    _ ↔ Int.natAbs d < Nat.ceil W := Nat.lt_ceil.symm
    _ ↔ Int.natAbs d ≤ ndA5TubeRadius W := by omega

/-- Failure of a strict real bound at an integer point is the strict bad-event
inequality above the real cast of `ceil(W)-1`. -/
theorem not_intCast_abs_lt_iff_ndA5TubeRadius_lt
    {W : ℝ} (hW : 0 < W) (d : ℤ) :
    (¬ |(d : ℝ)| < W) ↔ (ndA5TubeRadius W : ℝ) < |(d : ℝ)| := by
  rw [intCast_abs_lt_iff_natAbs_le_ndA5TubeRadius hW]
  have habs : |(d : ℝ)| = (Int.natAbs d : ℝ) := by
    rw [Nat.cast_natAbs]
    norm_cast
  rw [habs]
  norm_cast
  omega

/-- The centered Geom(2) list weight lies on the same integer lattice as the
strict prefix deviation. -/
theorem not_abs_taoGeom2CenteredListWeight_lt_iff_ndA5TubeRadius_lt
    {W : ℝ} (hW : 0 < W) (as : List ℕ+) :
    (¬ |Tao.taoGeom2CenteredListWeight as| < W) ↔
      (ndA5TubeRadius W : ℝ) <
        |Tao.taoGeom2CenteredListWeight as| := by
  let d : ℤ := (Tao.taoTupleWeight as : ℤ) - 2 * (as.length : ℤ)
  have hd : Tao.taoGeom2CenteredListWeight as = (d : ℝ) := by
    unfold Tao.taoGeom2CenteredListWeight
    dsimp [d]
    push_cast
    ring
  rw [hd]
  exact not_intCast_abs_lt_iff_ndA5TubeRadius_lt hW d

private theorem taoGeom2CenteredListWeight_take_eq
    {as : List ℕ+} {r k : ℕ} (hlen : as.length = r) (hk : k ≤ r) :
    Tao.taoGeom2CenteredListWeight (as.take k) =
      (Tao.taoTupleWeight (as.take k) : ℝ) - 2 * (k : ℝ) := by
  unfold Tao.taoGeom2CenteredListWeight
  rw [List.length_take, hlen, Nat.min_eq_left hk]

/-- On an exact-length list, failure of the strict ND tube is exactly one
positive-prefix bad event at threshold `ceil(W)-1`.  The zero prefix is
discharged by positivity of `W`. -/
theorem not_ndA5PrefixGood_iff_prefixBad
    {B r : ℕ} {C : ℝ} {as : List ℕ+}
    (hlen : as.length = r) (hW : 0 < ndA5TubeWidth B C) :
    ¬ ndA5PrefixGood B C r as ↔
      as ∈ Tao.taoGeom2PrefixBadEvent
        (ndA5TubeRadius (ndA5TubeWidth B C) : ℝ) r := by
  constructor
  · intro hnot
    have hfail : ¬ ∀ k ≤ r,
        |(Tao.taoTupleWeight (as.take k) : ℝ) - 2 * (k : ℝ)| <
          ndA5TubeWidth B C := by
      intro hall
      exact hnot ⟨hlen, hall⟩
    push Not at hfail
    rcases hfail with ⟨k, hk, hbad⟩
    have hk0 : k ≠ 0 := by
      intro hkZero
      subst k
      have : ndA5TubeWidth B C ≤ 0 := by
        simpa [Tao.taoTupleWeight] using hbad
      linarith
    let j : Fin r := ⟨k - 1, by omega⟩
    refine ⟨j, ?_⟩
    have hj : j.1 + 1 = k := by
      dsimp [j]
      omega
    rw [hj]
    apply
      (not_abs_taoGeom2CenteredListWeight_lt_iff_ndA5TubeRadius_lt
        hW (as.take k)).mp
    rw [taoGeom2CenteredListWeight_take_eq hlen hk]
    exact not_lt_of_ge hbad
  · intro hbad hgood
    rcases hbad with ⟨j, hjbad⟩
    have hj : j.1 + 1 ≤ r := by omega
    have hnot :=
      (not_abs_taoGeom2CenteredListWeight_lt_iff_ndA5TubeRadius_lt
        hW (as.take (j.1 + 1))).mpr hjbad
    apply hnot
    rw [taoGeom2CenteredListWeight_take_eq hlen hj]
    exact hgood.2 (j.1 + 1) hj

/-- The complement of the literal FullGood source event is exactly the
preimage of one positive-prefix Geom(2) bad event. -/
theorem ndA5FullPrefixGoodEvent_compl_eq_preimage_prefixBad
    {B : ℕ} {C : ℝ} (hW : 0 < ndA5TubeWidth B C) :
    (ndA5FullPrefixGoodEvent B C)ᶜ =
      (fun N : Tao.TaoOddNat =>
        Tao.syracuseValuationPNatList
          (Tao.taoSection5N0 B) N.1 N.2) ⁻¹'
        Tao.taoGeom2PrefixBadEvent
          (ndA5TubeRadius (ndA5TubeWidth B C) : ℝ)
          (Tao.taoSection5N0 B) := by
  ext N
  rw [Set.mem_compl_iff]
  change (¬ ndA5PrefixGood B C (Tao.taoSection5N0 B)
      (Tao.syracuseValuationPNatList
        (Tao.taoSection5N0 B) N.1 N.2)) ↔ _
  exact not_ndA5PrefixGood_iff_prefixBad
    (Tao.syracuseValuationPNatList_length _ _ _) hW

end

end ND
end Erdos1135
