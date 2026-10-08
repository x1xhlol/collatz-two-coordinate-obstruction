import Erdos1135.ND.Band.A5Regularity
import Erdos1135.ND.Discrepancy.LocalizedKoksma
import Erdos1135.ND.Discrepancy.PhaseToDbar

/-!
# A5 Equal Padding and Abel Factor

This endpoint-shaped leaf implements the frozen X.5 zero-padding seam at the
already checked exact-zero-head Abel consumer.  If the intrinsic tube has
cardinality `s`, the first `s` entries are zero and the next `s` entries are
the normalized tube weights in increasing order.  The phase anchor is shifted
inside the additive circle, so no natural subtraction can clip.
-/

open scoped BigOperators

namespace Erdos1135
namespace ND

noncomputable section

/-- The absolute Abel factor is at most the vector length times its
unweighted terminal-plus-increment variation. -/
theorem ndAbsAbelFactor_le_length_mul_variation
    (omega : ℕ → ℝ) (V : ℕ) :
    ndAbsAbelFactor omega V ≤
      (V : ℝ) *
        (|omega (V - 1)| +
          ∑ i ∈ Finset.range (V - 1),
            |omega i - omega (i + 1)|) := by
  unfold ndAbsAbelFactor
  calc
    |omega (V - 1)| * (V : ℝ) +
          ∑ i ∈ Finset.range (V - 1),
            |omega i - omega (i + 1)| * ((i + 1 : ℕ) : ℝ) =
        (V : ℝ) * |omega (V - 1)| +
          ∑ i ∈ Finset.range (V - 1),
            ((i + 1 : ℕ) : ℝ) * |omega i - omega (i + 1)| := by
      congr 1
      · ring
      · apply Finset.sum_congr rfl
        intro i hi
        ring
    _ ≤ (V : ℝ) * |omega (V - 1)| +
          ∑ i ∈ Finset.range (V - 1),
            (V : ℝ) * |omega i - omega (i + 1)| := by
      apply add_le_add le_rfl
      apply Finset.sum_le_sum
      intro i hi
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast (show i + 1 ≤ V by
          have hil := Finset.mem_range.mp hi
          omega)
      · exact abs_nonneg _
    _ = (V : ℝ) *
          (|omega (V - 1)| +
            ∑ i ∈ Finset.range (V - 1),
              |omega i - omega (i + 1)|) := by
      rw [mul_add, Finset.mul_sum]

private noncomputable def ndEqualLeftPad
    (u : ℕ → ℝ) (s m : ℕ) : ℝ :=
  if m < s then 0 else u (m - s)

/-- Exact terminal-plus-increment variation of an equal left pad.  The first
summand on the right is the exit jump, the second is the entry jump, and the
remaining sum consists of the internal edges. -/
private theorem ndEqualLeftPad_variation
    (u : ℕ → ℝ) (s : ℕ) (hs : 0 < s) :
    |ndEqualLeftPad u s (2 * s - 1)| +
        (∑ i ∈ Finset.range (2 * s - 1),
          |ndEqualLeftPad u s i - ndEqualLeftPad u s (i + 1)|) =
      |u (s - 1)| + |u 0| +
        ∑ k ∈ Finset.range (s - 1), |u k - u (k + 1)| := by
  have hlast : 2 * s - 1 = s + (s - 1) := by omega
  rw [hlast]
  have hterminal :
      ndEqualLeftPad u s (s + (s - 1)) = u (s - 1) := by
    simp [ndEqualLeftPad]
  rw [hterminal]
  rw [show s + (s - 1) = (s - 1) + s by omega]
  rw [Finset.sum_range_add]
  have hzero :
      (∑ i ∈ Finset.range (s - 1),
        |ndEqualLeftPad u s i - ndEqualLeftPad u s (i + 1)|) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    have hi' := Finset.mem_range.mp hi
    have his : i < s := by omega
    have hisucc : i + 1 < s := by omega
    simp [ndEqualLeftPad, his, hisucc]
  rw [hzero, zero_add]
  rw [show Finset.range s = Finset.range ((s - 1) + 1) by
    congr 1
    omega]
  rw [Finset.sum_range_succ']
  simp only [Nat.add_zero]
  have hentry :
      |ndEqualLeftPad u s (s - 1) -
          ndEqualLeftPad u s (s - 1 + 1)| = |u 0| := by
    have hpred : s - 1 < s := by omega
    have hsucc : s - 1 + 1 = s := by omega
    simp [ndEqualLeftPad, hpred, hsucc]
  rw [hentry]
  have hinternal :
      (∑ k ∈ Finset.range (s - 1),
        |ndEqualLeftPad u s (s - 1 + (k + 1)) -
          ndEqualLeftPad u s (s - 1 + (k + 1) + 1)|) =
      ∑ k ∈ Finset.range (s - 1), |u k - u (k + 1)| := by
    apply Finset.sum_congr rfl
    intro k hk
    have hk' := Finset.mem_range.mp hk
    have hleft : s - 1 + (k + 1) = s + k := by omega
    rw [hleft]
    have hnot : ¬ s + k + 1 < s := by omega
    have hsub : s + k + 1 - s = k + 1 := by omega
    simp [ndEqualLeftPad, hnot, hsub]
  rw [hinternal]
  ring

/-- Length of the equal-padded A5 vector: one full zero block followed by the
full intrinsic tube. -/
noncomputable def ndA5EqualPaddedLength (A W : ℝ) : ℕ :=
  2 * (ndA5FullTube A W).card

/-- Equal-padded normalized A5 weights.  Only indices below
`ndA5EqualPaddedLength` are consumed. -/
noncomputable def ndA5EqualPaddedOmega (A W : ℝ) (m : ℕ) : ℝ :=
  let s := (ndA5FullTube A W).card
  ndEqualLeftPad
    (fun k => ndA5NormalizedQ A W (ndA5TubeLo A W + k)) s m

/-- Anchor shift for the equal padding, performed in the additive circle
rather than by truncated natural subtraction. -/
noncomputable def ndA5EqualPaddedAnchor
    (phi : UnitAddCircle) (A W : ℝ) : UnitAddCircle :=
  let s := (ndA5FullTube A W).card
  phi + ndA5TubeLo A W • (logTwoThree : UnitAddCircle) -
    s • (logTwoThree : UnitAddCircle)

@[simp] theorem ndA5EqualPaddedOmega_of_lt_card
    {A W : ℝ} {m : ℕ} (hm : m < (ndA5FullTube A W).card) :
    ndA5EqualPaddedOmega A W m = 0 := by
  simp [ndA5EqualPaddedOmega, ndEqualLeftPad, hm]

@[simp] theorem ndA5EqualPaddedOmega_card_add
    (A W : ℝ) (k : ℕ) :
    ndA5EqualPaddedOmega A W ((ndA5FullTube A W).card + k) =
      ndA5NormalizedQ A W (ndA5TubeLo A W + k) := by
  simp [ndA5EqualPaddedOmega, ndEqualLeftPad]

theorem ndA5EqualPaddedOmega_nonneg (A W : ℝ) (m : ℕ) :
    0 ≤ ndA5EqualPaddedOmega A W m := by
  unfold ndA5EqualPaddedOmega ndEqualLeftPad
  dsimp only
  split_ifs
  · exact le_rfl
  · exact ndA5NormalizedQ_nonneg A W _

/-- Nonempty checked tubes give a genuinely positive equal-padding length. -/
theorem ndA5FullTube_card_pos_of_interior
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    (hTube : NDA5InteriorTubeFacts B j branch C M) :
    0 < (ndA5FullTube
      (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
      (ndA5TubeWidth B C)).card :=
  Finset.card_pos.mpr hTube.nonempty

/-- Equal padding leaves room for a nonempty supported block after its zero
head. -/
theorem ndA5FullTube_card_lt_equalPaddedLength
    {A W : ℝ} (hne : (ndA5FullTube A W).Nonempty) :
    (ndA5FullTube A W).card < ndA5EqualPaddedLength A W := by
  unfold ndA5EqualPaddedLength
  have hs := Finset.card_pos.mpr hne
  omega

/-- The circle anchor exactly compensates for the zero block. -/
theorem ndPhaseOrbit_ndA5EqualPaddedAnchor_card_add
    (phi : UnitAddCircle) (A W : ℝ) (k : ℕ) :
    ndPhaseOrbit (ndA5EqualPaddedAnchor phi A W)
        ((ndA5FullTube A W).card + k) =
      ndPhaseOrbit phi (ndA5TubeLo A W + k) := by
  unfold ndA5EqualPaddedAnchor ndPhaseOrbit
  dsimp only
  simp only [add_nsmul]
  abel

/-- Splitting at the equal zero block leaves the source weights in their
original order. -/
theorem sum_range_ndA5EqualPaddedOmega_mul
    (A W : ℝ) (f : ℕ → ℝ) :
    (∑ m ∈ Finset.range (ndA5EqualPaddedLength A W),
        ndA5EqualPaddedOmega A W m * f m) =
      ∑ k ∈ Finset.range (ndA5FullTube A W).card,
        ndA5NormalizedQ A W (ndA5TubeLo A W + k) *
          f ((ndA5FullTube A W).card + k) := by
  unfold ndA5EqualPaddedLength
  rw [two_mul, Finset.sum_range_add]
  have hzero :
      (∑ m ∈ Finset.range (ndA5FullTube A W).card,
        ndA5EqualPaddedOmega A W m * f m) = 0 := by
    apply Finset.sum_eq_zero
    intro m hm
    rw [ndA5EqualPaddedOmega_of_lt_card (Finset.mem_range.mp hm)]
    exact zero_mul _
  rw [hzero, zero_add]
  apply Finset.sum_congr rfl
  intro k hk
  rw [ndA5EqualPaddedOmega_card_add]

/-- The range presentation of the equal padding is exactly the intrinsic
tube sum, with no endpoint loss. -/
theorem sum_range_ndA5EqualPaddedOmega_mul_eq_fullTube
    {A W : ℝ} (hW : 0 < W) (hne : (ndA5FullTube A W).Nonempty)
    (f : ℕ → ℝ) :
    (∑ m ∈ Finset.range (ndA5EqualPaddedLength A W),
        ndA5EqualPaddedOmega A W m * f m) =
      ∑ nu ∈ ndA5FullTube A W,
        ndA5NormalizedQ A W nu *
          f (nu - ndA5TubeLo A W + (ndA5FullTube A W).card) := by
  let lo := ndA5TubeLo A W
  let hi := ndA5TubeHi A W
  let s := (ndA5FullTube A W).card
  have hEq : ndA5FullTube A W = Finset.Icc lo hi := by
    simpa [lo, hi] using ndA5FullTube_eq_Icc hW hne
  have hcard : s = hi + 1 - lo := by
    dsimp [s]
    rw [hEq, Nat.card_Icc]
  rw [sum_range_ndA5EqualPaddedOmega_mul]
  symm
  calc
    (∑ nu ∈ ndA5FullTube A W,
        ndA5NormalizedQ A W nu *
          f (nu - ndA5TubeLo A W + (ndA5FullTube A W).card)) =
        ∑ nu ∈ Finset.Icc lo hi,
          ndA5NormalizedQ A W nu * f (nu - lo + s) := by
      simp only [hEq, lo, s]
    _ = ∑ nu ∈ Finset.Ico lo (hi + 1),
          ndA5NormalizedQ A W nu * f (nu - lo + s) := by
      rw [Finset.Ico_add_one_right_eq_Icc]
    _ = ∑ k ∈ Finset.range (hi + 1 - lo),
          ndA5NormalizedQ A W (lo + k) *
            f ((lo + k) - lo + s) :=
      Finset.sum_Ico_eq_sum_range _ lo (hi + 1)
    _ = ∑ k ∈ Finset.range s,
          ndA5NormalizedQ A W (ndA5TubeLo A W + k) *
            f (s + k) := by
      rw [← hcard]
      apply Finset.sum_congr rfl
      intro k hk
      simp only [lo]
      congr 2
      omega

/-- Generic phase-profile reindex.  The circle-group anchor shift makes this
identity valid even when the natural inequality `card <= tubeLo` is absent. -/
theorem sum_ndA5EqualPaddedOmega_phase_reindex
    {A W : ℝ} (hW : 0 < W) (hne : (ndA5FullTube A W).Nonempty)
    (phi : UnitAddCircle) (gamma : UnitAddCircle → ℝ) :
    (∑ m ∈ Finset.range (ndA5EqualPaddedLength A W),
        ndA5EqualPaddedOmega A W m *
          gamma (ndPhaseOrbit (ndA5EqualPaddedAnchor phi A W) m)) =
      ∑ nu ∈ ndA5FullTube A W,
        ndA5NormalizedQ A W nu * gamma (ndPhaseOrbit phi nu) := by
  rw [sum_range_ndA5EqualPaddedOmega_mul_eq_fullTube hW hne]
  have hEq := ndA5FullTube_eq_Icc hW hne
  apply Finset.sum_congr rfl
  intro nu hnu
  have hbounds : ndA5TubeLo A W ≤ nu ∧ nu ≤ ndA5TubeHi A W := by
    exact Finset.mem_Icc.mp (by simpa [hEq] using hnu)
  have hphase :
      ndPhaseOrbit (ndA5EqualPaddedAnchor phi A W)
          (nu - ndA5TubeLo A W + (ndA5FullTube A W).card) =
        ndPhaseOrbit phi nu := by
    rw [show nu - ndA5TubeLo A W + (ndA5FullTube A W).card =
        (ndA5FullTube A W).card + (nu - ndA5TubeLo A W) by omega]
    rw [ndPhaseOrbit_ndA5EqualPaddedAnchor_card_add]
    congr 1
    omega
  rw [hphase]

/-- The equal-padded vector has a literal zero head of length equal to the
tube cardinality. -/
theorem ndA5EqualPaddedOmega_zero_head
    (A W : ℝ) {m : ℕ} (hm : m < (ndA5FullTube A W).card) :
    ndA5EqualPaddedOmega A W m = 0 :=
  ndA5EqualPaddedOmega_of_lt_card hm

/-- The checked exact-zero-head Abel theorem consumes the equal-padded A5
vector directly at the positive endpoint `P=card(tube)`. -/
theorem ndA5EqualPaddedOmega_zeroHeadAbel
    {A W : ℝ} (hne : (ndA5FullTube A W).Nonempty)
    (B : ℕ → ℝ) (D : ℕ → ℝ) (Q : ℝ)
    (hQ : 0 ≤ Q) (hD : ∀ m, 0 ≤ D m)
    (hanti : AntitoneOn D (Set.Ici 1))
    (hprefix : ∀ m, 0 < m → m ≤ ndA5EqualPaddedLength A W →
      |∑ n ∈ Finset.range m, B n| ≤ Q * (m : ℝ) * D m) :
    |∑ n ∈ Finset.range (ndA5EqualPaddedLength A W),
        ndA5EqualPaddedOmega A W n * B n| ≤
      Q * D (ndA5FullTube A W).card *
        ndAbsAbelFactor (ndA5EqualPaddedOmega A W)
          (ndA5EqualPaddedLength A W) := by
  apply ndZeroHeadAbel_of_antitonePrefix
  · exact Finset.card_pos.mpr hne
  · exact ndA5FullTube_card_lt_equalPaddedLength hne
  · exact hQ
  · exact hD
  · exact hanti
  · intro n hn
    exact ndA5EqualPaddedOmega_of_lt_card hn
  · exact hprefix

/-- X.4 normalization survives equal padding exactly on an analytic tube. -/
theorem sum_ndA5EqualPaddedOmega_eq_one_of_analytic
    {B : ℕ} {C A : ℝ} (hTube : NDA5AnalyticTubeFacts B C A) :
    (∑ m ∈ Finset.range
        (ndA5EqualPaddedLength A (ndA5TubeWidth B C)),
      ndA5EqualPaddedOmega A (ndA5TubeWidth B C) m) = 1 := by
  let W := ndA5TubeWidth B C
  have hW : 0 < W := by
    simpa [W] using hTube.width_pos
  have hreindex := sum_range_ndA5EqualPaddedOmega_mul_eq_fullTube
    (A := A) (W := W) hW (by simpa [W] using hTube.nonempty)
      (fun _ => (1 : ℝ))
  simp only [mul_one] at hreindex
  rw [hreindex]
  simpa [W] using sum_ndA5NormalizedQ_eq_one_of_analytic hTube

/-- Physical interior specialization of analytic equal-padding normalization. -/
theorem sum_ndA5EqualPaddedOmega_eq_one_of_interior
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    (hTube : NDA5InteriorTubeFacts B j branch C M) :
    (∑ m ∈ Finset.range (ndA5EqualPaddedLength
        (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
        (ndA5TubeWidth B C)),
      ndA5EqualPaddedOmega
        (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
        (ndA5TubeWidth B C) m) = 1 := by
  simpa using
    sum_ndA5EqualPaddedOmega_eq_one_of_analytic
      (NDA5InteriorTubeFacts.toAnalytic hTube)

/-- The unweighted finite Abel bracket of the equal-padded vector is exactly
the full zero-extension variation checked in X.4.  In particular, a
singleton tube contributes its unique weight twice. -/
theorem ndA5EqualPaddedVariation_eq
    {A W : ℝ} (hW : 0 < W) (hne : (ndA5FullTube A W).Nonempty) :
    |ndA5EqualPaddedOmega A W (ndA5EqualPaddedLength A W - 1)| +
        (∑ i ∈ Finset.range (ndA5EqualPaddedLength A W - 1),
          |ndA5EqualPaddedOmega A W i -
            ndA5EqualPaddedOmega A W (i + 1)|) =
      ndA5NormalizedQExtendedVariation A W := by
  let lo := ndA5TubeLo A W
  let hi := ndA5TubeHi A W
  let s := (ndA5FullTube A W).card
  let u : ℕ → ℝ := fun k => ndA5NormalizedQ A W (lo + k)
  have hEq : ndA5FullTube A W = Finset.Icc lo hi := by
    simpa [lo, hi] using ndA5FullTube_eq_Icc hW hne
  have hlohi : lo ≤ hi := by
    rw [← Finset.nonempty_Icc, ← hEq]
    exact hne
  have hs : 0 < s := by
    simpa [s] using Finset.card_pos.mpr hne
  have hcard : s = hi + 1 - lo := by
    dsimp [s]
    rw [hEq, Nat.card_Icc]
  have hlast : lo + (s - 1) = hi := by omega
  have hspan : s - 1 = hi - lo := by omega
  have hpad := ndEqualLeftPad_variation u s hs
  have hgeneric :
      |ndA5EqualPaddedOmega A W (ndA5EqualPaddedLength A W - 1)| +
          (∑ i ∈ Finset.range (ndA5EqualPaddedLength A W - 1),
            |ndA5EqualPaddedOmega A W i -
              ndA5EqualPaddedOmega A W (i + 1)|) =
        |u (s - 1)| + |u 0| +
          ∑ k ∈ Finset.range (s - 1), |u k - u (k + 1)| := by
    simpa [ndA5EqualPaddedLength, ndA5EqualPaddedOmega, s, u, lo] using hpad
  have hinternal :
      (∑ k ∈ Finset.range (s - 1), |u k - u (k + 1)|) =
        ∑ nu ∈ Finset.Ico lo hi,
          |ndA5NormalizedQ A W (nu + 1) -
            ndA5NormalizedQ A W nu| := by
    calc
      (∑ k ∈ Finset.range (s - 1), |u k - u (k + 1)|) =
          ∑ k ∈ Finset.range (hi - lo),
            |ndA5NormalizedQ A W (lo + k) -
              ndA5NormalizedQ A W ((lo + k) + 1)| := by
        rw [hspan]
        apply Finset.sum_congr rfl
        intro k hk
        simp only [u]
        rfl
      _ = ∑ nu ∈ Finset.Ico lo hi,
            |ndA5NormalizedQ A W nu -
              ndA5NormalizedQ A W (nu + 1)| :=
        (Finset.sum_Ico_eq_sum_range
          (fun nu => |ndA5NormalizedQ A W nu -
            ndA5NormalizedQ A W (nu + 1)|) lo hi).symm
      _ = ∑ nu ∈ Finset.Ico lo hi,
            |ndA5NormalizedQ A W (nu + 1) -
              ndA5NormalizedQ A W nu| := by
        apply Finset.sum_congr rfl
        intro nu hnu
        exact abs_sub_comm _ _
  rw [hgeneric]
  unfold ndA5NormalizedQExtendedVariation
  dsimp only
  change |u (s - 1)| + |u 0| +
      (∑ k ∈ Finset.range (s - 1), |u k - u (k + 1)|) =
    |ndA5NormalizedQ A W lo| +
      (∑ nu ∈ Finset.Ico lo hi,
        |ndA5NormalizedQ A W (nu + 1) -
          ndA5NormalizedQ A W nu|) +
      |ndA5NormalizedQ A W hi|
  rw [hinternal]
  simp only [u, Nat.add_zero, hlast]
  ring

/-- Exact finite X.6 bound for equal padding on an analytic tube.  It retains
the tube cardinality explicitly for the later rate adapter. -/
theorem ndAbsAbelFactor_ndA5EqualPaddedOmega_le_of_analytic
    {B : ℕ} {C A : ℝ} (hTube : NDA5AnalyticTubeFacts B C A) :
    ndAbsAbelFactor
        (ndA5EqualPaddedOmega A (ndA5TubeWidth B C))
        (ndA5EqualPaddedLength A (ndA5TubeWidth B C)) ≤
      64 *
        ((ndA5FullTube A (ndA5TubeWidth B C)).card : ℝ) *
        ndA5TubeWidth B C /
          (ndA5TubeLo A (ndA5TubeWidth B C) : ℝ) := by
  let W := ndA5TubeWidth B C
  let s := (ndA5FullTube A W).card
  have hW : 0 < W := by
    simpa [W] using hTube.width_pos
  have hne : (ndA5FullTube A W).Nonempty := by
    simpa [W] using hTube.nonempty
  have hfactor := ndAbsAbelFactor_le_length_mul_variation
    (ndA5EqualPaddedOmega A W) (ndA5EqualPaddedLength A W)
  rw [ndA5EqualPaddedVariation_eq hW hne] at hfactor
  have hvariation :=
    ndA5NormalizedQExtendedVariation_le_thirty_two_mul_width_div_lo_of_analytic
      hTube
  calc
    ndAbsAbelFactor (ndA5EqualPaddedOmega A W)
        (ndA5EqualPaddedLength A W) ≤
        (ndA5EqualPaddedLength A W : ℝ) *
          ndA5NormalizedQExtendedVariation A W := hfactor
    _ ≤ (2 * s : ℕ) * (32 * W / (ndA5TubeLo A W : ℝ)) := by
      apply mul_le_mul_of_nonneg_left
      · simpa [W] using hvariation
      · positivity
    _ = 64 * (s : ℝ) * W / (ndA5TubeLo A W : ℝ) := by
      push_cast
      ring

/-- Physical interior specialization of the analytic equal-padding Abel bound. -/
theorem ndAbsAbelFactor_ndA5EqualPaddedOmega_le_of_interior
    {B j : ℕ} {branch : Tao.TaoSection5SourceBranch} {C M : ℝ}
    (hTube : NDA5InteriorTubeFacts B j branch C M) :
    ndAbsAbelFactor
        (ndA5EqualPaddedOmega
          (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
          (ndA5TubeWidth B C))
        (ndA5EqualPaddedLength
          (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
          (ndA5TubeWidth B C)) ≤
      64 *
        ((ndA5FullTube
          (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
          (ndA5TubeWidth B C)).card : ℝ) *
        ndA5TubeWidth B C /
          (ndA5TubeLo
            (ndA5PhysicalPhase (ndA5BandLower B branch j) M)
            (ndA5TubeWidth B C) : ℝ) := by
  simpa using
    ndAbsAbelFactor_ndA5EqualPaddedOmega_le_of_analytic
      (NDA5InteriorTubeFacts.toAnalytic hTube)

end

end ND
end Erdos1135
