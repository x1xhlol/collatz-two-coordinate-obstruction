import Erdos1135.Tao.Renewal.Lemma77PotentialCore
import Erdos1135.Tao.Renewal.Lemma77HorizontalMarginal

/-!
# Lemma 7.7 Local-Limit Vocabulary

This module starts the checked layer below the Lemma 7.7 pointwise endpoint
socket.  It names finite iid `Hold` prefix endpoint events and a local-limit
input surface over those events.

It does not prove Lemma 7.7, Lemma 7.6, Lemma 2.2, the pointwise endpoint law,
or the vertical summation into `exactKernelTailSummand`.
-/

namespace Erdos1135
namespace Tao

open scoped BigOperators

noncomputable section

namespace TaoSection7Lemma77

/-- Dimension-two local-limit prefactor at prefix length `n`. -/
def lemma77LocalLimitPrefactor (n : ℕ) : ℝ :=
  ((n + 1 : ℕ) : ℝ) ^ (-(1 : ℝ))

/-- For positive prefix length, Tao's `(n + 1)^-1` prefactor is at most `n^-1`. -/
theorem lemma77LocalLimitPrefactor_le_inv_of_pos
    {n : ℕ} (hn : 0 < n) :
    lemma77LocalLimitPrefactor n ≤ ((n : ℝ)⁻¹) := by
  unfold lemma77LocalLimitPrefactor
  rw [Real.rpow_neg_one]
  have hn_pos : 0 < (n : ℝ) := by
    exact_mod_cast hn
  have hnp1_pos : 0 < (((n + 1 : ℕ) : ℝ)) := by
    positivity
  have hle : (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_succ n
  exact (inv_le_inv₀ hnp1_pos hn_pos).mpr hle

/-- For positive prefix length, the local-limit prefactor is at most one. -/
theorem lemma77LocalLimitPrefactor_le_one_of_pos
    {n : ℕ} (hn : 0 < n) :
    lemma77LocalLimitPrefactor n ≤ 1 := by
  have hpref := lemma77LocalLimitPrefactor_le_inv_of_pos hn
  have hnR : 0 < (n : ℝ) := by
    exact_mod_cast hn
  have hn_ge_one : (1 : ℝ) ≤ n := by
    exact_mod_cast hn
  have hinv_le_one : ((n : ℝ)⁻¹) ≤ 1 := by
    field_simp [hnR.ne']
    exact hn_ge_one
  exact le_trans hpref hinv_le_one

/-- Radial two-dimensional wrapper around Tao's `G_n` weight. -/
def taoLemma22GaussianWeight2 (n : ℕ) (x y : ℝ) : ℝ :=
  taoLemma22GaussianWeight n (Real.sqrt (x ^ 2 + y ^ 2))

@[simp]
theorem taoLemma22GaussianWeight2_zero (x y : ℝ) :
    taoLemma22GaussianWeight2 0 x y =
      Real.exp (-Real.sqrt (x ^ 2 + y ^ 2)) := by
  unfold taoLemma22GaussianWeight2 taoLemma22GaussianWeight
  simp [abs_of_nonneg (Real.sqrt_nonneg (x ^ 2 + y ^ 2))]


/--
Endpoint event for an iid `Hold` prefix of length `n`, expressed as a
two-dimensional relative endpoint fiber from a fixed start point.
-/
def lemma77HoldPrefixEndpointEvent
    (start : TaoSection7RenewalPoint) (n r : ℕ) (ell : ℤ) :
    Set (List TaoSection7RenewalPoint) :=
  {hs |
    lemma77HoldPrefixIncrement start n hs = r ∧
      lemma77HoldPrefixVerticalIncrement start n hs = ell}

/-- The iid `Hold` prefix endpoint event is the fixed-start relative endpoint fiber. -/
theorem lemma77HoldPrefixEndpointEvent_eq_relativeEndpointFiberEvent
    (start : TaoSection7RenewalPoint) (n r : ℕ) (ell : ℤ) :
    lemma77HoldPrefixEndpointEvent start n r ell =
      relativeEndpointFiberEvent
        (fun _ : List TaoSection7RenewalPoint => start)
        (fun _ => n)
        (fun hs => hs)
        r ell := by
  rfl

/-- Membership in the `Hold` prefix endpoint event unfolds to the two relative increments. -/
theorem mem_lemma77HoldPrefixEndpointEvent_iff
    {start : TaoSection7RenewalPoint} {n r : ℕ} {ell : ℤ}
    {hs : List TaoSection7RenewalPoint} :
    hs ∈ lemma77HoldPrefixEndpointEvent start n r ell ↔
      lemma77HoldPrefixIncrement start n hs = r ∧
        lemma77HoldPrefixVerticalIncrement start n hs = ell := by
  rfl

/-- The natural endpoint event is the signed endpoint event at `j = r`. -/
theorem lemma77HoldPrefixEndpointEvent_eq_signedEndpointEvent
    (start : TaoSection7RenewalPoint) (n r : ℕ) (ell : ℤ) :
    lemma77HoldPrefixEndpointEvent start n r ell =
      lemma77HoldPrefixSignedEndpointEvent start n (r : ℤ) ell := by
  ext hs
  constructor
  · intro h
    exact ⟨by exact_mod_cast h.1, h.2⟩
  · intro h
    exact ⟨by exact_mod_cast h.1, h.2⟩

/--
Mass of a `Hold` prefix endpoint event under the iid `Hold` list law.

The sample space `List TaoSection7RenewalPoint` is not finite, so this uses
`PMF.toOuterMeasure` rather than the finite `pmfProb` helper.
-/
def lemma77HoldPrefixEndpointMass
    (start : TaoSection7RenewalPoint) (n r : ℕ) (ell : ℤ) : ℝ :=
  ((taoSection7HoldListPMF n).toOuterMeasure
      (lemma77HoldPrefixEndpointEvent start n r ell)).toReal

/-- Point-mass summand for a signed iid `Hold` prefix endpoint fiber. -/
def lemma77HoldPrefixSignedEndpointMassSummand
    (start : TaoSection7RenewalPoint) (n : ℕ) (j ell : ℤ)
    (hs : List TaoSection7RenewalPoint) : ℝ := by
  classical
  exact
    if hs ∈ lemma77HoldPrefixSignedEndpointEvent start n j ell then
      (taoSection7HoldListPMF n hs).toReal
    else
      0

/--
The signed endpoint summand is supported on lists of length `n`.

This is a pointwise support guard for the later outer-measure/`tsum`
atomization bridge; it is not the atomization bridge itself.
-/
theorem lemma77HoldPrefixSignedEndpointMassSummand_eq_zero_of_length_ne
    {start : TaoSection7RenewalPoint} {n : ℕ} {j ell : ℤ}
    {hs : List TaoSection7RenewalPoint}
    (h : hs.length ≠ n) :
    lemma77HoldPrefixSignedEndpointMassSummand start n j ell hs = 0 := by
  classical
  by_cases hmem :
      hs ∈ lemma77HoldPrefixSignedEndpointEvent start n j ell
  · rw [lemma77HoldPrefixSignedEndpointMassSummand, ite_eq_left hmem]
    exact lemma77HoldListPMF_toReal_eq_zero_of_length_ne h
  · rw [lemma77HoldPrefixSignedEndpointMassSummand, ite_eq_right hmem]

/--
Atomization of signed iid `Hold` endpoint mass as a real `tsum` over all list
atoms with the endpoint-fiber summand.
-/
theorem lemma77HoldPrefixSignedEndpointMass_eq_tsum_summand
    (start : TaoSection7RenewalPoint) (n : ℕ) (j ell : ℤ) :
    lemma77HoldPrefixSignedEndpointMass start n j ell =
      ∑' hs : List TaoSection7RenewalPoint,
        lemma77HoldPrefixSignedEndpointMassSummand start n j ell hs := by
  classical
  rw [lemma77HoldPrefixSignedEndpointMass,
    pmf_toOuterMeasure_toReal_eq_tsum_indicator]
  apply tsum_congr
  intro hs
  by_cases hmem :
      hs ∈ lemma77HoldPrefixSignedEndpointEvent start n j ell
  · rw [lemma77HoldPrefixSignedEndpointMassSummand, ite_eq_left hmem]
    simp [Set.indicator, hmem]
  · rw [lemma77HoldPrefixSignedEndpointMassSummand, ite_eq_right hmem]
    simp [Set.indicator, hmem]

/--
Atomization of signed iid `Hold` endpoint mass as a real `tsum` over the
endpoint fiber subtype.
-/
theorem lemma77HoldPrefixSignedEndpointMass_eq_tsum_fiber
    (start : TaoSection7RenewalPoint) (n : ℕ) (j ell : ℤ) :
    lemma77HoldPrefixSignedEndpointMass start n j ell =
      ∑' hs : {hs : List TaoSection7RenewalPoint //
          hs ∈ lemma77HoldPrefixSignedEndpointEvent start n j ell},
        (taoSection7HoldListPMF n hs.1).toReal := by
  classical
  rw [lemma77HoldPrefixSignedEndpointMass,
    pmf_toOuterMeasure_toReal_eq_tsum_indicator]
  exact (tsum_subtype
    (lemma77HoldPrefixSignedEndpointEvent start n j ell)
    (fun hs : List TaoSection7RenewalPoint =>
      (taoSection7HoldListPMF n hs).toReal)).symm

/-- Natural endpoint mass is signed endpoint mass at `j = r`. -/
theorem lemma77HoldPrefixEndpointMass_eq_signedEndpointMass
    (start : TaoSection7RenewalPoint) (n r : ℕ) (ell : ℤ) :
    lemma77HoldPrefixEndpointMass start n r ell =
      lemma77HoldPrefixSignedEndpointMass start n (r : ℤ) ell := by
  rw [lemma77HoldPrefixEndpointMass, lemma77HoldPrefixSignedEndpointMass,
    lemma77HoldPrefixEndpointEvent_eq_signedEndpointEvent]

/-- Horizontal displacement from the mean `4n` of the iid `Hold` prefix. -/
def lemma77HoldMeanHorizontalDisplacement (n : ℕ) (j : ℤ) : ℝ :=
  (j : ℝ) - 4 * (n : ℝ)

/-- Vertical displacement from the mean `16n` of the iid `Hold` prefix. -/
def lemma77HoldMeanVerticalDisplacement (n : ℕ) (ell : ℤ) : ℝ :=
  (ell : ℝ) - 16 * (n : ℝ)

/-- Time offset from the central scalar summation regime `16n = s'`. -/
def lemma77ScalarTimeOffset (n s' : ℕ) : ℝ :=
  16 * (n : ℝ) - (s' : ℝ)

/-- Integer-index form of the scalar time offset. -/
theorem lemma77ScalarTimeOffset_eq_intIndex (n s' : ℕ) :
    lemma77ScalarTimeOffset n s' =
      ((16 * (n : ℤ) - (s' : ℤ) : ℤ) : ℝ) := by
  unfold lemma77ScalarTimeOffset
  norm_num

/-- The scalar time-offset lattice embeds injectively into `ℤ`. -/
theorem lemma77ScalarTimeOffset_intIndex_injective (s' : ℕ) :
    Function.Injective (fun n : ℕ => (16 * (n : ℤ) - (s' : ℤ) : ℤ)) := by
  intro m n h
  have hadd := congrArg (fun z : ℤ => z + (s' : ℤ)) h
  have hmul : 16 * (m : ℤ) = 16 * (n : ℤ) := by
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using hadd
  have hmneq : (m : ℤ) = (n : ℤ) := by
    nlinarith
  exact_mod_cast hmneq

/--
Left-of-center quotient distance is bounded by the scalar time offset.

This is the first lattice-spacing helper for the main shifted linear count.
-/
theorem lemma77ScalarTimeOffset_abs_ge_leftQuotDistance
    {n s' : ℕ} (hn : n ≤ s' / 16) :
    (((s' / 16) - n : ℕ) : ℝ) ≤
      |lemma77ScalarTimeOffset n s'| := by
  let q := s' / 16
  let r := s' % 16
  have hdivmod_nat : 16 * q + r = s' := by
    dsimp [q, r]
    exact Nat.div_add_mod s' 16
  have hdivmod : (s' : ℝ) = 16 * (q : ℝ) + (r : ℝ) := by
    have hcast : ((16 * q + r : ℕ) : ℝ) = (s' : ℝ) := by
      exact_mod_cast hdivmod_nat
    norm_num at hcast
    linarith
  have hq : (q : ℝ) = (n : ℝ) + (((q - n : ℕ) : ℝ)) := by
    have hnat : n + (q - n) = q := Nat.add_sub_of_le hn
    have hcast : (((n + (q - n) : ℕ) : ℝ)) = (q : ℝ) := by
      exact_mod_cast hnat
    norm_num at hcast
    linarith
  have hoff : lemma77ScalarTimeOffset n s' =
      -(16 * (((q - n : ℕ) : ℝ)) + (r : ℝ)) := by
    unfold lemma77ScalarTimeOffset
    nlinarith
  have hnonneg : 0 ≤ 16 * (((q - n : ℕ) : ℝ)) + (r : ℝ) := by
    positivity
  rw [hoff, abs_neg, abs_of_nonneg hnonneg]
  nlinarith [show 0 ≤ (((q - n : ℕ) : ℝ)) by positivity]

/--
Right-of-center quotient distance is bounded by the scalar time offset.

This is the second lattice-spacing helper for the main shifted linear count.
-/
theorem lemma77ScalarTimeOffset_abs_ge_rightQuotDistance
    {n s' : ℕ} (hn : s' / 16 < n) :
    ((n - (s' / 16 + 1 : ℕ) : ℕ) : ℝ) ≤
      |lemma77ScalarTimeOffset n s'| := by
  let q := s' / 16
  let r := s' % 16
  have hdivmod_nat : 16 * q + r = s' := by
    dsimp [q, r]
    exact Nat.div_add_mod s' 16
  have hdivmod : (s' : ℝ) = 16 * (q : ℝ) + (r : ℝ) := by
    have hcast : ((16 * q + r : ℕ) : ℝ) = (s' : ℝ) := by
      exact_mod_cast hdivmod_nat
    norm_num at hcast
    linarith
  have hq1_le : q + 1 ≤ n := by
    omega
  have hn_eq :
      (n : ℝ) = (q : ℝ) + 1 + (((n - (q + 1) : ℕ) : ℝ)) := by
    have hnat : (q + 1) + (n - (q + 1)) = n :=
      Nat.add_sub_of_le hq1_le
    have hcast : ((((q + 1) + (n - (q + 1)) : ℕ) : ℝ)) =
        (n : ℝ) := by
      exact_mod_cast hnat
    norm_num at hcast
    linarith
  have hr_lt : (r : ℝ) < 16 := by
    have hnat : r < 16 := by
      dsimp [r]
      exact Nat.mod_lt s' (by norm_num)
    exact_mod_cast hnat
  have hoff : lemma77ScalarTimeOffset n s' =
      16 + 16 * (((n - (q + 1) : ℕ) : ℝ)) - (r : ℝ) := by
    unfold lemma77ScalarTimeOffset
    nlinarith
  have hnonneg : 0 ≤
      16 + 16 * (((n - (q + 1) : ℕ) : ℝ)) - (r : ℝ) := by
    have hd_nonneg : 0 ≤ (((n - (q + 1) : ℕ) : ℝ)) := by
      positivity
    nlinarith
  rw [hoff, abs_of_nonneg hnonneg]
  nlinarith [show 0 ≤ (((n - (q + 1) : ℕ) : ℝ)) by positivity]

/--
The horizontal local-limit displacement in centered scalar coordinates.

This records the deterministic algebra behind Tao's post-`(7.33)` summation:
the prefix horizontal mean is shifted by one quarter of the vertical time
offset.
-/
theorem lemma77HoldMeanHorizontalDisplacement_eq_scalarCentered_sub_timeOffset
    (n : ℕ) (j : ℤ) (s' : ℕ) :
    lemma77HoldMeanHorizontalDisplacement n j =
      lemma77ScalarCenteredHorizontal j s' -
        lemma77ScalarTimeOffset n s' / 4 := by
  unfold lemma77HoldMeanHorizontalDisplacement
    lemma77ScalarCenteredHorizontal lemma77ScalarTimeOffset
  ring

/-- The vertical local-limit displacement is the negative scalar time offset. -/
theorem lemma77HoldMeanVerticalDisplacement_eq_neg_scalarTimeOffset
    (n s' : ℕ) :
    lemma77HoldMeanVerticalDisplacement n (s' : ℤ) =
      -lemma77ScalarTimeOffset n s' := by
  unfold lemma77HoldMeanVerticalDisplacement lemma77ScalarTimeOffset
  norm_num

/--
Two-dimensional local-limit kernel vocabulary for iid `Hold` prefix endpoints.

This is deliberately below the first-passage endpoint socket: it is a raw
finite-prefix kernel, before the height-potential/first-passage summation that
would produce the pointwise endpoint law.
-/
def lemma77HoldPrefixLocalLimitKernel
    (C c : ℝ) (n : ℕ) (j ell : ℤ) : ℝ :=
  C * lemma77LocalLimitPrefactor n *
    taoLemma22GaussianWeight2 n
      (c * lemma77HoldMeanHorizontalDisplacement n j)
      (c * lemma77HoldMeanVerticalDisplacement n ell)

/-- Scalar-indexed alias for the local-limit kernel term at target height `s'`. -/
def lemma77ScalarKernelTerm (C c : ℝ) (j : ℤ) (s' n : ℕ) : ℝ :=
  lemma77HoldPrefixLocalLimitKernel C c n j (s' : ℤ)

/-- Local-limit kernel at height `s'`, rewritten in scalar centered coordinates. -/
theorem lemma77HoldPrefixLocalLimitKernel_eq_scalarOffsets
    (C c : ℝ) (n : ℕ) (j : ℤ) (s' : ℕ) :
    lemma77HoldPrefixLocalLimitKernel C c n j (s' : ℤ) =
      C * lemma77LocalLimitPrefactor n *
        taoLemma22GaussianWeight2 n
          (c * (lemma77ScalarCenteredHorizontal j s' -
            lemma77ScalarTimeOffset n s' / 4))
          (c * (-lemma77ScalarTimeOffset n s')) := by
  rw [lemma77HoldPrefixLocalLimitKernel,
    lemma77HoldMeanHorizontalDisplacement_eq_scalarCentered_sub_timeOffset,
    lemma77HoldMeanVerticalDisplacement_eq_neg_scalarTimeOffset]

/-- Main scalar summation region: `16n` is comparable to `s'`. -/
def lemma77ScalarMainRegion (n s' : ℕ) : Prop :=
  s' ≤ 32 * n ∧ 16 * n ≤ 2 * s'

/-- Low scalar summation region: `16n` is below `s' / 2`. -/
def lemma77ScalarLowRegion (n s' : ℕ) : Prop :=
  32 * n < s'

/-- High scalar summation region: `16n` is above `2s'`. -/
def lemma77ScalarHighRegion (n s' : ℕ) : Prop :=
  2 * s' < 16 * n

/-- The main scalar region is decidable by Nat arithmetic. -/
instance lemma77ScalarMainRegionDecidable (n s' : ℕ) :
    Decidable (lemma77ScalarMainRegion n s') := by
  unfold lemma77ScalarMainRegion
  infer_instance

/-- The low scalar region is decidable by Nat arithmetic. -/
instance lemma77ScalarLowRegionDecidable (n s' : ℕ) :
    Decidable (lemma77ScalarLowRegion n s') := by
  unfold lemma77ScalarLowRegion
  infer_instance

/-- The high scalar region is decidable by Nat arithmetic. -/
instance lemma77ScalarHighRegionDecidable (n s' : ℕ) :
    Decidable (lemma77ScalarHighRegion n s') := by
  unfold lemma77ScalarHighRegion
  infer_instance

/-- Tao's three scalar summation regions cover every prefix length. -/
theorem lemma77ScalarRegion_trichotomy (n s' : ℕ) :
    lemma77ScalarLowRegion n s' ∨
      lemma77ScalarMainRegion n s' ∨
        lemma77ScalarHighRegion n s' := by
  by_cases hlow : lemma77ScalarLowRegion n s'
  · exact Or.inl hlow
  · by_cases hhigh : lemma77ScalarHighRegion n s'
    · exact Or.inr (Or.inr hhigh)
    · right
      left
      unfold lemma77ScalarLowRegion lemma77ScalarMainRegion
        lemma77ScalarHighRegion at *
      omega

/-- If neither outer scalar region holds, the prefix length is in the main region. -/
theorem lemma77ScalarMainRegion_of_not_low_not_high
    {n s' : ℕ}
    (hlow : ¬ lemma77ScalarLowRegion n s')
    (hhigh : ¬ lemma77ScalarHighRegion n s') :
    lemma77ScalarMainRegion n s' := by
  unfold lemma77ScalarLowRegion lemma77ScalarMainRegion
    lemma77ScalarHighRegion at *
  omega

/-- The low scalar region is disjoint from the main scalar region. -/
theorem lemma77ScalarLowRegion_not_main
    {n s' : ℕ}
    (hlow : lemma77ScalarLowRegion n s') :
    ¬ lemma77ScalarMainRegion n s' := by
  intro hmain
  unfold lemma77ScalarLowRegion lemma77ScalarMainRegion at *
  omega

/-- The high scalar region is disjoint from the main scalar region. -/
theorem lemma77ScalarHighRegion_not_main
    {n s' : ℕ}
    (hhigh : lemma77ScalarHighRegion n s') :
    ¬ lemma77ScalarMainRegion n s' := by
  intro hmain
  unfold lemma77ScalarHighRegion lemma77ScalarMainRegion at *
  omega

/-- The low scalar region is disjoint from the high scalar region. -/
theorem lemma77ScalarLowRegion_not_high
    {n s' : ℕ}
    (hlow : lemma77ScalarLowRegion n s') :
    ¬ lemma77ScalarHighRegion n s' := by
  intro hhigh
  unfold lemma77ScalarLowRegion lemma77ScalarHighRegion at *
  omega

/-- At target height zero, the main scalar region only contains `n = 0`. -/
theorem lemma77ScalarMainRegion_szero_iff (n : ℕ) :
    lemma77ScalarMainRegion n 0 ↔ n = 0 := by
  constructor
  · intro h
    unfold lemma77ScalarMainRegion at h
    omega
  · intro h
    subst h
    unfold lemma77ScalarMainRegion
    omega

/-- At prefix length zero, the main scalar region only contains `s' = 0`. -/
theorem lemma77ScalarMainRegion_nzero_iff (s' : ℕ) :
    lemma77ScalarMainRegion 0 s' ↔ s' = 0 := by
  constructor
  · intro h
    unfold lemma77ScalarMainRegion at h
    omega
  · intro h
    subst h
    unfold lemma77ScalarMainRegion
    omega

/-- In the main scalar region, positive target height forces positive prefix length. -/
theorem lemma77ScalarMainRegion_pos_of_spos
    {n s' : ℕ}
    (hs : 0 < s') (hmain : lemma77ScalarMainRegion n s') :
    0 < n := by
  unfold lemma77ScalarMainRegion at hmain
  omega

/-- In the main scalar region, the prefix length is at most the target height. -/
theorem lemma77ScalarMainRegion_le_height
    {n s' : ℕ}
    (hmain : lemma77ScalarMainRegion n s') :
    n ≤ s' := by
  unfold lemma77ScalarMainRegion at hmain
  omega

/-- The main scalar region has finite prefix support below `s' + 1`. -/
theorem lemma77ScalarMainRegion_lt_succ
    {n s' : ℕ}
    (hmain : lemma77ScalarMainRegion n s') :
    n < s' + 1 := by
  unfold lemma77ScalarMainRegion at hmain
  omega

/-- Prefix lengths at or beyond `s' + 1` are outside the main scalar region. -/
theorem lemma77ScalarMainRegion_not_of_succ_height_le
    {n s' : ℕ}
    (h : s' + 1 ≤ n) :
    ¬ lemma77ScalarMainRegion n s' := by
  intro hmain
  have hlt : n < s' + 1 := lemma77ScalarMainRegion_lt_succ hmain
  omega

/-- Any main-region-filtered scalar sequence is summable by finite support. -/
theorem lemma77ScalarMainRegion_filtered_summable_of_finite_support
    (g : ℕ → ℝ) (s' : ℕ) :
    Summable fun n : ℕ =>
      if lemma77ScalarMainRegion n s' then g n else 0 := by
  let f : ℕ → ℝ := fun n =>
    if lemma77ScalarMainRegion n s' then g n else 0
  have hsupport : Function.support f ⊆ Set.Iio (s' + 1) := by
    intro n hn
    by_contra hlt
    have hge : s' + 1 ≤ n := Nat.le_of_not_gt hlt
    have hzero : f n = 0 := by
      dsimp [f]
      have hnot := lemma77ScalarMainRegion_not_of_succ_height_le hge
      simp [hnot]
    exact hn hzero
  have hfinite : Function.HasFiniteSupport f :=
    Set.Finite.subset (Set.finite_Iio (s' + 1)) hsupport
  simpa [f] using (summable_of_hasFiniteSupport hfinite : Summable f)

/-- The filtered main-region kernel is summable by finite support. -/
theorem lemma77ScalarMainRegion_filteredKernel_summable_of_finite_support
    (C c : ℝ) (j : ℤ) (s' : ℕ) :
    Summable fun n : ℕ =>
      if lemma77ScalarMainRegion n s' then
        lemma77HoldPrefixLocalLimitKernel C c n j (s' : ℤ)
      else 0 :=
  lemma77ScalarMainRegion_filtered_summable_of_finite_support
    (fun n : ℕ => lemma77HoldPrefixLocalLimitKernel C c n j (s' : ℤ)) s'

/-- Main-region height is bounded by an absolute multiple of `n + 1`. -/
theorem lemma77ScalarMainRegion_succ_le_thirtythree_mul_succ
    {n s' : ℕ}
    (hmain : lemma77ScalarMainRegion n s') :
    s' + 1 ≤ 33 * (n + 1) := by
  unfold lemma77ScalarMainRegion at hmain
  omega

/-- Real-cast version of the main-region height bound. -/
theorem lemma77ScalarMainRegion_one_add_le_thirtythree_mul_succ_real
    {n s' : ℕ}
    (hmain : lemma77ScalarMainRegion n s') :
    (1 + (s' : ℝ)) ≤ 33 * ((n + 1 : ℕ) : ℝ) := by
  have hnat : s' + 1 ≤ 33 * (n + 1) :=
    lemma77ScalarMainRegion_succ_le_thirtythree_mul_succ hmain
  have hreal : ((s' + 1 : ℕ) : ℝ) ≤
      33 * (((n + 1 : ℕ) : ℝ)) := by
    exact_mod_cast hnat
  norm_num at hreal ⊢
  linarith

/-- Alias for the main-region real height comparability socket. -/
theorem lemma77ScalarMainRegion_one_add_le_thirtythree_mul
    {n s' : ℕ}
    (hmain : lemma77ScalarMainRegion n s') :
    (1 + (s' : ℝ)) ≤ 33 * ((n + 1 : ℕ) : ℝ) :=
  lemma77ScalarMainRegion_one_add_le_thirtythree_mul_succ_real hmain

/--
In the main scalar region, the local-limit prefactor is controlled by the
target height with one absolute constant.
-/
theorem lemma77ScalarMainRegion_prefactor_le_thirtythree_inv_height
    {n s' : ℕ}
    (hmain : lemma77ScalarMainRegion n s') :
    lemma77LocalLimitPrefactor n ≤
      33 * ((1 + (s' : ℝ))⁻¹) := by
  have hS : 0 < 1 + (s' : ℝ) := by
    positivity
  have hN : 0 < (((n + 1 : ℕ) : ℝ)) := by
    positivity
  have hle : (1 + (s' : ℝ)) ≤ 33 * (((n + 1 : ℕ) : ℝ)) :=
    lemma77ScalarMainRegion_one_add_le_thirtythree_mul_succ_real hmain
  unfold lemma77LocalLimitPrefactor
  rw [Real.rpow_neg_one]
  field_simp [hS.ne', hN.ne']
  nlinarith

/-- Alias for the main-region prefactor socket. -/
theorem lemma77ScalarMainRegion_prefactor_le_thirtythree_inv
    {n s' : ℕ}
    (hmain : lemma77ScalarMainRegion n s') :
    lemma77LocalLimitPrefactor n ≤
      33 * ((1 + (s' : ℝ))⁻¹) :=
  lemma77ScalarMainRegion_prefactor_le_thirtythree_inv_height hmain

/-- The low scalar region has positive target height. -/
theorem lemma77ScalarLowRegion_spos
    {n s' : ℕ}
    (hlow : lemma77ScalarLowRegion n s') :
    0 < s' := by
  unfold lemma77ScalarLowRegion at hlow
  omega

/-- In the low scalar region, the scalar time offset is negative. -/
theorem lemma77ScalarTimeOffset_neg_of_lowRegion
    {n s' : ℕ}
    (hlow : lemma77ScalarLowRegion n s') :
    lemma77ScalarTimeOffset n s' < 0 := by
  unfold lemma77ScalarLowRegion at hlow
  have hnat : 16 * n < s' := by
    omega
  have hreal : 16 * (n : ℝ) < (s' : ℝ) := by
    exact_mod_cast hnat
  unfold lemma77ScalarTimeOffset
  nlinarith

/-- Alias for the low-region negative time-offset socket. -/
theorem lemma77ScalarLowRegion_timeOffset_neg
    {n s' : ℕ}
    (hlow : lemma77ScalarLowRegion n s') :
    lemma77ScalarTimeOffset n s' < 0 :=
  lemma77ScalarTimeOffset_neg_of_lowRegion hlow

/-- In the low scalar region, the negative time offset is positive. -/
theorem lemma77ScalarLowRegion_neg_timeOffset_pos
    {n s' : ℕ}
    (hlow : lemma77ScalarLowRegion n s') :
    0 < -lemma77ScalarTimeOffset n s' := by
  have h := lemma77ScalarTimeOffset_neg_of_lowRegion hlow
  linarith

/--
Low-region height is controlled by twice the positive gap
`s' - 16n = -timeOffset`.
-/
theorem lemma77ScalarLowRegion_one_add_le_two_mul_neg_timeOffset
    {n s' : ℕ}
    (hlow : lemma77ScalarLowRegion n s') :
    (1 + (s' : ℝ)) ≤ 2 * (-lemma77ScalarTimeOffset n s') := by
  unfold lemma77ScalarLowRegion at hlow
  have hnat : 32 * n + 1 ≤ s' := by
    omega
  have hreal : 32 * (n : ℝ) + 1 ≤ (s' : ℝ) := by
    exact_mod_cast hnat
  unfold lemma77ScalarTimeOffset
  nlinarith

/-- Alias for the low-region height-gap socket. -/
theorem lemma77ScalarLowRegion_one_add_le_two_neg_timeOffset
    {n s' : ℕ}
    (hlow : lemma77ScalarLowRegion n s') :
    (1 + (s' : ℝ)) ≤ 2 * (-lemma77ScalarTimeOffset n s') :=
  lemma77ScalarLowRegion_one_add_le_two_mul_neg_timeOffset hlow

/-- The low scalar region has finite prefix support below `s' + 1`. -/
theorem lemma77ScalarLowRegion_lt_succ_height
    {n s' : ℕ}
    (hlow : lemma77ScalarLowRegion n s') :
    n < s' + 1 := by
  unfold lemma77ScalarLowRegion at hlow
  omega

/-- Prefix lengths at or beyond `s' + 1` are outside the low scalar region. -/
theorem lemma77ScalarLowRegion_not_of_succ_height_le
    {n s' : ℕ}
    (h : s' + 1 ≤ n) :
    ¬ lemma77ScalarLowRegion n s' := by
  intro hlow
  unfold lemma77ScalarLowRegion at hlow
  omega

/-- The filtered low-region kernel vanishes outside its finite support. -/
theorem lemma77ScalarLowRegion_filteredKernel_eq_zero_of_succ_height_le
    {C c : ℝ} {j : ℤ} {n s' : ℕ}
    (h : s' + 1 ≤ n) :
    (if lemma77ScalarLowRegion n s' then
      lemma77HoldPrefixLocalLimitKernel C c n j (s' : ℤ)
    else 0) = 0 := by
  have hnot : ¬ lemma77ScalarLowRegion n s' :=
    lemma77ScalarLowRegion_not_of_succ_height_le h
  simp [hnot]

/-- The filtered low-region kernel is summable by finite support. -/
theorem lemma77ScalarLowRegion_filteredKernel_summable_of_finite_support
    (C c : ℝ) (j : ℤ) (s' : ℕ) :
    Summable fun n : ℕ =>
      if lemma77ScalarLowRegion n s' then
        lemma77HoldPrefixLocalLimitKernel C c n j (s' : ℤ)
      else 0 := by
  let f : ℕ → ℝ := fun n =>
    if lemma77ScalarLowRegion n s' then
      lemma77HoldPrefixLocalLimitKernel C c n j (s' : ℤ)
    else 0
  have hsupport : Function.support f ⊆ Set.Iio (s' + 1) := by
    intro n hn
    by_contra hlt
    have hge : s' + 1 ≤ n := Nat.le_of_not_gt hlt
    have hzero : f n = 0 := by
      dsimp [f]
      exact lemma77ScalarLowRegion_filteredKernel_eq_zero_of_succ_height_le
        (C := C) (c := c) (j := j) hge
    exact hn hzero
  have hfinite : Function.HasFiniteSupport f :=
    Set.Finite.subset (Set.finite_Iio (s' + 1)) hsupport
  simpa [f] using (summable_of_hasFiniteSupport hfinite : Summable f)

/-- Safe common low-region pointwise decay rate. -/
def lemma77ScalarLowRegionRate (c : ℝ) : ℝ :=
  min (c / 8) (2 * c ^ 2)

/-- The low-region pointwise decay rate is positive for positive input rate. -/
theorem lemma77ScalarLowRegionRate_pos
    {c : ℝ} (hc : 0 < c) :
    0 < lemma77ScalarLowRegionRate c := by
  unfold lemma77ScalarLowRegionRate
  exact lt_min (by positivity) (by positivity)

/-- The low-region pointwise decay rate is at most `c / 8`. -/
theorem lemma77ScalarLowRegionRate_le_c_div_eight (c : ℝ) :
    lemma77ScalarLowRegionRate c ≤ c / 8 := by
  unfold lemma77ScalarLowRegionRate
  exact min_le_left _ _

/-- The low-region pointwise decay rate is at most `2 * c^2`. -/
theorem lemma77ScalarLowRegionRate_le_two_mul_sq (c : ℝ) :
    lemma77ScalarLowRegionRate c ≤ 2 * c ^ 2 := by
  unfold lemma77ScalarLowRegionRate
  exact min_le_right _ _

/-- In the low scalar region, the positive time gap dominates `16n`. -/
theorem lemma77ScalarLowRegion_sixteen_mul_lt_neg_timeOffset_real
    {n s' : ℕ}
    (hlow : lemma77ScalarLowRegion n s') :
    16 * (n : ℝ) < -lemma77ScalarTimeOffset n s' := by
  unfold lemma77ScalarLowRegion at hlow
  have hnat : 32 * n < s' := hlow
  have hreal : 32 * (n : ℝ) < (s' : ℝ) := by
    exact_mod_cast hnat
  unfold lemma77ScalarTimeOffset
  nlinarith

/--
Positive-index low-region Gaussian time reserve.  This is the division-safe
form used before bounding the low Gaussian branch by a linear height tail.
-/
theorem lemma77ScalarLowRegion_timeOffset_sq_div_ge_sixteen_gap
    {n s' : ℕ}
    (hlow : lemma77ScalarLowRegion n s') (hn : 0 < n) :
    16 * (-lemma77ScalarTimeOffset n s') ≤
      (lemma77ScalarTimeOffset n s') ^ 2 / (n : ℝ) := by
  let v : ℝ := -lemma77ScalarTimeOffset n s'
  have hv_pos : 0 < v := by
    dsimp [v]
    exact lemma77ScalarLowRegion_neg_timeOffset_pos hlow
  have hnR : 0 < (n : ℝ) := by
    exact_mod_cast hn
  have hgap : 16 * (n : ℝ) < v := by
    dsimp [v]
    exact lemma77ScalarLowRegion_sixteen_mul_lt_neg_timeOffset_real hlow
  have hmul : 16 * (n : ℝ) * v ≤ v ^ 2 := by
    nlinarith [hgap, hv_pos]
  dsimp [v] at hmul hv_pos hgap
  have hsq : (-lemma77ScalarTimeOffset n s') ^ 2 =
      (lemma77ScalarTimeOffset n s') ^ 2 := by
    ring
  rw [hsq] at hmul
  field_simp [hnR.ne']
  nlinarith

/-- Elementary square budget used by the positive low Gaussian branch. -/
theorem lemma77_two_abs_le_sq_div_add_nat
    (y : ℝ) {n : ℕ} (hn : 0 < n) :
    2 * |y| ≤ y ^ 2 / (n : ℝ) + (n : ℝ) := by
  have hnR : 0 < (n : ℝ) := by
    exact_mod_cast hn
  have hsquare : 0 ≤ (|y| - (n : ℝ)) ^ 2 := sq_nonneg _
  have hy2 : |y| ^ 2 = y ^ 2 := by
    rw [sq_abs]
  field_simp [hnR.ne']
  nlinarith

/--
Combined low-region horizontal and height budget before spending the vertical
square reserve.
-/
theorem lemma77ScalarLowRegion_height_horizontal_budget
    {n s' : ℕ} (hn : 0 < n)
    (hlow : lemma77ScalarLowRegion n s') (x : ℝ) :
    2 * (|x| + (1 + (s' : ℝ))) ≤
      ((x - lemma77ScalarTimeOffset n s' / 4) ^ 2 / (n : ℝ)) +
        16 * (-lemma77ScalarTimeOffset n s') := by
  let u : ℝ := lemma77ScalarTimeOffset n s'
  let v : ℝ := -u
  let y : ℝ := x - u / 4
  have hv_pos : 0 < v := by
    dsimp [v, u]
    exact lemma77ScalarLowRegion_neg_timeOffset_pos hlow
  have hv_big : 16 * (n : ℝ) < v := by
    dsimp [v, u]
    exact lemma77ScalarLowRegion_sixteen_mul_lt_neg_timeOffset_real hlow
  have hs_eq : (s' : ℝ) = v + 16 * (n : ℝ) := by
    dsimp [v, u, lemma77ScalarTimeOffset]
    ring
  have hn_ge_one : (1 : ℝ) ≤ (n : ℝ) := by
    exact_mod_cast hn
  have hy_bound : 2 * |y| ≤ y ^ 2 / (n : ℝ) + (n : ℝ) :=
    lemma77_two_abs_le_sq_div_add_nat y hn
  have hx_eq : x = y - v / 4 := by
    dsimp [y, v, u]
    ring
  have hv4_nonneg : 0 ≤ v / 4 := by
    positivity
  have hneg_abs : |-v / 4| = v / 4 := by
    rw [show -v / 4 = -(v / 4) by ring, abs_neg,
      abs_of_nonneg hv4_nonneg]
  have hx_abs : |x| ≤ |y| + v / 4 := by
    calc
      |x| = |y + (-v / 4)| := by
        rw [hx_eq]
        ring_nf
      _ ≤ |y| + |-v / 4| := abs_add_le y (-v / 4)
      _ = |y| + v / 4 := by
        rw [hneg_abs]
  have hx_budget : 2 * |x| ≤ y ^ 2 / (n : ℝ) + (n : ℝ) + v / 2 := by
    nlinarith [hx_abs, hy_bound]
  have hheight_budget :
      (n : ℝ) + v / 2 + 2 * (1 + (s' : ℝ)) ≤ 16 * v := by
    nlinarith [hs_eq, hv_big, hn_ge_one]
  dsimp [y, v, u] at hx_budget hheight_budget ⊢
  nlinarith

/--
Positive-index low-region quadratic reserve retaining both target-height and
centered-horizontal decay.
-/
theorem lemma77ScalarLowRegion_quadraticReserve_ge_two_height_horizontal
    {n s' : ℕ} (hn : 0 < n)
    (hlow : lemma77ScalarLowRegion n s') (x : ℝ) :
    2 * (|x| + (1 + (s' : ℝ))) ≤
      (((x - lemma77ScalarTimeOffset n s' / 4) ^ 2 +
        (lemma77ScalarTimeOffset n s') ^ 2) / (n : ℝ)) := by
  have hbudget :=
    lemma77ScalarLowRegion_height_horizontal_budget hn hlow x
  have hgap :=
    lemma77ScalarLowRegion_timeOffset_sq_div_ge_sixteen_gap hlow hn
  calc
    2 * (|x| + (1 + (s' : ℝ))) ≤
        (x - lemma77ScalarTimeOffset n s' / 4) ^ 2 / (n : ℝ) +
          16 * (-lemma77ScalarTimeOffset n s') := hbudget
    _ ≤ (x - lemma77ScalarTimeOffset n s' / 4) ^ 2 / (n : ℝ) +
          (lemma77ScalarTimeOffset n s') ^ 2 / (n : ℝ) := by
        exact add_le_add le_rfl hgap
    _ = (((x - lemma77ScalarTimeOffset n s' / 4) ^ 2 +
        (lemma77ScalarTimeOffset n s') ^ 2) / (n : ℝ)) := by
        ring

/-- In the high scalar region the prefix length is positive. -/
theorem lemma77ScalarHighRegion_pos
    {n s' : ℕ}
    (hhigh : lemma77ScalarHighRegion n s') :
    0 < n := by
  unfold lemma77ScalarHighRegion at hhigh
  omega

/-- In the high scalar region, the local-limit prefactor is bounded by `1/n`. -/
theorem lemma77LocalLimitPrefactor_le_inv_of_highRegion
    {n s' : ℕ}
    (hhigh : lemma77ScalarHighRegion n s') :
    lemma77LocalLimitPrefactor n ≤ ((n : ℝ)⁻¹) :=
  lemma77LocalLimitPrefactor_le_inv_of_pos
    (lemma77ScalarHighRegion_pos hhigh)

/-- In the high scalar region, `s' + 1` is bounded by `8n`. -/
theorem lemma77ScalarHighRegion_succ_le_eight_mul
    {n s' : ℕ}
    (hhigh : lemma77ScalarHighRegion n s') :
    s' + 1 ≤ 8 * n := by
  unfold lemma77ScalarHighRegion at hhigh
  omega

/-- Real-cast version of the high-region bound `s' + 1 ≤ 8n`. -/
theorem lemma77ScalarHighRegion_one_add_le_eight_mul_real
    {n s' : ℕ}
    (hhigh : lemma77ScalarHighRegion n s') :
    (1 + (s' : ℝ)) ≤ 8 * (n : ℝ) := by
  have hnat : s' + 1 ≤ 8 * n :=
    lemma77ScalarHighRegion_succ_le_eight_mul hhigh
  have hreal : ((s' + 1 : ℕ) : ℝ) ≤ 8 * (n : ℝ) := by
    exact_mod_cast hnat
  norm_num at hreal ⊢
  linarith

/--
In the high scalar region, `1/n` is controlled by the target
`(1+s')^(-1/2)` prefactor up to an absolute constant.
-/
theorem lemma77ScalarHighRegion_inv_le_eight_prefactor
    {n s' : ℕ}
    (hhigh : lemma77ScalarHighRegion n s') :
    ((n : ℝ)⁻¹) ≤
      8 * ((1 + (s' : ℝ)) ^ (-(1 / 2 : ℝ))) := by
  have hn : 0 < n := lemma77ScalarHighRegion_pos hhigh
  have hnR : 0 < (n : ℝ) := by
    exact_mod_cast hn
  have hm_pos : 0 < 1 + (s' : ℝ) := by
    positivity
  have hm_nonneg : 0 ≤ 1 + (s' : ℝ) := le_of_lt hm_pos
  have hm_ge_one : 1 ≤ 1 + (s' : ℝ) := by
    exact le_add_of_nonneg_right (Nat.cast_nonneg s')
  have hm_le : 1 + (s' : ℝ) ≤ 8 * (n : ℝ) :=
    lemma77ScalarHighRegion_one_add_le_eight_mul_real hhigh
  have hsqr_le_self : Real.sqrt (1 + (s' : ℝ)) ≤ 1 + (s' : ℝ) := by
    rw [Real.sqrt_le_left hm_nonneg]
    nlinarith [hm_ge_one]
  have hsqr_le : Real.sqrt (1 + (s' : ℝ)) ≤ 8 * (n : ℝ) :=
    le_trans hsqr_le_self hm_le
  rw [Real.rpow_neg hm_nonneg]
  rw [← Real.sqrt_eq_rpow]
  field_simp [hnR.ne', (Real.sqrt_pos.2 hm_pos).ne']
  nlinarith [hsqr_le]

/--
In the high scalar region, the local-limit prefactor is controlled by the
target height-potential prefactor.
-/
theorem lemma77ScalarHighRegion_prefactor_le_heightPrefactor
    {n s' : ℕ}
    (hhigh : lemma77ScalarHighRegion n s') :
    lemma77LocalLimitPrefactor n ≤
      8 * ((1 + (s' : ℝ)) ^ (-(1 / 2 : ℝ))) :=
  le_trans (lemma77LocalLimitPrefactor_le_inv_of_highRegion hhigh)
    (lemma77ScalarHighRegion_inv_le_eight_prefactor hhigh)

/-- The scalar time offset is positive in the high scalar region. -/
theorem lemma77ScalarTimeOffset_pos_of_highRegion
    {n s' : ℕ}
    (hhigh : lemma77ScalarHighRegion n s') :
    0 < lemma77ScalarTimeOffset n s' := by
  unfold lemma77ScalarHighRegion at hhigh
  have hnat : s' < 16 * n := by
    omega
  have hreal : (s' : ℝ) < 16 * (n : ℝ) := by
    exact_mod_cast hnat
  unfold lemma77ScalarTimeOffset
  nlinarith

/-- In the high scalar region, the scalar time offset is larger than `8n`. -/
theorem lemma77ScalarHighRegion_eight_mul_lt_timeOffset_real
    {n s' : ℕ}
    (hhigh : lemma77ScalarHighRegion n s') :
    8 * (n : ℝ) < lemma77ScalarTimeOffset n s' := by
  unfold lemma77ScalarHighRegion at hhigh
  have hnat : s' < 8 * n := by
    omega
  have hreal : (s' : ℝ) < 8 * (n : ℝ) := by
    exact_mod_cast hnat
  unfold lemma77ScalarTimeOffset
  nlinarith

/--
High-region squared time-offset comparison, divided by positive prefix length.

This reserves the large vertical offset before later spending part of its
exponential decay on the final `(1+s')^(-1/2)` prefactor.
-/
theorem lemma77ScalarHighRegion_eight_mul_sq_div_le_timeOffset_sq_div
    {n s' : ℕ}
    (hhigh : lemma77ScalarHighRegion n s') :
    (8 * (n : ℝ)) ^ 2 / (n : ℝ) ≤
      (lemma77ScalarTimeOffset n s') ^ 2 / (n : ℝ) := by
  have hn : 0 < n := lemma77ScalarHighRegion_pos hhigh
  have hnR : 0 < (n : ℝ) := by
    exact_mod_cast hn
  have hu : 8 * (n : ℝ) < lemma77ScalarTimeOffset n s' :=
    lemma77ScalarHighRegion_eight_mul_lt_timeOffset_real hhigh
  have hnonneg : 0 ≤ 8 * (n : ℝ) := by
    positivity
  have hsquare :
      (8 * (n : ℝ)) ^ 2 ≤ (lemma77ScalarTimeOffset n s') ^ 2 := by
    exact sq_le_sq.mpr (by
      simpa [abs_of_nonneg hnonneg,
        abs_of_nonneg (le_of_lt (lt_trans (by positivity) hu))]
        using le_of_lt hu)
  exact div_le_div_of_nonneg_right hsquare hnR.le

/--
Reserved high-region time decay converted to the final
`(1+s')^(-1/2)` prefactor.

This is a preparatory bound: later high-region kernel estimates should reserve
one positive exponential decay factor and apply this lemma before consuming the
remaining decay through the product-tail estimate.
-/
theorem lemma77ScalarHighRegion_exp_time_le_prefactor
    {a : ℝ} (ha : 0 < a)
    {n s' : ℕ}
    (hhigh : lemma77ScalarHighRegion n s') :
    Real.exp (-(a * (n : ℝ))) ≤
      ((8 * Real.exp (-1)) / a) *
        ((1 + (s' : ℝ)) ^ (-(1 / 2 : ℝ))) := by
  have hn : 0 < n := lemma77ScalarHighRegion_pos hhigh
  have hnR : 0 < (n : ℝ) := by
    exact_mod_cast hn
  have hy_pos : 0 < a * (n : ℝ) := mul_pos ha hnR
  have hmul := Real.mul_exp_neg_le_exp_neg_one (a * (n : ℝ))
  have hexp_le :
      Real.exp (-(a * (n : ℝ))) ≤ Real.exp (-1) / (a * (n : ℝ)) := by
    rw [le_div_iff₀' hy_pos]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmul
  have hinv := lemma77ScalarHighRegion_inv_le_eight_prefactor hhigh
  have hconst_nonneg : 0 ≤ Real.exp (-1) / a := by
    positivity
  calc
    Real.exp (-(a * (n : ℝ))) ≤
        Real.exp (-1) / (a * (n : ℝ)) := hexp_le
    _ = (Real.exp (-1) / a) * ((n : ℝ)⁻¹) := by
        field_simp [ha.ne']
    _ ≤ (Real.exp (-1) / a) *
          (8 * ((1 + (s' : ℝ)) ^ (-(1 / 2 : ℝ)))) :=
        mul_le_mul_of_nonneg_left hinv hconst_nonneg
    _ = ((8 * Real.exp (-1)) / a) *
          ((1 + (s' : ℝ)) ^ (-(1 / 2 : ℝ))) := by
        field_simp [ha.ne']

/--
High-region time-offset reserve large enough to spend two exponential prefix
factors in the quadratic branch.
-/
theorem lemma77ScalarHighRegion_two_mul_le_timeOffset_sq_div
    {n s' : ℕ}
    (hhigh : lemma77ScalarHighRegion n s') :
    2 * (n : ℝ) ≤
      (lemma77ScalarTimeOffset n s') ^ 2 / (n : ℝ) := by
  have hn : 0 < n := lemma77ScalarHighRegion_pos hhigh
  have hnR : 0 < (n : ℝ) := by
    exact_mod_cast hn
  have h64 :=
    lemma77ScalarHighRegion_eight_mul_sq_div_le_timeOffset_sq_div hhigh
  have htwo_le :
      2 * (n : ℝ) ≤ (8 * (n : ℝ)) ^ 2 / (n : ℝ) := by
    field_simp [hnR.ne']
    nlinarith [hnR.le]
  exact le_trans htwo_le h64

/--
Squared scalar geometric lower bound.

The constant `1 / 4` is deliberately non-sharp; it is a stable absolute
constant for the later low/high scalar summation estimates and avoids
introducing square-root monotonicity into the first scalar prelude.
-/
theorem lemma77ScalarDisplacement_sq_coercive (x u : ℝ) :
    (1 / 4 : ℝ) * (x ^ 2 + u ^ 2) ≤
      (x - u / 4) ^ 2 + u ^ 2 := by
  nlinarith [sq_nonneg (6 * x - 2 * u), sq_nonneg u]

/-- Sharper square-coercivity canary for the main scalar region. -/
theorem lemma77ScalarMainRegion_radial_sq_lower (x u : ℝ) :
    (1 / 2 : ℝ) * x ^ 2 + (1 / 2 : ℝ) * u ^ 2 ≤
      (x - u / 4) ^ 2 + u ^ 2 := by
  nlinarith [sq_nonneg (4 * x - 2 * u), sq_nonneg u]

/--
Radial lower bound for the high-region linear branch.

This keeps the linear part of Tao's two-term `G_n` kernel separate from the
quadratic/product-tail branch.
-/
theorem lemma77ScalarDisplacement_abs_add_abs_le_radial (x u : ℝ) :
    (|x| + |u|) / 4 ≤ Real.sqrt ((x - u / 4) ^ 2 + u ^ 2) := by
  apply Real.le_sqrt_of_sq_le
  have hcoer := lemma77ScalarDisplacement_sq_coercive x u
  have hsum : (|x| + |u|) ^ 2 ≤ 2 * (x ^ 2 + u ^ 2) := by
    nlinarith [sq_nonneg (|x| - |u|), sq_abs x, sq_abs u]
  nlinarith

/-- Main-slice-facing name for the reusable scalar radial lower bound. -/
theorem lemma77Scalar_radial_main_lower (x u : ℝ) :
    (|x| + |u|) / 4 ≤ Real.sqrt ((x - u / 4) ^ 2 + u ^ 2) :=
  lemma77ScalarDisplacement_abs_add_abs_le_radial x u

/-- Low-slice-facing radial lower bound with positive height gap `v`. -/
theorem lemma77Scalar_radial_low_lower
    {v : ℝ} (hv : 0 ≤ v) (x : ℝ) :
    (|x| + v) / 4 ≤ Real.sqrt ((x + v / 4) ^ 2 + v ^ 2) := by
  have h := lemma77ScalarDisplacement_abs_add_abs_le_radial x (-v)
  have heq :
      Real.sqrt ((x - (-v) / 4) ^ 2 + (-v) ^ 2) =
        Real.sqrt ((x + v / 4) ^ 2 + v ^ 2) := by
    congr 1
    ring
  calc
    (|x| + v) / 4 = (|x| + |-v|) / 4 := by
      rw [abs_neg, abs_of_nonneg hv]
    _ ≤ Real.sqrt ((x - (-v) / 4) ^ 2 + (-v) ^ 2) := h
    _ = Real.sqrt ((x + v / 4) ^ 2 + v ^ 2) := heq

/--
Low-region radial lower bound retaining both signed horizontal displacement
and target-height decay.
-/
theorem lemma77ScalarLowRegion_radial_ge_height_horizontal
    {n s' : ℕ}
    (hlow : lemma77ScalarLowRegion n s') (x : ℝ) :
    (|x| + (1 + (s' : ℝ))) / 8 ≤
      Real.sqrt ((x - lemma77ScalarTimeOffset n s' / 4) ^ 2 +
        (lemma77ScalarTimeOffset n s') ^ 2) := by
  let v : ℝ := -lemma77ScalarTimeOffset n s'
  have hv_nonneg : 0 ≤ v := by
    dsimp [v]
    exact (lemma77ScalarLowRegion_neg_timeOffset_pos hlow).le
  have hS : (1 + (s' : ℝ)) ≤ 2 * v := by
    dsimp [v]
    exact lemma77ScalarLowRegion_one_add_le_two_mul_neg_timeOffset hlow
  have hpre :
      (|x| + (1 + (s' : ℝ))) / 8 ≤ (|x| + v) / 4 := by
    nlinarith [abs_nonneg x, hv_nonneg, hS]
  have hrad := lemma77Scalar_radial_low_lower hv_nonneg x
  have heq :
      Real.sqrt ((x + v / 4) ^ 2 + v ^ 2) =
        Real.sqrt ((x - lemma77ScalarTimeOffset n s' / 4) ^ 2 +
          (lemma77ScalarTimeOffset n s') ^ 2) := by
    dsimp [v]
    congr 1
    ring
  exact le_trans hpre (by
    rw [heq] at hrad
    exact hrad)

/-- Positive scale factors pull out of the radial square root. -/
theorem lemma77ScalarScaledRadial_eq
    {c : ℝ} (hc : 0 < c) (x u : ℝ) :
    Real.sqrt ((c * (x - u / 4)) ^ 2 + (c * (-u)) ^ 2) =
      c * Real.sqrt ((x - u / 4) ^ 2 + u ^ 2) := by
  calc
    Real.sqrt ((c * (x - u / 4)) ^ 2 + (c * (-u)) ^ 2)
        = Real.sqrt (c ^ 2 * ((x - u / 4) ^ 2 + u ^ 2)) := by
          congr 1
          ring
    _ = Real.sqrt (c ^ 2) * Real.sqrt ((x - u / 4) ^ 2 + u ^ 2) := by
          rw [Real.sqrt_mul (sq_nonneg c)]
    _ = c * Real.sqrt ((x - u / 4) ^ 2 + u ^ 2) := by
          rw [Real.sqrt_sq_eq_abs, abs_of_pos hc]

/--
High-region radial lower bound scaled by a positive linear-kernel rate.

This supplies the geometric split for the linear branch:
one exponential prefix factor can be spent on the height prefactor and one can
remain as the summable high-region tail.
-/
theorem lemma77ScalarHighRegion_scaledRadial_ge_abs_time
    {c : ℝ} (hc : 0 < c) {n s' : ℕ}
    (hhigh : lemma77ScalarHighRegion n s') (x : ℝ) :
    c * (|x| / 4 + 2 * (n : ℝ)) ≤
      c * Real.sqrt ((x - lemma77ScalarTimeOffset n s' / 4) ^ 2 +
        (lemma77ScalarTimeOffset n s') ^ 2) := by
  let u := lemma77ScalarTimeOffset n s'
  have hn : 0 < n := lemma77ScalarHighRegion_pos hhigh
  have hnR : 0 < (n : ℝ) := by
    exact_mod_cast hn
  have hrad := lemma77ScalarDisplacement_abs_add_abs_le_radial x u
  have hu : 8 * (n : ℝ) < u :=
    lemma77ScalarHighRegion_eight_mul_lt_timeOffset_real hhigh
  have hu_abs : 8 * (n : ℝ) ≤ |u| := by
    have hzero_lt : 0 < 8 * (n : ℝ) := by
      positivity
    have hu_nonneg : 0 ≤ u := le_of_lt (lt_trans hzero_lt hu)
    rw [abs_of_nonneg hu_nonneg]
    exact le_of_lt hu
  have hpre : |x| / 4 + 2 * (n : ℝ) ≤ (|x| + |u|) / 4 := by
    nlinarith
  have hle := le_trans hpre hrad
  exact mul_le_mul_of_nonneg_left hle hc.le

/--
Positive-height main-region quadratic branch, before summing over the shifted
time-offset lattice.
-/
theorem lemma77ScalarMainRegion_quadraticKernel_le_prefactor_mul_shiftedGaussian
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    {n s' : ℕ} (hs : 0 < s') (hmain : lemma77ScalarMainRegion n s')
    (j : ℤ) :
    C * lemma77LocalLimitPrefactor n *
      Real.exp (-(((c * (lemma77ScalarCenteredHorizontal j s' -
              lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
            (c * (-lemma77ScalarTimeOffset n s')) ^ 2) / (n : ℝ))) ≤
      (33 * C) * ((1 + (s' : ℝ))⁻¹) *
        Real.exp (-(((c ^ 2) / 4) *
          (lemma77ScalarCenteredHorizontal j s') ^ 2 / (1 + (s' : ℝ)))) *
        Real.exp (-(((c ^ 2) / 4) *
          (lemma77ScalarTimeOffset n s') ^ 2 / (1 + (s' : ℝ)))) := by
  let x : ℝ := lemma77ScalarCenteredHorizontal j s'
  let u : ℝ := lemma77ScalarTimeOffset n s'
  let S : ℝ := 1 + (s' : ℝ)
  let a : ℝ := (c ^ 2) / 4
  let D : ℝ := (c * (x - u / 4)) ^ 2 + (c * (-u)) ^ 2
  have hn : 0 < n := lemma77ScalarMainRegion_pos_of_spos hs hmain
  have hnR : 0 < (n : ℝ) := by
    exact_mod_cast hn
  have hS_pos : 0 < S := by
    dsimp [S]
    positivity
  have hn_le_s : n ≤ s' := lemma77ScalarMainRegion_le_height hmain
  have hn_le_S : (n : ℝ) ≤ S := by
    dsimp [S]
    have hn_le_s_real : (n : ℝ) ≤ (s' : ℝ) := by
      exact_mod_cast hn_le_s
    linarith
  have ha_nonneg : 0 ≤ a := by
    dsimp [a]
    positivity
  have hx2_nonneg : 0 ≤ x ^ 2 := sq_nonneg x
  have hu2_nonneg : 0 ≤ u ^ 2 := sq_nonneg u
  have hA_nonneg : 0 ≤ a * (x ^ 2 + u ^ 2) := by
    exact mul_nonneg ha_nonneg (add_nonneg hx2_nonneg hu2_nonneg)
  have hD_nonneg : 0 ≤ D := by
    dsimp [D]
    positivity
  have hrad := lemma77ScalarMainRegion_radial_sq_lower x u
  have hD_lower : a * (x ^ 2 + u ^ 2) ≤ D := by
    dsimp [a, D]
    have hc2_nonneg : 0 ≤ c ^ 2 := sq_nonneg c
    nlinarith [mul_le_mul_of_nonneg_left hrad hc2_nonneg]
  have hdiv : a * (x ^ 2 + u ^ 2) / S ≤ D / (n : ℝ) := by
    rw [div_le_div_iff₀ hS_pos hnR]
    nlinarith [hD_lower, hn_le_S, hA_nonneg, hD_nonneg]
  have hexp :
      Real.exp (-(D / (n : ℝ))) ≤
        Real.exp (-(a * x ^ 2 / S)) *
          Real.exp (-(a * u ^ 2 / S)) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    have hsplit :
        a * (x ^ 2 + u ^ 2) / S = a * x ^ 2 / S + a * u ^ 2 / S := by
      ring
    nlinarith [hdiv, hsplit]
  have hpref := lemma77ScalarMainRegion_prefactor_le_thirtythree_inv hmain
  have hcpref : C * lemma77LocalLimitPrefactor n ≤ C * (33 * S⁻¹) := by
    dsimp [S]
    exact mul_le_mul_of_nonneg_left hpref hC
  have hright_factor_nonneg : 0 ≤ C * (33 * S⁻¹) := by
    exact mul_nonneg hC (by dsimp [S]; positivity)
  calc
    C * lemma77LocalLimitPrefactor n *
      Real.exp (-(((c * (lemma77ScalarCenteredHorizontal j s' -
              lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
            (c * (-lemma77ScalarTimeOffset n s')) ^ 2) / (n : ℝ)))
        = (C * lemma77LocalLimitPrefactor n) * Real.exp (-(D / (n : ℝ))) := by
          simp [D, x, u]
    _ ≤ (C * (33 * S⁻¹)) *
        (Real.exp (-(a * x ^ 2 / S)) * Real.exp (-(a * u ^ 2 / S))) := by
          exact mul_le_mul hcpref hexp (le_of_lt (Real.exp_pos _))
            hright_factor_nonneg
    _ = (33 * C) * ((1 + (s' : ℝ))⁻¹) *
        Real.exp (-(((c ^ 2) / 4) *
          (lemma77ScalarCenteredHorizontal j s') ^ 2 / (1 + (s' : ℝ)))) *
        Real.exp (-(((c ^ 2) / 4) *
          (lemma77ScalarTimeOffset n s') ^ 2 / (1 + (s' : ℝ)))) := by
          simp [S, a, x, u]
          ring

/--
Main-region linear branch, before summing over the shifted time-offset
lattice.
-/
theorem lemma77ScalarMainRegion_linearKernel_le_prefactor_mul_shiftedLinear
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    {n s' : ℕ} (hmain : lemma77ScalarMainRegion n s')
    (j : ℤ) :
    C * lemma77LocalLimitPrefactor n *
      Real.exp (-Real.sqrt
        ((c * (lemma77ScalarCenteredHorizontal j s' -
              lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
            (c * (-lemma77ScalarTimeOffset n s')) ^ 2)) ≤
      (33 * C) * ((1 + (s' : ℝ))⁻¹) *
        Real.exp (-((c / 4) * |lemma77ScalarCenteredHorizontal j s'|)) *
        Real.exp (-((c / 4) * |lemma77ScalarTimeOffset n s'|)) := by
  let x : ℝ := lemma77ScalarCenteredHorizontal j s'
  let u : ℝ := lemma77ScalarTimeOffset n s'
  let S : ℝ := 1 + (s' : ℝ)
  let R : ℝ := Real.sqrt ((x - u / 4) ^ 2 + u ^ 2)
  have hscaled :
      Real.sqrt ((c * (x - u / 4)) ^ 2 + (c * (-u)) ^ 2) = c * R := by
    dsimp [R]
    exact lemma77ScalarScaledRadial_eq hc x u
  have hrad := lemma77ScalarDisplacement_abs_add_abs_le_radial x u
  have hrad_scaled : (c / 4) * |x| + (c / 4) * |u| ≤ c * R := by
    nlinarith [mul_le_mul_of_nonneg_left hrad hc.le]
  have hexp :
      Real.exp (-(c * R)) ≤
        Real.exp (-((c / 4) * |x|)) * Real.exp (-((c / 4) * |u|)) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    nlinarith
  have hpref := lemma77ScalarMainRegion_prefactor_le_thirtythree_inv hmain
  have hcpref : C * lemma77LocalLimitPrefactor n ≤ C * (33 * S⁻¹) := by
    dsimp [S]
    exact mul_le_mul_of_nonneg_left hpref hC
  have hright_factor_nonneg : 0 ≤ C * (33 * S⁻¹) := by
    exact mul_nonneg hC (by dsimp [S]; positivity)
  calc
    C * lemma77LocalLimitPrefactor n *
      Real.exp (-Real.sqrt
        ((c * (lemma77ScalarCenteredHorizontal j s' -
              lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
            (c * (-lemma77ScalarTimeOffset n s')) ^ 2))
        = (C * lemma77LocalLimitPrefactor n) * Real.exp (-(c * R)) := by
          rw [show Real.sqrt
            ((c * (lemma77ScalarCenteredHorizontal j s' -
                  lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
                (c * (-lemma77ScalarTimeOffset n s')) ^ 2) = c * R by
              simpa [x, u] using hscaled]
    _ ≤ (C * (33 * S⁻¹)) *
        (Real.exp (-((c / 4) * |x|)) *
          Real.exp (-((c / 4) * |u|))) := by
          exact mul_le_mul hcpref hexp (le_of_lt (Real.exp_pos _))
            hright_factor_nonneg
    _ = (33 * C) * ((1 + (s' : ℝ))⁻¹) *
        Real.exp (-((c / 4) * |lemma77ScalarCenteredHorizontal j s'|)) *
        Real.exp (-((c / 4) * |lemma77ScalarTimeOffset n s'|)) := by
          simp [S, x, u]
          ring

/-- Pure exponential decay over `ℕ` is summable for positive rate. -/
theorem lemma77ExpNegMulNat_summable {a : ℝ} (ha : 0 < a) :
    Summable fun n : ℕ => Real.exp (-(a * (n : ℝ))) := by
  have hr : ‖Real.exp (-a)‖ < 1 := by
    rw [Real.norm_eq_abs]
    rw [abs_of_pos (Real.exp_pos (-a))]
    rw [Real.exp_lt_one_iff]
    linarith
  have hgeom : Summable fun n : ℕ => (Real.exp (-a)) ^ n :=
    summable_geometric_of_norm_lt_one hr
  convert hgeom using 1
  ext n
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- The pure exponential tail over `ℕ` has its geometric `tsum` value. -/
theorem lemma77ExpNegMulNat_tsum {a : ℝ} (ha : 0 < a) :
    (∑' n : ℕ, Real.exp (-(a * (n : ℝ)))) =
      (1 - Real.exp (-a))⁻¹ := by
  have hbase_nonneg : 0 ≤ Real.exp (-a) := le_of_lt (Real.exp_pos _)
  have hbase_lt : Real.exp (-a) < 1 := by
    rw [Real.exp_lt_one_iff]
    linarith
  rw [← tsum_geometric_of_lt_one hbase_nonneg hbase_lt]
  apply tsum_congr
  intro n
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- Pure exponential decay over `ℤ` with absolute value is summable. -/
theorem lemma77ExpNegMulIntAbs_summable {a : ℝ} (ha : 0 < a) :
    Summable fun z : ℤ => Real.exp (-(a * |(z : ℝ)|)) := by
  apply Summable.of_nat_of_neg_add_one
  · simpa using (lemma77ExpNegMulNat_summable ha)
  · have htail :
        Summable fun n : ℕ =>
          Real.exp (-(a * (((n + 1 : ℕ) : ℝ)))) := by
      simpa [Function.comp_def] using
        (lemma77ExpNegMulNat_summable ha).comp_injective Nat.succ_injective
    convert htail using 1
    ext n
    have habs : |-1 + -(n : ℝ)| = (n : ℝ) + 1 := by
      rw [abs_of_nonpos]
      · ring
      · nlinarith [show 0 ≤ (n : ℝ) by positivity]
    simpa [Int.cast_neg, Int.cast_add, Int.cast_natCast] using (Or.inl habs)

/-- A two-sided exponential tail over `ℤ` is bounded by two one-sided tails. -/
theorem lemma77ExpNegMulIntAbs_tsum_le {a : ℝ} (ha : 0 < a) :
    (∑' z : ℤ, Real.exp (-(a * |(z : ℝ)|))) ≤
      2 * (1 - Real.exp (-a))⁻¹ := by
  let f : ℤ → ℝ := fun z => Real.exp (-(a * |(z : ℝ)|))
  have hf_nat : Summable fun n : ℕ => Real.exp (-(a * (n : ℝ))) :=
    lemma77ExpNegMulNat_summable ha
  have htail_model :
      Summable fun n : ℕ =>
        Real.exp (-(a * (((n + 1 : ℕ) : ℝ)))) := by
    simpa [Function.comp_def] using
      (lemma77ExpNegMulNat_summable ha).comp_injective Nat.succ_injective
  have hf_pos : Summable fun n : ℕ => f (n : ℤ) := by
    simpa [f] using hf_nat
  have hf_neg : Summable fun n : ℕ => f (-(↑n + 1 : ℤ)) := by
    convert htail_model using 1
    ext n
    have habs : |-1 + -(n : ℝ)| = (n : ℝ) + 1 := by
      rw [abs_of_nonpos]
      · ring
      · nlinarith [show 0 ≤ (n : ℝ) by positivity]
    simpa [f, Int.cast_neg, Int.cast_add, Int.cast_natCast] using (Or.inl habs)
  have htail_le :
      (∑' n : ℕ, f (-(↑n + 1 : ℤ))) ≤
        (∑' n : ℕ, Real.exp (-(a * (n : ℝ)))) := by
    have hpoint :
        ∀ n : ℕ, f (-(↑n + 1 : ℤ)) ≤
          Real.exp (-(a * (n : ℝ))) := by
      intro n
      change Real.exp (-(a * |((-(↑n + 1 : ℤ) : ℤ) : ℝ)|)) ≤
        Real.exp (-(a * (n : ℝ)))
      rw [Real.exp_le_exp]
      have habs : |((-(↑n + 1 : ℤ) : ℤ) : ℝ)| = (n : ℝ) + 1 := by
        have habs' : |-1 + -(n : ℝ)| = (n : ℝ) + 1 := by
          rw [abs_of_nonpos]
          · ring
          · nlinarith [show 0 ≤ (n : ℝ) by positivity]
        simpa [Int.cast_neg, Int.cast_add, Int.cast_natCast] using habs'
      rw [habs]
      nlinarith [ha, show 0 ≤ (n : ℝ) by positivity]
    exact hf_neg.tsum_le_tsum hpoint hf_nat
  have hpos_eq :
      (∑' n : ℕ, f (n : ℤ)) =
        (∑' n : ℕ, Real.exp (-(a * (n : ℝ)))) := by
    apply tsum_congr
    intro n
    simp [f]
  have hnat_eq := lemma77ExpNegMulNat_tsum ha
  have hsplit := tsum_of_nat_of_neg_add_one (f := f) hf_pos hf_neg
  calc
    (∑' z : ℤ, Real.exp (-(a * |(z : ℝ)|))) =
        (∑' n : ℕ, f (n : ℤ)) + (∑' n : ℕ, f (-(↑n + 1 : ℤ))) := by
          simpa [f] using hsplit
    _ ≤ (∑' n : ℕ, Real.exp (-(a * (n : ℝ)))) +
          (∑' n : ℕ, Real.exp (-(a * (n : ℝ)))) := by
          exact add_le_add (le_of_eq hpos_eq) htail_le
    _ = 2 * (1 - Real.exp (-a))⁻¹ := by
          rw [hnat_eq]
          ring

/-- Finite-range shifted linear-exponential count for the main scalar route. -/
theorem lemma77ScalarTimeOffset_rangeLinearCount_le_const_explicit
    {a : ℝ} (ha : 0 < a) (s' : ℕ) :
    (∑ n ∈ Finset.range (s' + 1),
      Real.exp (-(a * |lemma77ScalarTimeOffset n s'|))) ≤
        2 * (1 - Real.exp (-a))⁻¹ := by
  let idx : ℕ → ℤ := fun n => 16 * (n : ℤ) - (s' : ℤ)
  let f : ℤ → ℝ := fun z => Real.exp (-(a * |(z : ℝ)|))
  have hinj : Function.Injective idx := by
    simpa [idx] using lemma77ScalarTimeOffset_intIndex_injective s'
  have hcomp_summable : Summable fun n : ℕ => f (idx n) :=
    (lemma77ExpNegMulIntAbs_summable ha).comp_injective hinj
  have hsum_eq :
      (∑ n ∈ Finset.range (s' + 1),
        Real.exp (-(a * |lemma77ScalarTimeOffset n s'|))) =
          ∑ n ∈ Finset.range (s' + 1), f (idx n) := by
    apply Finset.sum_congr rfl
    intro n hn
    simp [f, idx, lemma77ScalarTimeOffset_eq_intIndex n s']
  have hfinite_le_full :
      (∑ n ∈ Finset.range (s' + 1), f (idx n)) ≤
        ∑' n : ℕ, f (idx n) :=
    hcomp_summable.sum_le_tsum (Finset.range (s' + 1))
      (by intro n hn; exact le_of_lt (Real.exp_pos _))
  have hfull_le_int : (∑' n : ℕ, f (idx n)) ≤ ∑' z : ℤ, f z :=
    tsum_comp_le_tsum_of_inj (lemma77ExpNegMulIntAbs_summable ha)
      (by intro z; exact le_of_lt (Real.exp_pos _)) hinj
  calc
    (∑ n ∈ Finset.range (s' + 1),
      Real.exp (-(a * |lemma77ScalarTimeOffset n s'|))) =
        ∑ n ∈ Finset.range (s' + 1), f (idx n) := hsum_eq
    _ ≤ ∑' n : ℕ, f (idx n) := hfinite_le_full
    _ ≤ ∑' z : ℤ, f z := hfull_le_int
    _ ≤ 2 * (1 - Real.exp (-a))⁻¹ := lemma77ExpNegMulIntAbs_tsum_le ha

/-- Uniform finite-range shifted linear-exponential count. -/
theorem lemma77ScalarTimeOffset_rangeLinearCount_le_const
    {a : ℝ} (ha : 0 < a) :
    ∃ K, 0 ≤ K ∧ ∀ s' : ℕ,
      (∑ n ∈ Finset.range (s' + 1),
        Real.exp (-(a * |lemma77ScalarTimeOffset n s'|))) ≤ K := by
  refine ⟨2 * (1 - Real.exp (-a))⁻¹, ?_, ?_⟩
  · have hlt : Real.exp (-a) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith
    have hpos : 0 < 1 - Real.exp (-a) := by
      linarith
    positivity
  · intro s'
    exact lemma77ScalarTimeOffset_rangeLinearCount_le_const_explicit ha s'

/-- Filtered main shifted linear-exponential count. -/
theorem lemma77ScalarMainRegion_shiftedLinearCount_le_const
    {a : ℝ} (ha : 0 < a) :
    ∃ K, 0 ≤ K ∧ ∀ s' : ℕ,
      (∑' n : ℕ,
        if lemma77ScalarMainRegion n s' then
          Real.exp (-(a * |lemma77ScalarTimeOffset n s'|))
        else 0) ≤ K := by
  obtain ⟨K, hK, hKbound⟩ :=
    lemma77ScalarTimeOffset_rangeLinearCount_le_const ha
  refine ⟨K, hK, ?_⟩
  intro s'
  let term : ℕ → ℝ :=
    fun n => Real.exp (-(a * |lemma77ScalarTimeOffset n s'|))
  have htsum_eq :
      (∑' n : ℕ,
        if lemma77ScalarMainRegion n s' then term n else 0) =
        ∑ n ∈ Finset.range (s' + 1),
          if lemma77ScalarMainRegion n s' then term n else 0 := by
    apply tsum_eq_sum
    intro n hn
    have hnlt : ¬ n < s' + 1 := by
      simpa [Finset.mem_range] using hn
    have hge : s' + 1 ≤ n := Nat.le_of_not_gt hnlt
    have hnot : ¬ lemma77ScalarMainRegion n s' :=
      lemma77ScalarMainRegion_not_of_succ_height_le hge
    simp [hnot]
  have hfinite_le :
      (∑ n ∈ Finset.range (s' + 1),
        if lemma77ScalarMainRegion n s' then term n else 0) ≤
      ∑ n ∈ Finset.range (s' + 1), term n := by
    apply Finset.sum_le_sum
    intro n hn
    by_cases hmain : lemma77ScalarMainRegion n s'
    · simp [hmain]
    · simp [hmain]
      exact le_of_lt (Real.exp_pos _)
  calc
    (∑' n : ℕ,
      if lemma77ScalarMainRegion n s' then
        Real.exp (-(a * |lemma77ScalarTimeOffset n s'|))
      else 0) =
        ∑ n ∈ Finset.range (s' + 1),
          if lemma77ScalarMainRegion n s' then term n else 0 := by
          simpa [term] using htsum_eq
    _ ≤ ∑ n ∈ Finset.range (s' + 1), term n := hfinite_le
    _ ≤ K := by
      simpa [term] using hKbound s'

/-- Reciprocal control for a small exponential denominator. -/
theorem lemma77_one_sub_exp_neg_inv_le_exp_div
    {r A : ℝ} (hr : 0 < r) (hrA : r ≤ A) :
    (1 - Real.exp (-r))⁻¹ ≤ Real.exp A / r := by
  have hexp_pos : 0 < Real.exp r := Real.exp_pos r
  have hdiff_ge : r ≤ Real.exp r - 1 := by
    have h := Real.add_one_le_exp r
    linarith
  have hdiff_pos : 0 < Real.exp r - 1 := lt_of_lt_of_le hr hdiff_ge
  have hden_eq : 1 - Real.exp (-r) = (Real.exp r - 1) / Real.exp r := by
    rw [Real.exp_neg]
    field_simp [hexp_pos.ne']
  calc
    (1 - Real.exp (-r))⁻¹ = Real.exp r / (Real.exp r - 1) := by
      rw [hden_eq]
      field_simp [hexp_pos.ne', hdiff_pos.ne']
    _ ≤ Real.exp r / r := by
      exact div_le_div_of_nonneg_left hexp_pos.le hr hdiff_ge
    _ ≤ Real.exp A / r := by
      exact div_le_div_of_nonneg_right (Real.exp_le_exp.mpr hrA) hr.le

/-- A Gaussian at scale `S` is dominated by a scaled linear exponential tail. -/
theorem lemma77ExpNegMulIntSqDiv_le_scaledAbs
    {a S : ℝ} (ha : 0 ≤ a) (hS : 0 < S) (z : ℤ) :
    Real.exp (-(a * (z : ℝ) ^ 2 / S)) ≤
      Real.exp (a / 4) *
        Real.exp (-((a / Real.sqrt S) * |(z : ℝ)|)) := by
  let y : ℝ := |(z : ℝ)| / Real.sqrt S
  have hS_nonneg : 0 ≤ S := hS.le
  have hsqrt_pos : 0 < Real.sqrt S := Real.sqrt_pos.2 hS
  have hy_sq : y ^ 2 = (z : ℝ) ^ 2 / S := by
    dsimp [y]
    have hsqrt_sq : (Real.sqrt S) ^ 2 = S := Real.sq_sqrt hS_nonneg
    calc
      (|(z : ℝ)| / Real.sqrt S) ^ 2 =
          |(z : ℝ)| ^ 2 / (Real.sqrt S) ^ 2 := by ring
      _ = (z : ℝ) ^ 2 / S := by rw [sq_abs, hsqrt_sq]
  have hyineq : y - 1 / 4 ≤ y ^ 2 := by
    nlinarith [sq_nonneg (y - 1 / 2)]
  have hmul : a * (y - 1 / 4) ≤ a * y ^ 2 :=
    mul_le_mul_of_nonneg_left hyineq ha
  have htarget_y : -(a * y ^ 2) ≤ a / 4 - a * y := by
    nlinarith
  have hrewrite : a * y = (a / Real.sqrt S) * |(z : ℝ)| := by
    dsimp [y]
    field_simp [hsqrt_pos.ne']
  have hquad : -(a * (z : ℝ) ^ 2 / S) ≤
      a / 4 - (a / Real.sqrt S) * |(z : ℝ)| := by
    calc
      -(a * (z : ℝ) ^ 2 / S) = -(a * y ^ 2) := by
        rw [hy_sq]
        ring
      _ ≤ a / 4 - a * y := htarget_y
      _ = a / 4 - (a / Real.sqrt S) * |(z : ℝ)| := by
        rw [hrewrite]
  calc
    Real.exp (-(a * (z : ℝ) ^ 2 / S))
        ≤ Real.exp (a / 4 - (a / Real.sqrt S) * |(z : ℝ)|) := by
          rw [Real.exp_le_exp]
          exact hquad
    _ = Real.exp (a / 4) *
          Real.exp (-((a / Real.sqrt S) * |(z : ℝ)|)) := by
          rw [← Real.exp_add]
          congr 1

/-- Integer Gaussian tails are summable at every positive scale. -/
theorem lemma77ExpNegMulIntSqDiv_summable
    {a S : ℝ} (ha : 0 < a) (hS : 0 < S) :
    Summable fun z : ℤ => Real.exp (-(a * (z : ℝ) ^ 2 / S)) := by
  let r : ℝ := a / Real.sqrt S
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hright : Summable fun z : ℤ =>
      Real.exp (a / 4) * Real.exp (-(r * |(z : ℝ)|)) :=
    (lemma77ExpNegMulIntAbs_summable hr).mul_left (Real.exp (a / 4))
  have hpoint : ∀ z : ℤ,
      Real.exp (-(a * (z : ℝ) ^ 2 / S)) ≤
        Real.exp (a / 4) * Real.exp (-(r * |(z : ℝ)|)) := by
    intro z
    simpa [r] using lemma77ExpNegMulIntSqDiv_le_scaledAbs ha.le hS z
  exact Summable.of_nonneg_of_le
    (fun z => le_of_lt (Real.exp_pos _)) hpoint hright

/-- Explicit square-root bound for two-sided integer Gaussian tails. -/
theorem lemma77ExpNegMulIntSqDiv_tsum_le_sqrt_explicit
    {a S : ℝ} (ha : 0 < a) (hS : 1 ≤ S) :
    (∑' z : ℤ, Real.exp (-(a * (z : ℝ) ^ 2 / S))) ≤
      (2 * Real.exp (a / 4) * Real.exp a / a) * Real.sqrt S := by
  let r : ℝ := a / Real.sqrt S
  have hS_pos : 0 < S := lt_of_lt_of_le zero_lt_one hS
  have hsqrt_pos : 0 < Real.sqrt S := Real.sqrt_pos.2 hS_pos
  have hr : 0 < r := by
    dsimp [r]
    positivity
  have hsqrt_ge_one : 1 ≤ Real.sqrt S := by
    rw [Real.one_le_sqrt]
    exact hS
  have hr_le_a : r ≤ a := by
    dsimp [r]
    rw [div_le_iff₀ hsqrt_pos]
    nlinarith [ha, hsqrt_ge_one]
  have hleft : Summable fun z : ℤ =>
      Real.exp (-(a * (z : ℝ) ^ 2 / S)) :=
    lemma77ExpNegMulIntSqDiv_summable ha hS_pos
  have hright : Summable fun z : ℤ =>
      Real.exp (a / 4) * Real.exp (-(r * |(z : ℝ)|)) :=
    (lemma77ExpNegMulIntAbs_summable hr).mul_left (Real.exp (a / 4))
  have hpoint : ∀ z : ℤ,
      Real.exp (-(a * (z : ℝ) ^ 2 / S)) ≤
        Real.exp (a / 4) * Real.exp (-(r * |(z : ℝ)|)) := by
    intro z
    simpa [r] using lemma77ExpNegMulIntSqDiv_le_scaledAbs ha.le hS_pos z
  have htail := lemma77ExpNegMulIntAbs_tsum_le hr
  have hrec := lemma77_one_sub_exp_neg_inv_le_exp_div hr hr_le_a
  calc
    (∑' z : ℤ, Real.exp (-(a * (z : ℝ) ^ 2 / S)))
        ≤ ∑' z : ℤ, Real.exp (a / 4) *
            Real.exp (-(r * |(z : ℝ)|)) :=
          hleft.tsum_le_tsum hpoint hright
    _ = Real.exp (a / 4) *
          (∑' z : ℤ, Real.exp (-(r * |(z : ℝ)|))) := by
          rw [tsum_mul_left]
    _ ≤ Real.exp (a / 4) * (2 * (1 - Real.exp (-r))⁻¹) := by
          exact mul_le_mul_of_nonneg_left htail (le_of_lt (Real.exp_pos _))
    _ ≤ Real.exp (a / 4) * (2 * (Real.exp a / r)) := by
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_left hrec (by norm_num : (0 : ℝ) ≤ 2))
            (le_of_lt (Real.exp_pos _))
    _ = (2 * Real.exp (a / 4) * Real.exp a / a) * Real.sqrt S := by
          dsimp [r]
          field_simp [ha.ne', hsqrt_pos.ne']

/-- Packaged square-root bound for two-sided integer Gaussian tails. -/
theorem lemma77ExpNegMulIntSqDiv_tsum_le_sqrt
    {a : ℝ} (ha : 0 < a) :
    ∃ K, 0 ≤ K ∧ ∀ S : ℝ, 1 ≤ S →
      (∑' z : ℤ, Real.exp (-(a * (z : ℝ) ^ 2 / S))) ≤
        K * Real.sqrt S := by
  refine ⟨2 * Real.exp (a / 4) * Real.exp a / a, ?_, ?_⟩
  · positivity
  · intro S hS
    exact lemma77ExpNegMulIntSqDiv_tsum_le_sqrt_explicit ha hS

/-- Finite-range shifted Gaussian count for the main scalar route. -/
theorem lemma77ScalarTimeOffset_rangeGaussianCount_le_sqrt_explicit
    {a : ℝ} (ha : 0 < a) (s' : ℕ) :
    (∑ n ∈ Finset.range (s' + 1),
      Real.exp (-(a * (lemma77ScalarTimeOffset n s') ^ 2 /
        (1 + (s' : ℝ))))) ≤
      (2 * Real.exp (a / 4) * Real.exp a / a) *
        Real.sqrt (1 + (s' : ℝ)) := by
  let S : ℝ := 1 + (s' : ℝ)
  let idx : ℕ → ℤ := fun n => 16 * (n : ℤ) - (s' : ℤ)
  let f : ℤ → ℝ := fun z => Real.exp (-(a * (z : ℝ) ^ 2 / S))
  have hS_pos : 0 < S := by
    dsimp [S]
    positivity
  have hS_ge_one : 1 ≤ S := by
    dsimp [S]
    exact le_add_of_nonneg_right (Nat.cast_nonneg s')
  have hinj : Function.Injective idx := by
    simpa [idx] using lemma77ScalarTimeOffset_intIndex_injective s'
  have hcomp_summable : Summable fun n : ℕ => f (idx n) :=
    (lemma77ExpNegMulIntSqDiv_summable ha hS_pos).comp_injective hinj
  have hsum_eq :
      (∑ n ∈ Finset.range (s' + 1),
        Real.exp (-(a * (lemma77ScalarTimeOffset n s') ^ 2 /
          (1 + (s' : ℝ))))) =
          ∑ n ∈ Finset.range (s' + 1), f (idx n) := by
    apply Finset.sum_congr rfl
    intro n hn
    simp [f, idx, S, lemma77ScalarTimeOffset_eq_intIndex n s']
  have hfinite_le_full :
      (∑ n ∈ Finset.range (s' + 1), f (idx n)) ≤
        ∑' n : ℕ, f (idx n) :=
    hcomp_summable.sum_le_tsum (Finset.range (s' + 1))
      (by intro n hn; exact le_of_lt (Real.exp_pos _))
  have hfull_le_int : (∑' n : ℕ, f (idx n)) ≤ ∑' z : ℤ, f z :=
    tsum_comp_le_tsum_of_inj (lemma77ExpNegMulIntSqDiv_summable ha hS_pos)
      (by intro z; exact le_of_lt (Real.exp_pos _)) hinj
  calc
    (∑ n ∈ Finset.range (s' + 1),
      Real.exp (-(a * (lemma77ScalarTimeOffset n s') ^ 2 /
        (1 + (s' : ℝ))))) =
        ∑ n ∈ Finset.range (s' + 1), f (idx n) := hsum_eq
    _ ≤ ∑' n : ℕ, f (idx n) := hfinite_le_full
    _ ≤ ∑' z : ℤ, f z := hfull_le_int
    _ ≤ (2 * Real.exp (a / 4) * Real.exp a / a) *
        Real.sqrt (1 + (s' : ℝ)) := by
        simpa [f, S] using
          lemma77ExpNegMulIntSqDiv_tsum_le_sqrt_explicit ha hS_ge_one

/-- Uniform finite-range shifted Gaussian count. -/
theorem lemma77ScalarTimeOffset_rangeGaussianCount_le_sqrt
    {a : ℝ} (ha : 0 < a) :
    ∃ K, 0 ≤ K ∧ ∀ s' : ℕ,
      (∑ n ∈ Finset.range (s' + 1),
        Real.exp (-(a * (lemma77ScalarTimeOffset n s') ^ 2 /
          (1 + (s' : ℝ))))) ≤ K * Real.sqrt (1 + (s' : ℝ)) := by
  refine ⟨2 * Real.exp (a / 4) * Real.exp a / a, ?_, ?_⟩
  · positivity
  · intro s'
    exact lemma77ScalarTimeOffset_rangeGaussianCount_le_sqrt_explicit ha s'

/-- Filtered main shifted Gaussian count. -/
theorem lemma77ScalarMainRegion_shiftedGaussianCount_le_sqrt
    {a : ℝ} (ha : 0 < a) :
    ∃ K, 0 ≤ K ∧ ∀ s' : ℕ,
      (∑' n : ℕ,
        if lemma77ScalarMainRegion n s' then
          Real.exp (-(a * (lemma77ScalarTimeOffset n s') ^ 2 /
            (1 + (s' : ℝ))))
        else 0) ≤ K * Real.sqrt (1 + (s' : ℝ)) := by
  obtain ⟨K, hK, hKbound⟩ :=
    lemma77ScalarTimeOffset_rangeGaussianCount_le_sqrt ha
  refine ⟨K, hK, ?_⟩
  intro s'
  let term : ℕ → ℝ :=
    fun n => Real.exp (-(a * (lemma77ScalarTimeOffset n s') ^ 2 /
      (1 + (s' : ℝ))))
  have htsum_eq :
      (∑' n : ℕ,
        if lemma77ScalarMainRegion n s' then term n else 0) =
        ∑ n ∈ Finset.range (s' + 1),
          if lemma77ScalarMainRegion n s' then term n else 0 := by
    apply tsum_eq_sum
    intro n hn
    have hnlt : ¬ n < s' + 1 := by
      simpa [Finset.mem_range] using hn
    have hge : s' + 1 ≤ n := Nat.le_of_not_gt hnlt
    have hnot : ¬ lemma77ScalarMainRegion n s' :=
      lemma77ScalarMainRegion_not_of_succ_height_le hge
    simp [hnot]
  have hfinite_le :
      (∑ n ∈ Finset.range (s' + 1),
        if lemma77ScalarMainRegion n s' then term n else 0) ≤
      ∑ n ∈ Finset.range (s' + 1), term n := by
    apply Finset.sum_le_sum
    intro n hn
    by_cases hmain : lemma77ScalarMainRegion n s'
    · simp [hmain]
    · simp [hmain]
      exact le_of_lt (Real.exp_pos _)
  calc
    (∑' n : ℕ,
      if lemma77ScalarMainRegion n s' then
        Real.exp (-(a * (lemma77ScalarTimeOffset n s') ^ 2 /
          (1 + (s' : ℝ))))
      else 0) =
        ∑ n ∈ Finset.range (s' + 1),
          if lemma77ScalarMainRegion n s' then term n else 0 := by
          simpa [term] using htsum_eq
    _ ≤ ∑ n ∈ Finset.range (s' + 1), term n := hfinite_le
    _ ≤ K * Real.sqrt (1 + (s' : ℝ)) := by
      simpa [term] using hKbound s'

/--
Positive-index product-tail term for the isolated scalar product estimate.

The `n = 0` branch is explicitly zero, keeping the division-by-zero convention
out of the source-facing product estimate.
-/
def lemma77ScalarProductTailTerm (a x : ℝ) (n : ℕ) : ℝ :=
  if n = 0 then
    0
  else
    Real.exp (-(a * (n : ℝ)) - a * (x ^ 2 / (n : ℝ))) / (n : ℝ)

@[simp]
theorem lemma77ScalarProductTailTerm_zero (a x : ℝ) :
    lemma77ScalarProductTailTerm a x 0 = 0 := by
  simp [lemma77ScalarProductTailTerm]

/-- Positive-index product-tail terms unfold to the source-facing quotient. -/
theorem lemma77ScalarProductTailTerm_of_pos
    {a x : ℝ} {n : ℕ}
    (hn : 0 < n) :
    lemma77ScalarProductTailTerm a x n =
      Real.exp (-(a * (n : ℝ)) - a * (x ^ 2 / (n : ℝ))) / (n : ℝ) := by
  rw [lemma77ScalarProductTailTerm, ite_eq_right (Nat.ne_of_gt hn)]

/-- Product-tail terms are nonnegative. -/
theorem lemma77ScalarProductTailTerm_nonneg (a x : ℝ) (n : ℕ) :
    0 ≤ lemma77ScalarProductTailTerm a x n := by
  unfold lemma77ScalarProductTailTerm
  by_cases hn : n = 0
  · simp [hn]
  · have hn_pos : 0 < (n : ℝ) := by
      exact_mod_cast Nat.pos_of_ne_zero hn
    simp [hn, div_nonneg (le_of_lt (Real.exp_pos _)) hn_pos.le]

/--
High-region quadratic branch with one exponential factor reserved for the
target height prefactor and the remaining pointwise term left in the checked
product-tail form.

This is not yet the full scalar summation estimate: it is the pointwise
producer that the high Gaussian branch can sum through
`Lemma77ScalarProductTailInput`.
-/
theorem lemma77ScalarHighRegion_quadraticTerm_le_prefactor_mul_productTailTerm
    {a : ℝ} (ha : 0 < a)
    {n s' : ℕ}
    (hhigh : lemma77ScalarHighRegion n s') (x : ℝ) :
    lemma77LocalLimitPrefactor n *
      Real.exp (-(a * (x ^ 2 / (n : ℝ) +
        (lemma77ScalarTimeOffset n s') ^ 2 / (n : ℝ)))) ≤
      ((8 * Real.exp (-1)) / a) *
        ((1 + (s' : ℝ)) ^ (-(1 / 2 : ℝ))) *
        lemma77ScalarProductTailTerm a x n := by
  have hn : 0 < n := lemma77ScalarHighRegion_pos hhigh
  have hnR : 0 < (n : ℝ) := by
    exact_mod_cast hn
  have hpref := lemma77LocalLimitPrefactor_le_inv_of_highRegion hhigh
  have htime :
      2 * (n : ℝ) ≤
        (lemma77ScalarTimeOffset n s') ^ 2 / (n : ℝ) :=
    lemma77ScalarHighRegion_two_mul_le_timeOffset_sq_div hhigh
  have hnum_exp :
      Real.exp (-(a * (x ^ 2 / (n : ℝ) +
        (lemma77ScalarTimeOffset n s') ^ 2 / (n : ℝ)))) ≤
        Real.exp (-(a * (n : ℝ))) *
          Real.exp (-(a * (n : ℝ)) - a * (x ^ 2 / (n : ℝ))) := by
    rw [← Real.exp_add, Real.exp_le_exp]
    nlinarith [mul_le_mul_of_nonneg_left htime ha.le]
  have hquad_to_tail :
      lemma77LocalLimitPrefactor n *
        Real.exp (-(a * (x ^ 2 / (n : ℝ) +
          (lemma77ScalarTimeOffset n s') ^ 2 / (n : ℝ)))) ≤
        Real.exp (-(a * (n : ℝ))) *
          lemma77ScalarProductTailTerm a x n := by
    calc
      lemma77LocalLimitPrefactor n *
          Real.exp (-(a * (x ^ 2 / (n : ℝ) +
            (lemma77ScalarTimeOffset n s') ^ 2 / (n : ℝ))))
          ≤ ((n : ℝ)⁻¹) *
              Real.exp (-(a * (x ^ 2 / (n : ℝ) +
                (lemma77ScalarTimeOffset n s') ^ 2 / (n : ℝ)))) := by
            exact mul_le_mul_of_nonneg_right hpref (le_of_lt (Real.exp_pos _))
      _ ≤ ((n : ℝ)⁻¹) *
            (Real.exp (-(a * (n : ℝ))) *
              Real.exp (-(a * (n : ℝ)) - a * (x ^ 2 / (n : ℝ)))) := by
            exact mul_le_mul_of_nonneg_left hnum_exp (inv_nonneg.mpr hnR.le)
      _ = Real.exp (-(a * (n : ℝ))) *
            lemma77ScalarProductTailTerm a x n := by
            rw [lemma77ScalarProductTailTerm_of_pos hn]
            field_simp [hnR.ne']
  have hreserve := lemma77ScalarHighRegion_exp_time_le_prefactor ha hhigh
  have htail_nonneg : 0 ≤ lemma77ScalarProductTailTerm a x n :=
    lemma77ScalarProductTailTerm_nonneg a x n
  calc
    lemma77LocalLimitPrefactor n *
        Real.exp (-(a * (x ^ 2 / (n : ℝ) +
          (lemma77ScalarTimeOffset n s') ^ 2 / (n : ℝ))))
        ≤ Real.exp (-(a * (n : ℝ))) *
            lemma77ScalarProductTailTerm a x n := hquad_to_tail
    _ ≤ (((8 * Real.exp (-1)) / a) *
          ((1 + (s' : ℝ)) ^ (-(1 / 2 : ℝ)))) *
            lemma77ScalarProductTailTerm a x n := by
          exact mul_le_mul_of_nonneg_right hreserve htail_nonneg
    _ = ((8 * Real.exp (-1)) / a) *
        ((1 + (s' : ℝ)) ^ (-(1 / 2 : ℝ))) *
        lemma77ScalarProductTailTerm a x n := by
          ring

/--
Source-facing high-region bound for the quadratic branch of Tao's two-term
local-limit kernel.

The theorem keeps the final height prefactor visible and leaves the summable
horizontal profile in the existing `/n` product-tail term.
-/
theorem lemma77ScalarHighRegion_gaussianKernel_le_prefactor_mul_productTailTerm
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    {j : ℤ} {n s' : ℕ}
    (hhigh : lemma77ScalarHighRegion n s') :
    C * lemma77LocalLimitPrefactor n *
      Real.exp (-(((c * (lemma77ScalarCenteredHorizontal j s' -
              lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
            (c * (-lemma77ScalarTimeOffset n s')) ^ 2) / (n : ℝ))) ≤
      (C * ((8 * Real.exp (-1)) / ((c ^ 2) / 4))) *
        ((1 + (s' : ℝ)) ^ (-(1 / 2 : ℝ))) *
        lemma77ScalarProductTailTerm ((c ^ 2) / 4)
          (lemma77ScalarCenteredHorizontal j s') n := by
  let x := lemma77ScalarCenteredHorizontal j s'
  let u := lemma77ScalarTimeOffset n s'
  have hn : 0 < n := lemma77ScalarHighRegion_pos hhigh
  have hnR : 0 < (n : ℝ) := by
    exact_mod_cast hn
  have ha : 0 < (c ^ 2) / 4 := by
    positivity
  have hpref_nonneg : 0 ≤ lemma77LocalLimitPrefactor n := by
    unfold lemma77LocalLimitPrefactor
    positivity
  have hcoer := lemma77ScalarDisplacement_sq_coercive x u
  have hgeom :
      ((c ^ 2) / 4) * (x ^ 2 + u ^ 2) ≤
        (c * (x - u / 4)) ^ 2 + (c * (-u)) ^ 2 := by
    have hmul := mul_le_mul_of_nonneg_left hcoer (sq_nonneg c)
    nlinarith
  have harg :
      ((c ^ 2) / 4) * (x ^ 2 / (n : ℝ) + u ^ 2 / (n : ℝ)) ≤
        ((c * (x - u / 4)) ^ 2 + (c * (-u)) ^ 2) / (n : ℝ) := by
    field_simp [hnR.ne']
    nlinarith [hgeom]
  have hexp :
      Real.exp (-(((c * (x - u / 4)) ^ 2 + (c * (-u)) ^ 2) /
          (n : ℝ))) ≤
        Real.exp (-(((c ^ 2) / 4) *
          (x ^ 2 / (n : ℝ) + u ^ 2 / (n : ℝ)))) := by
    rw [Real.exp_le_exp]
    nlinarith [harg]
  have hbase :
      lemma77LocalLimitPrefactor n *
        Real.exp (-(((c * (x - u / 4)) ^ 2 + (c * (-u)) ^ 2) /
          (n : ℝ))) ≤
        lemma77LocalLimitPrefactor n *
          Real.exp (-(((c ^ 2) / 4) *
            (x ^ 2 / (n : ℝ) + u ^ 2 / (n : ℝ)))) :=
    mul_le_mul_of_nonneg_left hexp hpref_nonneg
  have hprod :=
    lemma77ScalarHighRegion_quadraticTerm_le_prefactor_mul_productTailTerm
      ha hhigh x
  calc
    C * lemma77LocalLimitPrefactor n *
        Real.exp (-(((c * (lemma77ScalarCenteredHorizontal j s' -
              lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
            (c * (-lemma77ScalarTimeOffset n s')) ^ 2) / (n : ℝ)))
        = C * (lemma77LocalLimitPrefactor n *
          Real.exp (-(((c * (x - u / 4)) ^ 2 + (c * (-u)) ^ 2) /
            (n : ℝ)))) := by
          simp [x, u]
          ring
    _ ≤ C * (lemma77LocalLimitPrefactor n *
          Real.exp (-(((c ^ 2) / 4) *
            (x ^ 2 / (n : ℝ) + u ^ 2 / (n : ℝ))))) :=
          mul_le_mul_of_nonneg_left hbase hC
    _ ≤ C * (((8 * Real.exp (-1)) / ((c ^ 2) / 4)) *
          ((1 + (s' : ℝ)) ^ (-(1 / 2 : ℝ))) *
          lemma77ScalarProductTailTerm ((c ^ 2) / 4) x n) :=
          mul_le_mul_of_nonneg_left hprod hC
    _ = (C * ((8 * Real.exp (-1)) / ((c ^ 2) / 4))) *
        ((1 + (s' : ℝ)) ^ (-(1 / 2 : ℝ))) *
        lemma77ScalarProductTailTerm ((c ^ 2) / 4)
          (lemma77ScalarCenteredHorizontal j s') n := by
          simp [x]
          ring

/--
Source-facing high-region bound for the linear branch of Tao's two-term
local-limit kernel.

The branch is intentionally separate from `lemma77ScalarProductTailTerm`: one
high-time exponential factor is spent on the target height prefactor, while
one `exp (-c*n)` factor remains for the later high-region summation.
-/
theorem lemma77ScalarHighRegion_linearKernel_le_prefactor_mul_expTail
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    {j : ℤ} {n s' : ℕ}
    (hhigh : lemma77ScalarHighRegion n s') :
    C * lemma77LocalLimitPrefactor n *
      Real.exp (-(c * Real.sqrt
        ((lemma77ScalarCenteredHorizontal j s' -
            lemma77ScalarTimeOffset n s' / 4) ^ 2 +
          (lemma77ScalarTimeOffset n s') ^ 2))) ≤
      (C * ((8 * Real.exp (-1)) / c)) *
        ((1 + (s' : ℝ)) ^ (-(1 / 2 : ℝ))) *
        Real.exp (-(c * (n : ℝ))) *
        Real.exp (-((c / 4) * |lemma77ScalarCenteredHorizontal j s'|)) := by
  let x := lemma77ScalarCenteredHorizontal j s'
  have hn : 0 < n := lemma77ScalarHighRegion_pos hhigh
  have hscaled := lemma77ScalarHighRegion_scaledRadial_ge_abs_time hc hhigh x
  have hexp :
      Real.exp (-(c * Real.sqrt
        ((x - lemma77ScalarTimeOffset n s' / 4) ^ 2 +
          (lemma77ScalarTimeOffset n s') ^ 2))) ≤
      Real.exp (-(c * (|x| / 4 + 2 * (n : ℝ)))) := by
    rw [Real.exp_le_exp]
    nlinarith [hscaled]
  have hpref_one : lemma77LocalLimitPrefactor n ≤ 1 :=
    lemma77LocalLimitPrefactor_le_one_of_pos hn
  have hbase :
      lemma77LocalLimitPrefactor n *
        Real.exp (-(c * Real.sqrt
          ((x - lemma77ScalarTimeOffset n s' / 4) ^ 2 +
            (lemma77ScalarTimeOffset n s') ^ 2))) ≤
      Real.exp (-(c * (n : ℝ))) *
        Real.exp (-(c * (n : ℝ))) *
        Real.exp (-((c / 4) * |x|)) := by
    calc
      lemma77LocalLimitPrefactor n *
          Real.exp (-(c * Real.sqrt
            ((x - lemma77ScalarTimeOffset n s' / 4) ^ 2 +
              (lemma77ScalarTimeOffset n s') ^ 2)))
          ≤ 1 * Real.exp (-(c * (|x| / 4 + 2 * (n : ℝ)))) := by
            exact mul_le_mul hpref_one hexp
              (le_of_lt (Real.exp_pos _)) (by positivity)
      _ = Real.exp (-(c * (n : ℝ))) *
            Real.exp (-(c * (n : ℝ))) *
            Real.exp (-((c / 4) * |x|)) := by
            rw [one_mul, ← Real.exp_add, ← Real.exp_add]
            congr 1
            ring
  have hreserve := lemma77ScalarHighRegion_exp_time_le_prefactor hc hhigh
  calc
    C * lemma77LocalLimitPrefactor n *
        Real.exp (-(c * Real.sqrt
          ((lemma77ScalarCenteredHorizontal j s' -
              lemma77ScalarTimeOffset n s' / 4) ^ 2 +
            (lemma77ScalarTimeOffset n s') ^ 2)))
        = C * (lemma77LocalLimitPrefactor n *
          Real.exp (-(c * Real.sqrt
            ((x - lemma77ScalarTimeOffset n s' / 4) ^ 2 +
              (lemma77ScalarTimeOffset n s') ^ 2)))) := by
          simp [x]
          ring
    _ ≤ C * (Real.exp (-(c * (n : ℝ))) *
        Real.exp (-(c * (n : ℝ))) *
        Real.exp (-((c / 4) * |x|))) :=
          mul_le_mul_of_nonneg_left hbase hC
    _ = C * (Real.exp (-(c * (n : ℝ))) *
        (Real.exp (-(c * (n : ℝ))) *
        Real.exp (-((c / 4) * |x|)))) := by
          ring
    _ ≤ C * ((((8 * Real.exp (-1)) / c) *
        ((1 + (s' : ℝ)) ^ (-(1 / 2 : ℝ)))) *
        (Real.exp (-(c * (n : ℝ))) *
        Real.exp (-((c / 4) * |x|)))) := by
          have htail_nonneg :
              0 ≤ Real.exp (-(c * (n : ℝ))) *
                Real.exp (-((c / 4) * |x|)) := by
            positivity
          exact mul_le_mul_of_nonneg_left
            (mul_le_mul_of_nonneg_right hreserve htail_nonneg) hC
    _ = (C * ((8 * Real.exp (-1)) / c)) *
        ((1 + (s' : ℝ)) ^ (-(1 / 2 : ℝ))) *
        Real.exp (-(c * (n : ℝ))) *
        Real.exp (-((c / 4) * |lemma77ScalarCenteredHorizontal j s'|)) := by
          simp [x]
          ring

/--
Actual scaled high-region linear branch from Tao's two-dimensional
`G_n` argument.

This wrapper rewrites the scaled radial square root before applying the
unscaled positive-rate linear estimate.
-/
theorem lemma77ScalarHighRegion_linearKernelScaled_le_prefactor_mul_expTail
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    {j : ℤ} {n s' : ℕ}
    (hhigh : lemma77ScalarHighRegion n s') :
    C * lemma77LocalLimitPrefactor n *
      Real.exp (-Real.sqrt
        ((c * (lemma77ScalarCenteredHorizontal j s' -
              lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
          (c * (-lemma77ScalarTimeOffset n s')) ^ 2)) ≤
      (C * ((8 * Real.exp (-1)) / c)) *
        ((1 + (s' : ℝ)) ^ (-(1 / 2 : ℝ))) *
        Real.exp (-(c * (n : ℝ))) *
        Real.exp (-((c / 4) * |lemma77ScalarCenteredHorizontal j s'|)) := by
  rw [lemma77ScalarScaledRadial_eq hc
    (lemma77ScalarCenteredHorizontal j s') (lemma77ScalarTimeOffset n s')]
  exact lemma77ScalarHighRegion_linearKernel_le_prefactor_mul_expTail
    hC hc hhigh

/--
At positive prefix length, the local-limit kernel uses the positive-index
branch of Tao's two-term `G_n` weight, splitting into quadratic and linear
contributions.
-/
theorem lemma77HoldPrefixLocalLimitKernel_eq_positiveBranches
    (C c : ℝ) {n : ℕ} (hnpos : 0 < n) (j : ℤ) (s' : ℕ) :
    lemma77HoldPrefixLocalLimitKernel C c n j (s' : ℤ) =
      C * lemma77LocalLimitPrefactor n *
        Real.exp (-(((c * (lemma77ScalarCenteredHorizontal j s' -
                lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
              (c * (-lemma77ScalarTimeOffset n s')) ^ 2) / (n : ℝ))) +
      C * lemma77LocalLimitPrefactor n *
        Real.exp (-Real.sqrt
          ((c * (lemma77ScalarCenteredHorizontal j s' -
                lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
            (c * (-lemma77ScalarTimeOffset n s')) ^ 2)) := by
  have hn : n ≠ 0 := Nat.ne_of_gt hnpos
  let S : ℝ :=
    (c * (lemma77ScalarCenteredHorizontal j s' -
      lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
      (c * (-lemma77ScalarTimeOffset n s')) ^ 2
  have hS_nonneg : 0 ≤ S := by
    dsimp [S]
    positivity
  have hsq : (Real.sqrt S) ^ 2 = S := Real.sq_sqrt hS_nonneg
  have habs : |Real.sqrt S| = Real.sqrt S :=
    abs_of_nonneg (Real.sqrt_nonneg S)
  rw [lemma77HoldPrefixLocalLimitKernel_eq_scalarOffsets]
  change C * lemma77LocalLimitPrefactor n *
      taoLemma22GaussianWeight n (Real.sqrt S) =
    C * lemma77LocalLimitPrefactor n * Real.exp (-(S / (n : ℝ))) +
      C * lemma77LocalLimitPrefactor n * Real.exp (-Real.sqrt S)
  unfold taoLemma22GaussianWeight
  simp [hn, hsq, habs]
  ring

/--
At zero prefix length, the local-limit kernel is the `G_0` radial branch.
-/
theorem lemma77HoldPrefixLocalLimitKernel_zero_eq
    (C c : ℝ) (j : ℤ) (s' : ℕ) :
    lemma77HoldPrefixLocalLimitKernel C c 0 j (s' : ℤ) =
      C * Real.exp (-Real.sqrt ((c * (j : ℝ)) ^ 2 +
        (c * (s' : ℝ)) ^ 2)) := by
  unfold lemma77HoldPrefixLocalLimitKernel taoLemma22GaussianWeight2
    taoLemma22GaussianWeight lemma77LocalLimitPrefactor
    lemma77HoldMeanHorizontalDisplacement lemma77HoldMeanVerticalDisplacement
  simp

/--
In the high region the local-limit kernel uses the positive-index branch of
Tao's two-term `G_n` weight, splitting into quadratic and linear contributions.
-/
theorem lemma77HoldPrefixLocalLimitKernel_eq_highRegionBranches
    (C c : ℝ) {n s' : ℕ}
    (hhigh : lemma77ScalarHighRegion n s') (j : ℤ) :
    lemma77HoldPrefixLocalLimitKernel C c n j (s' : ℤ) =
      C * lemma77LocalLimitPrefactor n *
        Real.exp (-(((c * (lemma77ScalarCenteredHorizontal j s' -
                lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
              (c * (-lemma77ScalarTimeOffset n s')) ^ 2) / (n : ℝ))) +
      C * lemma77LocalLimitPrefactor n *
        Real.exp (-Real.sqrt
          ((c * (lemma77ScalarCenteredHorizontal j s' -
                lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
            (c * (-lemma77ScalarTimeOffset n s')) ^ 2)) :=
  lemma77HoldPrefixLocalLimitKernel_eq_positiveBranches C c
    (lemma77ScalarHighRegion_pos hhigh) j s'

/-- Positive-index branch split in the main region away from the `(0, 0)` boundary. -/
theorem lemma77HoldPrefixLocalLimitKernel_eq_mainRegionBranches_of_spos
    (C c : ℝ) {n s' : ℕ}
    (hs : 0 < s') (hmain : lemma77ScalarMainRegion n s') (j : ℤ) :
    lemma77HoldPrefixLocalLimitKernel C c n j (s' : ℤ) =
      C * lemma77LocalLimitPrefactor n *
        Real.exp (-(((c * (lemma77ScalarCenteredHorizontal j s' -
                lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
              (c * (-lemma77ScalarTimeOffset n s')) ^ 2) / (n : ℝ))) +
      C * lemma77LocalLimitPrefactor n *
        Real.exp (-Real.sqrt
          ((c * (lemma77ScalarCenteredHorizontal j s' -
                lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
            (c * (-lemma77ScalarTimeOffset n s')) ^ 2)) :=
  lemma77HoldPrefixLocalLimitKernel_eq_positiveBranches C c
    (lemma77ScalarMainRegion_pos_of_spos hs hmain) j s'

/-- Positive-index branch split for the low region. -/
theorem lemma77HoldPrefixLocalLimitKernel_eq_lowRegionPositiveBranches
    (C c : ℝ) {n s' : ℕ}
    (_hlow : lemma77ScalarLowRegion n s') (hn : 0 < n) (j : ℤ) :
    lemma77HoldPrefixLocalLimitKernel C c n j (s' : ℤ) =
      C * lemma77LocalLimitPrefactor n *
        Real.exp (-(((c * (lemma77ScalarCenteredHorizontal j s' -
                lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
              (c * (-lemma77ScalarTimeOffset n s')) ^ 2) / (n : ℝ))) +
      C * lemma77LocalLimitPrefactor n *
        Real.exp (-Real.sqrt
          ((c * (lemma77ScalarCenteredHorizontal j s' -
                lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
            (c * (-lemma77ScalarTimeOffset n s')) ^ 2)) :=
  lemma77HoldPrefixLocalLimitKernel_eq_positiveBranches C c hn j s'

/-- Zero-index `G_0` branch for the low region. -/
theorem lemma77HoldPrefixLocalLimitKernel_eq_lowRegionZeroBranch
    (C c : ℝ) {s' : ℕ}
    (_hlow : lemma77ScalarLowRegion 0 s') (j : ℤ) :
    lemma77HoldPrefixLocalLimitKernel C c 0 j (s' : ℤ) =
      C * Real.exp (-Real.sqrt ((c * (j : ℝ)) ^ 2 +
        (c * (s' : ℝ)) ^ 2)) :=
  lemma77HoldPrefixLocalLimitKernel_zero_eq C c j s'

/--
Low-region zero-index branch with centered horizontal decay and target-height
decay at the common low-region rate.
-/
theorem lemma77ScalarLowRegion_zeroKernel_le_exp_profile
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    {j : ℤ} {s' : ℕ}
    (hlow : lemma77ScalarLowRegion 0 s') :
    lemma77HoldPrefixLocalLimitKernel C c 0 j (s' : ℤ) ≤
      C * Real.exp (-(lemma77ScalarLowRegionRate c * (1 + (s' : ℝ)))) *
        Real.exp (-(lemma77ScalarLowRegionRate c *
          |lemma77ScalarCenteredHorizontal j s'|)) := by
  let x := lemma77ScalarCenteredHorizontal j s'
  let S : ℝ := 1 + (s' : ℝ)
  let R : ℝ := Real.sqrt ((x - lemma77ScalarTimeOffset 0 s' / 4) ^ 2 +
    (lemma77ScalarTimeOffset 0 s') ^ 2)
  have hrad := lemma77ScalarLowRegion_radial_ge_height_horizontal hlow x
  have hscaled :
      Real.sqrt ((c * (j : ℝ)) ^ 2 + (c * (s' : ℝ)) ^ 2) = c * R := by
    rw [show (j : ℝ) = x - lemma77ScalarTimeOffset 0 s' / 4 by
      dsimp [x, lemma77ScalarCenteredHorizontal, lemma77ScalarTimeOffset]
      ring]
    rw [show (s' : ℝ) = -lemma77ScalarTimeOffset 0 s' by
      dsimp [lemma77ScalarTimeOffset]
      ring]
    dsimp [R]
    rw [lemma77ScalarScaledRadial_eq hc]
  have hrho_le : lemma77ScalarLowRegionRate c ≤ c / 8 :=
    lemma77ScalarLowRegionRate_le_c_div_eight c
  have hsum_nonneg : 0 ≤ |x| + S := by
    dsimp [S]
    positivity
  have hscale_le :
      lemma77ScalarLowRegionRate c * (|x| + S) ≤ c * ((|x| + S) / 8) := by
    nlinarith [mul_le_mul_of_nonneg_right hrho_le hsum_nonneg]
  have hrad_scaled : c * ((|x| + S) / 8) ≤ c * R := by
    exact mul_le_mul_of_nonneg_left (by simpa [S, R] using hrad) hc.le
  have hdecay_arg : lemma77ScalarLowRegionRate c * (|x| + S) ≤
      Real.sqrt ((c * (j : ℝ)) ^ 2 + (c * (s' : ℝ)) ^ 2) := by
    rw [hscaled]
    exact le_trans hscale_le hrad_scaled
  have hexp :
      Real.exp (-Real.sqrt ((c * (j : ℝ)) ^ 2 + (c * (s' : ℝ)) ^ 2)) ≤
        Real.exp (-(lemma77ScalarLowRegionRate c * (|x| + S))) := by
    rw [Real.exp_le_exp]
    linarith
  have hsplit :
      Real.exp (-(lemma77ScalarLowRegionRate c * (|x| + S))) =
        Real.exp (-(lemma77ScalarLowRegionRate c * S)) *
          Real.exp (-(lemma77ScalarLowRegionRate c * |x|)) := by
    rw [← Real.exp_add]
    ring_nf
  rw [lemma77HoldPrefixLocalLimitKernel_eq_lowRegionZeroBranch C c hlow j]
  calc
    C * Real.exp (-Real.sqrt ((c * (j : ℝ)) ^ 2 + (c * (s' : ℝ)) ^ 2))
        ≤ C * Real.exp (-(lemma77ScalarLowRegionRate c * (|x| + S))) :=
      mul_le_mul_of_nonneg_left hexp hC
    _ = C * (Real.exp (-(lemma77ScalarLowRegionRate c * S)) *
          Real.exp (-(lemma77ScalarLowRegionRate c * |x|))) := by
      rw [hsplit]
    _ = C * Real.exp (-(lemma77ScalarLowRegionRate c * S)) *
        Real.exp (-(lemma77ScalarLowRegionRate c * |x|)) := by
      ring
    _ = C * Real.exp (-(lemma77ScalarLowRegionRate c * (1 + (s' : ℝ)))) *
        Real.exp (-(lemma77ScalarLowRegionRate c *
          |lemma77ScalarCenteredHorizontal j s'|)) := by
      simp [x, S]

/--
Positive-index low-region quadratic branch bounded by the common low
height-horizontal profile.
-/
theorem lemma77ScalarLowRegion_quadraticKernel_le_exp_profile
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    {j : ℤ} {n s' : ℕ} (hn : 0 < n)
    (hlow : lemma77ScalarLowRegion n s') :
    C * lemma77LocalLimitPrefactor n *
      Real.exp (-(((c * (lemma77ScalarCenteredHorizontal j s' -
              lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
            (c * (-lemma77ScalarTimeOffset n s')) ^ 2) / (n : ℝ))) ≤
      C * Real.exp (-(lemma77ScalarLowRegionRate c * (1 + (s' : ℝ)))) *
        Real.exp (-(lemma77ScalarLowRegionRate c *
          |lemma77ScalarCenteredHorizontal j s'|)) := by
  let x := lemma77ScalarCenteredHorizontal j s'
  let u := lemma77ScalarTimeOffset n s'
  let S : ℝ := 1 + (s' : ℝ)
  let A : ℝ := |x| + S
  have hnR : 0 < (n : ℝ) := by
    exact_mod_cast hn
  have hpref_one : lemma77LocalLimitPrefactor n ≤ 1 :=
    lemma77LocalLimitPrefactor_le_one_of_pos hn
  have hA_nonneg : 0 ≤ A := by
    dsimp [A, S]
    positivity
  have hrho_le : lemma77ScalarLowRegionRate c ≤ 2 * c ^ 2 :=
    lemma77ScalarLowRegionRate_le_two_mul_sq c
  have hreserve :
      2 * A ≤ ((x - u / 4) ^ 2 + u ^ 2) / (n : ℝ) := by
    dsimp [A, S, x, u]
    exact lemma77ScalarLowRegion_quadraticReserve_ge_two_height_horizontal
      hn hlow (lemma77ScalarCenteredHorizontal j s')
  have hscale : lemma77ScalarLowRegionRate c * A ≤
      (((c * (x - u / 4)) ^ 2 + (c * (-u)) ^ 2) / (n : ℝ)) := by
    have h1 :
        lemma77ScalarLowRegionRate c * A ≤ (2 * c ^ 2) * A := by
      exact mul_le_mul_of_nonneg_right hrho_le hA_nonneg
    have h2 :
        (2 * c ^ 2) * A ≤
          c ^ 2 * (((x - u / 4) ^ 2 + u ^ 2) / (n : ℝ)) := by
      nlinarith [mul_le_mul_of_nonneg_left hreserve (sq_nonneg c)]
    calc
      lemma77ScalarLowRegionRate c * A ≤ (2 * c ^ 2) * A := h1
      _ ≤ c ^ 2 * (((x - u / 4) ^ 2 + u ^ 2) / (n : ℝ)) := h2
      _ = (((c * (x - u / 4)) ^ 2 + (c * (-u)) ^ 2) / (n : ℝ)) := by
        field_simp [hnR.ne']
  have hexp :
      Real.exp (-(((c * (x - u / 4)) ^ 2 + (c * (-u)) ^ 2) / (n : ℝ))) ≤
        Real.exp (-(lemma77ScalarLowRegionRate c * A)) := by
    rw [Real.exp_le_exp]
    linarith
  have hbase :
      lemma77LocalLimitPrefactor n *
        Real.exp (-(((c * (x - u / 4)) ^ 2 + (c * (-u)) ^ 2) /
          (n : ℝ))) ≤
        Real.exp (-(lemma77ScalarLowRegionRate c * A)) := by
    calc
      lemma77LocalLimitPrefactor n *
          Real.exp (-(((c * (x - u / 4)) ^ 2 + (c * (-u)) ^ 2) /
            (n : ℝ)))
          ≤ 1 * Real.exp (-(lemma77ScalarLowRegionRate c * A)) := by
            exact mul_le_mul hpref_one hexp (le_of_lt (Real.exp_pos _))
              (by positivity)
      _ = Real.exp (-(lemma77ScalarLowRegionRate c * A)) := by
        ring
  have hsplit :
      Real.exp (-(lemma77ScalarLowRegionRate c * A)) =
        Real.exp (-(lemma77ScalarLowRegionRate c * S)) *
          Real.exp (-(lemma77ScalarLowRegionRate c * |x|)) := by
    dsimp [A]
    rw [← Real.exp_add]
    ring_nf
  calc
    C * lemma77LocalLimitPrefactor n *
      Real.exp (-(((c * (lemma77ScalarCenteredHorizontal j s' -
              lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
            (c * (-lemma77ScalarTimeOffset n s')) ^ 2) / (n : ℝ)))
        = C * (lemma77LocalLimitPrefactor n *
          Real.exp (-(((c * (x - u / 4)) ^ 2 + (c * (-u)) ^ 2) /
            (n : ℝ)))) := by
          simp [x, u]
          ring
    _ ≤ C * Real.exp (-(lemma77ScalarLowRegionRate c * A)) :=
      mul_le_mul_of_nonneg_left hbase hC
    _ = C * (Real.exp (-(lemma77ScalarLowRegionRate c * S)) *
          Real.exp (-(lemma77ScalarLowRegionRate c * |x|))) := by
      rw [hsplit]
    _ = C * Real.exp (-(lemma77ScalarLowRegionRate c * (1 + (s' : ℝ)))) *
        Real.exp (-(lemma77ScalarLowRegionRate c *
          |lemma77ScalarCenteredHorizontal j s'|)) := by
      simp [x, S]
      ring

/--
Positive-index low-region linear branch bounded by the common low
height-horizontal profile.
-/
theorem lemma77ScalarLowRegion_linearKernel_le_exp_profile
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    {j : ℤ} {n s' : ℕ} (hn : 0 < n)
    (hlow : lemma77ScalarLowRegion n s') :
    C * lemma77LocalLimitPrefactor n *
      Real.exp (-Real.sqrt
        ((c * (lemma77ScalarCenteredHorizontal j s' -
              lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
          (c * (-lemma77ScalarTimeOffset n s')) ^ 2)) ≤
      C * Real.exp (-(lemma77ScalarLowRegionRate c * (1 + (s' : ℝ)))) *
        Real.exp (-(lemma77ScalarLowRegionRate c *
          |lemma77ScalarCenteredHorizontal j s'|)) := by
  let x := lemma77ScalarCenteredHorizontal j s'
  let u := lemma77ScalarTimeOffset n s'
  let S : ℝ := 1 + (s' : ℝ)
  let A : ℝ := |x| + S
  let R : ℝ := Real.sqrt ((x - u / 4) ^ 2 + u ^ 2)
  have hpref_one : lemma77LocalLimitPrefactor n ≤ 1 :=
    lemma77LocalLimitPrefactor_le_one_of_pos hn
  have hA_nonneg : 0 ≤ A := by
    dsimp [A, S]
    positivity
  have hrho_le : lemma77ScalarLowRegionRate c ≤ c / 8 :=
    lemma77ScalarLowRegionRate_le_c_div_eight c
  have hrad : A / 8 ≤ R := by
    dsimp [A, S, R, x, u]
    exact lemma77ScalarLowRegion_radial_ge_height_horizontal hlow
      (lemma77ScalarCenteredHorizontal j s')
  have hscaled :
      Real.sqrt ((c * (x - u / 4)) ^ 2 + (c * (-u)) ^ 2) = c * R := by
    dsimp [R]
    rw [lemma77ScalarScaledRadial_eq hc]
  have hscale : lemma77ScalarLowRegionRate c * A ≤
      Real.sqrt ((c * (x - u / 4)) ^ 2 + (c * (-u)) ^ 2) := by
    have h1 : lemma77ScalarLowRegionRate c * A ≤ (c / 8) * A := by
      exact mul_le_mul_of_nonneg_right hrho_le hA_nonneg
    have h2 : (c / 8) * A ≤ c * R := by
      nlinarith [mul_le_mul_of_nonneg_left hrad hc.le]
    rw [hscaled]
    exact le_trans h1 h2
  have hexp :
      Real.exp (-Real.sqrt ((c * (x - u / 4)) ^ 2 + (c * (-u)) ^ 2)) ≤
        Real.exp (-(lemma77ScalarLowRegionRate c * A)) := by
    rw [Real.exp_le_exp]
    linarith
  have hbase :
      lemma77LocalLimitPrefactor n *
        Real.exp (-Real.sqrt ((c * (x - u / 4)) ^ 2 +
          (c * (-u)) ^ 2)) ≤
        Real.exp (-(lemma77ScalarLowRegionRate c * A)) := by
    calc
      lemma77LocalLimitPrefactor n *
          Real.exp (-Real.sqrt ((c * (x - u / 4)) ^ 2 +
            (c * (-u)) ^ 2))
          ≤ 1 * Real.exp (-(lemma77ScalarLowRegionRate c * A)) := by
            exact mul_le_mul hpref_one hexp (le_of_lt (Real.exp_pos _))
              (by positivity)
      _ = Real.exp (-(lemma77ScalarLowRegionRate c * A)) := by
        ring
  have hsplit :
      Real.exp (-(lemma77ScalarLowRegionRate c * A)) =
        Real.exp (-(lemma77ScalarLowRegionRate c * S)) *
          Real.exp (-(lemma77ScalarLowRegionRate c * |x|)) := by
    dsimp [A]
    rw [← Real.exp_add]
    ring_nf
  calc
    C * lemma77LocalLimitPrefactor n *
      Real.exp (-Real.sqrt
        ((c * (lemma77ScalarCenteredHorizontal j s' -
              lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
          (c * (-lemma77ScalarTimeOffset n s')) ^ 2))
        = C * (lemma77LocalLimitPrefactor n *
          Real.exp (-Real.sqrt ((c * (x - u / 4)) ^ 2 +
            (c * (-u)) ^ 2))) := by
          simp [x, u]
          ring
    _ ≤ C * Real.exp (-(lemma77ScalarLowRegionRate c * A)) :=
      mul_le_mul_of_nonneg_left hbase hC
    _ = C * (Real.exp (-(lemma77ScalarLowRegionRate c * S)) *
          Real.exp (-(lemma77ScalarLowRegionRate c * |x|))) := by
      rw [hsplit]
    _ = C * Real.exp (-(lemma77ScalarLowRegionRate c * (1 + (s' : ℝ)))) *
        Real.exp (-(lemma77ScalarLowRegionRate c *
          |lemma77ScalarCenteredHorizontal j s'|)) := by
      simp [x, S]
      ring

/-- Positive-index low-region full `G_n` kernel profile bound. -/
theorem lemma77ScalarLowRegion_posKernel_le_exp_profile
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    {j : ℤ} {n s' : ℕ} (hn : 0 < n)
    (hlow : lemma77ScalarLowRegion n s') :
    lemma77HoldPrefixLocalLimitKernel C c n j (s' : ℤ) ≤
      (2 * C) *
        Real.exp (-(lemma77ScalarLowRegionRate c * (1 + (s' : ℝ)))) *
        Real.exp (-(lemma77ScalarLowRegionRate c *
          |lemma77ScalarCenteredHorizontal j s'|)) := by
  have hquad :=
    lemma77ScalarLowRegion_quadraticKernel_le_exp_profile
      hC hc hn hlow (j := j)
  have hlin :=
    lemma77ScalarLowRegion_linearKernel_le_exp_profile
      hC hc hn hlow (j := j)
  rw [lemma77HoldPrefixLocalLimitKernel_eq_lowRegionPositiveBranches
    C c hlow hn j]
  calc
    C * lemma77LocalLimitPrefactor n *
        Real.exp (-(((c * (lemma77ScalarCenteredHorizontal j s' -
                lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
              (c * (-lemma77ScalarTimeOffset n s')) ^ 2) / (n : ℝ))) +
      C * lemma77LocalLimitPrefactor n *
        Real.exp (-Real.sqrt
          ((c * (lemma77ScalarCenteredHorizontal j s' -
                lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
            (c * (-lemma77ScalarTimeOffset n s')) ^ 2))
        ≤
      C * Real.exp (-(lemma77ScalarLowRegionRate c * (1 + (s' : ℝ)))) *
          Real.exp (-(lemma77ScalarLowRegionRate c *
            |lemma77ScalarCenteredHorizontal j s'|)) +
        C * Real.exp (-(lemma77ScalarLowRegionRate c * (1 + (s' : ℝ)))) *
          Real.exp (-(lemma77ScalarLowRegionRate c *
            |lemma77ScalarCenteredHorizontal j s'|)) :=
      add_le_add hquad hlin
    _ = (2 * C) *
        Real.exp (-(lemma77ScalarLowRegionRate c * (1 + (s' : ℝ)))) *
        Real.exp (-(lemma77ScalarLowRegionRate c *
          |lemma77ScalarCenteredHorizontal j s'|)) := by
      ring

/--
Low-region full pointwise profile.  This combines the positive-index two-term
`G_n` branch with the zero-index `G_0` branch, but does not yet sum the finite
low region into the height kernel.
-/
theorem lemma77ScalarLowRegion_kernel_le_exp_profile
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    {j : ℤ} {n s' : ℕ}
    (hlow : lemma77ScalarLowRegion n s') :
    lemma77HoldPrefixLocalLimitKernel C c n j (s' : ℤ) ≤
      (2 * C) *
        Real.exp (-(lemma77ScalarLowRegionRate c * (1 + (s' : ℝ)))) *
        Real.exp (-(lemma77ScalarLowRegionRate c *
          |lemma77ScalarCenteredHorizontal j s'|)) := by
  by_cases hn0 : n = 0
  · subst n
    have hzero :=
      lemma77ScalarLowRegion_zeroKernel_le_exp_profile
        hC hc (j := j) hlow
    have hC_le : C ≤ 2 * C := by
      nlinarith [hC]
    have hprofile_nonneg :
        0 ≤
          Real.exp (-(lemma77ScalarLowRegionRate c * (1 + (s' : ℝ)))) *
            Real.exp (-(lemma77ScalarLowRegionRate c *
              |lemma77ScalarCenteredHorizontal j s'|)) := by
      positivity
    calc
      lemma77HoldPrefixLocalLimitKernel C c 0 j (s' : ℤ)
          ≤ C *
              Real.exp (-(lemma77ScalarLowRegionRate c * (1 + (s' : ℝ)))) *
              Real.exp (-(lemma77ScalarLowRegionRate c *
                |lemma77ScalarCenteredHorizontal j s'|)) := hzero
      _ = C *
          (Real.exp (-(lemma77ScalarLowRegionRate c * (1 + (s' : ℝ)))) *
            Real.exp (-(lemma77ScalarLowRegionRate c *
              |lemma77ScalarCenteredHorizontal j s'|))) := by
        ring
      _ ≤ (2 * C) *
          (Real.exp (-(lemma77ScalarLowRegionRate c * (1 + (s' : ℝ)))) *
            Real.exp (-(lemma77ScalarLowRegionRate c *
              |lemma77ScalarCenteredHorizontal j s'|))) :=
        mul_le_mul_of_nonneg_right hC_le hprofile_nonneg
      _ = (2 * C) *
          Real.exp (-(lemma77ScalarLowRegionRate c * (1 + (s' : ℝ)))) *
          Real.exp (-(lemma77ScalarLowRegionRate c *
            |lemma77ScalarCenteredHorizontal j s'|)) := by
        ring
  · exact lemma77ScalarLowRegion_posKernel_le_exp_profile
      hC hc (Nat.pos_of_ne_zero hn0) hlow

/-- The model low-region exponential profile is summable by finite support. -/
theorem lemma77ScalarLowRegion_expProfile_summable
    (K rho : ℝ) (j : ℤ) (s' : ℕ) :
    Summable fun n : ℕ =>
      if lemma77ScalarLowRegion n s' then
        K * Real.exp (-(rho * (1 + (s' : ℝ)))) *
          Real.exp (-(rho * |lemma77ScalarCenteredHorizontal j s'|))
      else 0 := by
  let f : ℕ → ℝ := fun n =>
    if lemma77ScalarLowRegion n s' then
      K * Real.exp (-(rho * (1 + (s' : ℝ)))) *
        Real.exp (-(rho * |lemma77ScalarCenteredHorizontal j s'|))
    else 0
  have hsupport : Function.support f ⊆ Set.Iio (s' + 1) := by
    intro n hn
    by_contra hlt
    have hge : s' + 1 ≤ n := Nat.le_of_not_gt hlt
    have hzero : f n = 0 := by
      dsimp [f]
      have hnot := lemma77ScalarLowRegion_not_of_succ_height_le hge
      simp [hnot]
    exact hn hzero
  have hfinite : Function.HasFiniteSupport f :=
    Set.Finite.subset (Set.finite_Iio (s' + 1)) hsupport
  simpa [f] using (summable_of_hasFiniteSupport hfinite : Summable f)

/--
The finite low support contributes at most `s' + 1` copies of the common
pointwise profile.
-/
theorem lemma77ScalarLowRegion_expProfile_tsum_le_count
    {K rho : ℝ} (hK : 0 ≤ K) (j : ℤ) (s' : ℕ) :
    (∑' n : ℕ,
      if lemma77ScalarLowRegion n s' then
        K * Real.exp (-(rho * (1 + (s' : ℝ)))) *
          Real.exp (-(rho * |lemma77ScalarCenteredHorizontal j s'|))
      else 0) ≤
      (((s' + 1 : ℕ) : ℝ) * K) *
        Real.exp (-(rho * (1 + (s' : ℝ)))) *
        Real.exp (-(rho * |lemma77ScalarCenteredHorizontal j s'|)) := by
  let B : ℝ := K * Real.exp (-(rho * (1 + (s' : ℝ)))) *
    Real.exp (-(rho * |lemma77ScalarCenteredHorizontal j s'|))
  have hB : 0 ≤ B := by
    dsimp [B]
    positivity
  have htsum_eq :
      (∑' n : ℕ,
        if lemma77ScalarLowRegion n s' then B else 0) =
        ∑ n ∈ Finset.range (s' + 1),
          if lemma77ScalarLowRegion n s' then B else 0 := by
    refine tsum_eq_sum ?_
    intro n hn
    have hn_not_lt : ¬ n < s' + 1 := by
      simpa [Finset.mem_range] using hn
    have hge : s' + 1 ≤ n := Nat.le_of_not_gt hn_not_lt
    have hnot := lemma77ScalarLowRegion_not_of_succ_height_le hge
    simp [hnot]
  have hsum_le :
      (∑ n ∈ Finset.range (s' + 1),
          if lemma77ScalarLowRegion n s' then B else 0) ≤
        ∑ n ∈ Finset.range (s' + 1), B := by
    apply Finset.sum_le_sum
    intro n _hn
    by_cases hlow : lemma77ScalarLowRegion n s'
    · simp [hlow]
    · simp [hlow, hB]
  calc
    (∑' n : ℕ,
      if lemma77ScalarLowRegion n s' then
        K * Real.exp (-(rho * (1 + (s' : ℝ)))) *
          Real.exp (-(rho * |lemma77ScalarCenteredHorizontal j s'|))
      else 0)
        = ∑' n : ℕ, if lemma77ScalarLowRegion n s' then B else 0 := by
          simp [B]
    _ = ∑ n ∈ Finset.range (s' + 1),
          if lemma77ScalarLowRegion n s' then B else 0 := htsum_eq
    _ ≤ ∑ n ∈ Finset.range (s' + 1), B := hsum_le
    _ = (((s' + 1 : ℕ) : ℝ) * K) *
        Real.exp (-(rho * (1 + (s' : ℝ)))) *
        Real.exp (-(rho * |lemma77ScalarCenteredHorizontal j s'|)) := by
      simp [B, nsmul_eq_mul]
      ring

/--
Finite-support low-region `tsum` bound from any supplied pointwise exponential
profile.
-/
theorem lemma77ScalarLowRegion_filteredKernel_tsum_le_exp_profile
    {C c K rho : ℝ} (hK : 0 ≤ K)
    (hpoint :
      ∀ {j : ℤ} {n s' : ℕ},
        lemma77ScalarLowRegion n s' →
          lemma77HoldPrefixLocalLimitKernel C c n j (s' : ℤ) ≤
            K * Real.exp (-(rho * (1 + (s' : ℝ)))) *
              Real.exp (-(rho * |lemma77ScalarCenteredHorizontal j s'|)))
    (j : ℤ) (s' : ℕ) :
    (∑' n : ℕ,
      if lemma77ScalarLowRegion n s' then
        lemma77HoldPrefixLocalLimitKernel C c n j (s' : ℤ)
      else 0) ≤
      (((s' + 1 : ℕ) : ℝ) * K) *
        Real.exp (-(rho * (1 + (s' : ℝ)))) *
        Real.exp (-(rho * |lemma77ScalarCenteredHorizontal j s'|)) := by
  have hleft_summable :
      Summable fun n : ℕ =>
        if lemma77ScalarLowRegion n s' then
          lemma77HoldPrefixLocalLimitKernel C c n j (s' : ℤ)
        else 0 :=
    lemma77ScalarLowRegion_filteredKernel_summable_of_finite_support C c j s'
  have hright_summable :
      Summable fun n : ℕ =>
        if lemma77ScalarLowRegion n s' then
          K * Real.exp (-(rho * (1 + (s' : ℝ)))) *
            Real.exp (-(rho * |lemma77ScalarCenteredHorizontal j s'|))
        else 0 :=
    lemma77ScalarLowRegion_expProfile_summable K rho j s'
  have hle : ∀ n : ℕ,
      (if lemma77ScalarLowRegion n s' then
        lemma77HoldPrefixLocalLimitKernel C c n j (s' : ℤ)
      else 0) ≤
      (if lemma77ScalarLowRegion n s' then
        K * Real.exp (-(rho * (1 + (s' : ℝ)))) *
          Real.exp (-(rho * |lemma77ScalarCenteredHorizontal j s'|))
      else 0) := by
    intro n
    by_cases hlow : lemma77ScalarLowRegion n s'
    · simp [hlow, hpoint hlow]
    · simp [hlow]
  have htsum := hleft_summable.tsum_le_tsum hle hright_summable
  exact le_trans htsum
    (lemma77ScalarLowRegion_expProfile_tsum_le_count hK j s')

/-- The middle-region count prefactor `S⁻¹ * sqrt S` is exactly the
height-potential prefactor. -/
theorem lemma77_one_add_inv_mul_sqrt_eq_rpow_neg_half
    (s' : ℕ) :
    ((1 + (s' : ℝ))⁻¹) * Real.sqrt (1 + (s' : ℝ)) =
      (1 + (s' : ℝ)) ^ (-(1 / 2 : ℝ)) := by
  let S : ℝ := 1 + (s' : ℝ)
  have hS_pos : 0 < S := by
    dsimp [S]
    positivity
  have hS_nonneg : 0 ≤ S := hS_pos.le
  have hsqrt_pos : 0 < Real.sqrt S := Real.sqrt_pos.2 hS_pos
  rw [show 1 + (s' : ℝ) = S by rfl]
  rw [Real.rpow_neg hS_nonneg]
  rw [← Real.sqrt_eq_rpow]
  have hsqrt_sq : (Real.sqrt S) ^ 2 = S := Real.sq_sqrt hS_nonneg
  field_simp [hS_pos.ne', hsqrt_pos.ne']
  nlinarith

/-- The middle-region linear count prefactor is bounded by the height-potential
prefactor. -/
theorem lemma77_one_add_inv_le_rpow_neg_half
    (s' : ℕ) :
    (1 + (s' : ℝ))⁻¹ ≤
      (1 + (s' : ℝ)) ^ (-(1 / 2 : ℝ)) := by
  let S : ℝ := 1 + (s' : ℝ)
  have hS_pos : 0 < S := by
    dsimp [S]
    positivity
  have hS_nonneg : 0 ≤ S := hS_pos.le
  have hS_ge_one : 1 ≤ S := by
    dsimp [S]
    exact le_add_of_nonneg_right (Nat.cast_nonneg s')
  have hsqrt_le_self : Real.sqrt S ≤ S := by
    rw [Real.sqrt_le_left hS_nonneg]
    nlinarith [hS_ge_one]
  rw [show 1 + (s' : ℝ) = S by rfl]
  rw [Real.rpow_neg hS_nonneg]
  rw [← Real.sqrt_eq_rpow]
  exact (inv_le_inv₀ hS_pos (Real.sqrt_pos.2 hS_pos)).mpr
    hsqrt_le_self

/--
Uniform height-tail absorption for the finite low support count.

The left side is the `s' + 1` cardinality factor times the low target-height
exponential profile.  The right side has the height-potential prefactor.
-/
theorem lemma77_one_add_mul_exp_neg_le_rpow_neg_half
    {rho : ℝ} (hrho : 0 < rho) (s' : ℕ) :
    (1 + (s' : ℝ)) * Real.exp (-(rho * (1 + (s' : ℝ)))) ≤
      ((2 * Real.exp (-1)) / rho) ^ 2 *
        ((1 + (s' : ℝ)) ^ (-(1 / 2 : ℝ))) := by
  let S : ℝ := 1 + (s' : ℝ)
  let a : ℝ := rho / 2
  have hS_pos : 0 < S := by
    dsimp [S]
    positivity
  have hS_nonneg : 0 ≤ S := hS_pos.le
  have hS_ge_one : 1 ≤ S := by
    dsimp [S]
    exact le_add_of_nonneg_right (Nat.cast_nonneg s')
  have ha_pos : 0 < a := by
    dsimp [a]
    positivity
  have haS_pos : 0 < a * S := mul_pos ha_pos hS_pos
  have hmul := Real.mul_exp_neg_le_exp_neg_one (a * S)
  have hSexp : S * Real.exp (-(a * S)) ≤ Real.exp (-1) / a := by
    calc
      S * Real.exp (-(a * S))
          = ((a * S) * Real.exp (-(a * S))) / a := by
        field_simp [ha_pos.ne']
      _ ≤ Real.exp (-1) / a := div_le_div_of_nonneg_right hmul ha_pos.le
  have hexp : Real.exp (-(a * S)) ≤ Real.exp (-1) / (a * S) := by
    calc
      Real.exp (-(a * S))
          = ((a * S) * Real.exp (-(a * S))) / (a * S) := by
        field_simp [haS_pos.ne']
      _ ≤ Real.exp (-1) / (a * S) :=
        div_le_div_of_nonneg_right hmul haS_pos.le
  have hsplit : Real.exp (-(rho * S)) =
      Real.exp (-(a * S)) * Real.exp (-(a * S)) := by
    rw [← Real.exp_add]
    dsimp [a]
    congr 1
    ring
  have hsqrt_le_self : Real.sqrt S ≤ S := by
    rw [Real.sqrt_le_left hS_nonneg]
    nlinarith [hS_ge_one]
  have hSinv_le : S⁻¹ ≤ S ^ (-(1 / 2 : ℝ)) := by
    simpa [S] using lemma77_one_add_inv_le_rpow_neg_half s'
  calc
    (1 + (s' : ℝ)) * Real.exp (-(rho * (1 + (s' : ℝ))))
        = S * Real.exp (-(rho * S)) := by
          simp [S]
    _ = (S * Real.exp (-(a * S))) * Real.exp (-(a * S)) := by
      rw [hsplit]
      ring
    _ ≤ (Real.exp (-1) / a) * (Real.exp (-1) / (a * S)) := by
      exact mul_le_mul hSexp hexp (le_of_lt (Real.exp_pos _))
        (by positivity)
    _ = ((2 * Real.exp (-1)) / rho) ^ 2 * S⁻¹ := by
      dsimp [a]
      field_simp [hrho.ne', hS_pos.ne']
    _ ≤ ((2 * Real.exp (-1)) / rho) ^ 2 *
        (S ^ (-(1 / 2 : ℝ))) := by
      exact mul_le_mul_of_nonneg_left hSinv_le (sq_nonneg _)
    _ = ((2 * Real.exp (-1)) / rho) ^ 2 *
        ((1 + (s' : ℝ)) ^ (-(1 / 2 : ℝ))) := by
      simp [S]

/--
The product-tail term is bounded by the pure exponential tail.

This is only a summability pilot; it deliberately drops the `x`-decay and is
not the product-tail estimate needed for the scalar height-potential theorem.
-/
theorem lemma77ScalarProductTailTerm_le_exp_neg
    {a : ℝ} (ha : 0 ≤ a) (x : ℝ) (n : ℕ) :
    lemma77ScalarProductTailTerm a x n ≤ Real.exp (-(a * (n : ℝ))) := by
  unfold lemma77ScalarProductTailTerm
  by_cases hn : n = 0
  · simp [hn]
  · have hn_nat_pos : 0 < n := Nat.pos_of_ne_zero hn
    have hden_pos : 0 < (n : ℝ) := by
      exact_mod_cast hn_nat_pos
    have hden_one : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn_nat_pos
    have hquad_nonneg :
        0 ≤ a * (x ^ 2 / (n : ℝ)) := by
      exact mul_nonneg ha (div_nonneg (sq_nonneg x) hden_pos.le)
    have hexp_le :
        Real.exp (-(a * (n : ℝ)) - a * (x ^ 2 / (n : ℝ))) ≤
          Real.exp (-(a * (n : ℝ))) := by
      rw [Real.exp_le_exp]
      nlinarith
    simp [hn]
    calc
      Real.exp (-(a * (n : ℝ)) - a * (x ^ 2 / (n : ℝ))) /
          (n : ℝ)
          ≤ Real.exp (-(a * (n : ℝ))) / (n : ℝ) := by
            exact div_le_div_of_nonneg_right hexp_le hden_pos.le
      _ ≤ Real.exp (-(a * (n : ℝ))) := by
        rw [div_le_iff₀ hden_pos]
        nlinarith [le_of_lt (Real.exp_pos (-(a * (n : ℝ))))]

/-- The positive-index product-tail term is summable for positive rate. -/
theorem lemma77ScalarProductTailTerm_summable
    {a : ℝ} (ha : 0 < a) (x : ℝ) :
    Summable fun n : ℕ => lemma77ScalarProductTailTerm a x n := by
  exact Summable.of_nonneg_of_le
    (fun n => lemma77ScalarProductTailTerm_nonneg a x n)
    (fun n => lemma77ScalarProductTailTerm_le_exp_neg ha.le x n)
    (lemma77ExpNegMulNat_summable ha)

/-- `tsum` side of the isolated scalar product-tail target. -/
def lemma77ScalarProductTailTsum (a x : ℝ) : ℝ :=
  ∑' n : ℕ, lemma77ScalarProductTailTerm a x n

/-- Source-facing decay rate for the product-tail target. -/
def lemma77ScalarProductTailRate (a : ℝ) : ℝ :=
  a / 2

/-- Explicit constant proposed for the product-tail target. -/
def lemma77ScalarProductTailConstant (a : ℝ) : ℝ :=
  (1 - Real.exp (-(a / 2)))⁻¹

/-- The product-tail geometric constant is nonnegative for positive rate. -/
theorem lemma77ScalarProductTailConstant_nonneg
    {a : ℝ} (ha : 0 < a) :
    0 ≤ lemma77ScalarProductTailConstant a := by
  unfold lemma77ScalarProductTailConstant
  have hbase_lt : Real.exp (-(a / 2)) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith
  have hpos : 0 < 1 - Real.exp (-(a / 2)) := by
    linarith
  exact inv_nonneg.mpr hpos.le

/-- Deterministic core inequality for product-tail horizontal decay. -/
theorem lemma77_abs_add_half_le_self_add_sq_div
    (x t : ℝ) (ht : 0 < t) :
    |x| + t / 2 ≤ t + x ^ 2 / t := by
  have hsq : 0 ≤ (t - |x|) ^ 2 := sq_nonneg _
  have hsabs : |x| ^ 2 = x ^ 2 := by
    simp [sq_abs]
  have ht_nonneg : 0 ≤ t := le_of_lt ht
  field_simp [ht.ne']
  nlinarith [hsq, hsabs, abs_nonneg x, ht_nonneg]

/--
Pointwise product-tail domination retaining the horizontal `|x|` decay.

This is the isolated analytic inequality needed before the later high-region
scalar summation consumes the product-tail input.
-/
theorem lemma77ScalarProductTailTerm_le_exp_abs_mul_exp_half
    {a : ℝ} (ha : 0 < a) (x : ℝ) (n : ℕ) :
    lemma77ScalarProductTailTerm a x n ≤
      Real.exp (-(a * |x|)) *
        Real.exp (-((a / 2) * (n : ℝ))) := by
  by_cases hn : n = 0
  · have hnonneg :
        0 ≤ Real.exp (-(a * |x|)) *
          Real.exp (-((a / 2) * (n : ℝ))) :=
      mul_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt (Real.exp_pos _))
    simpa [lemma77ScalarProductTailTerm, hn] using hnonneg
  · have hn_nat_pos : 0 < n := Nat.pos_of_ne_zero hn
    have hden_pos : 0 < (n : ℝ) := by
      exact_mod_cast hn_nat_pos
    have hden_one : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn_nat_pos
    have hcore :
        |x| + (n : ℝ) / 2 ≤ (n : ℝ) + x ^ 2 / (n : ℝ) :=
      lemma77_abs_add_half_le_self_add_sq_div x (n : ℝ) hden_pos
    have hscaled := mul_le_mul_of_nonneg_left hcore ha.le
    have hexp_le :
        Real.exp (-(a * (n : ℝ)) - a * (x ^ 2 / (n : ℝ))) ≤
          Real.exp (-(a * |x|)) *
            Real.exp (-((a / 2) * (n : ℝ))) := by
      rw [← Real.exp_add, Real.exp_le_exp]
      nlinarith
    rw [lemma77ScalarProductTailTerm, ite_eq_right hn]
    calc
      Real.exp (-(a * (n : ℝ)) - a * (x ^ 2 / (n : ℝ))) / (n : ℝ)
          ≤ Real.exp (-(a * (n : ℝ)) - a * (x ^ 2 / (n : ℝ))) := by
            rw [div_le_iff₀ hden_pos]
            nlinarith [hden_one,
              le_of_lt
                (Real.exp_pos
                  (-(a * (n : ℝ)) - a * (x ^ 2 / (n : ℝ))))]
      _ ≤ Real.exp (-(a * |x|)) *
            Real.exp (-((a / 2) * (n : ℝ))) :=
        hexp_le

/-- Geometric `tsum` value for the product-tail profile. -/
theorem lemma77ScalarProductTailProfile_tsum
    {a : ℝ} (ha : 0 < a) :
    (∑' n : ℕ, Real.exp (-((a / 2) * (n : ℝ)))) =
      (1 - Real.exp (-(a / 2)))⁻¹ := by
  have hbase_nonneg : 0 ≤ Real.exp (-(a / 2)) := le_of_lt (Real.exp_pos _)
  have hbase_lt : Real.exp (-(a / 2)) < 1 := by
    rw [Real.exp_lt_one_iff]
    nlinarith
  rw [← tsum_geometric_of_lt_one hbase_nonneg hbase_lt]
  apply tsum_congr
  intro n
  rw [← Real.exp_nat_mul]
  congr 1
  ring

/-- The isolated product-tail `tsum` has strong exponential decay in `|x|`. -/
theorem lemma77ScalarProductTailTsum_le_exp_abs_strong
    {a : ℝ} (ha : 0 < a) (x : ℝ) :
    lemma77ScalarProductTailTsum a x ≤
      lemma77ScalarProductTailConstant a *
        Real.exp (-(a * |x|)) := by
  have hhalf : 0 < a / 2 := by positivity
  have hright_summable :
      Summable fun n : ℕ =>
        Real.exp (-(a * |x|)) *
          Real.exp (-((a / 2) * (n : ℝ))) := by
    exact (lemma77ExpNegMulNat_summable hhalf).mul_left _
  have hle := (lemma77ScalarProductTailTerm_summable ha x).tsum_le_tsum
    (fun n => lemma77ScalarProductTailTerm_le_exp_abs_mul_exp_half ha x n)
    hright_summable
  calc
    lemma77ScalarProductTailTsum a x
        ≤ ∑' n : ℕ,
            Real.exp (-(a * |x|)) *
              Real.exp (-((a / 2) * (n : ℝ))) := hle
    _ = Real.exp (-(a * |x|)) *
          (∑' n : ℕ, Real.exp (-((a / 2) * (n : ℝ)))) := by
          exact tsum_mul_left
    _ = Real.exp (-(a * |x|)) *
          lemma77ScalarProductTailConstant a := by
          rw [lemma77ScalarProductTailProfile_tsum ha,
            lemma77ScalarProductTailConstant]
    _ = lemma77ScalarProductTailConstant a *
          Real.exp (-(a * |x|)) := by
          ring

/-- The isolated product-tail `tsum` has the packaged exponential decay rate. -/
theorem lemma77ScalarProductTailTsum_le_exp_abs
    {a : ℝ} (ha : 0 < a) (x : ℝ) :
    lemma77ScalarProductTailTsum a x ≤
      lemma77ScalarProductTailConstant a *
        Real.exp (-(lemma77ScalarProductTailRate a) * |x|) := by
  have hprofile :
      Real.exp (-(a * |x|)) ≤
        Real.exp (-(lemma77ScalarProductTailRate a) * |x|) := by
    rw [Real.exp_le_exp, lemma77ScalarProductTailRate]
    nlinarith [ha.le, abs_nonneg x]
  exact le_trans (lemma77ScalarProductTailTsum_le_exp_abs_strong ha x)
    (mul_le_mul_of_nonneg_left hprofile
      (lemma77ScalarProductTailConstant_nonneg ha))

/--
Input surface for the hard scalar product-tail estimate.

This names the analytic estimate that should be proved before the full
central/low/high scalar summation consumes it.
-/
structure Lemma77ScalarProductTailInput (a Cprod : ℝ) : Prop where
  constants : 0 < a ∧ 0 ≤ Cprod
  term_summable :
    ∀ x,
      Summable fun n : ℕ => lemma77ScalarProductTailTerm a x n
  tsum_bound :
    ∀ x,
      lemma77ScalarProductTailTsum a x ≤
        Cprod * Real.exp (-(lemma77ScalarProductTailRate a) * |x|)

/-- Explicit product-tail input from the checked pointwise profile estimate. -/
theorem lemma77ScalarProductTailInput_explicit
    {a : ℝ} (ha : 0 < a) :
    Lemma77ScalarProductTailInput a (lemma77ScalarProductTailConstant a) where
  constants := by
    constructor
    · exact ha
    · exact lemma77ScalarProductTailConstant_nonneg ha
  term_summable := by
    intro x
    exact lemma77ScalarProductTailTerm_summable ha x
  tsum_bound := by
    intro x
    exact lemma77ScalarProductTailTsum_le_exp_abs ha x

/--
Filtered high-region contribution of the quadratic/Gaussian branch.

This sums only the high-region quadratic branch and consumes an abstract
product-tail input.  It is still not the full high-region slice, because the
linear branch is summed separately.
-/
theorem lemma77ScalarHighRegion_quadraticContribution_le_exp
    {C c Cprod : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (hprod : Lemma77ScalarProductTailInput ((c ^ 2) / 4) Cprod)
    (j : ℤ) (s' : ℕ) :
    (∑' n : ℕ,
      if lemma77ScalarHighRegion n s' then
        C * lemma77LocalLimitPrefactor n *
          Real.exp (-(((c * (lemma77ScalarCenteredHorizontal j s' -
                  lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
                (c * (-lemma77ScalarTimeOffset n s')) ^ 2) / (n : ℝ)))
      else 0) ≤
      (C * ((8 * Real.exp (-1)) / ((c ^ 2) / 4)) * Cprod) *
        ((1 + (s' : ℝ)) ^ (-(1 / 2 : ℝ))) *
        Real.exp (-(lemma77ScalarProductTailRate ((c ^ 2) / 4)) *
          |lemma77ScalarCenteredHorizontal j s'|) := by
  let x := lemma77ScalarCenteredHorizontal j s'
  let a := (c ^ 2) / 4
  let height := (1 + (s' : ℝ)) ^ (-(1 / 2 : ℝ))
  let K := (C * ((8 * Real.exp (-1)) / a)) * height
  have hK_nonneg : 0 ≤ K := by
    dsimp [K, a, height]
    positivity
  have hleft_nonneg :
      ∀ n : ℕ,
        0 ≤ if lemma77ScalarHighRegion n s' then
          C * lemma77LocalLimitPrefactor n *
            Real.exp (-(((c * (lemma77ScalarCenteredHorizontal j s' -
                    lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
                  (c * (-lemma77ScalarTimeOffset n s')) ^ 2) / (n : ℝ)))
        else 0 := by
    intro n
    by_cases hhigh : lemma77ScalarHighRegion n s'
    · have hpref_nonneg : 0 ≤ lemma77LocalLimitPrefactor n := by
        unfold lemma77LocalLimitPrefactor
        positivity
      simp [hhigh]
      exact mul_nonneg (mul_nonneg hC hpref_nonneg)
        (le_of_lt (Real.exp_pos _))
    · simp [hhigh]
  have hle :
      ∀ n : ℕ,
        (if lemma77ScalarHighRegion n s' then
          C * lemma77LocalLimitPrefactor n *
            Real.exp (-(((c * (lemma77ScalarCenteredHorizontal j s' -
                    lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
                  (c * (-lemma77ScalarTimeOffset n s')) ^ 2) / (n : ℝ)))
        else 0) ≤ K * lemma77ScalarProductTailTerm a x n := by
    intro n
    by_cases hhigh : lemma77ScalarHighRegion n s'
    · have hpoint :=
        lemma77ScalarHighRegion_gaussianKernel_le_prefactor_mul_productTailTerm
          hC hc (j := j) (n := n) (s' := s') hhigh
      simpa [hhigh, K, a, height, x, mul_assoc] using hpoint
    · have htail_nonneg : 0 ≤ lemma77ScalarProductTailTerm a x n :=
        lemma77ScalarProductTailTerm_nonneg a x n
      have hright_nonneg : 0 ≤ K * lemma77ScalarProductTailTerm a x n :=
        mul_nonneg hK_nonneg htail_nonneg
      simpa [hhigh] using hright_nonneg
  have hright_summable :
      Summable fun n : ℕ => K * lemma77ScalarProductTailTerm a x n :=
    (hprod.term_summable x).mul_left K
  have hleft_summable :
      Summable fun n : ℕ =>
        if lemma77ScalarHighRegion n s' then
          C * lemma77LocalLimitPrefactor n *
            Real.exp (-(((c * (lemma77ScalarCenteredHorizontal j s' -
                    lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
                  (c * (-lemma77ScalarTimeOffset n s')) ^ 2) / (n : ℝ)))
        else 0 :=
    Summable.of_nonneg_of_le hleft_nonneg hle hright_summable
  have htsum := hleft_summable.tsum_le_tsum hle hright_summable
  have hprod_bound := hprod.tsum_bound x
  calc
    (∑' n : ℕ,
      if lemma77ScalarHighRegion n s' then
        C * lemma77LocalLimitPrefactor n *
          Real.exp (-(((c * (lemma77ScalarCenteredHorizontal j s' -
                  lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
                (c * (-lemma77ScalarTimeOffset n s')) ^ 2) / (n : ℝ)))
      else 0)
        ≤ ∑' n : ℕ, K * lemma77ScalarProductTailTerm a x n := htsum
    _ = K * lemma77ScalarProductTailTsum a x := by
        rw [lemma77ScalarProductTailTsum]
        exact tsum_mul_left
    _ ≤ K * (Cprod * Real.exp (-(lemma77ScalarProductTailRate a) * |x|)) :=
        mul_le_mul_of_nonneg_left hprod_bound hK_nonneg
    _ = (C * ((8 * Real.exp (-1)) / ((c ^ 2) / 4)) * Cprod) *
        ((1 + (s' : ℝ)) ^ (-(1 / 2 : ℝ))) *
        Real.exp (-(lemma77ScalarProductTailRate ((c ^ 2) / 4)) *
          |lemma77ScalarCenteredHorizontal j s'|) := by
        simp [K, a, height, x]
        ring

/--
Explicit high-region quadratic contribution using the checked product-tail
constant.
-/
theorem lemma77ScalarHighRegion_quadraticContribution_le_explicit
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (j : ℤ) (s' : ℕ) :
    (∑' n : ℕ,
      if lemma77ScalarHighRegion n s' then
        C * lemma77LocalLimitPrefactor n *
          Real.exp (-(((c * (lemma77ScalarCenteredHorizontal j s' -
                  lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
                (c * (-lemma77ScalarTimeOffset n s')) ^ 2) / (n : ℝ)))
      else 0) ≤
      (C * ((8 * Real.exp (-1)) / ((c ^ 2) / 4)) *
        lemma77ScalarProductTailConstant ((c ^ 2) / 4)) *
        ((1 + (s' : ℝ)) ^ (-(1 / 2 : ℝ))) *
        Real.exp (-(lemma77ScalarProductTailRate ((c ^ 2) / 4)) *
          |lemma77ScalarCenteredHorizontal j s'|) :=
  lemma77ScalarHighRegion_quadraticContribution_le_exp hC hc
    (lemma77ScalarProductTailInput_explicit (a := (c ^ 2) / 4) (by positivity))
    j s'

/-- Summability of the filtered high-region quadratic contribution. -/
theorem lemma77ScalarHighRegion_quadraticContribution_summable
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (j : ℤ) (s' : ℕ) :
    Summable fun n : ℕ =>
      if lemma77ScalarHighRegion n s' then
        C * lemma77LocalLimitPrefactor n *
          Real.exp (-(((c * (lemma77ScalarCenteredHorizontal j s' -
                  lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
                (c * (-lemma77ScalarTimeOffset n s')) ^ 2) / (n : ℝ)))
      else 0 := by
  let x := lemma77ScalarCenteredHorizontal j s'
  let a := (c ^ 2) / 4
  let height := (1 + (s' : ℝ)) ^ (-(1 / 2 : ℝ))
  let K := (C * ((8 * Real.exp (-1)) / a)) * height
  have hK_nonneg : 0 ≤ K := by
    dsimp [K, a, height]
    positivity
  have hprod :
      Lemma77ScalarProductTailInput a (lemma77ScalarProductTailConstant a) :=
    lemma77ScalarProductTailInput_explicit (a := a) (by positivity)
  have hleft_nonneg :
      ∀ n : ℕ,
        0 ≤ if lemma77ScalarHighRegion n s' then
          C * lemma77LocalLimitPrefactor n *
            Real.exp (-(((c * (lemma77ScalarCenteredHorizontal j s' -
                    lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
                  (c * (-lemma77ScalarTimeOffset n s')) ^ 2) / (n : ℝ)))
        else 0 := by
    intro n
    by_cases hhigh : lemma77ScalarHighRegion n s'
    · have hpref_nonneg : 0 ≤ lemma77LocalLimitPrefactor n := by
        unfold lemma77LocalLimitPrefactor
        positivity
      simp [hhigh]
      exact mul_nonneg (mul_nonneg hC hpref_nonneg)
        (le_of_lt (Real.exp_pos _))
    · simp [hhigh]
  have hle :
      ∀ n : ℕ,
        (if lemma77ScalarHighRegion n s' then
          C * lemma77LocalLimitPrefactor n *
            Real.exp (-(((c * (lemma77ScalarCenteredHorizontal j s' -
                    lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
                  (c * (-lemma77ScalarTimeOffset n s')) ^ 2) / (n : ℝ)))
        else 0) ≤ K * lemma77ScalarProductTailTerm a x n := by
    intro n
    by_cases hhigh : lemma77ScalarHighRegion n s'
    · have hpoint :=
        lemma77ScalarHighRegion_gaussianKernel_le_prefactor_mul_productTailTerm
          hC hc (j := j) (n := n) (s' := s') hhigh
      simpa [hhigh, K, a, height, x, mul_assoc] using hpoint
    · have htail_nonneg : 0 ≤ lemma77ScalarProductTailTerm a x n :=
        lemma77ScalarProductTailTerm_nonneg a x n
      have hright_nonneg : 0 ≤ K * lemma77ScalarProductTailTerm a x n :=
        mul_nonneg hK_nonneg htail_nonneg
      simpa [hhigh] using hright_nonneg
  exact Summable.of_nonneg_of_le hleft_nonneg hle
    ((hprod.term_summable x).mul_left K)

/--
Filtered high-region contribution of the linear branch.

This uses the actual scaled radial `G_n` linear term and sums the remaining
pure exponential high-time tail.
-/
theorem lemma77ScalarHighRegion_linearContribution_le_exp
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (j : ℤ) (s' : ℕ) :
    (∑' n : ℕ,
      if lemma77ScalarHighRegion n s' then
        C * lemma77LocalLimitPrefactor n *
          Real.exp (-Real.sqrt
            ((c * (lemma77ScalarCenteredHorizontal j s' -
                  lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
              (c * (-lemma77ScalarTimeOffset n s')) ^ 2))
      else 0) ≤
      (C * ((8 * Real.exp (-1)) / c) *
        (1 - Real.exp (-c))⁻¹) *
        ((1 + (s' : ℝ)) ^ (-(1 / 2 : ℝ))) *
        Real.exp (-((c / 4) * |lemma77ScalarCenteredHorizontal j s'|)) := by
  let x := lemma77ScalarCenteredHorizontal j s'
  let height := (1 + (s' : ℝ)) ^ (-(1 / 2 : ℝ))
  let horiz := Real.exp (-((c / 4) * |x|))
  let K := ((C * ((8 * Real.exp (-1)) / c)) * height) * horiz
  have hK_nonneg : 0 ≤ K := by
    dsimp [K, height, horiz]
    positivity
  have hleft_nonneg :
      ∀ n : ℕ,
        0 ≤ if lemma77ScalarHighRegion n s' then
          C * lemma77LocalLimitPrefactor n *
            Real.exp (-Real.sqrt
              ((c * (lemma77ScalarCenteredHorizontal j s' -
                    lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
                (c * (-lemma77ScalarTimeOffset n s')) ^ 2))
        else 0 := by
    intro n
    by_cases hhigh : lemma77ScalarHighRegion n s'
    · have hpref_nonneg : 0 ≤ lemma77LocalLimitPrefactor n := by
        unfold lemma77LocalLimitPrefactor
        positivity
      simp [hhigh]
      exact mul_nonneg (mul_nonneg hC hpref_nonneg)
        (le_of_lt (Real.exp_pos _))
    · simp [hhigh]
  have hle :
      ∀ n : ℕ,
        (if lemma77ScalarHighRegion n s' then
          C * lemma77LocalLimitPrefactor n *
            Real.exp (-Real.sqrt
              ((c * (lemma77ScalarCenteredHorizontal j s' -
                    lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
                (c * (-lemma77ScalarTimeOffset n s')) ^ 2))
        else 0) ≤ K * Real.exp (-(c * (n : ℝ))) := by
    intro n
    by_cases hhigh : lemma77ScalarHighRegion n s'
    · have hpoint :=
        lemma77ScalarHighRegion_linearKernelScaled_le_prefactor_mul_expTail
          hC hc (j := j) (n := n) (s' := s') hhigh
      calc
        (if lemma77ScalarHighRegion n s' then
          C * lemma77LocalLimitPrefactor n *
            Real.exp (-Real.sqrt
              ((c * (lemma77ScalarCenteredHorizontal j s' -
                    lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
                (c * (-lemma77ScalarTimeOffset n s')) ^ 2))
        else 0)
            ≤ (C * ((8 * Real.exp (-1)) / c)) *
                height * Real.exp (-(c * (n : ℝ))) * horiz := by
              simpa [hhigh, height, horiz, x] using hpoint
        _ = K * Real.exp (-(c * (n : ℝ))) := by
              simp [K, height, horiz]
              ring
    · have hright_nonneg : 0 ≤ K * Real.exp (-(c * (n : ℝ))) :=
        mul_nonneg hK_nonneg (le_of_lt (Real.exp_pos _))
      simpa [hhigh] using hright_nonneg
  have hright_summable :
      Summable fun n : ℕ => K * Real.exp (-(c * (n : ℝ))) :=
    (lemma77ExpNegMulNat_summable hc).mul_left K
  have hleft_summable :
      Summable fun n : ℕ =>
        if lemma77ScalarHighRegion n s' then
          C * lemma77LocalLimitPrefactor n *
            Real.exp (-Real.sqrt
              ((c * (lemma77ScalarCenteredHorizontal j s' -
                    lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
                (c * (-lemma77ScalarTimeOffset n s')) ^ 2))
        else 0 :=
    Summable.of_nonneg_of_le hleft_nonneg hle hright_summable
  have htsum := hleft_summable.tsum_le_tsum hle hright_summable
  calc
    (∑' n : ℕ,
      if lemma77ScalarHighRegion n s' then
        C * lemma77LocalLimitPrefactor n *
          Real.exp (-Real.sqrt
            ((c * (lemma77ScalarCenteredHorizontal j s' -
                  lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
              (c * (-lemma77ScalarTimeOffset n s')) ^ 2))
      else 0)
        ≤ ∑' n : ℕ, K * Real.exp (-(c * (n : ℝ))) := htsum
    _ = K * (∑' n : ℕ, Real.exp (-(c * (n : ℝ)))) := by
        exact tsum_mul_left
    _ = K * (1 - Real.exp (-c))⁻¹ := by
        rw [lemma77ExpNegMulNat_tsum hc]
    _ = (C * ((8 * Real.exp (-1)) / c) *
        (1 - Real.exp (-c))⁻¹) *
        ((1 + (s' : ℝ)) ^ (-(1 / 2 : ℝ))) *
        Real.exp (-((c / 4) * |lemma77ScalarCenteredHorizontal j s'|)) := by
        simp [K, height, horiz, x]
        ring

/-- Summability of the filtered high-region linear contribution. -/
theorem lemma77ScalarHighRegion_linearContribution_summable
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (j : ℤ) (s' : ℕ) :
    Summable fun n : ℕ =>
      if lemma77ScalarHighRegion n s' then
        C * lemma77LocalLimitPrefactor n *
          Real.exp (-Real.sqrt
            ((c * (lemma77ScalarCenteredHorizontal j s' -
                  lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
              (c * (-lemma77ScalarTimeOffset n s')) ^ 2))
      else 0 := by
  let x := lemma77ScalarCenteredHorizontal j s'
  let height := (1 + (s' : ℝ)) ^ (-(1 / 2 : ℝ))
  let horiz := Real.exp (-((c / 4) * |x|))
  let K := ((C * ((8 * Real.exp (-1)) / c)) * height) * horiz
  have hK_nonneg : 0 ≤ K := by
    dsimp [K, height, horiz]
    positivity
  have hleft_nonneg :
      ∀ n : ℕ,
        0 ≤ if lemma77ScalarHighRegion n s' then
          C * lemma77LocalLimitPrefactor n *
            Real.exp (-Real.sqrt
              ((c * (lemma77ScalarCenteredHorizontal j s' -
                    lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
                (c * (-lemma77ScalarTimeOffset n s')) ^ 2))
        else 0 := by
    intro n
    by_cases hhigh : lemma77ScalarHighRegion n s'
    · have hpref_nonneg : 0 ≤ lemma77LocalLimitPrefactor n := by
        unfold lemma77LocalLimitPrefactor
        positivity
      simp [hhigh]
      exact mul_nonneg (mul_nonneg hC hpref_nonneg)
        (le_of_lt (Real.exp_pos _))
    · simp [hhigh]
  have hle :
      ∀ n : ℕ,
        (if lemma77ScalarHighRegion n s' then
          C * lemma77LocalLimitPrefactor n *
            Real.exp (-Real.sqrt
              ((c * (lemma77ScalarCenteredHorizontal j s' -
                    lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
                (c * (-lemma77ScalarTimeOffset n s')) ^ 2))
        else 0) ≤ K * Real.exp (-(c * (n : ℝ))) := by
    intro n
    by_cases hhigh : lemma77ScalarHighRegion n s'
    · have hpoint :=
        lemma77ScalarHighRegion_linearKernelScaled_le_prefactor_mul_expTail
          hC hc (j := j) (n := n) (s' := s') hhigh
      calc
        (if lemma77ScalarHighRegion n s' then
          C * lemma77LocalLimitPrefactor n *
            Real.exp (-Real.sqrt
              ((c * (lemma77ScalarCenteredHorizontal j s' -
                    lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
                (c * (-lemma77ScalarTimeOffset n s')) ^ 2))
        else 0)
            ≤ (C * ((8 * Real.exp (-1)) / c)) *
                height * Real.exp (-(c * (n : ℝ))) * horiz := by
              simpa [hhigh, height, horiz, x] using hpoint
        _ = K * Real.exp (-(c * (n : ℝ))) := by
              simp [K, height, horiz]
              ring
    · have hright_nonneg : 0 ≤ K * Real.exp (-(c * (n : ℝ))) :=
        mul_nonneg hK_nonneg (le_of_lt (Real.exp_pos _))
      simpa [hhigh] using hright_nonneg
  exact Summable.of_nonneg_of_le hleft_nonneg hle
    ((lemma77ExpNegMulNat_summable hc).mul_left K)

/--
Local-limit input surface for iid `Hold` prefix endpoints.

The `point_bound` field is the future Lemma 7.6/Lemma 2.2 producer.  It is an
input here, not a proved theorem.
-/
structure HoldPrefixLocalLimit2DInput (C c : ℝ) : Prop where
  constants : 0 ≤ C ∧ 0 < c
  point_bound :
    ∀ start n j ell,
      lemma77HoldPrefixSignedEndpointMass start n j ell ≤
        lemma77HoldPrefixLocalLimitKernel C c n j ell

/-- Projection of the local-limit endpoint bound from its explicit input surface. -/
theorem lemma77HoldPrefixSignedEndpointMass_le_of_localLimit2DInput
    {C c : ℝ}
    (h : HoldPrefixLocalLimit2DInput C c)
    (start : TaoSection7RenewalPoint) (n : ℕ) (j ell : ℤ) :
    lemma77HoldPrefixSignedEndpointMass start n j ell ≤
      lemma77HoldPrefixLocalLimitKernel C c n j ell :=
  h.point_bound start n j ell

/-- Natural-coordinate projection of the local-limit endpoint bound. -/
theorem lemma77HoldPrefixEndpointMass_le_of_localLimit2DInput
    {C c : ℝ}
    (h : HoldPrefixLocalLimit2DInput C c)
    (start : TaoSection7RenewalPoint) (n r : ℕ) (ell : ℤ) :
    lemma77HoldPrefixEndpointMass start n r ell ≤
      lemma77HoldPrefixLocalLimitKernel C c n (r : ℤ) ell := by
  rw [lemma77HoldPrefixEndpointMass_eq_signedEndpointMass]
  exact lemma77HoldPrefixSignedEndpointMass_le_of_localLimit2DInput
    h start n (r : ℤ) ell

/-- Height-potential kernels are monotone in the leading constant. -/
theorem lemma77HeightPotentialKernel_const_mono
    {C₁ C₂ c : ℝ} (hC : C₁ ≤ C₂) (j : ℤ) (s' : ℕ) :
    lemma77HeightPotentialKernel C₁ c j s' ≤
      lemma77HeightPotentialKernel C₂ c j s' := by
  unfold lemma77HeightPotentialKernel
  have hfactor_nonneg :
      0 ≤ ((1 + (s' : ℝ)) ^ (-(1 / 2 : ℝ))) *
        taoLemma22GaussianWeight (1 + s')
          (c * ((j : ℝ) - (s' : ℝ) / 4)) := by
    exact mul_nonneg (by positivity)
      (taoLemma22GaussianWeight_nonneg (1 + s')
        (c * ((j : ℝ) - (s' : ℝ) / 4)))
  nlinarith [mul_le_mul_of_nonneg_right hC hfactor_nonneg]

/-- Height-potential kernels with the same rate add in the leading constant. -/
theorem lemma77HeightPotentialKernel_add_same_rate
    (C₁ C₂ c : ℝ) (j : ℤ) (s' : ℕ) :
    lemma77HeightPotentialKernel C₁ c j s' +
      lemma77HeightPotentialKernel C₂ c j s' =
        lemma77HeightPotentialKernel (C₁ + C₂) c j s' := by
  unfold lemma77HeightPotentialKernel
  ring

/--
Weakening the height-kernel rate increases the kernel, for nonnegative leading
constant and positive weaker rate.
-/
theorem lemma77HeightPotentialKernel_rate_mono
    {C cweak cstrong : ℝ}
    (hC : 0 ≤ C) (hcweak : 0 < cweak) (hle : cweak ≤ cstrong)
    (j : ℤ) (s' : ℕ) :
    lemma77HeightPotentialKernel C cstrong j s' ≤
      lemma77HeightPotentialKernel C cweak j s' := by
  let x : ℝ := (j : ℝ) - (s' : ℝ) / 4
  let height : ℝ := (1 + (s' : ℝ)) ^ (-(1 / 2 : ℝ))
  let N : ℝ := ((1 + s' : ℕ) : ℝ)
  have hcs_nonneg : 0 ≤ cstrong := le_trans hcweak.le hle
  have hx_abs_nonneg : 0 ≤ |x| := abs_nonneg x
  have hlinear_weight :
      Real.exp (-(|cstrong| * |x|)) ≤ Real.exp (-(|cweak| * |x|)) := by
    rw [Real.exp_le_exp]
    rw [abs_of_nonneg hcs_nonneg, abs_of_pos hcweak]
    nlinarith [mul_le_mul_of_nonneg_right hle hx_abs_nonneg]
  have hN_pos : 0 < N := by
    dsimp [N]
    positivity
  have hc_sq : cweak ^ 2 ≤ cstrong ^ 2 := by
    nlinarith [hle, hcweak.le, hcs_nonneg]
  have hx_sq : 0 ≤ x ^ 2 := sq_nonneg x
  have hsq : (cweak * x) ^ 2 ≤ (cstrong * x) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hc_sq hx_sq]
  have hquad_arg :
      (cweak * x) ^ 2 / N ≤ (cstrong * x) ^ 2 / N := by
    exact div_le_div_of_nonneg_right hsq hN_pos.le
  have hquad :
      Real.exp (-(((cstrong * x) ^ 2) / N)) ≤
        Real.exp (-(((cweak * x) ^ 2) / N)) := by
    rw [Real.exp_le_exp]
    linarith
  have hweight :
      taoLemma22GaussianWeight (1 + s') (cstrong * x) ≤
        taoLemma22GaussianWeight (1 + s') (cweak * x) := by
    unfold taoLemma22GaussianWeight
    simp
    exact add_le_add (by simpa [N] using hquad) hlinear_weight
  have hfactor_nonneg : 0 ≤ C * height := by
    exact mul_nonneg hC (by dsimp [height]; positivity)
  unfold lemma77HeightPotentialKernel
  dsimp [x, height] at hweight ⊢
  exact mul_le_mul_of_nonneg_left hweight hfactor_nonneg

/-- Combine constant and rate weakening for height-potential kernels. -/
theorem lemma77HeightPotentialKernel_le_of_const_rate
    {C C' cweak cstrong : ℝ}
    (hC : 0 ≤ C) (hCC' : C ≤ C') (hcweak : 0 < cweak)
    (hle : cweak ≤ cstrong) (j : ℤ) (s' : ℕ) :
    lemma77HeightPotentialKernel C cstrong j s' ≤
      lemma77HeightPotentialKernel C' cweak j s' :=
  le_trans (lemma77HeightPotentialKernel_rate_mono hC hcweak hle j s')
    (lemma77HeightPotentialKernel_const_mono hCC' j s')

/--
Absorb a horizontal exponential profile into the linear branch of the
height-potential kernel.

This is the reusable bridge from high-region branch estimates to the final
height-kernel profile.
-/
theorem lemma77HeightPotentialKernel_absExp_le
    {K r ch : ℝ} (hK : 0 ≤ K) (_hr : 0 < r) (hch : 0 < ch)
    (hch_le : ch ≤ r) (j : ℤ) (s' : ℕ) :
    K * ((1 + (s' : ℝ)) ^ (-(1 / 2 : ℝ))) *
      Real.exp (-(r * |lemma77ScalarCenteredHorizontal j s'|)) ≤
    lemma77HeightPotentialKernel K ch j s' := by
  let x := lemma77ScalarCenteredHorizontal j s'
  have hheight_nonneg : 0 ≤ (1 + (s' : ℝ)) ^ (-(1 / 2 : ℝ)) := by
    positivity
  have hx_nonneg : 0 ≤ |x| := abs_nonneg x
  have hch_abs : |ch * x| = ch * |x| := by
    rw [abs_mul, abs_of_pos hch]
  have hexp_le :
      Real.exp (-(r * |x|)) ≤ Real.exp (-|ch * x|) := by
    rw [Real.exp_le_exp, hch_abs]
    nlinarith [mul_le_mul_of_nonneg_right hch_le hx_nonneg]
  have hweight_nonneg :
      0 ≤ Real.exp (-(((ch * x) ^ 2) / ((1 + s' : ℕ) : ℝ))) :=
    le_of_lt (Real.exp_pos _)
  have hlinear :
      Real.exp (-|ch * x|) ≤
        Real.exp (-(((ch * x) ^ 2) / ((1 + s' : ℕ) : ℝ))) +
          Real.exp (-|ch * x|) :=
    le_add_of_nonneg_left hweight_nonneg
  have hweight :
      Real.exp (-(r * |x|)) ≤ taoLemma22GaussianWeight (1 + s') (ch * x) := by
    unfold taoLemma22GaussianWeight
    simp
    simpa [hch_abs, abs_of_pos hch] using le_trans hexp_le hlinear
  have hmul :=
    mul_le_mul_of_nonneg_left hweight (mul_nonneg hK hheight_nonneg)
  simpa [lemma77HeightPotentialKernel, lemma77ScalarCenteredHorizontal, x,
    mul_assoc] using hmul

/--
Absorb a Gaussian horizontal profile into the quadratic branch of the
height-potential kernel.
-/
theorem lemma77HeightPotentialKernel_gaussianExp_le
    {K r ch : ℝ} (hK : 0 ≤ K) (_hr : 0 < r) (_hch : 0 < ch)
    (hch_sq : ch ^ 2 ≤ r) (j : ℤ) (s' : ℕ) :
    K * ((1 + (s' : ℝ)) ^ (-(1 / 2 : ℝ))) *
      Real.exp (-(r * (lemma77ScalarCenteredHorizontal j s') ^ 2 /
        (1 + (s' : ℝ)))) ≤
      lemma77HeightPotentialKernel K ch j s' := by
  let x := lemma77ScalarCenteredHorizontal j s'
  let height : ℝ := (1 + (s' : ℝ)) ^ (-(1 / 2 : ℝ))
  have hS_pos : 0 < 1 + (s' : ℝ) := by
    positivity
  have hx_sq : 0 ≤ x ^ 2 := sq_nonneg x
  have hsq : (ch * x) ^ 2 ≤ r * x ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hch_sq hx_sq]
  have harg :
      (ch * x) ^ 2 / (1 + (s' : ℝ)) ≤
        r * x ^ 2 / (1 + (s' : ℝ)) := by
    exact div_le_div_of_nonneg_right hsq hS_pos.le
  have hexp :
      Real.exp (-(r * x ^ 2 / (1 + (s' : ℝ)))) ≤
        Real.exp (-((ch * x) ^ 2 / (1 + (s' : ℝ)))) := by
    rw [Real.exp_le_exp]
    linarith
  have hweight :
      Real.exp (-(r * x ^ 2 / (1 + (s' : ℝ)))) ≤
        taoLemma22GaussianWeight (1 + s') (ch * x) := by
    unfold taoLemma22GaussianWeight
    simp [Nat.cast_add, Nat.cast_one]
    exact le_trans hexp
      (le_add_of_nonneg_right (le_of_lt (Real.exp_pos _)))
  have hfactor_nonneg : 0 ≤ K * height := by
    exact mul_nonneg hK (by dsimp [height]; positivity)
  have hmul := mul_le_mul_of_nonneg_left hweight hfactor_nonneg
  simpa [lemma77HeightPotentialKernel, lemma77ScalarCenteredHorizontal, x,
    height, mul_assoc] using hmul

/-- At height zero, the only main-region local-limit kernel is a linear radial
exponential in the horizontal coordinate. -/
theorem lemma77ScalarMainRegion_zeroKernel_eq_exp_abs
    {C c : ℝ} (hc : 0 < c) (j : ℤ) :
    lemma77HoldPrefixLocalLimitKernel C c 0 j (0 : ℤ) =
      C * Real.exp (-(c * |(j : ℝ)|)) := by
  change lemma77HoldPrefixLocalLimitKernel C c 0 j ((0 : ℕ) : ℤ) =
      C * Real.exp (-(c * |(j : ℝ)|))
  rw [lemma77HoldPrefixLocalLimitKernel_zero_eq C c j 0]
  have hsqrt :
      Real.sqrt ((c * (j : ℝ)) ^ 2 + (c * ((0 : ℕ) : ℝ)) ^ 2) =
        c * |(j : ℝ)| := by
    simp only [Nat.cast_zero, mul_zero, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, add_zero]
    rw [Real.sqrt_sq_eq_abs, abs_mul, abs_of_pos hc]
  rw [hsqrt]

/-- The height-zero main-region filtered kernel sum is the single `n = 0`
term. -/
theorem lemma77ScalarMainRegion_zeroKernel_tsum_eq (C c : ℝ) (j : ℤ) :
    (∑' n : ℕ,
      if lemma77ScalarMainRegion n 0 then
        lemma77HoldPrefixLocalLimitKernel C c n j (0 : ℤ)
      else 0) =
      lemma77HoldPrefixLocalLimitKernel C c 0 j (0 : ℤ) := by
  apply tsum_eq_single 0
  intro n hn
  have hnot : ¬ lemma77ScalarMainRegion n 0 := by
    intro hmain
    have hz := (lemma77ScalarMainRegion_szero_iff n).mp hmain
    exact hn hz
  simp [hnot]

/-- The height-zero endpoint of the main-region contribution is absorbed by
the height-potential kernel. -/
theorem lemma77ScalarMainRegion_zeroKernel_le_heightKernel
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (j : ℤ) :
    (∑' n : ℕ,
      if lemma77ScalarMainRegion n 0 then
        lemma77HoldPrefixLocalLimitKernel C c n j (0 : ℤ)
      else 0) ≤ lemma77HeightPotentialKernel C (c / 4) j 0 := by
  calc
    (∑' n : ℕ,
      if lemma77ScalarMainRegion n 0 then
        lemma77HoldPrefixLocalLimitKernel C c n j (0 : ℤ)
      else 0) = lemma77HoldPrefixLocalLimitKernel C c 0 j (0 : ℤ) := by
        exact lemma77ScalarMainRegion_zeroKernel_tsum_eq C c j
    _ = C * Real.exp (-(c * |(j : ℝ)|)) :=
        lemma77ScalarMainRegion_zeroKernel_eq_exp_abs hc j
    _ = C * ((1 + (0 : ℝ)) ^ (-(1 / 2 : ℝ))) *
        Real.exp (-(c * |lemma77ScalarCenteredHorizontal j 0|)) := by
        simp [lemma77ScalarCenteredHorizontal]
    _ ≤ lemma77HeightPotentialKernel C (c / 4) j 0 := by
        simpa [lemma77ScalarCenteredHorizontal] using
          (lemma77HeightPotentialKernel_absExp_le (K := C) (r := c)
            (ch := c / 4) hC hc (by positivity) (by nlinarith [hc]) j 0)

/--
Positive-height main-region quadratic branch summed into the height-potential
kernel.
-/
theorem lemma77ScalarMainRegion_quadraticContribution_le_heightKernel_of_spos
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) :
    ∃ KQ, 0 ≤ KQ ∧ ∀ j s', 0 < s' →
      Summable (fun n : ℕ =>
        if lemma77ScalarMainRegion n s' then
          C * lemma77LocalLimitPrefactor n *
            Real.exp (-(((c * (lemma77ScalarCenteredHorizontal j s' -
                    lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
                  (c * (-lemma77ScalarTimeOffset n s')) ^ 2) / (n : ℝ)))
        else 0) ∧
      (∑' n : ℕ,
        if lemma77ScalarMainRegion n s' then
          C * lemma77LocalLimitPrefactor n *
            Real.exp (-(((c * (lemma77ScalarCenteredHorizontal j s' -
                    lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
                  (c * (-lemma77ScalarTimeOffset n s')) ^ 2) / (n : ℝ)))
        else 0) ≤
        lemma77HeightPotentialKernel KQ (c / 4) j s' := by
  let a : ℝ := (c ^ 2) / 4
  have ha : 0 < a := by
    dsimp [a]
    positivity
  obtain ⟨KG, hKG, hKGbound⟩ :=
    lemma77ScalarMainRegion_shiftedGaussianCount_le_sqrt ha
  let KQ : ℝ := 33 * C * KG
  have hKQ : 0 ≤ KQ := by
    dsimp [KQ]
    positivity
  refine ⟨KQ, hKQ, ?_⟩
  intro j s' hspos
  let S : ℝ := 1 + (s' : ℝ)
  let height : ℝ := (1 + (s' : ℝ)) ^ (-(1 / 2 : ℝ))
  let horiz : ℝ :=
    Real.exp (-(a * (lemma77ScalarCenteredHorizontal j s') ^ 2 / S))
  let A : ℝ := (33 * C) * S⁻¹ * horiz
  have hA_nonneg : 0 ≤ A := by
    dsimp [A, S, horiz]
    positivity
  have hleft_summable :
      Summable (fun n : ℕ =>
        if lemma77ScalarMainRegion n s' then
          C * lemma77LocalLimitPrefactor n *
            Real.exp (-(((c * (lemma77ScalarCenteredHorizontal j s' -
                    lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
                  (c * (-lemma77ScalarTimeOffset n s')) ^ 2) / (n : ℝ)))
        else 0) :=
    lemma77ScalarMainRegion_filtered_summable_of_finite_support
      (fun n : ℕ =>
        C * lemma77LocalLimitPrefactor n *
          Real.exp (-(((c * (lemma77ScalarCenteredHorizontal j s' -
                  lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
                (c * (-lemma77ScalarTimeOffset n s')) ^ 2) / (n : ℝ)))) s'
  have hright_summable :
      Summable (fun n : ℕ =>
        if lemma77ScalarMainRegion n s' then
          A * Real.exp (-(a * (lemma77ScalarTimeOffset n s') ^ 2 / S))
        else 0) :=
    lemma77ScalarMainRegion_filtered_summable_of_finite_support
      (fun n : ℕ =>
        A * Real.exp (-(a * (lemma77ScalarTimeOffset n s') ^ 2 / S))) s'
  have hpoint : ∀ n : ℕ,
      (if lemma77ScalarMainRegion n s' then
        C * lemma77LocalLimitPrefactor n *
          Real.exp (-(((c * (lemma77ScalarCenteredHorizontal j s' -
                  lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
                (c * (-lemma77ScalarTimeOffset n s')) ^ 2) / (n : ℝ)))
      else 0) ≤
      (if lemma77ScalarMainRegion n s' then
        A * Real.exp (-(a * (lemma77ScalarTimeOffset n s') ^ 2 / S))
      else 0) := by
    intro n
    by_cases hmain : lemma77ScalarMainRegion n s'
    · have hpoint :=
        lemma77ScalarMainRegion_quadraticKernel_le_prefactor_mul_shiftedGaussian
          hC hc hspos hmain j
      simpa [hmain, A, a, S, horiz, mul_assoc] using hpoint
    · simp [hmain]
  have htsum := hleft_summable.tsum_le_tsum hpoint hright_summable
  have hfactor :
      (∑' n : ℕ,
        if lemma77ScalarMainRegion n s' then
          A * Real.exp (-(a * (lemma77ScalarTimeOffset n s') ^ 2 / S))
        else 0) =
        A * (∑' n : ℕ,
          if lemma77ScalarMainRegion n s' then
            Real.exp (-(a * (lemma77ScalarTimeOffset n s') ^ 2 / S))
          else 0) := by
    calc
      (∑' n : ℕ,
        if lemma77ScalarMainRegion n s' then
          A * Real.exp (-(a * (lemma77ScalarTimeOffset n s') ^ 2 / S))
        else 0) =
        (∑' n : ℕ,
          A * (if lemma77ScalarMainRegion n s' then
            Real.exp (-(a * (lemma77ScalarTimeOffset n s') ^ 2 / S))
          else 0)) := by
          apply tsum_congr
          intro n
          by_cases hmain : lemma77ScalarMainRegion n s' <;> simp [hmain]
      _ = A * (∑' n : ℕ,
          if lemma77ScalarMainRegion n s' then
            Real.exp (-(a * (lemma77ScalarTimeOffset n s') ^ 2 / S))
          else 0) := by
          rw [tsum_mul_left]
  have hcount := hKGbound s'
  have hprofile :
      A * (∑' n : ℕ,
        if lemma77ScalarMainRegion n s' then
          Real.exp (-(a * (lemma77ScalarTimeOffset n s') ^ 2 / S))
        else 0) ≤ KQ * height * horiz := by
    calc
      A * (∑' n : ℕ,
        if lemma77ScalarMainRegion n s' then
          Real.exp (-(a * (lemma77ScalarTimeOffset n s') ^ 2 / S))
        else 0) ≤ A * (KG * Real.sqrt S) :=
          mul_le_mul_of_nonneg_left (by simpa [S, a] using hcount) hA_nonneg
      _ = (33 * C * KG) *
          (((1 + (s' : ℝ))⁻¹) * Real.sqrt (1 + (s' : ℝ))) * horiz := by
          dsimp [A, S]
          ring
      _ = KQ * height * horiz := by
          dsimp [KQ, height]
          rw [lemma77_one_add_inv_mul_sqrt_eq_rpow_neg_half s']
  have hto_height :
      KQ * height * horiz ≤
        lemma77HeightPotentialKernel KQ (c / 4) j s' := by
    have hch : 0 < c / 4 := by positivity
    have hch_sq : (c / 4) ^ 2 ≤ a := by
      dsimp [a]
      nlinarith [sq_nonneg c]
    simpa [height, horiz, S, a] using
      (lemma77HeightPotentialKernel_gaussianExp_le (K := KQ) (r := a)
        (ch := c / 4) hKQ ha hch hch_sq j s')
  refine ⟨hleft_summable, ?_⟩
  calc
    (∑' n : ℕ,
      if lemma77ScalarMainRegion n s' then
        C * lemma77LocalLimitPrefactor n *
          Real.exp (-(((c * (lemma77ScalarCenteredHorizontal j s' -
                  lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
                (c * (-lemma77ScalarTimeOffset n s')) ^ 2) / (n : ℝ)))
      else 0)
        ≤ (∑' n : ℕ,
          if lemma77ScalarMainRegion n s' then
            A * Real.exp (-(a * (lemma77ScalarTimeOffset n s') ^ 2 / S))
          else 0) := htsum
    _ = A * (∑' n : ℕ,
          if lemma77ScalarMainRegion n s' then
            Real.exp (-(a * (lemma77ScalarTimeOffset n s') ^ 2 / S))
          else 0) := hfactor
    _ ≤ KQ * height * horiz := hprofile
    _ ≤ lemma77HeightPotentialKernel KQ (c / 4) j s' := hto_height

/--
Positive-height main-region linear branch summed into the height-potential
kernel.
-/
theorem lemma77ScalarMainRegion_linearContribution_le_heightKernel_of_spos
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) :
    ∃ KL, 0 ≤ KL ∧ ∀ j s', 0 < s' →
      Summable (fun n : ℕ =>
        if lemma77ScalarMainRegion n s' then
          C * lemma77LocalLimitPrefactor n *
            Real.exp (-Real.sqrt
              ((c * (lemma77ScalarCenteredHorizontal j s' -
                    lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
                (c * (-lemma77ScalarTimeOffset n s')) ^ 2))
        else 0) ∧
      (∑' n : ℕ,
        if lemma77ScalarMainRegion n s' then
          C * lemma77LocalLimitPrefactor n *
            Real.exp (-Real.sqrt
              ((c * (lemma77ScalarCenteredHorizontal j s' -
                    lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
                (c * (-lemma77ScalarTimeOffset n s')) ^ 2))
        else 0) ≤
        lemma77HeightPotentialKernel KL (c / 4) j s' := by
  let a : ℝ := c / 4
  have ha : 0 < a := by
    dsimp [a]
    positivity
  obtain ⟨KLin, hKLin, hKLinBound⟩ :=
    lemma77ScalarMainRegion_shiftedLinearCount_le_const ha
  let KL : ℝ := 33 * C * KLin
  have hKL : 0 ≤ KL := by
    dsimp [KL]
    positivity
  refine ⟨KL, hKL, ?_⟩
  intro j s' _hspos
  let S : ℝ := 1 + (s' : ℝ)
  let height : ℝ := (1 + (s' : ℝ)) ^ (-(1 / 2 : ℝ))
  let horiz : ℝ :=
    Real.exp (-(a * |lemma77ScalarCenteredHorizontal j s'|))
  let A : ℝ := (33 * C) * S⁻¹ * horiz
  have hA_nonneg : 0 ≤ A := by
    dsimp [A, S, horiz]
    positivity
  have hhoriz_nonneg : 0 ≤ horiz := by
    dsimp [horiz]
    exact le_of_lt (Real.exp_pos _)
  have hleft_summable :
      Summable (fun n : ℕ =>
        if lemma77ScalarMainRegion n s' then
          C * lemma77LocalLimitPrefactor n *
            Real.exp (-Real.sqrt
              ((c * (lemma77ScalarCenteredHorizontal j s' -
                    lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
                (c * (-lemma77ScalarTimeOffset n s')) ^ 2))
        else 0) :=
    lemma77ScalarMainRegion_filtered_summable_of_finite_support
      (fun n : ℕ =>
        C * lemma77LocalLimitPrefactor n *
          Real.exp (-Real.sqrt
            ((c * (lemma77ScalarCenteredHorizontal j s' -
                  lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
              (c * (-lemma77ScalarTimeOffset n s')) ^ 2))) s'
  have hright_summable :
      Summable (fun n : ℕ =>
        if lemma77ScalarMainRegion n s' then
          A * Real.exp (-(a * |lemma77ScalarTimeOffset n s'|))
        else 0) :=
    lemma77ScalarMainRegion_filtered_summable_of_finite_support
      (fun n : ℕ =>
        A * Real.exp (-(a * |lemma77ScalarTimeOffset n s'|))) s'
  have hpoint : ∀ n : ℕ,
      (if lemma77ScalarMainRegion n s' then
        C * lemma77LocalLimitPrefactor n *
          Real.exp (-Real.sqrt
            ((c * (lemma77ScalarCenteredHorizontal j s' -
                  lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
              (c * (-lemma77ScalarTimeOffset n s')) ^ 2))
      else 0) ≤
      (if lemma77ScalarMainRegion n s' then
        A * Real.exp (-(a * |lemma77ScalarTimeOffset n s'|))
      else 0) := by
    intro n
    by_cases hmain : lemma77ScalarMainRegion n s'
    · have hpoint :=
        lemma77ScalarMainRegion_linearKernel_le_prefactor_mul_shiftedLinear
          hC hc hmain j
      simpa [hmain, A, a, S, horiz, mul_assoc] using hpoint
    · simp [hmain]
  have htsum := hleft_summable.tsum_le_tsum hpoint hright_summable
  have hfactor :
      (∑' n : ℕ,
        if lemma77ScalarMainRegion n s' then
          A * Real.exp (-(a * |lemma77ScalarTimeOffset n s'|))
        else 0) =
        A * (∑' n : ℕ,
          if lemma77ScalarMainRegion n s' then
            Real.exp (-(a * |lemma77ScalarTimeOffset n s'|))
          else 0) := by
    calc
      (∑' n : ℕ,
        if lemma77ScalarMainRegion n s' then
          A * Real.exp (-(a * |lemma77ScalarTimeOffset n s'|))
        else 0) =
        (∑' n : ℕ,
          A * (if lemma77ScalarMainRegion n s' then
            Real.exp (-(a * |lemma77ScalarTimeOffset n s'|))
          else 0)) := by
          apply tsum_congr
          intro n
          by_cases hmain : lemma77ScalarMainRegion n s' <;> simp [hmain]
      _ = A * (∑' n : ℕ,
          if lemma77ScalarMainRegion n s' then
            Real.exp (-(a * |lemma77ScalarTimeOffset n s'|))
          else 0) := by
          rw [tsum_mul_left]
  have hcount := hKLinBound s'
  have hprofile :
      A * (∑' n : ℕ,
        if lemma77ScalarMainRegion n s' then
          Real.exp (-(a * |lemma77ScalarTimeOffset n s'|))
        else 0) ≤ KL * height * horiz := by
    calc
      A * (∑' n : ℕ,
        if lemma77ScalarMainRegion n s' then
          Real.exp (-(a * |lemma77ScalarTimeOffset n s'|))
        else 0) ≤ A * KLin :=
          mul_le_mul_of_nonneg_left (by simpa [a] using hcount) hA_nonneg
      _ = KL * S⁻¹ * horiz := by
          dsimp [A, KL]
          ring
      _ ≤ KL * height * horiz := by
          have hinv : S⁻¹ ≤ height := by
            dsimp [S, height]
            exact lemma77_one_add_inv_le_rpow_neg_half s'
          have hscaled : KL * S⁻¹ ≤ KL * height :=
            mul_le_mul_of_nonneg_left hinv hKL
          exact mul_le_mul_of_nonneg_right hscaled hhoriz_nonneg
  have hto_height :
      KL * height * horiz ≤
        lemma77HeightPotentialKernel KL (c / 4) j s' := by
    have hch : 0 < c / 4 := by positivity
    simpa [height, horiz, S, a] using
      (lemma77HeightPotentialKernel_absExp_le (K := KL) (r := c / 4)
        (ch := c / 4) hKL hch hch (le_rfl) j s')
  refine ⟨hleft_summable, ?_⟩
  calc
    (∑' n : ℕ,
      if lemma77ScalarMainRegion n s' then
        C * lemma77LocalLimitPrefactor n *
          Real.exp (-Real.sqrt
            ((c * (lemma77ScalarCenteredHorizontal j s' -
                  lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
              (c * (-lemma77ScalarTimeOffset n s')) ^ 2))
      else 0)
        ≤ (∑' n : ℕ,
          if lemma77ScalarMainRegion n s' then
            A * Real.exp (-(a * |lemma77ScalarTimeOffset n s'|))
          else 0) := htsum
    _ = A * (∑' n : ℕ,
          if lemma77ScalarMainRegion n s' then
            Real.exp (-(a * |lemma77ScalarTimeOffset n s'|))
          else 0) := hfactor
    _ ≤ KL * height * horiz := hprofile
    _ ≤ lemma77HeightPotentialKernel KL (c / 4) j s' := hto_height

/--
Filtered main-region local-limit contribution summed into a height-potential
kernel.

This is the main-region slice only: low/high slices and the unfiltered scalar
summation input are separate assembly steps.
-/
theorem lemma77ScalarMainRegion_kernelContribution_le_heightKernel
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) :
    ∃ Cmain cmain, 0 ≤ Cmain ∧ 0 < cmain ∧
      ∀ j s',
        Summable (fun n : ℕ =>
          if lemma77ScalarMainRegion n s' then
            lemma77HoldPrefixLocalLimitKernel C c n j (s' : ℤ)
          else 0) ∧
        (∑' n : ℕ,
          if lemma77ScalarMainRegion n s' then
            lemma77HoldPrefixLocalLimitKernel C c n j (s' : ℤ)
          else 0) ≤
          lemma77HeightPotentialKernel Cmain cmain j s' := by
  obtain ⟨KQ, hKQ, hQ⟩ :=
    lemma77ScalarMainRegion_quadraticContribution_le_heightKernel_of_spos
      hC hc
  obtain ⟨KL, hKL, hL⟩ :=
    lemma77ScalarMainRegion_linearContribution_le_heightKernel_of_spos
      hC hc
  let Cmain : ℝ := C + KQ + KL
  let cmain : ℝ := c / 4
  have hCmain : 0 ≤ Cmain := by
    dsimp [Cmain]
    nlinarith
  have hcmain : 0 < cmain := by
    dsimp [cmain]
    positivity
  have hC_le_Cmain : C ≤ Cmain := by
    dsimp [Cmain]
    nlinarith [hKQ, hKL]
  have hQKL_le_Cmain : KQ + KL ≤ Cmain := by
    dsimp [Cmain]
    nlinarith [hC]
  refine ⟨Cmain, cmain, hCmain, hcmain, ?_⟩
  intro j s'
  have hkernel_summable :
      Summable (fun n : ℕ =>
        if lemma77ScalarMainRegion n s' then
          lemma77HoldPrefixLocalLimitKernel C c n j (s' : ℤ)
        else 0) :=
    lemma77ScalarMainRegion_filteredKernel_summable_of_finite_support
      C c j s'
  refine ⟨hkernel_summable, ?_⟩
  by_cases hs0 : s' = 0
  · subst s'
    calc
      (∑' n : ℕ,
        if lemma77ScalarMainRegion n 0 then
          lemma77HoldPrefixLocalLimitKernel C c n j (0 : ℤ)
        else 0) ≤ lemma77HeightPotentialKernel C (c / 4) j 0 :=
          lemma77ScalarMainRegion_zeroKernel_le_heightKernel hC hc j
      _ ≤ lemma77HeightPotentialKernel Cmain cmain j 0 := by
          simpa [cmain] using
            lemma77HeightPotentialKernel_const_mono hC_le_Cmain j 0
  · have hspos : 0 < s' := Nat.pos_of_ne_zero hs0
    let q : ℕ → ℝ := fun n =>
      if lemma77ScalarMainRegion n s' then
        C * lemma77LocalLimitPrefactor n *
          Real.exp (-(((c * (lemma77ScalarCenteredHorizontal j s' -
                  lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
                (c * (-lemma77ScalarTimeOffset n s')) ^ 2) / (n : ℝ)))
      else 0
    let l : ℕ → ℝ := fun n =>
      if lemma77ScalarMainRegion n s' then
        C * lemma77LocalLimitPrefactor n *
          Real.exp (-Real.sqrt
            ((c * (lemma77ScalarCenteredHorizontal j s' -
                  lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
              (c * (-lemma77ScalarTimeOffset n s')) ^ 2))
      else 0
    obtain ⟨hqsumm0, hqbound0⟩ := hQ j s' hspos
    obtain ⟨hlsumm0, hlbound0⟩ := hL j s' hspos
    have hqsumm : Summable q := by
      simpa [q] using hqsumm0
    have hlsumm : Summable l := by
      simpa [l] using hlsumm0
    have hqbound :
        (∑' n : ℕ, q n) ≤
          lemma77HeightPotentialKernel KQ (c / 4) j s' := by
      simpa [q] using hqbound0
    have hlbound :
        (∑' n : ℕ, l n) ≤
          lemma77HeightPotentialKernel KL (c / 4) j s' := by
      simpa [l] using hlbound0
    have hbranch_summable : Summable fun n : ℕ => q n + l n :=
      hqsumm.add hlsumm
    have hpoint : ∀ n : ℕ,
        (if lemma77ScalarMainRegion n s' then
          lemma77HoldPrefixLocalLimitKernel C c n j (s' : ℤ)
        else 0) ≤ q n + l n := by
      intro n
      by_cases hmain : lemma77ScalarMainRegion n s'
      · have heq :=
          lemma77HoldPrefixLocalLimitKernel_eq_mainRegionBranches_of_spos
            C c hspos hmain j
        simp [q, l, hmain, heq]
      · simp [q, l, hmain]
    have htsum :=
      hkernel_summable.tsum_le_tsum hpoint hbranch_summable
    calc
      (∑' n : ℕ,
        if lemma77ScalarMainRegion n s' then
          lemma77HoldPrefixLocalLimitKernel C c n j (s' : ℤ)
        else 0) ≤ (∑' n : ℕ, (q n + l n)) := htsum
      _ = (∑' n : ℕ, q n) + (∑' n : ℕ, l n) :=
          hqsumm.tsum_add hlsumm
      _ ≤ lemma77HeightPotentialKernel KQ (c / 4) j s' +
          lemma77HeightPotentialKernel KL (c / 4) j s' :=
          add_le_add hqbound hlbound
      _ = lemma77HeightPotentialKernel (KQ + KL) (c / 4) j s' := by
          exact lemma77HeightPotentialKernel_add_same_rate KQ KL (c / 4) j s'
      _ ≤ lemma77HeightPotentialKernel Cmain cmain j s' := by
          simpa [cmain] using
            lemma77HeightPotentialKernel_const_mono hQKL_le_Cmain j s'

/--
Filtered low-region contribution to the height-potential kernel.

This packages the checked low pointwise profile, finite low support, and
height-tail absorption into the same public shape as the high-region slice.
-/
theorem lemma77ScalarLowRegion_kernelContribution_le_heightKernel
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) :
    ∃ Clow clow, 0 ≤ Clow ∧ 0 < clow ∧
      ∀ j s',
        Summable (fun n : ℕ =>
          if lemma77ScalarLowRegion n s' then
            lemma77HoldPrefixLocalLimitKernel C c n j (s' : ℤ)
          else 0) ∧
        (∑' n : ℕ,
          if lemma77ScalarLowRegion n s' then
            lemma77HoldPrefixLocalLimitKernel C c n j (s' : ℤ)
          else 0) ≤
          lemma77HeightPotentialKernel Clow clow j s' := by
  let rho : ℝ := lemma77ScalarLowRegionRate c
  let Kpoint : ℝ := 2 * C
  let Ktail : ℝ := ((2 * Real.exp (-1)) / rho) ^ 2
  let Clow : ℝ := Kpoint * Ktail
  let clow : ℝ := rho
  have hrho : 0 < rho := by
    dsimp [rho]
    exact lemma77ScalarLowRegionRate_pos hc
  have hKpoint_nonneg : 0 ≤ Kpoint := by
    dsimp [Kpoint]
    nlinarith [hC]
  have hKtail_nonneg : 0 ≤ Ktail := by
    dsimp [Ktail]
    positivity
  have hClow_nonneg : 0 ≤ Clow := by
    dsimp [Clow]
    exact mul_nonneg hKpoint_nonneg hKtail_nonneg
  refine ⟨Clow, clow, hClow_nonneg, by simpa [clow] using hrho, ?_⟩
  intro j s'
  let height : ℝ := (1 + (s' : ℝ)) ^ (-(1 / 2 : ℝ))
  let horiz : ℝ :=
    Real.exp (-(rho * |lemma77ScalarCenteredHorizontal j s'|))
  have hfiltered_summable :
      Summable fun n : ℕ =>
        if lemma77ScalarLowRegion n s' then
          lemma77HoldPrefixLocalLimitKernel C c n j (s' : ℤ)
        else 0 :=
    lemma77ScalarLowRegion_filteredKernel_summable_of_finite_support C c j s'
  have hpoint :
      ∀ {j : ℤ} {n s' : ℕ},
        lemma77ScalarLowRegion n s' →
          lemma77HoldPrefixLocalLimitKernel C c n j (s' : ℤ) ≤
            Kpoint * Real.exp (-(rho * (1 + (s' : ℝ)))) *
              Real.exp (-(rho * |lemma77ScalarCenteredHorizontal j s'|)) := by
    intro j n s' hlow
    dsimp [Kpoint, rho]
    exact lemma77ScalarLowRegion_kernel_le_exp_profile hC hc hlow
  have hfinite_profile :=
    lemma77ScalarLowRegion_filteredKernel_tsum_le_exp_profile
      hKpoint_nonneg hpoint j s'
  have htail :
      (((s' + 1 : ℕ) : ℝ) *
          Real.exp (-(rho * (1 + (s' : ℝ))))) ≤
        Ktail * height := by
    have htail0 :=
      lemma77_one_add_mul_exp_neg_le_rpow_neg_half hrho s'
    dsimp [Ktail, height]
    simpa [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc]
      using htail0
  have hprofile_to_height :
      (((s' + 1 : ℕ) : ℝ) * Kpoint) *
          Real.exp (-(rho * (1 + (s' : ℝ)))) * horiz ≤
        Clow * height * horiz := by
    have hscaled :
        Kpoint *
            ((((s' + 1 : ℕ) : ℝ) *
              Real.exp (-(rho * (1 + (s' : ℝ))))) ) ≤
          Kpoint * (Ktail * height) :=
      mul_le_mul_of_nonneg_left htail hKpoint_nonneg
    calc
      (((s' + 1 : ℕ) : ℝ) * Kpoint) *
          Real.exp (-(rho * (1 + (s' : ℝ)))) * horiz
          = Kpoint *
              ((((s' + 1 : ℕ) : ℝ) *
                Real.exp (-(rho * (1 + (s' : ℝ))))) ) * horiz := by
            ring
      _ ≤ Kpoint * (Ktail * height) * horiz :=
          mul_le_mul_of_nonneg_right hscaled (le_of_lt (Real.exp_pos _))
      _ = Clow * height * horiz := by
          simp [Clow, Ktail, height, horiz]
          ring
  have habsorb :
      Clow * height * horiz ≤
        lemma77HeightPotentialKernel Clow clow j s' := by
    dsimp [height, horiz, clow]
    exact lemma77HeightPotentialKernel_absExp_le
      hClow_nonneg hrho hrho le_rfl j s'
  constructor
  · exact hfiltered_summable
  · exact le_trans hfinite_profile (le_trans hprofile_to_height habsorb)

/--
Combined high-region contribution to the height-potential kernel.

This packages the quadratic and linear high-region branch estimates into the
source-shaped filtered full kernel, retaining both summability and the `tsum`
bound needed by the later three-region scalar summation input.
-/
theorem lemma77ScalarHighRegion_kernelContribution_le_heightKernel
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) :
    ∃ Chigh chigh, 0 ≤ Chigh ∧ 0 < chigh ∧
      ∀ j s',
        Summable (fun n : ℕ =>
          if lemma77ScalarHighRegion n s' then
            lemma77HoldPrefixLocalLimitKernel C c n j (s' : ℤ)
          else 0) ∧
        (∑' n : ℕ,
          if lemma77ScalarHighRegion n s' then
            lemma77HoldPrefixLocalLimitKernel C c n j (s' : ℤ)
          else 0) ≤
          lemma77HeightPotentialKernel Chigh chigh j s' := by
  classical
  let aQ : ℝ := (c ^ 2) / 4
  let rQ : ℝ := lemma77ScalarProductTailRate aQ
  let rL : ℝ := c / 4
  let chigh : ℝ := min rQ rL
  let KQ : ℝ :=
    C * ((8 * Real.exp (-1)) / aQ) * lemma77ScalarProductTailConstant aQ
  let KL : ℝ := C * ((8 * Real.exp (-1)) / c) * (1 - Real.exp (-c))⁻¹
  let Chigh : ℝ := KQ + KL
  have haQ : 0 < aQ := by
    dsimp [aQ]
    positivity
  have hrQ : 0 < rQ := by
    dsimp [rQ, lemma77ScalarProductTailRate]
    positivity
  have hrL : 0 < rL := by
    dsimp [rL]
    positivity
  have hchigh_pos : 0 < chigh := by
    dsimp [chigh]
    exact lt_min hrQ hrL
  have hchigh_le_Q : chigh ≤ rQ := by
    dsimp [chigh]
    exact min_le_left _ _
  have hchigh_le_L : chigh ≤ rL := by
    dsimp [chigh]
    exact min_le_right _ _
  have hQfactor_nonneg : 0 ≤ (8 * Real.exp (-1)) / aQ := by
    positivity
  have hQconst_nonneg : 0 ≤ lemma77ScalarProductTailConstant aQ :=
    lemma77ScalarProductTailConstant_nonneg haQ
  have hKQ_nonneg : 0 ≤ KQ := by
    dsimp [KQ]
    exact mul_nonneg (mul_nonneg hC hQfactor_nonneg) hQconst_nonneg
  have hLfactor_nonneg : 0 ≤ (8 * Real.exp (-1)) / c := by
    positivity
  have hden_pos : 0 < 1 - Real.exp (-c) := by
    have hbase_lt : Real.exp (-c) < 1 := by
      rw [Real.exp_lt_one_iff]
      linarith
    linarith
  have hLconst_nonneg : 0 ≤ (1 - Real.exp (-c))⁻¹ :=
    inv_nonneg.mpr hden_pos.le
  have hKL_nonneg : 0 ≤ KL := by
    dsimp [KL]
    exact mul_nonneg (mul_nonneg hC hLfactor_nonneg) hLconst_nonneg
  have hChigh_nonneg : 0 ≤ Chigh := by
    dsimp [Chigh]
    exact add_nonneg hKQ_nonneg hKL_nonneg
  refine ⟨Chigh, chigh, hChigh_nonneg, hchigh_pos, ?_⟩
  intro j s'
  let quad : ℕ → ℝ := fun n =>
    if lemma77ScalarHighRegion n s' then
      C * lemma77LocalLimitPrefactor n *
        Real.exp (-(((c * (lemma77ScalarCenteredHorizontal j s' -
                lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
              (c * (-lemma77ScalarTimeOffset n s')) ^ 2) / (n : ℝ)))
    else 0
  let lin : ℕ → ℝ := fun n =>
    if lemma77ScalarHighRegion n s' then
      C * lemma77LocalLimitPrefactor n *
        Real.exp (-Real.sqrt
          ((c * (lemma77ScalarCenteredHorizontal j s' -
                lemma77ScalarTimeOffset n s' / 4)) ^ 2 +
            (c * (-lemma77ScalarTimeOffset n s')) ^ 2))
    else 0
  let kern : ℕ → ℝ := fun n =>
    if lemma77ScalarHighRegion n s' then
      lemma77HoldPrefixLocalLimitKernel C c n j (s' : ℤ)
    else 0
  have hkern_eq : ∀ n, kern n = quad n + lin n := by
    intro n
    by_cases hhigh : lemma77ScalarHighRegion n s'
    · rw [show kern n = lemma77HoldPrefixLocalLimitKernel C c n j (s' : ℤ) by
        simp [kern, hhigh]]
      rw [lemma77HoldPrefixLocalLimitKernel_eq_highRegionBranches C c hhigh j]
      simp [quad, lin, hhigh]
    · simp [kern, quad, lin, hhigh]
  have hquad_summable : Summable quad := by
    simpa [quad] using
      lemma77ScalarHighRegion_quadraticContribution_summable hC hc j s'
  have hlin_summable : Summable lin := by
    simpa [lin] using
      lemma77ScalarHighRegion_linearContribution_summable hC hc j s'
  have hkern_summable : Summable kern := by
    exact (hquad_summable.add hlin_summable).congr (by
      intro n
      exact (hkern_eq n).symm)
  have htsum_split :
      (∑' n : ℕ, kern n) = (∑' n : ℕ, (quad n + lin n)) := by
    apply tsum_congr
    intro n
    exact hkern_eq n
  have htsum_add :
      (∑' n : ℕ, (quad n + lin n)) =
        (∑' n : ℕ, quad n) + (∑' n : ℕ, lin n) :=
    hquad_summable.tsum_add hlin_summable
  have htsum_kernel :
      (∑' n : ℕ, kern n) =
        (∑' n : ℕ, quad n) + (∑' n : ℕ, lin n) :=
    htsum_split.trans htsum_add
  have hquad_abs :
      (∑' n : ℕ, quad n) ≤
        lemma77HeightPotentialKernel KQ chigh j s' := by
    calc
      (∑' n : ℕ, quad n) ≤
          KQ * ((1 + (s' : ℝ)) ^ (-(1 / 2 : ℝ))) *
            Real.exp (-(rQ * |lemma77ScalarCenteredHorizontal j s'|)) := by
        simpa [quad, KQ, aQ, rQ] using
          lemma77ScalarHighRegion_quadraticContribution_le_explicit hC hc j s'
      _ ≤ lemma77HeightPotentialKernel KQ chigh j s' := by
        exact lemma77HeightPotentialKernel_absExp_le
          hKQ_nonneg hrQ hchigh_pos hchigh_le_Q j s'
  have hlin_abs :
      (∑' n : ℕ, lin n) ≤
        lemma77HeightPotentialKernel KL chigh j s' := by
    calc
      (∑' n : ℕ, lin n) ≤
          KL * ((1 + (s' : ℝ)) ^ (-(1 / 2 : ℝ))) *
            Real.exp (-(rL * |lemma77ScalarCenteredHorizontal j s'|)) := by
        simpa [lin, KL, rL] using
          lemma77ScalarHighRegion_linearContribution_le_exp hC hc j s'
      _ ≤ lemma77HeightPotentialKernel KL chigh j s' := by
        exact lemma77HeightPotentialKernel_absExp_le
          hKL_nonneg hrL hchigh_pos hchigh_le_L j s'
  have hkernel_bound :
      (∑' n : ℕ, kern n) ≤
        lemma77HeightPotentialKernel KQ chigh j s' +
          lemma77HeightPotentialKernel KL chigh j s' := by
    rw [htsum_kernel]
    exact add_le_add hquad_abs hlin_abs
  have hcombine :
      lemma77HeightPotentialKernel KQ chigh j s' +
          lemma77HeightPotentialKernel KL chigh j s' =
        lemma77HeightPotentialKernel Chigh chigh j s' := by
    dsimp [lemma77HeightPotentialKernel, Chigh]
    ring
  constructor
  · simpa [kern] using hkern_summable
  · calc
      (∑' n : ℕ,
        if lemma77ScalarHighRegion n s' then
          lemma77HoldPrefixLocalLimitKernel C c n j (s' : ℤ)
        else 0) = (∑' n : ℕ, kern n) := by
          rfl
      _ ≤ lemma77HeightPotentialKernel KQ chigh j s' +
          lemma77HeightPotentialKernel KL chigh j s' := hkernel_bound
      _ = lemma77HeightPotentialKernel Chigh chigh j s' := hcombine

/--
The raw scalar kernel is the pointwise sum of its low/main/high filtered
pieces.
-/
theorem lemma77HoldPrefixLocalLimitKernel_eq_scalarRegionFilters
    (C c : ℝ) (n : ℕ) (j : ℤ) (s' : ℕ) :
    lemma77HoldPrefixLocalLimitKernel C c n j (s' : ℤ) =
      (if lemma77ScalarLowRegion n s' then
        lemma77HoldPrefixLocalLimitKernel C c n j (s' : ℤ)
      else 0) +
      (if lemma77ScalarMainRegion n s' then
        lemma77HoldPrefixLocalLimitKernel C c n j (s' : ℤ)
      else 0) +
      (if lemma77ScalarHighRegion n s' then
        lemma77HoldPrefixLocalLimitKernel C c n j (s' : ℤ)
      else 0) := by
  rcases lemma77ScalarRegion_trichotomy n s' with hlow | hmain | hhigh
  · have hnot_main : ¬ lemma77ScalarMainRegion n s' :=
      lemma77ScalarLowRegion_not_main hlow
    have hnot_high : ¬ lemma77ScalarHighRegion n s' :=
      lemma77ScalarLowRegion_not_high hlow
    simp [hlow, hnot_main, hnot_high]
  · have hnot_low : ¬ lemma77ScalarLowRegion n s' := by
      intro hlow
      exact lemma77ScalarLowRegion_not_main hlow hmain
    have hnot_high : ¬ lemma77ScalarHighRegion n s' := by
      intro hhigh
      exact lemma77ScalarHighRegion_not_main hhigh hmain
    simp [hmain, hnot_low, hnot_high]
  · have hnot_low : ¬ lemma77ScalarLowRegion n s' := by
      intro hlow
      exact lemma77ScalarLowRegion_not_high hlow hhigh
    have hnot_main : ¬ lemma77ScalarMainRegion n s' :=
      lemma77ScalarHighRegion_not_main hhigh
    simp [hhigh, hnot_low, hnot_main]

/-- Kernel side of the height-potential summation over iid prefix lengths. -/
def lemma77HeightPotentialKernelTsum
    (C c : ℝ) (j : ℤ) (s' : ℕ) : ℝ :=
  ∑' n : ℕ, lemma77HoldPrefixLocalLimitKernel C c n j (s' : ℤ)

/-- Signed endpoint masses are nonnegative. -/
theorem lemma77HoldPrefixSignedEndpointMass_nonneg
    (start : TaoSection7RenewalPoint) (n : ℕ) (j ell : ℤ) :
    0 ≤ lemma77HoldPrefixSignedEndpointMass start n j ell := by
  simp [lemma77HoldPrefixSignedEndpointMass, ENNReal.toReal_nonneg]

/--
Scalar summation input for turning the pointwise iid `Hold` local-limit
estimate into the height-potential estimate.

The hard analytic content is the summability and comparison of the kernel
`tsum`; the monotone passage from endpoint masses to that `tsum` is checked
below from `HoldPrefixLocalLimit2DInput`.
-/
structure Lemma77HeightPotentialScalarSummationInput
    (C c Csum csum : ℝ) : Prop where
  constants : 0 ≤ Csum ∧ 0 < csum
  kernel_summable :
    ∀ j (s' : ℕ),
      Summable (fun n : ℕ =>
        lemma77HoldPrefixLocalLimitKernel C c n j (s' : ℤ))
  kernel_tsum_bound :
    ∀ j s',
      lemma77HeightPotentialKernelTsum C c j s' ≤
        lemma77HeightPotentialKernel Csum csum j s'

/--
Construct the raw scalar summation input from the checked low/main/high
filtered height-kernel slices.
-/
theorem lemma77HeightPotentialScalarSummationInput_of_region_contributions
    {C c : ℝ} (hC : 0 ≤ C) (hc : 0 < c) :
    ∃ Csum csum,
      Lemma77HeightPotentialScalarSummationInput C c Csum csum := by
  obtain ⟨Clow, clow, hClow, hclow, hlow⟩ :=
    lemma77ScalarLowRegion_kernelContribution_le_heightKernel hC hc
  obtain ⟨Cmain, cmain, hCmain, hcmain, hmain⟩ :=
    lemma77ScalarMainRegion_kernelContribution_le_heightKernel hC hc
  obtain ⟨Chigh, chigh, hChigh, hchigh, hhigh⟩ :=
    lemma77ScalarHighRegion_kernelContribution_le_heightKernel hC hc
  let csum : ℝ := min clow (min cmain chigh)
  let Csum : ℝ := Clow + Cmain + Chigh
  have hcsum : 0 < csum := by
    dsimp [csum]
    exact lt_min hclow (lt_min hcmain hchigh)
  have hCsum : 0 ≤ Csum := by
    dsimp [Csum]
    nlinarith
  have hcsum_le_clow : csum ≤ clow := by
    dsimp [csum]
    exact min_le_left _ _
  have hcsum_le_cmain : csum ≤ cmain := by
    dsimp [csum]
    exact le_trans (min_le_right clow (min cmain chigh))
      (min_le_left cmain chigh)
  have hcsum_le_chigh : csum ≤ chigh := by
    dsimp [csum]
    exact le_trans (min_le_right clow (min cmain chigh))
      (min_le_right cmain chigh)
  refine ⟨Csum, csum, ?_⟩
  refine
    { constants := ⟨hCsum, hcsum⟩
      kernel_summable := ?_
      kernel_tsum_bound := ?_ }
  · intro j s'
    let low : ℕ → ℝ := fun n =>
      if lemma77ScalarLowRegion n s' then
        lemma77HoldPrefixLocalLimitKernel C c n j (s' : ℤ)
      else 0
    let main : ℕ → ℝ := fun n =>
      if lemma77ScalarMainRegion n s' then
        lemma77HoldPrefixLocalLimitKernel C c n j (s' : ℤ)
      else 0
    let high : ℕ → ℝ := fun n =>
      if lemma77ScalarHighRegion n s' then
        lemma77HoldPrefixLocalLimitKernel C c n j (s' : ℤ)
      else 0
    obtain ⟨hlow_summ0, _⟩ := hlow j s'
    obtain ⟨hmain_summ0, _⟩ := hmain j s'
    obtain ⟨hhigh_summ0, _⟩ := hhigh j s'
    have hlow_summ : Summable low := by
      simpa [low] using hlow_summ0
    have hmain_summ : Summable main := by
      simpa [main] using hmain_summ0
    have hhigh_summ : Summable high := by
      simpa [high] using hhigh_summ0
    have hregion_summ :
        Summable fun n : ℕ => (low n + main n + high n) :=
      (hlow_summ.add hmain_summ).add hhigh_summ
    have hraw_eq : ∀ n : ℕ,
        lemma77HoldPrefixLocalLimitKernel C c n j (s' : ℤ) =
          low n + main n + high n := by
      intro n
      simpa [low, main, high] using
        lemma77HoldPrefixLocalLimitKernel_eq_scalarRegionFilters C c n j s'
    exact hregion_summ.congr (by
      intro n
      exact (hraw_eq n).symm)
  · intro j s'
    let low : ℕ → ℝ := fun n =>
      if lemma77ScalarLowRegion n s' then
        lemma77HoldPrefixLocalLimitKernel C c n j (s' : ℤ)
      else 0
    let main : ℕ → ℝ := fun n =>
      if lemma77ScalarMainRegion n s' then
        lemma77HoldPrefixLocalLimitKernel C c n j (s' : ℤ)
      else 0
    let high : ℕ → ℝ := fun n =>
      if lemma77ScalarHighRegion n s' then
        lemma77HoldPrefixLocalLimitKernel C c n j (s' : ℤ)
      else 0
    obtain ⟨hlow_summ0, hlow_bound0⟩ := hlow j s'
    obtain ⟨hmain_summ0, hmain_bound0⟩ := hmain j s'
    obtain ⟨hhigh_summ0, hhigh_bound0⟩ := hhigh j s'
    have hlow_summ : Summable low := by
      simpa [low] using hlow_summ0
    have hmain_summ : Summable main := by
      simpa [main] using hmain_summ0
    have hhigh_summ : Summable high := by
      simpa [high] using hhigh_summ0
    have hlow_bound :
        (∑' n : ℕ, low n) ≤
          lemma77HeightPotentialKernel Clow clow j s' := by
      simpa [low] using hlow_bound0
    have hmain_bound :
        (∑' n : ℕ, main n) ≤
          lemma77HeightPotentialKernel Cmain cmain j s' := by
      simpa [main] using hmain_bound0
    have hhigh_bound :
        (∑' n : ℕ, high n) ≤
          lemma77HeightPotentialKernel Chigh chigh j s' := by
      simpa [high] using hhigh_bound0
    have hlow_common :
        (∑' n : ℕ, low n) ≤
          lemma77HeightPotentialKernel Clow csum j s' :=
      le_trans hlow_bound
        (lemma77HeightPotentialKernel_le_of_const_rate (C := Clow)
          (C' := Clow) (cweak := csum) (cstrong := clow)
          hClow le_rfl hcsum hcsum_le_clow j s')
    have hmain_common :
        (∑' n : ℕ, main n) ≤
          lemma77HeightPotentialKernel Cmain csum j s' :=
      le_trans hmain_bound
        (lemma77HeightPotentialKernel_le_of_const_rate (C := Cmain)
          (C' := Cmain) (cweak := csum) (cstrong := cmain)
          hCmain le_rfl hcsum hcsum_le_cmain j s')
    have hhigh_common :
        (∑' n : ℕ, high n) ≤
          lemma77HeightPotentialKernel Chigh csum j s' :=
      le_trans hhigh_bound
        (lemma77HeightPotentialKernel_le_of_const_rate (C := Chigh)
          (C' := Chigh) (cweak := csum) (cstrong := chigh)
          hChigh le_rfl hcsum hcsum_le_chigh j s')
    have hregion_summ :
        Summable fun n : ℕ => (low n + main n + high n) :=
      (hlow_summ.add hmain_summ).add hhigh_summ
    have hraw_eq : ∀ n : ℕ,
        lemma77HoldPrefixLocalLimitKernel C c n j (s' : ℤ) =
          low n + main n + high n := by
      intro n
      simpa [low, main, high] using
        lemma77HoldPrefixLocalLimitKernel_eq_scalarRegionFilters C c n j s'
    have htsum_raw :
        lemma77HeightPotentialKernelTsum C c j s' =
          (∑' n : ℕ, (low n + main n + high n)) := by
      unfold lemma77HeightPotentialKernelTsum
      apply tsum_congr
      intro n
      exact hraw_eq n
    have htsum_add_low_main :
        (∑' n : ℕ, (low n + main n)) =
          (∑' n : ℕ, low n) + (∑' n : ℕ, main n) :=
      hlow_summ.tsum_add hmain_summ
    have hlow_main_summ : Summable fun n : ℕ => low n + main n :=
      hlow_summ.add hmain_summ
    have htsum_add_three :
        (∑' n : ℕ, (low n + main n + high n)) =
          ((∑' n : ℕ, low n) + (∑' n : ℕ, main n)) +
            (∑' n : ℕ, high n) := by
      calc
        (∑' n : ℕ, (low n + main n + high n)) =
            (∑' n : ℕ, (low n + main n)) +
              (∑' n : ℕ, high n) :=
              hlow_main_summ.tsum_add hhigh_summ
        _ = ((∑' n : ℕ, low n) + (∑' n : ℕ, main n)) +
              (∑' n : ℕ, high n) := by
              rw [htsum_add_low_main]
    have hsum_common :
        ((∑' n : ℕ, low n) + (∑' n : ℕ, main n)) +
            (∑' n : ℕ, high n) ≤
          (lemma77HeightPotentialKernel Clow csum j s' +
            lemma77HeightPotentialKernel Cmain csum j s') +
            lemma77HeightPotentialKernel Chigh csum j s' :=
      add_le_add (add_le_add hlow_common hmain_common) hhigh_common
    have hcombine :
        (lemma77HeightPotentialKernel Clow csum j s' +
            lemma77HeightPotentialKernel Cmain csum j s') +
            lemma77HeightPotentialKernel Chigh csum j s' =
          lemma77HeightPotentialKernel Csum csum j s' := by
      rw [lemma77HeightPotentialKernel_add_same_rate Clow Cmain csum j s']
      rw [lemma77HeightPotentialKernel_add_same_rate (Clow + Cmain) Chigh csum j s']
    calc
      lemma77HeightPotentialKernelTsum C c j s' =
          (∑' n : ℕ, (low n + main n + high n)) := htsum_raw
      _ = ((∑' n : ℕ, low n) + (∑' n : ℕ, main n)) +
            (∑' n : ℕ, high n) := htsum_add_three
      _ ≤ (lemma77HeightPotentialKernel Clow csum j s' +
            lemma77HeightPotentialKernel Cmain csum j s') +
            lemma77HeightPotentialKernel Chigh csum j s' := hsum_common
      _ = lemma77HeightPotentialKernel Csum csum j s' := hcombine

/-- Height-potential masses are nonnegative. -/
theorem lemma77HeightPotentialMass_nonneg
    (start : TaoSection7RenewalPoint) (j : ℤ) (s' : ℕ) :
    0 ≤ lemma77HeightPotentialMass start j s' := by
  unfold lemma77HeightPotentialMass
  exact tsum_nonneg fun n =>
    lemma77HoldPrefixSignedEndpointMass_nonneg start n j (s' : ℤ)

/--
Endpoint height-potential masses are summable in prefix length once the
pointwise local-limit input is paired with the scalar kernel summability
input.
-/
theorem lemma77HeightPotentialMass_summable_of_localLimit2DInput
    {C c Csum csum : ℝ}
    (hlocal : HoldPrefixLocalLimit2DInput C c)
    (hscalar : Lemma77HeightPotentialScalarSummationInput C c Csum csum)
    (start : TaoSection7RenewalPoint) (j : ℤ) (s' : ℕ) :
    Summable (fun n : ℕ =>
      lemma77HoldPrefixSignedEndpointMass start n j (s' : ℤ)) := by
  exact Summable.of_nonneg_of_le
    (fun n =>
      lemma77HoldPrefixSignedEndpointMass_nonneg start n j (s' : ℤ))
    (fun n => hlocal.point_bound start n j (s' : ℤ))
    (hscalar.kernel_summable j s')

/-- Projection from local-limit input plus the scalar summation input. -/
theorem lemma77HeightPotentialMass_le_of_localLimit2DInput
    {C c Csum csum : ℝ}
    (hlocal : HoldPrefixLocalLimit2DInput C c)
    (hscalar : Lemma77HeightPotentialScalarSummationInput C c Csum csum)
    (start : TaoSection7RenewalPoint) (j : ℤ) (s' : ℕ) :
    lemma77HeightPotentialMass start j s' ≤
      lemma77HeightPotentialKernel Csum csum j s' :=
  calc
    lemma77HeightPotentialMass start j s'
        = ∑' n : ℕ,
            lemma77HoldPrefixSignedEndpointMass start n j (s' : ℤ) := by
          rfl
    _ ≤ lemma77HeightPotentialKernelTsum C c j s' :=
        (lemma77HeightPotentialMass_summable_of_localLimit2DInput
            hlocal hscalar start j s').tsum_le_tsum
          (fun n => hlocal.point_bound start n j (s' : ℤ))
          (hscalar.kernel_summable j s')
    _ ≤ lemma77HeightPotentialKernel Csum csum j s' :=
        hscalar.kernel_tsum_bound j s'

/--
Build the height-potential input from pointwise iid `Hold` local-limit input
plus the explicit summation/comparison adapter.
-/
theorem lemma77HeightPotentialInput_of_localLimit2DInput
    {C c Csum csum : ℝ}
    (hlocal : HoldPrefixLocalLimit2DInput C c)
    (hscalar : Lemma77HeightPotentialScalarSummationInput C c Csum csum) :
    Lemma77HeightPotentialInput Csum csum where
  constants := hscalar.constants
  height_potential := by
    intro start j s'
    exact lemma77HeightPotentialMass_le_of_localLimit2DInput
      hlocal hscalar start j s'

/--
Tao `(7.33)` vertical-smoothing mass surface.

This finite sum is the source-shaped convolution over the vertical leftover
`l'_k`, with the height-potential mass at height `s - l'_k`.
-/
def lemma77VerticalSmoothing733Mass
    (beta : ℝ) (start : TaoSection7RenewalPoint) (j : ℤ) (s : ℕ) : ℝ :=
  ∑ lp ∈ Finset.range (s + 1),
    Real.exp (-beta * (lp : ℝ)) *
      lemma77HeightPotentialMass start j (s - lp)

/--
Kernel side of the `(7.33)` vertical-smoothing convolution.

This is an intermediate finite kernel sum, before the supplied comparison to
the final height-potential kernel at scale `s`.
-/
def lemma77VerticalSmoothing733KernelSum
    (C c beta : ℝ) (j : ℤ) (s : ℕ) : ℝ :=
  ∑ lp ∈ Finset.range (s + 1),
    Real.exp (-beta * (lp : ℝ)) *
      lemma77HeightPotentialKernel C c j (s - lp)

/--
Input surface for Tao's `(7.33)` vertical-smoothing comparison.

The finite mass-to-kernel step is checked below from a height-potential input.
The analytic comparison from the finite kernel convolution to the final kernel
is an input here, not proved.
-/
structure Lemma77VerticalSmoothing733Input
    (C c beta C33 c33 : ℝ) : Prop where
  constants : 0 < beta ∧ 0 ≤ C33 ∧ 0 < c33
  kernel_sum_bound :
    ∀ j s,
      lemma77VerticalSmoothing733KernelSum C c beta j s ≤
        lemma77HeightPotentialKernel C33 c33 j s

/--
Linear-branch center drift for the `(7.33)` vertical convolution.

The terminal factor pays for moving the center from height `s - lp` back to
height `s`, leaving half of the vertical exponential for summing in `lp`.
-/
theorem lemma77VerticalSmoothing733_linearBranch_centerDrift_le
    {beta c c33 : ℝ} (hc33 : 0 < c33)
    (hc33_le_c : c33 ≤ c) (hquarter : c33 / 4 ≤ beta / 2)
    (x : ℝ) (lp : ℕ) :
    Real.exp (-(beta * (lp : ℝ))) *
        Real.exp (-(c * |x + (lp : ℝ) / 4|)) ≤
      Real.exp (-((beta / 2) * (lp : ℝ))) *
        Real.exp (-(c33 * |x|)) := by
  let L : ℝ := lp
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    exact Nat.cast_nonneg lp
  have hquarter_nonneg : 0 ≤ L / 4 := by positivity
  have htri0 : |(x + L / 4) - L / 4| ≤ |x + L / 4| + |L / 4| := by
    simpa using abs_sub_le (x + L / 4) 0 (L / 4)
  have htri : |x| ≤ |x + L / 4| + L / 4 := by
    have h_abs : |L / 4| = L / 4 := abs_of_nonneg hquarter_nonneg
    simpa [h_abs] using htri0
  have hscaled : c33 * |x| ≤ c * |x + L / 4| + (beta / 2) * L := by
    have h1 : c33 * |x| ≤ c33 * (|x + L / 4| + L / 4) :=
      mul_le_mul_of_nonneg_left htri hc33.le
    have h2 : c33 * (|x + L / 4| + L / 4) ≤
        c * |x + L / 4| + (beta / 2) * L := by
      have habs_nonneg : 0 ≤ |x + L / 4| := abs_nonneg _
      have hquarter_scaled : c33 * (L / 4) ≤ (beta / 2) * L := by
        nlinarith [mul_le_mul_of_nonneg_right hquarter hL_nonneg]
      nlinarith [mul_le_mul_of_nonneg_right hc33_le_c habs_nonneg,
        hquarter_scaled]
    exact le_trans h1 h2
  rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  nlinarith [hscaled]

/--
Height-prefactor comparison for the `(7.33)` vertical convolution.

For a summand with `lp ≤ s`, the inner height `s - lp` loses at most the
polynomial factor `lp + 1` relative to the outer height `s`.
-/
theorem lemma77VerticalSmoothing733_heightScaleTerm_le
    (s lp : ℕ) (hlp : lp ≤ s) :
    ((1 + ((s - lp : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ))) ≤
      (1 + (lp : ℝ)) * ((1 + (s : ℝ)) ^ (-(1 / 2 : ℝ))) := by
  let A : ℝ := 1 + (s : ℝ)
  let B : ℝ := 1 + ((s - lp : ℕ) : ℝ)
  let P : ℝ := 1 + (lp : ℝ)
  have hA_pos : 0 < A := by
    dsimp [A]
    positivity
  have hB_pos : 0 < B := by
    dsimp [B]
    positivity
  have hP_pos : 0 < P := by
    dsimp [P]
    positivity
  have hsub : ((s - lp : ℕ) : ℝ) = (s : ℝ) - (lp : ℝ) := by
    rw [Nat.cast_sub hlp]
  have hlpR : (lp : ℝ) ≤ (s : ℝ) := by
    exact_mod_cast hlp
  have hPB : A ≤ P * B := by
    have hnonneg : 0 ≤ (lp : ℝ) * ((s : ℝ) - (lp : ℝ)) :=
      mul_nonneg (Nat.cast_nonneg lp) (sub_nonneg.mpr hlpR)
    dsimp [A, B, P]
    rw [hsub]
    nlinarith [hnonneg]
  have hprod : A ≤ P ^ 2 * B := by
    have hP_ge_one : 1 ≤ P := by
      dsimp [P]
      exact le_add_of_nonneg_right (Nat.cast_nonneg lp)
    have hB_nonneg : 0 ≤ B := hB_pos.le
    have hPB_le : P * B ≤ P ^ 2 * B := by
      nlinarith [mul_le_mul_of_nonneg_right hP_ge_one hB_nonneg]
    exact le_trans hPB hPB_le
  have hsqrt : Real.sqrt A ≤ P * Real.sqrt B := by
    refine (Real.sqrt_le_left (mul_nonneg hP_pos.le (Real.sqrt_nonneg B))).2 ?_
    calc
      A ≤ P ^ 2 * B := hprod
      _ = (P * Real.sqrt B) ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hB_pos.le]
  have hsqrtA_pos : 0 < Real.sqrt A := Real.sqrt_pos.2 hA_pos
  have hsqrtB_pos : 0 < Real.sqrt B := Real.sqrt_pos.2 hB_pos
  rw [show 1 + ((s - lp : ℕ) : ℝ) = B by rfl]
  rw [show 1 + (s : ℝ) = A by rfl]
  rw [Real.rpow_neg hB_pos.le, Real.rpow_neg hA_pos.le]
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  change (Real.sqrt B)⁻¹ ≤ P / Real.sqrt A
  rw [le_div_iff₀' hsqrtA_pos]
  change Real.sqrt A / Real.sqrt B ≤ P
  rw [div_le_iff₀ hsqrtB_pos]
  simpa [mul_comm, mul_left_comm, mul_assoc] using hsqrt

/--
Polynomial-times-exponential decay is controlled by a half-rate exponential.
-/
theorem lemma77_one_add_nat_mul_exp_neg_le_const_mul_exp_neg_half
    {delta : ℝ} (hdelta : 0 < delta) (n : ℕ) :
    (1 + (n : ℝ)) * Real.exp (-(delta * (n : ℝ))) ≤
      (Real.exp (delta / 2) * (Real.exp (-1) / (delta / 2))) *
        Real.exp (-((delta / 2) * (n : ℝ))) := by
  let a : ℝ := delta / 2
  have ha : 0 < a := by
    dsimp [a]
    positivity
  have hS_pos : 0 < 1 + (n : ℝ) := by positivity
  have hmul := Real.mul_exp_neg_le_exp_neg_one (a * (1 + (n : ℝ)))
  have hcore : (1 + (n : ℝ)) * Real.exp (-(a * (1 + (n : ℝ)))) ≤
      Real.exp (-1) / a := by
    calc
      (1 + (n : ℝ)) * Real.exp (-(a * (1 + (n : ℝ))))
          = ((a * (1 + (n : ℝ))) *
              Real.exp (-(a * (1 + (n : ℝ))))) / a := by
            field_simp [ha.ne']
      _ ≤ Real.exp (-1) / a := div_le_div_of_nonneg_right hmul ha.le
  have hbounded : (1 + (n : ℝ)) * Real.exp (-(a * (n : ℝ))) ≤
      Real.exp a * (Real.exp (-1) / a) := by
    calc
      (1 + (n : ℝ)) * Real.exp (-(a * (n : ℝ)))
          = (1 + (n : ℝ)) *
              (Real.exp a * Real.exp (-(a * (1 + (n : ℝ))))) := by
            rw [← Real.exp_add]
            congr 1
            ring_nf
      _ = Real.exp a *
            ((1 + (n : ℝ)) * Real.exp (-(a * (1 + (n : ℝ))))) := by
            ring_nf
      _ ≤ Real.exp a * (Real.exp (-1) / a) :=
          mul_le_mul_of_nonneg_left hcore (le_of_lt (Real.exp_pos a))
  have hsplit : (1 + (n : ℝ)) * Real.exp (-(delta * (n : ℝ))) =
      ((1 + (n : ℝ)) * Real.exp (-(a * (n : ℝ)))) *
        Real.exp (-(a * (n : ℝ))) := by
    calc
      (1 + (n : ℝ)) * Real.exp (-(delta * (n : ℝ)))
          = (1 + (n : ℝ)) *
              (Real.exp (-(a * (n : ℝ))) *
                Real.exp (-(a * (n : ℝ)))) := by
              rw [← Real.exp_add]
              congr 1
              dsimp [a]
              ring_nf
      _ = ((1 + (n : ℝ)) * Real.exp (-(a * (n : ℝ)))) *
          Real.exp (-(a * (n : ℝ))) := by
          ring_nf
  rw [hsplit]
  have hexp_nonneg : 0 ≤ Real.exp (-(a * (n : ℝ))) :=
    le_of_lt (Real.exp_pos _)
  have hmul_le := mul_le_mul_of_nonneg_right hbounded hexp_nonneg
  dsimp [a] at hmul_le
  simpa [mul_assoc] using hmul_le

/--
Finite height-scale convolution for the `(7.33)` vertical smoothing sum.

After a branch drift leaves residual exponential decay in `lp`, the inner
height prefactors can be summed back to the outer height `s`.
-/
theorem lemma77VerticalSmoothing733_heightScaleConvolution_le
    {delta : ℝ} (hdelta : 0 < delta) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ s : ℕ,
      (∑ lp ∈ Finset.range (s + 1),
        Real.exp (-(delta * (lp : ℝ))) *
          ((1 + ((s - lp : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ)))) ≤
        K * ((1 + (s : ℝ)) ^ (-(1 / 2 : ℝ))) := by
  let a : ℝ := delta / 2
  let K0 : ℝ := Real.exp a * (Real.exp (-1) / a)
  let G : ℝ := (1 - Real.exp (-a))⁻¹
  refine ⟨K0 * G, ?_, ?_⟩
  · have ha : 0 < a := by
      dsimp [a]
      positivity
    have hden_pos : 0 < 1 - Real.exp (-a) := by
      rw [sub_pos]
      rw [Real.exp_lt_one_iff]
      linarith
    have hK0_nonneg : 0 ≤ K0 := by
      dsimp [K0]
      positivity
    have hG_nonneg : 0 ≤ G := by
      dsimp [G]
      exact inv_nonneg.mpr hden_pos.le
    exact mul_nonneg hK0_nonneg hG_nonneg
  · intro s
    have ha : 0 < a := by
      dsimp [a]
      positivity
    have houter_nonneg : 0 ≤ ((1 + (s : ℝ)) ^ (-(1 / 2 : ℝ))) :=
      Real.rpow_nonneg (by positivity) _
    have hK0_nonneg : 0 ≤ K0 := by
      dsimp [K0]
      positivity
    have hfinite_le_tsum :
        (∑ lp ∈ Finset.range (s + 1), Real.exp (-(a * (lp : ℝ)))) ≤
          ∑' lp : ℕ, Real.exp (-(a * (lp : ℝ))) :=
      (lemma77ExpNegMulNat_summable ha).sum_le_tsum (Finset.range (s + 1))
        (by intro lp _hlp; exact le_of_lt (Real.exp_pos _))
    have hsum_bound :
        (∑ lp ∈ Finset.range (s + 1), Real.exp (-(a * (lp : ℝ)))) ≤ G := by
      calc
        (∑ lp ∈ Finset.range (s + 1), Real.exp (-(a * (lp : ℝ)))) ≤
            ∑' lp : ℕ, Real.exp (-(a * (lp : ℝ))) := hfinite_le_tsum
        _ = G := by
          dsimp [G]
          rw [lemma77ExpNegMulNat_tsum ha]
    have hpoint : ∀ lp ∈ Finset.range (s + 1),
        Real.exp (-(delta * (lp : ℝ))) *
          ((1 + ((s - lp : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ))) ≤
        (K0 * Real.exp (-(a * (lp : ℝ)))) *
          ((1 + (s : ℝ)) ^ (-(1 / 2 : ℝ))) := by
      intro lp hlp_mem
      have hlp : lp ≤ s := Nat.lt_succ_iff.mp (Finset.mem_range.mp hlp_mem)
      have hscale := lemma77VerticalSmoothing733_heightScaleTerm_le s lp hlp
      have hexp_nonneg : 0 ≤ Real.exp (-(delta * (lp : ℝ))) :=
        le_of_lt (Real.exp_pos _)
      have htail :=
        lemma77_one_add_nat_mul_exp_neg_le_const_mul_exp_neg_half hdelta lp
      have htail' :
          Real.exp (-(delta * (lp : ℝ))) * (1 + (lp : ℝ)) ≤
            K0 * Real.exp (-(a * (lp : ℝ))) := by
        dsimp [K0, a]
        simpa [mul_comm, mul_left_comm, mul_assoc] using htail
      calc
        Real.exp (-(delta * (lp : ℝ))) *
            ((1 + ((s - lp : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ))) ≤
          Real.exp (-(delta * (lp : ℝ))) *
            ((1 + (lp : ℝ)) *
              ((1 + (s : ℝ)) ^ (-(1 / 2 : ℝ)))) :=
            mul_le_mul_of_nonneg_left hscale hexp_nonneg
        _ = (Real.exp (-(delta * (lp : ℝ))) * (1 + (lp : ℝ))) *
              ((1 + (s : ℝ)) ^ (-(1 / 2 : ℝ))) := by
            ring
        _ ≤ (K0 * Real.exp (-(a * (lp : ℝ)))) *
              ((1 + (s : ℝ)) ^ (-(1 / 2 : ℝ))) :=
            mul_le_mul_of_nonneg_right htail' houter_nonneg
    calc
      (∑ lp ∈ Finset.range (s + 1),
        Real.exp (-(delta * (lp : ℝ))) *
          ((1 + ((s - lp : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ)))) ≤
        ∑ lp ∈ Finset.range (s + 1),
          (K0 * Real.exp (-(a * (lp : ℝ)))) *
            ((1 + (s : ℝ)) ^ (-(1 / 2 : ℝ))) :=
          Finset.sum_le_sum hpoint
      _ = (K0 *
            (∑ lp ∈ Finset.range (s + 1), Real.exp (-(a * (lp : ℝ))))) *
            ((1 + (s : ℝ)) ^ (-(1 / 2 : ℝ))) := by
          rw [← Finset.sum_mul, ← Finset.mul_sum]
      _ ≤ (K0 * G) * ((1 + (s : ℝ)) ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hsum_bound hK0_nonneg) houter_nonneg

/--
Completed-square center/scale comparison for the Gaussian branch.

This is the real-variable core used when the inner height denominator `T` and
the outer height denominator `S` satisfy `S = T + L`.
-/
theorem lemma77VerticalSmoothing733_gaussianCenterScale_base
    {S T L x : ℝ} (hT : 0 < T) (hS : 0 < S) (hL : 0 ≤ L)
    (hS_eq : S = T + L) :
    x ^ 2 / S ≤ (x + L / 4) ^ 2 / T + L / 16 := by
  have hidentity :
      (x + L / 4) ^ 2 / T + L / 16 - x ^ 2 / S =
        L * (x + S / 4) ^ 2 / (T * S) := by
    subst S
    field_simp [hT.ne']
    ring_nf
  have hnonneg : 0 ≤ L * (x + S / 4) ^ 2 / (T * S) := by
    exact div_nonneg (mul_nonneg hL (sq_nonneg _))
      (mul_nonneg hT.le hS.le)
  nlinarith

/--
Gaussian-branch center and scale drift for the `(7.33)` vertical convolution.

The terminal vertical factor pays for moving from the inner center and height
`s - lp` to the outer center and height `s`, retaining half of the vertical
exponential for the finite height-scale convolution.
-/
theorem lemma77VerticalSmoothing733_gaussianBranch_centerScaleDrift_le
    {beta c c33 : ℝ} (_hc33 : 0 < c33)
    (hquad : 2 * c33 ^ 2 ≤ c ^ 2)
    (hbudget : c33 ^ 2 / 8 ≤ beta / 2)
    {s lp : ℕ} (hlp : lp ≤ s) (x : ℝ) :
    Real.exp (-(beta * (lp : ℝ))) *
        Real.exp (-(((c * (x + (lp : ℝ) / 4)) ^ 2) /
          ((1 + (s - lp : ℕ) : ℝ)))) ≤
      Real.exp (-((beta / 2) * (lp : ℝ))) *
        Real.exp (-(((c33 * x) ^ 2) / (1 + (s : ℝ)))) := by
  let L : ℝ := lp
  let T : ℝ := (1 + (s - lp : ℕ) : ℝ)
  let S : ℝ := 1 + (s : ℝ)
  let y : ℝ := x + L / 4
  have hL_nonneg : 0 ≤ L := by
    dsimp [L]
    positivity
  have hT_pos : 0 < T := by
    dsimp [T]
    positivity
  have hS_pos : 0 < S := by
    dsimp [S]
    positivity
  have hsub : ((s - lp : ℕ) : ℝ) = (s : ℝ) - (lp : ℝ) := by
    rw [Nat.cast_sub hlp]
  have hS_eq : S = T + L := by
    dsimp [S, T, L]
    rw [hsub]
    ring
  have hbase : x ^ 2 / S ≤ y ^ 2 / T + L / 16 := by
    simpa [y] using
      lemma77VerticalSmoothing733_gaussianCenterScale_base
        (S := S) (T := T) (L := L) (x := x)
        hT_pos hS_pos hL_nonneg hS_eq
  have hc33_sq_nonneg : 0 ≤ c33 ^ 2 := sq_nonneg c33
  have hbase_scaled :
      (c33 * x) ^ 2 / S ≤ c33 ^ 2 * (y ^ 2 / T + L / 16) := by
    calc
      (c33 * x) ^ 2 / S = c33 ^ 2 * (x ^ 2 / S) := by ring
      _ ≤ c33 ^ 2 * (y ^ 2 / T + L / 16) :=
          mul_le_mul_of_nonneg_left hbase hc33_sq_nonneg
  have hquad_weak : c33 ^ 2 ≤ c ^ 2 := by
    nlinarith [hc33_sq_nonneg, hquad]
  have hy_sq_nonneg : 0 ≤ y ^ 2 := sq_nonneg y
  have hgauss_cmp : c33 ^ 2 * (y ^ 2 / T) ≤ (c * y) ^ 2 / T := by
    have hnum : c33 ^ 2 * y ^ 2 ≤ c ^ 2 * y ^ 2 :=
      mul_le_mul_of_nonneg_right hquad_weak hy_sq_nonneg
    have hdiv : c33 ^ 2 * y ^ 2 / T ≤ c ^ 2 * y ^ 2 / T :=
      div_le_div_of_nonneg_right hnum hT_pos.le
    calc
      c33 ^ 2 * (y ^ 2 / T) = c33 ^ 2 * y ^ 2 / T := by ring
      _ ≤ c ^ 2 * y ^ 2 / T := hdiv
      _ = (c * y) ^ 2 / T := by ring
  have hbudget16 : c33 ^ 2 / 16 ≤ beta / 2 := by
    nlinarith [hc33_sq_nonneg, hbudget]
  have hL_cmp : c33 ^ 2 * (L / 16) ≤ (beta / 2) * L := by
    nlinarith [mul_le_mul_of_nonneg_right hbudget16 hL_nonneg]
  have hscaled :
      (c33 * x) ^ 2 / S ≤ (c * y) ^ 2 / T + (beta / 2) * L := by
    have hright : c33 ^ 2 * (y ^ 2 / T + L / 16) ≤
        (c * y) ^ 2 / T + (beta / 2) * L := by
      nlinarith [hgauss_cmp, hL_cmp]
    exact le_trans hbase_scaled hright
  rw [← Real.exp_add, ← Real.exp_add, Real.exp_le_exp]
  dsimp [S, T, L, y] at hscaled ⊢
  nlinarith [hscaled]

/-- Inner vertical-convolution center in terms of the outer center. -/
theorem lemma77VerticalSmoothing733_innerCentered_eq
    (j : ℤ) (s lp : ℕ) (hlp : lp ≤ s) :
    lemma77ScalarCenteredHorizontal j (s - lp) =
      lemma77ScalarCenteredHorizontal j s + (lp : ℝ) / 4 := by
  unfold lemma77ScalarCenteredHorizontal
  rw [Nat.cast_sub hlp]
  ring

/--
Pointwise branch comparison for one summand of the `(7.33)` kernel
convolution.

The inner `G` kernel at height `s - lp` is split into its Gaussian and linear
branches, both moved to the outer center and outer height `s`.
-/
theorem lemma77VerticalSmoothing733_kernelSummand_le_outerBranchProfiles
    {C c beta c33 : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hc33 : 0 < c33)
    (hc33_le_c : c33 ≤ c) (hquarter : c33 / 4 ≤ beta / 2)
    (hquad : 2 * c33 ^ 2 ≤ c ^ 2)
    (hbudget : c33 ^ 2 / 8 ≤ beta / 2)
    (j : ℤ) {s lp : ℕ} (hlp : lp ≤ s) :
    Real.exp (-(beta * (lp : ℝ))) *
        lemma77HeightPotentialKernel C c j (s - lp) ≤
      C * (((1 + ((s - lp : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ))) *
        (Real.exp (-((beta / 2) * (lp : ℝ))) *
          Real.exp (-(((c33 * lemma77ScalarCenteredHorizontal j s) ^ 2) /
            (1 + (s : ℝ)))) +
         Real.exp (-((beta / 2) * (lp : ℝ))) *
          Real.exp (-(c33 * |lemma77ScalarCenteredHorizontal j s|)))) := by
  let x : ℝ := lemma77ScalarCenteredHorizontal j s
  let y : ℝ := lemma77ScalarCenteredHorizontal j (s - lp)
  let H : ℝ := ((1 + ((s - lp : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ)))
  have hH_nonneg : 0 ≤ H := by
    dsimp [H]
    positivity
  have hfactor_nonneg : 0 ≤ C * H := mul_nonneg hC hH_nonneg
  have hcenter : y = x + (lp : ℝ) / 4 := by
    dsimp [x, y]
    exact lemma77VerticalSmoothing733_innerCentered_eq j s lp hlp
  have hlin_inner : Real.exp (-|c * y|) = Real.exp (-(c * |y|)) := by
    rw [abs_mul, abs_of_pos hc]
  have hlin :=
    lemma77VerticalSmoothing733_linearBranch_centerDrift_le
      hc33 hc33_le_c hquarter x lp
  have hlin' :
      Real.exp (-(beta * (lp : ℝ))) * Real.exp (-|c * y|) ≤
        Real.exp (-((beta / 2) * (lp : ℝ))) *
          Real.exp (-(c33 * |x|)) := by
    rw [hlin_inner, hcenter]
    exact hlin
  have hgauss :=
    lemma77VerticalSmoothing733_gaussianBranch_centerScaleDrift_le
      hc33 hquad hbudget hlp x
  have hgauss' :
      Real.exp (-(beta * (lp : ℝ))) *
          Real.exp (-(((c * y) ^ 2) / ((1 + (s - lp : ℕ) : ℝ)))) ≤
        Real.exp (-((beta / 2) * (lp : ℝ))) *
          Real.exp (-(((c33 * x) ^ 2) / (1 + (s : ℝ)))) := by
    rw [hcenter]
    exact hgauss
  have hsum :
      Real.exp (-(beta * (lp : ℝ))) *
          Real.exp (-(((c * y) ^ 2) / ((1 + (s - lp : ℕ) : ℝ)))) +
        Real.exp (-(beta * (lp : ℝ))) * Real.exp (-|c * y|) ≤
      Real.exp (-((beta / 2) * (lp : ℝ))) *
          Real.exp (-(((c33 * x) ^ 2) / (1 + (s : ℝ)))) +
        Real.exp (-((beta / 2) * (lp : ℝ))) *
          Real.exp (-(c33 * |x|)) :=
    add_le_add hgauss' hlin'
  have hmul := mul_le_mul_of_nonneg_left hsum hfactor_nonneg
  unfold lemma77HeightPotentialKernel
  dsimp [x, y, H] at hmul ⊢
  unfold taoLemma22GaussianWeight
  simp [mul_add, mul_assoc, mul_left_comm, mul_comm] at hmul ⊢
  exact hmul

/--
The `(7.33)` finite kernel convolution is bounded by the outer
height-potential kernel once a finite height-scale convolution constant is
available.
-/
theorem lemma77VerticalSmoothing733KernelSum_le_heightKernel_of_heightScale
    {C c beta K c33 : ℝ} (hC : 0 ≤ C) (hc : 0 < c)
    (hK : 0 ≤ K) (hc33 : 0 < c33)
    (hc33_le_c : c33 ≤ c) (hquarter : c33 / 4 ≤ beta / 2)
    (hquad : 2 * c33 ^ 2 ≤ c ^ 2)
    (hbudget : c33 ^ 2 / 8 ≤ beta / 2)
    (hheight : ∀ s : ℕ,
      (∑ lp ∈ Finset.range (s + 1),
        Real.exp (-((beta / 2) * (lp : ℝ))) *
          ((1 + ((s - lp : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ)))) ≤
        K * ((1 + (s : ℝ)) ^ (-(1 / 2 : ℝ))))
    (j : ℤ) (s : ℕ) :
    lemma77VerticalSmoothing733KernelSum C c beta j s ≤
      lemma77HeightPotentialKernel (C * K + C * K) c33 j s := by
  let R := Finset.range (s + 1)
  let x : ℝ := lemma77ScalarCenteredHorizontal j s
  let Hout : ℝ := (1 + (s : ℝ)) ^ (-(1 / 2 : ℝ))
  let Q : ℝ := Real.exp (-(((c33 * x) ^ 2) / (1 + (s : ℝ))))
  let Lprof : ℝ := Real.exp (-(c33 * |x|))
  let A : ℕ → ℝ := fun lp =>
    Real.exp (-((beta / 2) * (lp : ℝ))) *
      ((1 + ((s - lp : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ)))
  have hHout_nonneg : 0 ≤ Hout := by
    dsimp [Hout]
    positivity
  have hQ_nonneg : 0 ≤ Q := by
    dsimp [Q]
    positivity
  have hLprof_nonneg : 0 ≤ Lprof := by
    dsimp [Lprof]
    positivity
  have hCK_nonneg : 0 ≤ C * K := mul_nonneg hC hK
  have hA_sum : R.sum A ≤ K * Hout := by
    dsimp [R, A, Hout]
    exact hheight s
  have hpoint : ∀ lp ∈ R,
      Real.exp (-beta * (lp : ℝ)) *
          lemma77HeightPotentialKernel C c j (s - lp) ≤
        C * (A lp * Q + A lp * Lprof) := by
    intro lp hlp_mem
    have hlp : lp ≤ s := by
      dsimp [R] at hlp_mem
      exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hlp_mem)
    have hp :=
      lemma77VerticalSmoothing733_kernelSummand_le_outerBranchProfiles
        hC hc hc33 hc33_le_c hquarter hquad hbudget j hlp
    calc
      Real.exp (-beta * (lp : ℝ)) *
          lemma77HeightPotentialKernel C c j (s - lp)
          = Real.exp (-(beta * (lp : ℝ))) *
              lemma77HeightPotentialKernel C c j (s - lp) := by
            congr 1
            ring_nf
      _ ≤ C * (((1 + ((s - lp : ℕ) : ℝ)) ^ (-(1 / 2 : ℝ))) *
          (Real.exp (-((beta / 2) * (lp : ℝ))) *
            Real.exp (-(((c33 * lemma77ScalarCenteredHorizontal j s) ^ 2) /
              (1 + (s : ℝ)))) +
           Real.exp (-((beta / 2) * (lp : ℝ))) *
            Real.exp (-(c33 * |lemma77ScalarCenteredHorizontal j s|)))) := hp
      _ = C * (A lp * Q + A lp * Lprof) := by
        dsimp [A, Q, Lprof, x]
        ring
  have hsum_decomp :
      R.sum (fun n => A n * Q + A n * Lprof) =
        R.sum A * Q + R.sum A * Lprof := by
    rw [Finset.sum_add_distrib, Finset.sum_mul, Finset.sum_mul]
  calc
    lemma77VerticalSmoothing733KernelSum C c beta j s ≤
        R.sum (fun n => C * (A n * Q + A n * Lprof)) := by
      unfold lemma77VerticalSmoothing733KernelSum
      dsimp [R]
      exact Finset.sum_le_sum hpoint
    _ = C * R.sum (fun n => A n * Q + A n * Lprof) := by
      exact (Finset.mul_sum R (fun n => A n * Q + A n * Lprof) C).symm
    _ = C * (R.sum A * Q + R.sum A * Lprof) := by
      exact congrArg (fun z => C * z) hsum_decomp
    _ ≤ C * ((K * Hout) * Q + (K * Hout) * Lprof) := by
      have hq : R.sum A * Q ≤ (K * Hout) * Q :=
        mul_le_mul_of_nonneg_right hA_sum hQ_nonneg
      have hl : R.sum A * Lprof ≤ (K * Hout) * Lprof :=
        mul_le_mul_of_nonneg_right hA_sum hLprof_nonneg
      exact mul_le_mul_of_nonneg_left (add_le_add hq hl) hC
    _ = (C * K) * Hout * Q + (C * K) * Hout * Lprof := by
        ring
    _ ≤ lemma77HeightPotentialKernel (C * K) c33 j s +
          lemma77HeightPotentialKernel (C * K) c33 j s := by
      exact add_le_add
        (by
          have h := lemma77HeightPotentialKernel_gaussianExp_le
            (K := C * K) (r := c33 ^ 2) (ch := c33)
            hCK_nonneg (pow_pos hc33 2) hc33 le_rfl j s
          dsimp [Hout, Q, x]
          simpa [pow_two, mul_assoc, mul_left_comm, mul_comm] using h)
        (by
          dsimp [Hout, Lprof, x]
          exact lemma77HeightPotentialKernel_absExp_le
            hCK_nonneg hc33 hc33 le_rfl j s)
    _ = lemma77HeightPotentialKernel (C * K + C * K) c33 j s := by
      rw [lemma77HeightPotentialKernel_add_same_rate]

/--
Analytic producer for Tao's vertical smoothing estimate `(7.33)`.

This constructs the existing `(7.33)` input surface from the checked branch
drift estimates and finite height-scale convolution.
-/
theorem lemma77VerticalSmoothing733Input_of_kernel_convolution
    {C c beta : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hbeta : 0 < beta) :
    ∃ C33 c33,
      Lemma77VerticalSmoothing733Input C c beta C33 c33 := by
  obtain ⟨K, hK, hheight⟩ :=
    lemma77VerticalSmoothing733_heightScaleConvolution_le
      (delta := beta / 2) (by positivity)
  let c33 : ℝ := min (c / 4) (min beta 1)
  let C33 : ℝ := C * K + C * K
  have hc4_pos : 0 < c / 4 := by
    positivity
  have hc33_pos : 0 < c33 := by
    dsimp [c33]
    exact lt_min hc4_pos (lt_min hbeta zero_lt_one)
  have hc33_nonneg : 0 ≤ c33 := hc33_pos.le
  have hc33_le_c4 : c33 ≤ c / 4 := by
    dsimp [c33]
    exact min_le_left _ _
  have hc33_le_beta : c33 ≤ beta := by
    dsimp [c33]
    exact le_trans (min_le_right (c / 4) (min beta 1)) (min_le_left beta 1)
  have hc33_le_one : c33 ≤ 1 := by
    dsimp [c33]
    exact le_trans (min_le_right (c / 4) (min beta 1)) (min_le_right beta 1)
  have hc33_le_c : c33 ≤ c := by
    nlinarith
  have hquarter : c33 / 4 ≤ beta / 2 := by
    nlinarith
  have hc4_nonneg : 0 ≤ c / 4 := by
    positivity
  have hsq_le_c4 : c33 ^ 2 ≤ (c / 4) ^ 2 :=
    (sq_le_sq₀ hc33_nonneg hc4_nonneg).2 hc33_le_c4
  have hquad : 2 * c33 ^ 2 ≤ c ^ 2 := by
    nlinarith [hsq_le_c4]
  have hsq_le_self : c33 ^ 2 ≤ c33 := by
    have hmul := mul_le_mul_of_nonneg_left hc33_le_one hc33_nonneg
    nlinarith [hmul]
  have hbudget : c33 ^ 2 / 8 ≤ beta / 2 := by
    nlinarith
  have hC33_nonneg : 0 ≤ C33 := by
    dsimp [C33]
    nlinarith [mul_nonneg hC hK]
  refine ⟨C33, c33, ?_⟩
  refine
    { constants := ⟨hbeta, hC33_nonneg, hc33_pos⟩
      kernel_sum_bound := ?_ }
  intro j s
  dsimp [C33]
  exact lemma77VerticalSmoothing733KernelSum_le_heightKernel_of_heightScale
    hC hc hK hc33_pos hc33_le_c hquarter hquad hbudget hheight j s

/-- The `(7.33)` mass convolution is bounded by the kernel convolution. -/
theorem lemma77VerticalSmoothing733Mass_le_kernelSum
    {C c beta : ℝ}
    (hheight : Lemma77HeightPotentialInput C c)
    (start : TaoSection7RenewalPoint) (j : ℤ) (s : ℕ) :
    lemma77VerticalSmoothing733Mass beta start j s ≤
      lemma77VerticalSmoothing733KernelSum C c beta j s := by
  unfold lemma77VerticalSmoothing733Mass
    lemma77VerticalSmoothing733KernelSum
  apply Finset.sum_le_sum
  intro lp _hlp
  exact mul_le_mul_of_nonneg_left
    (hheight.height_potential start j (s - lp))
    (le_of_lt (Real.exp_pos _))

/-- Projection from height-potential input plus the explicit `(7.33)` input. -/
theorem lemma77VerticalSmoothing733Mass_le_of_verticalSmoothing733Input
    {C c beta C33 c33 : ℝ}
    (hheight : Lemma77HeightPotentialInput C c)
    (h733 : Lemma77VerticalSmoothing733Input C c beta C33 c33)
    (start : TaoSection7RenewalPoint) (j : ℤ) (s : ℕ) :
    lemma77VerticalSmoothing733Mass beta start j s ≤
      lemma77HeightPotentialKernel C33 c33 j s :=
  le_trans (lemma77VerticalSmoothing733Mass_le_kernelSum hheight start j s)
    (h733.kernel_sum_bound j s)

/-- Positive horizontal increment `j_k = q + 1` from Tao's `(7.32)` step. -/
def lemma77PositiveHorizontalIncrement (q : ℕ) : ℤ :=
  ((q + 1 : ℕ) : ℤ)

/-- Signed horizontal shift `j - j_k` from Tao's `(7.32)` step. -/
def lemma77HorizontalShift732 (j : ℤ) (q : ℕ) : ℤ :=
  j - lemma77PositiveHorizontalIncrement q

/-- Kernel side of the `(7.32)` horizontal convolution. -/
def lemma77HorizontalConvolution732KernelTsum
    (alpha C c : ℝ) (j : ℤ) (s : ℕ) : ℝ :=
  ∑' q : ℕ,
    Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
      lemma77HeightPotentialKernel C c
        (lemma77HorizontalShift732 j q) s

/--
Input surface for Tao's `(7.32)` horizontal convolution comparison.

The mass-to-kernel `tsum` step is checked below from the `(7.33)` projection.
The analytic comparison from the horizontal kernel convolution to the final
kernel is supplied by the producer in this section.
-/
structure Lemma77HorizontalConvolution732Input
    (alpha C33 c33 C32 c32 : ℝ) : Prop where
  constants : 0 < alpha ∧ 0 ≤ C32 ∧ 0 < c32
  kernel_summable :
    ∀ j s,
      Summable (fun q : ℕ =>
        Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
          lemma77HeightPotentialKernel C33 c33
            (lemma77HorizontalShift732 j q) s)
  kernel_tsum_bound :
    ∀ j s,
      lemma77HorizontalConvolution732KernelTsum alpha C33 c33 j s ≤
        lemma77HeightPotentialKernel C32 c32 j s

/-- The `(7.32)` horizontal shift subtracts the positive increment in centered coordinates. -/
theorem lemma77HorizontalShift732_centered_eq (j : ℤ) (q s : ℕ) :
    lemma77ScalarCenteredHorizontal (lemma77HorizontalShift732 j q) s =
      lemma77ScalarCenteredHorizontal j s - (((q + 1 : ℕ) : ℝ)) := by
  unfold lemma77HorizontalShift732 lemma77PositiveHorizontalIncrement
    lemma77ScalarCenteredHorizontal
  norm_num
  ring

/-- Tao's one-dimensional `G_n` weight is bounded by `2`. -/
theorem taoLemma22GaussianWeight_le_two (n : ℕ) (x : ℝ) :
    taoLemma22GaussianWeight n x ≤ 2 := by
  unfold taoLemma22GaussianWeight
  by_cases hn : n = 0
  · simp [hn]
    have hlin : Real.exp (-|x|) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact neg_nonpos.mpr (abs_nonneg x)
    nlinarith
  · simp [hn]
    have hn_pos_nat : 0 < n := Nat.pos_of_ne_zero hn
    have hn_pos : 0 < (n : ℝ) := by exact_mod_cast hn_pos_nat
    have hquad_nonneg : 0 ≤ x ^ 2 / (n : ℝ) :=
      div_nonneg (sq_nonneg x) hn_pos.le
    have hquad : Real.exp (-(x ^ 2 / (n : ℝ))) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact neg_nonpos.mpr hquad_nonneg
    have hlin : Real.exp (-|x|) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      exact neg_nonpos.mpr (abs_nonneg x)
    nlinarith

/--
Small horizontal shifts preserve the `G` profile after weakening the rate.

This is the local branch used in the `(7.32)` one-sided convolution when the
positive increment is at most half of the centered horizontal distance.
-/
theorem lemma77HorizontalConvolution732_weight_smallShift_le
    {c ch x n : ℝ} (hc : 0 < c) (hch : 0 < ch)
    (h2ch : 2 * ch ≤ c) (hn_nonneg : 0 ≤ n)
    (hsmall : n ≤ |x| / 2) (s : ℕ) :
    taoLemma22GaussianWeight (1 + s) (c * (x - n)) ≤
      taoLemma22GaussianWeight (1 + s) (ch * x) := by
  have htri : |x| ≤ |x - n| + |n| := by
    have h := abs_add_le (x - n) n
    simpa [sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using h
  have hn_abs : |n| = n := abs_of_nonneg hn_nonneg
  have hx_le : |x| ≤ 2 * |x - n| := by
    rw [hn_abs] at htri
    nlinarith [htri, hsmall]
  have hch_abs : |ch * x| = ch * |x| := by
    rw [abs_mul, abs_of_pos hch]
  have hc_abs : |c * (x - n)| = c * |x - n| := by
    rw [abs_mul, abs_of_pos hc]
  have habs : |ch * x| ≤ |c * (x - n)| := by
    rw [hch_abs, hc_abs]
    calc
      ch * |x| ≤ ch * (2 * |x - n|) :=
        mul_le_mul_of_nonneg_left hx_le hch.le
      _ = (2 * ch) * |x - n| := by ring
      _ ≤ c * |x - n| :=
        mul_le_mul_of_nonneg_right h2ch (abs_nonneg (x - n))
  have hsq_abs : |ch * x| ^ 2 ≤ |c * (x - n)| ^ 2 := by
    nlinarith [habs, abs_nonneg (ch * x), abs_nonneg (c * (x - n))]
  have hsq : (ch * x) ^ 2 ≤ (c * (x - n)) ^ 2 := by
    calc
      (ch * x) ^ 2 = |ch * x| ^ 2 := by
        rw [sq_abs]
      _ ≤ |c * (x - n)| ^ 2 := hsq_abs
      _ = (c * (x - n)) ^ 2 := by
        rw [sq_abs]
  have hN_pos : 0 < ((1 + s : ℕ) : ℝ) := by positivity
  have hquad_arg :
      (ch * x) ^ 2 / ((1 + s : ℕ) : ℝ) ≤
        (c * (x - n)) ^ 2 / ((1 + s : ℕ) : ℝ) :=
    div_le_div_of_nonneg_right hsq hN_pos.le
  have hquad :
      Real.exp (-((c * (x - n)) ^ 2 / ((1 + s : ℕ) : ℝ))) ≤
        Real.exp (-((ch * x) ^ 2 / ((1 + s : ℕ) : ℝ))) := by
    rw [Real.exp_le_exp]
    linarith
  have hlin :
      Real.exp (-|c * (x - n)|) ≤ Real.exp (-|ch * x|) := by
    rw [Real.exp_le_exp]
    linarith
  unfold taoLemma22GaussianWeight
  simp
  simpa [Nat.cast_add, Nat.cast_one] using add_le_add hquad hlin

/--
One summand in the one-sided horizontal `(7.32)` kernel convolution is bounded
by a same-center profile plus a residual geometric tail.
-/
theorem lemma77HorizontalConvolution732_weightSummand_le_profiles
    {alpha c ch : ℝ} (hc : 0 < c) (hch : 0 < ch)
    (h2ch : 2 * ch ≤ c) (h4ch : 4 * ch ≤ alpha)
    (q s : ℕ) (x : ℝ) :
    Real.exp (-(alpha * (((q + 1 : ℕ) : ℝ)))) *
        taoLemma22GaussianWeight (1 + s)
          (c * (x - (((q + 1 : ℕ) : ℝ)))) ≤
      Real.exp (-(alpha * (((q + 1 : ℕ) : ℝ)))) *
        taoLemma22GaussianWeight (1 + s) (ch * x) +
      2 * Real.exp (-((alpha / 2) * (((q + 1 : ℕ) : ℝ)))) *
        Real.exp (-(ch * |x|)) := by
  let n : ℝ := ((q + 1 : ℕ) : ℝ)
  have hn_nonneg : 0 ≤ n := by
    dsimp [n]
    positivity
  have hn_pos : 0 < n := by
    dsimp [n]
    positivity
  by_cases hsmall : n ≤ |x| / 2
  · have hweight :=
      lemma77HorizontalConvolution732_weight_smallShift_le
        hc hch h2ch hn_nonneg hsmall s
        (x := x) (n := n)
    have hmul :
        Real.exp (-(alpha * n)) *
            taoLemma22GaussianWeight (1 + s) (c * (x - n)) ≤
          Real.exp (-(alpha * n)) *
            taoLemma22GaussianWeight (1 + s) (ch * x) :=
      mul_le_mul_of_nonneg_left hweight (le_of_lt (Real.exp_pos _))
    have htail_nonneg :
        0 ≤ 2 * Real.exp (-((alpha / 2) * n)) *
          Real.exp (-(ch * |x|)) := by
      positivity
    dsimp [n] at hmul ⊢
    exact le_trans hmul (le_add_of_nonneg_right htail_nonneg)
  · have hlarge : |x| / 2 < n := lt_of_not_ge hsmall
    have hhalf_tail :
        Real.exp (-((alpha / 2) * n)) ≤ Real.exp (-(ch * |x|)) := by
      rw [Real.exp_le_exp]
      have hx_nonneg : 0 ≤ |x| := abs_nonneg x
      nlinarith [hlarge, h4ch, hch.le, hx_nonneg, hn_pos.le]
    have hweight_bound :
        taoLemma22GaussianWeight (1 + s) (c * (x - n)) ≤ 2 :=
      taoLemma22GaussianWeight_le_two (1 + s) (c * (x - n))
    have hsplit :
        Real.exp (-(alpha * n)) =
          Real.exp (-((alpha / 2) * n)) *
            Real.exp (-((alpha / 2) * n)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have hterm :
        Real.exp (-(alpha * n)) *
            taoLemma22GaussianWeight (1 + s) (c * (x - n)) ≤
          2 * Real.exp (-((alpha / 2) * n)) *
            Real.exp (-(ch * |x|)) := by
      calc
        Real.exp (-(alpha * n)) *
            taoLemma22GaussianWeight (1 + s) (c * (x - n)) ≤
          Real.exp (-(alpha * n)) * 2 :=
            mul_le_mul_of_nonneg_left hweight_bound (le_of_lt (Real.exp_pos _))
        _ = 2 * Real.exp (-((alpha / 2) * n)) *
              Real.exp (-((alpha / 2) * n)) := by
            rw [hsplit]
            ring
        _ ≤ 2 * Real.exp (-((alpha / 2) * n)) *
              Real.exp (-(ch * |x|)) := by
            exact mul_le_mul_of_nonneg_left hhalf_tail
              (by positivity)
    have hfirst_nonneg :
        0 ≤ Real.exp (-(alpha * n)) *
          taoLemma22GaussianWeight (1 + s) (ch * x) := by
      exact mul_nonneg (le_of_lt (Real.exp_pos _))
        (taoLemma22GaussianWeight_nonneg (1 + s) (ch * x))
    dsimp [n] at hterm ⊢
    exact le_trans hterm (le_add_of_nonneg_left hfirst_nonneg)

/-- Kernel-level pointwise envelope for the `(7.32)` horizontal summand. -/
theorem lemma77HorizontalConvolution732_kernelSummand_le_profiles
    {C alpha c ch : ℝ} (hC : 0 ≤ C) (hc : 0 < c) (hch : 0 < ch)
    (h2ch : 2 * ch ≤ c) (h4ch : 4 * ch ≤ alpha)
    (j : ℤ) (q s : ℕ) :
    Real.exp (-(alpha * (((q + 1 : ℕ) : ℝ)))) *
        lemma77HeightPotentialKernel C c (lemma77HorizontalShift732 j q) s ≤
      Real.exp (-(alpha * (((q + 1 : ℕ) : ℝ)))) *
        lemma77HeightPotentialKernel C ch j s +
      (2 * C) * ((1 + (s : ℝ)) ^ (-(1 / 2 : ℝ))) *
        Real.exp (-((alpha / 2) * (((q + 1 : ℕ) : ℝ)))) *
        Real.exp (-(ch * |lemma77ScalarCenteredHorizontal j s|)) := by
  let x : ℝ := lemma77ScalarCenteredHorizontal j s
  let n : ℝ := ((q + 1 : ℕ) : ℝ)
  let H : ℝ := (1 + (s : ℝ)) ^ (-(1 / 2 : ℝ))
  have hH_nonneg : 0 ≤ H := by
    dsimp [H]
    positivity
  have hfactor_nonneg : 0 ≤ C * H := mul_nonneg hC hH_nonneg
  have hcenter :
      lemma77ScalarCenteredHorizontal (lemma77HorizontalShift732 j q) s =
        x - n := by
    dsimp [x, n]
    exact lemma77HorizontalShift732_centered_eq j q s
  have hweight :=
    lemma77HorizontalConvolution732_weightSummand_le_profiles
      hc hch h2ch h4ch q s x
  have hmul := mul_le_mul_of_nonneg_left hweight hfactor_nonneg
  calc
    Real.exp (-(alpha * (((q + 1 : ℕ) : ℝ)))) *
        lemma77HeightPotentialKernel C c (lemma77HorizontalShift732 j q) s =
      (C * H) *
        (Real.exp (-(alpha * n)) *
          taoLemma22GaussianWeight (1 + s) (c * (x - n))) := by
        simp [lemma77HeightPotentialKernel, lemma77ScalarCenteredHorizontal,
          lemma77HorizontalShift732, lemma77PositiveHorizontalIncrement, H, x, n]
        ring_nf
    _ ≤ (C * H) *
        (Real.exp (-(alpha * n)) *
          taoLemma22GaussianWeight (1 + s) (ch * x) +
        2 * Real.exp (-((alpha / 2) * n)) *
          Real.exp (-(ch * |x|))) := hmul
    _ = Real.exp (-(alpha * (((q + 1 : ℕ) : ℝ)))) *
          lemma77HeightPotentialKernel C ch j s +
        (2 * C) * ((1 + (s : ℝ)) ^ (-(1 / 2 : ℝ))) *
          Real.exp (-((alpha / 2) * (((q + 1 : ℕ) : ℝ)))) *
          Real.exp (-(ch * |lemma77ScalarCenteredHorizontal j s|)) := by
        unfold lemma77HeightPotentialKernel
        dsimp [H, x, n, lemma77ScalarCenteredHorizontal]
        ring_nf

/-- The shifted one-sided horizontal kernel family is summable. -/
theorem lemma77HorizontalConvolution732Kernel_summable
    {alpha C c ch : ℝ} (hC : 0 ≤ C) (halpha : 0 < alpha)
    (hc : 0 < c) (hch : 0 < ch)
    (h2ch : 2 * ch ≤ c) (h4ch : 4 * ch ≤ alpha)
    (j : ℤ) (s : ℕ) :
    Summable (fun q : ℕ =>
      Real.exp (-(alpha * (((q + 1 : ℕ) : ℝ)))) *
        lemma77HeightPotentialKernel C c (lemma77HorizontalShift732 j q) s) := by
  let x : ℝ := lemma77ScalarCenteredHorizontal j s
  let H : ℝ := (1 + (s : ℝ)) ^ (-(1 / 2 : ℝ))
  let first : ℕ → ℝ := fun q =>
    lemma77HeightPotentialKernel C ch j s *
      Real.exp (-(alpha * (((q + 1 : ℕ) : ℝ))))
  let second : ℕ → ℝ := fun q =>
    ((2 * C) * H * Real.exp (-(ch * |x|))) *
      Real.exp (-((alpha / 2) * (((q + 1 : ℕ) : ℝ))))
  have hA_summ :
      Summable fun q : ℕ =>
        Real.exp (-(alpha * (((q + 1 : ℕ) : ℝ)))) := by
    simpa [Function.comp_def, Nat.succ_eq_add_one] using
      (lemma77ExpNegMulNat_summable halpha).comp_injective Nat.succ_injective
  have hhalf : 0 < alpha / 2 := by positivity
  have hB_summ :
      Summable fun q : ℕ =>
        Real.exp (-((alpha / 2) * (((q + 1 : ℕ) : ℝ)))) := by
    simpa [Function.comp_def, Nat.succ_eq_add_one] using
      (lemma77ExpNegMulNat_summable hhalf).comp_injective Nat.succ_injective
  have hfirst_summ : Summable first := hA_summ.mul_left _
  have hsecond_summ : Summable second := hB_summ.mul_left _
  have hupper_summ : Summable fun q : ℕ => first q + second q :=
    hfirst_summ.add hsecond_summ
  refine Summable.of_nonneg_of_le ?_ ?_ hupper_summ
  · intro q
    exact mul_nonneg (le_of_lt (Real.exp_pos _))
      (lemma77HeightPotentialKernel_nonneg hC (lemma77HorizontalShift732 j q) s)
  · intro q
    have hpoint :=
      lemma77HorizontalConvolution732_kernelSummand_le_profiles
        hC hc hch h2ch h4ch j q s
    dsimp [first, second, x, H]
    nlinarith [hpoint]

/--
Analytic one-sided horizontal convolution bound for Tao's `(7.32)` kernel.
-/
theorem lemma77HorizontalConvolution732KernelTsum_le_heightKernel
    {alpha C c ch : ℝ} (hC : 0 ≤ C) (halpha : 0 < alpha)
    (hc : 0 < c) (hch : 0 < ch)
    (h2ch : 2 * ch ≤ c) (h4ch : 4 * ch ≤ alpha)
    (j : ℤ) (s : ℕ) :
    lemma77HorizontalConvolution732KernelTsum alpha C c j s ≤
      lemma77HeightPotentialKernel
        (C * (∑' q : ℕ,
          Real.exp (-(alpha * (((q + 1 : ℕ) : ℝ))))) +
          (2 * C) * (∑' q : ℕ,
            Real.exp (-((alpha / 2) * (((q + 1 : ℕ) : ℝ))))))
        ch j s := by
  let x : ℝ := lemma77ScalarCenteredHorizontal j s
  let H : ℝ := (1 + (s : ℝ)) ^ (-(1 / 2 : ℝ))
  let A : ℝ := ∑' q : ℕ,
    Real.exp (-(alpha * (((q + 1 : ℕ) : ℝ))))
  let B : ℝ := ∑' q : ℕ,
    Real.exp (-((alpha / 2) * (((q + 1 : ℕ) : ℝ))))
  let first : ℕ → ℝ := fun q =>
    lemma77HeightPotentialKernel C ch j s *
      Real.exp (-(alpha * (((q + 1 : ℕ) : ℝ))))
  let second : ℕ → ℝ := fun q =>
    ((2 * C) * H * Real.exp (-(ch * |x|))) *
      Real.exp (-((alpha / 2) * (((q + 1 : ℕ) : ℝ))))
  have hA_summ :
      Summable fun q : ℕ =>
        Real.exp (-(alpha * (((q + 1 : ℕ) : ℝ)))) := by
    simpa [Function.comp_def, Nat.succ_eq_add_one] using
      (lemma77ExpNegMulNat_summable halpha).comp_injective Nat.succ_injective
  have hhalf : 0 < alpha / 2 := by positivity
  have hB_summ :
      Summable fun q : ℕ =>
        Real.exp (-((alpha / 2) * (((q + 1 : ℕ) : ℝ)))) := by
    simpa [Function.comp_def, Nat.succ_eq_add_one] using
      (lemma77ExpNegMulNat_summable hhalf).comp_injective Nat.succ_injective
  have hfirst_summ : Summable first := hA_summ.mul_left _
  have hsecond_summ : Summable second := hB_summ.mul_left _
  have hupper_summ : Summable fun q : ℕ => first q + second q :=
    hfirst_summ.add hsecond_summ
  have hkernel_summ :
      Summable (fun q : ℕ =>
        Real.exp (-(alpha * (((q + 1 : ℕ) : ℝ)))) *
          lemma77HeightPotentialKernel C c
            (lemma77HorizontalShift732 j q) s) :=
    lemma77HorizontalConvolution732Kernel_summable
      hC halpha hc hch h2ch h4ch j s
  have hpoint : ∀ q : ℕ,
      Real.exp (-(alpha * (((q + 1 : ℕ) : ℝ)))) *
          lemma77HeightPotentialKernel C c
            (lemma77HorizontalShift732 j q) s ≤
        first q + second q := by
    intro q
    have h :=
      lemma77HorizontalConvolution732_kernelSummand_le_profiles
        hC hc hch h2ch h4ch j q s
    dsimp [first, second, x, H]
    nlinarith [h]
  have htsum_le :
      lemma77HorizontalConvolution732KernelTsum alpha C c j s ≤
        (∑' q : ℕ, (first q + second q)) := by
    unfold lemma77HorizontalConvolution732KernelTsum
    have hkernel_summ' :
        Summable (fun q : ℕ =>
          Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
            lemma77HeightPotentialKernel C c
              (lemma77HorizontalShift732 j q) s) := by
      simpa [neg_mul] using hkernel_summ
    exact hkernel_summ'.tsum_le_tsum
      (fun i => by simpa [neg_mul] using hpoint i) hupper_summ
  have htsum_upper :
      (∑' q : ℕ, (first q + second q)) =
        (∑' q : ℕ, first q) + (∑' q : ℕ, second q) :=
    hfirst_summ.tsum_add hsecond_summ
  have hfirst_tsum :
      (∑' q : ℕ, first q) =
        lemma77HeightPotentialKernel (C * A) ch j s := by
    have hmul :
        (∑' q : ℕ, first q) =
          lemma77HeightPotentialKernel C ch j s * A := by
      dsimp [first, A]
      rw [tsum_mul_left]
    rw [hmul]
    unfold lemma77HeightPotentialKernel
    ring
  have hsecond_tsum :
      (∑' q : ℕ, second q) =
        ((2 * C) * B) * H * Real.exp (-(ch * |x|)) := by
    have hmul :
        (∑' q : ℕ, second q) =
          ((2 * C) * H * Real.exp (-(ch * |x|))) * B := by
      dsimp [second, B]
      rw [tsum_mul_left]
    rw [hmul]
    ring
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact tsum_nonneg fun q => le_of_lt (Real.exp_pos _)
  have hsecond_absorb :
      ((2 * C) * B) * H * Real.exp (-(ch * |x|)) ≤
        lemma77HeightPotentialKernel ((2 * C) * B) ch j s := by
    have hK_nonneg : 0 ≤ (2 * C) * B := by
      positivity
    dsimp [H, x]
    exact lemma77HeightPotentialKernel_absExp_le
      hK_nonneg hch hch le_rfl j s
  calc
    lemma77HorizontalConvolution732KernelTsum alpha C c j s ≤
        (∑' q : ℕ, (first q + second q)) := htsum_le
    _ = (∑' q : ℕ, first q) + (∑' q : ℕ, second q) := htsum_upper
    _ = lemma77HeightPotentialKernel (C * A) ch j s +
          ((2 * C) * B) * H * Real.exp (-(ch * |x|)) := by
        rw [hfirst_tsum, hsecond_tsum]
    _ ≤ lemma77HeightPotentialKernel (C * A) ch j s +
          lemma77HeightPotentialKernel ((2 * C) * B) ch j s :=
        add_le_add le_rfl hsecond_absorb
    _ = lemma77HeightPotentialKernel (C * A + (2 * C) * B) ch j s := by
        rw [lemma77HeightPotentialKernel_add_same_rate]
    _ = lemma77HeightPotentialKernel
        (C * (∑' q : ℕ,
          Real.exp (-(alpha * (((q + 1 : ℕ) : ℝ))))) +
          (2 * C) * (∑' q : ℕ,
            Real.exp (-((alpha / 2) * (((q + 1 : ℕ) : ℝ))))))
        ch j s := by
        dsimp [A, B]

/--
Analytic producer for Tao's horizontal smoothing estimate `(7.32)`.

The proof keeps the one-sided positive horizontal increment `q + 1`, weakens
the horizontal rate, and pays two geometric tails for the near-shift and
far-shift pieces of the `G` kernel.
-/
theorem lemma77HorizontalConvolution732Input_of_kernel_convolution
    {alpha C33 c33 : ℝ} (halpha : 0 < alpha)
    (hC33 : 0 ≤ C33) (hc33 : 0 < c33) :
    ∃ C32 c32,
      Lemma77HorizontalConvolution732Input alpha C33 c33 C32 c32 := by
  let c32 : ℝ := min (c33 / 2) (alpha / 4)
  let A : ℝ := ∑' q : ℕ,
    Real.exp (-(alpha * (((q + 1 : ℕ) : ℝ))))
  let B : ℝ := ∑' q : ℕ,
    Real.exp (-((alpha / 2) * (((q + 1 : ℕ) : ℝ))))
  let C32 : ℝ := C33 * A + (2 * C33) * B
  have hc32_pos : 0 < c32 := by
    dsimp [c32]
    exact lt_min (by positivity) (by positivity)
  have hc32_le_c33_half : c32 ≤ c33 / 2 := by
    dsimp [c32]
    exact min_le_left _ _
  have hc32_le_alpha_four : c32 ≤ alpha / 4 := by
    dsimp [c32]
    exact min_le_right _ _
  have h2c32 : 2 * c32 ≤ c33 := by
    nlinarith
  have h4c32 : 4 * c32 ≤ alpha := by
    nlinarith
  have hA_nonneg : 0 ≤ A := by
    dsimp [A]
    exact tsum_nonneg fun q => le_of_lt (Real.exp_pos _)
  have hB_nonneg : 0 ≤ B := by
    dsimp [B]
    exact tsum_nonneg fun q => le_of_lt (Real.exp_pos _)
  have hC32_nonneg : 0 ≤ C32 := by
    dsimp [C32]
    positivity
  refine ⟨C32, c32, ?_⟩
  refine
    { constants := ⟨halpha, hC32_nonneg, hc32_pos⟩
      kernel_summable := ?_
      kernel_tsum_bound := ?_ }
  · intro j s
    simpa [neg_mul] using
      lemma77HorizontalConvolution732Kernel_summable
        hC33 halpha hc33 hc32_pos h2c32 h4c32 j s
  · intro j s
    dsimp [C32, A, B, c32]
    exact lemma77HorizontalConvolution732KernelTsum_le_heightKernel
      hC33 halpha hc33 hc32_pos h2c32 h4c32 j s

/--
Tao `(7.32)` horizontal convolution mass surface after the vertical smoothing
step.

The sum is indexed by `q : ℕ` with positive horizontal increment
`j_k = q + 1`, matching Tao's `j_k ∈ ℕ+1`.
-/
def lemma77HorizontalConvolution732Mass
    (alpha beta : ℝ)
    (start : TaoSection7RenewalPoint) (j : ℤ) (s : ℕ) : ℝ :=
  ∑' q : ℕ,
    Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
      lemma77VerticalSmoothing733Mass beta start
        (lemma77HorizontalShift732 j q) s

/-- The `(7.33)` vertical-smoothing mass surface is nonnegative. -/
theorem lemma77VerticalSmoothing733Mass_nonneg
    (beta : ℝ) (start : TaoSection7RenewalPoint) (j : ℤ) (s : ℕ) :
    0 ≤ lemma77VerticalSmoothing733Mass beta start j s := by
  unfold lemma77VerticalSmoothing733Mass
  apply Finset.sum_nonneg
  intro lp _hlp
  exact mul_nonneg (le_of_lt (Real.exp_pos _))
    (lemma77HeightPotentialMass_nonneg start j (s - lp))

/--
The `(7.32)` mass convolution is summable once `(7.33)` and the horizontal
kernel summability input have been supplied.
-/
theorem lemma77HorizontalConvolution732Mass_summable_of_verticalSmoothing733Input
    {C c beta C33 c33 alpha C32 c32 : ℝ}
    (hheight : Lemma77HeightPotentialInput C c)
    (h733 : Lemma77VerticalSmoothing733Input C c beta C33 c33)
    (h732 : Lemma77HorizontalConvolution732Input alpha C33 c33 C32 c32)
    (start : TaoSection7RenewalPoint) (j : ℤ) (s : ℕ) :
    Summable (fun q : ℕ =>
      Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
        lemma77VerticalSmoothing733Mass beta start
          (lemma77HorizontalShift732 j q) s) := by
  exact Summable.of_nonneg_of_le
    (fun q => mul_nonneg (le_of_lt (Real.exp_pos _))
      (lemma77VerticalSmoothing733Mass_nonneg beta start
        (lemma77HorizontalShift732 j q) s))
    (fun q => mul_le_mul_of_nonneg_left
      (lemma77VerticalSmoothing733Mass_le_of_verticalSmoothing733Input
        hheight h733 start (lemma77HorizontalShift732 j q) s)
      (le_of_lt (Real.exp_pos _)))
    (h732.kernel_summable j s)

/-- The `(7.32)` mass convolution is bounded by the kernel convolution. -/
theorem lemma77HorizontalConvolution732Mass_le_kernelSum
    {C c beta C33 c33 alpha C32 c32 : ℝ}
    (hheight : Lemma77HeightPotentialInput C c)
    (h733 : Lemma77VerticalSmoothing733Input C c beta C33 c33)
    (h732 : Lemma77HorizontalConvolution732Input alpha C33 c33 C32 c32)
    (start : TaoSection7RenewalPoint) (j : ℤ) (s : ℕ) :
    lemma77HorizontalConvolution732Mass alpha beta start j s ≤
      lemma77HorizontalConvolution732KernelTsum alpha C33 c33 j s := by
  calc
    lemma77HorizontalConvolution732Mass alpha beta start j s
        = ∑' q : ℕ,
            Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
              lemma77VerticalSmoothing733Mass beta start
                (lemma77HorizontalShift732 j q) s := by
          rfl
    _ ≤ lemma77HorizontalConvolution732KernelTsum alpha C33 c33 j s :=
        (lemma77HorizontalConvolution732Mass_summable_of_verticalSmoothing733Input
          hheight h733 h732 start j s).tsum_le_tsum
          (fun q => mul_le_mul_of_nonneg_left
            (lemma77VerticalSmoothing733Mass_le_of_verticalSmoothing733Input
              hheight h733 start (lemma77HorizontalShift732 j q) s)
            (le_of_lt (Real.exp_pos _)))
          (h732.kernel_summable j s)

/-- Projection from `(7.33)` plus the explicit horizontal `(7.32)` input. -/
theorem lemma77HorizontalConvolution732Mass_le_of_horizontalConvolution732Input
    {C c beta C33 c33 alpha C32 c32 : ℝ}
    (hheight : Lemma77HeightPotentialInput C c)
    (h733 : Lemma77VerticalSmoothing733Input C c beta C33 c33)
    (h732 : Lemma77HorizontalConvolution732Input alpha C33 c33 C32 c32)
    (start : TaoSection7RenewalPoint) (j : ℤ) (s : ℕ) :
    lemma77HorizontalConvolution732Mass alpha beta start j s ≤
      lemma77HeightPotentialKernel C32 c32 j s :=
  le_trans
    (lemma77HorizontalConvolution732Mass_le_kernelSum
      hheight h733 h732 start j s)
    (h732.kernel_tsum_bound j s)

end TaoSection7Lemma77

end

end Tao
end Erdos1135
