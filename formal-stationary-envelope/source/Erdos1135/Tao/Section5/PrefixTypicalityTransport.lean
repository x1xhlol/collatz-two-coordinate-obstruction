import Erdos1135.Tao.Section5.PassTypicalFailure

/-!
# Section 5 Prefix Typicality Transport

This leaf transports the closed-prefix failure estimate at the common horizon
`n0` to every shorter iid Geom(2) list.  The atypical-list event records exact
length explicitly: without that support condition, failure of the length
clause need not produce a bad prefix.
-/

namespace Erdos1135
namespace Tao

noncomputable section

/-- Exact-length lists that fail the closed Section 5 typicality condition. -/
def taoSection5SupportedAtypicalEvent (B q : ℕ) : Set (List ℕ+) :=
  {as | as.length = q ∧ ¬ taoSection5TypicalTuple B q as}

@[simp] theorem taoSection5SupportedAtypicalEvent_zero (B : ℕ) :
    taoSection5SupportedAtypicalEvent B 0 = ∅ := by
  have hslack : 0 ≤ taoSection5TypicalSlack B := by
    unfold taoSection5TypicalSlack
    apply Real.rpow_nonneg
    by_cases hB : B = 0
    · simp [hB]
    · exact Real.log_nonneg (by
        exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hB))
  ext as
  simp [taoSection5SupportedAtypicalEvent, taoSection5TypicalTuple,
    taoTupleWeight, hslack]

private theorem taoGeom2CenteredListWeight_take_eq_of_length
    {as : List ℕ+} {q j : ℕ} (hlen : as.length = q) (hj : j ≤ q) :
    taoGeom2CenteredListWeight (as.take j) =
      (taoTupleWeight (as.take j) : ℝ) - 2 * (j : ℝ) := by
  unfold taoGeom2CenteredListWeight
  rw [List.length_take, hlen, Nat.min_eq_left hj]

/-- On an exact-length list, failure of closed typicality is exactly failure
at one positive prefix. -/
theorem taoSection5_not_typical_iff_prefixBad_of_length
    {B q : ℕ} {as : List ℕ+} (hlen : as.length = q)
    (hslack : 0 < taoSection5TypicalSlack B) :
    ¬ taoSection5TypicalTuple B q as ↔
      as ∈ taoGeom2PrefixBadEvent (taoSection5TypicalSlack B) q := by
  constructor
  · intro hnot
    by_contra hnotBad
    apply hnot
    refine ⟨hlen, ?_⟩
    intro j hj
    by_cases hj0 : j = 0
    · subst j
      simp [taoTupleWeight, hslack.le]
    · let k : Fin q := ⟨j - 1, by omega⟩
      have hknot :
          ¬ taoSection5TypicalSlack B <
            |taoGeom2CenteredListWeight (as.take (k.1 + 1))| := by
        intro hk
        apply hnotBad
        exact ⟨k, hk⟩
      have hkj : k.1 + 1 = j := by
        dsimp [k]
        omega
      rw [hkj] at hknot
      rw [taoGeom2CenteredListWeight_take_eq_of_length hlen hj] at hknot
      exact not_lt.mp hknot
  · intro hbad htyp
    rcases hbad with ⟨j, hjbad⟩
    have hj : j.1 + 1 ≤ q := by omega
    have hbound := htyp.2 (j.1 + 1) hj
    rw [taoGeom2CenteredListWeight_take_eq_of_length hlen hj] at hjbad
    exact (not_lt_of_ge hbound) hjbad

/-- The explicitly supported atypical event lies in the corresponding
positive-prefix bad event. -/
theorem taoSection5SupportedAtypicalEvent_subset_prefixBad
    {B q : ℕ} (hslack : 0 < taoSection5TypicalSlack B) :
    taoSection5SupportedAtypicalEvent B q ⊆
      taoGeom2PrefixBadEvent (taoSection5TypicalSlack B) q := by
  intro as has
  exact (taoSection5_not_typical_iff_prefixBad_of_length has.1 hslack).mp has.2

/-- Pulling a shorter positive-prefix bad event back along `List.take` lies in
the longer positive-prefix bad event.  This inclusion needs no support
hypothesis because both events only inspect positive prefixes. -/
theorem preimage_taoGeom2PrefixBadEvent_take_subset
    {lambda : ℝ} {q n : ℕ} (hqn : q ≤ n) :
    (fun as : List ℕ+ => as.take q) ⁻¹'
        taoGeom2PrefixBadEvent lambda q ⊆
      taoGeom2PrefixBadEvent lambda n := by
  intro as has
  rcases has with ⟨j, hj⟩
  let k : Fin n := ⟨j.1, j.2.trans_le hqn⟩
  refine ⟨k, ?_⟩
  have hjq : j.1 + 1 ≤ q := by omega
  simpa only [k, List.take_take, Nat.min_eq_left hjq] using hj

/-- Prefix-bad outer mass is monotone in the iid list horizon. -/
theorem geom2PNatListPMF_prefixBad_mono
    {lambda : ℝ} {q n : ℕ} (hqn : q ≤ n) :
    (geom2PNatListPMF q).toOuterMeasure
        (taoGeom2PrefixBadEvent lambda q) ≤
      (geom2PNatListPMF n).toOuterMeasure
        (taoGeom2PrefixBadEvent lambda n) := by
  calc
    (geom2PNatListPMF q).toOuterMeasure
        (taoGeom2PrefixBadEvent lambda q) =
      ((geom2PNatListPMF n).map (fun as => as.take q)).toOuterMeasure
        (taoGeom2PrefixBadEvent lambda q) := by
          rw [geom2PNatListPMF_map_take_low_eq_of_le hqn]
    _ = (geom2PNatListPMF n).toOuterMeasure
          ((fun as : List ℕ+ => as.take q) ⁻¹'
            taoGeom2PrefixBadEvent lambda q) := by
      rw [PMF.toOuterMeasure_map_apply]
    _ ≤ (geom2PNatListPMF n).toOuterMeasure
          (taoGeom2PrefixBadEvent lambda n) :=
      (geom2PNatListPMF n).toOuterMeasure.mono
        (preimage_taoGeom2PrefixBadEvent_take_subset hqn)

/-- Real-valued form of prefix-bad horizon monotonicity. -/
theorem geom2PNatListPMF_prefixBad_toReal_mono
    {lambda : ℝ} {q n : ℕ} (hqn : q ≤ n) :
    ((geom2PNatListPMF q).toOuterMeasure
        (taoGeom2PrefixBadEvent lambda q)).toReal ≤
      ((geom2PNatListPMF n).toOuterMeasure
        (taoGeom2PrefixBadEvent lambda n)).toReal := by
  have hfinite :
      (geom2PNatListPMF n).toOuterMeasure
          (taoGeom2PrefixBadEvent lambda n) ≠ ⊤ := by
    apply ne_of_lt
    calc
      (geom2PNatListPMF n).toOuterMeasure
          (taoGeom2PrefixBadEvent lambda n) ≤
          (geom2PNatListPMF n).toOuterMeasure Set.univ :=
        (geom2PNatListPMF n).toOuterMeasure.mono (Set.subset_univ _)
      _ = 1 :=
        ((geom2PNatListPMF n).toOuterMeasure_apply_eq_one_iff Set.univ).2
          (Set.subset_univ _)
      _ < ⊤ := ENNReal.one_lt_top
  exact ENNReal.toReal_mono hfinite (geom2PNatListPMF_prefixBad_mono hqn)

/-- Under the length-`q` iid law, raw failure of typicality has exactly the
same mass as the explicitly supported atypical event. -/
theorem geom2PNatListPMF_notTypical_eq_supportedAtypical
    (B q : ℕ) :
    (geom2PNatListPMF q).toOuterMeasure
        {as | ¬ taoSection5TypicalTuple B q as} =
      (geom2PNatListPMF q).toOuterMeasure
        (taoSection5SupportedAtypicalEvent B q) := by
  apply (geom2PNatListPMF q).toOuterMeasure_apply_eq_of_inter_support_eq
  ext as
  simp only [Set.mem_inter_iff, Set.mem_setOf_eq,
    taoSection5SupportedAtypicalEvent]
  constructor
  · rintro ⟨hnot, hsupp⟩
    exact ⟨⟨geom2PNatListPMF_support_length_eq hsupp, hnot⟩, hsupp⟩
  · rintro ⟨⟨_hlen, hnot⟩, hsupp⟩
    exact ⟨hnot, hsupp⟩

/-- Native support-aware transport from raw shorter-horizon non-typicality to
the common horizon bad event. -/
theorem geom2PNatListPMF_notTypical_le_horizonBad
    {B q : ℕ} (hq : q ≤ taoSection5N0 B)
    (hslack : 0 < taoSection5TypicalSlack B) :
    (geom2PNatListPMF q).toOuterMeasure
        {as | ¬ taoSection5TypicalTuple B q as} ≤
      (geom2PNatListPMF (taoSection5N0 B)).toOuterMeasure
        (taoSection5ClosedPrefixBadEvent B) := by
  rw [geom2PNatListPMF_notTypical_eq_supportedAtypical]
  calc
    (geom2PNatListPMF q).toOuterMeasure
        (taoSection5SupportedAtypicalEvent B q) ≤
      (geom2PNatListPMF q).toOuterMeasure
        (taoGeom2PrefixBadEvent (taoSection5TypicalSlack B) q) :=
      (geom2PNatListPMF q).toOuterMeasure.mono
        (taoSection5SupportedAtypicalEvent_subset_prefixBad hslack)
    _ ≤ (geom2PNatListPMF (taoSection5N0 B)).toOuterMeasure
        (taoGeom2PrefixBadEvent
          (taoSection5TypicalSlack B) (taoSection5N0 B)) :=
      geom2PNatListPMF_prefixBad_mono hq
    _ = (geom2PNatListPMF (taoSection5N0 B)).toOuterMeasure
        (taoSection5ClosedPrefixBadEvent B) := rfl

/-- The stored horizon-`n0` failure estimate controls every shorter
positive-prefix bad event. -/
theorem TaoSection5PassTypicalFailureFacts.prefixBad_le_delta
    {B : ℕ} (facts : TaoSection5PassTypicalFailureFacts B)
    {q : ℕ} (hq : q ≤ taoSection5N0 B) :
    ((geom2PNatListPMF q).toOuterMeasure
        (taoGeom2PrefixBadEvent (taoSection5TypicalSlack B) q)).toReal ≤
      taoSection5PowerInteriorDelta B := by
  exact (geom2PNatListPMF_prefixBad_toReal_mono hq).trans facts.ideal_le

/-- The same estimate controls exact-length lists that are not closed
typical.  The support clause is intentionally visible in the event. -/
theorem TaoSection5PassTypicalFailureFacts.supportedAtypical_le_delta
    {B : ℕ} (facts : TaoSection5PassTypicalFailureFacts B)
    {q : ℕ} (hq : q ≤ taoSection5N0 B) :
    ((geom2PNatListPMF q).toOuterMeasure
        (taoSection5SupportedAtypicalEvent B q)).toReal ≤
      taoSection5PowerInteriorDelta B := by
  have hfinite :
      (geom2PNatListPMF q).toOuterMeasure
          (taoGeom2PrefixBadEvent (taoSection5TypicalSlack B) q) ≠ ⊤ := by
    apply ne_of_lt
    calc
      (geom2PNatListPMF q).toOuterMeasure
          (taoGeom2PrefixBadEvent (taoSection5TypicalSlack B) q) ≤
          (geom2PNatListPMF q).toOuterMeasure Set.univ :=
        (geom2PNatListPMF q).toOuterMeasure.mono (Set.subset_univ _)
      _ = 1 :=
        ((geom2PNatListPMF q).toOuterMeasure_apply_eq_one_iff Set.univ).2
          (Set.subset_univ _)
      _ < ⊤ := ENNReal.one_lt_top
  calc
    ((geom2PNatListPMF q).toOuterMeasure
        (taoSection5SupportedAtypicalEvent B q)).toReal ≤
      ((geom2PNatListPMF q).toOuterMeasure
        (taoGeom2PrefixBadEvent (taoSection5TypicalSlack B) q)).toReal :=
      ENNReal.toReal_mono hfinite
        ((geom2PNatListPMF q).toOuterMeasure.mono
          (taoSection5SupportedAtypicalEvent_subset_prefixBad facts.slack_pos))
    _ ≤ taoSection5PowerInteriorDelta B := facts.prefixBad_le_delta hq

/-- Consumer-facing bound for the raw complement of closed typicality.  Its
proof is support-aware even though the support clause is absent from the
event syntax. -/
theorem TaoSection5PassTypicalFailureFacts.short_notTypical_le_delta
    {B : ℕ} (facts : TaoSection5PassTypicalFailureFacts B)
    {q : ℕ} (hq : q ≤ taoSection5N0 B) :
    ((geom2PNatListPMF q).toOuterMeasure
        {as | ¬ taoSection5TypicalTuple B q as}).toReal ≤
      taoSection5PowerInteriorDelta B := by
  rw [geom2PNatListPMF_notTypical_eq_supportedAtypical]
  exact facts.supportedAtypical_le_delta hq

/-- Eventually, the support-aware shorter-horizon atypical estimate holds
uniformly for every `q ≤ n0`. -/
theorem eventually_geom2PNatListPMF_supportedAtypical_le_delta :
    ∀ᶠ B : ℕ in Filter.atTop, ∀ q ≤ taoSection5N0 B,
      ((geom2PNatListPMF q).toOuterMeasure
          (taoSection5SupportedAtypicalEvent B q)).toReal ≤
        taoSection5PowerInteriorDelta B := by
  filter_upwards [eventually_taoSection5PassTypicalFailureFacts]
    with B facts
  intro q hq
  exact facts.supportedAtypical_le_delta hq

/-- Eventually, raw shorter-horizon non-typicality has mass at most `delta`,
uniformly for every `q ≤ n0`. -/
theorem eventually_geom2PNatListPMF_notTypical_le_delta :
    ∀ᶠ B : ℕ in Filter.atTop, ∀ q ≤ taoSection5N0 B,
      ((geom2PNatListPMF q).toOuterMeasure
          {as | ¬ taoSection5TypicalTuple B q as}).toReal ≤
        taoSection5PowerInteriorDelta B := by
  filter_upwards [eventually_taoSection5PassTypicalFailureFacts]
    with B facts
  intro q hq
  exact facts.short_notTypical_le_delta hq

end

end Tao
end Erdos1135
