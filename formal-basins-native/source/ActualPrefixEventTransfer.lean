import SyracuseLandingLowerBound
import TaoLocalPrefixConcentration

namespace CollatzClockAudit
open Erdos1135.Tao

/-- One event on the starting point controls every actual valuation prefix. -/
def actualPrefixGoodEvent (n : ℕ) (E : ℝ) : Set TaoOddNat :=
  {q | ∀ j ≤ n,
    |(taoTupleWeight (syracuseValuationPNatList j q.1 q.2) : ℝ) - 2 * j| ≤ E}

/-- A deterministic local clock event, including existence of a genuine hit. -/
def localClockGoodEvent (B n : ℕ) (E : ℝ) : Set TaoOddNat :=
  {q | ∃ τ ≤ n, syracuseFirstHitAtMost B q.1 τ ∧
    |(τ : ℝ) - clockCenter B q.1| ≤ 5 * (E + 1)}

/-- The landing remains above the square-root scale and occurs by time `n`. -/
def largeLandingGoodEvent (B n : ℕ) : Set TaoOddNat :=
  {q | ∃ τ ≤ n, syracuseFirstHitAtMost B q.1 τ ∧
    (B : ℝ) ^ (1 / 2 : ℝ) < ((syracuse^[τ]) q.1 : ℝ)}

theorem actual_prefix_centered_take (q : TaoOddNat) {j n : ℕ} (hj : j ≤ n) :
    taoGeom2CenteredListWeight ((syracuseValuationPNatList n q.1 q.2).take j) =
      (taoTupleWeight (syracuseValuationPNatList j q.1 q.2) : ℝ) - 2 * j := by
  rw [syracuseValuationPNatList_take_of_le q.2 hj]
  simp [taoGeom2CenteredListWeight, syracuseValuationPNatList_length]

theorem actual_prefix_bad_iff (q : TaoOddNat) (n : ℕ) {E : ℝ} (hE : 0 ≤ E) :
    syracuseValuationPNatList n q.1 q.2 ∈ taoGeom2PrefixBadEvent E n ↔
      q ∉ actualPrefixGoodEvent n E := by
  constructor
  · rintro ⟨j, hj⟩ hgood
    rw [actual_prefix_centered_take q (by omega)] at hj
    exact not_lt_of_ge (hgood (j.1 + 1) (by omega)) hj
  · intro hn
    change ¬ ∀ j ≤ n,
      |(taoTupleWeight (syracuseValuationPNatList j q.1 q.2) : ℝ) - 2 * j| ≤ E at hn
    push Not at hn
    obtain ⟨j, hjn, hj⟩ := hn
    have hjpos : 0 < j := by
      by_contra hz
      have hj0 : j = 0 := by omega
      subst j
      simp [syracuseValuationPNatList, taoTupleWeight, not_lt_of_ge hE] at hj
    refine ⟨⟨j - 1, by omega⟩, ?_⟩
    have hjid : j - 1 + 1 = j := by omega
    change E < |taoGeom2CenteredListWeight
      ((syracuseValuationPNatList n q.1 q.2).take (j - 1 + 1))|
    rw [hjid, actual_prefix_centered_take q hjn]
    exact hj

theorem actual_prefix_bad_mass (μ : PMF TaoOddNat) (n : ℕ) {E : ℝ} (hE : 0 ≤ E) :
    (taoProp19ActualValuationLaw μ n).toOuterMeasure (taoGeom2PrefixBadEvent E n) =
      μ.toOuterMeasure (actualPrefixGoodEvent n E)ᶜ := by
  unfold taoProp19ActualValuationLaw
  rw [PMF.toOuterMeasure_map_apply]
  congr 1
  ext q
  exact actual_prefix_bad_iff q n hE

/-- Any event forced by the full good prefix inherits the sharp finite
concentration error, on the actual source support. -/
theorem source_event_bad_probability_le (μ : PMF TaoOddNat) {n : ℕ} (hn : 0 < n)
    {E err : ℝ} (hE : 0 < E) (G : Set TaoOddNat)
    (hTV : taoProp19ValuationTV μ n ≤ err)
    (hgood : ∀ q ∈ μ.support, q ∈ actualPrefixGoodEvent n E → q ∈ G) :
    (μ.toOuterMeasure Gᶜ).toReal ≤
      (n : ℝ) * (2 * Real.exp (-min (E ^ 2 / (32 * (n : ℝ))) (E / 8))) + err := by
  have hmono : μ.toOuterMeasure Gᶜ ≤ μ.toOuterMeasure (actualPrefixGoodEvent n E)ᶜ := by
    apply μ.toOuterMeasure_mono
    intro q hq
    exact fun hp => hq.1 (hgood q hq.2 hp)
  have hp := actual_prefix_bad_probability_le μ hn hE hTV
  rw [actual_prefix_bad_mass μ n hE.le] at hp
  apply le_trans (ENNReal.toReal_mono ?_ hmono) hp
  apply ne_of_lt
  calc
    μ.toOuterMeasure (actualPrefixGoodEvent n E)ᶜ ≤ μ.toOuterMeasure Set.univ :=
      μ.toOuterMeasure.mono (Set.subset_univ _)
    _ = 1 := (μ.toOuterMeasure_apply_eq_one_iff Set.univ).2 (Set.subset_univ _)
    _ < ⊤ := ENNReal.one_lt_top

end CollatzClockAudit

#print axioms CollatzClockAudit.actual_prefix_centered_take
#print axioms CollatzClockAudit.actual_prefix_bad_iff
#print axioms CollatzClockAudit.actual_prefix_bad_mass
#print axioms CollatzClockAudit.source_event_bad_probability_le
