import LadderClockLimit
import ActualPrefixEvents
import FixedLadderGoodCumulative

set_option autoImplicit false

open Filter Topology MeasureTheory Preorder
open scoped ENNReal

namespace CollatzCylinderPacking.Arithmetic.InverseDoob
open Erdos1135.Tao CollatzClockAudit CollatzCanonical.NativeTao
open CollatzCanonical.RawOccupation CollatzCanonical.DirichletAbelian

noncomputable def ladderPrefixDepth (n : ℕ) (M : ℝ) (I : ℕ) : ℕ :=
  (Finset.range (I + 1)).sup (fun j => lastVisitDepthBound n ⌊clockScale M j⌋₊)

theorem lastVisitDepthBound_le_ladderPrefixDepth {n I j : ℕ} {M : ℝ} (hj : j ≤ I) :
    lastVisitDepthBound n ⌊clockScale M j⌋₊ ≤ ladderPrefixDepth n M I :=
  Finset.le_sup (f := fun j => lastVisitDepthBound n ⌊clockScale M j⌋₊)
    (Finset.mem_range.mpr (by omega))

theorem finiteLadderClockEvent_prefix_congr {n I : ℕ} {M : ℝ} {x y : ℕ → ℕ}
    (hxy : ∀ k ≤ ladderPrefixDepth n M I, x k = y k) :
    x ∈ finiteLadderClockEvent n M I ↔ y ∈ finiteLadderClockEvent n M I := by
  have he (j : ℕ) (hj : j ≤ I) : ladderLastClock n M x j = ladderLastClock n M y j :=
    lastVisitIndex_prefix_congr (fun k hk =>
      hxy k (hk.trans (lastVisitDepthBound_le_ladderPrefixDepth hj)))
  constructor
  · intro hx j hj
    simpa only [← he j hj] using hx j hj
  · intro hy j hj
    simpa only [he j hj] using hy j hj

def finiteLadderBadPrefixes (n : ℕ) (M : ℝ) (I : ℕ) :
    Set (PrefixIndex (ladderPrefixDepth n M I)) :=
  {p | prefixExtend (ladderPrefixDepth n M I) p ∉ finiteLadderClockEvent n M I}

theorem finiteLadderClockEvent_compl_eq_prefixEvent (n : ℕ) (M : ℝ) (I : ℕ) :
    (finiteLadderClockEvent n M I)ᶜ =
      prefixEvent (ladderPrefixDepth n M I) (finiteLadderBadPrefixes n M I) := by
  ext x
  change (x ∉ finiteLadderClockEvent n M I) ↔
    (prefixExtend (ladderPrefixDepth n M I)
      (frestrictLe (ladderPrefixDepth n M I) x) ∉ finiteLadderClockEvent n M I)
  apply not_congr
  apply finiteLadderClockEvent_prefix_congr
  intro k hk
  simp only [prefixExtend_apply _ hk, frestrictLe_apply]

theorem measurableSet_finiteLadderClockEvent (n : ℕ) (M : ℝ) (I : ℕ) :
    MeasurableSet (finiteLadderClockEvent n M I) := by
  apply MeasurableSet.of_compl
  rw [finiteLadderClockEvent_compl_eq_prefixEvent]
  exact measurableSet_prefixEvent _ _

theorem oddEventWeight_odd_mask (G : Set TaoOddNat) :
    (fun q => if q % 2 = 1 then oddEventWeight G q else 0) = oddEventWeight G := by
  funext q
  by_cases hq : q % 2 = 1
  · simp only [if_pos hq]
  · have hnot : ¬ ∃ hn : Odd q, (⟨q, hn⟩ : TaoOddNat) ∈ G := by
      rintro ⟨hn, _⟩
      exact hq (Nat.odd_iff.mp hn)
    simp only [if_neg hq, oddEventWeight, if_neg hnot]

theorem logarithmicCumulative_oddEventWeight (G : Set TaoOddNat) (t : ℝ) :
    logarithmicCumulative (oddEventWeight G) t =
      oddLogarithmicCumulative (oddEventWeight G) t := by
  unfold oddLogarithmicCumulative
  rw [oddEventWeight_odd_mask]

theorem finiteLadderClock_failure_probability_of_source_good
    {n I : ℕ} {M C c : ℝ} (hn : 0 < n) (hu : n % 3 ≠ 0)
    (hnodd : n % 2 = 1) (hnp : Nonperiodic n)
    (hC : 0 ≤ C) (hc : 0 < c) (hM : 1 < M) (hMe : Real.exp 1 ≤ M)
    (facts : ∀ i, RealClockScaleFacts C c (clockScale M i))
    (hgood : ∀ (p : PrefixIndex (ladderPrefixDepth n M I)) (q : TaoOddNat),
      ValidPrefix n (ladderPrefixDepth n M I) (prefixExtend (ladderPrefixDepth n M I) p) →
      (∃ A, iterate A q.1 = prefixExtend (ladderPrefixDepth n M I) p
        (ladderPrefixDepth n M I)) →
      q ∈ fixedLadderGoodEvent M hM.le I →
      prefixExtend (ladderPrefixDepth n M I) p ∈ finiteLadderClockEvent n M I) :
    pathLaw n (finiteLadderClockEvent n M I)ᶜ ≤
      ENNReal.ofReal (2 * clockLadderFailureEnvelope C c M * taoAlpha / actualFirstHitDensity n) := by
  classical
  let E := finiteLadderBadPrefixes n M I
  let bad := oddEventWeight (fixedLadderGoodEvent M hM.le I)ᶜ
  have hD : 0 < actualFirstHitDensity n := (actual_weighted_density_positive_iff_unit hn).mpr hu
  have hdom (p : PrefixIndex (ladderPrefixDepth n M I)) (hp : p ∈ E) (q : ℕ) :
      prefixSourceWeight n (ladderPrefixDepth n M I) p q ≤ bad q := by
    by_cases hs : prefixSourceWeight n (ladderPrefixDepth n M I) p q = 0
    · rw [hs]
      exact (oddEventWeight_bounds _ q).1
    · obtain ⟨hv, hhit⟩ := prefixSourceWeight_nonzero hs
      have hq : q % 2 = 1 := by
        by_contra he
        apply hs
        simp only [prefixSourceWeight, if_pos (And.intro hv hhit), oddFirstHitWeight, if_neg he]
      have hqo : Odd q := Nat.odd_iff.mpr hq
      have hbad : (⟨q, hqo⟩ : TaoOddNat) ∉ fixedLadderGoodEvent M hM.le I := by
        intro hg
        exact hp (hgood p ⟨q, hqo⟩ hv hhit hg)
      have hb : bad q = 1 := by
        change oddEventWeight _ (⟨q, hqo⟩ : TaoOddNat).1 = 1
        rw [oddEventWeight_of_odd, Set.indicator_of_mem hbad]
      rw [hb]
      simp only [prefixSourceWeight, if_pos (And.intro hv hhit), oddFirstHitWeight, if_pos hq]
      exact (firstHitWeight_bounds _ _).2
  have hbound : ∀ ε : ℝ, 0 < ε → ∀ᶠ t : ℝ in atTop,
      (2 / actualFirstHitDensity n) * (logarithmicCumulative bad t / t) ≤
        2 * clockLadderFailureEnvelope C c M * taoAlpha / actualFirstHitDensity n + ε := by
    intro ε hε
    filter_upwards [fixedLadderGoodEvent_failure_normalized_cumulative hC hc hM hMe facts I
      (mul_pos hε hD)] with t ht
    have hh := div_le_div_of_nonneg_right ht hD.le
    rw [← logarithmicCumulative_oddEventWeight] at hh
    change (2 * logarithmicCumulative bad t / t) / actualFirstHitDensity n ≤ _ at hh
    have he : (2 * clockLadderFailureEnvelope C c M * taoAlpha + ε * actualFirstHitDensity n) /
        actualFirstHitDensity n =
        2 * clockLadderFailureEnvelope C c M * taoAlpha / actualFirstHitDensity n + ε := by
      rw [add_div, mul_div_cancel_right₀ _ hD.ne']
    rw [he] at hh
    convert hh using 1
    ring
  have h := actual_prefix_event_probability_le_of_eventual_add hn hu hnodd hnp E bad
    (fun q => (oddEventWeight_bounds _ q).1) hdom hbound
  rw [← finiteLadderClockEvent_compl_eq_prefixEvent] at h
  exact (ENNReal.le_ofReal_iff_toReal_le (measure_ne_top _ _)
    (ENNReal.toReal_nonneg.trans h)).mpr h

#print axioms finiteLadderClockEvent_compl_eq_prefixEvent
#print axioms finiteLadderClock_failure_probability_of_source_good

end CollatzCylinderPacking.Arithmetic.InverseDoob
