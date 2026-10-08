import Erdos1135.Tao.Renewal.Lemma79R2Aggregation
import Erdos1135.Tao.Renewal.Lemma79CutoffStatistic

/-!
# Lemma 7.9 Key-Dependent Master Transport

This proof leaf transports key masses and key-weighted cutoff statistics
between an original iid Hold law and any longer iid master.  Every result is
returned to the original law before countable key aggregation.
-/

namespace Erdos1135
namespace Tao

noncomputable section

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

/-- Native PMF expectations pull back exactly along a longer iid Hold prefix. -/
theorem lemma79_holdList_pmfENNExpectation_comp_take_eq_of_le
    {J B : ℕ} (hJB : J ≤ B) (F : List TaoSection7RenewalPoint -> ENNReal) :
    lemma79PMFENNExpectation (taoSection7HoldListPMF B)
        (F ∘ fun full => full.take J) =
      lemma79PMFENNExpectation (taoSection7HoldListPMF J) F := by
  calc
    lemma79PMFENNExpectation (taoSection7HoldListPMF B)
        (F ∘ fun full => full.take J) =
        lemma79PMFENNExpectation
          ((taoSection7HoldListPMF B).map fun full => full.take J) F :=
      (lemma79PMFENNExpectation_map
        (taoSection7HoldListPMF B) (fun full => full.take J) F).symm
    _ = _ := by rw [taoSection7HoldListPMF_map_take_eq_of_le hJB]

/-- Event masses pull back exactly along a longer iid Hold prefix. -/
theorem lemma79_holdList_preimage_mass_eq_of_le
    {J B : ℕ} (hJB : J ≤ B)
    (Event : Set (List TaoSection7RenewalPoint)) :
    (taoSection7HoldListPMF B).toOuterMeasure
        ((fun full => full.take J) ⁻¹' Event) =
      (taoSection7HoldListPMF J).toOuterMeasure Event := by
  calc
    (taoSection7HoldListPMF B).toOuterMeasure
        ((fun full => full.take J) ⁻¹' Event) =
        ((taoSection7HoldListPMF B).map
          fun full => full.take J).toOuterMeasure Event :=
      (PMF.toOuterMeasure_map_apply
        (fun full : List TaoSection7RenewalPoint => full.take J)
        (taoSection7HoldListPMF B) Event).symm
    _ = _ := by rw [taoSection7HoldListPMF_map_take_eq_of_le hJB]

/-- The semantic first-entry key is unchanged after retaining its complete
cutoff prefix. -/
theorem lemma79HoldPathHeadKey_take
    (start : TaoSection7RenewalPoint)
    (family : Set TaoSection7Triangle) (C : ℕ)
    (full : List TaoSection7RenewalPoint) :
    lemma79HoldPathHeadKey start family C full =
      lemma79HoldPathHeadKey start family C (full.take C) := by
  exact lemma79HoldPathInclusiveTraceHeadKey_take

/-- The native repaired cutoff statistic is unchanged after retaining its
complete cutoff prefix. -/
theorem lemma79HoldPathCutoffTailMomentENN_take
    {n C R : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {start : TaoSection7RenewalPoint}
    {full : List TaoSection7RenewalPoint}
    {family : Set TaoSection7Triangle}
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family) :
    lemma79HoldPathCutoffTailMomentENN
        start family n xi epsilon C R full =
      lemma79HoldPathCutoffTailMomentENN
        start family n xi epsilon C R (full.take C) := by
  unfold lemma79HoldPathCutoffTailMomentENN
  rw [lemma79HoldPathCutoffTailMoment_take hpair]

/-- A semantic key atom has exactly the same mass under the original law and
its preimage in any longer iid Hold master. -/
theorem lemma79_holdList_keyAtom_mass_eq_of_le
    {J B : ℕ} (hJB : J ≤ B)
    (start : TaoSection7RenewalPoint)
    (family : Set TaoSection7Triangle)
    (key : Option (ℕ × TaoSection7Point)) :
    (taoSection7HoldListPMF B).toOuterMeasure
        (lemma79KeyAtom Set.univ
          (lemma79HoldPathHeadKey start family J) key) =
      (taoSection7HoldListPMF J).toOuterMeasure
        (lemma79KeyAtom Set.univ
          (lemma79HoldPathHeadKey start family J) key) := by
  let Event :=
    lemma79KeyAtom Set.univ
      (lemma79HoldPathHeadKey start family J) key
  have hatom :
      lemma79KeyAtom Set.univ
          (lemma79HoldPathHeadKey start family J) key =
        (fun full : List TaoSection7RenewalPoint => full.take J) ⁻¹' Event := by
    ext full
    simp only [Event, lemma79KeyAtom, Set.mem_ofPred_eq, Set.mem_univ,
      true_and, Set.mem_preimage]
    rw [lemma79HoldPathHeadKey_take]
  calc
    (taoSection7HoldListPMF B).toOuterMeasure
        (lemma79KeyAtom Set.univ
          (lemma79HoldPathHeadKey start family J) key) =
        (taoSection7HoldListPMF B).toOuterMeasure
          ((fun full : List TaoSection7RenewalPoint => full.take J) ⁻¹' Event) :=
      congrArg (taoSection7HoldListPMF B).toOuterMeasure hatom
    _ = (taoSection7HoldListPMF J).toOuterMeasure Event :=
      lemma79_holdList_preimage_mass_eq_of_le hJB Event
    _ = _ := rfl

/-- A key-weighted repaired cutoff statistic has exactly the same expectation
under the original law and any longer iid Hold master. -/
theorem lemma79_holdList_keyAtom_cutoffTailMomentENN_expectation_eq_of_le
    {J B n R : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hJB : J ≤ B)
    (start : TaoSection7RenewalPoint)
    (family : Set TaoSection7Triangle)
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (key : Option (ℕ × TaoSection7Point)) :
    lemma79PMFENNExpectation
        (taoSection7HoldListPMF B)
        ((lemma79KeyAtom Set.univ
          (lemma79HoldPathHeadKey start family J) key).indicator
            (lemma79HoldPathCutoffTailMomentENN
              start family n xi epsilon J R)) =
      lemma79PMFENNExpectation
        (taoSection7HoldListPMF J)
        ((lemma79KeyAtom Set.univ
          (lemma79HoldPathHeadKey start family J) key).indicator
            (lemma79HoldPathCutoffTailMomentENN
              start family n xi epsilon J R)) := by
  let Event :=
    lemma79KeyAtom Set.univ
      (lemma79HoldPathHeadKey start family J) key
  let F :=
    Event.indicator
      (lemma79HoldPathCutoffTailMomentENN
        start family n xi epsilon J R)
  calc
    lemma79PMFENNExpectation
        (taoSection7HoldListPMF B)
        (Event.indicator
          (lemma79HoldPathCutoffTailMomentENN
            start family n xi epsilon J R)) =
        lemma79PMFENNExpectation
          (taoSection7HoldListPMF B)
          (F ∘ fun full => full.take J) := by
      apply congrArg (lemma79PMFENNExpectation (taoSection7HoldListPMF B))
      funext full
      have hmem : full ∈ Event ↔ full.take J ∈ Event := by
        simp only [Event, lemma79KeyAtom, Set.mem_ofPred_eq, Set.mem_univ,
          true_and]
        rw [lemma79HoldPathHeadKey_take]
      have hstat :
          lemma79HoldPathCutoffTailMomentENN
              start family n xi epsilon J R full =
            lemma79HoldPathCutoffTailMomentENN
              start family n xi epsilon J R (full.take J) :=
        lemma79HoldPathCutoffTailMomentENN_take
          (n := n) (C := J) (R := R) (xi := xi)
          (epsilon := epsilon) (start := start) (full := full)
          (family := family) hpair
      change
        Event.indicator
            (lemma79HoldPathCutoffTailMomentENN
              start family n xi epsilon J R) full =
          Event.indicator
            (lemma79HoldPathCutoffTailMomentENN
              start family n xi epsilon J R) (full.take J)
      by_cases hfull : full ∈ Event
      · rw [Set.indicator_of_mem hfull,
          Set.indicator_of_mem (hmem.mp hfull)]
        exact hstat
      · have hshort : full.take J ∉ Event := fun h => hfull (hmem.mpr h)
        simp [Set.indicator, hfull, hshort]
    _ = lemma79PMFENNExpectation (taoSection7HoldListPMF J) F :=
      lemma79_holdList_pmfENNExpectation_comp_take_eq_of_le hJB F
    _ = _ := rfl

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end

end Tao
end Erdos1135
