/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.TerminalTotalCancellation
import Erdos1135Predecessor.ND.Probability.Geom2FiniteTwoEventTail

namespace Erdos1135Predecessor

namespace ND

namespace PositiveDensity

open scoped BigOperators Topology

noncomputable section

private noncomputable def oneLawIndicator (P : Prop) : ℝ := by
  classical
  exact if P then 1 else 0

private theorem abs_oneLawIndicator_le_one (P : Prop) :
    |oneLawIndicator P| ≤ 1 := by
  classical
  by_cases hP : P <;> simp [oneLawIndicator, hP]

def ndFiniteFirstHitAt
    {Omega : Type*} (I : Finset ℕ) (Hit : ℕ → Omega → Prop)
    (r : ℕ) (omega : Omega) : Prop :=
  r ∈ I ∧ Hit r omega ∧
    ∀ s ∈ I, s < r → ¬ Hit s omega

def ndFiniteAnyHit
    {Omega : Type*} (I : Finset ℕ) (Hit : ℕ → Omega → Prop)
    (omega : Omega) : Prop :=
  ∃ r ∈ I, Hit r omega

private theorem exists_unique_ndFiniteFirstHitAt
    {Omega : Type*} (I : Finset ℕ) (Hit : ℕ → Omega → Prop)
    {omega : Omega} (h : ndFiniteAnyHit I Hit omega) :
    ∃! r, ndFiniteFirstHitAt I Hit r omega := by
  classical
  let P : ℕ → Prop := fun r => r ∈ I ∧ Hit r omega
  have hP : ∃ r, P r := by
    simpa only [P, ndFiniteAnyHit] using h
  let r0 := Nat.find hP
  have hr0 : P r0 := Nat.find_spec hP
  refine ⟨r0, ?_, ?_⟩
  · refine ⟨hr0.1, hr0.2, ?_⟩
    intro s hsI hsr0 hsHit
    exact (Nat.find_min hP hsr0) ⟨hsI, hsHit⟩
  · intro r hr
    have hr0le : r0 ≤ r :=
      Nat.find_min' hP ⟨hr.1, hr.2.1⟩
    by_contra hne
    have hr0ne : r0 ≠ r := fun h => hne h.symm
    have hr0lt : r0 < r := lt_of_le_of_ne hr0le hr0ne
    exact hr.2.2 r0 hr0.1 hr0lt hr0.2

private theorem ndPMFWeightedExpectation_finset_sum_bounded
    {Omega ι : Type*} (p : PMF Omega) (S : Finset ι)
    (phi : ι → Omega → ℝ) (H : ι → ℝ)
    (hH : ∀ i ∈ S, 0 ≤ H i)
    (hphi : ∀ i ∈ S, ∀ omega, |phi i omega| ≤ H i) :
    ndPMFWeightedExpectation p (fun omega => ∑ i ∈ S, phi i omega) =
      ∑ i ∈ S, ndPMFWeightedExpectation p (phi i) := by
  classical
  unfold ndPMFWeightedExpectation
  calc
    (∑' omega, (p omega).toReal * ∑ i ∈ S, phi i omega) =
        ∑' omega, ∑ i ∈ S, (p omega).toReal * phi i omega := by
      apply tsum_congr
      intro omega
      rw [Finset.mul_sum]
    _ = ∑ i ∈ S, ∑' omega, (p omega).toReal * phi i omega := by
      rw [Summable.tsum_finsetSum]
      intro i hi
      exact summable_pmf_toReal_mul_of_abs_le
        p (phi i) (H i) (hH i hi) (hphi i hi)

private theorem ndPMFWeightedExpectation_indicator_eq_outerMass
    {Omega : Type*} (p : PMF Omega) (P : Omega → Prop) :
    ndPMFWeightedExpectation p (fun omega => oneLawIndicator (P omega)) =
      (p.toOuterMeasure {omega | P omega}).toReal := by
  classical
  unfold ndPMFWeightedExpectation
  rw [Tao.pmfOuterMass_toReal_eq_tsum_indicator]
  apply tsum_congr
  intro omega
  by_cases hP : P omega <;>
    simp [oneLawIndicator, Set.indicator, hP]

theorem sum_firstHit_pmfEventMass_eq_anyHit
    {Omega : Type*} (p : PMF Omega) (I : Finset ℕ)
    (Hit : ℕ → Omega → Prop) :
    (∑ r ∈ I,
        (p.toOuterMeasure
          {omega | ndFiniteFirstHitAt I Hit r omega}).toReal) =
      (p.toOuterMeasure {omega | ndFiniteAnyHit I Hit omega}).toReal := by
  classical
  have hpoint : (fun omega =>
      ∑ r ∈ I, oneLawIndicator (ndFiniteFirstHitAt I Hit r omega)) =
      fun omega => oneLawIndicator (ndFiniteAnyHit I Hit omega) := by
    funext omega
    by_cases hAny : ndFiniteAnyHit I Hit omega
    · rcases exists_unique_ndFiniteFirstHitAt I Hit hAny with
        ⟨r0, hr0, hunique⟩
      have hsum :
          (∑ r ∈ I,
            oneLawIndicator (ndFiniteFirstHitAt I Hit r omega)) =
            oneLawIndicator (ndFiniteFirstHitAt I Hit r0 omega) := by
        apply Finset.sum_eq_single r0
        · intro r hrI hne
          have hnot : ¬ ndFiniteFirstHitAt I Hit r omega := by
            intro hr
            exact hne (hunique r hr)
          simp [oneLawIndicator, hnot]
        · intro hnotMem
          exact (hnotMem hr0.1).elim
      rw [hsum]
      simp [oneLawIndicator, hAny, hr0]
    · have hnot : ∀ r ∈ I, ¬ ndFiniteFirstHitAt I Hit r omega := by
        intro r hrI hr
        exact hAny ⟨r, hrI, hr.2.1⟩
      rw [show oneLawIndicator (ndFiniteAnyHit I Hit omega) = 0 by
        simp [oneLawIndicator, hAny]]
      apply Finset.sum_eq_zero
      intro r hr
      simp [oneLawIndicator, hnot r hr]
  calc
    (∑ r ∈ I,
        (p.toOuterMeasure
          {omega | ndFiniteFirstHitAt I Hit r omega}).toReal) =
        ndPMFWeightedExpectation p (fun omega =>
          ∑ r ∈ I, oneLawIndicator
            (ndFiniteFirstHitAt I Hit r omega)) := by
      rw [ndPMFWeightedExpectation_finset_sum_bounded
        p I
        (fun r omega => oneLawIndicator
          (ndFiniteFirstHitAt I Hit r omega))
        (fun _ => 1) (by simp) (by
          intro r _hr omega
          exact abs_oneLawIndicator_le_one _)]
      apply Finset.sum_congr rfl
      intro r _hr
      rw [ndPMFWeightedExpectation_indicator_eq_outerMass]
    _ = ndPMFWeightedExpectation p
          (fun omega => oneLawIndicator (ndFiniteAnyHit I Hit omega)) := by
      rw [hpoint]
    _ = (p.toOuterMeasure
          {omega | ndFiniteAnyHit I Hit omega}).toReal :=
      ndPMFWeightedExpectation_indicator_eq_outerMass _ _

end

end PositiveDensity

end ND

end Erdos1135Predecessor
