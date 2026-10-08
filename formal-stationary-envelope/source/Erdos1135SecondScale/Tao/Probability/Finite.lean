/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Probability.Distributions.Uniform
import Mathlib.Data.ENNReal.BigOperators
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite PMF Conventions For Tao's Syracuse Route

This module fixes project-local finite probability notation and Tao's full-L1 total-variation
convention.  It intentionally contains no Syracuse-specific random variables, Fourier analysis, or
renewal estimates.
-/

open scoped BigOperators

namespace Erdos1135SecondScale
namespace Tao

/-- Probability of an event under a finite PMF, represented as a real finite sum. -/
noncomputable def pmfProb {α : Type*} [Fintype α] (p : PMF α) (E : Set α) : ℝ := by
  classical
  exact ∑ a, if a ∈ E then (p a).toReal else 0

/-- Real-valued expectation of a finite PMF random variable. -/
noncomputable def pmfExpectation
    {α : Type*} [Fintype α] (p : PMF α) (X : α → ℝ) : ℝ :=
  ∑ a, (p a).toReal * X a

/-- Tao's total-variation convention: full L1 distance, not half L1. -/
noncomputable def taoTV {α : Type*} [Fintype α] (p q : PMF α) : ℝ :=
  ∑ a, |(p a).toReal - (q a).toReal|

theorem pmf_sum_toReal {α : Type*} [Fintype α] (p : PMF α) :
    (∑ a, (p a).toReal) = 1 := by
  have htsum := congrArg ENNReal.toReal (PMF.tsum_coe p)
  rw [ENNReal.tsum_toReal_eq (PMF.apply_ne_top p)] at htsum
  rw [tsum_fintype] at htsum
  simpa using htsum

theorem pmfProb_univ {α : Type*} [Fintype α] (p : PMF α) :
    pmfProb p Set.univ = 1 := by
  classical
  simp [pmfProb, pmf_sum_toReal p]

theorem pmfProb_empty {α : Type*} [Fintype α] (p : PMF α) :
    pmfProb p ∅ = 0 := by
  classical
  simp [pmfProb]

theorem pmfProb_compl {α : Type*} [Fintype α] (p : PMF α) (E : Set α) :
    pmfProb p Eᶜ = 1 - pmfProb p E := by
  classical
  unfold pmfProb
  rw [← pmf_sum_toReal p, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro a _ha
  by_cases ha : a ∈ E <;> simp [ha]

theorem pmfProb_nonneg {α : Type*} [Fintype α] (p : PMF α) (E : Set α) :
    0 ≤ pmfProb p E := by
  classical
  unfold pmfProb
  exact Finset.sum_nonneg fun a _ => by
    by_cases ha : a ∈ E <;> simp [ha]

theorem pmfProb_eq_toOuterMeasure_toReal {α : Type*} [Fintype α]
    (p : PMF α) (E : Set α) :
    pmfProb p E = (p.toOuterMeasure E).toReal := by
  classical
  rw [pmfProb, PMF.toOuterMeasure_apply_fintype]
  rw [ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro a _ha
    by_cases hmem : a ∈ E <;> simp [hmem]
  · intro a _ha
    by_cases hmem : a ∈ E
    · simp [hmem, PMF.apply_ne_top]
    · simp [hmem]

theorem pmfProb_mono {α : Type*} [Fintype α]
    (p : PMF α) {E F : Set α} (hEF : E ⊆ F) :
    pmfProb p E ≤ pmfProb p F := by
  classical
  unfold pmfProb
  exact Finset.sum_le_sum fun a _ => by
    by_cases haE : a ∈ E
    · have haF : a ∈ F := hEF haE
      simp [haE, haF]
    · by_cases haF : a ∈ F
      · simp [haE, haF]
      · simp [haE, haF]

theorem pmfExpectation_mono {α : Type*} [Fintype α]
    (p : PMF α) {X Y : α → ℝ}
    (hXY : ∀ a, X a ≤ Y a) :
    pmfExpectation p X ≤ pmfExpectation p Y := by
  unfold pmfExpectation
  exact Finset.sum_le_sum fun a _ha =>
    mul_le_mul_of_nonneg_left (hXY a) ENNReal.toReal_nonneg

theorem pmfProb_union_le_add {α : Type*} [Fintype α]
    (p : PMF α) (E F : Set α) :
    pmfProb p (E ∪ F) ≤ pmfProb p E + pmfProb p F := by
  classical
  unfold pmfProb
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun a _ => by
    by_cases haE : a ∈ E
    · by_cases haF : a ∈ F
      · simp [haE, haF]
      · simp [haE, haF]
    · by_cases haF : a ∈ F
      · simp [haE, haF]
      · simp [haE, haF]

/--
Finite-PMF Markov inequality for a nonnegative real random variable.

This is intentionally elementary and finite-sum based, matching `pmfProb`.
It is the probability algebra needed by source-specific `FSlack` packets; it
does not prove any source moment estimate by itself.
-/
theorem pmfProb_gt_le_of_expect_le_mul {α : Type*} [Fintype α]
    (p : PMF α) (X : α → ℝ) {cutoff budget : ℝ}
    (hX_nonneg : ∀ a, 0 ≤ X a)
    (hcutoff : 0 < cutoff)
    (hmean : pmfExpectation p X ≤ cutoff * budget) :
    pmfProb p {a | cutoff < X a} ≤ budget := by
  classical
  let E : Set α := {a | cutoff < X a}
  have hcut_prob_le_expect :
      cutoff * pmfProb p E ≤ pmfExpectation p X := by
    calc
      cutoff * pmfProb p E =
          ∑ a, cutoff * (if a ∈ E then (p a).toReal else 0) := by
            simp [pmfProb, Finset.mul_sum]
      _ ≤ ∑ a, (p a).toReal * X a := by
            exact Finset.sum_le_sum fun a _ => by
              by_cases ha : a ∈ E
              · have hle : cutoff ≤ X a := le_of_lt ha
                have hp_nonneg : 0 ≤ (p a).toReal := ENNReal.toReal_nonneg
                have hmul :
                    (p a).toReal * cutoff ≤ (p a).toReal * X a :=
                  mul_le_mul_of_nonneg_left hle hp_nonneg
                simpa [E, ha, mul_comm, mul_left_comm, mul_assoc] using hmul
              · have hterm_nonneg : 0 ≤ (p a).toReal * X a :=
                  mul_nonneg ENNReal.toReal_nonneg (hX_nonneg a)
                simpa [E, ha] using hterm_nonneg
      _ = pmfExpectation p X := rfl
  have hcut_prob_le_budget :
      cutoff * pmfProb p E ≤ cutoff * budget :=
    le_trans hcut_prob_le_expect hmean
  nlinarith [hcut_prob_le_budget, hcutoff]

/--
Finite union bound for a cover by an indexed finite family of events.

The cover is intentionally expressed by an existential over the finite index
set, which is the shape used by source event decompositions.
-/
theorem pmfProb_le_finset_sum_of_subset_exists
    {Ω ι : Type*} [Fintype Ω] [DecidableEq ι]
    (μ : PMF Ω) (I : Finset ι) (event : ι → Set Ω)
    (largeEvent : Set Ω)
    (hcover :
      ∀ ω, ω ∈ largeEvent → ∃ i, i ∈ I ∧ ω ∈ event i) :
    pmfProb μ largeEvent ≤ I.sum fun i => pmfProb μ (event i) := by
  classical
  revert largeEvent
  refine Finset.induction_on I ?empty ?insert
  · intro largeEvent hcover
    have hlarge_empty : largeEvent = ∅ := by
      ext ω
      constructor
      · intro hω
        rcases hcover ω hω with ⟨i, hi, _hωi⟩
        simp at hi
      · intro hω
        cases hω
    simp [hlarge_empty, pmfProb_empty]
  · intro i I hi_not_mem ih largeEvent hcover
    let restEvent : Set Ω := largeEvent \ event i
    have hlarge_subset :
        largeEvent ⊆ event i ∪ restEvent := by
      intro ω hω
      by_cases hωi : ω ∈ event i
      · exact Or.inl hωi
      · exact Or.inr ⟨hω, hωi⟩
    have hrest_cover :
        ∀ ω, ω ∈ restEvent → ∃ j, j ∈ I ∧ ω ∈ event j := by
      intro ω hω
      rcases hcover ω hω.1 with ⟨j, hj, hωj⟩
      rcases Finset.mem_insert.mp hj with rfl | hjI
      · exact False.elim (hω.2 hωj)
      · exact ⟨j, hjI, hωj⟩
    have hrest :
        pmfProb μ restEvent ≤ I.sum fun j => pmfProb μ (event j) :=
      ih restEvent hrest_cover
    calc
      pmfProb μ largeEvent
          ≤ pmfProb μ (event i ∪ restEvent) :=
            pmfProb_mono μ hlarge_subset
      _ ≤ pmfProb μ (event i) + pmfProb μ restEvent :=
            pmfProb_union_le_add μ (event i) restEvent
      _ ≤ pmfProb μ (event i) +
            I.sum fun j => pmfProb μ (event j) := by
            exact add_le_add le_rfl hrest
      _ = (insert i I).sum fun j => pmfProb μ (event j) := by
            simp [Finset.sum_insert, hi_not_mem]

theorem pmfProb_diff_le_of_diff_subset {α : Type*} [Fintype α]
    (p : PMF α) {E Bad Good : Set α} (h : E \ Bad ⊆ Good) :
    pmfProb p E - pmfProb p Bad ≤ pmfProb p Good := by
  have hE : E ⊆ Bad ∪ Good := by
    intro a haE
    by_cases haBad : a ∈ Bad
    · exact Or.inl haBad
    · exact Or.inr (h ⟨haE, haBad⟩)
  calc
    pmfProb p E - pmfProb p Bad ≤ pmfProb p (Bad ∪ Good) - pmfProb p Bad := by
      exact sub_le_sub_right (pmfProb_mono p hE) (pmfProb p Bad)
    _ ≤ pmfProb p Good := by
      linarith [pmfProb_union_le_add p Bad Good]

/-- A finite source can compare arbitrary target events after a PMF map.
The subset hypothesis stays on source preimages, so the target need not be
finite or carry any additional measurable structure. -/
theorem pmfMapOuterMass_diff_le_of_preimage_diff_subset
    {α β : Type*} [Fintype α]
    (p : PMF α) (f : α → β) {E Bad Good : Set β}
    (h : f ⁻¹' E \ f ⁻¹' Bad ⊆ f ⁻¹' Good) :
    ((p.map f).toOuterMeasure E).toReal -
        ((p.map f).toOuterMeasure Bad).toReal ≤
      ((p.map f).toOuterMeasure Good).toReal := by
  rw [PMF.toOuterMeasure_map_apply, PMF.toOuterMeasure_map_apply,
    PMF.toOuterMeasure_map_apply]
  rw [← pmfProb_eq_toOuterMeasure_toReal,
    ← pmfProb_eq_toOuterMeasure_toReal,
    ← pmfProb_eq_toOuterMeasure_toReal]
  exact pmfProb_diff_le_of_diff_subset p h

theorem pmfProb_map_preimage {α β : Type*} [Fintype α] [Fintype β]
    (p : PMF α) (f : α → β) (E : Set β) :
    pmfProb (p.map f) E = pmfProb p (f ⁻¹' E) := by
  rw [pmfProb_eq_toOuterMeasure_toReal, pmfProb_eq_toOuterMeasure_toReal]
  rw [PMF.toOuterMeasure_map_apply]

/--
Finite event probability as a pushed-forward singleton atom.

Unlike `pmfProb_map_preimage`, this does not require the target type to be
finite; it only sums over the finite source carrier.
-/
theorem pmfProb_singleton_eq_map_apply_toReal
    {α β : Type*} [Fintype α]
    (p : PMF α) (f : α → β) (b : β) :
    pmfProb p {a | f a = b} = ((p.map f) b).toReal := by
  classical
  rw [pmfProb, PMF.map_apply]
  rw [ENNReal.tsum_toReal_eq]
  · rw [tsum_fintype]
    apply Finset.sum_congr rfl
    intro a _ha
    have hiff : (a ∈ {a | f a = b}) ↔ b = f a := by
      constructor
      · intro h
        exact h.symm
      · intro h
        exact h.symm
    by_cases hb : b = f a
    · rw [if_pos (hiff.mpr hb), if_pos hb]
    · rw [if_neg (fun hmem => hb (hiff.mp hmem)), if_neg hb]
      rfl
  · intro a
    by_cases hb : b = f a <;>
      simp [hb, PMF.apply_ne_top p a]

/--
Global finite fiber masses determine a pushed-forward PMF.

The hypothesis is intentionally stated over the whole source PMF `p`: it is
not a conditional or atom-normalized source law.
-/
theorem pmf_eq_map_of_fiber_prob_toReal
    {α β : Type*} [Fintype α]
    {p : PMF α} {q : PMF β} {f : α → β}
    (h :
      ∀ b,
        (q b).toReal = pmfProb p {a | f a = b}) :
    q = p.map f := by
  classical
  apply PMF.ext
  intro b
  exact
    (ENNReal.toReal_eq_toReal_iff'
      (PMF.apply_ne_top q b)
      (PMF.apply_ne_top (p.map f) b)).mp
      ((h b).trans (pmfProb_singleton_eq_map_apply_toReal p f b))

theorem pmfProb_uniformOfFintype {α : Type*} [Fintype α] [Nonempty α]
    (E : Set α) [Fintype E] :
    pmfProb (PMF.uniformOfFintype α) E =
      (Fintype.card E : ℝ) / (Fintype.card α : ℝ) := by
  rw [pmfProb_eq_toOuterMeasure_toReal]
  rw [PMF.toOuterMeasure_uniformOfFintype_apply]
  simp [ENNReal.toReal_div, ENNReal.toReal_natCast]

theorem pmfProb_uniformOfFintype_finset {α : Type*} [Fintype α] [Nonempty α]
    (S : Finset α) :
    pmfProb (PMF.uniformOfFintype α) {a | a ∈ S} =
      (S.card : ℝ) / (Fintype.card α : ℝ) := by
  classical
  rw [pmfProb_uniformOfFintype]
  simp

theorem taoTV_nonneg {α : Type*} [Fintype α] (p q : PMF α) :
    0 ≤ taoTV p q := by
  unfold taoTV
  exact Finset.sum_nonneg fun _a _ => abs_nonneg _

theorem taoTV_self {α : Type*} [Fintype α] (p : PMF α) :
    taoTV p p = 0 := by
  simp [taoTV]

theorem taoTV_comm {α : Type*} [Fintype α] (p q : PMF α) :
    taoTV p q = taoTV q p := by
  simp [taoTV, abs_sub_comm]

/-- Triangle inequality for Tao's full-L1 convention on finite PMFs. -/
theorem taoTV_triangle {α : Type*} [Fintype α] (p q r : PMF α) :
    taoTV p r ≤ taoTV p q + taoTV q r := by
  unfold taoTV
  rw [← Finset.sum_add_distrib]
  exact Finset.sum_le_sum fun a _ha => by
    have hsplit :
        (p a).toReal - (r a).toReal =
          ((p a).toReal - (q a).toReal) +
            ((q a).toReal - (r a).toReal) := by
      ring
    rw [hsplit]
    exact abs_add_le _ _

/-- Finite Hahn identity for the project full-L1 convention. The positive
event is oriented from `q` to `p`, so its discrepancy is nonnegative and the
full L1 distance is exactly twice that discrepancy. -/
theorem taoTV_eq_two_mul_positive_event_discrepancy
    {α : Type*} [Fintype α] (p q : PMF α) :
    taoTV p q =
      2 * (pmfProb p {a | (q a).toReal ≤ (p a).toReal} -
        pmfProb q {a | (q a).toReal ≤ (p a).toReal}) := by
  classical
  let E : Set α := {a | (q a).toReal ≤ (p a).toReal}
  change taoTV p q = 2 * (pmfProb p E - pmfProb q E)
  have hEvent :
      pmfProb p E - pmfProb q E =
        ∑ a, if a ∈ E then (p a).toReal - (q a).toReal else 0 := by
    rw [pmfProb, pmfProb, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _ha
    by_cases ha : a ∈ E <;> simp [ha]
  have hTotal :
      (∑ a, ((p a).toReal - (q a).toReal)) = 0 := by
    rw [Finset.sum_sub_distrib, pmf_sum_toReal p,
      pmf_sum_toReal q, sub_self]
  unfold taoTV
  calc
    (∑ a, |(p a).toReal - (q a).toReal|) =
        ∑ a, (2 * (if a ∈ E then
          (p a).toReal - (q a).toReal else 0) -
          ((p a).toReal - (q a).toReal)) := by
      apply Finset.sum_congr rfl
      intro a _ha
      by_cases ha : (q a).toReal ≤ (p a).toReal
      · simp only [E, Set.mem_setOf_eq, if_pos ha,
          abs_of_nonneg (sub_nonneg.mpr ha)]
        ring
      · have hap : (p a).toReal ≤ (q a).toReal := le_of_not_ge ha
        simp only [E, Set.mem_setOf_eq, if_neg ha,
          abs_of_nonpos (sub_nonpos.mpr hap)]
        ring
    _ = 2 * (∑ a, if a ∈ E then
          (p a).toReal - (q a).toReal else 0) -
        ∑ a, ((p a).toReal - (q a).toReal) := by
      rw [Finset.sum_sub_distrib, Finset.mul_sum]
    _ = 2 * (pmfProb p E - pmfProb q E) := by
      rw [hTotal, sub_zero, ← hEvent]

/-- A uniform one-sided finite-event discrepancy controls project full L1
with the single Hahn factor `2`. -/
theorem taoTV_le_two_mul_of_forall_pmfProb_sub_le
    {α : Type*} [Fintype α] (p q : PMF α) {ε : ℝ}
    (h : ∀ E : Set α, pmfProb p E - pmfProb q E ≤ ε) :
    taoTV p q ≤ 2 * ε := by
  rw [taoTV_eq_two_mul_positive_event_discrepancy]
  exact mul_le_mul_of_nonneg_left (h _) (by norm_num)

/-- Absolute event discrepancy form of the finite Hahn bound. -/
theorem taoTV_le_two_mul_of_event_discrepancy
    {α : Type*} [Fintype α] (p q : PMF α) {ε : ℝ}
    (h : ∀ E : Set α, |pmfProb p E - pmfProb q E| ≤ ε) :
    taoTV p q ≤ 2 * ε := by
  apply taoTV_le_two_mul_of_forall_pmfProb_sub_le p q
  intro E
  exact (le_abs_self _).trans (h E)

/-- Universal cap for the project full-L1 distance between finite PMFs. -/
theorem taoTV_le_two {α : Type*} [Fintype α] (p q : PMF α) :
    taoTV p q ≤ 2 := by
  simpa using
    (taoTV_le_two_mul_of_forall_pmfProb_sub_le p q (ε := 1) fun E => by
      have hp := pmfProb_mono p (show E ⊆ Set.univ from Set.subset_univ E)
      rw [pmfProb_univ] at hp
      linarith [pmfProb_nonneg q E])

theorem abs_pmfProb_sub_le_taoTV {α : Type*} [Fintype α]
    (p q : PMF α) (E : Set α) :
    |pmfProb p E - pmfProb q E| ≤ taoTV p q := by
  classical
  have hdiff :
      pmfProb p E - pmfProb q E =
        ∑ a, if a ∈ E then (p a).toReal - (q a).toReal else 0 := by
    rw [pmfProb, pmfProb, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro a _ha
    by_cases hmem : a ∈ E <;> simp [hmem]
  rw [hdiff]
  calc
    |∑ a, if a ∈ E then (p a).toReal - (q a).toReal else 0|
        ≤ ∑ a, |if a ∈ E then (p a).toReal - (q a).toReal else 0| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ taoTV p q := by
          unfold taoTV
          exact Finset.sum_le_sum fun a _ => by
            by_cases hmem : a ∈ E
            · simp [hmem]
            · simp [hmem, abs_nonneg]

theorem pmfProb_sub_taoTV_le_pmfProb {α : Type*} [Fintype α]
    (p q : PMF α) (E : Set α) :
    pmfProb p E - taoTV p q ≤ pmfProb q E := by
  have h := abs_pmfProb_sub_le_taoTV p q E
  have hle : pmfProb p E - pmfProb q E ≤ taoTV p q := (abs_le.mp h).2
  linarith

theorem pmfProb_le_pmfProb_add_taoTV {α : Type*} [Fintype α]
    (p q : PMF α) (E : Set α) :
    pmfProb q E ≤ pmfProb p E + taoTV p q := by
  have h := abs_pmfProb_sub_le_taoTV p q E
  have hle : -taoTV p q ≤ pmfProb p E - pmfProb q E := (abs_le.mp h).1
  linarith

end Tao
end Erdos1135SecondScale
