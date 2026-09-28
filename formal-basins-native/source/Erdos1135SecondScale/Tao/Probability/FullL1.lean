/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Probability.Finite
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Topology.Algebra.InfiniteSum.Ring

/-!
# Full L1 distance for probability mass functions

This module extends the finite `taoTV` convention to arbitrary PMF carriers
and records the neutral summability, event-comparison, and deterministic
finite-map APIs needed by the Proposition 1.9 truncation route.
-/

open scoped BigOperators

namespace Erdos1135SecondScale
namespace Tao

/-- Tao's full-L1 distance for PMFs on possibly infinite codomains. -/
noncomputable def taoPMFFullL1 {α : Type*} (p q : PMF α) : ℝ :=
  ∑' a : α, |(p a).toReal - (q a).toReal|

theorem taoPMF_summable_toReal {α : Type*} (p : PMF α) :
    Summable fun a : α => (p a).toReal := by
  refine ENNReal.summable_toReal ?_
  rw [PMF.tsum_coe p]
  norm_num

theorem taoPMF_map_apply_toReal_tsum {α β : Type*} [DecidableEq β]
    (p : PMF α) (f : α → β) (b : β) :
    ((p.map f) b).toReal =
      ∑' a : α, if b = f a then (p a).toReal else 0 := by
  classical
  rw [PMF.map_apply, ENNReal.tsum_toReal_eq]
  · apply tsum_congr
    intro a
    by_cases h : b = f a <;> simp [h]
  · intro a
    by_cases h : b = f a <;> simp [h, PMF.apply_ne_top p a]

theorem taoPMFFullL1_summable {α : Type*} (p q : PMF α) :
    Summable fun a : α => |(p a).toReal - (q a).toReal| := by
  exact ((taoPMF_summable_toReal p).sub (taoPMF_summable_toReal q)).abs

private theorem abs_tsum_subtype_sub_le_tsum_abs
    {α : Type*} (f g : α → ℝ) (E : Set α)
    (hf : Summable f) (hg : Summable g) :
    |(∑' a : E, f a) - ∑' a : E, g a| ≤
      ∑' a : α, |f a - g a| := by
  let fE : E → ℝ := fun a => f a
  let gE : E → ℝ := fun a => g a
  have hfE : Summable fE := by
    simpa [fE] using hf.subtype E
  have hgE : Summable gE := by
    simpa [gE] using hg.subtype E
  calc
    |(∑' a : E, f a) - ∑' a : E, g a| =
        |∑' a : E, (fE a - gE a)| := by
      rw [hfE.tsum_sub hgE]
    _ ≤ ∑' a : E, |fE a - gE a| := by
      simpa only [Real.norm_eq_abs] using
        norm_tsum_le_tsum_norm ((hfE.sub hgE).norm)
    _ ≤ ∑' a : α, |f a - g a| := by
      simpa [fE, gE] using
        Summable.tsum_subtype_le (fun a : α => |f a - g a|) E
          (fun _ => abs_nonneg _) ((hf.sub hg).abs)

/-- Real mass of an arbitrary PMF event as the sum of its indicated atoms. -/
theorem pmfOuterMass_toReal_eq_tsum_indicator
    {α : Type*} (p : PMF α) (E : Set α) :
    (p.toOuterMeasure E).toReal =
      ∑' a : α, E.indicator (fun a => (p a).toReal) a := by
  classical
  rw [PMF.toOuterMeasure_apply, ENNReal.tsum_toReal_eq]
  · apply tsum_congr
    intro a
    by_cases h : a ∈ E <;> simp [Set.indicator, h]
  · intro a
    by_cases h : a ∈ E <;>
      simp [Set.indicator, h, PMF.apply_ne_top p a]

/-- Subtype form of arbitrary PMF event atomization. -/
theorem pmfOuterMass_toReal_eq_tsum_subtype
    {α : Type*} (p : PMF α) (E : Set α) :
    (p.toOuterMeasure E).toReal = ∑' a : E, (p a).toReal := by
  rw [pmfOuterMass_toReal_eq_tsum_indicator]
  exact (tsum_subtype E (fun a : α => (p a).toReal)).symm

/-- An event-mass discrepancy is bounded by Tao's full-L1 distance on any
PMF carrier.  The coefficient is `1`, with no half-TV normalization. -/
theorem abs_pmfOuterMass_sub_le_taoPMFFullL1
    {α : Type*} (p q : PMF α) (E : Set α) :
    |(p.toOuterMeasure E).toReal - (q.toOuterMeasure E).toReal| ≤
      taoPMFFullL1 p q := by
  rw [pmfOuterMass_toReal_eq_tsum_subtype,
    pmfOuterMass_toReal_eq_tsum_subtype]
  exact abs_tsum_subtype_sub_le_tsum_abs
    (fun a : α => (p a).toReal) (fun a : α => (q a).toReal) E
    (taoPMF_summable_toReal p) (taoPMF_summable_toReal q)

/-- One-sided arbitrary-carrier event comparison in the project full-L1
convention. -/
theorem pmfOuterMass_le_add_taoPMFFullL1
    {α : Type*} (p q : PMF α) (E : Set α) :
    (p.toOuterMeasure E).toReal ≤
      (q.toOuterMeasure E).toReal + taoPMFFullL1 p q := by
  have hdiff := (le_abs_self
    ((p.toOuterMeasure E).toReal - (q.toOuterMeasure E).toReal)).trans
    (abs_pmfOuterMass_sub_le_taoPMFFullL1 p q E)
  linarith

/-- Consume a supplied full-L1 bound in the arbitrary-carrier event
comparison. -/
theorem pmfOuterMass_le_add_of_taoPMFFullL1_le
    {α : Type*} (p q : PMF α) (E : Set α) {ε : ℝ}
    (h : taoPMFFullL1 p q ≤ ε) :
    (p.toOuterMeasure E).toReal ≤ (q.toOuterMeasure E).toReal + ε :=
  (pmfOuterMass_le_add_taoPMFFullL1 p q E).trans
    (by linarith)

theorem taoPMFFullL1_eq_taoTV {α : Type*} [Fintype α]
    (p q : PMF α) :
    taoPMFFullL1 p q = taoTV p q := by
  rw [taoPMFFullL1, taoTV, tsum_fintype]

/-- Deterministic maps contract Tao's full-L1 convention on finite carriers. -/
theorem taoTV_map_le {α β : Type*} [Fintype α] [Fintype β]
    (p q : PMF α) (f : α → β) :
    taoTV (p.map f) (q.map f) ≤ taoTV p q := by
  classical
  unfold taoTV
  calc
    (∑ b : β, |((p.map f) b).toReal - ((q.map f) b).toReal|) =
        ∑ b : β, |∑ a : α,
          if b = f a then (p a).toReal - (q a).toReal else 0| := by
      apply Finset.sum_congr rfl
      intro b _hb
      rw [taoPMF_map_apply_toReal_tsum, taoPMF_map_apply_toReal_tsum,
        tsum_fintype, tsum_fintype, ← Finset.sum_sub_distrib]
      apply congrArg abs
      apply Finset.sum_congr rfl
      intro a _ha
      by_cases h : b = f a <;> simp [h]
    _ ≤ ∑ b : β, ∑ a : α,
          |if b = f a then (p a).toReal - (q a).toReal else 0| := by
      exact Finset.sum_le_sum fun b _hb => Finset.abs_sum_le_sum_abs _ _
    _ = ∑ a : α, |(p a).toReal - (q a).toReal| := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _ha
      rw [Finset.sum_eq_single (f a)]
      · simp
      · intro b _hb hba
        simp [hba]
      · exact fun h => False.elim (h (Finset.mem_univ (f a)))

end Tao
end Erdos1135SecondScale
