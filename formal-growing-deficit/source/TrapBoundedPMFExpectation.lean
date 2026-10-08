import Mathlib.Probability.ProbabilityMassFunction.Constructions
import Mathlib.Topology.Algebra.InfiniteSum.ENNReal
import Mathlib.Tactic

/-! Bounded real PMF expectations and exact bind/map identities. -/

set_option autoImplicit false

open scoped BigOperators

namespace CollatzResearch

noncomputable def trapPMFExpectation {α : Type*} (p : PMF α) (f : α → ℝ) : ℝ :=
  ∑' a, (p a).toReal * f a

theorem trap_pmf_expectation_summable {α : Type*}
    (p : PMF α) (f : α → ℝ)
    (hf0 : ∀ a, 0 ≤ f a) (hf1 : ∀ a, f a ≤ 1) :
    Summable fun a => (p a).toReal * f a := by
  refine Summable.of_norm_bounded (ENNReal.summable_toReal p.tsum_coe_ne_top) ?_
  intro a
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ENNReal.toReal_nonneg (hf0 a))]
  exact mul_le_of_le_one_right ENNReal.toReal_nonneg (hf1 a)

theorem trap_pmf_expectation_nonneg {α : Type*}
    (p : PMF α) (f : α → ℝ) (hf0 : ∀ a, 0 ≤ f a) :
    0 ≤ trapPMFExpectation p f :=
  tsum_nonneg fun a => mul_nonneg ENNReal.toReal_nonneg (hf0 a)

private theorem trap_pmf_ennreal_expectation_le_one {α : Type*}
    (p : PMF α) (f : α → ℝ) (hf1 : ∀ a, f a ≤ 1) :
    (∑' a, p a * ENNReal.ofReal (f a)) ≤ 1 := by
  calc
    (∑' a, p a * ENNReal.ofReal (f a)) ≤ ∑' a, p a := by
      apply ENNReal.tsum_le_tsum
      intro a
      calc
        p a * ENNReal.ofReal (f a) ≤ p a * 1 := by
          gcongr
          exact ENNReal.ofReal_le_one.mpr (hf1 a)
        _ = p a := mul_one _
    _ = 1 := p.tsum_coe

private theorem trap_pmf_expectation_eq_ennreal {α : Type*}
    (p : PMF α) (f : α → ℝ) (hf0 : ∀ a, 0 ≤ f a) :
    trapPMFExpectation p f = (∑' a, p a * ENNReal.ofReal (f a)).toReal := by
  rw [ENNReal.tsum_toReal_eq (fun a =>
    ENNReal.mul_ne_top (p.apply_ne_top a) ENNReal.ofReal_ne_top)]
  apply tsum_congr
  intro a
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (hf0 a)]

theorem trap_pmf_expectation_le_one {α : Type*}
    (p : PMF α) (f : α → ℝ)
    (hf0 : ∀ a, 0 ≤ f a) (hf1 : ∀ a, f a ≤ 1) :
    trapPMFExpectation p f ≤ 1 := by
  rw [trap_pmf_expectation_eq_ennreal p f hf0]
  simpa using ENNReal.toReal_mono ENNReal.one_ne_top
    (trap_pmf_ennreal_expectation_le_one p f hf1)

theorem trap_pmf_expectation_bind {α β : Type*}
    (p : PMF α) (K : α → PMF β) (f : β → ℝ)
    (hf0 : ∀ b, 0 ≤ f b) (hf1 : ∀ b, f b ≤ 1) :
    trapPMFExpectation (p.bind K) f =
      trapPMFExpectation p (fun a => trapPMFExpectation (K a) f) := by
  have henn :
      (∑' b, (p.bind K) b * ENNReal.ofReal (f b)) =
        ∑' a, p a * (∑' b, K a b * ENNReal.ofReal (f b)) := by
    calc
      (∑' b, (p.bind K) b * ENNReal.ofReal (f b)) =
          ∑' b, ∑' a, (p a * K a b) * ENNReal.ofReal (f b) := by
        apply tsum_congr
        intro b
        rw [PMF.bind_apply, ENNReal.tsum_mul_right]
      _ = ∑' a, ∑' b, (p a * K a b) * ENNReal.ofReal (f b) :=
        ENNReal.tsum_comm
      _ = ∑' a, p a * (∑' b, K a b * ENNReal.ofReal (f b)) := by
        apply tsum_congr
        intro a
        rw [← ENNReal.tsum_mul_left]
        apply tsum_congr
        intro b
        exact mul_assoc _ _ _
  have hfinite : ∀ a, (∑' b, K a b * ENNReal.ofReal (f b)) ≠ ⊤ := by
    intro a
    exact ne_top_of_le_ne_top ENNReal.one_ne_top
      (trap_pmf_ennreal_expectation_le_one (K a) f hf1)
  rw [trap_pmf_expectation_eq_ennreal (p.bind K) f hf0, henn,
    ENNReal.tsum_toReal_eq (fun a => ENNReal.mul_ne_top (p.apply_ne_top a) (hfinite a))]
  apply tsum_congr
  intro a
  rw [ENNReal.toReal_mul, ← trap_pmf_expectation_eq_ennreal (K a) f hf0]

theorem trap_pmf_expectation_map {α β : Type*}
    (p : PMF α) (g : α → β) (f : β → ℝ)
    (hf0 : ∀ b, 0 ≤ f b) (hf1 : ∀ b, f b ≤ 1) :
    trapPMFExpectation (p.map g) f =
      trapPMFExpectation p (fun a => f (g a)) := by
  classical
  have hpure : ∀ b, trapPMFExpectation (PMF.pure b) f = f b := by
    intro b
    unfold trapPMFExpectation
    rw [tsum_eq_single b]
    · simp [PMF.pure_apply]
    · intro a hab
      simp [PMF.pure_apply, hab]
  change trapPMFExpectation (p.bind fun a => PMF.pure (g a)) f = _
  rw [trap_pmf_expectation_bind p _ f hf0 hf1]
  simp only [hpure]

end CollatzResearch

#print axioms CollatzResearch.trap_pmf_expectation_summable
#print axioms CollatzResearch.trap_pmf_expectation_nonneg
#print axioms CollatzResearch.trap_pmf_expectation_le_one
#print axioms CollatzResearch.trap_pmf_expectation_bind
#print axioms CollatzResearch.trap_pmf_expectation_map
