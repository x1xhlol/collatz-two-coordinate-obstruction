import TrapProductTransport
import TrapPascalPrefixLaw
import TrapBoundedPMFExpectation
import Erdos1135.Tao.Fourier.Section7PairExpectation

/-! Exact prefix recursion of the native raw-Pascal source envelope. -/

set_option autoImplicit false

open CollatzResearch
open scoped Classical

namespace Erdos1135.Tao

theorem trap_sourceEnvelope_nonneg (n : ℕ) (xi : ZMod (3 ^ n)) (m j s : ℕ) :
    0 ≤ taoSection7PairSourceEnvelope n xi m j s := by
  exact trap_pmf_expectation_nonneg (taoSection7PascalSourceListPMF m)
    (taoSection7FactorProductFrom (taoSection7SourceFThreeFactor n xi) j s)
    (taoSection7FactorProductFrom_nonneg (taoSection7SourceFThreeFactor_nonneg n xi) j s)

theorem trap_sourceEnvelope_le_one (n : ℕ) (xi : ZMod (3 ^ n)) (m j s : ℕ) :
    taoSection7PairSourceEnvelope n xi m j s ≤ 1 := by
  exact trap_pmf_expectation_le_one (taoSection7PascalSourceListPMF m)
    (taoSection7FactorProductFrom (taoSection7SourceFThreeFactor n xi) j s)
    (taoSection7FactorProductFrom_nonneg (taoSection7SourceFThreeFactor_nonneg n xi) j s)
    (taoSection7FactorProductFrom_le_one (taoSection7SourceFThreeFactor_nonneg n xi)
      (taoSection7SourceFThreeFactor_le_one n xi) j s)

theorem trap_sourceEnvelope_summable (n : ℕ) (xi : ZMod (3 ^ n)) (m j s : ℕ) :
    Summable fun bs : List ℕ =>
      (taoSection7PascalSourceListPMF m bs).toReal *
        taoSection7FactorProductFrom (taoSection7SourceFThreeFactor n xi) j s bs := by
  exact trap_pmf_expectation_summable (taoSection7PascalSourceListPMF m)
    (taoSection7FactorProductFrom (taoSection7SourceFThreeFactor n xi) j s)
    (taoSection7FactorProductFrom_nonneg (taoSection7SourceFThreeFactor_nonneg n xi) j s)
    (taoSection7FactorProductFrom_le_one (taoSection7SourceFThreeFactor_nonneg n xi)
      (taoSection7SourceFThreeFactor_le_one n xi) j s)

theorem trap_sourceEnvelope_prefix_split (n u v : ℕ) (hu : 2 * u ≤ n)
    (xi : ZMod (3 ^ n)) :
    taoSection7PairSourceEnvelope n xi (u + v) 1 0 =
      ∑' bs : List ℕ,
        (taoSection7PascalSourceListPMF u bs).toReal *
          taoSection7FactorProduct (taoSection7SourceFThreeFactor n xi) bs *
          taoSection7PairSourceEnvelope (n - 2 * u)
            (trapPrefixFrequency n u (bs.sum : ℤ) xi) v 1 0 := by
  let P := taoSection7FactorProduct (taoSection7SourceFThreeFactor n xi)
  have hP0 : ∀ bs, 0 ≤ P bs :=
    taoSection7FactorProductFrom_nonneg (taoSection7SourceFThreeFactor_nonneg n xi) 1 0
  have hP1 : ∀ bs, P bs ≤ 1 :=
    taoSection7FactorProduct_le_one (taoSection7SourceFThreeFactor_nonneg n xi)
      (taoSection7SourceFThreeFactor_le_one n xi)
  change trapPMFExpectation (taoSection7PascalSourceListPMF (u + v)) P = _
  rw [trap_pascalList_append, trap_pmf_expectation_bind _ _ _ hP0 hP1]
  unfold trapPMFExpectation
  apply tsum_congr
  intro bs
  dsimp only
  by_cases hlen : bs.length = u
  · rw [show (∑' cs : List ℕ,
        ((taoSection7PascalSourceListPMF v).map (fun cs => bs ++ cs) cs).toReal * P cs) =
      ∑' cs : List ℕ, (taoSection7PascalSourceListPMF v cs).toReal * P (bs ++ cs) from
        trap_pmf_expectation_map (taoSection7PascalSourceListPMF v)
          (fun cs => bs ++ cs) P hP0 hP1]
    simp only [P, trap_factorProduct_prefix_split n u hu xi bs _ hlen]
    rw [taoSection7PairSourceEnvelope]
    simp only [taoSection7FactorProduct]
    rw [← tsum_mul_left, ← tsum_mul_left]
    apply tsum_congr
    intro cs
    ring
  · rw [trap_pascalList_zero_of_length_ne u bs hlen]
    simp

noncomputable def trapSourceEnvelopeQ (n J : ℕ) : ℝ :=
  ⨆ xi : ZMod (3 ^ n),
    if zmodThreePrimitive n xi then taoSection7PairSourceEnvelope n xi J 1 0 else 0

theorem trap_sourceEnvelopeQ_bdd (n J : ℕ) :
    BddAbove (Set.range fun xi : ZMod (3 ^ n) =>
      if zmodThreePrimitive n xi then taoSection7PairSourceEnvelope n xi J 1 0 else 0) := by
  refine ⟨1, ?_⟩
  rintro x ⟨xi, rfl⟩
  dsimp only
  split_ifs
  · exact trap_sourceEnvelope_le_one n xi J 1 0
  · norm_num

theorem trap_sourceEnvelopeQ_nonneg (n J : ℕ) : 0 ≤ trapSourceEnvelopeQ n J := by
  have h := le_ciSup (trap_sourceEnvelopeQ_bdd n J) (0 : ZMod (3 ^ n))
  apply le_trans _ h
  split_ifs
  · exact trap_sourceEnvelope_nonneg n 0 J 1 0
  · exact le_rfl

theorem trap_sourceEnvelopeQ_le_one (n J : ℕ) : trapSourceEnvelopeQ n J ≤ 1 := by
  apply ciSup_le
  intro xi
  split_ifs
  · exact trap_sourceEnvelope_le_one n xi J 1 0
  · norm_num

theorem trap_sourceEnvelope_le_Q (n J : ℕ) (xi : ZMod (3 ^ n))
    (hxi : zmodThreePrimitive n xi) :
    taoSection7PairSourceEnvelope n xi J 1 0 ≤ trapSourceEnvelopeQ n J := by
  have h := le_ciSup (trap_sourceEnvelopeQ_bdd n J) xi
  simpa only [ite_eq_left hxi, trapSourceEnvelopeQ] using h

theorem trap_sourceEnvelope_prefix_le (n u v : ℕ) (hu : 2 * u < n)
    (xi : ZMod (3 ^ n)) (hxi : zmodThreePrimitive n xi) :
    taoSection7PairSourceEnvelope n xi (u + v) 1 0 ≤
      taoSection7PairSourceEnvelope n xi u 1 0 * trapSourceEnvelopeQ (n - 2 * u) v := by
  let w : List ℕ → ℝ := fun bs =>
    (taoSection7PascalSourceListPMF u bs).toReal *
      taoSection7FactorProduct (taoSection7SourceFThreeFactor n xi) bs
  let T : List ℕ → ℝ := fun bs =>
    taoSection7PairSourceEnvelope (n - 2 * u)
      (trapPrefixFrequency n u (bs.sum : ℤ) xi) v 1 0
  have hw0 : ∀ bs, 0 ≤ w bs := by
    intro bs
    exact mul_nonneg ENNReal.toReal_nonneg
      (taoSection7FactorProductFrom_nonneg
        (taoSection7SourceFThreeFactor_nonneg n xi) 1 0 bs)
  have hw : Summable w := trap_sourceEnvelope_summable n xi u 1 0
  have hT0 : ∀ bs, 0 ≤ T bs := by
    intro bs
    exact trap_sourceEnvelope_nonneg _ _ _ _ _
  have hT1 : ∀ bs, T bs ≤ 1 := by
    intro bs
    exact trap_sourceEnvelope_le_one _ _ _ _ _
  have hTw : Summable (fun bs => w bs * T bs) := by
    refine Summable.of_norm_bounded hw ?_
    intro bs
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hw0 bs) (hT0 bs))]
    exact mul_le_of_le_one_right (hw0 bs) (hT1 bs)
  rw [trap_sourceEnvelope_prefix_split n u v hu.le]
  change (∑' bs, w bs * T bs) ≤ _
  calc
    (∑' bs, w bs * T bs) ≤ ∑' bs, w bs * trapSourceEnvelopeQ (n - 2 * u) v := by
      apply hTw.tsum_le_tsum _ (hw.mul_right _)
      intro bs
      exact mul_le_mul_of_nonneg_left
        (trap_sourceEnvelope_le_Q _ _ _ (trapPrefixFrequency_primitive n u _ xi hxi hu))
        (hw0 bs)
    _ = taoSection7PairSourceEnvelope n xi u 1 0 * trapSourceEnvelopeQ (n - 2 * u) v := by
      rw [tsum_mul_right]
      rfl

theorem trap_sourceEnvelopeQ_add_le (n u v : ℕ) (hu : 2 * u < n) :
    trapSourceEnvelopeQ n (u + v) ≤
      trapSourceEnvelopeQ n u * trapSourceEnvelopeQ (n - 2 * u) v := by
  apply ciSup_le
  intro xi
  split_ifs with hxi
  · exact (trap_sourceEnvelope_prefix_le n u v hu xi hxi).trans
      (mul_le_mul_of_nonneg_right (trap_sourceEnvelope_le_Q n u xi hxi)
        (trap_sourceEnvelopeQ_nonneg _ _))
  · exact mul_nonneg (trap_sourceEnvelopeQ_nonneg _ _) (trap_sourceEnvelopeQ_nonneg _ _)

theorem trap_sourceEnvelopeQ_recursion (n J u : ℕ) (huJ : u ≤ J) (hu : 2 * u < n) :
    trapSourceEnvelopeQ n J ≤
      trapSourceEnvelopeQ n u * trapSourceEnvelopeQ (n - 2 * u) (J - u) := by
  simpa only [Nat.add_sub_of_le huJ] using trap_sourceEnvelopeQ_add_le n u (J - u) hu

end Erdos1135.Tao

#print axioms Erdos1135.Tao.trap_sourceEnvelope_prefix_split

#print axioms Erdos1135.Tao.trap_sourceEnvelopeQ_recursion
