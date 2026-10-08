import TrapHoldSourceSupport
import TrapBoundedPMFExpectation
import Erdos1135.Tao.Fourier.Section7PairExpectation
import Erdos1135.Tao.Fourier.Section7SourceDomain

/-! Exact shortened-prefix Laplace transport under the literal Hold list law. -/

set_option autoImplicit false

open CollatzResearch
open scoped BigOperators

namespace Erdos1135.Tao

noncomputable def trapHoldListWhiteCount
    (W : TaoSection7RenewalPoint → Prop) : List TaoSection7RenewalPoint → ℕ
  | [] => 0
  | p :: hs => taoSection7QWhiteVisitCount W p hs

theorem trap_holdSource_count_eq_holdList_count
    (W : ℕ → ℤ → Prop) (xs : List (ℕ × List ℕ))
    (hsupp : ∀ x ∈ xs, x.1 = x.2.length ∧ taoSection7NoThree x.2) :
    taoSection7WhiteHitCount W (taoSection7SourceBlocks (xs.map Prod.snd)) =
      trapHoldListWhiteCount (taoSection7SourceWhiteRenewal W)
        (xs.map fun x => taoSection7HoldPointOfPrefix x.1 x.2) := by
  cases xs with
  | nil => rfl
  | cons x xs =>
      have hx := hsupp x (by simp)
      have htail : ∀ y ∈ xs, y.1 = y.2.length ∧ taoSection7NoThree y.2 := by
        intro y hy
        exact hsupp y (by simp [hy])
      simp only [List.map_cons, trapHoldListWhiteCount]
      rw [taoSection7WhiteHitCount_blocks_eq_qvisit W x.2 (xs.map Prod.snd) hx.2
        (by
          intro pre hpre
          obtain ⟨y, hy, rfl⟩ := List.mem_map.mp hpre
          exact (htail y hy).2)]
      rw [hx.1, trap_holdPoint_length_eq_sourceHitPoint,
        trap_holdPoint_map_eq_increments_of_supported xs (fun y hy => (htail y hy).1)]

theorem trap_laplace_nonneg (a : ℝ) (k : ℕ) : 0 ≤ Real.exp (-a * (k : ℝ)) :=
  Real.exp_nonneg _

theorem trap_laplace_le_one (a : ℝ) (ha : 0 ≤ a) (k : ℕ) :
    Real.exp (-a * (k : ℝ)) ≤ 1 := by
  apply Real.exp_le_one_iff.mpr
  exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr ha) (Nat.cast_nonneg k)

theorem trap_rawPenalty_eq_holdList_laplace
    (n J N : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (hepsilon : 0 ≤ epsilon) (hJN : J ≤ N) :
    trapPMFExpectation (taoSection7PascalSourceListPMF J)
        (taoSection7WhiteHitPenalty epsilon (taoSection7SourceWhiteWCutoff n xi epsilon J)) =
      trapPMFExpectation (taoSection7HoldListPMF N)
        (fun hs => Real.exp (-(epsilon ^ 3) *
          (trapHoldListWhiteCount
            (taoSection7SourceWhiteRenewal
              (taoSection7SourceWhiteWCutoff n xi epsilon J)) hs : ℝ))) := by
  let W := taoSection7SourceWhiteWCutoff n xi epsilon J
  let F := taoSection7WhiteHitPenalty epsilon W
  let G := fun hs => Real.exp (-(epsilon ^ 3) *
    (trapHoldListWhiteCount (taoSection7SourceWhiteRenewal W) hs : ℝ))
  have hF0 : ∀ bs, 0 ≤ F bs := fun bs => Real.exp_nonneg _
  have hF1 : ∀ bs, F bs ≤ 1 := fun bs =>
    trap_laplace_le_one _ (pow_nonneg hepsilon _) _
  have hG0 : ∀ hs, 0 ≤ G hs := fun hs => Real.exp_nonneg _
  have hG1 : ∀ hs, G hs ≤ 1 := fun hs =>
    trap_laplace_le_one _ (pow_nonneg hepsilon _) _
  change trapPMFExpectation _ F = trapPMFExpectation _ G
  rw [← taoSection7HoldSourcePrefixListPMF_map_rawPrefix_eq_of_le J N hJN,
    trap_pmf_expectation_map _ _ _ hF0 hF1,
    ← taoSection7HoldSourcePrefixListPMF_map_holdPoint_eq N,
    trap_pmf_expectation_map _ _ _ hG0 hG1]
  unfold trapPMFExpectation
  apply tsum_congr
  intro xs
  by_cases hmass : (taoSection7HoldSourcePrefixListPMF N xs).toReal = 0
  · simp [hmass]
  · have hsupp := (trap_holdSourceList_toReal_ne_zero_support hmass).2
    congr 1
    change taoSection7WhiteHitPenalty epsilon W
        ((taoSection7SourceBlocks (xs.map Prod.snd)).take J) = _
    rw [taoSection7WhiteHitPenalty_cutoff_take_eq]
    change Real.exp (-(epsilon ^ 3) *
      (taoSection7WhiteHitCount W (taoSection7SourceBlocks (xs.map Prod.snd)) : ℝ)) = _
    rw [trap_holdSource_count_eq_holdList_count W xs hsupp]

theorem trap_sourceEnvelope_le_short_holdList_laplace
    (n J N : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1) (hJN : J ≤ N) :
    taoSection7PairSourceEnvelope n xi J 1 0 ≤
      trapPMFExpectation (taoSection7HoldListPMF N)
        (fun hs => Real.exp (-(epsilon ^ 3) *
          (trapHoldListWhiteCount
            (taoSection7SourceWhiteRenewal
              (taoSection7SourceWhiteWCutoff n xi epsilon J)) hs : ℝ))) := by
  rw [← trap_rawPenalty_eq_holdList_laplace n J N xi epsilon hepsilon0 hJN]
  let F := taoSection7FactorProduct (taoSection7SourceFThreeFactor n xi)
  let G := taoSection7WhiteHitPenalty epsilon (taoSection7SourceWhiteWCutoff n xi epsilon J)
  have hF0 : ∀ bs, 0 ≤ F bs :=
    taoSection7FactorProductFrom_nonneg (taoSection7SourceFThreeFactor_nonneg n xi) 1 0
  have hF1 : ∀ bs, F bs ≤ 1 :=
    taoSection7FactorProduct_le_one (taoSection7SourceFThreeFactor_nonneg n xi)
      (taoSection7SourceFThreeFactor_le_one n xi)
  have hG0 : ∀ bs, 0 ≤ G bs := fun bs => Real.exp_nonneg _
  have hG1 : ∀ bs, G bs ≤ 1 := fun bs =>
    trap_laplace_le_one _ (pow_nonneg hepsilon0 _) _
  apply (trap_pmf_expectation_summable _ F hF0 hF1).tsum_le_tsum
    _ (trap_pmf_expectation_summable _ G hG0 hG1)
  intro bs
  apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
  exact taoSection7FactorProduct_le_penalty
    (taoSection7SourceFThreeFactor_nonneg n xi)
    (taoSection7SourceFThreeFactor_hit_bound_cutoff n xi J hepsilon0 hepsilon1)
    (fun j s b _ => taoSection7SourceFThreeFactor_le_one n xi j s b) bs

end Erdos1135.Tao

#print axioms Erdos1135.Tao.trap_rawPenalty_eq_holdList_laplace
#print axioms Erdos1135.Tao.trap_sourceEnvelope_le_short_holdList_laplace
