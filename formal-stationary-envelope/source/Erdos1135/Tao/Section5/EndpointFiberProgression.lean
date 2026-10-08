import Erdos1135.Tao.Probability.ReciprocalProgression
import Erdos1135.Tao.Section5.EndpointValuationFiber

/-!
# Section 5 Endpoint Fibers As Reciprocal Progressions

This leaf projects attached endpoint fibers injectively to natural numbers,
preserves their reciprocal sums, and places the projected fibers inside the
low and high inclusive CRT progressions.  The logarithmic estimate is applied
only in the nonempty branch, where a witness supplies the required endpoint
order.
-/

open scoped BigOperators

namespace Erdos1135
namespace Tao

noncomputable section

/-- Natural-number projection of one attached endpoint valuation fiber. -/
def taoSection5EndpointValuationFiberNat
    (B : ℕ) (E : Set ℕ) (q : ℕ) (X : ZMod (3 ^ q))
    (bs : List ℕ+) : Finset ℕ := by
  classical
  exact (taoSection5EndpointValuationFiber B E q X bs).image
    (fun M => M.1)

theorem mem_taoSection5EndpointValuationFiberNat_iff
    {B : ℕ} {E : Set ℕ} {q : ℕ} {X : ZMod (3 ^ q)}
    {bs : List ℕ+} {N : ℕ} :
    N ∈ taoSection5EndpointValuationFiberNat B E q X bs ↔
      ∃ M : TaoSection5Endpoint B E,
        M ∈ taoSection5EndpointValuationFiber B E q X bs ∧ M.1 = N := by
  classical
  simp [taoSection5EndpointValuationFiberNat, eq_comm]

/-- Injective subtype projection loses no multiplicity in any additive sum. -/
theorem sum_taoSection5EndpointValuationFiber_eq_sum_nat
    {R : Type*} [AddCommMonoid R]
    {B : ℕ} {E : Set ℕ} (q : ℕ) (X : ZMod (3 ^ q))
    (bs : List ℕ+) (f : ℕ → R) :
    (∑ M ∈ taoSection5EndpointValuationFiber B E q X bs, f M.1) =
      ∑ N ∈ taoSection5EndpointValuationFiberNat B E q X bs, f N := by
  classical
  rw [taoSection5EndpointValuationFiberNat, Finset.sum_image]
  intro M₁ _hM₁ M₂ _hM₂ hEq
  exact Subtype.val_injective hEq

/-- Full CRT modulus for a fixed endpoint tuple and coefficient exponent. -/
def taoSection5EndpointFiberModulus (q : ℕ) (bs : List ℕ+) : ℕ :=
  2 ^ (taoTupleWeight bs + 1) * 3 ^ q

/-- The natural projection of a low endpoint fiber lies in its inclusive CRT
progression. -/
theorem taoSection5EndpointValuationFiberNat_subset_lowProgression
    {B : ℕ} {E : Set ℕ} (facts : TaoSection5PassLostWindowFacts B)
    {q : ℕ} {X : ZMod (3 ^ q)} {bs : List ℕ+} :
    taoSection5EndpointValuationFiberNat B E q X bs ⊆
      reciprocalModEqClass
        (taoSection5EndpointLower B bs)
        (taoSection5EndpointUpper B bs)
        (taoSection5EndpointFiberModulus q bs)
        (syracuseValuationCylinderCRTResidue bs q X) := by
  classical
  intro N hN
  rw [mem_taoSection5EndpointValuationFiberNat_iff] at hN
  rcases hN with ⟨M, hM, rfl⟩
  apply Finset.mem_filter.mpr
  exact
    ⟨taoSection5EndpointFiber_mem_interval facts hM,
      by simpa only [taoSection5EndpointFiberModulus] using
        taoSection5EndpointFiber_modEq_crt hM⟩

/-- The natural projection of a high endpoint fiber lies in the corresponding
inclusive CRT progression with the raised lower endpoint. -/
theorem taoSection5EndpointValuationFiberNat_subset_highProgression
    {B : ℕ} {E : Set ℕ} (facts : TaoSection5PassLostWindowFacts B)
    {q : ℕ} {X : ZMod (3 ^ q)} {bs : List ℕ+} :
    taoSection5EndpointValuationFiberNat B E q X bs ⊆
      reciprocalModEqClass
        (taoSection5EndpointHighLower B bs)
        (taoSection5EndpointUpper B bs)
        (taoSection5EndpointFiberModulus q bs)
        (syracuseValuationCylinderCRTResidue bs q X) := by
  classical
  intro N hN
  rw [mem_taoSection5EndpointValuationFiberNat_iff] at hN
  rcases hN with ⟨M, hM, rfl⟩
  apply Finset.mem_filter.mpr
  exact
    ⟨taoSection5EndpointFiber_mem_highInterval facts hM,
      by simpa only [taoSection5EndpointFiberModulus] using
        taoSection5EndpointFiber_modEq_crt hM⟩

private theorem taoSection5EndpointLower_one_le
    (B : ℕ) (bs : List ℕ+) :
    1 ≤ taoSection5EndpointLower B bs := by
  unfold taoSection5EndpointLower syracuseFirstPassageLowerEndpoint
  exact Nat.succ_le_succ (Nat.zero_le _)

private theorem taoSection5EndpointHighLower_one_le
    (B : ℕ) (bs : List ℕ+) :
    1 ≤ taoSection5EndpointHighLower B bs := by
  exact (taoSection5EndpointLower_one_le B bs).trans
    (le_max_left _ _)

private theorem taoSection5EndpointFiberModulus_pos
    (q : ℕ) (bs : List ℕ+) :
    0 < taoSection5EndpointFiberModulus q bs := by
  unfold taoSection5EndpointFiberModulus
  positivity

/-- Sharp low-progression reciprocal bound for a nonempty fixed endpoint
fiber. -/
theorem sum_taoSection5EndpointFiber_reciprocal_le_low_of_nonempty
    {B : ℕ} {E : Set ℕ} (facts : TaoSection5PassLostWindowFacts B)
    {q : ℕ} {X : ZMod (3 ^ q)} {bs : List ℕ+}
    (hne : (taoSection5EndpointValuationFiber B E q X bs).Nonempty) :
    (∑ M ∈ taoSection5EndpointValuationFiber B E q X bs,
        1 / (M.1 : ℝ)) ≤
      1 / (taoSection5EndpointLower B bs : ℝ) +
        (1 / (taoSection5EndpointFiberModulus q bs : ℝ)) *
          (1 / (taoSection5EndpointLower B bs : ℝ) +
            Real.log
              ((taoSection5EndpointUpper B bs : ℝ) /
                (taoSection5EndpointLower B bs : ℝ))) := by
  rw [sum_taoSection5EndpointValuationFiber_eq_sum_nat q X bs
    (fun N => 1 / (N : ℝ))]
  calc
    (∑ N ∈ taoSection5EndpointValuationFiberNat B E q X bs,
        1 / (N : ℝ)) ≤
        ∑ N ∈ reciprocalModEqClass
          (taoSection5EndpointLower B bs)
          (taoSection5EndpointUpper B bs)
          (taoSection5EndpointFiberModulus q bs)
          (syracuseValuationCylinderCRTResidue bs q X),
            1 / (N : ℝ) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (taoSection5EndpointValuationFiberNat_subset_lowProgression facts)
        (by
          intro N _hN _hnot
          positivity)
    _ ≤ 1 / (taoSection5EndpointLower B bs : ℝ) +
        (1 / (taoSection5EndpointFiberModulus q bs : ℝ)) *
          (1 / (taoSection5EndpointLower B bs : ℝ) +
            Real.log
              ((taoSection5EndpointUpper B bs : ℝ) /
                (taoSection5EndpointLower B bs : ℝ))) := by
      exact sum_Icc_reciprocal_modEq_le
        (taoSection5EndpointLower_one_le B bs)
        (taoSection5EndpointFiber_nonempty_lower_le_upper facts hne)
        (taoSection5EndpointFiberModulus_pos q bs)

/-- Sharp high-progression reciprocal bound for a nonempty fixed endpoint
fiber. -/
theorem sum_taoSection5EndpointFiber_reciprocal_le_high_of_nonempty
    {B : ℕ} {E : Set ℕ} (facts : TaoSection5PassLostWindowFacts B)
    {q : ℕ} {X : ZMod (3 ^ q)} {bs : List ℕ+}
    (hne : (taoSection5EndpointValuationFiber B E q X bs).Nonempty) :
    (∑ M ∈ taoSection5EndpointValuationFiber B E q X bs,
        1 / (M.1 : ℝ)) ≤
      1 / (taoSection5EndpointHighLower B bs : ℝ) +
        (1 / (taoSection5EndpointFiberModulus q bs : ℝ)) *
          (1 / (taoSection5EndpointHighLower B bs : ℝ) +
            Real.log
              ((taoSection5EndpointUpper B bs : ℝ) /
                (taoSection5EndpointHighLower B bs : ℝ))) := by
  rw [sum_taoSection5EndpointValuationFiber_eq_sum_nat q X bs
    (fun N => 1 / (N : ℝ))]
  calc
    (∑ N ∈ taoSection5EndpointValuationFiberNat B E q X bs,
        1 / (N : ℝ)) ≤
        ∑ N ∈ reciprocalModEqClass
          (taoSection5EndpointHighLower B bs)
          (taoSection5EndpointUpper B bs)
          (taoSection5EndpointFiberModulus q bs)
          (syracuseValuationCylinderCRTResidue bs q X),
            1 / (N : ℝ) := by
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (taoSection5EndpointValuationFiberNat_subset_highProgression facts)
        (by
          intro N _hN _hnot
          positivity)
    _ ≤ 1 / (taoSection5EndpointHighLower B bs : ℝ) +
        (1 / (taoSection5EndpointFiberModulus q bs : ℝ)) *
          (1 / (taoSection5EndpointHighLower B bs : ℝ) +
            Real.log
              ((taoSection5EndpointUpper B bs : ℝ) /
                (taoSection5EndpointHighLower B bs : ℝ))) := by
      exact sum_Icc_reciprocal_modEq_le
        (taoSection5EndpointHighLower_one_le B bs)
        (taoSection5EndpointFiber_nonempty_highLower_le_upper facts hne)
        (taoSection5EndpointFiberModulus_pos q bs)

theorem sum_taoSection5EndpointFiber_reciprocal_eq_zero_of_not_nonempty
    {B : ℕ} {E : Set ℕ} {q : ℕ} {X : ZMod (3 ^ q)} {bs : List ℕ+}
    (hempty : ¬ (taoSection5EndpointValuationFiber B E q X bs).Nonempty) :
    (∑ M ∈ taoSection5EndpointValuationFiber B E q X bs,
      1 / (M.1 : ℝ)) = 0 := by
  rw [Finset.not_nonempty_iff_eq_empty.mp hempty]
  simp

/-- Total low-bound dispatch: an empty fiber contributes zero, while a
nonempty fiber receives the sharp progression estimate. -/
theorem sum_taoSection5EndpointFiber_reciprocal_le_low_if_nonempty
    {B : ℕ} {E : Set ℕ} (facts : TaoSection5PassLostWindowFacts B)
    {q : ℕ} {X : ZMod (3 ^ q)} {bs : List ℕ+} :
    (∑ M ∈ taoSection5EndpointValuationFiber B E q X bs,
        1 / (M.1 : ℝ)) ≤
      if (taoSection5EndpointValuationFiber B E q X bs).Nonempty then
        1 / (taoSection5EndpointLower B bs : ℝ) +
          (1 / (taoSection5EndpointFiberModulus q bs : ℝ)) *
            (1 / (taoSection5EndpointLower B bs : ℝ) +
              Real.log
                ((taoSection5EndpointUpper B bs : ℝ) /
                  (taoSection5EndpointLower B bs : ℝ)))
      else 0 := by
  classical
  by_cases hne : (taoSection5EndpointValuationFiber B E q X bs).Nonempty
  · rw [if_pos hne]
    exact sum_taoSection5EndpointFiber_reciprocal_le_low_of_nonempty facts hne
  · rw [if_neg hne,
      sum_taoSection5EndpointFiber_reciprocal_eq_zero_of_not_nonempty hne]

/-- Total high-bound dispatch with the same explicit empty branch. -/
theorem sum_taoSection5EndpointFiber_reciprocal_le_high_if_nonempty
    {B : ℕ} {E : Set ℕ} (facts : TaoSection5PassLostWindowFacts B)
    {q : ℕ} {X : ZMod (3 ^ q)} {bs : List ℕ+} :
    (∑ M ∈ taoSection5EndpointValuationFiber B E q X bs,
        1 / (M.1 : ℝ)) ≤
      if (taoSection5EndpointValuationFiber B E q X bs).Nonempty then
        1 / (taoSection5EndpointHighLower B bs : ℝ) +
          (1 / (taoSection5EndpointFiberModulus q bs : ℝ)) *
            (1 / (taoSection5EndpointHighLower B bs : ℝ) +
              Real.log
                ((taoSection5EndpointUpper B bs : ℝ) /
                  (taoSection5EndpointHighLower B bs : ℝ)))
      else 0 := by
  classical
  by_cases hne : (taoSection5EndpointValuationFiber B E q X bs).Nonempty
  · rw [if_pos hne]
    exact sum_taoSection5EndpointFiber_reciprocal_le_high_of_nonempty facts hne
  · rw [if_neg hne,
      sum_taoSection5EndpointFiber_reciprocal_eq_zero_of_not_nonempty hne]

end

end Tao
end Erdos1135
