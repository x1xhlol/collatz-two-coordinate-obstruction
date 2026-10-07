import FinitePrefixSourceMass
import SourceSuffixPrefix

set_option autoImplicit false

open Filter Topology

namespace CollatzCylinderPacking.Arithmetic.InverseDoob
open CollatzCanonical.DirichletAbelian

theorem prefixIndex_eq_of_common_ancestor {n k q : ℕ} (hnodd : n % 2 = 1)
    (hnp : Nonperiodic n) {p r : PrefixIndex k}
    (hp : ValidPrefix n k (prefixExtend k p)) (hr : ValidPrefix n k (prefixExtend k r))
    (hqp : ∃ A, iterate A q = prefixExtend k p k)
    (hqr : ∃ A, iterate A q = prefixExtend k r k) : p = r := by
  have he := hp.eq_of_common_ancestor hr hnodd hnp hqp hqr
  funext i
  simpa only [prefixExtend_apply _ (Finset.mem_Iic.mp i.2)] using
    he i (Finset.mem_Iic.mp i.2)

theorem prefixSourceWeight_sum_le {n k : ℕ} (hnodd : n % 2 = 1) (hnp : Nonperiodic n)
    (S : Finset (PrefixIndex k)) (q : ℕ) :
    ∑ p ∈ S, prefixSourceWeight n k p q ≤ oddFirstHitWeight n q := by
  classical
  let P : PrefixIndex k → Prop := fun p => ValidPrefix n k (prefixExtend k p) ∧
    ∃ B, iterate B q = prefixExtend k p k
  by_cases hex : ∃ p ∈ S, P p
  · obtain ⟨p, hpS, hp⟩ := hex
    have hzero (r : PrefixIndex k) (_hrS : r ∈ S) (hrp : r ≠ p) :
        prefixSourceWeight n k r q = 0 := by
      have hnot : ¬ P r := by
        intro hr
        exact hrp (prefixIndex_eq_of_common_ancestor hnodd hnp hr.1 hp.1 hr.2 hp.2)
      exact if_neg hnot
    rw [Finset.sum_eq_single p hzero (by simp only [hpS, not_true_eq_false, false_implies])]
    exact le_of_eq (if_pos hp)
  · have hzero : ∀ p ∈ S, prefixSourceWeight n k p q = 0 := by
      intro p hp
      exact if_neg (fun hh => hex ⟨p, hp, hh⟩)
    rw [Finset.sum_eq_zero hzero]
    unfold oddFirstHitWeight
    split_ifs
    · exact (firstHitWeight_bounds _ _).1
    · exact le_rfl

theorem prefixSourceMass_sum_le {n k : ℕ} (hnodd : n % 2 = 1) (hnp : Nonperiodic n)
    (S : Finset (PrefixIndex k)) (t : ℝ) :
    ∑ p ∈ S, prefixSourceMass n k t p ≤ fullSourceMass n t := by
  by_cases ht : 0 < t
  · simp only [prefixSourceMass, fullSourceMass, if_pos ht]
    rw [← Finset.mul_sum, ← Finset.sum_div, ← logarithmicCumulative_sum]
    apply mul_le_mul_of_nonneg_left _ (div_nonneg (by norm_num) (actualFirstHitDensity_nonneg n))
    apply div_le_div_of_nonneg_right _ ht.le
    exact logarithmicCumulative_le_of_positive_weights
      (fun q _ => prefixSourceWeight_sum_le hnodd hnp S q) t
  · simp only [prefixSourceMass, fullSourceMass, if_neg ht, Finset.sum_const_zero, le_refl]

theorem prefixSourceMass_summable {n k : ℕ} (hnodd : n % 2 = 1) (hnp : Nonperiodic n)
    (t : ℝ) : Summable (prefixSourceMass n k t) :=
  summable_of_sum_le (prefixSourceMass_nonneg n k t) (fun S => prefixSourceMass_sum_le hnodd hnp S t)

theorem prefixSourceMass_tsum_le {n k : ℕ} (hnodd : n % 2 = 1) (hnp : Nonperiodic n)
    (t : ℝ) : ∑' p, prefixSourceMass n k t p ≤ fullSourceMass n t :=
  (prefixSourceMass_summable hnodd hnp t).tsum_le_of_sum_le
    (fun S => prefixSourceMass_sum_le hnodd hnp S t)

end CollatzCylinderPacking.Arithmetic.InverseDoob
