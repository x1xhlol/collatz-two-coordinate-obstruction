import ActualBasinPolynomialFloor

set_option autoImplicit false

open Filter Topology Classical
open scoped BigOperators

namespace CollatzCanonical.PeriodicCensusFloor

open CollatzCylinderPacking CollatzCylinderPacking.Arithmetic CollatzBasinMapBridges
open CollatzCanonical.BoundedInverseSeed
open Erdos1135Predecessor.ND.PositiveDensity

noncomputable section

theorem ordinary_reaches_shortcut_step (q : ℕ) :
    Erdos1135Predecessor.Reaches q (step q) := by
  have hraw (n : ℕ) : Erdos1135Predecessor.Reaches n (rawStep n) :=
    Erdos1135Predecessor.reaches_of_step_eq (rawStep_eq_predecessor_native n).symm
  by_cases hq : q % 2 = 0
  · simpa only [rawStep, step, if_pos hq] using hraw q
  · have hodd : q % 2 = 1 := by omega
    have heven : (3 * q + 1) % 2 = 0 := by omega
    have hfirst : Erdos1135Predecessor.Reaches q (3 * q + 1) := by
      simpa only [rawStep, if_neg hq] using hraw q
    have hsecond : Erdos1135Predecessor.Reaches (3 * q + 1) (step q) := by
      simpa only [rawStep, step, if_pos heven, if_neg hq] using hraw (3 * q + 1)
    exact hfirst.trans hsecond

theorem ordinary_reaches_shortcut_iterate (k q : ℕ) :
    Erdos1135Predecessor.Reaches q (iterate k q) := by
  induction k with
  | zero => exact Erdos1135Predecessor.reaches_refl q
  | succ k ih => exact ih.trans (ordinary_reaches_shortcut_step (iterate k q))

theorem shortcut_basin_subset_ordinary_predecessors {a : ℕ} (ha : 0 < a) :
    {q : ℕ | ∃ k : ℕ, iterate k q = a} ⊆ ordinaryPredecessorSet a := by
  intro q hq
  obtain ⟨k, hk⟩ := hq
  have hpos : 0 < q := by
    by_contra h
    have hzero : q = 0 := by omega
    rw [hzero, iterate_zero] at hk
    omega
  exact ⟨hpos, by simpa only [hk] using ordinary_reaches_shortcut_iterate k q⟩

theorem natCount_eq_indicator_sum (S : Set ℕ) (X : ℕ) :
    (Erdos1135Predecessor.Terras.natCount S X : ℝ) =
      ∑ q ∈ Finset.range X, if q ∈ S then (1 : ℝ) else 0 := by
  classical
  unfold Erdos1135Predecessor.Terras.natCount
  induction X with
  | zero => simp
  | succ X ih =>
    rw [Nat.count_succ, Nat.cast_add, ih, Finset.sum_range_succ]
    congr 1
    split_ifs <;> norm_num

theorem shortcut_basin_prefix_le_ordinary_count {a : ℕ} (ha : 0 < a) (X : ℕ) :
    (∑ q ∈ Finset.range X, basinIndicator a q) ≤
      (Erdos1135Predecessor.Terras.natCount (ordinaryPredecessorSet a) X : ℝ) := by
  classical
  rw [natCount_eq_indicator_sum]
  apply Finset.sum_le_sum
  intro q _
  by_cases hq : ∃ k : ℕ, iterate k q = a
  · rw [basinIndicator, if_pos hq,
      if_pos (shortcut_basin_subset_ordinary_predecessors ha hq)]
  · rw [basinIndicator, if_neg hq]
    split_ifs <;> norm_num

theorem ordinary_predecessors_polynomial_lower_count
    {a : ℕ} (ha : 0 < a) (hunit : a % 3 ≠ 0) :
    ∃ X0 : ℕ, ∀ X : ℕ, X0 ≤ X →
      (3 / (256 * (predecessorSeedMultiplier : ℝ) * (a : ℝ))) * (X : ℝ) ≤
        (Erdos1135Predecessor.Terras.natCount (ordinaryPredecessorSet a) X : ℝ) := by
  have hKpos : (0 : ℝ) < predecessorSeedMultiplier := by
    exact_mod_cast predecessorSeedMultiplier_pos
  have hapos : (0 : ℝ) < a := by exact_mod_cast ha
  have hlo : (0 : ℝ) < 3 / (256 * (predecessorSeedMultiplier : ℝ) * (a : ℝ)) :=
    div_pos (by norm_num) (mul_pos (mul_pos (by norm_num) hKpos) hapos)
  have htwice : 3 / (128 * (predecessorSeedMultiplier : ℝ) * (a : ℝ)) =
      2 * (3 / (256 * (predecessorSeedMultiplier : ℝ) * (a : ℝ))) := by ring
  have hstrict : 3 / (256 * (predecessorSeedMultiplier : ℝ) * (a : ℝ)) <
      actualBasinDensity a := by
    have h := actual_basin_polynomial_lower_density ha hunit
    rw [htwice] at h
    linarith only [h, hlo]
  obtain ⟨X0, hX0⟩ := eventually_atTop.mp
    ((actual_basin_sourceMean a).eventually_const_lt hstrict)
  refine ⟨max X0 1, ?_⟩
  intro X hX
  have hXpos : (0 : ℝ) < X := by exact_mod_cast (show 0 < X by omega)
  have hbound := (lt_div_iff₀ hXpos).mp (hX0 X (by omega))
  exact hbound.le.trans (shortcut_basin_prefix_le_ordinary_count ha X)

theorem exists_uniform_ordinary_predecessor_polynomial_lower_count :
    ∃ c : ℝ, 0 < c ∧ ∀ a : ℕ, 0 < a → a % 3 ≠ 0 →
      ∃ X0 : ℕ, ∀ X : ℕ, X0 ≤ X →
        (c / (a : ℝ)) * (X : ℝ) ≤
          (Erdos1135Predecessor.Terras.natCount (ordinaryPredecessorSet a) X : ℝ) := by
  have hKpos : (0 : ℝ) < predecessorSeedMultiplier := by
    exact_mod_cast predecessorSeedMultiplier_pos
  refine ⟨3 / (256 * (predecessorSeedMultiplier : ℝ)), by positivity, ?_⟩
  intro a ha hunit
  simpa only [div_div] using ordinary_predecessors_polynomial_lower_count ha hunit


theorem raw_hit_implies_shortcut_hit_or_bypass (k q a : ℕ)
    (h : rawIterate k q = a) :
    (∃ j : ℕ, iterate j q = a) ∨
      (a % 6 = 4 ∧ ∃ j : ℕ, iterate j q = (a - 1) / 3) := by
  induction k using Nat.strong_induction_on generalizing q with
  | h k ih =>
    have hlift (b : ℕ) (hhit : ∃ j : ℕ, iterate j (step q) = b) :
        ∃ j : ℕ, iterate j q = b := by
      obtain ⟨j, hj⟩ := hhit
      exact ⟨j + 1, by rw [← iterate_step]; exact hj⟩
    cases k with
    | zero => exact Or.inl ⟨0, h⟩
    | succ k =>
      by_cases he : q % 2 = 0
      · have hs : rawStep q = step q := by simp only [rawStep, step, if_pos he]
        have hh : rawIterate k (step q) = a := by
          simpa only [rawIterate, hs] using h
        rcases ih k (by omega) (step q) hh with ha | ⟨hmod, hb⟩
        · exact Or.inl (hlift a ha)
        · exact Or.inr ⟨hmod, hlift _ hb⟩
      · have ho : q % 2 = 1 := by omega
        have hr : rawStep q = 3 * q + 1 := by simp only [rawStep, if_neg he]
        cases k with
        | zero =>
          have ha : 3 * q + 1 = a := by simpa only [rawIterate, hr] using h
          exact Or.inr ⟨by omega, 0, by simp only [iterate]; omega⟩
        | succ k =>
          have heven : rawStep q % 2 = 0 := by rw [hr]; omega
          have hs : rawStep (rawStep q) = step q := by
            calc
              rawStep (rawStep q) = rawStep q / 2 := if_pos heven
              _ = step q := by simp only [hr, step, if_neg he]
          have hh : rawIterate k (step q) = a := by
            simpa only [rawIterate, hs] using h
          rcases ih k (by omega) (step q) hh with ha | ⟨hmod, hb⟩
          · exact Or.inl (hlift a ha)
          · exact Or.inr ⟨hmod, hlift _ hb⟩

theorem ordinary_reaches_iff_shortcut_hit_or_bypass (q a : ℕ) :
    Erdos1135Predecessor.Reaches q a ↔
      (∃ j : ℕ, iterate j q = a) ∨
        (a % 6 = 4 ∧ ∃ j : ℕ, iterate j q = (a - 1) / 3) := by
  constructor
  · rintro ⟨k, hk⟩
    apply raw_hit_implies_shortcut_hit_or_bypass k q a
    simpa only [rawIterate_eq_predecessor_native] using hk
  · rintro (⟨j, hj⟩ | ⟨hmod, j, hj⟩)
    · simpa only [hj] using ordinary_reaches_shortcut_iterate j q
    · have hodd : ((a - 1) / 3) % 2 ≠ 0 := by omega
      have hstep : rawStep ((a - 1) / 3) = a := by
        rw [rawStep, if_neg hodd]
        omega
      have hlast : Erdos1135Predecessor.Reaches ((a - 1) / 3) a :=
        Erdos1135Predecessor.reaches_of_step_eq
          ((rawStep_eq_predecessor_native _).symm.trans hstep)
      have hfirst : Erdos1135Predecessor.Reaches q ((a - 1) / 3) := by
        simpa only [hj] using ordinary_reaches_shortcut_iterate j q
      exact hfirst.trans hlast


theorem mem_ordinary_predecessors_iff {a : ℕ} (ha : 0 < a) (q : ℕ) :
    q ∈ ordinaryPredecessorSet a ↔
      (∃ j : ℕ, iterate j q = a) ∨
        (a % 6 = 4 ∧ ∃ j : ℕ, iterate j q = (a - 1) / 3) := by
  constructor
  · intro hq
    exact (ordinary_reaches_iff_shortcut_hit_or_bypass q a).mp hq.2
  · intro hq
    refine ⟨?_, (ordinary_reaches_iff_shortcut_hit_or_bypass q a).mpr hq⟩
    by_contra hpos
    have hzero : q = 0 := by omega
    rcases hq with ⟨j, hj⟩ | ⟨hmod, j, hj⟩ <;>
      rw [hzero, iterate_zero] at hj <;> omega

theorem shortcut_hits_trans {q a b : ℕ}
    (hqa : ∃ i : ℕ, iterate i q = a) (hab : ∃ j : ℕ, iterate j a = b) :
    ∃ k : ℕ, iterate k q = b := by
  obtain ⟨i, hi⟩ := hqa
  obtain ⟨j, hj⟩ := hab
  exact ⟨i + j, by rw [iterate_add, hi, hj]⟩

theorem shortcut_targets_comparable {q a b : ℕ}
    (hqa : ∃ i : ℕ, iterate i q = a) (hqb : ∃ j : ℕ, iterate j q = b) :
    (∃ k : ℕ, iterate k a = b) ∨ (∃ k : ℕ, iterate k b = a) := by
  obtain ⟨i, hi⟩ := hqa
  obtain ⟨j, hj⟩ := hqb
  rcases le_total i j with hij | hji
  · left
    refine ⟨j - i, ?_⟩
    rw [← hi, ← iterate_add, Nat.add_sub_of_le hij]
    exact hj
  · right
    refine ⟨i - j, ?_⟩
    rw [← hj, ← iterate_add, Nat.add_sub_of_le hji]
    exact hi

theorem ordinary_count_natural_density_exists {a : ℕ} (ha : 0 < a) :
    ∃ d : ℝ, Tendsto (fun X : ℕ =>
      (Erdos1135Predecessor.Terras.natCount (ordinaryPredecessorSet a) X : ℝ) / (X : ℝ))
      atTop (𝓝 d) := by
  by_cases hmod : a % 6 = 4
  · let b := (a - 1) / 3
    by_cases hab : ∃ k : ℕ, iterate k a = b
    · have hmem (q : ℕ) : q ∈ ordinaryPredecessorSet a ↔
          ∃ k : ℕ, iterate k q = b := by
        rw [mem_ordinary_predecessors_iff ha q]
        constructor
        · rintro (hq | ⟨_, hq⟩)
          · exact shortcut_hits_trans hq hab
          · exact hq
        · intro hq
          exact Or.inr ⟨hmod, hq⟩
      refine ⟨actualBasinDensity b, ?_⟩
      convert actual_basin_sourceMean b using 1
      funext X
      congr 1
      rw [natCount_eq_indicator_sum]
      apply Finset.sum_congr rfl
      intro q _
      simp only [hmem, basinIndicator]
    · by_cases hba : ∃ k : ℕ, iterate k b = a
      · have hmem (q : ℕ) : q ∈ ordinaryPredecessorSet a ↔
            ∃ k : ℕ, iterate k q = a := by
          rw [mem_ordinary_predecessors_iff ha q]
          constructor
          · rintro (hq | ⟨_, hq⟩)
            · exact hq
            · exact shortcut_hits_trans hq hba
          · intro hq
            exact Or.inl hq
        refine ⟨actualBasinDensity a, ?_⟩
        convert actual_basin_sourceMean a using 1
        funext X
        congr 1
        rw [natCount_eq_indicator_sum]
        apply Finset.sum_congr rfl
        intro q _
        simp only [hmem, basinIndicator]
      · have hsum (X : ℕ) :
            (Erdos1135Predecessor.Terras.natCount (ordinaryPredecessorSet a) X : ℝ) =
              (∑ q ∈ Finset.range X, basinIndicator a q) +
              (∑ q ∈ Finset.range X, basinIndicator b q) := by
          rw [natCount_eq_indicator_sum, ← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl
          intro q _
          rw [mem_ordinary_predecessors_iff ha q]
          by_cases hqa : ∃ k : ℕ, iterate k q = a
          · have hqb : ¬ ∃ k : ℕ, iterate k q = b := by
              intro hqb
              exact (shortcut_targets_comparable hqa hqb).elim hab hba
            simp only [hqa, hqb, hmod, basinIndicator, b, true_or, if_true,
              if_false, add_zero]
          · by_cases hqb : ∃ k : ℕ, iterate k q = b
            · simp only [basinIndicator, hqa, hqb, hmod, b, false_or, true_and,
                if_true, if_false, zero_add]
            · simp only [basinIndicator, hqa, hqb, hmod, b, false_or, true_and,
                if_false, add_zero]
        refine ⟨actualBasinDensity a + actualBasinDensity b, ?_⟩
        convert (actual_basin_sourceMean a).add (actual_basin_sourceMean b) using 1
        funext X
        rw [hsum, add_div]
        rfl
  · refine ⟨actualBasinDensity a, ?_⟩
    convert actual_basin_sourceMean a using 1
    funext X
    congr 1
    rw [natCount_eq_indicator_sum]
    apply Finset.sum_congr rfl
    intro q _
    simp only [mem_ordinary_predecessors_iff ha q, hmod, false_and, or_false,
      basinIndicator]


theorem ordinary_count_natural_density_ge_shortcut {a : ℕ} (ha : 0 < a) :
    ∃ d : ℝ, actualBasinDensity a ≤ d ∧ Tendsto (fun X : ℕ =>
      (Erdos1135Predecessor.Terras.natCount (ordinaryPredecessorSet a) X : ℝ) / (X : ℝ))
      atTop (𝓝 d) := by
  obtain ⟨d, hd⟩ := ordinary_count_natural_density_exists ha
  refine ⟨d, ?_, hd⟩
  apply le_of_tendsto_of_tendsto (actual_basin_sourceMean a) hd
  exact Eventually.of_forall (fun X => div_le_div_of_nonneg_right
    (shortcut_basin_prefix_le_ordinary_count ha X) (Nat.cast_nonneg X))

theorem ordinary_predecessors_polynomial_natural_density
    {a : ℕ} (ha : 0 < a) (hunit : a % 3 ≠ 0) :
    ∃ d : ℝ, 3 / (128 * (predecessorSeedMultiplier : ℝ) * (a : ℝ)) ≤ d ∧
      Tendsto (fun X : ℕ =>
        (Erdos1135Predecessor.Terras.natCount (ordinaryPredecessorSet a) X : ℝ) / (X : ℝ))
        atTop (𝓝 d) := by
  obtain ⟨d, hda, hd⟩ := ordinary_count_natural_density_ge_shortcut ha
  exact ⟨d, (actual_basin_polynomial_lower_density ha hunit).trans hda, hd⟩

theorem exists_uniform_ordinary_predecessor_polynomial_natural_density :
    ∃ c : ℝ, 0 < c ∧ ∀ a : ℕ, 0 < a → a % 3 ≠ 0 →
      ∃ d : ℝ, c / (a : ℝ) ≤ d ∧ Tendsto (fun X : ℕ =>
        (Erdos1135Predecessor.Terras.natCount (ordinaryPredecessorSet a) X : ℝ) / (X : ℝ))
        atTop (𝓝 d) := by
  have hKpos : (0 : ℝ) < predecessorSeedMultiplier := by
    exact_mod_cast predecessorSeedMultiplier_pos
  refine ⟨3 / (128 * (predecessorSeedMultiplier : ℝ)), by positivity, ?_⟩
  intro a ha hunit
  simpa only [div_div] using ordinary_predecessors_polynomial_natural_density ha hunit

#print axioms ordinary_count_natural_density_ge_shortcut
#print axioms ordinary_predecessors_polynomial_natural_density
#print axioms exists_uniform_ordinary_predecessor_polynomial_natural_density

#print axioms ordinary_count_natural_density_exists

#print axioms ordinary_reaches_iff_shortcut_hit_or_bypass

#print axioms ordinary_reaches_shortcut_iterate
#print axioms shortcut_basin_subset_ordinary_predecessors
#print axioms ordinary_predecessors_polynomial_lower_count
#print axioms exists_uniform_ordinary_predecessor_polynomial_lower_count

end
end CollatzCanonical.PeriodicCensusFloor
