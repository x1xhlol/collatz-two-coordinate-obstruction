import NativeWeightedPassageComparison

set_option autoImplicit false

namespace CollatzCylinderPacking.Arithmetic

noncomputable def basinIndicator (N q : ℕ) : ℝ := by
  classical
  exact if ∃ A, iterate A q = N then 1 else 0

theorem basinIndicator_bounds (N q : ℕ) :
    0 ≤ basinIndicator N q ∧ basinIndicator N q ≤ 1 := by
  unfold basinIndicator
  split_ifs <;> norm_num

theorem basinIndicator_prefix {A q N : ℕ}
    (havoid : ∀ i < A, iterate i q ≠ N) :
    basinIndicator N q = basinIndicator N (iterate A q) := by
  unfold basinIndicator
  rw [hit_iff_suffix_of_prefix_avoids havoid]

theorem basinIndicator_barrier {q l N : ℕ} {M : ℝ}
    (hN : (N : ℝ) ≤ M) (h : GoodOddBarrierLanding q l N M) :
    basinIndicator N q = basinIndicator N l := by
  obtain ⟨A, hpass, rfl, hland⟩ := h
  exact basinIndicator_prefix (hpass.prefix_avoids_of_landing_gt hN hland)

theorem basinIndicator_self (N : ℕ) : basinIndicator N N = 1 := by
  classical
  simp only [basinIndicator, if_pos (show ∃ A, iterate A N = N from ⟨0, rfl⟩)]

theorem basinIndicator_halving {N q : ℕ} (hne : 2 * q ≠ N) :
    basinIndicator N (2 * q) = basinIndicator N q := by
  have h := basinIndicator_prefix (A := 1) (q := 2 * q) (N := N) (by
    intro i hi
    have hi0 : i = 0 := by omega
    simpa only [hi0, iterate] using hne)
  simpa only [iterate, step_two_mul] using h

theorem basinIndicator_halving_defect (N q : ℕ) :
    0 ≤ basinIndicator N (2 * q) - basinIndicator N q ∧
      basinIndicator N (2 * q) - basinIndicator N q ≤ 1 := by
  by_cases h : 2 * q = N
  · rw [h, basinIndicator_self]
    have hb := basinIndicator_bounds N q
    constructor <;> linarith
  · rw [basinIndicator_halving h]
    norm_num

end CollatzCylinderPacking.Arithmetic

namespace CollatzCanonical.NativeTao
open Erdos1135 CollatzCylinderPacking.Arithmetic

/-- Basin membership is exactly preserved on a target-avoiding passage;
only exceptional probability and landing-law variation affect its mean. -/
theorem native_basin_passage_expectation {ι κ η : Type*}
    [Fintype ι] [Fintype κ] [Fintype η]
    (p : PMF ι) (q : PMF κ) (startP : ι → ℕ) (startQ : κ → ℕ)
    (landingP : ι → η) (landingQ : κ → η) (value : η → ℕ)
    (badP : ι → Prop) (badQ : κ → Prop) (N : ℕ) (M : ℝ)
    (hN : (N : ℝ) ≤ M)
    (hgoodP : ∀ i, ¬badP i → GoodOddBarrierLanding (startP i) (value (landingP i)) N M)
    (hgoodQ : ∀ i, ¬badQ i → GoodOddBarrierLanding (startQ i) (value (landingQ i)) N M) :
    |Tao.pmfExpectation p (fun i => basinIndicator N (startP i)) -
      Tao.pmfExpectation q (fun i => basinIndicator N (startQ i))| ≤
      Tao.pmfProb p {i | badP i} + Tao.pmfProb q {i | badQ i} +
        Tao.taoTV (p.map landingP) (q.map landingQ) := by
  have he := finiteMean_two_passage_bound
    (fun i => (p i).toReal) (fun i => (q i).toReal)
    (fun i => basinIndicator N (startP i)) (fun i => basinIndicator N (startQ i))
    landingP landingQ (fun z => basinIndicator N (value z)) badP badQ 0 0
    (fun _ => ENNReal.toReal_nonneg) (fun _ => ENNReal.toReal_nonneg)
    (Tao.pmf_sum_toReal p) (Tao.pmf_sum_toReal q)
    (fun i => basinIndicator_bounds N (startP i))
    (fun i => basinIndicator_bounds N (startQ i))
    (fun z => basinIndicator_bounds N (value z)) le_rfl le_rfl
    (fun i hi => by dsimp only; rw [basinIndicator_barrier hN (hgoodP i hi), sub_self, abs_zero])
    (fun i hi => by dsimp only; rw [basinIndicator_barrier hN (hgoodQ i hi), sub_self, abs_zero])
  rw [finiteBadMass_eq_native_probability, finiteBadMass_eq_native_probability,
    finite_landing_fullL1_eq_native_TV] at he
  simpa only [zero_add] using he

end CollatzCanonical.NativeTao
