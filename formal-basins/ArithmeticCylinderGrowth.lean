import EndpointTailBounds

set_option autoImplicit false

namespace CollatzCylinderPacking.Arithmetic

/-- At fixed total length, valid endpoints are distinct positive integers
bounded by the homogeneous inverse affine expression. -/
theorem validFiber_scaled_card_le {k N A : ℕ} (hk : 0 < k) (hN : 0 < N) :
    3 ^ k * (validFiber k N A).card ≤ 2 ^ A * N := by
  classical
  let B := 2 ^ A * N / 3 ^ k
  have hp (w : GeometricWord k) (hw : w ∈ validFiber k N A) :
      0 < tupleEndpoint N (wordList k w) ∧ tupleEndpoint N (wordList k w) ≤ B := by
    have hh := (mem_validFiber k N A w).mp hw
    refine ⟨(valid_tuple_path hN hh.2).1, ?_⟩
    have hb := valid_word_endpoint_bound hN hh.2
    rw [hh.1] at hb
    dsimp [B]
    exact (Nat.le_div_iff_mul_le (by positivity)).mpr (by nlinarith [hb])
  have hm : Set.MapsTo (fun w => tupleEndpoint N (wordList k w) - 1)
      (validFiber k N A) (Finset.range B) := by
    intro w hw
    have hh := hp w hw
    simp only [Finset.mem_coe, Finset.mem_range]
    omega
  have hi : Set.InjOn (fun w => tupleEndpoint N (wordList k w) - 1)
      (validFiber k N A) := by
    intro w hw v hv he
    have hpw := hp w hw
    have hpv := hp v hv
    have hw' := (mem_validFiber k N A w).mp hw
    have hv' := (mem_validFiber k N A v).mp hv
    apply wordList_injective k
    apply admissible_endpoint_injective (valid_word_admissible hk hN hw'.2)
      (valid_word_admissible hk hN hv'.2)
    · simp only [wordList_sum, hw'.1, hv'.1]
    · dsimp only at he
      omega
  have hc : (validFiber k N A).card ≤ B := by
    simpa only [Finset.card_range] using Finset.card_le_card_of_injOn _ hm hi
  calc
    3 ^ k * (validFiber k N A).card ≤ 3 ^ k * B := Nat.mul_le_mul_left _ hc
    _ ≤ 2 ^ A * N := by dsimp [B]; exact Nat.mul_div_le _ _

/-- The total inverse weight at one fixed total length is at most the target. -/
theorem validFiber_weight_le {k N A : ℕ} (hk : 0 < k) (hN : 0 < N) :
    (3 : ℝ) ^ k * ((validFiber k N A).card : ℝ) * (1 / 2 : ℝ) ^ A ≤ N := by
  have hb : (3 : ℝ) ^ k * ((validFiber k N A).card : ℝ) ≤ (2 : ℝ) ^ A * N := by
    exact_mod_cast validFiber_scaled_card_le (A := A) hk hN
  calc
    (3 : ℝ) ^ k * ((validFiber k N A).card : ℝ) * (1 / 2 : ℝ) ^ A ≤
        ((2 : ℝ) ^ A * N) * (1 / 2 : ℝ) ^ A :=
      mul_le_mul_of_nonneg_right hb (by positivity)
    _ = N := by rw [one_div_pow]; field_simp

noncomputable def growthHeadSet (k N : ℕ) : Finset (GeometricWord k) := by
  classical
  exact (wordBox k (6 * k)).filter (fun w => ValidWord k N w ∧ wordLength k w < 6 * k)

theorem mem_growthHeadSet (k N : ℕ) (w : GeometricWord k) :
    w ∈ growthHeadSet k N ↔ ValidWord k N w ∧ wordLength k w < 6 * k := by
  classical
  simp only [growthHeadSet, Finset.mem_filter]
  exact ⟨And.right, fun h => ⟨word_mem_box_of_length_lt k (6 * k) w h.2, h⟩⟩

theorem growthHeadSet_fiber (k N i : ℕ) (hi : i < 5 * k) :
    (growthHeadSet k N).filter (fun w => wordLength k w - k = i) =
      validFiber k N (k + i) := by
  classical
  ext w
  rw [Finset.mem_filter, mem_growthHeadSet, mem_validFiber]
  have hg := wordLength_ge_depth k w
  constructor
  · rintro ⟨⟨hv, hl⟩, he⟩
    exact ⟨by omega, hv⟩
  · rintro ⟨he, hv⟩
    exact ⟨⟨hv, by omega⟩, by omega⟩

noncomputable def arithmeticGrowthHeadTerm (k N : ℕ) (w : GeometricWord k) : ℝ := by
  classical
  exact if w ∈ growthHeadSet k N then (1 / 2 : ℝ) ^ wordLength k w else 0

theorem arithmeticGrowthHeadTerm_summable (k N : ℕ) :
    Summable (arithmeticGrowthHeadTerm k N) := by
  classical
  apply Summable.of_nonneg_of_le _ _ (geometric_word_probability k).summable
  · intro w
    unfold arithmeticGrowthHeadTerm
    split_ifs <;> positivity
  · intro w
    unfold arithmeticGrowthHeadTerm
    split_ifs
    · exact le_rfl
    · positivity

theorem arithmetic_growth_term_split (k N : ℕ) (w : GeometricWord k) :
    arithmeticTerm k N w = arithmeticGrowthHeadTerm k N w +
      arithmeticLengthTailTerm k N (6 * k) w := by
  classical
  by_cases hv : ValidWord k N w
  · by_cases hl : wordLength k w < 6 * k
    · simp [arithmeticTerm, arithmeticGrowthHeadTerm, arithmeticLengthTailTerm,
        mem_growthHeadSet, hv, hl, Nat.not_le.mpr hl]
    · simp [arithmeticTerm, arithmeticGrowthHeadTerm, arithmeticLengthTailTerm,
        mem_growthHeadSet, hv, hl, Nat.le_of_not_gt hl]
  · simp [arithmeticTerm, arithmeticGrowthHeadTerm, arithmeticLengthTailTerm,
      mem_growthHeadSet, hv]

theorem arithmeticGrowthHeadTerm_tsum (k N : ℕ) :
    (∑' w : GeometricWord k, arithmeticGrowthHeadTerm k N w) =
      ∑ w ∈ growthHeadSet k N, (1 / 2 : ℝ) ^ wordLength k w := by
  classical
  rw [tsum_eq_sum (s := growthHeadSet k N)
    (fun w hw => by simp [arithmeticGrowthHeadTerm, hw])]
  apply Finset.sum_congr rfl
  intro w hw
  simp [arithmeticGrowthHeadTerm, hw]

theorem arithmetic_growth_head_fiberwise (k N : ℕ) :
    (∑ w ∈ growthHeadSet k N, (1 / 2 : ℝ) ^ wordLength k w) =
      ∑ i ∈ Finset.range (5 * k), ((validFiber k N (k + i)).card : ℝ) *
        (1 / 2 : ℝ) ^ (k + i) := by
  classical
  have hm : ∀ w ∈ growthHeadSet k N, wordLength k w - k ∈ Finset.range (5 * k) := by
    intro w hw
    have hl := ((mem_growthHeadSet k N w).mp hw).2
    have hg := wordLength_ge_depth k w
    apply Finset.mem_range.mpr
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hm (fun w => (1 / 2 : ℝ) ^ wordLength k w)]
  apply Finset.sum_congr rfl
  intro i hi
  rw [growthHeadSet_fiber k N i (Finset.mem_range.mp hi)]
  calc
    (∑ w ∈ validFiber k N (k + i), (1 / 2 : ℝ) ^ wordLength k w) =
        ∑ _w ∈ validFiber k N (k + i), (1 / 2 : ℝ) ^ (k + i) := by
      apply Finset.sum_congr rfl
      intro w hw
      rw [((mem_validFiber k N (k + i) w).mp hw).1]
    _ = ((validFiber k N (k + i)).card : ℝ) * (1 / 2 : ℝ) ^ (k + i) := by
      rw [Finset.sum_const, nsmul_eq_mul]

theorem arithmetic_growth_head_bound {k N : ℕ} (hk : 0 < k) (hN : 0 < N) :
    (3 : ℝ) ^ k * (∑' w : GeometricWord k, arithmeticGrowthHeadTerm k N w) ≤
      5 * (k : ℝ) * N := by
  rw [arithmeticGrowthHeadTerm_tsum, arithmetic_growth_head_fiberwise, Finset.mul_sum]
  calc
    (∑ i ∈ Finset.range (5 * k), (3 : ℝ) ^ k *
      (((validFiber k N (k + i)).card : ℝ) * (1 / 2 : ℝ) ^ (k + i))) ≤
        ∑ _i ∈ Finset.range (5 * k), (N : ℝ) := by
      apply Finset.sum_le_sum
      intro i _
      simpa only [mul_assoc] using validFiber_weight_le (A := k + i) hk hN
    _ = 5 * (k : ℝ) * N := by simp

/-- Lemma 13's integer-height bound for the actual arithmetic cylinder law. -/
theorem arithmetic_rho_growth {k N : ℕ} (hk : 0 < k) (hN : 0 < N) :
    (3 : ℝ) ^ k * arithmeticMass k N ≤ 5 * (k : ℝ) * N + (64 / 81 : ℝ) ^ k := by
  unfold arithmeticMass
  simp_rw [arithmetic_growth_term_split]
  rw [Summable.tsum_add (arithmeticGrowthHeadTerm_summable k N)
    (arithmetic_length_tail_summable k N (6 * k)), mul_add]
  exact add_le_add (arithmetic_growth_head_bound hk hN) (arithmetic_six_depth_tail k N)

theorem arithmetic_mass_nonneg (k N : ℕ) : 0 ≤ arithmeticMass k N :=
  tsum_nonneg (arithmeticTerm_nonneg k N)

theorem arithmetic_mass_le_one (k N : ℕ) : arithmeticMass k N ≤ 1 := by
  exact (Summable.tsum_le_tsum (arithmeticTerm_le_probability k N)
    (arithmeticTerm_summable k N) (geometric_word_probability k).summable).trans_eq
      (geometric_word_probability k).tsum_eq

/-- A linear bound valid also at depth zero. -/
theorem arithmetic_rho_linear_bound {N : ℕ} (hN : 0 < N) (k : ℕ) :
    (3 : ℝ) ^ k * arithmeticMass k N ≤ 5 * (k : ℝ) * N + 1 := by
  by_cases hk : 0 < k
  · exact (arithmetic_rho_growth hk hN).trans (add_le_add le_rfl
      (pow_le_one₀ (by norm_num : (0 : ℝ) ≤ 64 / 81) (by norm_num)))
  · have he : k = 0 := by omega
    subst k
    simpa using arithmetic_mass_le_one 0 N

/-- The depth-generating series defining the Abel cylinder mean is summable. -/
theorem arithmetic_rho_abel_summable {N : ℕ} (hN : 0 < N)
    {z : ℝ} (hz : 0 ≤ z) (hz1 : z < 1) :
    Summable (fun k : ℕ => z ^ k * ((3 : ℝ) ^ k * arithmeticMass k N)) := by
  have hnorm : ‖z‖ < 1 := by simpa only [Real.norm_eq_abs, abs_of_nonneg hz] using hz1
  have hs : Summable (fun k : ℕ => z ^ k * (5 * (k : ℝ) * N + 1)) := by
    have hlin := (summable_pow_mul_geometric_of_norm_lt_one 1 hnorm).mul_left (5 * (N : ℝ))
    have hgeom := summable_geometric_of_lt_one hz hz1
    convert hlin.add hgeom using 1
    ext k
    simp only [pow_one]
    ring
  apply Summable.of_nonneg_of_le _ _ hs
  · intro k
    exact mul_nonneg (pow_nonneg hz k)
      (mul_nonneg (by positivity) (arithmetic_mass_nonneg k N))
  · intro k
    exact mul_le_mul_of_nonneg_left (arithmetic_rho_linear_bound hN k) (pow_nonneg hz k)

end CollatzCylinderPacking.Arithmetic
