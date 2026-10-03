import ActualWordDepth
import CanonicalCylinderAbel
import ShortcutOddEndpoints
import NativeSyracuseClockBridge

set_option autoImplicit false
open Classical
open scoped BigOperators

namespace CollatzCanonical.PeriodicCensusFloor
open CollatzCylinderPacking CollatzCylinderPacking.Arithmetic
open CollatzCanonical.NativeTao Erdos1135

noncomputable section

theorem odd_endpoint_time_eq_of_oddCount_eq {q A B : ℕ} (hq : Odd q)
    (hA : Odd (iterate A q)) (hB : Odd (iterate B q))
    (hc : oddCount A q = oddCount B q) : A = B := by
  obtain ⟨i, hi⟩ := shortcut_odd_endpoint_is_syracuse_clock A q hq hA
  obtain ⟨j, hj⟩ := shortcut_odd_endpoint_is_syracuse_clock B q hq hB
  rw [hi, hj, syracuse_shortcut_oddCount, syracuse_shortcut_oddCount] at hc
  exact hi.trans (hc ▸ hj.symm)

theorem valid_odd_target_word_endpoint_unique {k N M : ℕ} (hk : 0 < k)
    (hN : Odd N) (hM : Odd M) {w v : GeometricWord k}
    (hw : ValidWord k N w) (hv : ValidWord k M v)
    (he : tupleEndpoint N (wordList k w) = tupleEndpoint M (wordList k v)) :
    N = M ∧ w = v := by
  have hpw := valid_tuple_path hN.pos hw
  have hpv := valid_tuple_path hM.pos hv
  rw [wordList_sum] at hpw hpv
  have hq : Odd (tupleEndpoint N (wordList k w)) :=
    Nat.odd_iff.mpr (hpw.2.2.2 (wordList_ne_nil hk w))
  have htime : wordLength k w = wordLength k v := by
    apply odd_endpoint_time_eq_of_oddCount_eq hq
    · rwa [hpw.2.1]
    · rw [he, hpv.2.1]
      exact hM
    · rw [valid_word_oddCount hN.pos hw, he, valid_word_oddCount hM.pos hv]
  have hNM : N = M := by
    rw [← hpw.2.1, htime, he, hpv.2.1]
  subst M
  refine ⟨rfl, ?_⟩
  have hinj := valid_word_endpoint_time_injective hk hN.pos
  have hh := hinj (a₁ := ⟨w, hw⟩) (a₂ := ⟨v, hv⟩) (Prod.ext he htime)
  exact congrArg Subtype.val hh

theorem valid_word_normalized_weight_le_reciprocal {k N : ℕ}
    (hN : 0 < N) {w : GeometricWord k} (hw : ValidWord k N w) :
    (3 : ℝ) ^ k * (1 / 2 : ℝ) ^ wordLength k w / (N : ℝ) ≤
      1 / (tupleEndpoint N (wordList k w) : ℝ) := by
  have hq := (valid_tuple_path hN hw).1
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hqr : (0 : ℝ) < tupleEndpoint N (wordList k w) := by exact_mod_cast hq
  have hb : (3 : ℝ) ^ k * (tupleEndpoint N (wordList k w) : ℝ) ≤
      (2 : ℝ) ^ wordLength k w * (N : ℝ) := by
    exact_mod_cast valid_word_endpoint_bound hN hw
  rw [one_div_pow, mul_one_div, div_div]
  exact (div_le_div_iff₀ (mul_pos (by positivity) hNr) hqr).mpr (by simpa using hb)

theorem growthHead_endpoint_bound {k N : ℕ} (hN : 0 < N) (hheight : N ≤ 3 ^ k)
    {w : GeometricWord k} (hw : w ∈ growthHeadSet k N) :
    tupleEndpoint N (wordList k w) ≤ 2 ^ (6 * k) := by
  obtain ⟨hv, hl⟩ := (mem_growthHeadSet k N w).mp hw
  have hb := valid_word_endpoint_bound hN hv
  have hmul := Nat.mul_le_mul_left (2 ^ wordLength k w) hheight
  have hp : 0 < (3 : ℕ) ^ k := by positivity
  have hq : tupleEndpoint N (wordList k w) ≤ 2 ^ wordLength k w := by nlinarith
  exact hq.trans (Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hl.le)

def cylinderGrowthHead (k N : ℕ) : ℝ :=
  ∑ w ∈ growthHeadSet k N, (3 : ℝ) ^ k * (1 / 2 : ℝ) ^ wordLength k w / (N : ℝ)

theorem cylinderGrowthHead_nonneg (k N : ℕ) : 0 ≤ cylinderGrowthHead k N := by
  exact Finset.sum_nonneg (fun _ _ => by positivity)

theorem cylinderGrowthHead_le_cylinder {k N : ℕ} (hN : 0 < N) :
    cylinderGrowthHead k N ≤ canonicalRho k N / (N : ℝ) := by
  rw [canonicalRho_eq_arithmetic hN]
  unfold cylinderGrowthHead
  rw [← Finset.sum_div, ← Finset.mul_sum, ← arithmeticGrowthHeadTerm_tsum]
  apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg N)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  unfold arithmeticMass
  apply Summable.tsum_le_tsum _ (arithmeticGrowthHeadTerm_summable k N)
    (arithmeticTerm_summable k N)
  intro w
  unfold arithmeticGrowthHeadTerm arithmeticTerm
  split_ifs with hmem hv hv
  · rfl
  · exact False.elim (hv ((mem_growthHeadSet k N w).mp hmem).1)
  · positivity
  · rfl

theorem cylinder_le_growthHead_add_tail {k N : ℕ} (hN : 0 < N) :
    canonicalRho k N / (N : ℝ) ≤
      cylinderGrowthHead k N + (64 / 81 : ℝ) ^ k / (N : ℝ) := by
  rw [canonicalRho_eq_arithmetic hN]
  unfold arithmeticMass
  simp_rw [arithmetic_growth_term_split]
  rw [Summable.tsum_add (arithmeticGrowthHeadTerm_summable k N)
    (arithmetic_length_tail_summable k N (6 * k)), mul_add, add_div]
  apply add_le_add _ (div_le_div_of_nonneg_right (arithmetic_six_depth_tail k N)
    (Nat.cast_nonneg N))
  unfold cylinderGrowthHead
  rw [arithmeticGrowthHeadTerm_tsum, Finset.mul_sum, Finset.sum_div]

/-- The source budget is paid once across all odd target roots at a fixed depth. -/
theorem finite_cylinderGrowthHead_transport (Q : Finset ℕ) {k : ℕ} (hk : 0 < k)
    (hodd : ∀ N ∈ Q, Odd N) (hheight : ∀ N ∈ Q, N ≤ 3 ^ k) :
    ∃ R : Finset ℕ, (∀ q ∈ R, Odd q ∧ q ≤ 2 ^ (6 * k)) ∧
      (∑ N ∈ Q, cylinderGrowthHead k N) ≤ ∑ q ∈ R, 1 / (q : ℝ) := by
  let P : Finset (Σ _ : ℕ, GeometricWord k) := Q.sigma (fun N => growthHeadSet k N)
  let endpoint : (Σ _ : ℕ, GeometricWord k) → ℕ :=
    fun p => tupleEndpoint p.1 (wordList k p.2)
  let R : Finset ℕ := P.image endpoint
  have hmem (p : Σ _ : ℕ, GeometricWord k) (hp : p ∈ P) :
      p.1 ∈ Q ∧ p.2 ∈ growthHeadSet k p.1 := Finset.mem_sigma.mp hp
  have hinj : Set.InjOn endpoint P := by
    intro p hp q hq he
    have hp' := hmem p hp
    have hq' := hmem q hq
    have hu := valid_odd_target_word_endpoint_unique hk (hodd p.1 hp'.1) (hodd q.1 hq'.1)
      ((mem_growthHeadSet k p.1 p.2).mp hp'.2).1
      ((mem_growthHeadSet k q.1 q.2).mp hq'.2).1 he
    rcases p with ⟨N, w⟩
    rcases q with ⟨M, v⟩
    dsimp only at hu
    rcases hu with ⟨rfl, rfl⟩
    rfl
  refine ⟨R, ?_, ?_⟩
  · intro q hq
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hq
    have hp' := hmem p hp
    have hv := ((mem_growthHeadSet k p.1 p.2).mp hp'.2).1
    have hpath := valid_tuple_path (hodd p.1 hp'.1).pos hv
    exact ⟨Nat.odd_iff.mpr (hpath.2.2.2 (wordList_ne_nil hk p.2)),
      growthHead_endpoint_bound (hodd p.1 hp'.1).pos (hheight p.1 hp'.1) hp'.2⟩
  · dsimp only [R]
    rw [Finset.sum_image hinj]
    have hsum := Finset.sum_le_sum (s := P) (fun p hp =>
      valid_word_normalized_weight_le_reciprocal (hodd p.1 (hmem p hp).1).pos
        ((mem_growthHeadSet k p.1 p.2).mp (hmem p hp).2).1)
    simpa only [P, Finset.sum_sigma, cylinderGrowthHead, endpoint] using hsum

#print axioms valid_odd_target_word_endpoint_unique
#print axioms finite_cylinderGrowthHead_transport
#print axioms cylinder_le_growthHead_add_tail
end
end CollatzCanonical.PeriodicCensusFloor
