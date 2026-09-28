import FirstHitWordWeights
import EndpointTailBounds

set_option autoImplicit false

namespace CollatzCylinderPacking.Arithmetic

/-- A finite family of actual first hits at one odd-source depth injects into
its endpoint-restricted arithmetic word sum. -/
theorem first_hit_fixed_depth_tail_le (k N H : ℕ) (Q : Finset ℕ) (time : ℕ → ℕ)
    (hpos : ∀ q ∈ Q, 0 < q) (hodd : ∀ q ∈ Q, q % 2 = 1)
    (hfirst : ∀ q ∈ Q, FirstHit q N (time q))
    (hdepth : ∀ q ∈ Q, oddCount (time q) q = k)
    (hheight : ∀ q ∈ Q, N * 2 ^ H < q) :
    (∑ q ∈ Q, (N : ℝ) * firstHitWeight N q / q) ≤
      (3 : ℝ) ^ k * (∑' w : GeometricWord k, arithmeticEndpointTailTerm k N H w) := by
  classical
  have hex (q : ℕ) (hq : q ∈ Q) : ∃ w : GeometricWord k,
      tupleEndpoint N (wordList k w) = q ∧
        (3 : ℝ) ^ k * arithmeticEndpointTailTerm k N H w = (N : ℝ) * firstHitWeight N q / q := by
    have hh := first_hit_word_weight (hpos q hq) (hodd q hq) (hfirst q hq)
    rw [hdepth q hq] at hh
    obtain ⟨w, hv, hl, he, hw⟩ := hh
    refine ⟨w, he, ?_⟩
    simpa only [arithmeticEndpointTailTerm, he, if_pos (hheight q hq)] using hw
  have hne (k : ℕ) : Nonempty (GeometricWord k) := by
    induction k with
    | zero => exact ⟨()⟩
    | succ k ih => exact ⟨(0, Classical.choice ih)⟩
  let f : ℕ → GeometricWord k := fun q =>
    if hq : q ∈ Q then Classical.choose (hex q hq) else Classical.choice (hne k)
  have hf (q : ℕ) (hq : q ∈ Q) :
      tupleEndpoint N (wordList k (f q)) = q ∧
        (3 : ℝ) ^ k * arithmeticEndpointTailTerm k N H (f q) = (N : ℝ) * firstHitWeight N q / q := by
    dsimp only [f]
    rw [dif_pos hq]
    exact Classical.choose_spec (hex q hq)
  have hi : Set.InjOn f Q := by
    intro q hq r hr he
    have hq' := (hf q hq).1
    have hr' := (hf r hr).1
    rw [he] at hq'
    exact hq'.symm.trans hr'
  have hs := (arithmetic_endpoint_tail_summable k N H).mul_left ((3 : ℝ) ^ k)
  calc
    (∑ q ∈ Q, (N : ℝ) * firstHitWeight N q / q) =
        ∑ q ∈ Q, (3 : ℝ) ^ k * arithmeticEndpointTailTerm k N H (f q) := by
      apply Finset.sum_congr rfl
      intro q hq
      exact (hf q hq).2.symm
    _ = ∑ w ∈ Q.image f, (3 : ℝ) ^ k * arithmeticEndpointTailTerm k N H w :=
      (Finset.sum_image (f := fun w => (3 : ℝ) ^ k * arithmeticEndpointTailTerm k N H w) hi).symm
    _ ≤ ∑' w : GeometricWord k, (3 : ℝ) ^ k * arithmeticEndpointTailTerm k N H w := by
      apply hs.sum_le_tsum
      intro w _
      exact mul_nonneg (by positivity) (arithmeticEndpointTailTerm_nonneg k N H w)
    _ = (3 : ℝ) ^ k * (∑' w : GeometricWord k, arithmeticEndpointTailTerm k N H w) :=
      tsum_mul_left

/-- A nonempty shortcut path from an odd start has at least one odd source. -/
theorem oddCount_pos_of_odd_start {A q : ℕ} (hA : 0 < A) (hodd : q % 2 = 1) :
    0 < oddCount A q := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hA)
  rw [LowerBranch.oddCount_succ_first, hodd]
  omega

/-- The endpoint cutoff transferred to finite actual first-hit families.
The height cutoff automatically excludes the depth-zero path. -/
theorem first_hit_finite_family_tail {N : ℕ} (hN : 0 < N) (K : ℕ)
    (Q : Finset ℕ) (time : ℕ → ℕ)
    (hpos : ∀ q ∈ Q, 0 < q) (hodd : ∀ q ∈ Q, q % 2 = 1)
    (hfirst : ∀ q ∈ Q, FirstHit q N (time q))
    (hdepth : ∀ q ∈ Q, oddCount (time q) q ≤ K)
    (hheight : ∀ q ∈ Q, N * 2 ^ (6 * K) < q) :
    (∑ q ∈ Q, (N : ℝ) * firstHitWeight N q / q) ≤ (9 / 8 : ℝ) * (64 / 81 : ℝ) ^ K := by
  classical
  have hpdepth (q : ℕ) (hq : q ∈ Q) : 0 < oddCount (time q) q := by
    apply oddCount_pos_of_odd_start _ (hodd q hq)
    by_contra h
    have ht : time q = 0 := by omega
    have hqN : q = N := by simpa only [ht, iterate] using (hfirst q hq).1
    have hheight' := hheight q hq
    have hpow : 1 ≤ (2 : ℕ) ^ (6 * K) := Nat.one_le_pow _ _ (by decide)
    have hmul := Nat.mul_le_mul_left N hpow
    omega
  have hm : ∀ q ∈ Q, oddCount (time q) q - 1 ∈ Finset.range K := by
    intro q hq
    have hp := hpdepth q hq
    have hd := hdepth q hq
    exact Finset.mem_range.mpr (by omega)
  rw [← Finset.sum_fiberwise_of_maps_to hm (fun q => (N : ℝ) * firstHitWeight N q / q)]
  calc
    (∑ j ∈ Finset.range K,
      ∑ q ∈ Q.filter (fun q => oddCount (time q) q - 1 = j), (N : ℝ) * firstHitWeight N q / q) ≤
        ∑ j ∈ Finset.range K, (3 : ℝ) ^ (j + 1) *
          (∑' w : GeometricWord (j + 1), arithmeticEndpointTailTerm (j + 1) N (6 * K) w) := by
      apply Finset.sum_le_sum
      intro j hj
      apply first_hit_fixed_depth_tail_le (j + 1) N (6 * K) _ time
      · intro q hq
        exact hpos q (Finset.mem_filter.mp hq).1
      · intro q hq
        exact hodd q (Finset.mem_filter.mp hq).1
      · intro q hq
        exact hfirst q (Finset.mem_filter.mp hq).1
      · intro q hq
        obtain ⟨hq, hj⟩ := Finset.mem_filter.mp hq
        have hp := hpdepth q hq
        omega
      · intro q hq
        exact hheight q (Finset.mem_filter.mp hq).1
    _ ≤ (9 / 8 : ℝ) * (64 / 81 : ℝ) ^ K := arithmetic_endpoint_cutoff hN K

end CollatzCylinderPacking.Arithmetic
