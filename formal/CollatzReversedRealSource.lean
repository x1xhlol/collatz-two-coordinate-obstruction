import CollatzReversedRealGrowth

namespace CollatzResearch.RealSource

open Matrix CollatzCertificate RealAffine

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem real_powers_zero_of_first (B : Mat ι) (s t : Vec ι)
    (h : ∀ k : ℕ, k < Fintype.card ι → (s ᵥ* B ^ k) ⬝ᵥ t = 0)
    (k : ℕ) : (s ᵥ* B ^ k) ⬝ᵥ t = 0 := by
  have hne : B.charpoly ≠ 1 := by
    intro hz
    have hd := congrArg Polynomial.natDegree hz
    simp only [Matrix.charpoly_natDegree_eq_dim, Polynomial.natDegree_one] at hd
    have hp := Fintype.card_pos (α := ι)
    omega
  have hdeg : ((Polynomial.X : Polynomial ℝ) ^ k %ₘ B.charpoly).natDegree < Fintype.card ι := by
    simpa only [Matrix.charpoly_natDegree_eq_dim] using
      Polynomial.natDegree_modByMonic_lt ((Polynomial.X : Polynomial ℝ) ^ k) B.charpoly_monic hne
  rw [B.pow_eq_aeval_mod_charpoly k, Polynomial.aeval_eq_sum_range' hdeg B]
  simp only [Matrix.vecMul_sum, sum_dotProduct, vecMul_smul, smul_dotProduct]
  apply Finset.sum_eq_zero
  intro j hj
  rw [h j (Finset.mem_range.mp hj), smul_zero]

theorem real_powers_zero_of_window (B : Mat ι) (s t : Vec ι) (d : ℕ)
    (h : ∀ k : ℕ, d ≤ k → k < d + Fintype.card ι → (s ᵥ* B ^ k) ⬝ᵥ t = 0)
    (k : ℕ) (hk : d ≤ k) : (s ᵥ* B ^ k) ⬝ᵥ t = 0 := by
  have hi := real_powers_zero_of_first B (s ᵥ* B ^ d) t (by
    intro j hj
    rw [vecMul_vecMul, ← pow_add]
    exact h (d + j) (by omega) (by omega)) (k - d)
  rw [vecMul_vecMul, ← pow_add, Nat.add_sub_of_le hk] at hi
  exact hi

omit [Nonempty ι] in
theorem affine_iterate_sum (B : Affine ι) (k : ℕ) (x : Vec ι) :
    (eval B)^[k] x = B.matrix ^ k *ᵥ x + ∑ j ∈ Finset.range k, B.matrix ^ j *ᵥ B.offset := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih]
    simp only [eval, Matrix.mulVec_add, Matrix.mulVec_mulVec,
      pow_succ, Finset.sum_range_succ, add_left_comm, add_comm]

omit [Nonempty ι] in
theorem observed_affine_iterate_sum (B : Affine ι) (s x : Vec ι) (k : ℕ) :
    s ⬝ᵥ ((eval B)^[k] x) = (s ᵥ* B.matrix ^ k) ⬝ᵥ x +
      ∑ j ∈ Finset.range k, (s ᵥ* B.matrix ^ j) ⬝ᵥ B.offset := by
  rw [affine_iterate_sum]
  simp only [dotProduct_add, dotProduct_sum, dotProduct_mulVec]

omit [Nonempty ι] in
theorem observed_iterates_constant_of_zero_tail (B : Affine ι) (s x : Vec ι) (d : ℕ)
    (hB : B.Nonnegative) (hs : 0 ≤ s) (hx : 0 ≤ x)
    (h : ∀ k : ℕ, d ≤ k → (s ᵥ* B.matrix ^ k) ⬝ᵥ (x + B.offset) = 0)
    (n : ℕ) (hn : d ≤ n) : s ⬝ᵥ ((eval B)^[n] x) = s ⬝ᵥ ((eval B)^[d] x) := by
  have hz : ∀ k : ℕ, d ≤ k →
      (s ᵥ* B.matrix ^ k) ⬝ᵥ x = 0 ∧ (s ᵥ* B.matrix ^ k) ⬝ᵥ B.offset = 0 := by
    intro k hk
    have hkz := h k hk
    rw [dotProduct_add] at hkz
    have hxpos := dotProduct_nonneg_of_nonneg (rowMul_pow_nonneg hs hB.1 k) hx
    have hbpos := dotProduct_nonneg_of_nonneg (rowMul_pow_nonneg hs hB.1 k) hB.2
    constructor <;> linarith
  have hsum : (∑ j ∈ Finset.range d, (s ᵥ* B.matrix ^ j) ⬝ᵥ B.offset) =
      ∑ j ∈ Finset.range n, (s ᵥ* B.matrix ^ j) ⬝ᵥ B.offset := by
    apply Finset.sum_subset (Finset.range_mono hn)
    intro j hj hjd
    exact (hz j (by simpa only [Finset.mem_range, not_lt] using hjd)).2
  rw [observed_affine_iterate_sum, observed_affine_iterate_sum,
    (hz n hn).1, (hz d (by omega)).1, hsum]

theorem unbounded_iterates_have_finite_source_support (B : Affine ι) (s x : Vec ι)
    (hB : B.Nonnegative) (hs : 0 ≤ s) (hx : 0 ≤ x)
    (hu : ∀ K : ℝ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → K < s ⬝ᵥ ((eval B)^[n] x)) :
    ∃ k : ℕ, Fintype.card ι ≤ k ∧ k < 2 * Fintype.card ι ∧
      0 < (s ᵥ* B.matrix ^ k) ⬝ᵥ (x + B.offset) := by
  by_contra hn
  have hz : ∀ k : ℕ, Fintype.card ι ≤ k → k < Fintype.card ι + Fintype.card ι →
      (s ᵥ* B.matrix ^ k) ⬝ᵥ (x + B.offset) = 0 := by
    intro k hk hkd
    have hnonneg := dotProduct_nonneg_of_nonneg (rowMul_pow_nonneg hs hB.1 k) (add_nonneg hx hB.2)
    apply le_antisymm _ hnonneg
    by_contra hp
    exact hn ⟨k, hk, by omega, lt_of_not_ge hp⟩
  have htail := real_powers_zero_of_window B.matrix s (x + B.offset) (Fintype.card ι) hz
  obtain ⟨N, hN⟩ := hu (s ⬝ᵥ ((eval B)^[Fintype.card ι] x))
  have hg := hN (N + Fintype.card ι) (by omega)
  have hc := observed_iterates_constant_of_zero_tail B s x (Fintype.card ι) hB hs hx htail
    (N + Fintype.card ι) (by omega)
  rw [hc] at hg
  exact lt_irrefl _ hg

omit [Nonempty ι] in
theorem wordMatrix_nonnegative (A B : Mat ι) (hA : EntrywiseLE 0 A) (hB : EntrywiseLE 0 B)
    (w : List Bool) : EntrywiseLE 0 (RealGrowth.wordMatrix A B w) := by
  induction w with
  | nil =>
    intro i j
    simp only [RealGrowth.wordMatrix, Matrix.one_apply]
    split <;> norm_num
  | cons bit w ih =>
    intro i j
    cases bit <;> simp only [RealGrowth.wordMatrix, Bool.false_eq_true, ↓reduceIte, Matrix.mul_apply]
    · exact Finset.sum_nonneg (fun k _ => mul_nonneg (hA i k) (ih k j))
    · exact Finset.sum_nonneg (fun k _ => mul_nonneg (hB i k) (ih k j))

omit [Nonempty ι] in
theorem reversed_real_all_prefix_source_support
    (A B C D E F G : Affine ι) (i₀ : ι)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀)
    (w : List Bool) :
    ∃ k : ℕ, Fintype.card ι ≤ k ∧ k < 2 * Fintype.card ι ∧
      ((D.matrix i₀ ᵥ* RealGrowth.wordMatrix A.matrix B.matrix w) ᵥ* B.matrix ^ k) ⬝ᵥ
        (C.offset + B.offset) > 0 := by
  letI : Nonempty ι := ⟨i₀⟩
  apply unbounded_iterates_have_finite_source_support B _ C.offset hB
    (rowMul_nonneg (fun j => hD.1 i₀ j) (wordMatrix_nonnegative A.matrix B.matrix hA.1 hB.1 w)) hC.2
  exact RealGrowth.real_reversed_word_row_growth A B C D E F G i₀ hA hB hC hD hE hF hG h hstrict w

#print axioms real_powers_zero_of_first
#print axioms real_powers_zero_of_window
#print axioms affine_iterate_sum
#print axioms observed_affine_iterate_sum
#print axioms observed_iterates_constant_of_zero_tail
#print axioms unbounded_iterates_have_finite_source_support
#print axioms wordMatrix_nonnegative
#print axioms reversed_real_all_prefix_source_support

end CollatzResearch.RealSource
