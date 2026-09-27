import CollatzRankGrowth
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

namespace CollatzResearch.FiniteSourceSupport

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

theorem integer_powers_zero_of_first (B : Matrix ι ι ℤ) (s t : ι → ℤ)
    (h : ∀ k : ℕ, k < Fintype.card ι → (s ᵥ* B ^ k) ⬝ᵥ t = 0)
    (k : ℕ) : (s ᵥ* B ^ k) ⬝ᵥ t = 0 := by
  have hne : B.charpoly ≠ 1 := by
    intro hz
    have hd := congrArg Polynomial.natDegree hz
    simp only [Matrix.charpoly_natDegree_eq_dim, Polynomial.natDegree_one] at hd
    have hp := Fintype.card_pos (α := ι)
    omega
  have hdeg : ((Polynomial.X : Polynomial ℤ) ^ k %ₘ B.charpoly).natDegree < Fintype.card ι := by
    simpa only [Matrix.charpoly_natDegree_eq_dim] using
      Polynomial.natDegree_modByMonic_lt ((Polynomial.X : Polynomial ℤ) ^ k) B.charpoly_monic hne
  rw [B.pow_eq_aeval_mod_charpoly k, Polynomial.aeval_eq_sum_range' hdeg B]
  simp only [Matrix.vecMul_sum, sum_dotProduct, vecMul_smul, smul_dotProduct]
  apply Finset.sum_eq_zero
  intro j hj
  rw [h j (Finset.mem_range.mp hj), smul_zero]

theorem natural_powers_zero_of_first (B : Matrix ι ι ℕ) (s t : ι → ℕ)
    (h : ∀ k : ℕ, k < Fintype.card ι → (s ᵥ* B ^ k) ⬝ᵥ t = 0)
    (k : ℕ) : (s ᵥ* B ^ k) ⬝ᵥ t = 0 := by
  let f : ℕ →+* ℤ := Nat.castRingHom ℤ
  have hcast (j : ℕ) : f ((s ᵥ* B ^ j) ⬝ᵥ t) =
      ((f ∘ s) ᵥ* (B.map f) ^ j) ⬝ᵥ (f ∘ t) := by
    have hv : f ∘ (s ᵥ* B ^ j) = (f ∘ s) ᵥ* (B.map f) ^ j := by
      funext i
      change f ((s ᵥ* B ^ j) i) = ((f ∘ s) ᵥ* (B.map f) ^ j) i
      rw [RingHom.map_vecMul, Matrix.map_pow]
    rw [RingHom.map_dotProduct, hv]
  have hi := integer_powers_zero_of_first (B.map f) (f ∘ s) (f ∘ t) (by
    intro j hj
    rw [← hcast j, h j hj, map_zero]) k
  rw [← hcast k] at hi
  change (((s ᵥ* B ^ k) ⬝ᵥ t : ℕ) : ℤ) = 0 at hi
  exact_mod_cast hi

theorem natural_powers_zero_of_window (B : Matrix ι ι ℕ) (s t : ι → ℕ) (d : ℕ)
    (h : ∀ k : ℕ, d ≤ k → k < d + Fintype.card ι → (s ᵥ* B ^ k) ⬝ᵥ t = 0)
    (k : ℕ) (hk : d ≤ k) : (s ᵥ* B ^ k) ⬝ᵥ t = 0 := by
  have hi := natural_powers_zero_of_first B (s ᵥ* B ^ d) t (by
    intro j hj
    rw [vecMul_vecMul, ← pow_add]
    exact h (d + j) (by omega) (by omega)) (k - d)
  rw [vecMul_vecMul, ← pow_add, Nat.add_sub_of_le hk] at hi
  exact hi

omit [Nonempty ι] in
theorem affine_iterate_sum (B : NatAffine ι) (k : ℕ) (x : ι → ℕ) :
    B.eval^[k] x = B.matrix ^ k *ᵥ x + ∑ j ∈ Finset.range k, B.matrix ^ j *ᵥ B.offset := by
  induction k generalizing x with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply, ih]
    simp only [NatAffine.eval, Matrix.mulVec_add, Matrix.mulVec_mulVec,
      pow_succ, Finset.sum_range_succ, add_left_comm, add_comm]

omit [Nonempty ι] in
theorem observed_affine_iterate_sum (B : NatAffine ι) (s x : ι → ℕ) (k : ℕ) :
    s ⬝ᵥ (B.eval^[k] x) = (s ᵥ* B.matrix ^ k) ⬝ᵥ x +
      ∑ j ∈ Finset.range k, (s ᵥ* B.matrix ^ j) ⬝ᵥ B.offset := by
  rw [affine_iterate_sum]
  simp only [dotProduct_add, dotProduct_sum, dotProduct_mulVec]

omit [Nonempty ι] in
theorem observed_iterates_constant_of_zero_tail (B : NatAffine ι) (s x : ι → ℕ) (d : ℕ)
    (h : ∀ k : ℕ, d ≤ k → (s ᵥ* B.matrix ^ k) ⬝ᵥ (x + B.offset) = 0)
    (n : ℕ) (hn : d ≤ n) : s ⬝ᵥ (B.eval^[n] x) = s ⬝ᵥ (B.eval^[d] x) := by
  have hz : ∀ k : ℕ, d ≤ k →
      (s ᵥ* B.matrix ^ k) ⬝ᵥ x = 0 ∧ (s ᵥ* B.matrix ^ k) ⬝ᵥ B.offset = 0 := by
    intro k hk
    have hkz := h k hk
    rw [dotProduct_add] at hkz
    omega
  have hsum : (∑ j ∈ Finset.range d, (s ᵥ* B.matrix ^ j) ⬝ᵥ B.offset) =
      ∑ j ∈ Finset.range n, (s ᵥ* B.matrix ^ j) ⬝ᵥ B.offset := by
    apply Finset.sum_subset (Finset.range_mono hn)
    intro j hj hjd
    exact (hz j (by simpa only [Finset.mem_range, not_lt] using hjd)).2
  rw [observed_affine_iterate_sum, observed_affine_iterate_sum,
    (hz n hn).1, (hz d (by omega)).1, hsum]

theorem unbounded_iterates_have_finite_source_support (B : NatAffine ι) (s x : ι → ℕ)
    (hu : ∀ K : ℕ, ∃ N : ℕ, ∀ n : ℕ, N ≤ n → K < s ⬝ᵥ (B.eval^[n] x)) :
    ∃ k : ℕ, Fintype.card ι ≤ k ∧ k < 2 * Fintype.card ι ∧
      0 < (s ᵥ* B.matrix ^ k) ⬝ᵥ (x + B.offset) := by
  by_contra hn
  have hz : ∀ k : ℕ, Fintype.card ι ≤ k → k < Fintype.card ι + Fintype.card ι →
      (s ᵥ* B.matrix ^ k) ⬝ᵥ (x + B.offset) = 0 := by
    intro k hk hkd
    by_contra hne
    apply hn
    exact ⟨k, hk, by omega, Nat.pos_of_ne_zero hne⟩
  have htail := natural_powers_zero_of_window B.matrix s (x + B.offset) (Fintype.card ι) hz
  obtain ⟨N, hN⟩ := hu (s ⬝ᵥ (B.eval^[Fintype.card ι] x))
  have hg := hN (N + Fintype.card ι) (by omega)
  have hc := observed_iterates_constant_of_zero_tail B s x (Fintype.card ι) htail
    (N + Fintype.card ι) (by omega)
  rw [hc] at hg
  omega

omit [Nonempty ι] in
theorem reversed_all_prefix_source_support (m : ReversedNaturalConditions.Model ι) (i₀ : ι)
    (h : ReversedNaturalConditions.WeakRules m) (hs : ReversedNaturalConditions.StrictOffset m i₀)
    (w : List Bool) :
    ∃ k : ℕ, Fintype.card ι ≤ k ∧ k < 2 * Fintype.card ι ∧
      ((m.d.matrix i₀ ᵥ* RankGrowth.wordMatrix m.a.matrix m.b.matrix w) ᵥ* m.b.matrix ^ k) ⬝ᵥ
        (m.c.offset + m.b.offset) > 0 := by
  letI : Nonempty ι := ⟨i₀⟩
  exact unbounded_iterates_have_finite_source_support m.b
    (m.d.matrix i₀ ᵥ* RankGrowth.wordMatrix m.a.matrix m.b.matrix w) m.c.offset
    (RankGrowth.natural_reversed_word_row_growth m i₀ h hs w)

#print axioms integer_powers_zero_of_first
#print axioms natural_powers_zero_of_first
#print axioms natural_powers_zero_of_window
#print axioms affine_iterate_sum
#print axioms observed_affine_iterate_sum
#print axioms observed_iterates_constant_of_zero_tail
#print axioms unbounded_iterates_have_finite_source_support
#print axioms reversed_all_prefix_source_support

end CollatzResearch.FiniteSourceSupport
