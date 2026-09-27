import CollatzReversedNecessaryConditions
import Mathlib.Algebra.Ring.GeomSum

namespace CollatzResearch.OddBlocks

theorem rank_gap_over_odd_block (rank : ℕ → ℕ) (δ : ℕ)
    (hodd : ∀ m : ℕ, 0 < m → rank (3 * m + 2) + δ ≤ rank (2 * m + 1))
    (k t : ℕ) (ht : 2 ≤ t) :
    rank (3 ^ k * t - 1) + k * δ ≤ rank (2 ^ k * t - 1) := by
  induction k generalizing t with
  | zero => simp
  | succ k ih =>
    let p := 2 ^ k * t
    have hp : 2 ≤ p := by
      have hpow : 0 < 2 ^ k := by positivity
      dsimp [p]
      nlinarith
    have hs := hodd (p - 1) (by omega)
    have hi := ih (3 * t) (by omega)
    have heq1 : 3 * (p - 1) + 2 = 2 ^ k * (3 * t) - 1 := by
      have hm : 2 ^ k * (3 * t) = 3 * p := by dsimp [p]; ring
      rw [hm]
      omega
    have heq2 : 2 * (p - 1) + 1 = 2 ^ (k + 1) * t - 1 := by
      have hm : 2 ^ (k + 1) * t = 2 * p := by dsimp [p]; rw [pow_succ]; ring
      rw [hm]
      omega
    have heq3 : 3 ^ k * (3 * t) = 3 ^ (k + 1) * t := by rw [pow_succ]; ring
    rw [heq1, heq2] at hs
    rw [heq3] at hi
    rw [Nat.succ_mul]
    omega

theorem triple_divisor_of_cube {d x : ℤ} (hd : d ∣ x + 1) (hthree : 3 ∣ x + 1) :
    3 * d ∣ x ^ 3 + 1 := by
  obtain ⟨u, hu⟩ := hd
  obtain ⟨v, hv⟩ := hthree
  refine ⟨u * (3 * v ^ 2 - 3 * v + 1), ?_⟩
  calc
    x ^ 3 + 1 = (x + 1) * ((x + 1) ^ 2 - 3 * (x + 1) + 3) := by ring
    _ = (d * u) * (3 * (3 * v ^ 2 - 3 * v + 1)) := by
      conv_lhs => lhs; rw [hu]
      rw [hv]
      ring
    _ = 3 * d * (u * (3 * v ^ 2 - 3 * v + 1)) := by ring

theorem three_pow_dvd_two_pow_three_pow_add_one (k : ℕ) :
    3 ^ (k + 1) ∣ 2 ^ (3 ^ k) + 1 := by
  have hint : ∀ k : ℕ, (3 : ℤ) ^ (k + 1) ∣ (2 : ℤ) ^ (3 ^ k) + 1 := by
    intro k
    induction k with
    | zero => norm_num
    | succ k ih =>
      have hthree : (3 : ℤ) ∣ (2 : ℤ) ^ (3 ^ k) + 1 := by
        apply dvd_trans _ ih
        rw [pow_succ]
        exact dvd_mul_left 3 _
      have hc := triple_divisor_of_cube ih hthree
      have hd : (3 : ℤ) ^ (k + 1 + 1) = 3 * 3 ^ (k + 1) := by rw [pow_succ]; ring
      have he : (2 : ℤ) ^ (3 ^ (k + 1)) = ((2 : ℤ) ^ (3 ^ k)) ^ 3 := by
        rw [pow_succ, pow_mul]
      rw [hd, he]
      exact hc
  have h := hint k
  apply Int.natCast_dvd_natCast.mp
  simpa only [Nat.cast_pow, Nat.cast_add, Nat.cast_ofNat] using h

theorem three_pow_dvd_odd_multiple_exponent (k q : ℕ) :
    3 ^ k ∣ 2 ^ (3 ^ k * (2 * q + 1)) + 1 := by
  have hbase : 3 ^ k ∣ 2 ^ (3 ^ k) + 1 := by
    apply dvd_trans _ (three_pow_dvd_two_pow_three_pow_add_one k)
    rw [pow_succ]
    exact dvd_mul_right _ 3
  have hodd : Odd (2 * q + 1) := ⟨q, by omega⟩
  have hpower : 2 ^ (3 ^ k) + 1 ∣ (2 ^ (3 ^ k)) ^ (2 * q + 1) + 1 := by
    simpa only [one_pow] using
      (hodd.nat_add_dvd_pow_add_pow (x := 2 ^ (3 ^ k)) (y := 1))
  simpa only [pow_mul] using dvd_trans hbase hpower

theorem even_strict_rank_unbounded_on_binary_suffix (rank : ℕ → ℕ)
    (heven : ∀ m : ℕ, 0 < m → rank m < rank (2 * m))
    (hodd : ∀ m : ℕ, 0 < m → rank (3 * m + 2) ≤ rank (2 * m + 1))
    (k K : ℕ) : ∃ t : ℕ, 2 ≤ t ∧ K < rank (2 ^ k * t - 1) := by
  let e := 3 ^ k * (2 * K + 3)
  have hp : 0 < 3 ^ k := by positivity
  have he : K < e ∧ 2 * 3 ^ k ≤ e := by dsimp [e]; constructor <;> nlinarith
  have hdiv : 3 ^ k ∣ 2 ^ e + 1 := by
    simpa only [e, show 2 * (K + 1) + 1 = 2 * K + 3 by omega] using
      three_pow_dvd_odd_multiple_exponent k (K + 1)
  obtain ⟨t, htprod⟩ := hdiv
  have hexp : e < 2 ^ e := Nat.lt_two_pow_self
  have ht : 2 ≤ t := by
    by_contra hn
    have hsmall : t ≤ 1 := by omega
    have hmul := Nat.mul_le_mul_left (3 ^ k) hsmall
    omega
  have hb := rank_gap_over_odd_block rank 0 (by simpa using hodd) k t ht
  have hfinal : 3 ^ k * t - 1 = 2 ^ e := by omega
  rw [hfinal] at hb
  have hlower := even_strict_rank_power_two_lower_bound rank heven e
  refine ⟨t, ht, ?_⟩
  omega

theorem odd_strict_rank_unbounded_on_binary_suffix (rank : ℕ → ℕ)
    (hodd : ∀ m : ℕ, 0 < m → rank (3 * m + 2) < rank (2 * m + 1))
    (k K : ℕ) : ∃ t : ℕ, 2 ≤ t ∧ K < rank (2 ^ k * t - 1) := by
  let t := 2 ^ (K + 1) * 2
  have ht : 2 ≤ t := by
    have hpos : 0 < 2 ^ (K + 1) := by positivity
    dsimp [t]
    omega
  have hg : ∀ m : ℕ, 0 < m → rank (3 * m + 2) + 1 ≤ rank (2 * m + 1) := by
    intro m hm
    exact hodd m hm
  have hb := rank_gap_over_odd_block rank 1 hg (k + (K + 1)) 2 (by omega)
  have hform : 2 ^ (k + (K + 1)) * 2 = 2 ^ k * t := by
    dsimp [t]
    rw [pow_add]
    ring
  rw [hform] at hb
  refine ⟨t, ht, ?_⟩
  omega

theorem reversed_binary_suffix {α : Type*} (a b : α → α) (k t : ℕ) (ht : 2 ≤ t) (x : α) :
    ReversedCertificate.binaryInterp a b (2 ^ k * t - 1) x =
      b^[k] (ReversedCertificate.binaryInterp a b (t - 1) x) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hp : 2 ≤ 2 ^ k * t := by
      have hpos : 0 < 2 ^ k := by positivity
      nlinarith
    have hform : 2 ^ (k + 1) * t - 1 = 2 * (2 ^ k * t - 1) + 1 := by
      rw [pow_succ]
      have hm : 2 ^ k * 2 * t = 2 * (2 ^ k * t) := by ring
      rw [hm]
      omega
    rw [hform, ReversedCertificate.binaryInterp_odd a b (by omega), ih,
      Function.iterate_succ_apply']

theorem reversed_strict_readout_b_iterates_unbounded {α : Type*} [Preorder α]
    (c : ReversedCertificate.Data α)
    (hdb : ∀ x, c.readout (c.g x) ≤ c.readout (c.b x))
    (hs : (∀ x, c.readout x < c.readout (c.a x)) ∨
      (∀ x, c.readout (c.g x) < c.readout (c.b x))) (k K : ℕ) :
    ∃ x : α, K < c.readout (c.b^[k] x) := by
  let rank : ℕ → ℕ := fun n => c.readout (ReversedCertificate.binaryInterp c.a c.b n c.initial)
  have hlarge : ∃ t : ℕ, 2 ≤ t ∧ K < rank (2 ^ k * t - 1) := by
    rcases hs with ha | hb
    · apply even_strict_rank_unbounded_on_binary_suffix rank _ _ k K
      · intro m hm
        dsimp [rank]
        rw [ReversedCertificate.binaryInterp_even c.a c.b hm]
        exact ha _
      · intro m hm
        dsimp [rank]
        rw [ReversedCertificate.binaryInterp_odd c.a c.b hm]
        exact le_trans (c.readout_monotone
          (ReversedCertificate.ternary_conversion_weak c m hm).2.2) (hdb _)
    · apply odd_strict_rank_unbounded_on_binary_suffix rank _ k K
      intro m hm
      dsimp [rank]
      rw [ReversedCertificate.binaryInterp_odd c.a c.b hm]
      exact lt_of_le_of_lt (c.readout_monotone
        (ReversedCertificate.ternary_conversion_weak c m hm).2.2) (hb _)
  obtain ⟨t, ht, hlarge⟩ := hlarge
  refine ⟨ReversedCertificate.binaryInterp c.a c.b (t - 1) c.initial, ?_⟩
  simpa only [rank, reversed_binary_suffix c.a c.b k t ht] using hlarge

open Matrix ReversedNaturalConditions

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem affine_iterate (F : NatAffine ι) (k : ℕ) (x : ι → ℕ) :
    F.eval^[k] x = F.matrix ^ k *ᵥ x + F.eval^[k] 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]
    simp only [NatAffine.eval, Matrix.mulVec_add, pow_succ', Matrix.mulVec_mulVec, add_assoc]

theorem observed_affine_iterate (D B : NatAffine ι) (i₀ : ι) (k : ℕ) (x : ι → ℕ) :
    D.eval (B.eval^[k] x) i₀ =
      (D.matrix i₀ ᵥ* B.matrix ^ k) ⬝ᵥ x + D.eval (B.eval^[k] 0) i₀ := by
  change D.matrix i₀ ⬝ᵥ (B.eval^[k] x) + D.offset i₀ =
    (D.matrix i₀ ᵥ* B.matrix ^ k) ⬝ᵥ x + (D.matrix i₀ ⬝ᵥ (B.eval^[k] 0) + D.offset i₀)
  rw [affine_iterate B k x, dotProduct_add, dotProduct_mulVec]
  omega

theorem reversed_db_power_row_nonzero (m : Model ι) (i₀ : ι) (h : WeakRules m)
    (hs : StrictOffset m i₀) (k : ℕ) :
    ∃ j, 0 < (m.d.matrix i₀ ᵥ* m.b.matrix ^ k) j := by
  classical
  by_contra hn
  have hz : ∀ j, (m.d.matrix i₀ ᵥ* m.b.matrix ^ k) j = 0 := by
    intro j
    by_contra hne
    exact hn ⟨j, Nat.pos_of_ne_zero hne⟩
  let c := ofModel m h i₀
  have hdb : ∀ x, c.readout (c.g x) ≤ c.readout (c.b x) := by
    intro x
    simpa only [NatAffine.eval_comp] using NatAffine.eval_weak h.2.1 x i₀
  have hstrict : (∀ x, c.readout x < c.readout (c.a x)) ∨
      (∀ x, c.readout (c.g x) < c.readout (c.b x)) := by
    rcases hs with ha | hb
    · left
      intro x
      simpa only [NatAffine.eval_comp] using NatAffine.eval_strict_at h.1 i₀ ha x
    · right
      intro x
      simpa only [NatAffine.eval_comp] using NatAffine.eval_strict_at h.2.1 i₀ hb x
  obtain ⟨x, hx⟩ := reversed_strict_readout_b_iterates_unbounded c hdb hstrict k
    (m.d.eval (m.b.eval^[k] 0) i₀)
  have heq : c.readout (c.b^[k] x) = m.d.eval (m.b.eval^[k] 0) i₀ := by
    change m.d.eval (m.b.eval^[k] x) i₀ = m.d.eval (m.b.eval^[k] 0) i₀
    rw [observed_affine_iterate]
    simp [dotProduct, hz]
  rw [heq] at hx
  omega

theorem reversed_b_power_ne_zero (m : Model ι) (i₀ : ι) (h : WeakRules m)
    (hs : StrictOffset m i₀) (k : ℕ) : m.b.matrix ^ k ≠ 0 := by
  intro hz
  obtain ⟨j, hj⟩ := reversed_db_power_row_nonzero m i₀ h hs k
  simp [hz] at hj

#print axioms rank_gap_over_odd_block
#print axioms triple_divisor_of_cube
#print axioms three_pow_dvd_two_pow_three_pow_add_one
#print axioms three_pow_dvd_odd_multiple_exponent
#print axioms even_strict_rank_unbounded_on_binary_suffix
#print axioms odd_strict_rank_unbounded_on_binary_suffix
#print axioms reversed_binary_suffix
#print axioms reversed_strict_readout_b_iterates_unbounded
#print axioms affine_iterate
#print axioms observed_affine_iterate
#print axioms reversed_db_power_row_nonzero
#print axioms reversed_b_power_ne_zero

end CollatzResearch.OddBlocks
