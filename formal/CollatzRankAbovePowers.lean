import CollatzRankGrowth

namespace CollatzResearch.RankAbovePowers

theorem rank_step (rank : ℕ → ℕ)
    (heven : ∀ m : ℕ, 0 < m → rank m ≤ rank (2 * m))
    (hodd : ∀ m : ℕ, 0 < m → rank (3 * m + 2) ≤ rank (2 * m + 1))
    (hs : (∀ m : ℕ, 0 < m → rank m < rank (2 * m)) ∨
      (∀ m : ℕ, 0 < m → rank (3 * m + 2) < rank (2 * m + 1)))
    (e t : ℕ) (ht : 0 < t) :
    rank (2 ^ e * (3 * t) + 1) < rank (2 ^ (e + 2) * t + 1) := by
  have hm : 0 < 2 ^ (e + 1) * t := by positivity
  have hp : 0 < 2 ^ e * (3 * t) + 1 := by omega
  have hleft : 3 * (2 ^ (e + 1) * t) + 2 = 2 * (2 ^ e * (3 * t) + 1) := by
    rw [pow_succ]
    ring
  have hright : 2 * (2 ^ (e + 1) * t) + 1 = 2 ^ (e + 2) * t + 1 := by
    rw [show e + 2 = (e + 1) + 1 by omega, pow_succ]
    ring
  rcases hs with hs | hs
  · have ho := hodd (2 ^ (e + 1) * t) hm
    rw [hleft, hright] at ho
    exact lt_of_lt_of_le (hs _ hp) ho
  · have ho := hs (2 ^ (e + 1) * t) hm
    rw [hleft, hright] at ho
    exact lt_of_le_of_lt (heven _ hp) ho

theorem rank_lower_bound (rank : ℕ → ℕ)
    (heven : ∀ m : ℕ, 0 < m → rank m ≤ rank (2 * m))
    (hodd : ∀ m : ℕ, 0 < m → rank (3 * m + 2) ≤ rank (2 * m + 1))
    (hs : (∀ m : ℕ, 0 < m → rank m < rank (2 * m)) ∨
      (∀ m : ℕ, 0 < m → rank (3 * m + 2) < rank (2 * m + 1)))
    (K e t : ℕ) (he : 2 * K ≤ e) (ht : 0 < t) :
    K ≤ rank (2 ^ e * t + 1) := by
  induction K generalizing e t with
  | zero => omega
  | succ K ih =>
    have hi := ih (e - 2) (3 * t) (by omega) (by omega)
    have hstep := rank_step rank heven hodd hs (e - 2) t ht
    rw [show e - 2 + 2 = e by omega] at hstep
    omega

theorem binaryInterp_power {α : Type*} (a b : α → α) (n : ℕ) (x : α) :
    ReversedCertificate.binaryInterp a b (2 ^ n) x = a^[n] x := by
  induction n with
  | zero => simp [ReversedCertificate.binaryInterp_one]
  | succ n ih =>
    have hp : 0 < 2 ^ n := by positivity
    rw [pow_succ, Nat.mul_comm, ReversedCertificate.binaryInterp_even a b hp, ih,
      Function.iterate_succ_apply']

theorem reversed_b_a_growth {α : Type*} [Preorder α]
    (c : ReversedCertificate.Data α)
    (hda : ∀ x, c.readout x ≤ c.readout (c.a x))
    (hdb : ∀ x, c.readout (c.g x) ≤ c.readout (c.b x))
    (hs : (∀ x, c.readout x < c.readout (c.a x)) ∨
      (∀ x, c.readout (c.g x) < c.readout (c.b x)))
    (K : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → K < c.readout (c.b (c.a^[n] c.initial)) := by
  let rank : ℕ → ℕ := fun n => c.readout (ReversedCertificate.binaryInterp c.a c.b n c.initial)
  have heven : ∀ m : ℕ, 0 < m → rank m ≤ rank (2 * m) := by
    intro m hm
    dsimp [rank]
    rw [ReversedCertificate.binaryInterp_even c.a c.b hm]
    exact hda _
  have hodd : ∀ m : ℕ, 0 < m → rank (3 * m + 2) ≤ rank (2 * m + 1) := by
    intro m hm
    dsimp [rank]
    rw [ReversedCertificate.binaryInterp_odd c.a c.b hm]
    exact le_trans (c.readout_monotone
      (ReversedCertificate.ternary_conversion_weak c m hm).2.2) (hdb _)
  have hstrict : (∀ m : ℕ, 0 < m → rank m < rank (2 * m)) ∨
      (∀ m : ℕ, 0 < m → rank (3 * m + 2) < rank (2 * m + 1)) := by
    rcases hs with ha | hb
    · left
      intro m hm
      dsimp [rank]
      rw [ReversedCertificate.binaryInterp_even c.a c.b hm]
      exact ha _
    · right
      intro m hm
      dsimp [rank]
      rw [ReversedCertificate.binaryInterp_odd c.a c.b hm]
      exact lt_of_le_of_lt (c.readout_monotone
        (ReversedCertificate.ternary_conversion_weak c m hm).2.2) (hb _)
  refine ⟨2 * (K + 1), ?_⟩
  intro n hn
  have hg := rank_lower_bound rank heven hodd hstrict (K + 1) (n + 1) 1 (by omega) (by omega)
  dsimp [rank] at hg
  rw [Nat.mul_one, pow_succ, Nat.mul_comm,
    ReversedCertificate.binaryInterp_odd c.a c.b (by positivity : 0 < 2 ^ n),
    binaryInterp_power] at hg
  exact hg

#print axioms rank_step
#print axioms rank_lower_bound
#print axioms binaryInterp_power
#print axioms reversed_b_a_growth

end CollatzResearch.RankAbovePowers
