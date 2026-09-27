import CollatzRankAbovePowers
import CollatzMixedSupport

namespace CollatzResearch.RankPositiveOffsets

theorem odd_strict_positive_offsets (rank : ℕ → ℕ)
    (heven : ∀ m : ℕ, 0 < m → rank m ≤ rank (2 * m))
    (hodd : ∀ m : ℕ, 0 < m → rank (3 * m + 2) < rank (2 * m + 1))
    (K c : ℕ) (hc : 0 < c) :
    ∃ L : ℕ, ∀ e t : ℕ, L ≤ e → 0 < t → K ≤ rank (2 ^ e * t + c) := by
  have hmain : ∀ q c : ℕ, rank c = q → 0 < c →
      ∃ L : ℕ, ∀ e t : ℕ, L ≤ e → 0 < t → K ≤ rank (2 ^ e * t + c) := by
    intro q
    induction q using Nat.strong_induction_on with
    | h q ihq =>
      intro c
      induction c using Nat.strong_induction_on with
      | h c ihc =>
        intro hq hc
        by_cases hone : c = 1
        · subst c
          refine ⟨2 * K, ?_⟩
          intro e t he ht
          exact RankAbovePowers.rank_lower_bound rank heven
            (fun m hm => (hodd m hm).le) (Or.inr hodd) K e t he ht
        · by_cases heven_c : c % 2 = 0
          · have hm : 0 < c / 2 := by omega
            have hform : c = 2 * (c / 2) := by omega
            have hle : rank (c / 2) ≤ q := by
              have h := heven (c / 2) hm
              rwa [← hform, hq] at h
            obtain ⟨L, hL⟩ : ∃ L : ℕ, ∀ e t : ℕ, L ≤ e → 0 < t →
                K ≤ rank (2 ^ e * t + c / 2) := by
              rcases lt_or_eq_of_le hle with hlt | heq
              · exact ihq (rank (c / 2)) hlt (c / 2) rfl hm
              · exact ihc (c / 2) (by omega) heq hm
            refine ⟨L + 1, ?_⟩
            intro e t he ht
            have hi := hL (e - 1) t (by omega) ht
            have hp : 0 < 2 ^ (e - 1) * t + c / 2 := by positivity
            have hinput : 2 ^ e * t + c = 2 * (2 ^ (e - 1) * t + c / 2) := by
              conv_lhs => rw [show e = (e - 1) + 1 by omega, pow_succ]
              conv_lhs => rw [hform]
              ring
            rw [hinput]
            exact hi.trans (heven _ hp)
          · have hm : 0 < c / 2 := by omega
            have hform : c = 2 * (c / 2) + 1 := by omega
            have hlt : rank (3 * (c / 2) + 2) < q := by
              have h := hodd (c / 2) hm
              rwa [← hform, hq] at h
            obtain ⟨L, hL⟩ := ihq (rank (3 * (c / 2) + 2)) hlt
              (3 * (c / 2) + 2) rfl (by omega)
            refine ⟨L + 1, ?_⟩
            intro e t he ht
            have hi := hL (e - 1) (3 * t) (by omega) (by omega)
            have hp : 0 < 2 ^ (e - 1) * t + c / 2 := by positivity
            have hinput : 2 ^ e * t + c = 2 * (2 ^ (e - 1) * t + c / 2) + 1 := by
              conv_lhs => rw [show e = (e - 1) + 1 by omega, pow_succ]
              conv_lhs => rw [hform]
              ring
            have hnext : 2 ^ (e - 1) * (3 * t) + (3 * (c / 2) + 2) =
                3 * (2 ^ (e - 1) * t + c / 2) + 2 := by ring
            rw [hnext] at hi
            rw [hinput]
            exact (lt_of_le_of_lt hi (hodd _ hp)).le
  exact hmain (rank c) c rfl hc

theorem even_strict_positive_offsets (rank : ℕ → ℕ)
    (heven : ∀ m : ℕ, 0 < m → rank m < rank (2 * m))
    (hodd : ∀ m : ℕ, 0 < m → rank (3 * m + 2) ≤ rank (2 * m + 1))
    (K c : ℕ) :
    ∃ L : ℕ, ∀ e t : ℕ, L ≤ e → 0 < t → K < rank (2 ^ e * t + c) := by
  refine ⟨2 ^ K + 1, ?_⟩
  intro e t he ht
  have hpow := Nat.lt_two_pow_self (n := e)
  have hmul := Nat.le_mul_of_pos_right (2 ^ e) ht
  have hpositive : 0 < 2 ^ e * t + c := by positivity
  have hbound := RankGrowth.even_strict_rank_bounds_input rank heven hodd _ hpositive
  by_contra hn
  have hle : 2 ^ rank (2 ^ e * t + c) ≤ 2 ^ K :=
    Nat.pow_le_pow_right (by omega) (by omega)
  omega

theorem positive_offset_growth (rank : ℕ → ℕ)
    (heven : ∀ m : ℕ, 0 < m → rank m ≤ rank (2 * m))
    (hodd : ∀ m : ℕ, 0 < m → rank (3 * m + 2) ≤ rank (2 * m + 1))
    (hs : (∀ m : ℕ, 0 < m → rank m < rank (2 * m)) ∨
      (∀ m : ℕ, 0 < m → rank (3 * m + 2) < rank (2 * m + 1)))
    (K c : ℕ) (hc : 0 < c) :
    ∃ L : ℕ, ∀ e t : ℕ, L ≤ e → 0 < t → K < rank (2 ^ e * t + c) := by
  rcases hs with hs | hs
  · exact even_strict_positive_offsets rank hs hodd K c
  · exact odd_strict_positive_offsets rank heven hs (K + 1) c hc

theorem reversed_mixed_b_a_growth {α : Type*} [Preorder α]
    (c : ReversedCertificate.Data α)
    (hmono : ∀ k, Monotone (MixedSupport.digitMap c k))
    (hda : ∀ x, c.readout x ≤ c.readout (c.a x))
    (hdb : ∀ x, c.readout (c.g x) ≤ c.readout (c.b x))
    (hs : (∀ x, c.readout x < c.readout (c.a x)) ∨
      (∀ x, c.readout (c.g x) < c.readout (c.b x)))
    (w : List MixedSupport.Digit) (K : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → K < c.readout (MixedSupport.eval (MixedSupport.digitMap c) w (c.b (c.a^[n] c.initial))) := by
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
  have hpositive : 0 < MixedSupport.scale w + MixedSupport.label w 0 := by
    have hp := MixedSupport.scale_pos w
    omega
  obtain ⟨L, hL⟩ := positive_offset_growth rank heven hodd hstrict K
    (MixedSupport.scale w + MixedSupport.label w 0) hpositive
  refine ⟨L, ?_⟩
  intro n hn
  have hi := hL (n + 1) (MixedSupport.scale w) (by omega) (MixedSupport.scale_pos w)
  have hlabel : MixedSupport.label w (2 ^ (n + 1) + 1) =
      2 ^ (n + 1) * MixedSupport.scale w + (MixedSupport.scale w + MixedSupport.label w 0) := by
    rw [MixedSupport.label_affine]
    ring
  rw [← hlabel] at hi
  have hm := c.readout_monotone (MixedSupport.interp_label_le c hmono w
    (2 ^ (n + 1) + 1) (by positivity))
  rw [pow_succ, Nat.mul_comm,
    ReversedCertificate.binaryInterp_odd c.a c.b (by positivity : 0 < 2 ^ n),
    RankAbovePowers.binaryInterp_power] at hm
  dsimp [rank] at hi
  rw [pow_succ, Nat.mul_comm] at hi
  exact lt_of_lt_of_le hi hm

#print axioms reversed_mixed_b_a_growth
#print axioms odd_strict_positive_offsets
#print axioms even_strict_positive_offsets
#print axioms positive_offset_growth

end CollatzResearch.RankPositiveOffsets
