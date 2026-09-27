import CollatzRankPositiveOffsets

namespace CollatzResearch.PositiveWord

theorem label_append (v w : List MixedSupport.Digit) (n : ℕ) :
    MixedSupport.label (v ++ w) n = MixedSupport.label v (MixedSupport.label w n) := by
  induction v with
  | nil => rfl
  | cons k v ih => simp only [List.cons_append, MixedSupport.label, ih]

theorem positive_label_append (w : List MixedSupport.Digit)
    (hw : 0 < MixedSupport.label w 0) (k : MixedSupport.Digit) :
    0 < MixedSupport.label (w ++ [k]) 0 := by
  rw [label_append, MixedSupport.label_affine]
  omega

theorem positive_digit_append (w : List MixedSupport.Digit) (k : MixedSupport.Digit)
    (hk : 0 < MixedSupport.residue k) :
    0 < MixedSupport.label (w ++ [k]) 0 := by
  rw [label_append]
  apply MixedSupport.label_pos
  simpa only [MixedSupport.label, Nat.mul_zero, Nat.zero_add] using hk

theorem reversed_positive_word_a_growth {α : Type*} [Preorder α]
    (c : ReversedCertificate.Data α)
    (hmono : ∀ k, Monotone (MixedSupport.digitMap c k))
    (hda : ∀ x, c.readout x ≤ c.readout (c.a x))
    (hdb : ∀ x, c.readout (c.g x) ≤ c.readout (c.b x))
    (hs : (∀ x, c.readout x < c.readout (c.a x)) ∨
      (∀ x, c.readout (c.g x) < c.readout (c.b x)))
    (w : List MixedSupport.Digit) (hw : 0 < MixedSupport.label w 0) (K : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → K < c.readout (MixedSupport.eval (MixedSupport.digitMap c) w (c.a^[n] c.initial)) := by
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
  obtain ⟨L, hL⟩ := RankPositiveOffsets.positive_offset_growth rank heven hodd hstrict K
    (MixedSupport.label w 0) hw
  refine ⟨L, ?_⟩
  intro n hn
  have hi := hL n (MixedSupport.scale w) hn (MixedSupport.scale_pos w)
  have hlabel : MixedSupport.label w (2 ^ n) =
      2 ^ n * MixedSupport.scale w + MixedSupport.label w 0 := by
    rw [MixedSupport.label_affine]
    ring
  rw [← hlabel] at hi
  have hm := c.readout_monotone (MixedSupport.interp_label_le c hmono w
    (2 ^ n) (by positivity))
  rw [RankAbovePowers.binaryInterp_power] at hm
  exact lt_of_lt_of_le hi hm

#print axioms label_append
#print axioms positive_label_append
#print axioms positive_digit_append
#print axioms reversed_positive_word_a_growth

end CollatzResearch.PositiveWord
