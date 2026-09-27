import CollatzEvenStrictRank

namespace CollatzResearch.ReversedCertificate

variable {α : Type*}

def binaryInterp (a b : α → α) (n : ℕ) (x : α) : α :=
  if n ≤ 1 then x
  else (if n % 2 = 0 then a else b) (binaryInterp a b (n / 2) x)
termination_by n
decreasing_by omega

theorem binaryInterp_one (a b : α → α) (x : α) :
    binaryInterp a b 1 x = x := by
  rw [binaryInterp]
  simp

theorem binaryInterp_even (a b : α → α) {m : ℕ} (hm : 0 < m) (x : α) :
    binaryInterp a b (2 * m) x = a (binaryInterp a b m x) := by
  rw [binaryInterp]
  have hn : ¬ 2 * m ≤ 1 := by omega
  simp [hn]

theorem binaryInterp_odd (a b : α → α) {m : ℕ} (hm : 0 < m) (x : α) :
    binaryInterp a b (2 * m + 1) x = b (binaryInterp a b m x) := by
  rw [binaryInterp]
  have hn : ¬ 2 * m + 1 ≤ 1 := by omega
  have hd : (2 * m + 1) / 2 = m := by omega
  simp [hn, hd]

variable [Preorder α]

structure Data (α : Type*) [Preorder α] where
  a : α → α
  b : α → α
  e : α → α
  f : α → α
  g : α → α
  readout : α → ℕ
  initial : α
  a_monotone : Monotone a
  b_monotone : Monotone b
  readout_monotone : Monotone readout
  ea : ∀ x, a (e x) ≤ e (a x)
  fa : ∀ x, b (e x) ≤ f (a x)
  ga : ∀ x, a (f x) ≤ g (a x)
  eb : ∀ x, b (f x) ≤ e (b x)
  fb : ∀ x, a (g x) ≤ f (b x)
  gb : ∀ x, b (g x) ≤ g (b x)
  ec : b initial ≤ e initial
  fc : a (a initial) ≤ f initial
  gc : b (a initial) ≤ g initial

theorem ternary_conversion_weak (c : Data α) (n : ℕ) :
    0 < n →
      binaryInterp c.a c.b (3 * n) c.initial ≤ c.e (binaryInterp c.a c.b n c.initial) ∧
      binaryInterp c.a c.b (3 * n + 1) c.initial ≤ c.f (binaryInterp c.a c.b n c.initial) ∧
      binaryInterp c.a c.b (3 * n + 2) c.initial ≤ c.g (binaryInterp c.a c.b n c.initial) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn
    by_cases hone : n = 1
    · subst n
      simpa [binaryInterp] using And.intro c.ec (And.intro c.fc c.gc)
    · obtain ⟨m, hm, hform⟩ : ∃ m : ℕ, 0 < m ∧ (n = 2 * m ∨ n = 2 * m + 1) := by
        refine ⟨n / 2, ?_, ?_⟩ <;> omega
      have hmlt : m < n := by rcases hform with h | h <;> omega
      have he := (ih m hmlt hm).1
      have hf := (ih m hmlt hm).2.1
      have hg := (ih m hmlt hm).2.2
      rcases hform with rfl | rfl
      · refine ⟨?_, ?_, ?_⟩
        · have hidx : 3 * (2 * m) = 2 * (3 * m) := by ring
          rw [hidx, binaryInterp_even c.a c.b (by omega), binaryInterp_even c.a c.b hm]
          exact le_trans (c.a_monotone he) (c.ea _)
        · have hidx : 3 * (2 * m) + 1 = 2 * (3 * m) + 1 := by ring
          rw [hidx, binaryInterp_odd c.a c.b (by omega), binaryInterp_even c.a c.b hm]
          exact le_trans (c.b_monotone he) (c.fa _)
        · have hidx : 3 * (2 * m) + 2 = 2 * (3 * m + 1) := by ring
          rw [hidx, binaryInterp_even c.a c.b (by omega), binaryInterp_even c.a c.b hm]
          exact le_trans (c.a_monotone hf) (c.ga _)
      · refine ⟨?_, ?_, ?_⟩
        · have hidx : 3 * (2 * m + 1) = 2 * (3 * m + 1) + 1 := by ring
          rw [hidx, binaryInterp_odd c.a c.b (by omega), binaryInterp_odd c.a c.b hm]
          exact le_trans (c.b_monotone hf) (c.eb _)
        · have hidx : 3 * (2 * m + 1) + 1 = 2 * (3 * m + 2) := by ring
          rw [hidx, binaryInterp_even c.a c.b (by omega), binaryInterp_odd c.a c.b hm]
          exact le_trans (c.a_monotone hg) (c.fb _)
        · have hidx : 3 * (2 * m + 1) + 2 = 2 * (3 * m + 2) + 1 := by ring
          rw [hidx, binaryInterp_odd c.a c.b (by omega), binaryInterp_odd c.a c.b hm]
          exact le_trans (c.b_monotone hg) (c.gb _)

theorem strict_da_implies_collatz (c : Data α)
    (hda : ∀ x, c.readout x < c.readout (c.a x))
    (hdb : ∀ x, c.readout (c.g x) ≤ c.readout (c.b x)) :
    CollatzConjecture := by
  let rank : ℕ → ℕ := fun n => c.readout (binaryInterp c.a c.b n c.initial)
  apply collatz_of_even_strict_rank rank
  · intro m hm
    change c.readout (binaryInterp c.a c.b m c.initial) <
      c.readout (binaryInterp c.a c.b (2 * m) c.initial)
    rw [binaryInterp_even c.a c.b hm]
    exact hda _
  · intro m hm
    change c.readout (binaryInterp c.a c.b (3 * m + 2) c.initial) ≤
      c.readout (binaryInterp c.a c.b (2 * m + 1) c.initial)
    rw [binaryInterp_odd c.a c.b hm]
    exact le_trans (c.readout_monotone (ternary_conversion_weak c m hm).2.2) (hdb _)

theorem strict_db_implies_collatz (c : Data α)
    (hda : ∀ x, c.readout x ≤ c.readout (c.a x))
    (hdb : ∀ x, c.readout (c.g x) < c.readout (c.b x)) :
    CollatzConjecture := by
  let rank : ℕ → ℕ := fun n => c.readout (binaryInterp c.a c.b n c.initial)
  apply collatz_of_rank rank
  · intro m hm
    change c.readout (binaryInterp c.a c.b m c.initial) ≤
      c.readout (binaryInterp c.a c.b (2 * m) c.initial)
    rw [binaryInterp_even c.a c.b hm]
    exact hda _
  · intro m hm
    change c.readout (binaryInterp c.a c.b (3 * m + 2) c.initial) <
      c.readout (binaryInterp c.a c.b (2 * m + 1) c.initial)
    rw [binaryInterp_odd c.a c.b hm]
    exact lt_of_le_of_lt (c.readout_monotone (ternary_conversion_weak c m hm).2.2) (hdb _)

theorem first_eligible_root_implies_collatz (c : Data α)
    (hda : ∀ x, c.readout x ≤ c.readout (c.a x))
    (hdb : ∀ x, c.readout (c.g x) ≤ c.readout (c.b x))
    (hstrict : (∀ x, c.readout x < c.readout (c.a x)) ∨
      (∀ x, c.readout (c.g x) < c.readout (c.b x))) :
    CollatzConjecture := by
  rcases hstrict with hs | hs
  · exact strict_da_implies_collatz c hs hdb
  · exact strict_db_implies_collatz c hda hs

#print axioms binaryInterp_one
#print axioms binaryInterp_even
#print axioms binaryInterp_odd
#print axioms ternary_conversion_weak
#print axioms strict_da_implies_collatz
#print axioms strict_db_implies_collatz
#print axioms first_eligible_root_implies_collatz

end CollatzResearch.ReversedCertificate
