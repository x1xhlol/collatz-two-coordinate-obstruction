import CollatzCore

namespace CollatzResearch

variable {α : Type*}

def binaryInterp (a b : α → α) (n : ℕ) (x : α) : α :=
  if n ≤ 1 then x
  else binaryInterp a b (n / 2) ((if n % 2 = 0 then a else b) x)
termination_by n
decreasing_by omega

theorem binaryInterp_one (a b : α → α) (x : α) :
    binaryInterp a b 1 x = x := by
  rw [binaryInterp]
  simp

theorem binaryInterp_even (a b : α → α) {m : ℕ} (hm : 0 < m) (x : α) :
    binaryInterp a b (2 * m) x = binaryInterp a b m (a x) := by
  rw [binaryInterp]
  have hn : ¬ 2 * m ≤ 1 := by omega
  simp [hn]

theorem binaryInterp_odd (a b : α → α) {m : ℕ} (hm : 0 < m) (x : α) :
    binaryInterp a b (2 * m + 1) x = binaryInterp a b m (b x) := by
  rw [binaryInterp]
  have hn : ¬ 2 * m + 1 ≤ 1 := by omega
  have hd : (2 * m + 1) / 2 = m := by omega
  simp [hn, hd]

variable [Preorder α]

theorem binaryInterp_monotone {a b : α → α}
    (ha : Monotone a) (hb : Monotone b) (n : ℕ) :
    Monotone (binaryInterp a b n) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro x y hxy
    conv_lhs => rw [binaryInterp]
    conv_rhs => rw [binaryInterp]
    by_cases hn : n ≤ 1
    · simp only [if_pos hn]
      exact hxy
    · simp only [if_neg hn]
      have hm : n / 2 < n := by omega
      by_cases he : n % 2 = 0
      · simp only [if_pos he]
        exact ih (n / 2) hm (ha hxy)
      · simp only [if_neg he]
        exact ih (n / 2) hm (hb hxy)

structure RootStrictCertificate (α : Type*) [Preorder α] where
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
  ad : initial ≤ a initial
  bd : g initial ≤ b initial
  ae : ∀ x, e (a x) ≤ a (e x)
  af : ∀ x, e (b x) ≤ a (f x)
  ag : ∀ x, f (a x) ≤ a (g x)
  be : ∀ x, f (b x) ≤ b (e x)
  bf : ∀ x, g (a x) ≤ b (f x)
  bg : ∀ x, g (b x) ≤ b (g x)
  ce : ∀ x, readout (b x) < readout (e x)
  cf : ∀ x, readout (a (a x)) < readout (f x)
  cg : ∀ x, readout (a (b x)) < readout (g x)

theorem readout_binaryInterp_monotone (c : RootStrictCertificate α) (n : ℕ) :
    Monotone (fun x => c.readout (binaryInterp c.a c.b n x)) :=
  c.readout_monotone.comp (binaryInterp_monotone c.a_monotone c.b_monotone n)

theorem ternary_conversion_strict (c : RootStrictCertificate α) (n : ℕ) :
    0 < n → ∀ x,
      c.readout (binaryInterp c.a c.b (3 * n) x) <
        c.readout (binaryInterp c.a c.b n (c.e x)) ∧
      c.readout (binaryInterp c.a c.b (3 * n + 1) x) <
        c.readout (binaryInterp c.a c.b n (c.f x)) ∧
      c.readout (binaryInterp c.a c.b (3 * n + 2) x) <
        c.readout (binaryInterp c.a c.b n (c.g x)) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn x
    by_cases hone : n = 1
    · subst n
      simpa [binaryInterp] using And.intro (c.ce x) (And.intro (c.cf x) (c.cg x))
    · obtain ⟨m, hm, hform⟩ : ∃ m : ℕ, 0 < m ∧ (n = 2 * m ∨ n = 2 * m + 1) := by
        refine ⟨n / 2, ?_, ?_⟩ <;> omega
      have hmlt : m < n := by rcases hform with h | h <;> omega
      have he := fun y => (ih m hmlt hm y).1
      have hf := fun y => (ih m hmlt hm y).2.1
      have hg := fun y => (ih m hmlt hm y).2.2
      have hmono := readout_binaryInterp_monotone c m
      rcases hform with rfl | rfl
      · refine ⟨?_, ?_, ?_⟩
        · calc
            c.readout (binaryInterp c.a c.b (3 * (2 * m)) x) =
                c.readout (binaryInterp c.a c.b (3 * m) (c.a x)) := by
                  have hidx : 3 * (2 * m) = 2 * (3 * m) := by ring
                  rw [hidx, binaryInterp_even c.a c.b (by omega)]
            _ < c.readout (binaryInterp c.a c.b m (c.e (c.a x))) := he (c.a x)
            _ ≤ c.readout (binaryInterp c.a c.b m (c.a (c.e x))) := hmono (c.ae x)
            _ = c.readout (binaryInterp c.a c.b (2 * m) (c.e x)) := by
                  rw [binaryInterp_even c.a c.b hm]
        · calc
            c.readout (binaryInterp c.a c.b (3 * (2 * m) + 1) x) =
                c.readout (binaryInterp c.a c.b (3 * m) (c.b x)) := by
                  have hidx : 3 * (2 * m) + 1 = 2 * (3 * m) + 1 := by ring
                  rw [hidx, binaryInterp_odd c.a c.b (by omega)]
            _ < c.readout (binaryInterp c.a c.b m (c.e (c.b x))) := he (c.b x)
            _ ≤ c.readout (binaryInterp c.a c.b m (c.a (c.f x))) := hmono (c.af x)
            _ = c.readout (binaryInterp c.a c.b (2 * m) (c.f x)) := by
                  rw [binaryInterp_even c.a c.b hm]
        · calc
            c.readout (binaryInterp c.a c.b (3 * (2 * m) + 2) x) =
                c.readout (binaryInterp c.a c.b (3 * m + 1) (c.a x)) := by
                  have hidx : 3 * (2 * m) + 2 = 2 * (3 * m + 1) := by ring
                  rw [hidx, binaryInterp_even c.a c.b (by omega)]
            _ < c.readout (binaryInterp c.a c.b m (c.f (c.a x))) := hf (c.a x)
            _ ≤ c.readout (binaryInterp c.a c.b m (c.a (c.g x))) := hmono (c.ag x)
            _ = c.readout (binaryInterp c.a c.b (2 * m) (c.g x)) := by
                  rw [binaryInterp_even c.a c.b hm]
      · refine ⟨?_, ?_, ?_⟩
        · calc
            c.readout (binaryInterp c.a c.b (3 * (2 * m + 1)) x) =
                c.readout (binaryInterp c.a c.b (3 * m + 1) (c.b x)) := by
                  have hidx : 3 * (2 * m + 1) = 2 * (3 * m + 1) + 1 := by ring
                  rw [hidx, binaryInterp_odd c.a c.b (by omega)]
            _ < c.readout (binaryInterp c.a c.b m (c.f (c.b x))) := hf (c.b x)
            _ ≤ c.readout (binaryInterp c.a c.b m (c.b (c.e x))) := hmono (c.be x)
            _ = c.readout (binaryInterp c.a c.b (2 * m + 1) (c.e x)) := by
                  rw [binaryInterp_odd c.a c.b hm]
        · calc
            c.readout (binaryInterp c.a c.b (3 * (2 * m + 1) + 1) x) =
                c.readout (binaryInterp c.a c.b (3 * m + 2) (c.a x)) := by
                  have hidx : 3 * (2 * m + 1) + 1 = 2 * (3 * m + 2) := by ring
                  rw [hidx, binaryInterp_even c.a c.b (by omega)]
            _ < c.readout (binaryInterp c.a c.b m (c.g (c.a x))) := hg (c.a x)
            _ ≤ c.readout (binaryInterp c.a c.b m (c.b (c.f x))) := hmono (c.bf x)
            _ = c.readout (binaryInterp c.a c.b (2 * m + 1) (c.f x)) := by
                  rw [binaryInterp_odd c.a c.b hm]
        · calc
            c.readout (binaryInterp c.a c.b (3 * (2 * m + 1) + 2) x) =
                c.readout (binaryInterp c.a c.b (3 * m + 2) (c.b x)) := by
                  have hidx : 3 * (2 * m + 1) + 2 = 2 * (3 * m + 2) + 1 := by ring
                  rw [hidx, binaryInterp_odd c.a c.b (by omega)]
            _ < c.readout (binaryInterp c.a c.b m (c.g (c.b x))) := hg (c.b x)
            _ ≤ c.readout (binaryInterp c.a c.b m (c.b (c.g x))) := hmono (c.bg x)
            _ = c.readout (binaryInterp c.a c.b (2 * m + 1) (c.g x)) := by
                  rw [binaryInterp_odd c.a c.b hm]

theorem root_strict_certificate_implies_collatz (c : RootStrictCertificate α) :
    CollatzConjecture := by
  let rank : ℕ → ℕ := fun n => c.readout (binaryInterp c.a c.b n c.initial)
  apply collatz_of_rank rank
  · intro m hm
    change c.readout (binaryInterp c.a c.b m c.initial) ≤
      c.readout (binaryInterp c.a c.b (2 * m) c.initial)
    rw [binaryInterp_even c.a c.b hm]
    exact readout_binaryInterp_monotone c m c.ad
  · intro m hm
    change c.readout (binaryInterp c.a c.b (3 * m + 2) c.initial) <
      c.readout (binaryInterp c.a c.b (2 * m + 1) c.initial)
    rw [binaryInterp_odd c.a c.b hm]
    exact lt_of_lt_of_le (ternary_conversion_strict c m hm c.initial).2.2
      (readout_binaryInterp_monotone c m c.bd)

#print axioms binaryInterp_one
#print axioms binaryInterp_even
#print axioms binaryInterp_odd
#print axioms binaryInterp_monotone
#print axioms readout_binaryInterp_monotone
#print axioms ternary_conversion_strict
#print axioms root_strict_certificate_implies_collatz

end CollatzResearch
