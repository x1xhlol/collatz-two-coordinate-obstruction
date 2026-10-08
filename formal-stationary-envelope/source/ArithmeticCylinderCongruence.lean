import ArithmeticCylinderResidues

set_option autoImplicit false

namespace CollatzCylinderPacking.Arithmetic

/-- The numerator of the truncated affine series after multiplication by
2 to the sum of all exponents. -/
def affineNumerator : List ℕ → ℕ
  | [] => 0
  | _a :: as => 2 ^ as.sum + 3 * affineNumerator as

def Compatible (N : ℕ) (as : List ℕ) : Prop :=
  Nat.ModEq (3 ^ as.length) (2 ^ as.sum * N) (affineNumerator as)

theorem validBlock_iff_congruence {a N : ℕ} (hN : 0 < N) :
    ValidBlock a N ↔ 0 < a ∧ Nat.ModEq 3 (2 ^ a * N) 1 := by
  have hp : 1 ≤ 2 ^ a * N := Nat.succ_le_iff.mpr (by positivity)
  constructor
  · rintro ⟨ha, hd⟩
    refine ⟨ha, ?_⟩
    have hzero : Nat.ModEq 3 (2 ^ a * N - 1) 0 := Nat.modEq_zero_iff_dvd.mpr hd
    have h := hzero.add_right 1
    simpa only [Nat.sub_add_cancel hp, zero_add] using h
  · rintro ⟨ha, he⟩
    refine ⟨ha, Nat.modEq_zero_iff_dvd.mp ?_⟩
    simpa only [Nat.sub_self] using Nat.ModEq.sub_right hp (by decide : 1 ≤ 1) he

theorem compatible_cons_block {a N : ℕ} {as : List ℕ} (hN : 0 < N)
    (ha : 0 < a) (h : Compatible N (a :: as)) : ValidBlock a N := by
  apply (validBlock_iff_congruence hN).mpr
  refine ⟨ha, ?_⟩
  have h3 : Nat.ModEq 3 (2 ^ (a :: as).sum * N) (affineNumerator (a :: as)) :=
    h.of_dvd (by simp only [List.length_cons, pow_succ]; exact dvd_mul_left 3 _)
  have hn : Nat.ModEq 3 (affineNumerator (a :: as)) (2 ^ as.sum) := by
    change (2 ^ as.sum + 3 * affineNumerator as) % 3 = (2 ^ as.sum) % 3
    omega
  have hh := h3.trans hn
  have he : 2 ^ (a :: as).sum * N = 2 ^ as.sum * (2 ^ a * N) := by
    simp only [List.sum_cons, pow_add]
    ring
  rw [he] at hh
  have hg : Nat.Coprime 3 (2 ^ as.sum) := (by decide : Nat.Coprime 3 2).pow_right _
  exact Nat.ModEq.cancel_left_of_coprime hg (by simpa only [mul_one] using hh)

theorem compatible_cons_iff_tail {a N : ℕ} {as : List ℕ} (hN : 0 < N)
    (hv : ValidBlock a N) :
    Compatible N (a :: as) ↔ Compatible (inverseValue a N) as := by
  have hid := inverse_identity hN hv
  have he : 2 ^ (a :: as).sum * N =
      3 * (2 ^ as.sum * inverseValue a N) + 2 ^ as.sum := by
    simp only [List.sum_cons, pow_add]
    calc
      2 ^ a * 2 ^ as.sum * N = 2 ^ as.sum * (2 ^ a * N) := by ring
      _ = 2 ^ as.sum * (3 * inverseValue a N + 1) := by rw [hid]
      _ = _ := by ring
  unfold Compatible
  rw [he]
  simp only [List.length_cons, affineNumerator]
  rw [Nat.add_comm (2 ^ as.sum), Nat.ModEq.add_iff_right (Nat.ModEq.refl (2 ^ as.sum))]
  rw [pow_succ']
  exact Nat.ModEq.mul_left_cancel_iff' (by decide : 3 ≠ 0)

theorem validTuple_iff_compatible {N : ℕ} {as : List ℕ} (hN : 0 < N)
    (hpos : ∀ a ∈ as, 0 < a) : ValidTuple N as ↔ Compatible N as := by
  induction as generalizing N with
  | nil => simp [ValidTuple, Compatible, affineNumerator, Nat.ModEq, Nat.mod_one]
  | cons a as ih =>
    have ha : 0 < a := hpos a (by simp)
    have htail : ∀ b ∈ as, 0 < b := fun b hb => hpos b (by simp [hb])
    constructor
    · rintro ⟨hv, ht⟩
      exact (compatible_cons_iff_tail hN hv).mpr ((ih (inverse_positive hN hv) htail).mp ht)
    · intro hc
      have hv := compatible_cons_block hN ha hc
      refine ⟨hv, ?_⟩
      exact (ih (inverse_positive hN hv) htail).mpr ((compatible_cons_iff_tail hN hv).mp hc)

theorem validWord_iff_compatible {k N : ℕ} (hN : 0 < N) (w : GeometricWord k) :
    ValidWord k N w ↔ Compatible N (wordList k w) :=
  validTuple_iff_compatible hN (wordList_positive k w)

#print axioms validTuple_iff_compatible
#print axioms validWord_iff_compatible

end CollatzCylinderPacking.Arithmetic
