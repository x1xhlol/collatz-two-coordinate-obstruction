import CollatzAffineProgressions
import OddAffineParameter
import AffineDifferenceMeasure

set_option autoImplicit false

namespace CollatzAffineSynchronization

open CollatzPositiveProgression CollatzOddAffineParameter

def Synchronizes (r a s b : ℕ) : Prop :=
  ∃ k t₀ : ℕ, ∀ t : ℕ,
    iterate k (a + 3 ^ r * (t₀ + 2 ^ k * t)) =
      iterate k (b + 3 ^ s * (t₀ + 2 ^ k * t))

theorem synchronizes_symm (r a s b : ℕ) (h : Synchronizes r a s b) :
    Synchronizes s b r a := by
  obtain ⟨k, t₀, h⟩ := h
  exact ⟨k, t₀, fun t => (h t).symm⟩

theorem three_pow_odd (r : ℕ) : 3 ^ r % 2 = 1 := by
  simp [Nat.pow_mod]

theorem synchronizes_same_ordered (r a b : ℕ) (hab : a ≤ b) :
    Synchronizes r a r b := by
  obtain ⟨k, c, _, hc⟩ := coalesces_all (b - a)
  obtain ⟨t₀, ht₀, hmod⟩ :=
    exists_large_odd_affine_parameter_modEq a (3 ^ r) k c c (three_pow_odd r)
  have hp : 0 < (3 : ℕ) ^ r := pow_pos (by omega) r
  have hle : c ≤ a + 3 ^ r * t₀ := by nlinarith
  obtain ⟨u, hu⟩ := (Nat.modEq_iff_exists_eq_add hle).mp hmod.symm
  refine ⟨k, t₀, ?_⟩
  intro t
  have heq : a + 3 ^ r * (t₀ + 2 ^ k * t) = c + 2 ^ k * (u + 3 ^ r * t) := by
    calc
      _ = (a + 3 ^ r * t₀) + 2 ^ k * (3 ^ r * t) := by ring
      _ = _ := by rw [hu]; ring
  have hbeq : b + 3 ^ r * (t₀ + 2 ^ k * t) =
      c + 2 ^ k * (u + 3 ^ r * t) + (b - a) := by
    calc
      _ = (a + 3 ^ r * (t₀ + 2 ^ k * t)) + (b - a) := by omega
      _ = _ := by rw [heq]
  rw [heq, hbeq]
  exact (hc (u + 3 ^ r * t)).1

theorem synchronizes_same (r a b : ℕ) : Synchronizes r a r b := by
  rcases le_total a b with h | h
  · exact synchronizes_same_ordered r a b h
  · exact synchronizes_symm r b r a (synchronizes_same_ordered r b a h)

theorem step_refined_family (r a e t : ℕ) :
    step (a + 3 ^ r * (e + 2 * t)) =
      step (a + 3 ^ r * e) + 3 ^ (r + (a + 3 ^ r * e) % 2) * t := by
  have heq : a + 3 ^ r * (e + 2 * t) = (a + 3 ^ r * e) + 2 * (3 ^ r * t) := by ring
  rw [heq, step_add_even, pow_add]
  ring

theorem synchronizes_step (r a s b e : ℕ)
    (h : Synchronizes
      (r + (a + 3 ^ r * e) % 2) (step (a + 3 ^ r * e))
      (s + (b + 3 ^ s * e) % 2) (step (b + 3 ^ s * e))) :
    Synchronizes r a s b := by
  obtain ⟨k, p, h⟩ := h
  refine ⟨k + 1, e + 2 * p, ?_⟩
  intro t
  have heq : (e + 2 * p) + 2 ^ (k + 1) * t = e + 2 * (p + 2 ^ k * t) := by
    rw [pow_succ]
    ring
  simp only [heq, iterate, step_refined_family]
  exact h t

def difference (d a b : ℕ) : ℤ := (b : ℤ) - (3 : ℤ) ^ d * a

theorem difference_refine (d r a b e : ℕ) :
    difference d (a + 3 ^ r * e) (b + 3 ^ (r + d) * e) = difference d a b := by
  simp only [difference, Nat.cast_add, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat, pow_add]
  ring

theorem difference_parity (d a b : ℕ) :
    difference d a b % 2 = ((b : ℤ) % 2 - (a : ℤ) % 2) % 2 := by
  have hp : (3 : ℤ) ^ d % 2 = 1 := by exact_mod_cast three_pow_odd d
  simp [difference, Int.sub_emod, Int.mul_emod, hp]

theorem difference_even_parity (d a b : ℕ) (h : difference d a b % 2 = 0) :
    a % 2 = b % 2 := by
  rw [difference_parity] at h
  omega

theorem difference_odd_parity (d a b : ℕ) (h : difference d a b % 2 ≠ 0)
    (ha : a % 2 = 1) : b % 2 = 0 := by
  rw [difference_parity] at h
  omega

theorem twice_step_even (a : ℕ) (ha : a % 2 = 0) : 2 * step a = a := by
  simp only [step, ha, if_pos]
  omega

theorem twice_step_odd (a : ℕ) (ha : a % 2 = 1) : 2 * step a = 3 * a + 1 := by
  simp only [step, ha, Nat.one_ne_zero, if_false]
  omega

theorem difference_even_step (d a b : ℕ) (ha : a % 2 = 0) (hb : b % 2 = 0) :
    2 * difference d (step a) (step b) = difference d a b := by
  have ha' : 2 * (step a : ℤ) = a := by exact_mod_cast twice_step_even a ha
  have hb' : 2 * (step b : ℤ) = b := by exact_mod_cast twice_step_even b hb
  simp only [difference]
  calc
    _ = 2 * (step b : ℤ) - (3 : ℤ) ^ d * (2 * step a) := by ring
    _ = _ := by rw [ha', hb']

theorem difference_odd_step (d a b : ℕ) (ha : a % 2 = 1) (hb : b % 2 = 1) :
    2 * difference d (step a) (step b) = 3 * difference d a b + 1 - (3 : ℤ) ^ d := by
  have ha' : 2 * (step a : ℤ) = 3 * (a : ℤ) + 1 := by exact_mod_cast twice_step_odd a ha
  have hb' : 2 * (step b : ℤ) = 3 * (b : ℤ) + 1 := by exact_mod_cast twice_step_odd b hb
  simp only [difference]
  calc
    _ = 2 * (step b : ℤ) - (3 : ℤ) ^ d * (2 * step a) := by ring
    _ = _ := by rw [ha', hb']; ring

theorem synchronizes_ordered (d r a b : ℕ) : Synchronizes r a (r + d) b := by
  induction d generalizing r a b with
  | zero => simpa only [Nat.add_zero] using synchronizes_same r a b
  | succ d outer =>
    have main : ∀ W : ℕ, ∀ r a b : ℕ,
        differenceWeight (d + 1) (difference (d + 1) a b) = W →
        Synchronizes r a (r + (d + 1)) b := by
      intro W
      induction W using Nat.strong_induction_on with
      | h W inner =>
        intro r a b hw
        by_cases hz : difference (d + 1) a b = 0
        · obtain ⟨e, _, he⟩ :=
            exists_large_odd_affine_parameter a (3 ^ r) 1 1 0 (three_pow_odd r)
          norm_num only [pow_one, Nat.one_mod] at he
          let A := a + 3 ^ r * e
          let B := b + 3 ^ (r + (d + 1)) * e
          have hA : A % 2 = 1 := he
          have hdiff : difference (d + 1) A B = 0 := by
            rw [difference_refine, hz]
          have hB : B % 2 = 1 := by
            have hsame := difference_even_parity (d + 1) A B (by rw [hdiff]; norm_num)
            omega
          have hn : 2 * difference (d + 1) (step A) (step B) = 1 - (3 : ℤ) ^ (d + 1) := by
            rw [difference_odd_step _ _ _ hA hB, hdiff]
            ring
          have hlt : differenceWeight (d + 1) (difference (d + 1) (step A) (step B)) < W := by
            rw [← hw, hz]
            exact weight_zero (d + 1) _ (by omega) hn
          have hs := inner _ hlt (r + 1) (step A) (step B) rfl
          apply synchronizes_step r a (r + (d + 1)) b e
          change Synchronizes (r + A % 2) (step A) ((r + (d + 1)) + B % 2) (step B)
          have hexp : (r + (d + 1)) + 1 = (r + 1) + (d + 1) := by omega
          simpa only [hA, hB, hexp] using hs
        by_cases heven : difference (d + 1) a b % 2 = 0
        · obtain ⟨e, _, he⟩ :=
            exists_large_odd_affine_parameter a (3 ^ r) 1 0 0 (three_pow_odd r)
          norm_num only [pow_one, Nat.zero_mod] at he
          let A := a + 3 ^ r * e
          let B := b + 3 ^ (r + (d + 1)) * e
          have hA : A % 2 = 0 := he
          have hdiff : difference (d + 1) A B = difference (d + 1) a b :=
            difference_refine (d + 1) r a b e
          have hB : B % 2 = 0 := by
            have hsame := difference_even_parity (d + 1) A B (by rw [hdiff]; exact heven)
            omega
          have hn : 2 * difference (d + 1) (step A) (step B) = difference (d + 1) a b := by
            rw [difference_even_step _ _ _ hA hB, hdiff]
          have hlt : differenceWeight (d + 1) (difference (d + 1) (step A) (step B)) < W := by
            rw [← hw]
            exact weight_half (d + 1) _ _ hz hn
          have hs := inner _ hlt r (step A) (step B) rfl
          apply synchronizes_step r a (r + (d + 1)) b e
          change Synchronizes (r + A % 2) (step A) ((r + (d + 1)) + B % 2) (step B)
          simpa only [hA, hB, Nat.add_zero] using hs
        · obtain ⟨e, _, he⟩ :=
            exists_large_odd_affine_parameter a (3 ^ r) 1 1 0 (three_pow_odd r)
          norm_num only [pow_one, Nat.one_mod] at he
          let A := a + 3 ^ r * e
          let B := b + 3 ^ (r + (d + 1)) * e
          have hA : A % 2 = 1 := he
          have hdiff : difference (d + 1) A B = difference (d + 1) a b :=
            difference_refine (d + 1) r a b e
          have hB : B % 2 = 0 :=
            difference_odd_parity (d + 1) A B (by rw [hdiff]; exact heven) hA
          have hs := outer (r + 1) (step A) (step B)
          apply synchronizes_step r a (r + (d + 1)) b e
          change Synchronizes (r + A % 2) (step A) ((r + (d + 1)) + B % 2) (step B)
          have hexp : r + (d + 1) = (r + 1) + d := by omega
          simpa only [hA, hB, Nat.add_zero, hexp] using hs
    exact main _ r a b rfl

theorem synchronizes_all (r a s b : ℕ) : Synchronizes r a s b := by
  rcases le_total r s with h | h
  · have hs : r + (s - r) = s := by omega
    simpa only [hs] using synchronizes_ordered (s - r) r a b
  · have hr : s + (r - s) = r := by omega
    apply synchronizes_symm s b r a
    simpa only [hr] using synchronizes_ordered (r - s) s b a

#print axioms synchronizes_all

end CollatzAffineSynchronization
