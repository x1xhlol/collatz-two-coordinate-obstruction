import Mathlib.Tactic

/-!
A scalar conductor bootstrap. The recursion and qualitative contraction
are hypotheses; this file does not establish them for a native source law.
-/

set_option autoImplicit false

namespace CollatzResearch

theorem trap_bootstrap_rounded_block
    (theta lambda : ℝ) (htheta : 0 < theta) (hlambda : 0 < lambda)
    (hmargin : theta + 2 * lambda ≤ 1)
    (n : ℕ) (hn : 1 ≤ n) (hscale : 2 ≤ lambda * (n : ℝ)) :
    ∃ u : ℕ, 0 < u ∧ 2 * u < n ∧
      theta * (n : ℝ) ≤ (2 * u : ℕ) ∧
      lambda * (n : ℝ) ≤ (n - 2 * u : ℕ) ∧
      (n - 2 * u : ℕ) < lambda * (n : ℝ) + 2 := by
  let u : ℕ := ⌊(1 - lambda) * (n : ℝ) / 2⌋₊
  have hnr : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  have hlambda1 : lambda < 1 := by linarith
  have hx : 0 ≤ (1 - lambda) * (n : ℝ) / 2 := by positivity
  have hfloor := Nat.floor_le hx
  have hfloor' := Nat.lt_floor_add_one ((1 - lambda) * (n : ℝ) / 2)
  change (u : ℝ) ≤ (1 - lambda) * (n : ℝ) / 2 at hfloor
  change (1 - lambda) * (n : ℝ) / 2 < (u : ℝ) + 1 at hfloor'
  have hthetaN := mul_le_mul_of_nonneg_right hmargin (le_of_lt hnr)
  have hlarge : theta * (n : ℝ) ≤ (2 * u : ℕ) := by
    push_cast
    nlinarith
  have hu : 0 < u := by
    have hpos : 0 < (u : ℝ) := by
      push_cast at hlarge
      nlinarith [mul_pos htheta hnr]
    exact_mod_cast hpos
  have hlt : 2 * u < n := by
    have hlt' : (2 : ℝ) * (u : ℝ) < (n : ℝ) := by nlinarith
    exact_mod_cast hlt'
  refine ⟨u, hu, hlt, hlarge, ?_, ?_⟩ <;>
    rw [Nat.cast_sub (Nat.le_of_lt hlt)] <;> push_cast <;> nlinarith

theorem trap_deficit_bootstrap_of_blocks
    (Q : ℕ → ℕ → ℝ) (A M : ℕ) (lambda : ℝ) (hlambda : 0 < lambda)
    (hQ : ∀ n J, 1 ≤ n → 2 * J ≤ n → 0 ≤ Q n J ∧ Q n J ≤ 1)
    (hrec : ∀ n J u, 1 ≤ n → 2 * J ≤ n → u ≤ J → 2 * u < n →
      Q n J ≤ Q n u * Q (n - 2 * u) (J - u))
    (hblock : ∀ n J, 1 ≤ n → M ≤ n → 2 * J ≤ n →
      (n - 2 * J + 1 : ℕ) ≤ lambda * (n : ℝ) →
      ∃ u : ℕ, 0 < u ∧ u ≤ J ∧ 2 * u < n ∧
        lambda * (n : ℝ) ≤ (n - 2 * u : ℕ) ∧ Q n u ≤ lambda ^ A) :
    ∃ C : ℝ, 0 < C ∧ ∀ n J, 1 ≤ n → 2 * J ≤ n →
      Q n J ≤ C * ((n - 2 * J + 1 : ℕ) / (n : ℝ)) ^ A := by
  let B : ℝ := max ((M : ℝ) + 1) (1 / lambda)
  have hB0 : 0 < B := lt_of_lt_of_le (by positivity) (le_max_left _ _)
  have hMB : (M : ℝ) < B := lt_of_lt_of_le (by linarith) (le_max_left _ _)
  have hlambdaB : 1 ≤ B * lambda :=
    (div_le_iff₀ hlambda).mp (le_max_right _ _)
  have hscaled : ∀ n J, 1 ≤ n → 2 * J ≤ n →
      Q n J * (n : ℝ) ^ A ≤ B ^ A * (n - 2 * J + 1 : ℕ) ^ A := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro J hn hJ
      have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
      have hD : (1 : ℝ) ≤ (n - 2 * J + 1 : ℕ) := by exact_mod_cast (Nat.le_add_left 1 _)
      have hD0 : (0 : ℝ) ≤ (n - 2 * J + 1 : ℕ) := by positivity
      by_cases hsmall : (n : ℝ) ≤ B * (n - 2 * J + 1 : ℕ)
      · calc
          Q n J * (n : ℝ) ^ A ≤ (n : ℝ) ^ A :=
            mul_le_of_le_one_left (by positivity) (hQ n J hn hJ).2
          _ ≤ (B * (n - 2 * J + 1 : ℕ)) ^ A :=
            pow_le_pow_left₀ (le_of_lt hnpos) hsmall A
          _ = _ := mul_pow _ _ _
      · have hlarge : B * (n - 2 * J + 1 : ℕ) < (n : ℝ) := lt_of_not_ge hsmall
        have hBn : B < (n : ℝ) :=
          (le_mul_of_one_le_right (le_of_lt hB0) hD).trans_lt hlarge
        have hMn : M ≤ n := Nat.le_of_lt (by exact_mod_cast hMB.trans hBn)
        have hDscale : (n - 2 * J + 1 : ℕ) ≤ lambda * (n : ℝ) := by
          have hmul := mul_le_mul_of_nonneg_right hlambdaB hD0
          have hmul' := mul_lt_mul_of_pos_right hlarge hlambda
          nlinarith
        obtain ⟨u, hu, huJ, hun, hnext, hcontract⟩ := hblock n J hn hMn hJ hDscale
        have hnextpos : 1 ≤ n - 2 * u := by omega
        have hnextlt : n - 2 * u < n := by omega
        have hremain : 2 * (J - u) ≤ n - 2 * u := by omega
        have hdeficit : n - 2 * u - 2 * (J - u) + 1 = n - 2 * J + 1 := by omega
        have htail0 := (hQ (n - 2 * u) (J - u) hnextpos hremain).1
        have hstep := (hrec n J u hn hJ huJ hun).trans
          (mul_le_mul_of_nonneg_right hcontract htail0)
        calc
          Q n J * (n : ℝ) ^ A ≤
              (lambda ^ A * Q (n - 2 * u) (J - u)) * (n : ℝ) ^ A :=
            mul_le_mul_of_nonneg_right hstep (by positivity)
          _ = Q (n - 2 * u) (J - u) * (lambda * (n : ℝ)) ^ A := by
            rw [mul_pow]
            ring
          _ ≤ Q (n - 2 * u) (J - u) * (n - 2 * u : ℕ) ^ A :=
            mul_le_mul_of_nonneg_left
              (pow_le_pow_left₀ (by positivity) hnext A) htail0
          _ ≤ B ^ A * (n - 2 * J + 1 : ℕ) ^ A := by
            simpa only [hdeficit] using ih (n - 2 * u) hnextlt (J - u) hnextpos hremain
  refine ⟨B ^ A, by positivity, ?_⟩
  intro n J hn hJ
  have hnpos : 0 < (n : ℝ) := by exact_mod_cast (show 0 < n by omega)
  rw [div_pow, ← mul_div_assoc]
  exact (le_div_iff₀ (pow_pos hnpos A)).mpr (hscaled n J hn hJ)

theorem trap_deficit_bootstrap
    (Q : ℕ → ℕ → ℝ) (theta : ℝ) (htheta0 : 0 < theta) (htheta1 : theta < 1)
    (hQ : ∀ n J, 1 ≤ n → 2 * J ≤ n → 0 ≤ Q n J ∧ Q n J ≤ 1)
    (hrec : ∀ n J u, 1 ≤ n → 2 * J ≤ n → u ≤ J → 2 * u < n →
      Q n J ≤ Q n u * Q (n - 2 * u) (J - u))
    (hqual : ∀ epsilon : ℝ, 0 < epsilon → ∃ N : ℕ,
      ∀ n J, N ≤ n → 1 ≤ n → 2 * J ≤ n →
        theta * (n : ℝ) ≤ (2 * J : ℕ) → Q n J ≤ epsilon) :
    ∀ A : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ n J, 1 ≤ n → 2 * J ≤ n →
      Q n J ≤ C * ((n - 2 * J + 1 : ℕ) / (n : ℝ)) ^ A := by
  intro A
  let lambda : ℝ := (1 - theta) / 2
  have hlambda : 0 < lambda := by dsimp [lambda]; positivity
  have hmargin : theta + 2 * lambda ≤ 1 := by dsimp [lambda]; linarith
  obtain ⟨N, hN⟩ := hqual (lambda ^ A) (pow_pos hlambda A)
  let M : ℕ := max N ⌈2 / lambda⌉₊
  apply trap_deficit_bootstrap_of_blocks Q A M lambda hlambda hQ hrec
  intro n J hn hMn hJ hD
  have hceil : (⌈2 / lambda⌉₊ : ℕ) ≤ n := (Nat.le_max_right _ _).trans hMn
  have hscale : 2 ≤ lambda * (n : ℝ) := by
    have hceil' : (⌈2 / lambda⌉₊ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hceil
    have hdiv := (Nat.le_ceil (2 / lambda)).trans hceil'
    have hmul := (div_le_iff₀ hlambda).mp hdiv
    simpa only [mul_comm] using hmul
  obtain ⟨u, hu, hun, hlarge, hnext, _⟩ :=
    trap_bootstrap_rounded_block theta lambda htheta0 hlambda hmargin n hn hscale
  have huJ : u ≤ J := by
    have hcast := hD.trans hnext
    rw [Nat.cast_add, Nat.cast_sub hJ, Nat.cast_sub (Nat.le_of_lt hun)] at hcast
    push_cast at hcast
    have hreal : (u : ℝ) ≤ (J : ℝ) := by linarith
    exact_mod_cast hreal
  refine ⟨u, hu, huJ, hun, hnext, ?_⟩
  exact hN n u ((Nat.le_max_left _ _).trans hMn) hn (Nat.le_of_lt hun) hlarge

end CollatzResearch

#print axioms CollatzResearch.trap_bootstrap_rounded_block
#print axioms CollatzResearch.trap_deficit_bootstrap_of_blocks
#print axioms CollatzResearch.trap_deficit_bootstrap
