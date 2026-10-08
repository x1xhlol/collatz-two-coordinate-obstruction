import CanonicalEnvelopePointwiseSqueeze
import FixedBasinGreenBoundary

set_option autoImplicit false

open scoped ENNReal
open CollatzCylinderPacking CollatzCylinderPacking.Arithmetic Erdos1135.Tao
open CollatzCanonical.GreenKernelScalars

namespace CollatzCanonical.IntegerStationaryEnvelope

theorem periodic_predecessor_unique {p q : ℕ}
    (hp : ∃ r : ℕ, 0 < r ∧ iterate r p = p)
    (hq : ∃ r : ℕ, 0 < r ∧ iterate r q = q)
    (hstep : step p = step q) : p = q := by
  obtain ⟨r, hr, hpr⟩ := hp
  obtain ⟨s, hs, hqs⟩ := hq
  have hp' := iterate_mul_period hpr s
  have hq' : iterate (s * r) q = q := by
    simpa only [Nat.mul_comm] using iterate_mul_period hqs r
  have hpos : 0 < s * r := Nat.mul_pos hs hr
  have hsplit : s * r = 1 + (s * r - 1) := by omega
  rw [hsplit, iterate_add] at hp' hq'
  change iterate (s * r - 1) (step p) = p at hp'
  change iterate (s * r - 1) (step q) = q at hq'
  exact hp'.symm.trans ((congrArg (iterate (s * r - 1)) hstep).trans hq')

theorem periodic_iterate {n : ℕ}
    (hn : ∃ r : ℕ, 0 < r ∧ iterate r n = n) (k : ℕ) :
    ∃ r : ℕ, 0 < r ∧ iterate r (iterate k n) = iterate k n := by
  obtain ⟨r, hr, hret⟩ := hn
  refine ⟨r, hr, ?_⟩
  rw [← iterate_add, Nat.add_comm k r, iterate_add, hret]

theorem periodic_defect_one_step {d : ℕ → ℝ}
    (hz : ∀ n : ℕ, 0 < n → (¬ ∃ r : ℕ, 0 < r ∧ iterate r n = n) → d n = 0)
    (hs : ∀ n : ℕ, 0 < n → d n ≤ (1 / 2 : ℝ) * d (2 * n) +
      (3 / 2 : ℝ) * (if n % 3 = 2 then d (oddPredecessor n) else 0))
    {n : ℕ} (hn : 0 < n) (hp : ∃ r : ℕ, 0 < r ∧ iterate r n = n) :
    d (step n) ≤ orbitRatio 1 n * d n := by
  have hpos : 0 < step n := by
    simpa only [iterate] using Correction.iterate_pos 1 hn
  have hsub := hs (step n) hpos
  by_cases he : n % 2 = 0
  · have hnstep := step_even he
    have hzero : (if step n % 3 = 2 then d (oddPredecessor (step n)) else 0) = 0 := by
      split_ifs with hres
      · apply hz _ (oddPredecessor_spec hres).1
        intro hper
        have heq := periodic_predecessor_unique hper hp (oddPredecessor_spec hres).2.2
        have ho := (oddPredecessor_spec hres).2.1
        rw [heq, he] at ho
        contradiction
      · rfl
    rw [hzero, hnstep, mul_zero, add_zero] at hsub
    have hratio : orbitRatio 1 n = (1 / 2 : ℝ) := by
      rw [← hnstep]
      exact orbitRatio_one_even (step n)
    simpa only [hratio] using hsub
  · have ho : n % 2 = 1 := by omega
    have hpre := step_preimage_iff.mp (rfl : step n = step n)
    have hodd : step n % 3 = 2 ∧ n = oddPredecessor (step n) := by
      rcases hpre with hbad | hgood
      · have hm := congrArg (fun x : ℕ => x % 2) hbad
        simp only [Nat.mul_mod_right] at hm
        exact False.elim (he hm)
      · exact hgood
    have hzero : d (2 * step n) = 0 := by
      apply hz _ (by omega)
      intro hper
      have heq := periodic_predecessor_unique hper hp (step_two_mul (step n))
      have hm := congrArg (fun x : ℕ => x % 2) heq
      simp only [Nat.mul_mod_right, ho] at hm
      contradiction
    rw [hzero, if_pos hodd.1, ← hodd.2, mul_zero, zero_add] at hsub
    simpa only [orbitRatio_one_odd ho] using hsub

theorem periodic_defect_iterate {d : ℕ → ℝ}
    (hz : ∀ n : ℕ, 0 < n → (¬ ∃ r : ℕ, 0 < r ∧ iterate r n = n) → d n = 0)
    (hs : ∀ n : ℕ, 0 < n → d n ≤ (1 / 2 : ℝ) * d (2 * n) +
      (3 / 2 : ℝ) * (if n % 3 = 2 then d (oddPredecessor n) else 0))
    {n : ℕ} (hn : 0 < n) (hp : ∃ r : ℕ, 0 < r ∧ iterate r n = n) (k : ℕ) :
    d (iterate k n) ≤ orbitRatio k n * d n := by
  induction k with
  | zero => simp [iterate, orbitRatio, oddCount]
  | succ k ih =>
    have h := periodic_defect_one_step hz hs (Correction.iterate_pos k hn)
      (periodic_iterate hp k)
    calc
      d (iterate (k + 1) n) ≤ orbitRatio 1 (iterate k n) * d (iterate k n) := h
      _ ≤ orbitRatio 1 (iterate k n) * (orbitRatio k n * d n) :=
        mul_le_mul_of_nonneg_left ih (orbitRatio_pos 1 (iterate k n)).le
      _ = orbitRatio (k + 1) n * d n := by rw [orbitRatio_add]; ring

theorem nonnegative_defect_zero {d : ℕ → ℝ}
    (hd : ∀ n : ℕ, 0 < n → 0 ≤ d n)
    (hz : ∀ n : ℕ, 0 < n → (¬ ∃ r : ℕ, 0 < r ∧ iterate r n = n) → d n = 0)
    (hs : ∀ n : ℕ, 0 < n → d n ≤ (1 / 2 : ℝ) * d (2 * n) +
      (3 / 2 : ℝ) * (if n % 3 = 2 then d (oddPredecessor n) else 0))
    {n : ℕ} (hn : 0 < n) : d n = 0 := by
  by_cases hp : ∃ r : ℕ, 0 < r ∧ iterate r n = n
  · obtain ⟨r, hr, hret⟩ := hp
    have hi := periodic_defect_iterate hz hs hn ⟨r, hr, hret⟩ r
    rw [hret] at hi
    have hc := (positive_cycle_ratio_bounds hn hr hret).2
    have hnonneg := hd n hn
    nlinarith
  · exact hz n hn hp

theorem actualDensityValue_nonneg_of_pos {n : ℕ} (hn : 0 < n) :
    0 ≤ actualDensityValue actualFirstHitDensity n := by
  unfold actualDensityValue
  exact mul_nonneg (mul_nonneg (mul_nonneg delta_pos.le
    (greenCycleFactor_one_pos hn).le) (Nat.cast_nonneg n)) (actualFirstHitDensity_nonneg n)

theorem integerEnvelopeValue_eq_actualDensityValue {n : ℕ} (hn : 0 < n) :
    integerEnvelopeValue n = actualDensityValue actualFirstHitDensity n := by
  let d : ℕ → ℝ := fun n => actualDensityValue actualFirstHitDensity n - integerEnvelopeValue n
  have hd (m : ℕ) (hm : 0 < m) : 0 ≤ d m := by
    have h := ENNReal.toReal_mono (ne_of_lt (actualIntegerTrace_lt_top m))
      (canonicalIntegerEnvelope_natCast_le m hm)
    rw [actualIntegerTrace, ENNReal.toReal_ofReal (actualDensityValue_nonneg_of_pos hm)] at h
    exact sub_nonneg.mpr h
  have hz (m : ℕ) (hm : 0 < m)
      (hnp : ¬ ∃ r : ℕ, 0 < r ∧ iterate r m = m) : d m = 0 := by
    change actualDensityValue actualFirstHitDensity m -
      (canonicalIntegerEnvelope (m : ℤ_[3])).toReal = 0
    rw [canonicalIntegerEnvelope_natCast_eq_of_nonperiodic hm hnp,
      actualIntegerTrace, ENNReal.toReal_ofReal (actualDensityValue_nonneg_of_pos hm), sub_self]
  have hs (m : ℕ) (hm : 0 < m) : d m ≤ (1 / 2 : ℝ) * d (2 * m) +
      (3 / 2 : ℝ) * (if m % 3 = 2 then d (oddPredecessor m) else 0) := by
    have hg := actual_unconditional_density_harmonic hm
    have he := integerEnvelopeValue_superharmonic m hm
    dsimp only [d]
    split_ifs at hg he ⊢ <;> linarith
  have h := nonnegative_defect_zero hd hz hs hn
  dsimp only [d] at h
  linarith

theorem canonicalIntegerEnvelope_natCast_eq {n : ℕ} (hn : 0 < n) :
    canonicalIntegerEnvelope (n : ℤ_[3]) = actualIntegerTrace n := by
  rw [← ENNReal.ofReal_toReal (canonicalIntegerEnvelope_natCast_ne_top hn)]
  change ENNReal.ofReal (integerEnvelopeValue n) = _
  rw [integerEnvelopeValue_eq_actualDensityValue hn]
  rfl

#print axioms nonnegative_defect_zero
#print axioms canonicalIntegerEnvelope_natCast_eq

end CollatzCanonical.IntegerStationaryEnvelope
