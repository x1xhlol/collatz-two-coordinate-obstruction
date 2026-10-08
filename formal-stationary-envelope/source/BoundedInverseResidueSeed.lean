import Erdos1135Predecessor.ND.PositiveDensity.GeneralTargetResidueCoverage
import TwoSiblingNonreturn

set_option autoImplicit false

namespace CollatzCanonical.BoundedInverseSeed
open Erdos1135Predecessor
open Erdos1135Predecessor.ND.PositiveDensity

theorem exists_generalTargetRoot_start_bounded {a : ℕ} (hthree : ¬ 3 ∣ a) :
    ∃ r e : ℕ, 0 < e ∧ e ≤ 2 ∧ 3 * r + 1 = 2 ^ e * a := by
  have hmod : a % 3 = 1 ∨ a % 3 = 2 := by
    have hlt := Nat.mod_lt a (by norm_num : 0 < 3)
    have hn : a % 3 ≠ 0 := by simpa only [Nat.dvd_iff_mod_eq_zero] using hthree
    omega
  rcases hmod with h | h
  · refine ⟨(4 * a) / 3, 2, by norm_num, le_rfl, ?_⟩
    have hm : (4 * a) % 3 = 1 := by simp [Nat.mul_mod, h]
    norm_num
    omega
  · refine ⟨(2 * a) / 3, 1, by norm_num, by norm_num, ?_⟩
    have hm : (2 * a) % 3 = 1 := by simp [Nat.mul_mod, h]
    norm_num
    omega

theorem generalTargetRoot_le_explicit_multiple {a r e k B : ℕ}
    (hstart : 3 * r + 1 = 2 ^ e * a) (he : e ≤ 2) (hk : k ≤ B) :
    ndGeneralTargetRoot r k ≤ 4 ^ (B + 1) * a := by
  have hc := generalTargetRoot_cleared r k
  rw [hstart] at hc
  have htwo : 2 ^ e ≤ 4 := by
    simpa using (pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) he)
  have hfour : 4 ^ k ≤ 4 ^ B := pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 4) hk
  have hprod : 4 ^ k * (2 ^ e * a) ≤ 4 ^ (B + 1) * a := by
    calc
      _ ≤ 4 ^ B * (4 * a) := Nat.mul_le_mul hfour (Nat.mul_le_mul_right a htwo)
      _ = _ := by rw [pow_succ]; ring
  omega

theorem generalTargetRoot_strictMono (r : ℕ) : StrictMono (ndGeneralTargetRoot r) := by
  intro j k hjk
  have hp : 4 ^ j < 4 ^ k := Nat.pow_lt_pow_right (by norm_num : 1 < 4) hjk
  have hj := generalTargetRoot_cleared r j
  have hk := generalTargetRoot_cleared r k
  nlinarith

/-- A prescribed ternary residue contains a nonreturning ordinary inverse seed
whose height is bounded by an explicit multiple of the target. -/
theorem exists_bounded_nonreturning_predecessor_in_residue
    {a : ℕ} (_ha : 0 < a) (hthree : ¬ 3 ∣ a)
    (q X : ℕ) (y : Fin (3 ^ q)) :
    ∃ R : ℕ, X < R ∧ Odd R ∧ Reaches R a ∧ R % 3 ^ q = y ∧
      R ≤ 4 ^ ((X + 3) * 3 ^ q + 1) * a ∧
      ∀ k : ℕ, 0 < k → (Tao.syracuse^[k]) R ≠ R := by
  obtain ⟨r, e, _he, he2, hstart⟩ := exists_generalTargetRoot_start_bounded hthree
  obtain ⟨j, hj⟩ := generalTargetRoot_residue_surjective r q y
  let k₁ : ℕ := (j : ℕ) + (X + 1) * 3 ^ q
  let k₂ : ℕ := (j : ℕ) + (X + 2) * 3 ^ q
  have hP : 1 ≤ 3 ^ q := Nat.succ_le_of_lt (by positivity)
  have hk₁ : X < k₁ := by
    have h := Nat.mul_le_mul_left (X + 1) hP
    dsimp [k₁]
    omega
  have hk₂ : k₁ < k₂ := by dsimp [k₁, k₂]; nlinarith
  have hB₂ : k₂ ≤ (X + 3) * 3 ^ q := by
    have hjlt := j.isLt
    dsimp [k₂]
    nlinarith
  have hB₁ : k₁ ≤ (X + 3) * 3 ^ q := hk₂.le.trans hB₂
  have hres (t : ℕ) : ndGeneralTargetRoot r ((j : ℕ) + t * 3 ^ q) % 3 ^ q = y := by
    have h := generalTargetRoot_modEq_of_period r q j t
    change ndGeneralTargetRoot r (j : ℕ) % 3 ^ q =
      ndGeneralTargetRoot r ((j : ℕ) + t * 3 ^ q) % 3 ^ q at h
    exact h.symm.trans (congrArg Fin.val hj)
  have hcommon : Tao.syracuse (ndGeneralTargetRoot r k₁) =
      Tao.syracuse (ndGeneralTargetRoot r k₂) := by
    rw [generalTargetRoot_syracuse, generalTargetRoot_syracuse]
  have hne : ndGeneralTargetRoot r k₁ ≠ ndGeneralTargetRoot r k₂ :=
    (generalTargetRoot_strictMono r hk₂).ne
  have hchoose := no_return_or_no_return_of_same_successor hne hcommon
  rcases hchoose with hnonreturn | hnonreturn
  · refine ⟨ndGeneralTargetRoot r k₁,
      hk₁.trans_le (generalTargetRoot_ge_index r k₁),
      generalTargetRoot_odd r k₁ (by omega),
      generalTargetRoot_reaches hstart (by omega), hres (X + 1),
      generalTargetRoot_le_explicit_multiple hstart he2 hB₁, hnonreturn⟩
  · refine ⟨ndGeneralTargetRoot r k₂,
      (hk₁.trans hk₂).trans_le (generalTargetRoot_ge_index r k₂),
      generalTargetRoot_odd r k₂ (by omega),
      generalTargetRoot_reaches hstart (by omega), hres (X + 2),
      generalTargetRoot_le_explicit_multiple hstart he2 hB₂, hnonreturn⟩

#print axioms exists_generalTargetRoot_start_bounded
#print axioms generalTargetRoot_le_explicit_multiple
#print axioms generalTargetRoot_strictMono
#print axioms exists_bounded_nonreturning_predecessor_in_residue

end CollatzCanonical.BoundedInverseSeed
