import TrapBlackCriterion
import TrapReducedModulus
import TrapCarryIdentities

/-!
Arithmetic extracted from literal native black triangles at integer heights.
The finite-family endpoint chooses the integer carries and records the exact
modulus factors, primitive numerators and triangle bounds. It makes no
asymptotic assertion about the resulting data.
-/

set_option autoImplicit false

namespace Erdos1135.Tao

def trapReducedModulus (n : ℕ) (p : TaoSection7Point) : ℕ :=
  3 ^ (n - 2 * ((p.j : ℕ) - 1))

theorem trapReducedModulus_pos (n : ℕ) (p : TaoSection7Point) :
    0 < trapReducedModulus n p := by
  unfold trapReducedModulus
  positivity

theorem integerHeightTrap_black_iff_numerator_bound (n : ℕ) (xi : ZMod (3 ^ n))
    (p : TaoSection7Point) (h : ℕ) (hp : 2 * ((p.j : ℕ) - 1) ≤ n)
    {epsilon : ℝ} (hepsilon : epsilon < 1 / 4) :
    (integerHeightTrap p h).BlackOn (taoSection7SourceBlackPoint n xi epsilon) ↔
      |(trapReducedNumerator n xi p : ℝ)| ≤
        epsilon * (trapReducedModulus n p : ℝ) / (2 : ℝ) ^ h := by
  rw [integerHeightTrap_black_iff_top_small n xi p h hepsilon,
    sourceTheta_eq_trapReducedNumerator n xi p hp, abs_div,
    abs_of_pos (by positivity : (0 : ℝ) < 3 ^ (n - 2 * ((p.j : ℕ) - 1))),
    div_le_iff₀ (by positivity : (0 : ℝ) < 3 ^ (n - 2 * ((p.j : ℕ) - 1)))]
  have heq : epsilon / (2 : ℝ) ^ h * 3 ^ (n - 2 * ((p.j : ℕ) - 1)) =
      epsilon * (trapReducedModulus n p : ℝ) / (2 : ℝ) ^ h := by
    simp only [trapReducedModulus, Nat.cast_pow, Nat.cast_ofNat]
    ring
  rw [heq]

theorem trapReducedModulus_eq_nine_pow_mul (n m : ℕ) (p q : TaoSection7Point)
    (hj : (q.j : ℕ) = (p.j : ℕ) + m)
    (hq : 2 * ((q.j : ℕ) - 1) ≤ n) :
    trapReducedModulus n p = 9 ^ m * trapReducedModulus n q := by
  have hp0 := p.j.pos
  have hexp : n - 2 * ((p.j : ℕ) - 1) =
      2 * m + (n - 2 * ((q.j : ℕ) - 1)) := by omega
  unfold trapReducedModulus
  rw [hexp, pow_add, pow_mul]
  norm_num

theorem exists_trapReducedNumerator_carry (n : ℕ) (xi : ZMod (3 ^ n))
    (p q : TaoSection7Point) (hj : (p.j : ℕ) ≤ q.j) (hl : p.l ≤ q.l) :
    ∃ z : ℤ, trapReducedNumerator n xi p =
      (2 : ℤ) ^ (q.l - p.l).toNat * trapReducedNumerator n xi q -
        z * (trapReducedModulus n q : ℤ) := by
  exact CollatzResearch.exists_trap_carry_of_modEq _
    (trapReducedNumerator_common_frequency n xi p q hj hl)

/-- A finite chain of native black triangles supplies the actual arithmetic
data used by the carry and entropy arguments. -/
theorem exists_native_trap_arithmetic (n r : ℕ) (xi : ZMod (3 ^ n))
    (hxi : zmodThreePrimitive n xi) (p : ℕ → TaoSection7Point)
    (h m : ℕ → ℕ) {epsilon : ℝ} (hepsilon : epsilon < 1 / 4)
    (hstrip : ∀ i ≤ r, 2 * (((p i).j : ℕ) - 1) < n)
    (hj : ∀ i < r, ((p (i + 1)).j : ℕ) = ((p i).j : ℕ) + m i)
    (hl : ∀ i < r, (p i).l ≤ (p (i + 1)).l)
    (hblack : ∀ i ≤ r,
      (integerHeightTrap (p i) (h i)).BlackOn (taoSection7SourceBlackPoint n xi epsilon)) :
    ∃ z : ℕ → ℤ,
      (∀ i < r, trapReducedNumerator n xi (p i) =
        (2 : ℤ) ^ ((p (i + 1)).l - (p i).l).toNat *
          trapReducedNumerator n xi (p (i + 1)) -
            z i * (trapReducedModulus n (p (i + 1)) : ℤ)) ∧
      (∀ i ≤ r, trapReducedNumerator n xi (p i) ≠ 0 ∧
        ¬ (3 : ℤ) ∣ trapReducedNumerator n xi (p i)) ∧
      (∀ i ≤ r, 0 < trapReducedModulus n (p i)) ∧
      (∀ i ≤ r, |(trapReducedNumerator n xi (p i) : ℝ)| ≤
        epsilon * (trapReducedModulus n (p i) : ℝ) / (2 : ℝ) ^ h i) ∧
      (∀ i < r, trapReducedModulus n (p i) =
        9 ^ m i * trapReducedModulus n (p (i + 1))) := by
  classical
  have hc : ∀ i, ∃ z : ℤ, i < r → trapReducedNumerator n xi (p i) =
      (2 : ℤ) ^ ((p (i + 1)).l - (p i).l).toNat *
        trapReducedNumerator n xi (p (i + 1)) -
          z * (trapReducedModulus n (p (i + 1)) : ℤ) := by
    intro i
    by_cases hi : i < r
    · obtain ⟨z, hz⟩ := exists_trapReducedNumerator_carry n xi (p i) (p (i + 1))
        (by have := hj i hi; omega) (hl i hi)
      exact ⟨z, fun _ => hz⟩
    · exact ⟨0, fun hir => (hi hir).elim⟩
  choose z hz using hc
  refine ⟨z, hz, ?_, ?_, ?_, ?_⟩
  · intro i hi
    exact ⟨trapReducedNumerator_ne_zero hxi (p i) (hstrip i hi),
      three_not_dvd_trapReducedNumerator hxi (p i) (hstrip i hi)⟩
  · intro i _
    exact trapReducedModulus_pos n (p i)
  · intro i hi
    exact (integerHeightTrap_black_iff_numerator_bound n xi (p i) (h i)
      (hstrip i hi).le hepsilon).mp (hblack i hi)
  · intro i hi
    exact trapReducedModulus_eq_nine_pow_mul n (m i) (p i) (p (i + 1)) (hj i hi)
      (hstrip (i + 1) (by omega)).le

end Erdos1135.Tao

#print axioms Erdos1135.Tao.integerHeightTrap_black_iff_numerator_bound
#print axioms Erdos1135.Tao.trapReducedModulus_eq_nine_pow_mul
#print axioms Erdos1135.Tao.exists_trapReducedNumerator_carry
#print axioms Erdos1135.Tao.exists_native_trap_arithmetic
