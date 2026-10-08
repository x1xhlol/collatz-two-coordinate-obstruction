import Erdos1135.Tao.Renewal.HoldPoint
import Mathlib.Tactic

/-!
# Outer `(7.36)` Source Algebra

This module records the elementary algebra bridge used in Tao Section 7.4 when
turning a pointwise `(7.37)`-shaped gap decay into a polynomial moment in the
first Hold coordinate `j`.

It does not prove pointwise decay `(7.37)`, the first-coordinate Hold law,
Geom(4) moments, outer decay `(7.36)`, Proposition 7.8, or Tao's theorem.
-/

namespace Erdos1135
namespace Tao

namespace TaoSection7Outer736

/--
Elementary product domination for positive natural factors.

This helper keeps the later gap algebra over `Nat`, avoiding a brittle real
division argument before the final cast.
-/
theorem nat_add_sub_one_le_mul {a b : ℕ}
    (ha : 1 ≤ a) (hb : 1 ≤ b) :
    a + b - 1 ≤ a * b := by
  have hnonneg : 0 ≤ (a - 1 : ℤ) * (b - 1 : ℤ) :=
    mul_nonneg (by omega) (by omega)
  have hidentity :
      (a : ℤ) * (b : ℤ) =
        (a : ℤ) + (b : ℤ) - 1 + (a - 1 : ℤ) * (b - 1 : ℤ) := by
    ring
  have hcast : ((a + b - 1 : ℕ) : ℤ) = (a : ℤ) + (b : ℤ) - 1 := by
    omega
  have hleZ : ((a + b - 1 : ℕ) : ℤ) ≤ ((a * b : ℕ) : ℤ) := by
    rw [hcast]
    norm_num
    nlinarith
  omega

/--
Natural-number core behind Tao's source algebra near `(7.36)`.

The harmless constant `8` is intentionally not optimized; it cleanly covers
both the `j < n / 2` and `j >= n / 2` branches.
-/
theorem nat_le_eight_mul_pnat_mul_outerGap
    (n : ℕ) (j : ℕ+) :
    n ≤ 8 * (j : ℕ) * max (n / 2 - (j : ℕ)) 1 := by
  have hjpos : 1 ≤ (j : ℕ) := j.2
  by_cases hj : (j : ℕ) < n / 2
  · have hgap_pos : 1 ≤ n / 2 - (j : ℕ) := by
      omega
    rw [max_eq_left hgap_pos]
    have hprod : n / 2 - 1 ≤ (j : ℕ) * (n / 2 - (j : ℕ)) := by
      have hsum :
          (j : ℕ) + (n / 2 - (j : ℕ)) - 1 ≤
            (j : ℕ) * (n / 2 - (j : ℕ)) :=
        nat_add_sub_one_le_mul hjpos hgap_pos
      omega
    have hn_gap : n ≤ 8 * (n / 2 - 1) := by
      omega
    have hmul :
        8 * (n / 2 - 1) ≤ 8 * ((j : ℕ) * (n / 2 - (j : ℕ))) :=
      Nat.mul_le_mul_left 8 hprod
    exact le_trans hn_gap (by simpa [Nat.mul_assoc] using hmul)
  · have hgap_zero : n / 2 - (j : ℕ) = 0 := by
      omega
    rw [hgap_zero]
    norm_num
    have hn_floor : n ≤ 2 * (n / 2) + 1 := by
      omega
    have hfloor_j : n / 2 ≤ (j : ℕ) := by
      omega
    omega

/--
Source algebra for converting a pointwise inverse gap into a `j^A n^-A`
majorant.
-/
theorem gapInvPow_le_eightPow
    (A n : ℕ) (j : ℕ+) (hn : 0 < n) :
    (((max (n / 2 - (j : ℕ)) 1 : ℕ) : ℝ) ^ A)⁻¹ ≤
      ((8 : ℝ) ^ A) * (((j : ℕ) : ℝ) ^ A) * (((n : ℝ) ^ A)⁻¹) := by
  let M : ℕ := max (n / 2 - (j : ℕ)) 1
  have hMpos_nat : 0 < M := by
    dsimp [M]
    exact Nat.lt_of_lt_of_le Nat.zero_lt_one (le_max_right _ _)
  have hnR : (0 : ℝ) < n := by
    exact_mod_cast hn
  have hMR : (0 : ℝ) < M := by
    exact_mod_cast hMpos_nat
  have hcore_nat : n ≤ 8 * (j : ℕ) * M := by
    simpa [M] using nat_le_eight_mul_pnat_mul_outerGap n j
  have hcoreR : (n : ℝ) ≤ (8 : ℝ) * ((j : ℕ) : ℝ) * (M : ℝ) := by
    exact_mod_cast hcore_nat
  have hbase :
      (M : ℝ)⁻¹ ≤ (8 : ℝ) * ((j : ℕ) : ℝ) * (n : ℝ)⁻¹ := by
    field_simp [hnR.ne', hMR.ne']
    nlinarith [hcoreR]
  have hpow := pow_le_pow_left₀ (inv_nonneg.mpr hMR.le) hbase A
  simpa [M, inv_pow, mul_pow, mul_assoc, mul_left_comm, mul_comm] using hpow

/--
Consumer form for the outer `(7.36)` route.

Given a pointwise `(7.37)`-style decay in the distance from `n / 2`, this
rewrites it to the polynomial moment shape consumed by later Hold/Geom4
expectation steps.
-/
theorem sourceAlgebra_to_jPolynomial
    {Q : TaoSection7RenewalPoint → ℝ} {C : ℝ} {A n : ℕ}
    (hn : 0 < n) (hC0 : 0 ≤ C)
    (hpoint : ∀ h : TaoSection7RenewalPoint,
      Q h ≤ C * ((((max (n / 2 - (h.j : ℕ)) 1 : ℕ) : ℝ) ^ A)⁻¹)) :
    ∀ h : TaoSection7RenewalPoint,
      Q h ≤
        (C * ((8 : ℝ) ^ A) * (((n : ℝ) ^ A)⁻¹)) *
          (((h.j : ℕ) : ℝ) ^ A) := by
  intro h
  have halg := gapInvPow_le_eightPow A n h.j hn
  calc
    Q h ≤ C * ((((max (n / 2 - (h.j : ℕ)) 1 : ℕ) : ℝ) ^ A)⁻¹) :=
      hpoint h
    _ ≤ C * (((8 : ℝ) ^ A) * (((h.j : ℕ) : ℝ) ^ A) *
          (((n : ℝ) ^ A)⁻¹)) :=
      mul_le_mul_of_nonneg_left halg hC0
    _ = (C * ((8 : ℝ) ^ A) * (((n : ℝ) ^ A)⁻¹)) *
          (((h.j : ℕ) : ℝ) ^ A) := by
      ring

end TaoSection7Outer736

end Tao
end Erdos1135
