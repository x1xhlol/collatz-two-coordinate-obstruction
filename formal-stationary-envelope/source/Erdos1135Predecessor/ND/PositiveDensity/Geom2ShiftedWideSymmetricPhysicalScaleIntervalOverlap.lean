/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.ND.PositiveDensity.Geom2ShiftedWideSymmetricRegenerativeState

namespace Erdos1135Predecessor

namespace ND

namespace PositiveDensity

noncomputable section

noncomputable def ndGeom2ShiftedWideSymmetricPhysicalLowerScale
    (b a root : ℕ) : ℝ :=
  ((2 ^ a * 4 ^ b * root : ℕ) : ℝ) /
    ((4 * 2 ^ ndGeom2ShiftedWideSymmetricShiftRadius b * 3 ^ b : ℕ) : ℝ)

noncomputable def ndGeom2ShiftedWideSymmetricPhysicalIntervalMin
    (b root : ℕ) : ℝ :=
  ndGeom2ShiftedWideSymmetricPhysicalLowerScale b 0 root

noncomputable def ndGeom2ShiftedWideSymmetricPhysicalIntervalMax
    (b root : ℕ) : ℝ :=
  ndGeom2ShiftedWideSymmetricPhysicalLowerScale b
    (2 * ndGeom2ShiftedWideSymmetricShiftRadius b) root

theorem ndGeom2ShiftedWideSymmetricPhysicalLowerScale_succ
    (b a root : ℕ) :
    ndGeom2ShiftedWideSymmetricPhysicalLowerScale b (a + 1) root =
      2 * ndGeom2ShiftedWideSymmetricPhysicalLowerScale b a root := by
  unfold ndGeom2ShiftedWideSymmetricPhysicalLowerScale
  norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
  rw [pow_add, pow_one]
  ring

theorem exists_ndGeom2ShiftedWideSymmetricPhysicalLowerScale_mem_twoMul
    {b root : ℕ} {X : ℝ} (hX : 0 < X)
    (hmin : ndGeom2ShiftedWideSymmetricPhysicalIntervalMin b root ≤ X)
    (hmax : X ≤ ndGeom2ShiftedWideSymmetricPhysicalIntervalMax b root) :
    ∃ a ∈ ndGeom2ShiftedWideSymmetricShiftIndices b,
      X ≤ ndGeom2ShiftedWideSymmetricPhysicalLowerScale b a root ∧
        ndGeom2ShiftedWideSymmetricPhysicalLowerScale b a root < 2 * X := by
  let r := ndGeom2ShiftedWideSymmetricShiftRadius b
  let P : ℕ → Prop := fun a =>
    a ≤ 2 * r ∧ X ≤ ndGeom2ShiftedWideSymmetricPhysicalLowerScale b a root
  have hex : ∃ a, P a := by
    refine ⟨2 * r, le_rfl, ?_⟩
    simpa only [P, r, ndGeom2ShiftedWideSymmetricPhysicalIntervalMax] using hmax
  let a := Nat.find hex
  have ha : P a := Nat.find_spec hex
  refine ⟨a, ?_, ha.2, ?_⟩
  · unfold ndGeom2ShiftedWideSymmetricShiftIndices
    exact Finset.mem_Icc.mpr ⟨Nat.zero_le a, ha.1⟩
  · by_cases ha0 : a = 0
    · have hXlt : X < 2 * X := by linarith
      simpa only [a, ha0,
        ndGeom2ShiftedWideSymmetricPhysicalIntervalMin] using
          hmin.trans_lt hXlt
    · have hapos : 0 < a := Nat.pos_of_ne_zero ha0
      have hprevlt : a - 1 < a := by omega
      have hnot : ¬P (a - 1) := Nat.find_min hex hprevlt
      have hprevBound : a - 1 ≤ 2 * r := by omega
      have hprevNot :
          ¬X ≤ ndGeom2ShiftedWideSymmetricPhysicalLowerScale b (a - 1) root :=
        fun hprev => hnot ⟨hprevBound, hprev⟩
      have hprevLt :
          ndGeom2ShiftedWideSymmetricPhysicalLowerScale b (a - 1) root < X :=
        lt_of_not_ge hprevNot
      have haEq : a = (a - 1) + 1 := by omega
      rw [haEq,
        ndGeom2ShiftedWideSymmetricPhysicalLowerScale_succ]
      linarith

theorem two_pow_nineteen_mul_div_twelve_le_three_pow (m : ℕ) :
    2 ^ ((19 * m) / 12) ≤ 3 ^ m := by
  let q := m / 12
  let r := m % 12
  have hr : r < 12 := by
    dsimp only [r]
    exact Nat.mod_lt _ (by norm_num)
  have hm : m = 12 * q + r := by
    dsimp only [q, r]
    omega
  have hblocks : 2 ^ (19 * q) ≤ 3 ^ (12 * q) := by
    calc
      2 ^ (19 * q) = (2 ^ 19) ^ q := pow_mul 2 19 q
      _ ≤ (3 ^ 12) ^ q :=
        Nat.pow_le_pow_left (by norm_num) q
      _ = 3 ^ (12 * q) := (pow_mul 3 12 q).symm
  have hremainder : 2 ^ ((19 * r) / 12) ≤ 3 ^ r := by
    interval_cases r <;> norm_num
  calc
    2 ^ ((19 * m) / 12) =
        2 ^ (19 * q + (19 * r) / 12) := by
      congr 1
      omega
    _ = 2 ^ (19 * q) * 2 ^ ((19 * r) / 12) := by rw [pow_add]
    _ ≤ 3 ^ (12 * q) * 3 ^ r := Nat.mul_le_mul hblocks hremainder
    _ = 3 ^ (12 * q + r) := by rw [pow_add]
    _ = 3 ^ m := by rw [hm]

theorem nineteen_mul_div_twelve_le_ndBalancedTotal (m : ℕ) :
    (19 * m) / 12 ≤ ndBalancedTotal m := by
  have hmono := Nat.clog_monotone 2
    (two_pow_nineteen_mul_div_twelve_le_three_pow m)
  rw [Nat.clog_pow 2 ((19 * m) / 12) (by norm_num)] at hmono
  exact hmono

theorem three_pow_le_two_pow_twentySeven_mul_add_sixteen_div_seventeen
    (m : ℕ) :
    3 ^ m ≤ 2 ^ ((27 * m + 16) / 17) := by
  let q := m / 17
  let r := m % 17
  have hr : r < 17 := by
    dsimp only [r]
    exact Nat.mod_lt _ (by norm_num)
  have hm : m = 17 * q + r := by
    dsimp only [q, r]
    omega
  have hblocks : 3 ^ (17 * q) ≤ 2 ^ (27 * q) := by
    calc
      3 ^ (17 * q) = (3 ^ 17) ^ q := pow_mul 3 17 q
      _ ≤ (2 ^ 27) ^ q :=
        Nat.pow_le_pow_left (by norm_num) q
      _ = 2 ^ (27 * q) := (pow_mul 2 27 q).symm
  have hremainder : 3 ^ r ≤ 2 ^ ((27 * r + 16) / 17) := by
    interval_cases r <;> norm_num
  calc
    3 ^ m = 3 ^ (17 * q + r) := by rw [hm]
    _ = 3 ^ (17 * q) * 3 ^ r := by rw [pow_add]
    _ ≤ 2 ^ (27 * q) * 2 ^ ((27 * r + 16) / 17) :=
      Nat.mul_le_mul hblocks hremainder
    _ = 2 ^ (27 * q + (27 * r + 16) / 17) := by rw [pow_add]
    _ = 2 ^ ((27 * m + 16) / 17) := by
      congr 1
      omega

theorem seventeen_mul_ndBalancedTotal_le_twentySeven_mul_add_sixteen
    (m : ℕ) :
    17 * ndBalancedTotal m ≤ 27 * m + 16 := by
  have htotal : ndBalancedTotal m ≤ (27 * m + 16) / 17 := by
    apply Nat.clog_le_of_le_pow
    exact
      three_pow_le_two_pow_twentySeven_mul_add_sixteen_div_seventeen m
  omega

theorem oneHundredNinetyThree_mul_base_le_eightHundredFifty_mul_shiftRadius_add
    {b : ℕ} (hb : 200 ≤ b) :
    193 * b ≤
      850 * ndGeom2ShiftedWideSymmetricShiftRadius b + 1080 := by
  let w := ndGeom2ShiftedWideSymmetricWidth b
  let m := ndGeom2ShiftedWideSymmetricMarginNat b
  let c := ndBalancedTotal w
  let r := ndGeom2ShiftedWideSymmetricShiftRadius b
  have hc : 17 * c ≤ 27 * w + 16 := by
    simpa only [c] using
      seventeen_mul_ndBalancedTotal_le_twentySeven_mul_add_sixteen w
  have hgap :
      ndGeom2ShiftedWideSymmetricGap b + c = 2 * w := by
    dsimp only [c, w]
    unfold ndGeom2ShiftedWideSymmetricGap
    exact Nat.sub_add_cancel
      (ndBalancedTotal_le_two_mul
        (ndGeom2ShiftedWideSymmetricWidth b))
  have hr : r + 2 * m = ndGeom2ShiftedWideSymmetricGap b := by
    simpa only [r, m] using
      ndGeom2ShiftedWideSymmetricShiftRadius_add_two_margin hb
  have hw : 3 * b ≤ 5 * w + 4 := by
    dsimp only [w]
    unfold ndGeom2ShiftedWideSymmetricWidth
    omega
  have hm : 100 * m ≤ b := by
    dsimp only [m]
    unfold ndGeom2ShiftedWideSymmetricMarginNat
    omega
  dsimp only [w, m, c, r] at hc hgap hr hw hm ⊢
  omega

theorem ndGeom2ShiftedWideSymmetric_intervalOverlap_exponent
    {b b' K : ℕ} (hb : 600 ≤ b) (hb' : 200 ≤ b')
    (hK : K ≤ b / 200)
    (hbase : (19 * b) / 12 + 4 * b' < K + 6 * b + 5) :
    K + 1 + 2 * b' <
      ndGeom2ShiftedWideSymmetricShiftRadius b +
        ndGeom2ShiftedWideSymmetricShiftRadius b' +
          (19 * b') / 12 := by
  have hr :=
    oneHundredNinetyThree_mul_base_le_eightHundredFifty_mul_shiftRadius_add
      (show 200 ≤ b by omega)
  have hr' :=
    oneHundredNinetyThree_mul_base_le_eightHundredFifty_mul_shiftRadius_add
      hb'
  have hround : 19 * b ≤ 12 * ((19 * b) / 12) + 11 := by omega
  have hround' : 19 * b' ≤ 12 * ((19 * b') / 12) + 11 := by omega
  have hKmul : 200 * K ≤ b := by omega
  omega

end

end PositiveDensity

end ND

end Erdos1135Predecessor
