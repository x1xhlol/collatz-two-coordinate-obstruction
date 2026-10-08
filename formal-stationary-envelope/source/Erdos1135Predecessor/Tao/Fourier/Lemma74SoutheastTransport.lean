/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Fourier.Lemma74ThetaArithmetic

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

namespace TaoSection7Point

theorem ext' {p q : TaoSection7Point}
    (hj : p.j = q.j) (hl : p.l = q.l) : p = q := by
  cases p
  cases q
  cases hj
  cases hl
  rfl

def rightN (p : TaoSection7Point) : ℕ → TaoSection7Point
  | 0 => p
  | h + 1 => (rightN p h).right

def downN (p : TaoSection7Point) (v : ℕ) : TaoSection7Point :=
  ⟨p.j, p.l - v⟩

@[simp] theorem rightN_zero (p : TaoSection7Point) : p.rightN 0 = p := by
  rfl

@[simp] theorem downN_zero (p : TaoSection7Point) : p.downN 0 = p := by
  cases p
  simp [downN]

theorem rightN_succ (p : TaoSection7Point) (h : ℕ) :
    p.rightN (h + 1) = (p.rightN h).right := by
  rfl

theorem downN_succ (p : TaoSection7Point) (v : ℕ) :
    p.downN (v + 1) = (p.downN v).down := by
  cases p
  simp [downN, down]
  omega

@[simp] theorem rightN_j (p : TaoSection7Point) (h : ℕ) :
    ((p.rightN h).j : ℕ) = (p.j : ℕ) + h :=
  by
    induction h with
    | zero => simp
    | succ h ih => simp [rightN_succ, ih, Nat.add_assoc]

@[simp] theorem rightN_l (p : TaoSection7Point) (h : ℕ) :
    (p.rightN h).l = p.l :=
  by
    induction h with
    | zero => simp
    | succ h ih => simp [rightN_succ, ih]

@[simp] theorem downN_j (p : TaoSection7Point) (v : ℕ) :
    (p.downN v).j = p.j :=
  rfl

end TaoSection7Point

theorem taoSection7ThetaResidue_rightN
    (n : ℕ) (xi : ZMod (3 ^ n)) (p : TaoSection7Point) (h : ℕ) :
    taoSection7ThetaResidue n xi (p.rightN h).j (p.rightN h).l =
      (9 : ZMod (3 ^ n)) ^ h *
        taoSection7ThetaResidue n xi p.j p.l := by
  induction h with
  | zero => simp
  | succ h ih =>
      rw [show h + 1 = Nat.succ h by omega,
        TaoSection7Point.rightN_succ]
      rw [taoSection7ThetaResidue_right, ih, pow_succ]
      ring

theorem taoSection7ThetaResidue_downN
    (n : ℕ) (xi : ZMod (3 ^ n)) (p : TaoSection7Point) (v : ℕ) :
    taoSection7ThetaResidue n xi (p.downN v).j (p.downN v).l =
      (2 : ZMod (3 ^ n)) ^ v *
        taoSection7ThetaResidue n xi p.j p.l := by
  induction v with
  | zero => simp
  | succ v ih =>
      rw [show v + 1 = Nat.succ v by omega,
        TaoSection7Point.downN_succ]
      rw [taoSection7ThetaResidue_down, ih, pow_succ]
      ring

def taoSection7SoutheastH (a q : TaoSection7Point) : ℕ :=
  (q.j : ℕ) - (a.j : ℕ)

def taoSection7SoutheastV (a q : TaoSection7Point) : ℕ :=
  (a.l - q.l).toNat

theorem taoSection7SoutheastV_intCast
    (a q : TaoSection7Point) (hl : q.l ≤ a.l) :
    (taoSection7SoutheastV a q : ℤ) = a.l - q.l := by
  exact Int.toNat_of_nonneg (sub_nonneg.mpr hl)

def taoSection7SoutheastMultiplier (a q : TaoSection7Point) : ℕ :=
  9 ^ taoSection7SoutheastH a q * 2 ^ taoSection7SoutheastV a q

def taoSection7SoutheastWeight (a q : TaoSection7Point) : ℝ :=
  (taoSection7SoutheastH a q : ℝ) * Real.log 9 +
    (taoSection7SoutheastV a q : ℝ) * Real.log 2

theorem taoSection7Point_eq_downN_rightN
    (a q : TaoSection7Point)
    (hj : (a.j : ℕ) ≤ (q.j : ℕ)) (hl : q.l ≤ a.l) :
    q = (a.rightN (taoSection7SoutheastH a q)).downN
      (taoSection7SoutheastV a q) := by
  apply TaoSection7Point.ext'
  · rw [TaoSection7Point.downN_j]
    apply Subtype.ext
    change (q.j : ℕ) = ((a.rightN (taoSection7SoutheastH a q)).j : ℕ)
    rw [TaoSection7Point.rightN_j]
    change (q.j : ℕ) = (a.j : ℕ) + ((q.j : ℕ) - (a.j : ℕ))
    omega
  · simp [taoSection7SoutheastV, TaoSection7Point.downN,
      Int.toNat_of_nonneg (sub_nonneg.mpr hl)]

@[simp] theorem taoSection7SoutheastH_downN_rightN
    (a : TaoSection7Point) (h v : ℕ) :
    taoSection7SoutheastH a ((a.rightN h).downN v) = h := by
  simp [taoSection7SoutheastH]

@[simp] theorem taoSection7SoutheastV_downN_rightN
    (a : TaoSection7Point) (h v : ℕ) :
    taoSection7SoutheastV a ((a.rightN h).downN v) = v := by
  simp [taoSection7SoutheastV, TaoSection7Point.downN]

theorem taoSection7ThetaResidue_southeast
    (n : ℕ) (xi : ZMod (3 ^ n)) (a q : TaoSection7Point)
    (hj : (a.j : ℕ) ≤ (q.j : ℕ)) (hl : q.l ≤ a.l) :
    taoSection7ThetaResidue n xi q.j q.l =
      (taoSection7SoutheastMultiplier a q : ZMod (3 ^ n)) *
        taoSection7ThetaResidue n xi a.j a.l := by
  rw [taoSection7Point_eq_downN_rightN a q hj hl]
  rw [taoSection7ThetaResidue_downN, taoSection7ThetaResidue_rightN]
  simp only [taoSection7SoutheastMultiplier,
    taoSection7SoutheastH_downN_rightN,
    taoSection7SoutheastV_downN_rightN, Nat.cast_mul, Nat.cast_pow]
  ring

theorem natCast_taoSection7SoutheastMultiplier_eq_exp_weight
    (a q : TaoSection7Point) :
    (taoSection7SoutheastMultiplier a q : ℝ) =
      Real.exp (taoSection7SoutheastWeight a q) := by
  unfold taoSection7SoutheastMultiplier taoSection7SoutheastWeight
  rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Real.exp_add]
  rw [Real.exp_nat_mul, Real.exp_nat_mul]
  rw [Real.exp_log (by norm_num : (0 : ℝ) < 9),
    Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  norm_num

theorem abs_taoSection7SourceTheta_southeast_le
    (n : ℕ) (xi : ZMod (3 ^ n)) (a q : TaoSection7Point)
    (hj : (a.j : ℕ) ≤ (q.j : ℕ)) (hl : q.l ≤ a.l) :
    |taoSection7SourceTheta n xi q| ≤
      Real.exp (taoSection7SoutheastWeight a q) *
        |taoSection7SourceTheta n xi a| := by
  unfold taoSection7SourceTheta
  rw [taoSection7ThetaResidue_southeast n xi a q hj hl]
  rw [← natCast_taoSection7SoutheastMultiplier_eq_exp_weight]
  exact abs_taoSignedTheta_natCast_mul_le
    (taoSection7SoutheastMultiplier a q)
    (taoSection7ThetaResidue n xi a.j a.l)

theorem taoSection7SourceTheta_southeast_of_abs_lt_half
    (n : ℕ) (xi : ZMod (3 ^ n)) (a q : TaoSection7Point)
    (hj : (a.j : ℕ) ≤ (q.j : ℕ)) (hl : q.l ≤ a.l)
    (hguard :
      |Real.exp (taoSection7SoutheastWeight a q) *
        taoSection7SourceTheta n xi a| < (1 / 2 : ℝ)) :
    taoSection7SourceTheta n xi q =
      Real.exp (taoSection7SoutheastWeight a q) *
        taoSection7SourceTheta n xi a := by
  unfold taoSection7SourceTheta at hguard ⊢
  rw [taoSection7ThetaResidue_southeast n xi a q hj hl]
  rw [← natCast_taoSection7SoutheastMultiplier_eq_exp_weight] at hguard ⊢
  simpa using taoSignedTheta_int_mul_of_abs_lt_half
    (taoSection7SoutheastMultiplier a q : ℤ)
    (taoSection7ThetaResidue n xi a.j a.l) hguard

theorem abs_taoSection7SourceTheta_southeast_eq_of_lt_half
    (n : ℕ) (xi : ZMod (3 ^ n)) (a q : TaoSection7Point)
    (hj : (a.j : ℕ) ≤ (q.j : ℕ)) (hl : q.l ≤ a.l)
    (hguard :
      Real.exp (taoSection7SoutheastWeight a q) *
        |taoSection7SourceTheta n xi a| < (1 / 2 : ℝ)) :
    |taoSection7SourceTheta n xi q| =
      Real.exp (taoSection7SoutheastWeight a q) *
        |taoSection7SourceTheta n xi a| := by
  have hsigned := taoSection7SourceTheta_southeast_of_abs_lt_half
    n xi a q hj hl (by
      simpa [abs_mul, abs_of_pos (Real.exp_pos _)] using hguard)
  rw [hsigned, abs_mul, abs_of_pos (Real.exp_pos _)]

end

end Tao

end Erdos1135Predecessor
