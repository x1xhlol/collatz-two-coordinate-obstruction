/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Fourier.Section7SourcePredicates

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

noncomputable def taoSection7SourceTheta
    (n : ℕ) (xi : ZMod (3 ^ n)) (p : TaoSection7Point) : ℝ :=
  taoSignedTheta (taoSection7ThetaResidue n xi p.j p.l)

theorem taoSection7SourceBlackPoint_iff_geometryBlack
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (p : TaoSection7Point) :
    taoSection7SourceBlackPoint n xi epsilon p ↔
      TaoSection7Black epsilon (taoSection7SourceTheta n xi) p := by
  rfl

theorem taoSection7SourceWhitePoint_iff_not_geometryBlack
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ)
    (p : TaoSection7Point) :
    taoSection7SourceWhitePoint n xi epsilon p ↔
      ¬ TaoSection7Black epsilon (taoSection7SourceTheta n xi) p := by
  exact taoSection7White_iff_not_black epsilon
    (taoSection7ThetaResidue n xi p.j p.l)

theorem taoSection7SourceBlackInDomain_geometryBlack
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {p : TaoSection7Point}
    (hp : taoSection7SourceBlackInDomain n xi epsilon J p) :
    TaoSection7Black epsilon (taoSection7SourceTheta n xi) p := by
  exact (taoSection7SourceBlackPoint_iff_geometryBlack n xi epsilon p).1 hp.2

theorem taoSection7ThetaResidue_right
    (n : ℕ) (xi : ZMod (3 ^ n)) (p : TaoSection7Point) :
    taoSection7ThetaResidue n xi p.right.j p.right.l =
      9 * taoSection7ThetaResidue n xi p.j p.l := by
  have hj : 0 < (p.j : ℕ) := p.j.pos
  have hexp :
      2 * (((p.j : ℕ) + 1) - 1) = 2 + 2 * ((p.j : ℕ) - 1) := by
    omega
  unfold taoSection7ThetaResidue
  simp only [TaoSection7Point.right_j, TaoSection7Point.right_l]
  rw [hexp, pow_add]
  norm_num
  ring

theorem taoSection7ThetaResidue_down
    (n : ℕ) (xi : ZMod (3 ^ n)) (p : TaoSection7Point) :
    taoSection7ThetaResidue n xi p.down.j p.down.l =
      2 * taoSection7ThetaResidue n xi p.j p.l := by
  have htwo := two_mul_taoSection7TwoZPow_neg n (p.l - 1)
  have hpow :
      taoSection7TwoZPow n (1 - (p.l - 1)) =
        2 * taoSection7TwoZPow n (1 - p.l) := by
    simpa [show -(p.l - 1) = 1 - p.l by ring] using htwo.symm
  unfold taoSection7ThetaResidue
  simp only [TaoSection7Point.down_j, TaoSection7Point.down_l]
  rw [hpow]
  ring

theorem taoSection7ThetaResidue_eq_right_sub_four_down
    (n : ℕ) (xi : ZMod (3 ^ n)) (p : TaoSection7Point) :
    taoSection7ThetaResidue n xi p.j p.l =
      taoSection7ThetaResidue n xi p.right.j p.right.l -
        4 * taoSection7ThetaResidue n xi p.down.j p.down.l := by
  rw [taoSection7ThetaResidue_right, taoSection7ThetaResidue_down]
  ring

theorem taoSection7ThetaResidue_eq_nine_mul_left
    (n : ℕ) (xi : ZMod (3 ^ n)) (p : TaoSection7Point)
    (h : 1 < (p.j : ℕ)) :
    taoSection7ThetaResidue n xi p.j p.l =
      9 * taoSection7ThetaResidue n xi (p.left h).j (p.left h).l := by
  have hj : 0 < (p.j : ℕ) := p.j.pos
  have hexp :
      2 * ((p.j : ℕ) - 1) =
        2 + 2 * (((p.j : ℕ) - 1) - 1) := by
    omega
  unfold taoSection7ThetaResidue
  simp only [TaoSection7Point.left]
  rw [hexp, pow_add]
  norm_num
  ring

theorem taoSignedTheta_eq_intRatio_of_intCast_eq_of_abs_lt_half
    {N : ℕ} [NeZero N] (z : ZMod N) (m : ℤ)
    (hcast : (m : ZMod N) = z)
    (habs : |(m : ℝ) / (N : ℝ)| < (1 / 2 : ℝ)) :
    taoSignedTheta z = (m : ℝ) / (N : ℝ) := by
  have hN : (0 : ℝ) < (N : ℝ) := by exact_mod_cast NeZero.pos N
  have hbounds := (abs_lt.mp habs)
  have hlreal : (-(N : ℝ)) < (m : ℝ) * 2 := by
    have h := (lt_div_iff₀ hN).mp hbounds.1
    nlinarith
  have hureal : (m : ℝ) * 2 < (N : ℝ) := by
    have h := (div_lt_iff₀ hN).mp hbounds.2
    nlinarith
  have hl : (-(N : ℤ)) < m * 2 := by exact_mod_cast hlreal
  have hu : m * 2 ≤ (N : ℤ) := by
    have : m * 2 < (N : ℤ) := by exact_mod_cast hureal
    omega
  have hm : z.valMinAbs = m :=
    (ZMod.valMinAbs_spec z m).2 ⟨hcast.symm, hl, hu⟩
  rw [taoSignedTheta, hm]

theorem taoSignedTheta_int_mul_of_abs_lt_half
    {N : ℕ} [NeZero N] (k : ℤ) (z : ZMod N)
    (habs : |(k : ℝ) * taoSignedTheta z| < (1 / 2 : ℝ)) :
    taoSignedTheta ((k : ZMod N) * z) =
      (k : ℝ) * taoSignedTheta z := by
  let m : ℤ := k * z.valMinAbs
  have hcast : (m : ZMod N) = (k : ZMod N) * z := by
    dsimp [m]
    rw [Int.cast_mul, ZMod.coe_valMinAbs]
  have hratio :
      (m : ℝ) / (N : ℝ) = (k : ℝ) * taoSignedTheta z := by
    dsimp [m, taoSignedTheta]
    push_cast
    ring
  rw [taoSignedTheta_eq_intRatio_of_intCast_eq_of_abs_lt_half
    ((k : ZMod N) * z) m hcast (by simpa [hratio] using habs), hratio]

theorem taoSignedTheta_eq_right_sub_four_down_of_abs_lt_half
    {N : ℕ} [NeZero N] (z zRight zDown : ZMod N)
    (hresidue : z = zRight - 4 * zDown)
    (habs :
      |taoSignedTheta zRight - 4 * taoSignedTheta zDown| <
        (1 / 2 : ℝ)) :
    taoSignedTheta z =
      taoSignedTheta zRight - 4 * taoSignedTheta zDown := by
  let m : ℤ := zRight.valMinAbs - 4 * zDown.valMinAbs
  have hcast : (m : ZMod N) = z := by
    dsimp [m]
    rw [Int.cast_sub, Int.cast_mul, ZMod.coe_valMinAbs,
      ZMod.coe_valMinAbs, hresidue]
    norm_num
  have hratio :
      (m : ℝ) / (N : ℝ) =
        taoSignedTheta zRight - 4 * taoSignedTheta zDown := by
    dsimp [m, taoSignedTheta]
    push_cast
    ring
  rw [taoSignedTheta_eq_intRatio_of_intCast_eq_of_abs_lt_half
    z m hcast (by simpa [hratio] using habs), hratio]

theorem taoSection7SourceTheta_right_of_abs_lt_half
    (n : ℕ) (xi : ZMod (3 ^ n)) (p : TaoSection7Point)
    (habs : |9 * taoSection7SourceTheta n xi p| < (1 / 2 : ℝ)) :
    taoSection7SourceTheta n xi p.right =
      9 * taoSection7SourceTheta n xi p := by
  unfold taoSection7SourceTheta
  rw [taoSection7ThetaResidue_right]
  simpa using taoSignedTheta_int_mul_of_abs_lt_half
    (N := 3 ^ n) 9 (taoSection7ThetaResidue n xi p.j p.l) habs

theorem taoSection7SourceTheta_down_of_abs_lt_half
    (n : ℕ) (xi : ZMod (3 ^ n)) (p : TaoSection7Point)
    (habs : |2 * taoSection7SourceTheta n xi p| < (1 / 2 : ℝ)) :
    taoSection7SourceTheta n xi p.down =
      2 * taoSection7SourceTheta n xi p := by
  unfold taoSection7SourceTheta
  rw [taoSection7ThetaResidue_down]
  simpa using taoSignedTheta_int_mul_of_abs_lt_half
    (N := 3 ^ n) 2 (taoSection7ThetaResidue n xi p.j p.l) habs

theorem taoSection7SourceTheta_eq_right_sub_four_down_of_abs_lt_half
    (n : ℕ) (xi : ZMod (3 ^ n)) (p : TaoSection7Point)
    (habs :
      |taoSection7SourceTheta n xi p.right -
          4 * taoSection7SourceTheta n xi p.down| < (1 / 2 : ℝ)) :
    taoSection7SourceTheta n xi p =
      taoSection7SourceTheta n xi p.right -
        4 * taoSection7SourceTheta n xi p.down := by
  unfold taoSection7SourceTheta at habs ⊢
  exact taoSignedTheta_eq_right_sub_four_down_of_abs_lt_half
    (taoSection7ThetaResidue n xi p.j p.l)
    (taoSection7ThetaResidue n xi p.right.j p.right.l)
    (taoSection7ThetaResidue n xi p.down.j p.down.l)
    (taoSection7ThetaResidue_eq_right_sub_four_down n xi p) habs

theorem taoSection7SourceTheta_eq_nine_mul_left_of_abs_lt_half
    (n : ℕ) (xi : ZMod (3 ^ n)) (p : TaoSection7Point)
    (h : 1 < (p.j : ℕ))
    (habs : |9 * taoSection7SourceTheta n xi (p.left h)| < (1 / 2 : ℝ)) :
    taoSection7SourceTheta n xi p =
      9 * taoSection7SourceTheta n xi (p.left h) := by
  unfold taoSection7SourceTheta
  rw [taoSection7ThetaResidue_eq_nine_mul_left n xi p h]
  simpa using taoSignedTheta_int_mul_of_abs_lt_half
    (N := 3 ^ n) 9
    (taoSection7ThetaResidue n xi (p.left h).j (p.left h).l) habs

theorem taoSection7SourceTheta_weakBlackAdjacency
    (n : ℕ) (xi : ZMod (3 ^ n)) (epsilon : ℝ) :
    TaoSection7WeakBlackAdjacency epsilon (taoSection7SourceTheta n xi) := by
  let theta := taoSection7SourceTheta n xi
  constructor
  · intro p hp hright
    have hp' : |theta p| ≤ (1 / 100 : ℝ) := hp
    have hguard : |9 * theta p| < (1 / 2 : ℝ) := by
      calc
        |9 * theta p| = 9 * |theta p| := by rw [abs_mul]; norm_num
        _ ≤ 9 * (1 / 100 : ℝ) := mul_le_mul_of_nonneg_left hp' (by norm_num)
        _ < 1 / 2 := by norm_num
    have htransport :=
      taoSection7SourceTheta_right_of_abs_lt_half n xi p hguard
    change theta p.right = 9 * theta p at htransport
    have hright' : |theta p.right| ≤ epsilon := hright
    have hepsilon : 0 ≤ epsilon := (abs_nonneg _).trans hright'
    rw [htransport] at hright'
    have hscaled : 9 * |theta p| ≤ epsilon := by
      simpa [abs_mul] using hright'
    show |theta p| ≤ epsilon
    nlinarith [abs_nonneg (theta p)]
  · intro p hp hdown
    have hp' : |theta p| ≤ (1 / 100 : ℝ) := hp
    have hguard : |2 * theta p| < (1 / 2 : ℝ) := by
      calc
        |2 * theta p| = 2 * |theta p| := by rw [abs_mul]; norm_num
        _ ≤ 2 * (1 / 100 : ℝ) := mul_le_mul_of_nonneg_left hp' (by norm_num)
        _ < 1 / 2 := by norm_num
    have htransport :=
      taoSection7SourceTheta_down_of_abs_lt_half n xi p hguard
    change theta p.down = 2 * theta p at htransport
    have hdown' : |theta p.down| ≤ epsilon := hdown
    have hepsilon : 0 ≤ epsilon := (abs_nonneg _).trans hdown'
    rw [htransport] at hdown'
    have hscaled : 2 * |theta p| ≤ epsilon := by
      simpa [abs_mul] using hdown'
    show |theta p| ≤ epsilon
    nlinarith [abs_nonneg (theta p)]
  · intro p hright hdown
    have hright' : |theta p.right| ≤ (1 / 100 : ℝ) := hright
    have hdown' : |theta p.down| ≤ (1 / 100 : ℝ) := hdown
    have hcandidate :
        |theta p.right - 4 * theta p.down| ≤ (5 / 100 : ℝ) := by
      calc
        |theta p.right - 4 * theta p.down| ≤
            |theta p.right| + |4 * theta p.down| := abs_sub _ _
        _ = |theta p.right| + 4 * |theta p.down| := by
          rw [abs_mul]
          norm_num
        _ ≤ (1 / 100 : ℝ) + 4 * (1 / 100 : ℝ) :=
          add_le_add hright'
            (mul_le_mul_of_nonneg_left hdown' (by norm_num))
        _ = 5 / 100 := by norm_num
    have hguard :
        |theta p.right - 4 * theta p.down| < (1 / 2 : ℝ) :=
      hcandidate.trans_lt (by norm_num)
    have hrelation :=
      taoSection7SourceTheta_eq_right_sub_four_down_of_abs_lt_half
        n xi p hguard
    change theta p = theta p.right - 4 * theta p.down at hrelation
    have hp05 : |theta p| ≤ (5 / 100 : ℝ) := by
      rw [hrelation]
      exact hcandidate
    have hrightGuard : |9 * theta p| < (1 / 2 : ℝ) := by
      calc
        |9 * theta p| = 9 * |theta p| := by rw [abs_mul]; norm_num
        _ ≤ 9 * (5 / 100 : ℝ) :=
          mul_le_mul_of_nonneg_left hp05 (by norm_num)
        _ < 1 / 2 := by norm_num
    have hrightTransport :=
      taoSection7SourceTheta_right_of_abs_lt_half n xi p hrightGuard
    change theta p.right = 9 * theta p at hrightTransport
    rw [hrightTransport] at hright'
    have hsharp : 9 * |theta p| ≤ (1 / 100 : ℝ) := by
      simpa [abs_mul] using hright'
    show |theta p| ≤ (1 / 100 : ℝ)
    nlinarith [abs_nonneg (theta p)]

  · intro p h hleft hdown
    have hleft' : |theta (p.left h)| ≤ (1 / 100 : ℝ) := hleft
    have hdown' : |theta p.down| ≤ (1 / 100 : ℝ) := hdown
    have hleftGuard : |9 * theta (p.left h)| < (1 / 2 : ℝ) := by
      calc
        |9 * theta (p.left h)| = 9 * |theta (p.left h)| := by
          rw [abs_mul]
          norm_num
        _ ≤ 9 * (1 / 100 : ℝ) :=
          mul_le_mul_of_nonneg_left hleft' (by norm_num)
        _ < 1 / 2 := by norm_num
    have hleftTransport :=
      taoSection7SourceTheta_eq_nine_mul_left_of_abs_lt_half
        n xi p h hleftGuard
    change theta p = 9 * theta (p.left h) at hleftTransport
    have hp09 : |theta p| ≤ (9 / 100 : ℝ) := by
      calc
        |theta p| = 9 * |theta (p.left h)| := by
          rw [hleftTransport, abs_mul]
          norm_num
        _ ≤ 9 * (1 / 100 : ℝ) :=
          mul_le_mul_of_nonneg_left hleft' (by norm_num)
        _ = 9 / 100 := by ring
    have hdownGuard : |2 * theta p| < (1 / 2 : ℝ) := by
      calc
        |2 * theta p| = 2 * |theta p| := by rw [abs_mul]; norm_num
        _ ≤ 2 * (9 / 100 : ℝ) :=
          mul_le_mul_of_nonneg_left hp09 (by norm_num)
        _ < 1 / 2 := by norm_num
    have hdownTransport :=
      taoSection7SourceTheta_down_of_abs_lt_half n xi p hdownGuard
    change theta p.down = 2 * theta p at hdownTransport
    rw [hdownTransport] at hdown'
    have hsharp : 2 * |theta p| ≤ (1 / 100 : ℝ) := by
      simpa [abs_mul] using hdown'
    show |theta p| ≤ (1 / 100 : ℝ)
    nlinarith [abs_nonneg (theta p)]

theorem natAbs_valMinAbs_nsmul_le
    {N : ℕ} (k : ℕ) (z : ZMod N) :
    (k • z).valMinAbs.natAbs ≤ k * z.valMinAbs.natAbs := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [succ_nsmul]
      calc
        (k • z + z).valMinAbs.natAbs ≤
            ((k • z).valMinAbs + z.valMinAbs).natAbs :=
          ZMod.natAbs_valMinAbs_add_le (k • z) z
        _ ≤ (k • z).valMinAbs.natAbs + z.valMinAbs.natAbs :=
          Int.natAbs_add_le _ _
        _ ≤ k * z.valMinAbs.natAbs + z.valMinAbs.natAbs :=
          Nat.add_le_add_right ih _
        _ = (k + 1) * z.valMinAbs.natAbs := by ring

theorem abs_taoSignedTheta_natCast_mul_le
    {N : ℕ} [NeZero N] (k : ℕ) (z : ZMod N) :
    |taoSignedTheta ((k : ZMod N) * z)| ≤
      (k : ℝ) * |taoSignedTheta z| := by
  have hN : (0 : ℝ) < (N : ℝ) := by exact_mod_cast NeZero.pos N
  have hmul : (k : ZMod N) * z = k • z := by
    rw [mul_comm]
    exact (nsmul_eq_mul' z k).symm
  have hnumNat := natAbs_valMinAbs_nsmul_le (N := N) k z
  have hnumInt :
      |(k • z).valMinAbs| ≤ (k : ℤ) * |z.valMinAbs| := by
    rw [Int.abs_eq_natAbs, Int.abs_eq_natAbs]
    exact_mod_cast hnumNat
  have hnum :
      |((((k • z).valMinAbs : ℤ) : ℝ))| ≤
        (k : ℝ) * |((z.valMinAbs : ℤ) : ℝ)| := by
    rw [← Int.cast_abs, ← Int.cast_abs]
    exact_mod_cast hnumInt
  rw [taoSignedTheta, taoSignedTheta, hmul, abs_div, abs_div,
    abs_of_pos hN]
  calc
    |(((k • z).valMinAbs : ℤ) : ℝ)| / (N : ℝ) ≤
        ((k : ℝ) * |((z.valMinAbs : ℤ) : ℝ)|) / (N : ℝ) :=
      div_le_div_of_nonneg_right hnum hN.le
    _ = (k : ℝ) * (|((z.valMinAbs : ℤ) : ℝ)| / (N : ℝ)) := by ring

end

end Tao

end Erdos1135Predecessor
