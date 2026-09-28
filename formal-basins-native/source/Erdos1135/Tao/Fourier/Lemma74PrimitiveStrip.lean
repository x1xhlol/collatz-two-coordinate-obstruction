import Erdos1135.Tao.Fourier.DecayStatement
import Erdos1135.Tao.Fourier.Lemma74ThetaArithmetic

/-!
# Lemma 7.4 Primitive Strip

This proof leaf supplies the primitive-frequency arithmetic used to keep
Section 7 black points away from the right boundary and to find a bounded
white point above them. It stops before canonical selectors and triangle
families.
-/

namespace Erdos1135
namespace Tao

noncomputable section

/-- A primitive class modulo `3^n` is a unit. This uses nondivisibility by
`3`, not merely nonzeroness. -/
theorem zmodThreePrimitive.isUnit
    {n : ℕ} {xi : ZMod (3 ^ n)} (hxi : zmodThreePrimitive n xi) :
    IsUnit xi := by
  have hthree : ¬ 3 ∣ xi.val := by
    rintro ⟨k, hk⟩
    apply hxi
    refine ⟨(k : ZMod (3 ^ n)), ?_⟩
    rw [← ZMod.natCast_zmod_val xi, hk, Nat.cast_mul]
    norm_num
  rw [← ZMod.natCast_zmod_val xi]
  exact (ZMod.isUnit_iff_coprime xi.val (3 ^ n)).2
    (Nat.prime_three.coprime_pow_of_not_dvd hthree)

/-- Multiplication by `3^(n-1)` sends every unit modulo `3^n` to one of the
two nonzero elements annihilated by `3`, hence its centered numerator has
magnitude `3^(n-1)`. -/
theorem natAbs_valMinAbs_three_pow_pred_mul_unit
    {n : ℕ} (hn : 1 ≤ n) {u : ZMod (3 ^ n)} (hu : IsUnit u) :
    (((3 : ZMod (3 ^ n)) ^ (n - 1) * u).valMinAbs).natAbs =
      3 ^ (n - 1) := by
  let p : ℕ := 3 ^ (n - 1)
  let x : ZMod (3 ^ n) := (p : ZMod (3 ^ n)) * u
  have hp : 0 < p := by
    dsimp [p]
    positivity
  have hfactor : p * 3 = 3 ^ n := by
    dsimp [p]
    exact pow_sub_one_mul (by omega) 3
  have hp_lt : p < 3 ^ n := by
    rw [← hfactor]
    omega
  have hp_cast_ne : (p : ZMod (3 ^ n)) ≠ 0 := by
    intro hzero
    exact (Nat.not_dvd_of_pos_of_lt hp hp_lt)
      ((ZMod.natCast_eq_zero_iff p (3 ^ n)).1 hzero)
  have hx_ne : x ≠ 0 := by
    intro hx
    apply hp_cast_ne
    apply hu.mul_left_injective
    simpa [x] using hx
  have hthree_x : (3 : ZMod (3 ^ n)) * x = 0 := by
    dsimp [x]
    calc
      (3 : ZMod (3 ^ n)) * ((p : ZMod (3 ^ n)) * u) =
          ((p * 3 : ℕ) : ZMod (3 ^ n)) * u := by
            push_cast
            ring
      _ = 0 := by simp [hfactor]
  have hcast :
      (((3 : ℤ) * x.valMinAbs : ℤ) : ZMod (3 ^ n)) = 0 := by
    rw [Int.cast_mul, ZMod.coe_valMinAbs]
    simpa using hthree_x
  have hbig : ((3 ^ n : ℕ) : ℤ) ∣ (3 : ℤ) * x.valMinAbs :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd _ _).1 hcast
  have hsmall : (p : ℤ) ∣ x.valMinAbs := by
    have hfactorInt : (3 : ℤ) * (p : ℤ) = ((3 ^ n : ℕ) : ℤ) := by
      exact_mod_cast (by simpa [mul_comm] using hfactor)
    apply Int.dvd_of_mul_dvd_mul_left (by norm_num : (3 : ℤ) ≠ 0)
    rwa [hfactorInt]
  have hsmallNat : p ∣ x.valMinAbs.natAbs :=
    Int.natCast_dvd.mp hsmall
  have hnum_ne : x.valMinAbs.natAbs ≠ 0 := by
    simpa [Int.natAbs_eq_zero, ZMod.valMinAbs_eq_zero] using hx_ne
  have hupper : x.valMinAbs.natAbs ≤ (3 ^ n) / 2 :=
    ZMod.natAbs_valMinAbs_le x
  have hhalf : (3 ^ n) / 2 < 2 * p := by
    rw [← hfactor]
    omega
  have hlt : x.valMinAbs.natAbs < 2 * p := hupper.trans_lt hhalf
  rcases hsmallNat with ⟨q, hq⟩
  have hq_pos : 0 < q := by
    apply Nat.pos_of_ne_zero
    intro hq_zero
    apply hnum_ne
    simpa [hq_zero] using hq
  have hq_lt : q < 2 := by
    apply (Nat.mul_lt_mul_left hp).mp
    simpa [hq, mul_comm] using hlt
  have hq_one : q = 1 := by omega
  subst q
  simpa [x, p] using hq

/-- Tao's terminal primitive residue has exact centered magnitude `1/3`. -/
theorem abs_taoSignedTheta_three_pow_pred_mul_unit
    {n : ℕ} (hn : 1 ≤ n) {u : ZMod (3 ^ n)} (hu : IsUnit u) :
    |taoSignedTheta
      ((3 : ZMod (3 ^ n)) ^ (n - 1) * u)| = (1 : ℝ) / 3 := by
  let x : ZMod (3 ^ n) :=
    (3 : ZMod (3 ^ n)) ^ (n - 1) * u
  have hnumNat : x.valMinAbs.natAbs = 3 ^ (n - 1) := by
    simpa [x] using natAbs_valMinAbs_three_pow_pred_mul_unit hn hu
  have hnumReal :
      |((x.valMinAbs : ℤ) : ℝ)| = ((3 ^ (n - 1) : ℕ) : ℝ) := by
    rw [← Int.cast_abs, Int.abs_eq_natAbs]
    exact_mod_cast hnumNat
  have hfactor :
      ((3 ^ n : ℕ) : ℝ) = 3 * ((3 ^ (n - 1) : ℕ) : ℝ) := by
    have hfactorNat : 3 ^ n = 3 * 3 ^ (n - 1) := by
      calc
        3 ^ n = 3 ^ (n - 1) * 3 :=
          (pow_sub_one_mul (by omega : n ≠ 0) 3).symm
        _ = 3 * 3 ^ (n - 1) := by ring
    exact_mod_cast hfactorNat
  have hpReal : (0 : ℝ) < ((3 ^ (n - 1) : ℕ) : ℝ) := by positivity
  rw [taoSignedTheta, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (3 ^ n : ℕ))]
  change |((x.valMinAbs : ℤ) : ℝ)| / ((3 ^ n : ℕ) : ℝ) = _
  rw [hnumReal, hfactor]
  field_simp

/-- Multiplying a primitive class by an integral power of `2` preserves
unitness. -/
theorem taoSection7TwoZPow_mul_primitive_isUnit
    {n : ℕ} {xi : ZMod (3 ^ n)} (hxi : zmodThreePrimitive n xi)
    (l : ℤ) :
    IsUnit (taoSection7TwoZPow n (1 - l) * xi) := by
  have htwo : IsUnit (taoSection7TwoZPow n (1 - l)) := by
    unfold taoSection7TwoZPow
    exact Units.isUnit _
  exact htwo.mul hxi.isUnit

/-- Exact modular amplification of a Section 7 theta residue to its terminal
`3`-adic scale. -/
theorem three_pow_amplify_taoSection7ThetaResidue
    {n : ℕ} (xi : ZMod (3 ^ n)) (j : ℕ+) (l : ℤ)
    (hj : (j : ℕ) ≤ n / 2) :
    (3 : ZMod (3 ^ n)) ^ (n + 1 - 2 * (j : ℕ)) *
        taoSection7ThetaResidue n xi j l =
      (3 : ZMod (3 ^ n)) ^ (n - 1) *
        (taoSection7TwoZPow n (1 - l) * xi) := by
  have hexp :
      (n + 1 - 2 * (j : ℕ)) + 2 * ((j : ℕ) - 1) = n - 1 := by
    have hjpos : 0 < (j : ℕ) := j.pos
    omega
  unfold taoSection7ThetaResidue
  calc
    (3 : ZMod (3 ^ n)) ^ (n + 1 - 2 * (j : ℕ)) *
          (((3 : ZMod (3 ^ n)) ^ (2 * ((j : ℕ) - 1)) *
              taoSection7TwoZPow n (1 - l)) * xi) =
        (3 : ZMod (3 ^ n)) ^
            ((n + 1 - 2 * (j : ℕ)) + 2 * ((j : ℕ) - 1)) *
          (taoSection7TwoZPow n (1 - l) * xi) := by
            rw [pow_add]
            ring
    _ = _ := by rw [hexp]

/-- Primitive theta residues in the left half-strip cannot be too small after
amplification to the terminal `3`-adic scale. -/
theorem one_third_le_three_pow_mul_abs_taoSection7ThetaResidue
    {n : ℕ} {xi : ZMod (3 ^ n)} (hxi : zmodThreePrimitive n xi)
    (j : ℕ+) (hj : (j : ℕ) ≤ n / 2) (l : ℤ) :
    (1 : ℝ) / 3 ≤
      (3 : ℝ) ^ (n + 1 - 2 * (j : ℕ)) *
        |taoSignedTheta (taoSection7ThetaResidue n xi j l)| := by
  have hn : 1 ≤ n := by
    have hjpos : 0 < (j : ℕ) := j.pos
    omega
  have hu := taoSection7TwoZPow_mul_primitive_isUnit hxi l
  have hterminal := abs_taoSignedTheta_three_pow_pred_mul_unit hn hu
  have hscale := abs_taoSignedTheta_natCast_mul_le
    (N := 3 ^ n) (3 ^ (n + 1 - 2 * (j : ℕ)))
    (taoSection7ThetaResidue n xi j l)
  have hid := three_pow_amplify_taoSection7ThetaResidue xi j l hj
  have hcastIdentity :
      ((3 ^ (n + 1 - 2 * (j : ℕ)) : ℕ) : ZMod (3 ^ n)) *
          taoSection7ThetaResidue n xi j l =
        (3 : ZMod (3 ^ n)) ^ (n - 1) *
          (taoSection7TwoZPow n (1 - l) * xi) := by
    simpa using hid
  rw [hcastIdentity, hterminal] at hscale
  simpa using hscale

/-- A black primitive point obeys Tao's raw amplified strip inequality. -/
theorem one_third_le_three_pow_mul_epsilon_of_sourceBlackPoint
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi) (p : TaoSection7Point)
    (hp : (p.j : ℕ) ≤ n / 2)
    (hblack : taoSection7SourceBlackPoint n xi epsilon p) :
    (1 : ℝ) / 3 ≤
      (3 : ℝ) ^ (n + 1 - 2 * (p.j : ℕ)) * epsilon := by
  calc
    (1 : ℝ) / 3 ≤
        (3 : ℝ) ^ (n + 1 - 2 * (p.j : ℕ)) *
          |taoSection7SourceTheta n xi p| := by
            exact one_third_le_three_pow_mul_abs_taoSection7ThetaResidue
              hxi p.j hp p.l
    _ ≤ (3 : ℝ) ^ (n + 1 - 2 * (p.j : ℕ)) * epsilon := by
      exact mul_le_mul_of_nonneg_left hblack (by positivity)

/-- Logarithmic coordinate form of the primitive black-strip inequality. -/
theorem taoSection7SourceBlackPoint_raw_log_coordinate
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi) (hepsilon : 0 < epsilon)
    (p : TaoSection7Point) (hp : (p.j : ℕ) ≤ n / 2)
    (hblack : taoSection7SourceBlackPoint n xi epsilon p) :
    2 * (((p.j : ℕ) : ℝ)) +
        Real.log (1 / (3 * epsilon)) / Real.log 3 ≤
      (n : ℝ) + 1 := by
  have hamp := one_third_le_three_pow_mul_epsilon_of_sourceBlackPoint
    hxi p hp hblack
  have hthreeEpsilon : 0 < (3 : ℝ) * epsilon :=
    mul_pos (by norm_num) hepsilon
  have hdiv :
      (1 : ℝ) / (3 * epsilon) ≤
        (3 : ℝ) ^ (n + 1 - 2 * (p.j : ℕ)) := by
    rw [div_le_iff₀ hthreeEpsilon]
    nlinarith
  have hlog := Real.log_le_log (div_pos (by norm_num) hthreeEpsilon) hdiv
  rw [Real.log_pow] at hlog
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hquotient :
      Real.log (1 / (3 * epsilon)) / Real.log 3 ≤
        ((n + 1 - 2 * (p.j : ℕ) : ℕ) : ℝ) := by
    rw [div_le_iff₀ hlog3]
    simpa [mul_comm] using hlog
  have hsub : 2 * (p.j : ℕ) ≤ n + 1 := by omega
  have hcast :
      ((n + 1 - 2 * (p.j : ℕ) : ℕ) : ℝ) =
        (n : ℝ) + 1 - 2 * (((p.j : ℕ) : ℝ)) := by
    rw [Nat.cast_sub hsub]
    push_cast
    ring
  rw [hcast] at hquotient
  linarith

/-- The source regime `epsilon <= 1/100` supplies the scalar margin used to
turn the raw logarithmic coordinate bound into Tao's right-strip inset. -/
theorem one_add_taoSection7TriangleSeparation_le_logScale_div_log9
    {epsilon : ℝ} (hepsilon0 : 0 < epsilon)
    (hepsilon100 : epsilon ≤ (1 / 100 : ℝ)) :
    1 + taoSection7TriangleSeparation epsilon ≤
      taoSection7TriangleLogScale epsilon / Real.log 9 := by
  let L : ℝ := taoSection7TriangleLogScale epsilon
  have hlog9 : 0 < Real.log (9 : ℝ) := Real.log_pos (by norm_num)
  have hhundred : (100 : ℝ) ≤ 1 / epsilon := by
    rw [le_div_iff₀ hepsilon0]
    nlinarith
  have heightyOne : (81 : ℝ) ≤ 1 / epsilon := by linarith
  have htwoLog9 : 2 * Real.log 9 ≤ L := by
    have hlog := Real.log_le_log (by norm_num : (0 : ℝ) < 81) heightyOne
    rw [show (81 : ℝ) = 9 ^ 2 by norm_num, Real.log_pow] at hlog
    simpa [L, taoSection7TriangleLogScale] using hlog
  have hlog3_le_two : Real.log (3 : ℝ) ≤ 2 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
    norm_num at h
    exact h
  have hlog9_eq : Real.log (9 : ℝ) = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have hlog9_le_five : Real.log (9 : ℝ) ≤ 5 := by
    rw [hlog9_eq]
    linarith
  have hL0 : 0 ≤ L := by linarith
  have hfirstHalf : Real.log 9 ≤ L / 2 := by linarith
  have hsecondHalf : L * Real.log 9 / 10 ≤ L / 2 := by
    have hproduct : 0 ≤ L * (5 - Real.log 9) :=
      mul_nonneg hL0 (sub_nonneg.mpr hlog9_le_five)
    nlinarith
  apply (le_div_iff₀ hlog9).2
  change (1 + (1 / 10 : ℝ) * L) * Real.log 9 ≤ L
  nlinarith

/-- Primitive black points in the source regime lie inside Tao's real
right-strip boundary. The conclusion retains the real half `(n : ℝ) / 2`,
not the floored natural cutoff. -/
theorem taoSection7SourceBlackPoint_jReal_le_triangleRightBound
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hxi : zmodThreePrimitive n xi) (hepsilon0 : 0 < epsilon)
    (hepsilon100 : epsilon ≤ (1 / 100 : ℝ))
    (p : TaoSection7Point) (hp : (p.j : ℕ) ≤ n / 2)
    (hblack : taoSection7SourceBlackPoint n xi epsilon p) :
    (((p.j : ℕ) : ℝ)) ≤ taoSection7TriangleRightBound n epsilon := by
  let L : ℝ := taoSection7TriangleLogScale epsilon
  let rho : ℝ := taoSection7TriangleSeparation epsilon
  have hraw := taoSection7SourceBlackPoint_raw_log_coordinate
    hxi hepsilon0 p hp hblack
  have hscalar :=
    one_add_taoSection7TriangleSeparation_le_logScale_div_log9
      hepsilon0 hepsilon100
  have hlog3 : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
  have hlog9Eq : Real.log (9 : ℝ) = 2 * Real.log 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.log_pow]
    norm_num
  have harg : (1 : ℝ) / (3 * epsilon) = (1 / epsilon) / 3 := by
    field_simp
  have hlogArg :
      Real.log (1 / (3 * epsilon)) = L - Real.log 3 := by
    rw [harg, Real.log_div (one_div_ne_zero hepsilon0.ne') (by norm_num)]
    rfl
  have hratio :
      Real.log (1 / (3 * epsilon)) / Real.log 3 =
        2 * (L / Real.log 9) - 1 := by
    rw [hlogArg, hlog9Eq]
    field_simp [hlog3.ne']
  have hmargin :
      1 + 2 * rho ≤
        Real.log (1 / (3 * epsilon)) / Real.log 3 := by
    change 1 + rho ≤ L / Real.log 9 at hscalar
    rw [hratio]
    linarith
  unfold taoSection7TriangleRightBound
  change (((p.j : ℕ) : ℝ)) ≤ (n : ℝ) / 2 - rho
  linarith

namespace TaoSection7Point

/-- The point `t` integral steps above `p`. -/
def upN (p : TaoSection7Point) (t : ℕ) : TaoSection7Point :=
  ⟨p.j, p.l + t⟩

@[simp] theorem upN_zero (p : TaoSection7Point) : p.upN 0 = p := by
  cases p
  simp [upN]

@[simp] theorem upN_j (p : TaoSection7Point) (t : ℕ) :
    (p.upN t).j = p.j := by
  rfl

@[simp] theorem upN_l (p : TaoSection7Point) (t : ℕ) :
    (p.upN t).l = p.l + t := by
  rfl

@[simp] theorem upN_succ_down (p : TaoSection7Point) (t : ℕ) :
    (p.upN (t + 1)).down = p.upN t := by
  cases p
  simp [upN, down]
  omega

end TaoSection7Point

/-- A black vertical prefix transports the upper theta back to its starting
value by an exact power of `2`. -/
theorem pow_two_mul_sourceTheta_upN_eq_of_black_prefix
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (p : TaoSection7Point) (t : ℕ) (hepsilon : epsilon < 1 / 100)
    (hblack : ∀ u, u ≤ t →
      taoSection7SourceBlackPoint n xi epsilon (p.upN u)) :
    (2 : ℝ) ^ t * taoSection7SourceTheta n xi (p.upN t) =
      taoSection7SourceTheta n xi p := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hupper := hblack (t + 1) (by omega)
      have hguard :
          |2 * taoSection7SourceTheta n xi (p.upN (t + 1))| <
            (1 / 2 : ℝ) := by
        calc
          |2 * taoSection7SourceTheta n xi (p.upN (t + 1))| =
              2 * |taoSection7SourceTheta n xi (p.upN (t + 1))| := by
                rw [abs_mul]
                norm_num
          _ ≤ 2 * epsilon :=
            mul_le_mul_of_nonneg_left hupper (by norm_num)
          _ < 1 / 2 := by linarith
      have hdown := taoSection7SourceTheta_down_of_abs_lt_half
        n xi (p.upN (t + 1)) hguard
      rw [TaoSection7Point.upN_succ_down] at hdown
      have ih' := ih (fun u hu => hblack u (by omega))
      rw [pow_succ]
      calc
        (2 : ℝ) ^ t * 2 * taoSection7SourceTheta n xi (p.upN (t + 1)) =
            (2 : ℝ) ^ t * taoSection7SourceTheta n xi (p.upN t) := by
              rw [hdown]
              ring
        _ = taoSection7SourceTheta n xi p := ih'

/-- Every primitive black point in the left half-strip has a white point at
one of the next `2*n` vertical offsets. -/
theorem exists_sourceWhitePoint_upN_le_two_mul
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hn : 1 ≤ n) (hxi : zmodThreePrimitive n xi)
    (p : TaoSection7Point) (hp : (p.j : ℕ) ≤ n / 2)
    (hstart : taoSection7SourceBlackPoint n xi epsilon p)
    (hepsilon : epsilon < 1 / 100) :
    ∃ t : ℕ, 1 ≤ t ∧ t ≤ 2 * n ∧
      taoSection7SourceWhitePoint n xi epsilon (p.upN t) := by
  by_contra hnone
  have hall : ∀ u, u ≤ 2 * n →
      taoSection7SourceBlackPoint n xi epsilon (p.upN u) := by
    intro u hu
    by_cases hu0 : u = 0
    · simpa [hu0] using hstart
    · have hnotWhite :
          ¬ taoSection7SourceWhitePoint n xi epsilon (p.upN u) := by
        intro hwhite
        apply hnone
        exact ⟨u, Nat.one_le_iff_ne_zero.2 hu0, hu, hwhite⟩
      simpa [taoSection7SourceWhitePoint, taoSection7White,
        taoSection7SourceBlackPoint, taoSection7Black, not_lt] using hnotWhite
  have htransport := pow_two_mul_sourceTheta_upN_eq_of_black_prefix
    p (2 * n) hepsilon hall
  have hpowTwo : (2 : ℝ) ^ (2 * n) = (4 : ℝ) ^ n := by
    calc
      (2 : ℝ) ^ (2 * n) = ((2 : ℝ) ^ 2) ^ n := by rw [pow_mul]
      _ = (4 : ℝ) ^ n := by norm_num
  have hdecay :
      (4 : ℝ) ^ n *
          |taoSection7SourceTheta n xi (p.upN (2 * n))| ≤ epsilon := by
    calc
      (4 : ℝ) ^ n *
          |taoSection7SourceTheta n xi (p.upN (2 * n))| =
          |(2 : ℝ) ^ (2 * n) *
            taoSection7SourceTheta n xi (p.upN (2 * n))| := by
              rw [abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
                hpowTwo]
      _ = |taoSection7SourceTheta n xi p| := by rw [htransport]
      _ ≤ epsilon := hstart
  have hamp := one_third_le_three_pow_mul_abs_taoSection7ThetaResidue
    hxi p.j hp (p.upN (2 * n)).l
  have hamp' :
      (1 : ℝ) / 3 ≤
        (3 : ℝ) ^ (n + 1 - 2 * (p.j : ℕ)) *
          |taoSection7SourceTheta n xi (p.upN (2 * n))| := by
    simpa [taoSection7SourceTheta] using hamp
  have hexp : n + 1 - 2 * (p.j : ℕ) ≤ n - 1 := by
    have hjpos : 0 < (p.j : ℕ) := p.j.pos
    omega
  have hpowBound :
      (3 : ℝ) ^ (n + 1 - 2 * (p.j : ℕ)) ≤ (4 : ℝ) ^ n := by
    calc
      (3 : ℝ) ^ (n + 1 - 2 * (p.j : ℕ)) ≤
          (3 : ℝ) ^ (n - 1) :=
        pow_le_pow_right₀ (by norm_num) hexp
      _ ≤ (4 : ℝ) ^ (n - 1) := by
        gcongr
        norm_num
      _ ≤ (4 : ℝ) ^ n := by
        apply pow_le_pow_right₀ (by norm_num)
        omega
  have hscaled :
      (3 : ℝ) ^ (n + 1 - 2 * (p.j : ℕ)) *
          |taoSection7SourceTheta n xi (p.upN (2 * n))| ≤
        (4 : ℝ) ^ n *
          |taoSection7SourceTheta n xi (p.upN (2 * n))| :=
    mul_le_mul_of_nonneg_right hpowBound (abs_nonneg _)
  have hcontra : (1 : ℝ) / 3 < 1 / 3 :=
    hamp'.trans (hscaled.trans hdecay) |>.trans_lt
      (hepsilon.trans (by norm_num))
  exact (lt_irrefl ((1 : ℝ) / 3)) hcontra

end

end Tao
end Erdos1135
