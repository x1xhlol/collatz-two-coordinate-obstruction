import Erdos1135.Tao.Probability.CountableMarkov
import Erdos1135.Tao.Syracuse.ValuationDistribution
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Centered Exponential Moments of Positive Geom(2)

This low probability leaf proves the exact centered one-step MGF and its
finite iid-list power.  It stays native in `ENNReal` through the countable PMF
bind recursion, then projects the finite result to a real summable series.
-/

open scoped BigOperators Topology

namespace Erdos1135
namespace Tao

noncomputable section

/-- Centered exponential moment of one positive-support Geom(2) variable. -/
noncomputable def taoGeom2CenteredExpMoment (t : ℝ) : ℝ :=
  ∑' a : ℕ+, (geom2PNat a).toReal *
    Real.exp (t * (((a : ℕ) : ℝ) - 2))

theorem taoGeom2CenteredExpMoment_eq
    {t : ℝ} (ht : Real.exp t < 2) :
    taoGeom2CenteredExpMoment t =
      Real.exp (-t) / (2 - Real.exp t) := by
  have hratio0 : 0 ≤ Real.exp t / 2 := by positivity
  have hratio1 : Real.exp t / 2 < 1 := by linarith
  unfold taoGeom2CenteredExpMoment
  calc
    (∑' a : ℕ+, (geom2PNat a).toReal *
        Real.exp (t * (((a : ℕ) : ℝ) - 2))) =
      ∑' n : ℕ, (geom2PNat (Equiv.pnatEquivNat.symm n)).toReal *
        Real.exp (t *
          ((((Equiv.pnatEquivNat.symm n : ℕ+) : ℕ) : ℝ) - 2)) := by
            exact (Equiv.pnatEquivNat.symm.tsum_eq _).symm
    _ = ∑' n : ℕ, (Real.exp (-t) / 2) * (Real.exp t / 2) ^ n := by
      apply tsum_congr
      intro n
      rw [Equiv.pnatEquivNat_symm_apply]
      have hmass :
          (geom2PNat n.succPNat).toReal = (1 / 2 : ℝ) ^ (n + 1) := by
        simpa using geom2PNat_apply_toReal n.succPNat
      have hcoe : ((n.succPNat : ℕ+) : ℕ) = n + 1 := by rfl
      rw [hmass, hcoe]
      rw [show t * (((n + 1 : ℕ) : ℝ) - 2) =
          -t + (n : ℝ) * t by
            push_cast
            ring,
        Real.exp_add, Real.exp_nat_mul]
      ring
    _ = (Real.exp (-t) / 2) * ∑' n : ℕ, (Real.exp t / 2) ^ n := by
      rw [tsum_mul_left]
    _ = (Real.exp (-t) / 2) * (1 - Real.exp t / 2)⁻¹ := by
      rw [tsum_geometric_of_lt_one hratio0 hratio1]
    _ = Real.exp (-t) / (2 - Real.exp t) := by
      have hden : 2 - Real.exp t ≠ 0 := by linarith
      field_simp

theorem summable_geom2PNat_mul_centeredExp
    {t : ℝ} (ht : Real.exp t < 2) :
    Summable fun a : ℕ+ =>
      (geom2PNat a).toReal * Real.exp (t * (((a : ℕ) : ℝ) - 2)) := by
  have hratio0 : 0 ≤ Real.exp t / 2 := by positivity
  have hratio1 : Real.exp t / 2 < 1 := by linarith
  apply (Equiv.pnatEquivNat.symm.summable_iff).mp
  have hs : Summable fun n : ℕ =>
      (Real.exp (-t) / 2) * (Real.exp t / 2) ^ n :=
    (summable_geometric_of_norm_lt_one
      (show ‖Real.exp t / 2‖ < 1 by
        rw [Real.norm_of_nonneg hratio0]
        exact hratio1)).mul_left _
  apply hs.congr
  intro n
  rw [Function.comp_apply, Equiv.pnatEquivNat_symm_apply]
  have hmass :
      (geom2PNat n.succPNat).toReal = (1 / 2 : ℝ) ^ (n + 1) := by
    simpa using geom2PNat_apply_toReal n.succPNat
  have hcoe : ((n.succPNat : ℕ+) : ℕ) = n + 1 := by rfl
  rw [hmass, hcoe]
  rw [show t * (((n + 1 : ℕ) : ℝ) - 2) =
      -t + (n : ℝ) * t by
        push_cast
        ring,
    Real.exp_add, Real.exp_nat_mul]
  ring

theorem taoGeom2CenteredExpMoment_nonneg (t : ℝ) :
    0 ≤ taoGeom2CenteredExpMoment t := by
  unfold taoGeom2CenteredExpMoment
  exact tsum_nonneg fun a =>
    mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le

private theorem one_sub_sq_inv_le_exp_two_mul
    {x : ℝ} (hx : 0 ≤ x) (hxhalf : 2 * x ≤ 1) :
    (1 - x)⁻¹ ≤ Real.exp (2 * x) := by
  have hden : 0 < 1 - x := by linarith
  calc
    (1 - x)⁻¹ ≤ 1 + 2 * x := (inv_le_iff_one_le_mul₀ hden).2 (by
      nlinarith [mul_nonneg hx (by linarith : 0 ≤ 1 - 2 * x)])
    _ = 2 * x + 1 := by ring
    _ ≤ Real.exp (2 * x) := Real.add_one_le_exp (2 * x)

private theorem exp_lt_two_of_abs_le_quarter
    {t : ℝ} (ht : |t| ≤ 1 / 4) : Real.exp t < 2 := by
  by_cases ht0 : 0 ≤ t
  · have ht1 : t < 1 := by
      have := (le_trans (le_abs_self t) ht)
      norm_num at this ⊢
      linarith
    have hexp : Real.exp t ≤ (1 - t)⁻¹ := by
      simpa [one_div] using
        Real.exp_bound_div_one_sub_of_interval ht0 ht1
    have hden : 0 < 1 - t := by linarith
    have hinv : (1 - t)⁻¹ ≤ (4 / 3 : ℝ) := by
      rw [inv_le_iff_one_le_mul₀ hden]
      have htq : t ≤ 1 / 4 := (le_abs_self t).trans ht
      nlinarith
    exact lt_of_le_of_lt (hexp.trans hinv) (by norm_num)
  · have htneg : t < 0 := lt_of_not_ge ht0
    exact (Real.exp_lt_one_iff.mpr htneg).trans (by norm_num)

theorem taoGeom2CenteredExpMoment_eq_one_sub_sq_inv
    {t : ℝ} (ht : Real.exp t < 2) :
    taoGeom2CenteredExpMoment t =
      (1 - (Real.exp t - 1) ^ 2)⁻¹ := by
  rw [taoGeom2CenteredExpMoment_eq ht]
  rw [Real.exp_neg]
  rw [show 1 - (Real.exp t - 1) ^ 2 =
      Real.exp t * (2 - Real.exp t) by ring]
  rw [mul_inv, div_eq_mul_inv]

/-- Uniform quadratic MGF bound at all rates `|t| ≤ 1/4`. -/
theorem taoGeom2CenteredExpMoment_le_exp_eight_mul_sq
    {t : ℝ} (ht : |t| ≤ 1 / 4) :
    taoGeom2CenteredExpMoment t ≤ Real.exp (8 * t ^ 2) := by
  have hadm : Real.exp t < 2 := exp_lt_two_of_abs_le_quarter ht
  let u : ℝ := Real.exp t - 1
  have huabs : |u| ≤ 2 * |t| := by
    exact Real.abs_exp_sub_one_le (by linarith)
  have htquarter : |t| ≤ 1 / 4 := ht
  have hu2 : u ^ 2 ≤ 4 * t ^ 2 := by
    nlinarith [sq_nonneg (|u|), sq_nonneg (|t|),
      pow_le_pow_left₀ (abs_nonneg u) huabs 2,
      sq_abs u, sq_abs t]
  have huHalf : 2 * u ^ 2 ≤ 1 := by
    have ht2 : t ^ 2 ≤ (1 / 4 : ℝ) ^ 2 := by
      simpa [sq_abs] using pow_le_pow_left₀ (abs_nonneg t) htquarter 2
    nlinarith
  calc
    taoGeom2CenteredExpMoment t = (1 - u ^ 2)⁻¹ := by
      simpa [u] using taoGeom2CenteredExpMoment_eq_one_sub_sq_inv hadm
    _ ≤ Real.exp (2 * u ^ 2) :=
      one_sub_sq_inv_le_exp_two_mul (sq_nonneg u) huHalf
    _ ≤ Real.exp (8 * t ^ 2) := by
      exact Real.exp_le_exp.mpr (by nlinarith)

/-- Centered total valuation weight of a finite list. -/
noncomputable def taoGeom2CenteredListWeight (as : List ℕ+) : ℝ :=
  ((taoTupleWeight as : ℕ) : ℝ) - 2 * (as.length : ℝ)

theorem taoGeom2CenteredListWeight_cons (a : ℕ+) (as : List ℕ+) :
    taoGeom2CenteredListWeight (a :: as) =
      (((a : ℕ) : ℝ) - 2) + taoGeom2CenteredListWeight as := by
  unfold taoGeom2CenteredListWeight taoTupleWeight
  simp
  ring

theorem taoGeom2CenteredExpMoment_ennreal
    {t : ℝ} (ht : Real.exp t < 2) :
    taoPMFENNExpectation geom2PNat
        (fun a => ENNReal.ofReal
          (Real.exp (t * (((a : ℕ) : ℝ) - 2)))) =
      ENNReal.ofReal (taoGeom2CenteredExpMoment t) := by
  unfold taoPMFENNExpectation taoGeom2CenteredExpMoment
  rw [ENNReal.ofReal_tsum_of_nonneg]
  · apply tsum_congr
    intro a
    rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
      ENNReal.ofReal_toReal (PMF.apply_ne_top geom2PNat a)]
  · intro a
    exact mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le
  · exact summable_geom2PNat_mul_centeredExp ht

private theorem geom2CenteredExpWeight_cons
    (t : ℝ) (a : ℕ+) (as : List ℕ+) :
    ENNReal.ofReal
        (Real.exp (t * taoGeom2CenteredListWeight (a :: as))) =
      ENNReal.ofReal (Real.exp (t * (((a : ℕ) : ℝ) - 2))) *
        ENNReal.ofReal
          (Real.exp (t * taoGeom2CenteredListWeight as)) := by
  rw [taoGeom2CenteredListWeight_cons, mul_add, Real.exp_add,
    ENNReal.ofReal_mul (Real.exp_pos _).le]

/-- Exact native centered MGF of a length-`N` iid Geom(2) list. -/
theorem geom2PNatListPMF_centeredExpMoment_ennreal
    (N : ℕ) {t : ℝ} (ht : Real.exp t < 2) :
    taoPMFENNExpectation (geom2PNatListPMF N)
        (fun as => ENNReal.ofReal
          (Real.exp (t * taoGeom2CenteredListWeight as))) =
      ENNReal.ofReal (taoGeom2CenteredExpMoment t) ^ N := by
  induction N with
  | zero =>
      unfold taoPMFENNExpectation
      rw [tsum_eq_single []]
      · simp [geom2PNatListPMF, taoGeom2CenteredListWeight, taoTupleWeight]
      · intro as hne
        simp [geom2PNatListPMF, hne]
  | succ N ih =>
      let W : List ℕ+ → ENNReal := fun as =>
        ENNReal.ofReal
          (Real.exp (t * taoGeom2CenteredListWeight as))
      let WT : List ℕ+ → ENNReal := fun as =>
        ENNReal.ofReal
          (Real.exp (t * taoGeom2CenteredListWeight as))
      calc
        taoPMFENNExpectation (geom2PNatListPMF (N + 1)) W =
            taoPMFENNExpectation
              (geom2PNat.bind fun a =>
                (geom2PNatListPMF N).map fun as => a :: as) W := by rfl
        _ = ∑' a, geom2PNat a *
            taoPMFENNExpectation
              ((geom2PNatListPMF N).map fun as => a :: as) W :=
          taoPMFENNExpectation_bind _ _ _
        _ = ∑' a, geom2PNat a *
            taoPMFENNExpectation (geom2PNatListPMF N)
              (W ∘ fun as => a :: as) := by
          apply tsum_congr
          intro a
          rw [taoPMFENNExpectation_map]
        _ = ∑' a, geom2PNat a *
            (ENNReal.ofReal
                (Real.exp (t * (((a : ℕ) : ℝ) - 2))) *
              taoPMFENNExpectation (geom2PNatListPMF N) WT) := by
          apply tsum_congr
          intro a
          congr 1
          unfold taoPMFENNExpectation
          calc
            (∑' as, geom2PNatListPMF N as *
                (W ∘ fun as => a :: as) as) =
                ∑' as, geom2PNatListPMF N as *
                  (ENNReal.ofReal
                      (Real.exp (t * (((a : ℕ) : ℝ) - 2))) * WT as) := by
              apply tsum_congr
              intro as
              dsimp only [Function.comp_apply, W, WT]
              rw [geom2CenteredExpWeight_cons]
            _ = ENNReal.ofReal
                  (Real.exp (t * (((a : ℕ) : ℝ) - 2))) *
                ∑' as, geom2PNatListPMF N as * WT as := by
              calc
                (∑' as, geom2PNatListPMF N as *
                    (ENNReal.ofReal
                        (Real.exp (t * (((a : ℕ) : ℝ) - 2))) * WT as)) =
                    ∑' as, ENNReal.ofReal
                        (Real.exp (t * (((a : ℕ) : ℝ) - 2))) *
                      (geom2PNatListPMF N as * WT as) := by
                  apply tsum_congr
                  intro as
                  ac_rfl
                _ = ENNReal.ofReal
                    (Real.exp (t * (((a : ℕ) : ℝ) - 2))) *
                    ∑' as, geom2PNatListPMF N as * WT as :=
                  ENNReal.tsum_mul_left
        _ = (∑' a, geom2PNat a * ENNReal.ofReal
              (Real.exp (t * (((a : ℕ) : ℝ) - 2)))) *
            taoPMFENNExpectation (geom2PNatListPMF N) WT := by
          calc
            (∑' a, geom2PNat a *
                (ENNReal.ofReal
                    (Real.exp (t * (((a : ℕ) : ℝ) - 2))) *
                  taoPMFENNExpectation (geom2PNatListPMF N) WT)) =
                ∑' a, (geom2PNat a * ENNReal.ofReal
                    (Real.exp (t * (((a : ℕ) : ℝ) - 2)))) *
                  taoPMFENNExpectation (geom2PNatListPMF N) WT := by
              apply tsum_congr
              intro a
              ac_rfl
            _ = (∑' a, geom2PNat a * ENNReal.ofReal
                  (Real.exp (t * (((a : ℕ) : ℝ) - 2)))) *
                taoPMFENNExpectation (geom2PNatListPMF N) WT :=
              ENNReal.tsum_mul_right
        _ = ENNReal.ofReal (taoGeom2CenteredExpMoment t) *
            (ENNReal.ofReal (taoGeom2CenteredExpMoment t) ^ N) := by
          rw [show (∑' a, geom2PNat a * ENNReal.ofReal
              (Real.exp (t * (((a : ℕ) : ℝ) - 2)))) =
                ENNReal.ofReal (taoGeom2CenteredExpMoment t) by
              simpa [taoPMFENNExpectation] using
                taoGeom2CenteredExpMoment_ennreal ht]
          rw [show taoPMFENNExpectation (geom2PNatListPMF N) WT =
              ENNReal.ofReal (taoGeom2CenteredExpMoment t) ^ N by
                simpa [WT] using ih]
        _ = ENNReal.ofReal (taoGeom2CenteredExpMoment t) ^ (N + 1) := by
          rw [pow_succ']

/-- Real summability and exact centered MGF of the iid Geom(2) list. -/
theorem geom2PNatListPMF_centeredExpMoment
    (N : ℕ) {t : ℝ} (ht : Real.exp t < 2) :
    Summable (fun as : List ℕ+ =>
      (geom2PNatListPMF N as).toReal *
        Real.exp (t * taoGeom2CenteredListWeight as)) ∧
    (∑' as : List ℕ+, (geom2PNatListPMF N as).toReal *
        Real.exp (t * taoGeom2CenteredListWeight as)) =
      taoGeom2CenteredExpMoment t ^ N := by
  let g : List ℕ+ → ENNReal := fun as =>
    geom2PNatListPMF N as *
      ENNReal.ofReal (Real.exp (t * taoGeom2CenteredListWeight as))
  have hnative := geom2PNatListPMF_centeredExpMoment_ennreal N ht
  have hfinite : (∑' as, g as) ≠ ⊤ := by
    rw [show (∑' as, g as) =
      ENNReal.ofReal (taoGeom2CenteredExpMoment t) ^ N by
        simpa [g, taoPMFENNExpectation] using hnative]
    exact ENNReal.pow_ne_top ENNReal.ofReal_ne_top
  have hsumToReal : Summable fun as => (g as).toReal :=
    ENNReal.summable_toReal hfinite
  have hterm : ∀ as,
      (geom2PNatListPMF N as).toReal *
          Real.exp (t * taoGeom2CenteredListWeight as) =
        (g as).toReal := by
    intro as
    simp [g, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.exp_pos _).le]
  have hsum := hsumToReal.congr fun as => (hterm as).symm
  refine ⟨hsum, ?_⟩
  calc
    (∑' as : List ℕ+, (geom2PNatListPMF N as).toReal *
        Real.exp (t * taoGeom2CenteredListWeight as)) =
      ∑' as, (g as).toReal := tsum_congr hterm
    _ = (∑' as, g as).toReal := by
      rw [ENNReal.tsum_toReal_eq]
      intro as
      exact ENNReal.mul_ne_top (PMF.apply_ne_top _ _) ENNReal.ofReal_ne_top
    _ = (ENNReal.ofReal (taoGeom2CenteredExpMoment t) ^ N).toReal := by
      rw [show (∑' as, g as) =
          ENNReal.ofReal (taoGeom2CenteredExpMoment t) ^ N by
        simpa [g, taoPMFENNExpectation] using hnative]
    _ = taoGeom2CenteredExpMoment t ^ N := by
      rw [ENNReal.toReal_pow,
        ENNReal.toReal_ofReal (taoGeom2CenteredExpMoment_nonneg t)]

/-- Quadratic centered MGF bound for a length-`N` iid Geom(2) list. -/
theorem geom2PNatListPMF_centeredExpMoment_le
    (N : ℕ) {t : ℝ} (ht : |t| ≤ 1 / 4) :
    (∑' as : List ℕ+, (geom2PNatListPMF N as).toReal *
        Real.exp (t * taoGeom2CenteredListWeight as)) ≤
      Real.exp (8 * t ^ 2 * N) := by
  have hadm : Real.exp t < 2 := exp_lt_two_of_abs_le_quarter ht
  rw [(geom2PNatListPMF_centeredExpMoment N hadm).2]
  calc
    taoGeom2CenteredExpMoment t ^ N ≤
        Real.exp (8 * t ^ 2) ^ N :=
      pow_le_pow_left₀ (taoGeom2CenteredExpMoment_nonneg t)
        (taoGeom2CenteredExpMoment_le_exp_eight_mul_sq ht) N
    _ = Real.exp (8 * t ^ 2 * N) := by
      rw [← Real.exp_nat_mul]
      congr 1
      ring

/-- One-sided upper tail from the positive centered MGF. -/
theorem geom2PNatListPMF_centeredWeight_upperTail_le
    (N : ℕ) {t lambda : ℝ} (ht : 0 < t) (htsmall : t ≤ 1 / 4) :
    ((geom2PNatListPMF N).toOuterMeasure
        {as | lambda < taoGeom2CenteredListWeight as}).toReal ≤
      Real.exp (-t * lambda + 8 * t ^ 2 * N) := by
  let F : List ℕ+ → ENNReal := fun as =>
    ENNReal.ofReal
      (Real.exp (t * taoGeom2CenteredListWeight as))
  let cutoff : ENNReal := ENNReal.ofReal (Real.exp (t * lambda))
  have htAbs : |t| ≤ 1 / 4 := by
    rw [abs_of_pos ht]
    exact htsmall
  have hadm : Real.exp t < 2 := exp_lt_two_of_abs_le_quarter htAbs
  have hevent :
      {as | cutoff < F as} =
        {as | lambda < taoGeom2CenteredListWeight as} := by
    ext as
    simp only [Set.mem_ofPred_eq, F, cutoff]
    rw [ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _)]
    rw [Real.exp_lt_exp]
    constructor <;> intro h <;> nlinarith
  have hmarkov :=
    tao_pmfToOuterMeasure_gt_mul_le_expectation
      (geom2PNatListPMF N) F cutoff
  rw [hevent] at hmarkov
  have hexpect :
      taoPMFENNExpectation (geom2PNatListPMF N) F =
        ENNReal.ofReal (taoGeom2CenteredExpMoment t) ^ N := by
    simpa [F] using geom2PNatListPMF_centeredExpMoment_ennreal N hadm
  rw [hexpect] at hmarkov
  have hreal := ENNReal.toReal_mono
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hmarkov
  have hmul :
      ((geom2PNatListPMF N).toOuterMeasure
          {as | lambda < taoGeom2CenteredListWeight as}).toReal *
          Real.exp (t * lambda) ≤
        taoGeom2CenteredExpMoment t ^ N := by
    simpa [cutoff, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.exp_pos _).le,
      ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (taoGeom2CenteredExpMoment_nonneg t)] using hreal
  have hpow : taoGeom2CenteredExpMoment t ^ N ≤
      Real.exp (8 * t ^ 2 * N) := by
    calc
      taoGeom2CenteredExpMoment t ^ N ≤ Real.exp (8 * t ^ 2) ^ N :=
        pow_le_pow_left₀ (taoGeom2CenteredExpMoment_nonneg t)
          (taoGeom2CenteredExpMoment_le_exp_eight_mul_sq htAbs) N
      _ = Real.exp (8 * t ^ 2 * N) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  calc
    ((geom2PNatListPMF N).toOuterMeasure
        {as | lambda < taoGeom2CenteredListWeight as}).toReal ≤
        Real.exp (8 * t ^ 2 * N) / Real.exp (t * lambda) := by
      rw [le_div_iff₀ (Real.exp_pos _)]
      exact hmul.trans hpow
    _ = Real.exp (-t * lambda + 8 * t ^ 2 * N) := by
      rw [← Real.exp_sub]
      congr 1
      ring

/-- One-sided lower tail from the negative centered MGF. -/
theorem geom2PNatListPMF_centeredWeight_lowerTail_le
    (N : ℕ) {t lambda : ℝ} (ht : 0 < t) (htsmall : t ≤ 1 / 4) :
    ((geom2PNatListPMF N).toOuterMeasure
        {as | taoGeom2CenteredListWeight as < -lambda}).toReal ≤
      Real.exp (-t * lambda + 8 * t ^ 2 * N) := by
  let F : List ℕ+ → ENNReal := fun as =>
    ENNReal.ofReal
      (Real.exp ((-t) * taoGeom2CenteredListWeight as))
  let cutoff : ENNReal := ENNReal.ofReal (Real.exp (t * lambda))
  have htAbs : |-t| ≤ 1 / 4 := by
    rw [abs_neg, abs_of_pos ht]
    exact htsmall
  have hadm : Real.exp (-t) < 2 := exp_lt_two_of_abs_le_quarter htAbs
  have hevent :
      {as | cutoff < F as} =
        {as | taoGeom2CenteredListWeight as < -lambda} := by
    ext as
    simp only [Set.mem_ofPred_eq, F, cutoff]
    rw [ENNReal.ofReal_lt_ofReal_iff (Real.exp_pos _)]
    rw [Real.exp_lt_exp]
    constructor <;> intro h <;> nlinarith
  have hmarkov :=
    tao_pmfToOuterMeasure_gt_mul_le_expectation
      (geom2PNatListPMF N) F cutoff
  rw [hevent] at hmarkov
  have hexpect :
      taoPMFENNExpectation (geom2PNatListPMF N) F =
        ENNReal.ofReal (taoGeom2CenteredExpMoment (-t)) ^ N := by
    simpa [F] using geom2PNatListPMF_centeredExpMoment_ennreal N hadm
  rw [hexpect] at hmarkov
  have hreal := ENNReal.toReal_mono
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) hmarkov
  have hmul :
      ((geom2PNatListPMF N).toOuterMeasure
          {as | taoGeom2CenteredListWeight as < -lambda}).toReal *
          Real.exp (t * lambda) ≤
        taoGeom2CenteredExpMoment (-t) ^ N := by
    simpa [cutoff, ENNReal.toReal_mul,
      ENNReal.toReal_ofReal (Real.exp_pos _).le,
      ENNReal.toReal_pow,
      ENNReal.toReal_ofReal (taoGeom2CenteredExpMoment_nonneg (-t))] using hreal
  have hpow : taoGeom2CenteredExpMoment (-t) ^ N ≤
      Real.exp (8 * t ^ 2 * N) := by
    calc
      taoGeom2CenteredExpMoment (-t) ^ N ≤ Real.exp (8 * (-t) ^ 2) ^ N :=
        pow_le_pow_left₀ (taoGeom2CenteredExpMoment_nonneg (-t))
          (taoGeom2CenteredExpMoment_le_exp_eight_mul_sq htAbs) N
      _ = Real.exp (8 * t ^ 2 * N) := by
        rw [← Real.exp_nat_mul]
        congr 1
        ring
  calc
    ((geom2PNatListPMF N).toOuterMeasure
        {as | taoGeom2CenteredListWeight as < -lambda}).toReal ≤
        Real.exp (8 * t ^ 2 * N) / Real.exp (t * lambda) := by
      rw [le_div_iff₀ (Real.exp_pos _)]
      exact hmul.trans hpow
    _ = Real.exp (-t * lambda + 8 * t ^ 2 * N) := by
      rw [← Real.exp_sub]
      congr 1
      ring

/-- Two-sided centered tail at an arbitrary admissible positive rate. -/
theorem geom2PNatListPMF_centeredWeight_absTail_le
    (N : ℕ) {t lambda : ℝ} (ht : 0 < t) (htsmall : t ≤ 1 / 4)
    (hlambda : 0 ≤ lambda) :
    ((geom2PNatListPMF N).toOuterMeasure
        {as | lambda < |taoGeom2CenteredListWeight as|}).toReal ≤
      2 * Real.exp (-t * lambda + 8 * t ^ 2 * N) := by
  let Epos : Set (List ℕ+) :=
    {as | lambda < taoGeom2CenteredListWeight as}
  let Eneg : Set (List ℕ+) :=
    {as | taoGeom2CenteredListWeight as < -lambda}
  have hevent :
      {as | lambda < |taoGeom2CenteredListWeight as|} = Epos ∪ Eneg := by
    ext as
    simp only [Set.mem_ofPred_eq, Set.mem_union, Epos, Eneg]
    by_cases hweight : 0 ≤ taoGeom2CenteredListWeight as
    · rw [abs_of_nonneg hweight]
      constructor
      · intro h
        exact Or.inl h
      · rintro (h | h)
        · exact h
        · linarith
    · have hweightNeg : taoGeom2CenteredListWeight as < 0 := lt_of_not_ge hweight
      rw [abs_of_neg hweightNeg]
      constructor
      · intro h
        exact Or.inr (by linarith)
      · rintro (h | h)
        · linarith
        · linarith
  have hunion := MeasureTheory.measure_union_le
    (μ := (geom2PNatListPMF N).toOuterMeasure) Epos Eneg
  rw [← hevent] at hunion
  have hfinite (E : Set (List ℕ+)) :
      (geom2PNatListPMF N).toOuterMeasure E ≠ ⊤ := by
    apply ne_of_lt
    calc
      (geom2PNatListPMF N).toOuterMeasure E ≤
          (geom2PNatListPMF N).toOuterMeasure Set.univ :=
        (geom2PNatListPMF N).toOuterMeasure.mono (Set.subset_univ E)
      _ = 1 := ((geom2PNatListPMF N).toOuterMeasure_apply_eq_one_iff
        Set.univ).2 (Set.subset_univ _)
      _ < ⊤ := ENNReal.one_lt_top
  have hreal := ENNReal.toReal_mono
    (ENNReal.add_ne_top.mpr ⟨hfinite Epos, hfinite Eneg⟩)
    hunion
  rw [ENNReal.toReal_add (hfinite Epos) (hfinite Eneg)] at hreal
  have hpos := geom2PNatListPMF_centeredWeight_upperTail_le
    N (t := t) (lambda := lambda) ht htsmall
  have hneg := geom2PNatListPMF_centeredWeight_lowerTail_le
    N (t := t) (lambda := lambda) ht htsmall
  calc
    ((geom2PNatListPMF N).toOuterMeasure
        {as | lambda < |taoGeom2CenteredListWeight as|}).toReal ≤
        ((geom2PNatListPMF N).toOuterMeasure Epos).toReal +
          ((geom2PNatListPMF N).toOuterMeasure Eneg).toReal := hreal
    _ ≤ Real.exp (-t * lambda + 8 * t ^ 2 * N) +
        Real.exp (-t * lambda + 8 * t ^ 2 * N) := by
      exact add_le_add (by simpa [Epos] using hpos) (by simpa [Eneg] using hneg)
    _ = 2 * Real.exp (-t * lambda + 8 * t ^ 2 * N) := by ring

/-- Rate used to balance the quadratic and linear Geom(2) tails. -/
noncomputable def taoGeom2ChernoffRate (N : ℕ) (lambda : ℝ) : ℝ :=
  min (lambda / (16 * (N : ℝ))) (1 / 4)

theorem taoGeom2ChernoffRate_pos
    {N : ℕ} {lambda : ℝ} (hN : 0 < N) (hlambda : 0 < lambda) :
    0 < taoGeom2ChernoffRate N lambda := by
  unfold taoGeom2ChernoffRate
  apply lt_min
  · positivity
  · norm_num

theorem taoGeom2ChernoffRate_le_quarter (N : ℕ) (lambda : ℝ) :
    taoGeom2ChernoffRate N lambda ≤ 1 / 4 := by
  exact min_le_right _ _

private theorem taoGeom2ChernoffRate_exponent_le
    {N : ℕ} {lambda : ℝ} (hN : 0 < N) (hlambda : 0 < lambda) :
    -taoGeom2ChernoffRate N lambda * lambda +
        8 * taoGeom2ChernoffRate N lambda ^ 2 * N ≤
      -min (lambda ^ 2 / (32 * (N : ℝ))) (lambda / 8) := by
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  by_cases hsmall : lambda ≤ 4 * (N : ℝ)
  · have hrate : taoGeom2ChernoffRate N lambda =
        lambda / (16 * (N : ℝ)) := by
      unfold taoGeom2ChernoffRate
      rw [min_eq_left]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < 16 * N)]
      nlinarith
    have hmin : min (lambda ^ 2 / (32 * (N : ℝ))) (lambda / 8) =
        lambda ^ 2 / (32 * (N : ℝ)) := by
      rw [min_eq_left]
      rw [div_le_div_iff₀ (by positivity : (0 : ℝ) < 32 * N)
        (by norm_num : (0 : ℝ) < 8)]
      nlinarith [mul_pos hlambda hNR]
    rw [hrate, hmin]
    field_simp [hNR.ne']
    ring_nf
    norm_num
  · have hlarge : 4 * (N : ℝ) < lambda := lt_of_not_ge hsmall
    have hrate : taoGeom2ChernoffRate N lambda = 1 / 4 := by
      unfold taoGeom2ChernoffRate
      rw [min_eq_right]
      rw [le_div_iff₀ (by positivity : (0 : ℝ) < 16 * N)]
      nlinarith
    have hmin : min (lambda ^ 2 / (32 * (N : ℝ))) (lambda / 8) =
        lambda / 8 := by
      rw [min_eq_right]
      rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 8)
        (by positivity : (0 : ℝ) < 32 * N)]
      nlinarith [mul_pos hlambda hNR]
    rw [hrate, hmin]
    norm_num
    nlinarith

/-- Optimized two-sided Bernstein-form tail for a positive list length. -/
theorem geom2PNatListPMF_centeredWeight_absTail_le_min
    {N : ℕ} (hN : 0 < N) {lambda : ℝ} (hlambda : 0 < lambda) :
    ((geom2PNatListPMF N).toOuterMeasure
        {as | lambda < |taoGeom2CenteredListWeight as|}).toReal ≤
      2 * Real.exp
        (-min (lambda ^ 2 / (32 * (N : ℝ))) (lambda / 8)) := by
  let t := taoGeom2ChernoffRate N lambda
  have ht : 0 < t := taoGeom2ChernoffRate_pos hN hlambda
  have htsmall : t ≤ 1 / 4 := taoGeom2ChernoffRate_le_quarter N lambda
  have htail := geom2PNatListPMF_centeredWeight_absTail_le
    N ht htsmall hlambda.le
  calc
    ((geom2PNatListPMF N).toOuterMeasure
        {as | lambda < |taoGeom2CenteredListWeight as|}).toReal ≤
      2 * Real.exp (-t * lambda + 8 * t ^ 2 * N) := htail
    _ ≤ 2 * Real.exp
        (-min (lambda ^ 2 / (32 * (N : ℝ))) (lambda / 8)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      apply Real.exp_le_exp.mpr
      exact taoGeom2ChernoffRate_exponent_le hN hlambda

/-- Zero-length list canary. -/
theorem geom2PNatListPMF_centeredExpMoment_zero (t : ℝ) :
    (∑' as : List ℕ+, (geom2PNatListPMF 0 as).toReal *
        Real.exp (t * taoGeom2CenteredListWeight as)) = 1 := by
  rw [tsum_eq_single []]
  · simp [geom2PNatListPMF, taoGeom2CenteredListWeight, taoTupleWeight]
  · intro as hne
    simp [geom2PNatListPMF, hne]

end

end Tao
end Erdos1135
