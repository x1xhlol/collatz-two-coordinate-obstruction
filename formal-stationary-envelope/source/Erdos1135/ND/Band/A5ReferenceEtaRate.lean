import Erdos1135.ND.Band.A5ReferenceEta
import Erdos1135.ND.Band.A5PhysicalPaddingRate
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Scalar decay for the A5 reference-cell guards

This leaf proves the common fixed-total scale and eta bounds for the one A5
reference level.  The estimates are independent of the terminal cell and are
therefore suitable for the scheduler's quantifier order.
-/

namespace Erdos1135
namespace ND

open Filter
open scoped Topology

noncomputable section

private theorem rpow_mul_rpow_eq_rpow_add
    {x : ℝ} (hx : 0 < x) (a b : ℝ) :
    Real.rpow x a * Real.rpow x b = Real.rpow x (a + b) := by
  convert (Real.rpow_add hx a b).symm using 1

private theorem rpow_nat_pow_eq_rpow_mul
    {x : ℝ} (hx : 0 ≤ x) (a : ℝ) (n : ℕ) :
    Real.rpow x a ^ n = Real.rpow x (a * (n : ℝ)) := by
  calc
    Real.rpow x a ^ n =
        Real.rpow (Real.rpow x a) (n : ℝ) :=
      (Real.rpow_natCast (Real.rpow x a) n).symm
    _ = Real.rpow x (a * (n : ℝ)) :=
      (Real.rpow_mul hx a (n : ℝ)).symm

/-- At the common reference level, the fixed-total standard-deviation scale
is eventually at most `log(B)^(7/20)`. -/
theorem eventually_ndFixedTotalRatioScale_reference_le_log_rpow :
    ∀ᶠ B : ℕ in atTop,
      ndFixedTotalRatioScale (ndA5ReferenceLevel B) ≤
        Real.rpow (Real.log B) (7 / 20 : ℝ) := by
  have hlog :
      Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards
    [eventually_ndA5ReferenceLevel_integer_room,
      eventually_ndA5ReferenceLevel_cast_sandwich,
      hlog.eventually_ge_atTop (1 : ℝ)]
      with B hroom hsandwich hlogOne
  let L : ℝ := Real.log B
  let m : ℕ := ndA5ReferenceLevel B
  let S : ℝ := ndFixedTotalRatioScale m
  have hLpos : 0 < L := zero_lt_one.trans_le hlogOne
  have hmOne : 1 ≤ m := (by omega : 1 ≤ m)
  have hmPos : (0 : ℝ) < (m : ℝ) := by positivity
  have hmUpper :
      (m : ℝ) ≤ (1 / 50000 : ℝ) * Real.rpow L (3 / 5 : ℝ) := by
    simpa only [m, L] using hsandwich.2
  have hpowThreeFifths : Real.rpow L (3 / 5 : ℝ) ≤ L := by
    calc
      Real.rpow L (3 / 5 : ℝ) ≤ Real.rpow L (1 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hlogOne (by norm_num)
      _ = L := Real.rpow_one L
  have hmLeL : (m : ℝ) ≤ L := by
    calc
      (m : ℝ) ≤ (1 / 50000 : ℝ) * Real.rpow L (3 / 5 : ℝ) :=
        hmUpper
      _ ≤ (1 / 50000 : ℝ) * L :=
        mul_le_mul_of_nonneg_left hpowThreeFifths (by norm_num)
      _ ≤ L := by nlinarith
  have hlogmLe : Real.log (m : ℝ) ≤ Real.log L :=
    Real.strictMonoOn_log.monotoneOn hmPos hLpos hmLeL
  have hlogLLe : Real.log L ≤ 10 * Real.rpow L (1 / 10 : ℝ) := by
    calc
      Real.log L ≤ Real.rpow L (1 / 10 : ℝ) / (1 / 10 : ℝ) :=
        Real.log_le_rpow_div hLpos.le (by norm_num)
      _ = 10 * Real.rpow L (1 / 10 : ℝ) := by ring
  have hlogmLe' :
      Real.log (m : ℝ) ≤ 10 * Real.rpow L (1 / 10 : ℝ) :=
    hlogmLe.trans hlogLLe
  have hlogm0 : 0 ≤ Real.log (m : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hmOne)
  have hprod :
      (m : ℝ) * Real.log (m : ℝ) ≤ Real.rpow L (7 / 10 : ℝ) := by
    calc
      (m : ℝ) * Real.log (m : ℝ) ≤
          ((1 / 50000 : ℝ) * Real.rpow L (3 / 5 : ℝ)) *
            (10 * Real.rpow L (1 / 10 : ℝ)) :=
        mul_le_mul hmUpper hlogmLe' hlogm0
          (mul_nonneg (by norm_num) (Real.rpow_nonneg hLpos.le _))
      _ = (1 / 5000 : ℝ) * Real.rpow L (7 / 10 : ℝ) := by
        calc
          ((1 / 50000 : ℝ) * Real.rpow L (3 / 5 : ℝ)) *
              (10 * Real.rpow L (1 / 10 : ℝ)) =
            (1 / 5000 : ℝ) *
              (Real.rpow L (3 / 5 : ℝ) *
                Real.rpow L (1 / 10 : ℝ)) := by ring
          _ = (1 / 5000 : ℝ) * Real.rpow L (7 / 10 : ℝ) := by
            congr 1
            convert
              (Real.rpow_add hLpos (3 / 5 : ℝ) (1 / 10 : ℝ)).symm
                using 1
            all_goals norm_num
      _ ≤ Real.rpow L (7 / 10 : ℝ) := by
        have hp0 : 0 ≤ Real.rpow L (7 / 10 : ℝ) :=
          Real.rpow_nonneg hLpos.le _
        nlinarith
  have hS0 : 0 ≤ S := by
    simpa only [S] using ndFixedTotalRatioScale_nonneg m
  have htarget0 : 0 ≤ Real.rpow L (7 / 20 : ℝ) :=
    Real.rpow_nonneg hLpos.le _
  apply (sq_le_sq₀ hS0 htarget0).mp
  rw [show S ^ 2 = (m : ℝ) * Real.log (m : ℝ) by
    simpa only [S] using ndFixedTotalRatioScale_sq hmOne]
  calc
    (m : ℝ) * Real.log (m : ℝ) ≤ Real.rpow L (7 / 10 : ℝ) := hprod
    _ = Real.rpow L (7 / 20 : ℝ) ^ 2 := by
      symm
      calc
        Real.rpow L (7 / 20 : ℝ) ^ 2 =
            Real.rpow (Real.rpow L (7 / 20 : ℝ)) (2 : ℝ) := by
          exact (Real.rpow_natCast (Real.rpow L (7 / 20 : ℝ)) 2).symm
        _ = Real.rpow L ((7 / 20 : ℝ) * (2 : ℝ)) :=
          (Real.rpow_mul hLpos.le (7 / 20 : ℝ) (2 : ℝ)).symm
        _ = Real.rpow L (7 / 10 : ℝ) := by norm_num

/-- A three-term log-power envelope for the common eta parameter. -/
noncomputable def ndA5ReferenceEtaEnvelope (B : ℕ) : ℝ :=
  (57 * 100000 / 340 : ℝ) *
      Real.rpow (Real.log B) (-(1 / 20 : ℝ)) +
    (1021 * 100000 / 340 : ℝ) *
      Real.rpow (Real.log B) (-(3 / 10 : ℝ)) +
    (8 / (1 / 200000 : ℝ) ^ 3) *
      Real.rpow (Real.log B) (-(9 / 5 : ℝ))

/-- The complete common eta bar is eventually dominated by its explicit
three-term log-power envelope. -/
theorem eventually_ndA5ReferenceEtaBar_le_envelope
    (C : ℝ) (hC : 0 < C) :
    ∀ᶠ B : ℕ in atTop,
      ndA5ReferenceEtaBar B C ≤ ndA5ReferenceEtaEnvelope B := by
  have hlog :
      Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards
    [eventually_ndA5ReferenceLevel_integer_room,
      eventually_ndA5ReferenceLevel_cast_sandwich,
      eventually_ndFixedTotalRatioScale_reference_le_log_rpow,
      eventually_ndA5TubeWidth_le_taoSection5TypicalSlack C hC,
      hlog.eventually_ge_atTop (1 : ℝ)]
      with B hroom hsandwich hscale hwidth hlogOne
  let L : ℝ := Real.log B
  let m : ℕ := ndA5ReferenceLevel B
  let S : ℝ := ndFixedTotalRatioScale m
  let W : ℝ := ndA5TubeWidth B C
  let F : ℝ := ndA5ReferenceNuFloor B
  have hLpos : 0 < L := zero_lt_one.trans_le hlogOne
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg _
  have hS0 : 0 ≤ S := by
    simpa only [S] using ndFixedTotalRatioScale_nonneg m
  have hW0 : 0 ≤ W := by
    dsimp only [W, ndA5TubeWidth]
    positivity
  have hFpos : 0 < F := by
    dsimp only [F, ndA5ReferenceNuFloor, L]
    positivity
  have hscale' : S ≤ Real.rpow L (7 / 20 : ℝ) := by
    simpa only [S, m, L] using hscale
  have hwidth' : W ≤ Real.rpow L (3 / 5 : ℝ) := by
    simpa only [W, L, Tao.taoSection5TypicalSlack] using hwidth
  have hfirstPower :
      Real.rpow L (7 / 20 : ℝ) * Real.rpow L (3 / 5 : ℝ) =
        Real.rpow L (19 / 20 : ℝ) := by
    convert rpow_mul_rpow_eq_rpow_add hLpos (7 / 20 : ℝ) (3 / 5 : ℝ)
      using 1
    all_goals norm_num
  have hfirstNum :
      57 * S * W ≤ 57 * Real.rpow L (19 / 20 : ℝ) := by
    calc
      57 * S * W ≤
          57 * Real.rpow L (7 / 20 : ℝ) *
            Real.rpow L (3 / 5 : ℝ) := by
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left hscale' (by norm_num)) hwidth'
          hW0 (mul_nonneg (by norm_num) (Real.rpow_nonneg hLpos.le _))
      _ = 57 * Real.rpow L (19 / 20 : ℝ) := by
        calc
          57 * Real.rpow L (7 / 20 : ℝ) *
              Real.rpow L (3 / 5 : ℝ) =
            57 * (Real.rpow L (7 / 20 : ℝ) *
              Real.rpow L (3 / 5 : ℝ)) := by ring
          _ = 57 * Real.rpow L (19 / 20 : ℝ) := by rw [hfirstPower]
  have hfirstFactor :
      Real.rpow L (-(1 / 20 : ℝ)) * L =
        Real.rpow L (19 / 20 : ℝ) := by
    calc
      Real.rpow L (-(1 / 20 : ℝ)) * L =
          Real.rpow L (-(1 / 20 : ℝ)) * Real.rpow L (1 : ℝ) := by
        congr 1
        exact (Real.rpow_one L).symm
      _ = Real.rpow L (-(1 / 20 : ℝ) + 1) :=
        rpow_mul_rpow_eq_rpow_add hLpos _ _
      _ = Real.rpow L (19 / 20 : ℝ) := by norm_num
  have hfirst :
      57 * S * W / F ≤
        (57 * 100000 / 340 : ℝ) *
          Real.rpow L (-(1 / 20 : ℝ)) := by
    apply (div_le_iff₀ hFpos).2
    calc
      57 * S * W ≤ 57 * Real.rpow L (19 / 20 : ℝ) := hfirstNum
      _ = ((57 * 100000 / 340 : ℝ) *
            Real.rpow L (-(1 / 20 : ℝ))) * F := by
        symm
        calc
          ((57 * 100000 / 340 : ℝ) *
                Real.rpow L (-(1 / 20 : ℝ))) * F =
              57 * (Real.rpow L (-(1 / 20 : ℝ)) * L) := by
            dsimp only [F, ndA5ReferenceNuFloor, L]
            ring
          _ = 57 * Real.rpow L (19 / 20 : ℝ) := by rw [hfirstFactor]
  have hscaleSq : S ^ 2 ≤ Real.rpow L (7 / 10 : ℝ) := by
    calc
      S ^ 2 ≤ Real.rpow L (7 / 20 : ℝ) ^ 2 :=
        pow_le_pow_left₀ hS0 hscale' 2
      _ = Real.rpow L (7 / 10 : ℝ) := by
        convert rpow_nat_pow_eq_rpow_mul hLpos.le (7 / 20 : ℝ) 2
          using 1
        all_goals norm_num
  have hsecondFactor :
      Real.rpow L (-(3 / 10 : ℝ)) * L =
        Real.rpow L (7 / 10 : ℝ) := by
    calc
      Real.rpow L (-(3 / 10 : ℝ)) * L =
          Real.rpow L (-(3 / 10 : ℝ)) * Real.rpow L (1 : ℝ) := by
        congr 1
        exact (Real.rpow_one L).symm
      _ = Real.rpow L (-(3 / 10 : ℝ) + 1) :=
        rpow_mul_rpow_eq_rpow_add hLpos _ _
      _ = Real.rpow L (7 / 10 : ℝ) := by norm_num
  have hsecond :
      1021 * S ^ 2 / F ≤
        (1021 * 100000 / 340 : ℝ) *
          Real.rpow L (-(3 / 10 : ℝ)) := by
    apply (div_le_iff₀ hFpos).2
    calc
      1021 * S ^ 2 ≤ 1021 * Real.rpow L (7 / 10 : ℝ) :=
        mul_le_mul_of_nonneg_left hscaleSq (by norm_num)
      _ = ((1021 * 100000 / 340 : ℝ) *
            Real.rpow L (-(3 / 10 : ℝ))) * F := by
        symm
        calc
          ((1021 * 100000 / 340 : ℝ) *
                Real.rpow L (-(3 / 10 : ℝ))) * F =
              1021 * (Real.rpow L (-(3 / 10 : ℝ)) * L) := by
            dsimp only [F, ndA5ReferenceNuFloor, L]
            ring
          _ = 1021 * Real.rpow L (7 / 10 : ℝ) := by rw [hsecondFactor]
  let base : ℝ := (1 / 200000 : ℝ) * Real.rpow L (3 / 5 : ℝ)
  have hbasePos : 0 < base := by
    dsimp only [base]
    exact mul_pos (by norm_num) (Real.rpow_pos_of_pos hLpos _)
  have hbaseLe : base ≤ (m : ℝ) := by
    simpa only [base, m, L] using hsandwich.1
  have hbaseCube : base ^ 3 ≤ (m : ℝ) ^ 3 :=
    pow_le_pow_left₀ hbasePos.le hbaseLe 3
  have hbaseCubePos : 0 < base ^ 3 := pow_pos hbasePos 3
  have hthirdPre : 8 / (m : ℝ) ^ 3 ≤ 8 / base ^ 3 :=
    div_le_div_of_nonneg_left (by norm_num) hbaseCubePos hbaseCube
  have hpositivePower :
      Real.rpow L (3 / 5 : ℝ) ^ 3 =
        Real.rpow L (9 / 5 : ℝ) := by
    convert rpow_nat_pow_eq_rpow_mul hLpos.le (3 / 5 : ℝ) 3
      using 1
    all_goals norm_num
  have hnegativePower :
      Real.rpow L (-(9 / 5 : ℝ)) =
        (Real.rpow L (9 / 5 : ℝ))⁻¹ := by
    convert Real.rpow_neg hLpos.le (9 / 5 : ℝ) using 1
  have hthirdIdentity :
      8 / base ^ 3 =
        (8 / (1 / 200000 : ℝ) ^ 3) *
          Real.rpow L (-(9 / 5 : ℝ)) := by
    dsimp only [base]
    rw [mul_pow, hpositivePower, hnegativePower]
    have hpNe : Real.rpow L (9 / 5 : ℝ) ≠ 0 :=
      (Real.rpow_pos_of_pos hLpos _).ne'
    field_simp [hpNe]
  have hthird :
      8 / (m : ℝ) ^ 3 ≤
        (8 / (1 / 200000 : ℝ) ^ 3) *
          Real.rpow L (-(9 / 5 : ℝ)) := by
    simpa only [hthirdIdentity] using hthirdPre
  unfold ndA5ReferenceEtaBar ndA5ReferenceEtaEnvelope
  dsimp only [m, S, W, F, L] at hfirst hsecond hthird ⊢
  exact add_le_add (add_le_add hfirst hsecond) hthird

/-- The explicit common eta envelope tends to zero. -/
theorem tendsto_ndA5ReferenceEtaEnvelope_zero :
    Tendsto ndA5ReferenceEtaEnvelope atTop (nhds 0) := by
  have hlog :
      Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hfirst :
      Tendsto
        (fun B : ℕ => Real.rpow (Real.log B) (-(1 / 20 : ℝ)))
        atTop (nhds 0) := by
    simpa only using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 1 / 20)).comp hlog
  have hsecond :
      Tendsto
        (fun B : ℕ => Real.rpow (Real.log B) (-(3 / 10 : ℝ)))
        atTop (nhds 0) := by
    simpa only using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 3 / 10)).comp hlog
  have hthird :
      Tendsto
        (fun B : ℕ => Real.rpow (Real.log B) (-(9 / 5 : ℝ)))
        atTop (nhds 0) := by
    simpa only using
      (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ) < 9 / 5)).comp hlog
  simpa only [ndA5ReferenceEtaEnvelope, mul_zero, zero_add] using
    ((hfirst.const_mul (57 * 100000 / 340 : ℝ)).add
      (hsecond.const_mul (1021 * 100000 / 340 : ℝ))).add
        (hthird.const_mul (8 / (1 / 200000 : ℝ) ^ 3))

/-- For each fixed positive physical tube constant, the common eta bar
eventually enters the exact `25/86` absorption range. -/
theorem eventually_ndA5ReferenceEtaBar_le
    (C : ℝ) (hC : 0 < C) :
    ∀ᶠ B : ℕ in atTop,
      ndA5ReferenceEtaBar B C ≤ 25 / 86 := by
  filter_upwards
    [eventually_ndA5ReferenceEtaBar_le_envelope C hC,
      tendsto_ndA5ReferenceEtaEnvelope_zero.eventually_le_const
        (by norm_num : (0 : ℝ) < 25 / 86)]
      with B hmajor hsmall
  exact hmajor.trans hsmall

/-- The eta threshold also forces the common normalized center majorant into
the fixed-total central scale. -/
theorem ndA5ReferenceCenterBar_le_ratioScale_of_etaBar_le
    {B : ℕ} {C : ℝ}
    (hC : 0 < C)
    (hm : 150 ≤ ndA5ReferenceLevel B)
    (hfloor : 0 < ndA5ReferenceNuFloor B)
    (hetaBar : ndA5ReferenceEtaBar B C ≤ 25 / 86) :
    ndA5ReferenceCenterBar B C ≤
      ndFixedTotalRatioScale (ndA5ReferenceLevel B) := by
  let m : ℕ := ndA5ReferenceLevel B
  let M : ℝ := (m : ℝ)
  let S : ℝ := ndFixedTotalRatioScale m
  let W : ℝ := ndA5TubeWidth B C
  let F : ℝ := ndA5ReferenceNuFloor B
  have hmOne : 1 ≤ m := by omega
  have hMpos : 0 < M := by
    dsimp only [M]
    positivity
  have hS0 : 0 ≤ S := by
    simpa only [S] using ndFixedTotalRatioScale_nonneg m
  have hW0 : 0 ≤ W := by
    dsimp only [W, ndA5TubeWidth]
    positivity
  have hFpos : 0 < F := by simpa only [F] using hfloor
  have hlogOne : 1 ≤ Real.log M := by
    apply (Real.le_log_iff_exp_le hMpos).2
    have hexp : Real.exp 1 ≤ (3 : ℝ) := Real.exp_one_lt_three.le
    have hthree : (3 : ℝ) ≤ M := by
      dsimp only [M, m]
      exact_mod_cast (by omega : 3 ≤ ndA5ReferenceLevel B)
    exact hexp.trans hthree
  have hscaleSq : S ^ 2 = M * Real.log M := by
    dsimp only [S, M]
    simpa only using ndFixedTotalRatioScale_sq hmOne
  have hMLeScaleSq : M ≤ S ^ 2 := by
    rw [hscaleSq]
    nlinarith
  have hfirst0 : 0 ≤ 57 * S * W / F := by positivity
  have hsecond0 : 0 ≤ 1021 * S ^ 2 / F := by positivity
  have hthird0 : 0 ≤ 8 / M ^ 3 := by positivity
  have hfirstLeEtaBar : 57 * S * W / F ≤ ndA5ReferenceEtaBar B C := by
    unfold ndA5ReferenceEtaBar
    dsimp only [m, M, S, W, F] at hsecond0 hthird0 ⊢
    linarith
  have hSWF0 : 0 ≤ S * W / F := by positivity
  have hSWFOne : S * W / F ≤ 1 := by
    have hscaled : 57 * (S * W / F) ≤ 25 / 86 := by
      calc
        57 * (S * W / F) = 57 * S * W / F := by ring
        _ ≤ ndA5ReferenceEtaBar B C := hfirstLeEtaBar
        _ ≤ 25 / 86 := hetaBar
    nlinarith
  unfold ndA5ReferenceCenterBar
  change M * W / F ≤ S
  calc
    M * W / F ≤ S ^ 2 * W / F := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hMLeScaleSq hW0) hFpos.le
    _ = S * (S * W / F) := by ring
    _ ≤ S * 1 := mul_le_mul_of_nonneg_left hSWFOne hS0
    _ = S := mul_one S

end
end ND
end Erdos1135
