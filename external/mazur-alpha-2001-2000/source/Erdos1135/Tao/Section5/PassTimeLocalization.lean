import Erdos1135.Tao.Section5.PowerInteriorFacts
import Erdos1135.Tao.Section5.DescentScale
import Erdos1135.Tao.Syracuse.AffineCoefficient

/-!
# Section 5 Passage-Time Localization

This leaf uses the repaired multiplicative source interior and full closed
typicality through `n0` to construct a first hit inside the rounded branch
schedule. It contains no target event, lost-window, or probability assembly.
-/

namespace Erdos1135
namespace Tao

open Filter
open scoped Topology

noncomputable section

structure TaoSection5PassTimeLocalizationFacts (B : ℕ) : Prop where
  offset_room : 2 * (3 : ℝ) ^ taoSection5N0 B ≤ (B : ℝ)
  time_margin :
    Real.log (4 / 3 : ℝ) *
          Real.rpow (Real.log B) (4 / 5 : ℝ) +
        Real.log 2 * taoSection5TypicalSlack B +
        Real.log (8 / 3 : ℝ) ≤
      Real.rpow (Real.log B) (9 / 10 : ℝ)

private theorem log_two_lt_one_time : Real.log (2 : ℝ) < 1 := by
  have h := Real.log_lt_sub_one_of_pos
    (show (0 : ℝ) < 2 by norm_num)
    (show (2 : ℝ) ≠ 1 by norm_num)
  norm_num at h ⊢
  exact h

private theorem log_four_thirds_pos_time :
    0 < Real.log (4 / 3 : ℝ) :=
  Real.log_pos (by norm_num)

private theorem log_four_thirds_lt_one_time :
    Real.log (4 / 3 : ℝ) < 1 := by
  have h := Real.log_lt_sub_one_of_pos
    (show (0 : ℝ) < 4 / 3 by norm_num)
    (show (4 / 3 : ℝ) ≠ 1 by norm_num)
  norm_num at h ⊢
  linarith

private theorem log_eight_thirds_eq :
    Real.log (8 / 3 : ℝ) =
      Real.log 2 + Real.log (4 / 3 : ℝ) := by
  rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0)
    (by norm_num : (4 / 3 : ℝ) ≠ 0)]
  norm_num

private theorem log_three_four_eq_neg_log_four_thirds :
    Real.log (3 / 4 : ℝ) = -Real.log (4 / 3 : ℝ) := by
  rw [← Real.log_inv]
  congr 2
  norm_num

private theorem pow_eq_exp_nat_mul_log
    {x : ℝ} (hx : 0 < x) (n : ℕ) :
    x ^ n = Real.exp ((n : ℝ) * Real.log x) := by
  calc
    x ^ n = (Real.exp (Real.log x)) ^ n := by rw [Real.exp_log hx]
    _ = Real.exp ((n : ℝ) * Real.log x) := by rw [← Real.exp_nat_mul]

private theorem natCast_log_nonneg_time (B : ℕ) :
    0 ≤ Real.log (B : ℝ) := by
  by_cases hB : B = 0
  · simp [hB]
  · exact Real.log_nonneg (by exact_mod_cast (Nat.one_le_iff_ne_zero.mpr hB))

private theorem eventually_log_rpow_le_quarter_nine_tenths
    {p : ℝ} (hp : 0 < 9 / 10 - p) :
    ∀ᶠ B : ℕ in atTop,
      Real.rpow (Real.log B) p ≤
        Real.rpow (Real.log B) (9 / 10 : ℝ) / 4 := by
  have hlog :
      Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hratio :
      Tendsto
        (fun B : ℕ => Real.rpow (Real.log B) (-(9 / 10 - p)))
        atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop hp).comp hlog
  filter_upwards
    [hratio.eventually_le_const (by norm_num : (0 : ℝ) < 1 / 4),
      hlog.eventually_gt_atTop (0 : ℝ)] with B hratioB hlogB
  have hlargeNonneg :
      0 ≤ Real.rpow (Real.log B) (9 / 10 : ℝ) :=
    Real.rpow_nonneg hlogB.le _
  have hfactor :
      Real.rpow (Real.log B) p =
        Real.rpow (Real.log B) (-(9 / 10 - p) + 9 / 10) := by
    congr 1
    ring
  have hsplit :
      Real.rpow (Real.log B) (-(9 / 10 - p) + 9 / 10) =
        Real.rpow (Real.log B) (-(9 / 10 - p)) *
          Real.rpow (Real.log B) (9 / 10 : ℝ) :=
    Real.rpow_add hlogB (-(9 / 10 - p)) (9 / 10 : ℝ)
  rw [hfactor, hsplit]
  nlinarith [mul_le_mul_of_nonneg_right hratioB hlargeNonneg]

private theorem eventually_taoSection5PassTimeMargin :
    ∀ᶠ B : ℕ in atTop,
      Real.log (4 / 3 : ℝ) *
            Real.rpow (Real.log B) (4 / 5 : ℝ) +
          Real.log 2 * taoSection5TypicalSlack B +
          Real.log (8 / 3 : ℝ) ≤
        Real.rpow (Real.log B) (9 / 10 : ℝ) := by
  have hlog :
      Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlarge :
      Tendsto
        (fun B : ℕ => Real.rpow (Real.log B) (9 / 10 : ℝ))
        atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 9 / 10)).comp hlog
  filter_upwards
    [eventually_log_rpow_le_quarter_nine_tenths
      (p := (4 / 5 : ℝ)) (by norm_num),
      eventually_log_rpow_le_quarter_nine_tenths
        (p := (3 / 5 : ℝ)) (by norm_num),
      hlarge.eventually_ge_atTop
        (4 * Real.log (8 / 3 : ℝ))]
      with B hfour hthree hconst
  have hfourNonneg :
      0 ≤ Real.rpow (Real.log B) (4 / 5 : ℝ) :=
    Real.rpow_nonneg (natCast_log_nonneg_time B) _
  have hthreeNonneg : 0 ≤ taoSection5TypicalSlack B := by
    unfold taoSection5TypicalSlack
    exact Real.rpow_nonneg (natCast_log_nonneg_time B) _
  have hfourTerm :
      Real.log (4 / 3 : ℝ) * Real.rpow (Real.log B) (4 / 5 : ℝ) ≤
        Real.rpow (Real.log B) (4 / 5 : ℝ) := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right log_four_thirds_lt_one_time.le hfourNonneg
  have hthreeTerm :
      Real.log 2 * taoSection5TypicalSlack B ≤
        taoSection5TypicalSlack B := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right log_two_lt_one_time.le hthreeNonneg
  have hthreeBound :
      taoSection5TypicalSlack B ≤
        Real.rpow (Real.log B) (9 / 10 : ℝ) / 4 := by
    simpa only [taoSection5TypicalSlack] using hthree
  nlinarith

theorem eventually_taoSection5PassTimeLocalizationFacts :
    ∀ᶠ B : ℕ in atTop, TaoSection5PassTimeLocalizationFacts B := by
  filter_upwards
    [eventually_taoSection5DescentScaleFacts,
      eventually_taoSection5PassTimeMargin]
      with B descent hmargin
  have hsmallPower :
      (B : ℝ) ^ (1 / 5 : ℝ) ≤ (B : ℝ) ^ (99 / 100 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le
      (by exact_mod_cast descent.one_le_B) (by norm_num)
  have hoffset : 2 * (3 : ℝ) ^ taoSection5N0 B ≤ (B : ℝ) := by
    calc
      2 * (3 : ℝ) ^ taoSection5N0 B ≤
          2 * (B : ℝ) ^ (1 / 5 : ℝ) := by
        gcongr
        exact descent.offset
      _ = (B : ℝ) ^ (1 / 5 : ℝ) + (B : ℝ) ^ (1 / 5 : ℝ) := by ring
      _ ≤ (B : ℝ) ^ (99 / 100 : ℝ) + (B : ℝ) ^ (1 / 5 : ℝ) :=
        add_le_add_left hsmallPower _
      _ ≤ (B : ℝ) := descent.absorption
  exact ⟨hoffset, hmargin⟩

theorem taoSection5PowerInterior_real_bounds_of_mem
    {B N : ℕ} {branch : TaoSection5SourceBranch}
    (hmem : N ∈ taoSection5PowerInterior B branch) :
    taoSection5PowerInteriorLower B branch ≤ (N : ℝ) ∧
      (N : ℝ) ≤ taoSection5PowerInteriorUpper B branch := by
  rw [mem_taoSection5PowerInterior_iff] at hmem
  constructor
  · exact Nat.ceil_le.mp hmem.1
  · have hupperNonneg : 0 ≤ taoSection5PowerInteriorUpper B branch := by
      unfold taoSection5PowerInteriorUpper
      apply Real.rpow_nonneg
      rw [taoSection5SourceY_eq_branch_rpow]
      exact Real.rpow_nonneg (Nat.cast_nonneg B) _
    exact (Nat.le_floor_iff hupperNonneg).mp hmem.2.1

private theorem TaoSection5TypicalTuple.actual_prefix
    {B r N : ℕ} (hN : Odd N)
    (htyp : taoSection5TypicalTuple B r
      (syracuseValuationPNatList r N hN))
    {j : ℕ} (hj : j ≤ r) :
    taoSection5TypicalTuple B j
      (syracuseValuationPNatList j N hN) := by
  have htake := TaoSection5TypicalTuple.take htyp hj
  simpa only [syracuseValuationPNatList_take_of_le hN hj] using htake

theorem TaoSection5TypicalTuple.actual_prefix_weight_bounds
    {B r N : ℕ} (hN : Odd N)
    (htyp : taoSection5TypicalTuple B r
      (syracuseValuationPNatList r N hN))
    {j : ℕ} (hj : j ≤ r) :
    2 * (j : ℝ) - taoSection5TypicalSlack B ≤
        (taoTupleWeight (syracuseValuationPNatList j N hN) : ℝ) ∧
      (taoTupleWeight (syracuseValuationPNatList j N hN) : ℝ) ≤
        2 * (j : ℝ) + taoSection5TypicalSlack B := by
  have htypJ := TaoSection5TypicalTuple.actual_prefix hN htyp hj
  have htake :
      (syracuseValuationPNatList j N hN).take j =
        syracuseValuationPNatList j N hN := by
    simpa only [syracuseValuationPNatList_length] using
      (List.take_length (l := syracuseValuationPNatList j N hN))
  have hdev := htypJ.2 j le_rfl
  rw [htake] at hdev
  constructor <;> linarith [abs_le.mp hdev]

private theorem TaoSection5PassTimeLocalizationFacts.branch_margin
    {B : ℕ} (time : TaoSection5PassTimeLocalizationFacts B)
    (geom : TaoSection5PowerInteriorFacts B)
    (branch : TaoSection5SourceBranch) :
    Real.log (4 / 3 : ℝ) * Real.rpow (Real.log B) (4 / 5 : ℝ) +
        Real.log 2 * taoSection5TypicalSlack B + Real.log (8 / 3 : ℝ) ≤
      taoSection5PowerInteriorDelta B *
        Real.log (taoSection5SourceY B branch) := by
  have hBne : B ≠ 1 := by
    intro hB
    subst B
    have hdelta := geom.delta_pos
    norm_num [taoSection5PowerInteriorDelta] at hdelta
  have hBgt : 1 < B := lt_of_le_of_ne geom.schedule.one_le_B hBne.symm
  have hBnatPos : 0 < B := by omega
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hBnatPos
  have hlogPos : 0 < Real.log B := Real.log_pos (by exact_mod_cast hBgt)
  have hlogY :
      Real.log (taoSection5SourceY B branch) =
        taoSection5BranchExponent branch * Real.log B := by
    rw [taoSection5SourceY_eq_branch_rpow]
    exact Real.log_rpow hBpos _
  have hfactor :
      Real.rpow (Real.log B) (9 / 10 : ℝ) =
        taoSection5PowerInteriorDelta B * Real.log B := by
    unfold taoSection5PowerInteriorDelta
    have hadd := Real.rpow_add hlogPos (-1 / 10 : ℝ) (1 : ℝ)
    calc
      Real.rpow (Real.log B) (9 / 10 : ℝ) =
          Real.rpow (Real.log B) ((-1 / 10 : ℝ) + 1) := by norm_num
      _ = Real.rpow (Real.log B) (-1 / 10 : ℝ) *
          Real.rpow (Real.log B) (1 : ℝ) := hadd
      _ = Real.rpow (Real.log B) (-1 / 10 : ℝ) * Real.log B := by
        congr 1
        exact Real.rpow_one (Real.log B)
  have hbranch :
      Real.log B ≤ taoSection5BranchExponent branch * Real.log B := by
    simpa only [one_mul] using
      mul_le_mul_of_nonneg_right
        (one_le_taoSection5BranchExponent branch) hlogPos.le
  have hdeltaNonneg : 0 ≤ taoSection5PowerInteriorDelta B := geom.delta_pos.le
  have hlarge :
      Real.rpow (Real.log B) (9 / 10 : ℝ) ≤
        taoSection5PowerInteriorDelta B *
          Real.log (taoSection5SourceY B branch) := by
    rw [hfactor, hlogY]
    exact mul_le_mul_of_nonneg_left hbranch hdeltaNonneg
  exact time.time_margin.trans hlarge

private theorem real_ofNat_eq_exp_log {N : ℕ} (hN : 0 < N) :
    (N : ℝ) = Real.exp (Real.log (N : ℝ)) :=
  (Real.exp_log (by exact_mod_cast hN)).symm

private theorem taoSection5_passLower_le_of_firstHit
    {B n N : ℕ} {branch : TaoSection5SourceBranch}
    (geom : TaoSection5PowerInteriorFacts B)
    (time : TaoSection5PassTimeLocalizationFacts B)
    (hN : Odd N)
    (hmem : N ∈ taoSection5PowerInterior B branch)
    (hn0 : n ≤ taoSection5N0 B)
    (htyp : taoSection5TypicalTuple B (taoSection5N0 B)
      (syracuseValuationPNatList (taoSection5N0 B) N hN))
    (hfirst : syracuseFirstHitAtMost B N n) :
    taoSection5PassLower B branch ≤ (n : ℝ) := by
  have htypN := TaoSection5TypicalTuple.actual_prefix hN htyp hn0
  have hweight :=
    (TaoSection5TypicalTuple.actual_prefix_weight_bounds hN htyp hn0).2
  have hcoeff :=
    exp_neg_log_two_mul_mul_three_four_pow_le_three_pow_div_two_pow
      (q := n)
      (w := taoTupleWeight (syracuseValuationPNatList n N hN))
      (H := taoSection5TypicalSlack B) hweight
  have hmainQ := affineMainTerm_le_syracuse_iterate n N hN
  have hmainR :
      ((3 : ℝ) ^ n /
          (2 : ℝ) ^ taoTupleWeight (syracuseValuationPNatList n N hN)) *
          (N : ℝ) ≤ ((syracuse^[n]) N : ℝ) := by
    have hcast := (Rat.cast_le (K := ℝ)).2 hmainQ
    norm_num at hcast ⊢
    exact hcast
  have hterminal : ((syracuse^[n]) N : ℝ) ≤ (B : ℝ) := by
    exact_mod_cast hfirst.1
  have hlowMain :
      (Real.exp (-Real.log 2 * taoSection5TypicalSlack B) *
        (3 / 4 : ℝ) ^ n) * (N : ℝ) ≤ (B : ℝ) := by
    calc
      _ ≤ ((3 : ℝ) ^ n /
          (2 : ℝ) ^ taoTupleWeight (syracuseValuationPNatList n N hN)) *
          (N : ℝ) :=
        mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg N)
      _ ≤ ((syracuse^[n]) N : ℝ) := hmainR
      _ ≤ (B : ℝ) := hterminal
  let inverse : ℝ :=
    Real.exp (Real.log 2 * taoSection5TypicalSlack B) * (4 / 3 : ℝ) ^ n
  have hinverse :
      inverse *
          (Real.exp (-Real.log 2 * taoSection5TypicalSlack B) *
            (3 / 4 : ℝ) ^ n) = 1 := by
    dsimp [inverse]
    calc
      _ = (Real.exp (Real.log 2 * taoSection5TypicalSlack B) *
            Real.exp (-Real.log 2 * taoSection5TypicalSlack B)) *
          ((4 / 3 : ℝ) ^ n * (3 / 4 : ℝ) ^ n) := by ring
      _ = 1 := by
        rw [← Real.exp_add, ← mul_pow]
        norm_num
  have hNupper : (N : ℝ) ≤ inverse * (B : ℝ) := by
    calc
      (N : ℝ) = inverse *
          ((Real.exp (-Real.log 2 * taoSection5TypicalSlack B) *
            (3 / 4 : ℝ) ^ n) * (N : ℝ)) := by
        rw [← mul_assoc, hinverse, one_mul]
      _ ≤ inverse * (B : ℝ) :=
        mul_le_mul_of_nonneg_left hlowMain (by positivity)
  have hinterior := taoSection5PowerInterior_real_bounds_of_mem hmem
  have hsourcePos : 0 < taoSection5SourceY B branch := by
    rw [taoSection5SourceY_eq_branch_rpow]
    exact Real.rpow_pos_of_pos
      (by exact_mod_cast geom.schedule.one_le_B) _
  have hBpos : (0 : ℝ) < B := by
    exact_mod_cast geom.schedule.one_le_B
  have hpowerExp :
      taoSection5PowerInteriorLower B branch =
        Real.exp ((1 + taoSection5PowerInteriorDelta B) *
          Real.log (taoSection5SourceY B branch)) := by
    unfold taoSection5PowerInteriorLower
    calc
      _ = Real.exp (Real.log (taoSection5SourceY B branch) *
          (1 + taoSection5PowerInteriorDelta B)) :=
        Real.rpow_def_of_pos hsourcePos _
      _ = _ := by
        congr 1
        ring
  have hinverseExp :
      inverse * (B : ℝ) =
        Real.exp
          (Real.log 2 * taoSection5TypicalSlack B +
            (n : ℝ) * Real.log (4 / 3 : ℝ) + Real.log B) := by
    have hBexp : (B : ℝ) = Real.exp (Real.log B) :=
      real_ofNat_eq_exp_log
        (lt_of_lt_of_le Nat.zero_lt_one geom.schedule.one_le_B)
    dsimp [inverse]
    rw [pow_eq_exp_nat_mul_log (by norm_num : (0 : ℝ) < 4 / 3)]
    calc
      Real.exp (Real.log 2 * taoSection5TypicalSlack B) *
            Real.exp ((n : ℝ) * Real.log (4 / 3 : ℝ)) * (B : ℝ) =
          Real.exp (Real.log 2 * taoSection5TypicalSlack B) *
            Real.exp ((n : ℝ) * Real.log (4 / 3 : ℝ)) *
              Real.exp (Real.log B) :=
        congrArg
          (fun x : ℝ => Real.exp (Real.log 2 * taoSection5TypicalSlack B) *
            Real.exp ((n : ℝ) * Real.log (4 / 3 : ℝ)) * x) hBexp
      _ = _ := by rw [← Real.exp_add, ← Real.exp_add]
  have hexpLe :
      Real.exp ((1 + taoSection5PowerInteriorDelta B) *
          Real.log (taoSection5SourceY B branch)) ≤
        Real.exp
          (Real.log 2 * taoSection5TypicalSlack B +
            (n : ℝ) * Real.log (4 / 3 : ℝ) + Real.log B) := by
    rw [← hpowerExp, ← hinverseExp]
    exact hinterior.1.trans hNupper
  have hexponents := Real.exp_le_exp.mp hexpLe
  have hmargin := time.branch_margin geom branch
  have hlog8Nonneg : 0 ≤ Real.log (8 / 3 : ℝ) :=
    Real.log_nonneg (by norm_num)
  have hscaled :
      Real.log (taoSection5SourceY B branch / (B : ℝ)) +
          Real.log (4 / 3 : ℝ) *
            Real.rpow (Real.log B) (4 / 5 : ℝ) ≤
        Real.log (4 / 3 : ℝ) * (n : ℝ) := by
    rw [Real.log_div hsourcePos.ne' hBpos.ne']
    nlinarith [hlog8Nonneg]
  unfold taoSection5PassLower
  calc
    Real.log (taoSection5SourceY B branch / (B : ℝ)) /
          Real.log (4 / 3 : ℝ) +
        Real.rpow (Real.log B) (4 / 5 : ℝ) =
      (Real.log (taoSection5SourceY B branch / (B : ℝ)) +
        Real.log (4 / 3 : ℝ) *
          Real.rpow (Real.log B) (4 / 5 : ℝ)) /
        Real.log (4 / 3 : ℝ) := by field_simp
    _ ≤ (Real.log (4 / 3 : ℝ) * (n : ℝ)) /
        Real.log (4 / 3 : ℝ) :=
      (div_le_div_iff_of_pos_right log_four_thirds_pos_time).2 hscaled
    _ = (n : ℝ) := by field_simp

private theorem taoSection5_iterate_floor_passUpper_le
    {B N : ℕ} {branch : TaoSection5SourceBranch}
    (geom : TaoSection5PowerInteriorFacts B)
    (time : TaoSection5PassTimeLocalizationFacts B)
    (hN : Odd N)
    (hmem : N ∈ taoSection5PowerInterior B branch)
    (htyp : taoSection5TypicalTuple B (taoSection5N0 B)
      (syracuseValuationPNatList (taoSection5N0 B) N hN)) :
    (syracuse^[Nat.floor (taoSection5PassUpper B branch)]) N ≤ B := by
  let k := Nat.floor (taoSection5PassUpper B branch)
  rcases geom.schedule.nonempty branch with ⟨w, hw⟩
  rw [mem_taoSection5PassTimes_iff] at hw
  have hkMem : k ∈ taoSection5PassTimes B branch := by
    apply mem_taoSection5PassTimes_iff.mpr
    exact ⟨by simpa only [k] using hw.1.trans hw.2, le_rfl⟩
  have hk0 : k ≤ taoSection5N0 B :=
    (geom.schedule.range branch k hkMem).2
  have hweight :=
    (TaoSection5TypicalTuple.actual_prefix_weight_bounds hN htyp hk0).1
  have hcoeff :=
    three_pow_div_two_pow_le_exp_log_two_mul_mul_three_four_pow
      (q := k)
      (w := taoTupleWeight (syracuseValuationPNatList k N hN))
      (H := taoSection5TypicalSlack B) hweight
  have henvelopeQ := syracuse_iterate_le_affine_envelope k N hN
  have henvelopeR :
      ((syracuse^[k]) N : ℝ) ≤
        ((3 : ℝ) ^ k /
          (2 : ℝ) ^ taoTupleWeight (syracuseValuationPNatList k N hN)) *
          (N : ℝ) + (3 : ℝ) ^ k := by
    have hcast := (Rat.cast_le (K := ℝ)).2 henvelopeQ
    norm_num at hcast ⊢
    exact hcast
  have hinterior := taoSection5PowerInterior_real_bounds_of_mem hmem
  have hsourcePos : 0 < taoSection5SourceY B branch := by
    rw [taoSection5SourceY_eq_branch_rpow]
    exact Real.rpow_pos_of_pos
      (by exact_mod_cast geom.schedule.one_le_B) _
  have hpowerUpperPos : 0 < taoSection5PowerInteriorUpper B branch := by
    unfold taoSection5PowerInteriorUpper
    exact Real.rpow_pos_of_pos hsourcePos _
  have hmainReplace :
      ((3 : ℝ) ^ k /
          (2 : ℝ) ^ taoTupleWeight (syracuseValuationPNatList k N hN)) *
          (N : ℝ) ≤
        (Real.exp (Real.log 2 * taoSection5TypicalSlack B) *
          (3 / 4 : ℝ) ^ k) * taoSection5PowerInteriorUpper B branch := by
    calc
      _ ≤ (Real.exp (Real.log 2 * taoSection5TypicalSlack B) *
          (3 / 4 : ℝ) ^ k) * (N : ℝ) :=
        mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg N)
      _ ≤ _ := mul_le_mul_of_nonneg_left hinterior.2 (by positivity)
  have hBpos : (0 : ℝ) < B := by
    exact_mod_cast geom.schedule.one_le_B
  have hlogYalpha :
      Real.log
          (Real.rpow (taoSection5SourceY B branch) taoAlpha) =
        taoAlpha * Real.log (taoSection5SourceY B branch) :=
    Real.log_rpow hsourcePos _
  have houterPos :
      0 < Real.rpow (taoSection5SourceY B branch) taoAlpha :=
    Real.rpow_pos_of_pos hsourcePos _
  have hfloor := Nat.lt_floor_add_one (taoSection5PassUpper B branch)
  have hfloorDiv :
      Real.log
          (Real.rpow (taoSection5SourceY B branch) taoAlpha / (B : ℝ)) /
          Real.log (4 / 3 : ℝ) <
        (k : ℝ) + 1 + Real.rpow (Real.log B) (4 / 5 : ℝ) := by
    dsimp [k]
    unfold taoSection5PassUpper at hfloor ⊢
    simpa [add_assoc, add_comm, add_left_comm] using
      (sub_lt_iff_lt_add.mp hfloor)
  have hfloorScaled :=
    (div_lt_iff₀ log_four_thirds_pos_time).mp hfloorDiv
  have hmargin := time.branch_margin geom branch
  have hmainExponent :
      Real.log 2 * taoSection5TypicalSlack B -
          (k : ℝ) * Real.log (4 / 3 : ℝ) +
          (taoAlpha - taoSection5PowerInteriorDelta B) *
            Real.log (taoSection5SourceY B branch) <
        Real.log B - Real.log 2 := by
    rw [Real.log_div houterPos.ne' hBpos.ne', hlogYalpha] at hfloorScaled
    rw [log_eight_thirds_eq] at hmargin
    nlinarith
  have hmainHalf :
      (Real.exp (Real.log 2 * taoSection5TypicalSlack B) *
          (3 / 4 : ℝ) ^ k) * taoSection5PowerInteriorUpper B branch <
        (B : ℝ) / 2 := by
    have hupperExp :
        taoSection5PowerInteriorUpper B branch =
          Real.exp (Real.log (taoSection5SourceY B branch) *
            (taoAlpha - taoSection5PowerInteriorDelta B)) := by
      unfold taoSection5PowerInteriorUpper
      exact Real.rpow_def_of_pos hsourcePos _
    rw [hupperExp,
      pow_eq_exp_nat_mul_log (by norm_num : (0 : ℝ) < 3 / 4),
      ← Real.exp_add, ← Real.exp_add,
      log_three_four_eq_neg_log_four_thirds]
    calc
      Real.exp
          (Real.log 2 * taoSection5TypicalSlack B +
            (k : ℝ) * -Real.log (4 / 3 : ℝ) +
            Real.log (taoSection5SourceY B branch) *
              (taoAlpha - taoSection5PowerInteriorDelta B)) <
          Real.exp (Real.log B - Real.log 2) :=
        Real.exp_lt_exp.mpr (by nlinarith [hmainExponent])
      _ = (B : ℝ) / 2 := by
        rw [Real.exp_sub, Real.exp_log hBpos,
          Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hoffset : (3 : ℝ) ^ k ≤ (B : ℝ) / 2 := by
    have hpow : (3 : ℝ) ^ k ≤ (3 : ℝ) ^ taoSection5N0 B := by
      exact pow_le_pow_right₀ (by norm_num) hk0
    nlinarith [time.offset_room]
  have hstateReal : ((syracuse^[k]) N : ℝ) ≤ (B : ℝ) := by
    calc
      _ ≤ ((3 : ℝ) ^ k /
          (2 : ℝ) ^ taoTupleWeight (syracuseValuationPNatList k N hN)) *
          (N : ℝ) + (3 : ℝ) ^ k := henvelopeR
      _ ≤ (Real.exp (Real.log 2 * taoSection5TypicalSlack B) *
          (3 / 4 : ℝ) ^ k) * taoSection5PowerInteriorUpper B branch +
          (3 : ℝ) ^ k := add_le_add_left hmainReplace _
      _ ≤ (B : ℝ) := by linarith
  exact_mod_cast hstateReal

/-- The repaired interior and full closed typicality produce a least hit in
the rounded branch schedule. -/
theorem exists_taoSection5_firstHit_mem_passTimes
    {B N : ℕ} {branch : TaoSection5SourceBranch}
    (geom : TaoSection5PowerInteriorFacts B)
    (time : TaoSection5PassTimeLocalizationFacts B)
    (hN : Odd N)
    (hmem : N ∈ taoSection5PowerInterior B branch)
    (htyp : taoSection5TypicalTuple B (taoSection5N0 B)
      (syracuseValuationPNatList (taoSection5N0 B) N hN)) :
    ∃ n, n ∈ taoSection5PassTimes B branch ∧
      syracuseFirstHitAtMost B N n := by
  let k := Nat.floor (taoSection5PassUpper B branch)
  have hkHit : (syracuse^[k]) N ≤ B := by
    simpa only [k] using
      taoSection5_iterate_floor_passUpper_le geom time hN hmem htyp
  let hits : syracuseHitsAtMost N B := ⟨k, hkHit⟩
  let n := syracuseFirstPassageTime N B hits
  have hfirst : syracuseFirstHitAtMost B N n :=
    syracuseFirstHitAtMost_of_hitsAtMost N B hits
  have hnk : n ≤ k := by
    by_contra hnot
    have hkn : k < n := Nat.lt_of_not_ge hnot
    exact (Nat.not_lt_of_ge hkHit) (hfirst.2 k hkn)
  have hkMem : k ∈ taoSection5PassTimes B branch := by
    rcases geom.schedule.nonempty branch with ⟨w, hw⟩
    rw [mem_taoSection5PassTimes_iff] at hw
    apply mem_taoSection5PassTimes_iff.mpr
    exact ⟨by simpa only [k] using hw.1.trans hw.2, le_rfl⟩
  have hn0 : n ≤ taoSection5N0 B :=
    hnk.trans (geom.schedule.range branch k hkMem).2
  have hlower :=
    taoSection5_passLower_le_of_firstHit
      geom time hN hmem hn0 htyp hfirst
  refine ⟨n, mem_taoSection5PassTimes_iff.mpr ?_, hfirst⟩
  exact
    ⟨Nat.ceil_le.mpr hlower,
      hnk.trans (by simpa only [k] using le_rfl)⟩

theorem taoSection5_firstHit_mem_passTimes
    {B n N : ℕ} {branch : TaoSection5SourceBranch}
    (geom : TaoSection5PowerInteriorFacts B)
    (time : TaoSection5PassTimeLocalizationFacts B)
    (hN : Odd N)
    (hmem : N ∈ taoSection5PowerInterior B branch)
    (htyp : taoSection5TypicalTuple B (taoSection5N0 B)
      (syracuseValuationPNatList (taoSection5N0 B) N hN))
    (hfirst : syracuseFirstHitAtMost B N n) :
    n ∈ taoSection5PassTimes B branch := by
  rcases exists_taoSection5_firstHit_mem_passTimes
      geom time hN hmem htyp with ⟨m, hm, hmFirst⟩
  have hnm := syracuseFirstHitAtMost_unique hfirst hmFirst
  simpa only [hnm] using hm

theorem taoSection5_firstHit_mem_passTimes_of_sourceTypical
    {B n N : ℕ} {branch : TaoSection5SourceBranch}
    (geom : TaoSection5PowerInteriorFacts B)
    (time : TaoSection5PassTimeLocalizationFacts B)
    (hN : Odd N)
    (hmem : N ∈ taoSection5PowerInterior B branch)
    (htyp : taoSection5SourceTypicalTuple B (taoSection5N0 B)
      (syracuseValuationPNatList (taoSection5N0 B) N hN))
    (hfirst : syracuseFirstHitAtMost B N n) :
    n ∈ taoSection5PassTimes B branch :=
  taoSection5_firstHit_mem_passTimes geom time hN hmem
    (TaoSection5SourceTypicalTuple.to_closed htyp) hfirst

theorem eventually_taoSection5_firstHit_mem_passTimes :
    ∀ᶠ B : ℕ in atTop,
      ∀ {N : ℕ} {branch : TaoSection5SourceBranch} (hN : Odd N),
        N ∈ taoSection5PowerInterior B branch →
        taoSection5TypicalTuple B (taoSection5N0 B)
          (syracuseValuationPNatList (taoSection5N0 B) N hN) →
        ∀ {n : ℕ}, syracuseFirstHitAtMost B N n →
          n ∈ taoSection5PassTimes B branch := by
  filter_upwards
    [eventually_taoSection5PowerInteriorFacts,
      eventually_taoSection5PassTimeLocalizationFacts]
      with B geom time
  intro N branch hN hmem htyp n hfirst
  exact taoSection5_firstHit_mem_passTimes geom time hN hmem htyp hfirst

end

end Tao
end Erdos1135
