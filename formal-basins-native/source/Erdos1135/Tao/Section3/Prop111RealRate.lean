import Erdos1135.Tao.Probability.LogWindowEventualMassLower
import Erdos1135.Tao.Probability.LogWindowFloorPerturbation
import Erdos1135.Tao.Section3.WindowPerturbation
import Erdos1135.Tao.Section5.Prop111NaturalRate

/-!
# Actual-Real Proposition 1.11 Rate

This leaf transports the checked natural-threshold Proposition 1.11 rate to
the genuine real source windows.  The public asymptotic bounds are stated in
the actual real variable `x`; `floor x` appears only in the implementation of
the threshold and source comparison.
-/

namespace Erdos1135
namespace Tao

open Filter
open scoped Topology

noncomputable section

/-- Normalized source error supplied by the sharp floor-window producer. -/
noncomputable def taoProp111FloorSourceError (B : ℕ) : ℝ :=
  96000 / ((B : ℝ) * Real.log (B : ℝ))

private theorem TaoProp111RealFloorWindowMassFacts.alpha_floor_pos
    {x : ℝ} (facts : TaoProp111RealFloorWindowMassFacts x) :
    0 < logFinsetMass
      (taoNyOddWindow
        (((Nat.floor x : ℕ) : ℝ) ^ taoAlpha) taoAlpha) :=
  (div_pos facts.log_floor_pos (by norm_num)).trans_le facts.alpha_floor

private theorem TaoProp111RealFloorWindowMassFacts.alpha_real_pos
    {x : ℝ} (facts : TaoProp111RealFloorWindowMassFacts x) :
    0 < logFinsetMass (taoNyOddWindow (x ^ taoAlpha) taoAlpha) :=
  (div_pos facts.log_floor_pos (by norm_num)).trans_le facts.alpha_real

private theorem TaoProp111RealFloorWindowMassFacts.alphaSq_floor_pos
    {x : ℝ} (facts : TaoProp111RealFloorWindowMassFacts x) :
    0 < logFinsetMass
      (taoNyOddWindow
        (((Nat.floor x : ℕ) : ℝ) ^ (taoAlpha ^ 2)) taoAlpha) :=
  (div_pos facts.log_floor_pos (by norm_num)).trans_le facts.alphaSq_floor

private theorem TaoProp111RealFloorWindowMassFacts.alphaSq_real_pos
    {x : ℝ} (facts : TaoProp111RealFloorWindowMassFacts x) :
    0 < logFinsetMass
      (taoNyOddWindow (x ^ (taoAlpha ^ 2)) taoAlpha) :=
  (div_pos facts.log_floor_pos (by norm_num)).trans_le facts.alphaSq_real

private theorem TaoProp111RealFloorWindowMassFacts.alpha_perturbation
    {x : ℝ} (facts : TaoProp111RealFloorWindowMassFacts x) :
    TaoLogWindowSourcePerturbation
      (taoNyLo (x ^ taoAlpha))
      (taoNyHi (x ^ taoAlpha) taoAlpha)
      (taoNyLo (((Nat.floor x : ℕ) : ℝ) ^ taoAlpha))
      (taoNyHi (((Nat.floor x : ℕ) : ℝ) ^ taoAlpha) taoAlpha)
      (taoProp111FloorSourceError (Nat.floor x)) := by
  intro E
  simpa only [taoNyOddWindow, taoNyLo, taoNyHi,
      taoProp111FloorSourceError, abs_sub_comm] using
    abs_logFinsetProb_taoNyOddWindow_floor_taoAlpha_sub_le
      facts.one_le_x facts.log_floor_pos facts.alpha_floor facts.alpha_real E

private theorem TaoProp111RealFloorWindowMassFacts.alphaSq_perturbation
    {x : ℝ} (facts : TaoProp111RealFloorWindowMassFacts x) :
    TaoLogWindowSourcePerturbation
      (taoNyLo (x ^ (taoAlpha ^ 2)))
      (taoNyHi (x ^ (taoAlpha ^ 2)) taoAlpha)
      (taoNyLo (((Nat.floor x : ℕ) : ℝ) ^ (taoAlpha ^ 2)))
      (taoNyHi (((Nat.floor x : ℕ) : ℝ) ^ (taoAlpha ^ 2)) taoAlpha)
      (taoProp111FloorSourceError (Nat.floor x)) := by
  intro E
  simpa only [taoNyOddWindow, taoNyLo, taoNyHi,
      taoProp111FloorSourceError, abs_sub_comm] using
    abs_logFinsetProb_taoNyOddWindow_floor_taoAlpha_sq_sub_le
      facts.one_le_x facts.log_floor_pos
        facts.alphaSq_floor facts.alphaSq_real E

/-- Above the common mass cutoff, the two real no-hit errors pay one source
perturbation each and the real passage pair pays four source errors in total. -/
theorem taoProp111_real_bounds_of_natural_bounds
    {natNoHitErr natTVErr : ℕ → ℝ}
    (hnat :
      ∀ B lo₁ hi₁ lo₂ hi₂ : ℕ,
        (hB : 1 ≤ B) →
          TaoProp111WindowPair B lo₁ hi₁ lo₂ hi₂ →
            ∀ (hmass₁ : 0 < logFinsetMass (oddLogWindow lo₁ hi₁))
              (hmass₂ : 0 < logFinsetMass (oddLogWindow lo₂ hi₂)),
                syracuseNoHitWindowProb B lo₁ hi₁ hmass₁ ≤ natNoHitErr B ∧
                  syracuseNoHitWindowProb B lo₂ hi₂ hmass₂ ≤ natNoHitErr B ∧
                    syracusePassWindowTV B lo₁ hi₁ lo₂ hi₂ hB
                      hmass₁ hmass₂ ≤ natTVErr B)
    {x : ℝ} {lo₁ hi₁ lo₂ hi₂ : ℕ}
    (facts : TaoProp111RealFloorWindowMassFacts x)
    (hpair : TaoProp111RealWindowPair x lo₁ hi₁ lo₂ hi₂)
    (hrmass₁ : 0 < logFinsetMass (oddLogWindow lo₁ hi₁))
    (hrmass₂ : 0 < logFinsetMass (oddLogWindow lo₂ hi₂)) :
    syracuseNoHitRealWindowProb x lo₁ hi₁ hrmass₁ ≤
        natNoHitErr (Nat.floor x) +
          taoProp111FloorSourceError (Nat.floor x) ∧
      syracuseNoHitRealWindowProb x lo₂ hi₂ hrmass₂ ≤
        natNoHitErr (Nat.floor x) +
          taoProp111FloorSourceError (Nat.floor x) ∧
      syracusePassRealFloorWindowTV x lo₁ hi₁ lo₂ hi₂
          facts.one_le_x hrmass₁ hrmass₂ ≤
        natTVErr (Nat.floor x) +
          4 * taoProp111FloorSourceError (Nat.floor x) := by
  rcases hpair with ⟨rfl, rfl, rfl, rfl⟩
  have hB : 1 ≤ Nat.floor x := one_le_floor_of_one_le facts.one_le_x
  have hx0 : 0 ≤ x := zero_le_one.trans facts.one_le_x
  have hnmass₁ :
      0 < logFinsetMass
        (oddLogWindow (taoNyLo (taoProp111Y1 (Nat.floor x)))
          (taoNyHi (taoProp111Y1 (Nat.floor x)) taoAlpha)) := by
    simpa only [taoProp111Y1, taoNyOddWindow] using facts.alpha_floor_pos
  have hnmass₂ :
      0 < logFinsetMass
        (oddLogWindow (taoNyLo (taoProp111Y2 (Nat.floor x)))
          (taoNyHi (taoProp111Y2 (Nat.floor x)) taoAlpha)) := by
    simpa only [taoProp111Y2, taoNyOddWindow] using facts.alphaSq_floor_pos
  have hnatPair : TaoProp111WindowPair (Nat.floor x)
      (taoNyLo (taoProp111Y1 (Nat.floor x)))
      (taoNyHi (taoProp111Y1 (Nat.floor x)) taoAlpha)
      (taoNyLo (taoProp111Y2 (Nat.floor x)))
      (taoNyHi (taoProp111Y2 (Nat.floor x)) taoAlpha) :=
    ⟨rfl, rfl, rfl, rfl⟩
  rcases hnat (Nat.floor x)
      (taoNyLo (taoProp111Y1 (Nat.floor x)))
      (taoNyHi (taoProp111Y1 (Nat.floor x)) taoAlpha)
      (taoNyLo (taoProp111Y2 (Nat.floor x)))
      (taoNyHi (taoProp111Y2 (Nat.floor x)) taoAlpha)
      hB hnatPair hnmass₁ hnmass₂ with ⟨hno₁, hno₂, htv⟩
  have hperturb₁ := facts.alpha_perturbation
  have hperturb₂ := facts.alphaSq_perturbation
  have hdiff₁ := abs_syracuseNoHitWindowProb_sub_le_of_sourcePerturbation
    (B := Nat.floor x) hrmass₁ hnmass₁ hperturb₁
  have hdiff₂ := abs_syracuseNoHitWindowProb_sub_le_of_sourcePerturbation
    (B := Nat.floor x) hrmass₂ hnmass₂ hperturb₂
  have hdiff₁' :
      syracuseNoHitWindowProb (Nat.floor x)
          (taoNyLo (taoProp111RealY1 x))
          (taoNyHi (taoProp111RealY1 x) taoAlpha) hrmass₁ -
        syracuseNoHitWindowProb (Nat.floor x)
          (taoNyLo (taoProp111Y1 (Nat.floor x)))
          (taoNyHi (taoProp111Y1 (Nat.floor x)) taoAlpha) hnmass₁ ≤
        taoProp111FloorSourceError (Nat.floor x) :=
    (le_abs_self _).trans hdiff₁
  have hdiff₂' :
      syracuseNoHitWindowProb (Nat.floor x)
          (taoNyLo (taoProp111RealY2 x))
          (taoNyHi (taoProp111RealY2 x) taoAlpha) hrmass₂ -
        syracuseNoHitWindowProb (Nat.floor x)
          (taoNyLo (taoProp111Y2 (Nat.floor x)))
          (taoNyHi (taoProp111Y2 (Nat.floor x)) taoAlpha) hnmass₂ ≤
        taoProp111FloorSourceError (Nat.floor x) :=
    (le_abs_self _).trans hdiff₂
  have htv' :
      taoTV
          (syracusePassLocationLaw
            (taoNyLo (taoProp111Y1 (Nat.floor x)))
            (taoNyHi (taoProp111Y1 (Nat.floor x)) taoAlpha)
            (Nat.floor x) hB hnmass₁)
          (syracusePassLocationLaw
            (taoNyLo (taoProp111Y2 (Nat.floor x)))
            (taoNyHi (taoProp111Y2 (Nat.floor x)) taoAlpha)
            (Nat.floor x) hB hnmass₂) ≤ natTVErr (Nat.floor x) := by
    simpa only [syracusePassWindowTV] using htv
  have htvTransfer := taoTV_syracusePassLocationLaw_pair_le_of_sourcePerturbation
    hB hrmass₁ hnmass₁ hnmass₂ hrmass₂ hperturb₁ hperturb₂
  constructor
  · rw [syracuseNoHitRealWindowProb_eq_floor hx0]
    linarith [hdiff₁']
  constructor
  · rw [syracuseNoHitRealWindowProb_eq_floor hx0]
    linarith [hdiff₂']
  · rw [syracusePassRealFloorWindowTV_eq_floor]
    unfold syracusePassWindowTV
    calc
      taoTV
          (syracusePassLocationLaw
            (taoNyLo (taoProp111RealY1 x))
            (taoNyHi (taoProp111RealY1 x) taoAlpha)
            (Nat.floor x) hB hrmass₁)
          (syracusePassLocationLaw
            (taoNyLo (taoProp111RealY2 x))
            (taoNyHi (taoProp111RealY2 x) taoAlpha)
            (Nat.floor x) hB hrmass₂) ≤
          2 * taoProp111FloorSourceError (Nat.floor x) +
            taoTV
              (syracusePassLocationLaw
                (taoNyLo (taoProp111Y1 (Nat.floor x)))
                (taoNyHi (taoProp111Y1 (Nat.floor x)) taoAlpha)
                (Nat.floor x) hB hnmass₁)
              (syracusePassLocationLaw
                (taoNyLo (taoProp111Y2 (Nat.floor x)))
                (taoNyHi (taoProp111Y2 (Nat.floor x)) taoAlpha)
                (Nat.floor x) hB hnmass₂) +
            2 * taoProp111FloorSourceError (Nat.floor x) := htvTransfer
      _ ≤ 2 * taoProp111FloorSourceError (Nat.floor x) +
            natTVErr (Nat.floor x) +
          2 * taoProp111FloorSourceError (Nat.floor x) := by
        exact add_le_add (add_le_add (le_refl _) htv') (le_refl _)
      _ = natTVErr (Nat.floor x) +
          4 * taoProp111FloorSourceError (Nat.floor x) := by ring

/-- Rate-bearing real-threshold socket.  Errors remain indexed by the natural
floor threshold, but both asymptotic estimates are explicitly in real `x`. -/
def TaoRealFirstPassageStabilizationRateSocket
    (RealWindowPair : ℝ → ℕ → ℕ → ℕ → ℕ → Prop) : Prop :=
  ∃ errNoHit errTV : ℕ → ℝ,
    ∃ C c : ℝ,
      0 ≤ C ∧ 0 < c ∧
        (∀ᶠ x : ℝ in atTop,
          0 ≤ errNoHit (Nat.floor x) ∧
            0 ≤ errTV (Nat.floor x) ∧
              errNoHit (Nat.floor x) ≤ C * x ^ (-c) ∧
                errTV (Nat.floor x) ≤ C * (Real.log x) ^ (-c)) ∧
          ∀ x lo₁ hi₁ lo₂ hi₂,
            (hx : 1 ≤ x) →
              RealWindowPair x lo₁ hi₁ lo₂ hi₂ →
                ∀ (hmass₁ : 0 < logFinsetMass (oddLogWindow lo₁ hi₁))
                  (hmass₂ : 0 < logFinsetMass (oddLogWindow lo₂ hi₂)),
                    syracuseNoHitRealWindowProb x lo₁ hi₁ hmass₁ ≤
                        errNoHit (Nat.floor x) ∧
                      syracuseNoHitRealWindowProb x lo₂ hi₂ hmass₂ ≤
                        errNoHit (Nat.floor x) ∧
                      syracusePassRealFloorWindowTV x lo₁ hi₁ lo₂ hi₂ hx
                          hmass₁ hmass₂ ≤ errTV (Nat.floor x)

/-- Concrete actual-real rate statement for Tao's two Proposition 1.11
source windows. -/
def TaoProp111RealFirstPassageStabilizationRateStatement : Prop :=
  TaoRealFirstPassageStabilizationRateSocket TaoProp111RealWindowPair

private theorem half_le_natFloor_cast {x : ℝ} (hx : 2 ≤ x) :
    x / 2 ≤ ((Nat.floor x : ℕ) : ℝ) := by
  have hfloor := Nat.lt_floor_add_one x
  nlinarith

private theorem half_log_le_log_natFloor_cast
    {x : ℝ} (hx : 2 ≤ x) (hlog : 2 ≤ Real.log x) :
    Real.log x / 2 ≤ Real.log ((Nat.floor x : ℕ) : ℝ) := by
  have hxpos : 0 < x := by linarith
  have hxhalfPos : 0 < x / 2 := div_pos hxpos (by norm_num)
  have hhalf := half_le_natFloor_cast hx
  have hfloorPos : 0 < ((Nat.floor x : ℕ) : ℝ) :=
    hxhalfPos.trans_le hhalf
  have hmono := Real.strictMonoOn_log.monotoneOn hxhalfPos hfloorPos hhalf
  rw [Real.log_div hxpos.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hmono
  have hlogTwo : Real.log (2 : ℝ) < 1 := by
    have h := Real.log_lt_sub_one_of_pos
      (show (0 : ℝ) < 2 by norm_num) (show (2 : ℝ) ≠ 1 by norm_num)
    norm_num at h
    exact h
  linarith

private theorem rpow_neg_le_two_rpow_mul_of_half_le
    {a b c d : ℝ} (ha : 0 < a) (haOne : 1 ≤ a)
    (hab : a / 2 ≤ b) (hc : 0 ≤ c) (hdc : d ≤ c) :
    b ^ (-c) ≤ (2 : ℝ) ^ c * a ^ (-d) := by
  have hhalfPos : 0 < a / 2 := div_pos ha (by norm_num)
  have hbase : b ^ (-c) ≤ (a / 2) ^ (-c) :=
    Real.rpow_le_rpow_of_nonpos hhalfPos hab (neg_nonpos.mpr hc)
  have hfactor : (a / 2) ^ (-c) = (2 : ℝ) ^ c * a ^ (-c) := by
    rw [Real.div_rpow ha.le (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2)]
    simp only [div_eq_mul_inv, inv_inv]
    ring
  have hexponent : a ^ (-c) ≤ a ^ (-d) :=
    Real.rpow_le_rpow_of_exponent_le haOne (neg_le_neg hdc)
  calc
    b ^ (-c) ≤ (a / 2) ^ (-c) := hbase
    _ = (2 : ℝ) ^ c * a ^ (-c) := hfactor
    _ ≤ (2 : ℝ) ^ c * a ^ (-d) :=
      mul_le_mul_of_nonneg_left hexponent (Real.rpow_nonneg (by norm_num) _)

private theorem taoProp111FloorSourceError_le_inv_x
    {x : ℝ} (hx : 2 ≤ x)
    (hlogFloor : 1 ≤ Real.log ((Nat.floor x : ℕ) : ℝ)) :
    taoProp111FloorSourceError (Nat.floor x) ≤ 192000 / x := by
  have hxpos : 0 < x := by linarith
  have hhalf := half_le_natFloor_cast hx
  have hfloorNonneg : 0 ≤ ((Nat.floor x : ℕ) : ℝ) := Nat.cast_nonneg _
  have hfloorLeProd : ((Nat.floor x : ℕ) : ℝ) ≤
      ((Nat.floor x : ℕ) : ℝ) *
        Real.log ((Nat.floor x : ℕ) : ℝ) := by
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hlogFloor hfloorNonneg
  have hden : x / 2 ≤
      ((Nat.floor x : ℕ) : ℝ) *
        Real.log ((Nat.floor x : ℕ) : ℝ) := hhalf.trans hfloorLeProd
  unfold taoProp111FloorSourceError
  calc
    96000 /
          (((Nat.floor x : ℕ) : ℝ) *
            Real.log ((Nat.floor x : ℕ) : ℝ)) ≤
        96000 / (x / 2) :=
      div_le_div_of_nonneg_left (by norm_num) (div_pos hxpos (by norm_num)) hden
    _ = 192000 / x := by
      field_simp [hxpos.ne']
      norm_num

private theorem taoProp111FloorSourceError_le_real_power
    {x d : ℝ} (hx : 2 ≤ x)
    (hlogFloor : 1 ≤ Real.log ((Nat.floor x : ℕ) : ℝ))
    (hd : d ≤ 1) :
    taoProp111FloorSourceError (Nat.floor x) ≤ 192000 * x ^ (-d) := by
  have hxOne : 1 ≤ x := by linarith
  have hpow : x ^ (-1 : ℝ) ≤ x ^ (-d) :=
    Real.rpow_le_rpow_of_exponent_le hxOne (neg_le_neg hd)
  calc
    taoProp111FloorSourceError (Nat.floor x) ≤ 192000 / x :=
      taoProp111FloorSourceError_le_inv_x hx hlogFloor
    _ = 192000 * x ^ (-1 : ℝ) := by rw [Real.rpow_neg_one]; ring
    _ ≤ 192000 * x ^ (-d) := mul_le_mul_of_nonneg_left hpow (by norm_num)

private theorem four_mul_taoProp111FloorSourceError_le_real_log_power
    {x d : ℝ} (hx : 2 ≤ x) (hlog : 1 ≤ Real.log x)
    (hlogFloor : 1 ≤ Real.log ((Nat.floor x : ℕ) : ℝ))
    (hd : d ≤ 1) :
    4 * taoProp111FloorSourceError (Nat.floor x) ≤
      768000 * (Real.log x) ^ (-d) := by
  have hxpos : 0 < x := by linarith
  have hlogPos : 0 < Real.log x := zero_lt_one.trans_le hlog
  have hlogLeX : Real.log x ≤ x := by
    have h := Real.log_le_sub_one_of_pos hxpos
    linarith
  have hinv : 1 / x ≤ 1 / Real.log x :=
    one_div_le_one_div_of_le hlogPos hlogLeX
  have hlogPow : (Real.log x) ^ (-1 : ℝ) ≤
      (Real.log x) ^ (-d) :=
    Real.rpow_le_rpow_of_exponent_le hlog (neg_le_neg hd)
  calc
    4 * taoProp111FloorSourceError (Nat.floor x) ≤ 4 * (192000 / x) :=
      mul_le_mul_of_nonneg_left
        (taoProp111FloorSourceError_le_inv_x hx hlogFloor) (by norm_num)
    _ = 768000 * (1 / x) := by ring
    _ ≤ 768000 * (1 / Real.log x) :=
      mul_le_mul_of_nonneg_left hinv (by norm_num)
    _ = 768000 * (Real.log x) ^ (-1 : ℝ) := by
      rw [Real.rpow_neg_one]
      ring
    _ ≤ 768000 * (Real.log x) ^ (-d) :=
      mul_le_mul_of_nonneg_left hlogPow (by norm_num)

/-- Transport any natural Proposition 1.11 rate packet to the genuine real
source windows, with asymptotics expressed in actual real `x`. -/
theorem taoProp111RealFirstPassageStabilizationRate_of_naturalRate
    (hNat : TaoProp111ConcreteFirstPassageStabilizationRateStatement) :
    TaoProp111RealFirstPassageStabilizationRateStatement := by
  rcases hNat with
    ⟨natNoHitErr, natTVErr, C, c, hC, hc, hNatRate, hNatBound⟩
  rcases eventually_atTop.1 hNatRate with ⟨BNat, hBNat⟩
  rcases eventually_atTop.1 eventually_taoProp111RealFloorWindowMassFacts with
    ⟨xMass, hMass⟩
  let B₀ : ℕ := max BNat (Nat.ceil xMass)
  let realNoHitErr : ℕ → ℝ := fun B =>
    if B₀ ≤ B then natNoHitErr B + taoProp111FloorSourceError B else 1
  let realTVErr : ℕ → ℝ := fun B =>
    if B₀ ≤ B then natTVErr B + 4 * taoProp111FloorSourceError B else 2
  let cReal : ℝ := min c 1
  let CReal : ℝ := C * (2 : ℝ) ^ c + 768000
  have hcReal : 0 < cReal := by
    dsimp only [cReal]
    exact lt_min hc (by norm_num)
  have hcRealLeC : cReal ≤ c := by
    exact min_le_left c 1
  have hcRealLeOne : cReal ≤ 1 := by
    exact min_le_right c 1
  have hCReal : 0 ≤ CReal := by
    dsimp only [CReal]
    positivity
  refine ⟨realNoHitErr, realTVErr, CReal, cReal,
    hCReal, hcReal, ?_, ?_⟩
  · have hFloorTendsto : Tendsto (fun x : ℝ => Nat.floor x) atTop atTop :=
      tendsto_nat_floor_atTop
    have hNatRateFloor := hFloorTendsto.eventually hNatRate
    have hFloorLarge := hFloorTendsto.eventually_ge_atTop B₀
    have hlog : Tendsto (fun x : ℝ => Real.log x) atTop atTop :=
      Real.tendsto_log_atTop
    filter_upwards
      [hNatRateFloor, hFloorLarge,
        eventually_taoProp111RealFloorWindowMassFacts,
        eventually_ge_atTop (2 : ℝ), hlog.eventually_ge_atTop (2 : ℝ)]
        with x hnatRate hlarge facts hx hlogTwo
    have hxpos : 0 < x := by linarith
    have hxOne : 1 ≤ x := by linarith
    have hlogOne : 1 ≤ Real.log x := by linarith
    have hfloorHalf := half_le_natFloor_cast hx
    have hlogFloorHalf := half_log_le_log_natFloor_cast hx hlogTwo
    have hfloorLogOne :
        1 ≤ Real.log ((Nat.floor x : ℕ) : ℝ) := by
      linarith [facts.log_floor_large]
    have hqNonneg : 0 ≤ taoProp111FloorSourceError (Nat.floor x) := by
      unfold taoProp111FloorSourceError
      exact div_nonneg (by norm_num)
        (mul_nonneg (Nat.cast_nonneg _)
          (facts.log_floor_pos.le))
    have hpowFloor :
        ((Nat.floor x : ℕ) : ℝ) ^ (-c) ≤
          (2 : ℝ) ^ c * x ^ (-cReal) :=
      rpow_neg_le_two_rpow_mul_of_half_le
        hxpos hxOne hfloorHalf hc.le hcRealLeC
    have hpowLogFloor :
        (Real.log ((Nat.floor x : ℕ) : ℝ)) ^ (-c) ≤
          (2 : ℝ) ^ c * (Real.log x) ^ (-cReal) :=
      rpow_neg_le_two_rpow_mul_of_half_le
        (show 0 < Real.log x by linarith) hlogOne
        hlogFloorHalf hc.le hcRealLeC
    have hqNoHit := taoProp111FloorSourceError_le_real_power
      hx hfloorLogOne hcRealLeOne
    have hqTV := four_mul_taoProp111FloorSourceError_le_real_log_power
      hx hlogOne hfloorLogOne hcRealLeOne
    rw [show realNoHitErr (Nat.floor x) =
        natNoHitErr (Nat.floor x) + taoProp111FloorSourceError (Nat.floor x) by
      simp [realNoHitErr, hlarge],
      show realTVErr (Nat.floor x) =
        natTVErr (Nat.floor x) + 4 * taoProp111FloorSourceError (Nat.floor x) by
      simp [realTVErr, hlarge]]
    refine ⟨add_nonneg hnatRate.1 hqNonneg,
      add_nonneg hnatRate.2.1 (mul_nonneg (by norm_num) hqNonneg), ?_, ?_⟩
    · calc
        natNoHitErr (Nat.floor x) + taoProp111FloorSourceError (Nat.floor x) ≤
            C * (((Nat.floor x : ℕ) : ℝ) ^ (-c)) +
              192000 * x ^ (-cReal) :=
          add_le_add hnatRate.2.2.1 hqNoHit
        _ ≤ C * ((2 : ℝ) ^ c * x ^ (-cReal)) +
              192000 * x ^ (-cReal) :=
          add_le_add (mul_le_mul_of_nonneg_left hpowFloor hC) (le_refl _)
        _ = (C * (2 : ℝ) ^ c + 192000) * x ^ (-cReal) := by ring
        _ ≤ CReal * x ^ (-cReal) := by
          apply mul_le_mul_of_nonneg_right
          · dsimp only [CReal]
            linarith
          · positivity
    · calc
        natTVErr (Nat.floor x) +
            4 * taoProp111FloorSourceError (Nat.floor x) ≤
            C * (Real.log ((Nat.floor x : ℕ) : ℝ)) ^ (-c) +
              768000 * (Real.log x) ^ (-cReal) :=
          add_le_add hnatRate.2.2.2 hqTV
        _ ≤ C * ((2 : ℝ) ^ c * (Real.log x) ^ (-cReal)) +
              768000 * (Real.log x) ^ (-cReal) :=
          add_le_add (mul_le_mul_of_nonneg_left hpowLogFloor hC) (le_refl _)
        _ = CReal * (Real.log x) ^ (-cReal) := by
          dsimp only [CReal]
          ring
  · intro x lo₁ hi₁ lo₂ hi₂ hx hpair hmass₁ hmass₂
    by_cases hlarge : B₀ ≤ Nat.floor x
    · have hx0 : 0 ≤ x := zero_le_one.trans hx
      have hxMass : xMass ≤ x := by
        have hceil : xMass ≤ ((Nat.ceil xMass : ℕ) : ℝ) := Nat.le_ceil xMass
        have hceilFloorNat : Nat.ceil xMass ≤ Nat.floor x :=
          (le_max_right BNat (Nat.ceil xMass)).trans hlarge
        have hceilFloor : ((Nat.ceil xMass : ℕ) : ℝ) ≤
            ((Nat.floor x : ℕ) : ℝ) := by exact_mod_cast hceilFloorNat
        exact hceil.trans (hceilFloor.trans (Nat.floor_le hx0))
      have facts := hMass x hxMass
      rcases taoProp111_real_bounds_of_natural_bounds
          hNatBound facts hpair hmass₁ hmass₂ with ⟨hno₁, hno₂, htv⟩
      rw [show realNoHitErr (Nat.floor x) =
          natNoHitErr (Nat.floor x) + taoProp111FloorSourceError (Nat.floor x) by
        simp [realNoHitErr, hlarge],
        show realTVErr (Nat.floor x) =
          natTVErr (Nat.floor x) + 4 * taoProp111FloorSourceError (Nat.floor x) by
        simp [realTVErr, hlarge]]
      exact ⟨hno₁, hno₂, htv⟩
    · rw [show realNoHitErr (Nat.floor x) = 1 by
          simp [realNoHitErr, hlarge],
        show realTVErr (Nat.floor x) = 2 by simp [realTVErr, hlarge]]
      have hx0 : 0 ≤ x := zero_le_one.trans hx
      constructor
      · rw [syracuseNoHitRealWindowProb_eq_floor hx0]
        exact syracuseNoHitWindowProb_le_one _ _ _ hmass₁
      constructor
      · rw [syracuseNoHitRealWindowProb_eq_floor hx0]
        exact syracuseNoHitWindowProb_le_one _ _ _ hmass₂
      · unfold syracusePassRealFloorWindowTV
        exact taoTV_le_two _ _

/-- Checked actual-real Proposition 1.11 no-hit and passage stabilization
rate, obtained from the checked natural theorem and sharp source transport. -/
theorem taoProp111RealFirstPassageStabilizationRate_checked :
    TaoProp111RealFirstPassageStabilizationRateStatement :=
  taoProp111RealFirstPassageStabilizationRate_of_naturalRate
    taoProp111ConcreteFirstPassageStabilizationRate_checked

end


end Tao
end Erdos1135
