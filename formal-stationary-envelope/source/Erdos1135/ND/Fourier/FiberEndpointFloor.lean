import Erdos1135.ND.Fourier.FiberConditioning
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Int.NatAbs

/-!
# Fixed-Fiber Endpoint Floors

This leaf starts the denominator-floor part of pilot P1.  It keeps the
natural-logarithm window visible, records the exact adjacent endpoint ratio,
and proves a first checked central lower bound from Mathlib's central-binomial
estimate.  The off-centre telescope is developed here rather than hidden in
the later conditioned-M1 assembly.
-/

namespace Erdos1135
namespace ND

open Tao

/-- The natural-logarithm central window in the frozen v10 M1 statement. -/
def ndSection7M1Window (K : ℝ) (n L : ℕ) : Prop :=
  |(L : ℝ) - 2 * (n : ℝ)| ≤
    K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ))

/-- Natural denominator-loss exponent used by the conditioned-M1 assembly. -/
noncomputable def ndSection7M1FloorExponent (K : ℝ) : ℕ :=
  ⌈K ^ 2⌉₊ + 1

/-- Fixed positive denominator-floor constant used by conditioned M1. -/
noncomputable def ndSection7M1FloorConstant : ℝ :=
  Real.exp (-1) / 4

/-- Natural displacement of an endpoint from the central weight `2*n`. -/
def ndGeom2CentralDisplacement (n L : ℕ) : ℕ :=
  Int.natAbs ((L : ℤ) - ((2 * n : ℕ) : ℤ))

@[simp]
theorem cast_ndGeom2CentralDisplacement (n L : ℕ) :
    (ndGeom2CentralDisplacement n L : ℝ) =
      |(L : ℝ) - 2 * (n : ℝ)| := by
  simp [ndGeom2CentralDisplacement]

theorem ndGeom2CentralDisplacement_eq_sub_of_two_mul_le
    {n L : ℕ} (h : 2 * n ≤ L) :
    ndGeom2CentralDisplacement n L = L - 2 * n := by
  simpa [ndGeom2CentralDisplacement] using
    (Int.natAbs_natCast_sub_natCast_of_ge (a := L) (b := 2 * n) h)

theorem ndGeom2CentralDisplacement_eq_sub_of_le_two_mul
    {n L : ℕ} (h : L ≤ 2 * n) :
    ndGeom2CentralDisplacement n L = 2 * n - L := by
  simpa [ndGeom2CentralDisplacement] using
    (Int.natAbs_natCast_sub_natCast_of_le (a := L) (b := 2 * n) h)

/-- Every endpoint is its central value plus or minus its natural
displacement. -/
theorem ndGeom2CentralDisplacement_split (n L : ℕ) :
    2 * n + ndGeom2CentralDisplacement n L = L ∨
      L + ndGeom2CentralDisplacement n L = 2 * n := by
  rcases le_total (2 * n) L with h | h
  · left
    rw [ndGeom2CentralDisplacement_eq_sub_of_two_mul_le h]
    omega
  · right
    rw [ndGeom2CentralDisplacement_eq_sub_of_le_two_mul h]
    omega

/-- Exact one-step ratio for the negative-binomial endpoint law. -/
theorem ndGeom2EndpointMass_succ
    {n L : ℕ} (hn : 0 < n) (hL : n ≤ L) :
    ndGeom2EndpointMass n (L + 1) =
      ndGeom2EndpointMass n L *
        (L : ℝ) / (2 * ((L - n + 1 : ℕ) : ℝ)) := by
  rw [ndGeom2EndpointMass_eq_choose_mul_pow hn (by omega : n ≤ L + 1),
    ndGeom2EndpointMass_eq_choose_mul_pow hn hL, pow_succ]
  simp only [show L + 1 - 1 = L by omega]
  have hchoose := congrArg (fun m : ℕ ↦ (m : ℝ))
    (Nat.choose_mul_succ_eq (L - 1) (n - 1))
  have hLn : L - 1 + 1 = L := by omega
  have hgap : L - (n - 1) = L - n + 1 := by omega
  rw [hLn, hgap] at hchoose
  push_cast at hchoose
  rw [Nat.cast_add, Nat.cast_one]
  have hden : (2 * ((L - n + 1 : ℕ) : ℝ)) ≠ 0 := by
    positivity
  field_simp [hden]
  nlinarith

/-- The inverse form of the adjacent endpoint recurrence. -/
theorem ndGeom2EndpointMass_eq_succ_mul
    {n L : ℕ} (hn : 0 < n) (hL : n ≤ L) :
    ndGeom2EndpointMass n L =
      ndGeom2EndpointMass n (L + 1) *
        (2 * ((L - n + 1 : ℕ) : ℝ)) / (L : ℝ) := by
  rw [ndGeom2EndpointMass_succ hn hL]
  have hLReal : (0 : ℝ) < L := by exact_mod_cast (lt_of_lt_of_le hn hL)
  have hgapReal : (0 : ℝ) < (L - n + 1 : ℕ) := by positivity
  field_simp [hLReal.ne', hgapReal.ne']

/-- At the centre, the endpoint mass is half the normalized central
binomial coefficient. -/
theorem ndGeom2EndpointMass_two_mul_eq_centralBinom_div
    {n : ℕ} (hn : 0 < n) :
    ndGeom2EndpointMass n (2 * n) =
      (Nat.centralBinom n : ℝ) / (2 * (4 : ℝ) ^ n) := by
  rw [ndGeom2EndpointMass_eq_choose_mul_pow hn (by omega : n ≤ 2 * n)]
  have hcentral :
      Nat.centralBinom n = 2 * Nat.choose (2 * n - 1) (n - 1) := by
    rw [Nat.centralBinom_eq_two_mul_choose]
    have hpascal := Nat.choose_eq_choose_pred_add
      (show 0 < 2 * n by omega) hn
    have hsymm :
        Nat.choose (2 * n - 1) n =
          Nat.choose (2 * n - 1) (n - 1) := by
      rw [Nat.choose_symm_of_eq_add (show 2 * n - 1 = n + (n - 1) by omega)]
    rw [hpascal, hsymm]
    omega
  have hcentralReal := congrArg (fun m : ℕ ↦ (m : ℝ)) hcentral
  push_cast at hcentralReal
  rw [show (1 / 2 : ℝ) ^ (2 * n) = 1 / (4 : ℝ) ^ n by
    rw [pow_mul]
    norm_num [one_div_pow]]
  rw [hcentralReal]
  field_simp

/-- A first central endpoint floor.  This weaker-than-sharp bound is already
polynomially sufficient for conditioned M1; a later theorem sharpens the
factor `n` to `sqrt n` as in v10 Lemma 1(ii). -/
theorem one_div_four_mul_le_ndGeom2EndpointMass_two_mul
    {n : ℕ} (hn : 0 < n) :
    1 / (4 * (n : ℝ)) ≤ ndGeom2EndpointMass n (2 * n) := by
  rw [ndGeom2EndpointMass_two_mul_eq_centralBinom_div hn]
  have hcentral := Nat.four_pow_le_two_mul_self_mul_centralBinom n hn
  have hcentralReal :
      ((4 : ℝ) ^ n) ≤
        2 * (n : ℝ) * (Nat.centralBinom n : ℝ) := by
    exact_mod_cast hcentral
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have hpow : (0 : ℝ) < (4 : ℝ) ^ n := by positivity
  apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 4 * n)
    (by positivity : (0 : ℝ) < 2 * 4 ^ n)).2
  nlinarith

/-- Squared central-binomial lower invariant.  Keeping this step in `ℕ`
defers all square-root reasoning to a short real corollary. -/
private theorem four_pow_sq_le_four_mul_self_mul_centralBinom_sq
    (n : ℕ) (hn : 0 < n) :
    (4 ^ n) ^ 2 ≤ 4 * n * (Nat.centralBinom n) ^ 2 := by
  induction n, hn using Nat.le_induction with
  | base =>
      norm_num [Nat.centralBinom, Nat.choose]
  | succ n hn ih =>
      have hrecSq :
          (n + 1) ^ 2 * (Nat.centralBinom (n + 1)) ^ 2 =
            4 * (2 * n + 1) ^ 2 * (Nat.centralBinom n) ^ 2 := by
        calc
          _ = ((n + 1) * Nat.centralBinom (n + 1)) ^ 2 := by ring
          _ = (2 * (2 * n + 1) * Nat.centralBinom n) ^ 2 := by
            rw [Nat.succ_mul_centralBinom_succ]
          _ = _ := by ring
      have hratio : 4 * n * (n + 1) ≤ (2 * n + 1) ^ 2 := by
        have heq : (2 * n + 1) ^ 2 = 4 * n * (n + 1) + 1 := by ring
        rw [heq]
        omega
      refine Nat.le_of_mul_le_mul_left ?_ (Nat.succ_pos n)
      calc
        (n + 1) * (4 ^ (n + 1)) ^ 2 =
            16 * (n + 1) * (4 ^ n) ^ 2 := by
          rw [pow_succ]
          ring
        _ ≤ 16 * (n + 1) *
              (4 * n * (Nat.centralBinom n) ^ 2) :=
          Nat.mul_le_mul_left (16 * (n + 1)) ih
        _ = 64 * n * (n + 1) * (Nat.centralBinom n) ^ 2 := by ring
        _ ≤ 16 * (2 * n + 1) ^ 2 * (Nat.centralBinom n) ^ 2 := by
          calc
            _ = (16 * (Nat.centralBinom n) ^ 2) *
                (4 * n * (n + 1)) := by ring
            _ ≤ (16 * (Nat.centralBinom n) ^ 2) *
                (2 * n + 1) ^ 2 := Nat.mul_le_mul_left _ hratio
            _ = _ := by ring
        _ = 4 *
              ((n + 1) ^ 2 * (Nat.centralBinom (n + 1)) ^ 2) := by
          rw [hrecSq]
          ring
        _ = (n + 1) *
              (4 * (n + 1) * (Nat.centralBinom (n + 1)) ^ 2) := by
          ring

/-- Source-exact square-root lower bound for the central binomial
coefficient used in v10 Lemma 1(ii), Step 2. -/
theorem four_pow_le_two_mul_sqrt_mul_centralBinom
    (n : ℕ) (hn : 0 < n) :
    (4 : ℝ) ^ n ≤
      2 * Real.sqrt (n : ℝ) * (Nat.centralBinom n : ℝ) := by
  have hNat := four_pow_sq_le_four_mul_self_mul_centralBinom_sq n hn
  have hReal :
      ((4 : ℝ) ^ n) ^ 2 ≤
        4 * (n : ℝ) * (Nat.centralBinom n : ℝ) ^ 2 := by
    exact_mod_cast hNat
  refine le_of_sq_le_sq ?_ (by positivity)
  calc
    ((4 : ℝ) ^ n) ^ 2 ≤
        4 * (n : ℝ) * (Nat.centralBinom n : ℝ) ^ 2 := hReal
    _ = (2 * Real.sqrt (n : ℝ) *
          (Nat.centralBinom n : ℝ)) ^ 2 := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (Nat.cast_nonneg n)]
      ring

/-- The source-exact central endpoint floor `1 / (4 * sqrt n)`. -/
theorem one_div_four_mul_sqrt_le_ndGeom2EndpointMass_two_mul
    {n : ℕ} (hn : 0 < n) :
    1 / (4 * Real.sqrt (n : ℝ)) ≤
      ndGeom2EndpointMass n (2 * n) := by
  rw [ndGeom2EndpointMass_two_mul_eq_centralBinom_div hn]
  have hcentral := four_pow_le_two_mul_sqrt_mul_centralBinom n hn
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnReal
  apply (div_le_div_iff₀
    (by positivity : (0 : ℝ) < 4 * Real.sqrt (n : ℝ))
    (by positivity : (0 : ℝ) < 2 * (4 : ℝ) ^ n)).2
  calc
    1 * (2 * (4 : ℝ) ^ n) = 2 * (4 : ℝ) ^ n := by ring
    _ ≤ 2 *
        (2 * Real.sqrt (n : ℝ) * (Nat.centralBinom n : ℝ)) :=
      mul_le_mul_of_nonneg_left hcentral (by positivity)
    _ = (Nat.centralBinom n : ℝ) *
        (4 * Real.sqrt (n : ℝ)) := by ring

/-- Elementary lower exponential chord used in both directions of the
endpoint telescope. -/
theorem exp_neg_two_mul_le_one_sub
    {x : ℝ} (hx0 : 0 ≤ x) (hxhalf : x ≤ 1 / 2) :
    Real.exp (-2 * x) ≤ 1 - x := by
  have hy : 0 < 1 - x := by linarith
  have hlog := Real.one_sub_inv_le_log_of_pos hy
  have hratio : -2 * x ≤ 1 - (1 - x)⁻¹ := by
    rw [show 1 - (1 - x)⁻¹ = -x / (1 - x) by
      field_simp [hy.ne']
      ring]
    apply (le_div_iff₀ hy).2
    nlinarith [mul_nonneg hx0 (by linarith : 0 ≤ 1 - 2 * x)]
  calc
    Real.exp (-2 * x) ≤ Real.exp (Real.log (1 - x)) :=
      Real.exp_monotone (hratio.trans hlog)
    _ = 1 - x := Real.exp_log hy

/-- Lower bound for one step to the right of the central endpoint. -/
theorem exp_neg_right_step_le_endpoint_ratio
    (n t : ℕ) (hn : 0 < n) :
    Real.exp (-((t + 2 : ℕ) : ℝ) / (n : ℝ)) ≤
      ((2 * n + t : ℕ) : ℝ) /
        (2 * ((n + t + 1 : ℕ) : ℝ)) := by
  let x : ℝ :=
    ((t + 2 : ℕ) : ℝ) / (2 * ((n + t + 1 : ℕ) : ℝ))
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hx0 : 0 ≤ x := by
    dsimp [x]
    positivity
  have hxhalf : x ≤ 1 / 2 := by
    dsimp [x]
    apply (div_le_iff₀ (by positivity :
      (0 : ℝ) < 2 * ((n + t + 1 : ℕ) : ℝ))).2
    push_cast
    nlinarith
  have hfrac :
      ((t + 2 : ℕ) : ℝ) / ((n + t + 1 : ℕ) : ℝ) ≤
        ((t + 2 : ℕ) : ℝ) / (n : ℝ) := by
    apply div_le_div_of_nonneg_left
    · positivity
    · exact hnReal
    · exact_mod_cast (show n ≤ n + t + 1 by omega)
  have hexp :
      Real.exp (-((t + 2 : ℕ) : ℝ) / (n : ℝ)) ≤
        Real.exp (-2 * x) := by
    apply Real.exp_monotone
    dsimp [x]
    rw [show -2 *
        (((t + 2 : ℕ) : ℝ) / (2 * ((n + t + 1 : ℕ) : ℝ))) =
        -((t + 2 : ℕ) : ℝ) / ((n + t + 1 : ℕ) : ℝ) by
      field_simp]
    simpa only [neg_div] using neg_le_neg hfrac
  calc
    Real.exp (-((t + 2 : ℕ) : ℝ) / (n : ℝ)) ≤
        Real.exp (-2 * x) := hexp
    _ ≤ 1 - x := exp_neg_two_mul_le_one_sub hx0 hxhalf
    _ = ((2 * n + t : ℕ) : ℝ) /
        (2 * ((n + t + 1 : ℕ) : ℝ)) := by
      dsimp [x]
      push_cast
      field_simp
      ring

/-- Right-hand endpoint telescope from `2*n`.  The exponent is the exact
sum of the checked one-step losses. -/
theorem ndGeom2EndpointMass_two_mul_mul_exp_right_le
    (n d : ℕ) (hn : 0 < n) :
    ndGeom2EndpointMass n (2 * n) *
        Real.exp
          (-((d : ℝ) * ((d : ℝ) + 3) / (2 * (n : ℝ)))) ≤
      ndGeom2EndpointMass n (2 * n + d) := by
  induction d with
  | zero =>
      simp
  | succ d ih =>
      have hstep := exp_neg_right_step_le_endpoint_ratio n d hn
      have hmassNonneg : 0 ≤ ndGeom2EndpointMass n (2 * n + d) :=
        (ndGeom2EndpointMass_pos hn (by omega : n ≤ 2 * n + d)).le
      have hexp :
          Real.exp
              (-(((d + 1 : ℕ) : ℝ) * (((d + 1 : ℕ) : ℝ) + 3) /
                (2 * (n : ℝ)))) =
            Real.exp
                (-((d : ℝ) * ((d : ℝ) + 3) / (2 * (n : ℝ)))) *
              Real.exp (-((d + 2 : ℕ) : ℝ) / (n : ℝ)) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        field_simp
        ring
      calc
        ndGeom2EndpointMass n (2 * n) *
              Real.exp
                (-(((d + 1 : ℕ) : ℝ) * (((d + 1 : ℕ) : ℝ) + 3) /
                  (2 * (n : ℝ)))) =
            (ndGeom2EndpointMass n (2 * n) *
                Real.exp
                  (-((d : ℝ) * ((d : ℝ) + 3) / (2 * (n : ℝ))))) *
              Real.exp (-((d + 2 : ℕ) : ℝ) / (n : ℝ)) := by
          rw [hexp]
          ring
        _ ≤ ndGeom2EndpointMass n (2 * n + d) *
              (((2 * n + d : ℕ) : ℝ) /
                (2 * ((n + d + 1 : ℕ) : ℝ))) :=
          mul_le_mul ih hstep (Real.exp_nonneg _) hmassNonneg
        _ = ndGeom2EndpointMass n (2 * n + (d + 1)) := by
          rw [show 2 * n + (d + 1) = (2 * n + d) + 1 by omega,
            ndGeom2EndpointMass_succ hn (by omega : n ≤ 2 * n + d)]
          rw [show 2 * n + d - n + 1 = n + d + 1 by omega]
          ring

/-- Reverse recurrence indexed by a positive displacement from `2*n`. -/
theorem ndGeom2EndpointMass_two_mul_sub
    (n u : ℕ) (hn : 0 < n) (hu0 : 0 < u) (hu : u ≤ n) :
    ndGeom2EndpointMass n (2 * n - u) =
      ndGeom2EndpointMass n (2 * n - (u - 1)) *
        (2 * ((n - u + 1 : ℕ) : ℝ)) /
          ((2 * n - u : ℕ) : ℝ) := by
  rw [ndGeom2EndpointMass_eq_succ_mul hn
    (by omega : n ≤ 2 * n - u)]
  rw [show 2 * n - u + 1 = 2 * n - (u - 1) by omega,
    show 2 * n - u - n + 1 = n - u + 1 by omega]

/-- Lower exponential bound for one step to the left of the central
endpoint. -/
theorem exp_neg_left_step_le_endpoint_ratio
    (n u : ℕ) (hn : 0 < n) (hu : 2 * u ≤ n) :
    Real.exp (-2 * ((u : ℝ) / (n : ℝ))) ≤
      (2 * ((n - u + 1 : ℕ) : ℝ)) /
        ((2 * n - u : ℕ) : ℝ) := by
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have huLe : u ≤ n := by omega
  have huReal : (u : ℝ) ≤ n := by exact_mod_cast huLe
  have hx0 : 0 ≤ (u : ℝ) / (n : ℝ) := by positivity
  have hxhalf : (u : ℝ) / (n : ℝ) ≤ 1 / 2 := by
    apply (div_le_iff₀ hnReal).2
    have huRealTwo : (2 : ℝ) * u ≤ n := by exact_mod_cast hu
    nlinarith
  have hchord := exp_neg_two_mul_le_one_sub hx0 hxhalf
  have hdenReal : (0 : ℝ) < (2 * n - u : ℕ) := by
    exact_mod_cast (show 0 < 2 * n - u by omega)
  have hdenSub : (0 : ℝ) < 2 * (n : ℝ) - (u : ℝ) := by
    nlinarith
  have hratio :
      1 - (u : ℝ) / (n : ℝ) ≤
        (2 * ((n - u + 1 : ℕ) : ℝ)) /
          ((2 * n - u : ℕ) : ℝ) := by
    rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub huLe,
      Nat.cast_sub (by omega : u ≤ 2 * n)]
    push_cast
    apply (le_div_iff₀ hdenSub).2
    field_simp [hnReal.ne']
    nlinarith [mul_nonneg (show (0 : ℝ) ≤ u by positivity)
      (sub_nonneg.mpr huReal)]
  exact hchord.trans hratio

/-- Left-hand endpoint telescope from `2*n`, valid throughout the source
regime `2*d ≤ n`. -/
theorem ndGeom2EndpointMass_two_mul_mul_exp_left_le
    (n d : ℕ) (hn : 0 < n) :
    2 * d ≤ n →
      ndGeom2EndpointMass n (2 * n) *
          Real.exp
            (-((d : ℝ) * ((d : ℝ) + 1) / (n : ℝ))) ≤
        ndGeom2EndpointMass n (2 * n - d) := by
  induction d with
  | zero =>
      intro _hd
      simp
  | succ d ih =>
      intro hd
      have hdPrev : 2 * d ≤ n := by omega
      have ihPrev := ih hdPrev
      have hstep :=
        exp_neg_left_step_le_endpoint_ratio n (d + 1) hn hd
      have hmassNonneg : 0 ≤ ndGeom2EndpointMass n (2 * n - d) :=
        (ndGeom2EndpointMass_pos hn (by omega : n ≤ 2 * n - d)).le
      have hexp :
          Real.exp
              (-(((d + 1 : ℕ) : ℝ) * (((d + 1 : ℕ) : ℝ) + 1) /
                (n : ℝ))) =
            Real.exp
                (-((d : ℝ) * ((d : ℝ) + 1) / (n : ℝ))) *
              Real.exp (-2 * (((d + 1 : ℕ) : ℝ) / (n : ℝ))) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        field_simp
        ring
      calc
        ndGeom2EndpointMass n (2 * n) *
              Real.exp
                (-(((d + 1 : ℕ) : ℝ) * (((d + 1 : ℕ) : ℝ) + 1) /
                  (n : ℝ))) =
            (ndGeom2EndpointMass n (2 * n) *
                Real.exp
                  (-((d : ℝ) * ((d : ℝ) + 1) / (n : ℝ)))) *
              Real.exp (-2 * (((d + 1 : ℕ) : ℝ) / (n : ℝ))) := by
          rw [hexp]
          ring
        _ ≤ ndGeom2EndpointMass n (2 * n - d) *
              ((2 * ((n - (d + 1) + 1 : ℕ) : ℝ)) /
                ((2 * n - (d + 1) : ℕ) : ℝ)) :=
          mul_le_mul ihPrev hstep (Real.exp_nonneg _) hmassNonneg
        _ = ndGeom2EndpointMass n (2 * n - (d + 1)) := by
          rw [show ndGeom2EndpointMass n (2 * n - d) *
              ((2 * ((n - (d + 1) + 1 : ℕ) : ℝ)) /
                ((2 * n - (d + 1) : ℕ) : ℝ)) =
              ndGeom2EndpointMass n (2 * n - d) *
                (2 * ((n - (d + 1) + 1 : ℕ) : ℝ)) /
                  ((2 * n - (d + 1) : ℕ) : ℝ) by ring]
          simpa only [Nat.add_sub_cancel] using
            (ndGeom2EndpointMass_two_mul_sub n (d + 1) hn
              (by omega) (by omega)).symm

/-- Two-sided displacement floor obtained by combining the source-exact
central `sqrt` estimate with the checked adjacent telescopes. -/
theorem one_div_four_mul_sqrt_mul_exp_displacement_le_endpointMass
    {n L : ℕ} (hn : 0 < n)
    (hhalf : 2 * ndGeom2CentralDisplacement n L ≤ n) :
    1 / (4 * Real.sqrt (n : ℝ)) *
        Real.exp
          (-((ndGeom2CentralDisplacement n L : ℝ) *
            ((ndGeom2CentralDisplacement n L : ℝ) + 1) /
              (n : ℝ))) ≤
      ndGeom2EndpointMass n L := by
  let d := ndGeom2CentralDisplacement n L
  change 2 * d ≤ n at hhalf
  change 1 / (4 * Real.sqrt (n : ℝ)) *
      Real.exp (-((d : ℝ) * ((d : ℝ) + 1) / (n : ℝ))) ≤
    ndGeom2EndpointMass n L
  have hcenter := one_div_four_mul_sqrt_le_ndGeom2EndpointMass_two_mul hn
  have hcenterNonneg : 0 ≤ ndGeom2EndpointMass n (2 * n) :=
    (ndGeom2EndpointMass_pos hn (by omega : n ≤ 2 * n)).le
  have hsplit := ndGeom2CentralDisplacement_split n L
  change 2 * n + d = L ∨ L + d = 2 * n at hsplit
  rcases hsplit with hright | hleft
  · rw [← hright]
    have htelescope :=
      ndGeom2EndpointMass_two_mul_mul_exp_right_le n d hn
    have hexp :
        Real.exp (-((d : ℝ) * ((d : ℝ) + 1) / (n : ℝ))) ≤
          Real.exp
            (-((d : ℝ) * ((d : ℝ) + 3) / (2 * (n : ℝ)))) := by
      rcases eq_or_ne d 0 with hd0 | hd0
      · simp [hd0]
      · have hd := Nat.pos_of_ne_zero hd0
        apply Real.exp_monotone
        have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
        have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast hd
        have hfrac :
            (d : ℝ) * ((d : ℝ) + 3) / (2 * (n : ℝ)) ≤
              (d : ℝ) * ((d : ℝ) + 1) / (n : ℝ) := by
          apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < 2 * n)
            hnReal).2
          nlinarith [mul_nonneg (show (0 : ℝ) ≤ d by positivity)
            (sub_nonneg.mpr hdOne)]
        exact neg_le_neg hfrac
    exact (mul_le_mul hcenter hexp (Real.exp_nonneg _) hcenterNonneg).trans
      htelescope
  · have hL : L = 2 * n - d := by omega
    rw [hL]
    exact (mul_le_mul_of_nonneg_right hcenter (Real.exp_nonneg _)).trans
      (ndGeom2EndpointMass_two_mul_mul_exp_left_le n d hn hhalf)

/-- M1-facing polynomial endpoint floor.  The hypotheses isolate exactly
the two consequences later supplied by the natural-logarithm window: a
central-range guard and a quadratic displacement budget. -/
theorem ndGeom2EndpointMass_displacement_pow_floor
    {n L q : ℕ} (hn : 0 < n)
    (hedge : 4 * ndGeom2CentralDisplacement n L ≤ n)
    (hquad :
      (ndGeom2CentralDisplacement n L : ℝ) ^ 2 ≤
        (q : ℝ) * (n : ℝ) * Real.log (n : ℝ)) :
    Real.exp (-1) / (4 * (n : ℝ) ^ (q + 1)) ≤
      ndGeom2EndpointMass n L := by
  let d := ndGeom2CentralDisplacement n L
  change 4 * d ≤ n at hedge
  change (d : ℝ) ^ 2 ≤
    (q : ℝ) * (n : ℝ) * Real.log (n : ℝ) at hquad
  have hnReal : (0 : ℝ) < n := by exact_mod_cast hn
  have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsqrtPos : 0 < Real.sqrt (n : ℝ) := Real.sqrt_pos.2 hnReal
  have hsqrtLe : Real.sqrt (n : ℝ) ≤ (n : ℝ) := by
    rw [Real.sqrt_le_left hnReal.le]
    nlinarith
  have hreciprocal :
      1 / (4 * (n : ℝ)) ≤
        1 / (4 * Real.sqrt (n : ℝ)) := by
    exact one_div_le_one_div_of_le (by positivity)
      (mul_le_mul_of_nonneg_left hsqrtLe (by norm_num))
  have hdLe : d ≤ n := by omega
  have hdReal : (d : ℝ) ≤ n := by exact_mod_cast hdLe
  have hExponent :
      (d : ℝ) * ((d : ℝ) + 1) / (n : ℝ) ≤
        1 + (q : ℝ) * Real.log (n : ℝ) := by
    apply (div_le_iff₀ hnReal).2
    nlinarith
  have hExp :
      Real.exp (-(1 + (q : ℝ) * Real.log (n : ℝ))) ≤
        Real.exp (-((d : ℝ) * ((d : ℝ) + 1) / (n : ℝ))) :=
    Real.exp_monotone (neg_le_neg hExponent)
  have hexpPow :
      Real.exp (-(1 + (q : ℝ) * Real.log (n : ℝ))) =
        Real.exp (-1) / (n : ℝ) ^ q := by
    rw [show -(1 + (q : ℝ) * Real.log (n : ℝ)) =
      -1 + -((q : ℝ) * Real.log (n : ℝ)) by ring,
      Real.exp_add, Real.exp_neg, Real.exp_neg, Real.exp_nat_mul,
      Real.exp_log hnReal]
    ring
  have htarget :
      Real.exp (-1) / (4 * (n : ℝ) ^ (q + 1)) =
        (1 / (4 * (n : ℝ))) *
          Real.exp (-(1 + (q : ℝ) * Real.log (n : ℝ))) := by
    rw [hexpPow, pow_succ]
    field_simp
  rw [htarget]
  exact (mul_le_mul hreciprocal hExp (Real.exp_nonneg _)
    (by positivity : 0 ≤ 1 / (4 * Real.sqrt (n : ℝ)))).trans
      (one_div_four_mul_sqrt_mul_exp_displacement_le_endpointMass hn
        (by omega : 2 * ndGeom2CentralDisplacement n L ≤ n))

/-- The literal M1 window bounds the real cast of the central displacement. -/
theorem cast_displacement_le_of_m1Window
    {K : ℝ} {n L : ℕ} (hwin : ndSection7M1Window K n L) :
    (ndGeom2CentralDisplacement n L : ℝ) ≤
      K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by
  simpa only [ndSection7M1Window, cast_ndGeom2CentralDisplacement] using hwin

/-- An explicit eventual-size guard turns the M1 window into the finite
telescope's central-range hypothesis. -/
theorem four_displacement_le_of_m1Window_of_guard
    {K : ℝ} {n L : ℕ} (hwin : ndSection7M1Window K n L)
    (hguard :
      4 * K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤ (n : ℝ)) :
    4 * ndGeom2CentralDisplacement n L ≤ n := by
  have hd := cast_displacement_le_of_m1Window hwin
  have hr :
      (4 : ℝ) * (ndGeom2CentralDisplacement n L : ℝ) ≤ (n : ℝ) :=
    calc
      _ ≤ 4 *
          (K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) := by
        gcongr
      _ = 4 * K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by ring
      _ ≤ _ := hguard
  exact_mod_cast hr

/-- The squared M1 window is absorbed by the fixed natural exponent
`ceil(K^2)`. -/
theorem displacement_sq_le_natCeil_sq_mul_of_m1Window
    {K : ℝ} {n L : ℕ} (hK : 0 ≤ K) (hn : 1 ≤ n)
    (hwin : ndSection7M1Window K n L) :
    (ndGeom2CentralDisplacement n L : ℝ) ^ 2 ≤
      (⌈K ^ 2⌉₊ : ℝ) * (n : ℝ) * Real.log (n : ℝ) := by
  have hnReal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hlog : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnReal
  have hbase : 0 ≤ (n : ℝ) * Real.log (n : ℝ) :=
    mul_nonneg (by positivity) hlog
  have hd := cast_displacement_le_of_m1Window hwin
  have hsqrt :
      0 ≤ K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) :=
    mul_nonneg hK (Real.sqrt_nonneg _)
  have hsq := (sq_le_sq₀ (by positivity) hsqrt).2 hd
  have hKq : K ^ 2 ≤ (⌈K ^ 2⌉₊ : ℝ) := Nat.le_ceil _
  calc
    _ ≤ (K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ^ 2 := hsq
    _ = K ^ 2 * ((n : ℝ) * Real.log (n : ℝ)) := by
      rw [mul_pow, Real.sq_sqrt hbase]
    _ ≤ (⌈K ^ 2⌉₊ : ℝ) *
          ((n : ℝ) * Real.log (n : ℝ)) :=
      mul_le_mul_of_nonneg_right hKq hbase
    _ = (⌈K ^ 2⌉₊ : ℝ) * (n : ℝ) * Real.log (n : ℝ) := by
      ring

/-- Endpoint-shaped central-window floor with its sole eventual-size guard
still explicit. -/
theorem ndGeom2EndpointMass_m1Window_pow_floor_of_guard
    {K : ℝ} {n L : ℕ} (hK : 0 ≤ K) (hn : 0 < n)
    (hwin : ndSection7M1Window K n L)
    (hguard :
      4 * K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤ (n : ℝ)) :
    Real.exp (-1) /
        (4 * (n : ℝ) ^ (⌈K ^ 2⌉₊ + 1)) ≤
      ndGeom2EndpointMass n L := by
  exact ndGeom2EndpointMass_displacement_pow_floor hn
    (four_displacement_le_of_m1Window_of_guard hwin hguard)
    (displacement_sq_le_natCeil_sq_mul_of_m1Window hK hn hwin)

/-- Every fixed positive window constant eventually satisfies the sole real
size guard used by the finite endpoint telescope. -/
theorem eventually_four_mul_sqrt_nat_mul_log_le
    (K : ℝ) (hK : 0 < K) :
    ∀ᶠ n : ℕ in Filter.atTop,
      4 * K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤ (n : ℝ) := by
  have hc : 0 < 16 * K ^ 2 := by positivity
  have hsmallReal :=
    Real.isLittleO_log_id_atTop.bound (inv_pos.mpr hc)
  have hsmallNat := hsmallReal.natCast_atTop
  filter_upwards [hsmallNat, Filter.eventually_ge_atTop 1] with n hsmall hn
  have hnReal : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ (n : ℝ) := by positivity
  have hlog0 : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg hnReal
  simp only [Real.norm_eq_abs, abs_of_nonneg hlog0, id_eq,
    abs_of_nonneg hn0] at hsmall
  have hlogBound :
      16 * K ^ 2 * Real.log (n : ℝ) ≤ (n : ℝ) := by
    calc
      _ ≤ (16 * K ^ 2) * ((16 * K ^ 2)⁻¹ * (n : ℝ)) :=
        mul_le_mul_of_nonneg_left hsmall hc.le
      _ = (n : ℝ) := by field_simp [hc.ne']
  have hbase : 0 ≤ (n : ℝ) * Real.log (n : ℝ) :=
    mul_nonneg hn0 hlog0
  have hsq :
      (4 * K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ))) ^ 2 ≤
        (n : ℝ) ^ 2 := by
    calc
      _ = (n : ℝ) * (16 * K ^ 2 * Real.log (n : ℝ)) := by
        rw [mul_pow, Real.sq_sqrt hbase]
        ring
      _ ≤ (n : ℝ) * (n : ℝ) :=
        mul_le_mul_of_nonneg_left hlogBound hn0
      _ = (n : ℝ) ^ 2 := by ring
  exact (sq_le_sq₀ (by positivity) hn0).1 hsq

/-- The explicit guard can be hidden behind a threshold depending only on
the fixed M1 window constant. -/
theorem exists_m1Window_endpoint_pow_floor
    (K : ℝ) (hK : 1 ≤ K) :
    ∃ N : ℕ, 1 ≤ N ∧
      ∀ n L : ℕ, N ≤ n → ndSection7M1Window K n L →
        Real.exp (-1) /
            (4 * (n : ℝ) ^ (⌈K ^ 2⌉₊ + 1)) ≤
          ndGeom2EndpointMass n L := by
  rcases Filter.eventually_atTop.1
      (eventually_four_mul_sqrt_nat_mul_log_le K
        (zero_lt_one.trans_le hK)) with ⟨N, hN⟩
  refine ⟨max N 1, le_max_right N 1, ?_⟩
  intro n L hn hwin
  have hnN : N ≤ n := (le_max_left N 1).trans hn
  have hn1 : 1 ≤ n := (le_max_right N 1).trans hn
  exact ndGeom2EndpointMass_m1Window_pow_floor_of_guard
    (zero_le_one.trans hK) hn1 hwin
    (hN n hnN)

/-- Consumer-ready eventual endpoint floor, with the nonempty-fiber support
hypothesis kept visible in the same order as the M1 statement. -/
theorem exists_ndGeom2EndpointMass_m1_polynomial_floor
    (K : ℝ) (hK : 1 ≤ K) :
    ∃ N : ℕ, 1 ≤ N ∧
      ∀ n : ℕ, N ≤ n → ∀ L : ℕ, n ≤ L →
        ndSection7M1Window K n L →
          ndSection7M1FloorConstant /
              (n : ℝ) ^ ndSection7M1FloorExponent K ≤
            ndGeom2EndpointMass n L := by
  rcases exists_m1Window_endpoint_pow_floor K hK with
    ⟨N, hN1, hfloor⟩
  refine ⟨N, hN1, ?_⟩
  intro n hnN L _hL hwin
  calc
    ndSection7M1FloorConstant /
          (n : ℝ) ^ ndSection7M1FloorExponent K =
        Real.exp (-1) /
          (4 * (n : ℝ) ^ (⌈K ^ 2⌉₊ + 1)) := by
      unfold ndSection7M1FloorConstant ndSection7M1FloorExponent
      ring
    _ ≤ ndGeom2EndpointMass n L := hfloor n L hnN hwin

end ND
end Erdos1135
