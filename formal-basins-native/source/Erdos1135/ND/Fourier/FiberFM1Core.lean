import Erdos1135.ND.Fourier.FixedTotalRawPolynomial
import Erdos1135.ND.Fourier.FiberEndpointFloor

/-!
# Conditioned Natural-Exponent FM1 Core

This leaf divides the complete raw fixed-total oscillation bound by the
checked endpoint floor exactly once.  A private eventual theorem retains one
spare power, and the public natural-exponent endpoint absorbs the finite
initial range by the full-L1 bound for a probability mass.

No T3 tail or all-scale telescope occurs here.
-/

open scoped BigOperators

namespace Erdos1135
namespace ND

noncomputable section

/-- A conditioned fixed-fiber probability mass has oscillation at most two. -/
theorem ndSection7FiberPMF_oscillation_le_two
    (m n L : ℕ) (hn : 0 < n) (hmn : m ≤ n) (hL : n ≤ L) :
    Tao.taoZModPowOscillation m n
        (fun y => (ndSection7FiberPMF n L hn hL y).toReal) ≤ 2 := by
  have hmass :
      (∑ y : ZMod (3 ^ n),
        |(ndSection7FiberPMF n L hn hL y).toReal|) = 1 := by
    classical
    calc
      (∑ y : ZMod (3 ^ n),
          |(ndSection7FiberPMF n L hn hL y).toReal|) =
        ∑ y : ZMod (3 ^ n),
          (ndSection7FiberPMF n L hn hL y).toReal := by
        apply Finset.sum_congr rfl
        intro y _hy
        rw [abs_of_nonneg ENNReal.toReal_nonneg]
      _ = 1 := Tao.pmf_sum_toReal (ndSection7FiberPMF n L hn hL)
  calc
    Tao.taoZModPowOscillation m n
        (fun y => (ndSection7FiberPMF n L hn hL y).toReal) ≤
      2 * ∑ y : ZMod (3 ^ n),
        |(ndSection7FiberPMF n L hn hL y).toReal| :=
      Tao.taoZModPowOscillation_le_two_mul_sum_abs hmn _
    _ = 2 := by rw [hmass, mul_one]

/-- Conditioned fixed-total FM1 in the core regime at one natural exponent
and one central-window constant. -/
def ndSection7ConditionedFM1CoreNatAt (A : ℕ) (K C : ℝ) : Prop :=
  ∀ n : ℕ, (hn : 1 ≤ n) →
    ∀ m : ℕ, m ≤ n → 9 * n ≤ 10 * m →
      ∀ L : ℕ, (hL : n ≤ L) → ndSection7M1Window K n L →
        Tao.taoZModPowOscillation m n
            (fun y => (ndSection7FiberPMF n L
              (Nat.zero_lt_one.trans_le hn) hL y).toReal) ≤
          C / (n : ℝ) ^ A

/-- Natural-exponent statement surface for the frozen FM1 core regime. -/
def NDConditionedFM1CoreNatStatement : Prop :=
  ∀ A : ℕ, 0 < A →
    ∀ K : ℝ, 1 ≤ K →
      ∃ C : ℝ, 0 ≤ C ∧ ndSection7ConditionedFM1CoreNatAt A K C

/-- Eventual endpoint normalization.  The private extra power is retained
until the all-`n` source statement absorbs the finite range. -/
private theorem exists_ndSection7ConditionedFM1CoreNat_large
    (A : ℕ) (K : ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N0 : ℕ, 2 ≤ N0 ∧
      ∀ n : ℕ, (hn : 1 ≤ n) → N0 ≤ n →
        ∀ m : ℕ, m ≤ n → 9 * n ≤ 10 * m →
          ∀ L : ℕ, (hL : n ≤ L) → ndSection7M1Window K n L →
            Tao.taoZModPowOscillation m n
                (fun y => (ndSection7FiberPMF n L
                  (Nat.zero_lt_one.trans_le hn) hL y).toReal) ≤
              C / (n : ℝ) ^ (A + 1) := by
  let F : ℕ := ndSection7M1FloorExponent K
  let Q : ℕ := A + F
  obtain ⟨Craw, hCraw, Nraw, hNraw, hraw⟩ :=
    exists_ndSection6FixedTotalRawOscillation_le Q
  obtain ⟨Nfloor, _hNfloor, hfloor⟩ :=
    exists_ndGeom2EndpointMass_m1_polynomial_floor K hK
  let c0 : ℝ := ndSection7M1FloorConstant
  let C : ℝ := Craw / c0
  have hc0 : 0 < c0 := by
    dsimp [c0]
    unfold ndSection7M1FloorConstant
    positivity
  have hC : 0 ≤ C := by
    dsimp [C]
    exact div_nonneg hCraw hc0.le
  refine ⟨C, hC, max Nraw Nfloor,
    hNraw.trans (le_max_left _ _), ?_⟩
  intro n hn hnN m hmn hhigh L hL hwin
  have hn0 : 0 < n := Nat.zero_lt_one.trans_le hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hnRaw : Nraw ≤ n := (le_max_left _ _).trans hnN
  have hnFloor : Nfloor ≤ n := (le_max_right _ _).trans hnN
  let X : ℝ :=
    Tao.taoZModPowOscillation m n
      (fun y => (ndSection7FiberPMF n L hn0 hL y).toReal)
  have hX0 : 0 ≤ X := by
    dsimp [X]
    unfold Tao.taoZModPowOscillation
    exact Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hf :
      c0 / (n : ℝ) ^ F ≤ ndGeom2EndpointMass n L := by
    simpa [c0, F] using hfloor n hnFloor L hL hwin
  have hfp : 0 < c0 / (n : ℝ) ^ F :=
    div_pos hc0 (pow_pos hnR F)
  have hrawX :
      ndGeom2EndpointMass n L * X ≤
        Craw / (n : ℝ) ^ (Q + 1) := by
    have h := hraw n L m hnRaw hmn hhigh
    rw [ndSection6FixedSplitTailSubmass_zero_head_zero_weight_oscillation_eq
      m n L hn0 hL] at h
    simpa [X] using h
  have hscaled :
      (c0 / (n : ℝ) ^ F) * X ≤
        Craw / (n : ℝ) ^ (Q + 1) :=
    (mul_le_mul_of_nonneg_right hf hX0).trans hrawX
  have hdiv :
      X ≤ (Craw / (n : ℝ) ^ (Q + 1)) /
        (c0 / (n : ℝ) ^ F) :=
    (le_div_iff₀ hfp).2 (by simpa [mul_comm] using hscaled)
  have hQ : Q + 1 = (A + 1) + F := by
    dsimp [Q]
    omega
  have hcancel :
      (Craw / (n : ℝ) ^ ((A + 1) + F)) /
          (c0 / (n : ℝ) ^ F) =
        (Craw / c0) / (n : ℝ) ^ (A + 1) := by
    rw [pow_add, div_mul_eq_div_div,
      div_div_div_cancel_right₀ (pow_ne_zero F hnR.ne'),
      div_right_comm]
  have hfinal : X ≤ C / (n : ℝ) ^ (A + 1) := by
    calc
      X ≤ (Craw / (n : ℝ) ^ (Q + 1)) /
          (c0 / (n : ℝ) ^ F) := hdiv
      _ = C / (n : ℝ) ^ (A + 1) := by
        rw [hQ]
        simpa [C] using hcancel
  simpa [X] using hfinal

/-- The frozen natural-exponent FM1 core: one endpoint division followed by
finite-range absorption, with no public cutoff. -/
theorem ndConditionedFM1CoreNat : NDConditionedFM1CoreNatStatement := by
  intro A _hA K hK
  obtain ⟨Clarge, hClarge, N0, _hN0, hlarge⟩ :=
    exists_ndSection7ConditionedFM1CoreNat_large A K hK
  let Csmall : ℝ := 2 * (N0 : ℝ) ^ A
  let Cfinal : ℝ := max Clarge Csmall
  have hCsmall : 0 ≤ Csmall := by
    dsimp [Csmall]
    positivity
  have hCfinal : 0 ≤ Cfinal := by
    exact hClarge.trans (le_max_left Clarge Csmall)
  refine ⟨Cfinal, hCfinal, ?_⟩
  intro n hn m hmn hhigh L hL hwin
  have hn0 : 0 < n := Nat.zero_lt_one.trans_le hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have hden : 0 < (n : ℝ) ^ A := pow_pos hnR A
  by_cases hcut : N0 ≤ n
  · have hnext := hlarge n hn hcut m hmn hhigh L hL hwin
    have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hpow : (n : ℝ) ^ A ≤ (n : ℝ) ^ (A + 1) := by
      calc
        (n : ℝ) ^ A = (n : ℝ) ^ A * 1 := by ring
        _ ≤ (n : ℝ) ^ A * (n : ℝ) :=
          mul_le_mul_of_nonneg_left hnOne (pow_nonneg hnR.le A)
        _ = (n : ℝ) ^ (A + 1) := by rw [pow_succ]
    calc
      Tao.taoZModPowOscillation m n
          (fun y => (ndSection7FiberPMF n L hn0 hL y).toReal) ≤
        Clarge / (n : ℝ) ^ (A + 1) := by simpa using hnext
      _ ≤ Clarge / (n : ℝ) ^ A :=
        div_le_div_of_nonneg_left hClarge hden hpow
      _ ≤ Cfinal / (n : ℝ) ^ A :=
        div_le_div_of_nonneg_right
          (le_max_left Clarge Csmall) hden.le
  · have hnN0 : n ≤ N0 := by omega
    have hnN0R : (n : ℝ) ≤ (N0 : ℝ) := by exact_mod_cast hnN0
    have hpow : (n : ℝ) ^ A ≤ (N0 : ℝ) ^ A :=
      pow_le_pow_left₀ (Nat.cast_nonneg n) hnN0R A
    have hscaled : 2 * (n : ℝ) ^ A ≤ 2 * (N0 : ℝ) ^ A :=
      mul_le_mul_of_nonneg_left hpow (by norm_num)
    have hfinal : 2 * (n : ℝ) ^ A ≤ Cfinal := by
      calc
        2 * (n : ℝ) ^ A ≤ 2 * (N0 : ℝ) ^ A := hscaled
        _ = Csmall := rfl
        _ ≤ Cfinal := le_max_right Clarge Csmall
    have hunit := ndSection7FiberPMF_oscillation_le_two
      m n L hn0 hmn hL
    exact hunit.trans ((le_div_iff₀ hden).2 hfinal)

/-- Conditioned FM1 core at one positive real exponent. -/
def ndSection7ConditionedFM1CoreRealAt (A K C : ℝ) : Prop :=
  ∀ n : ℕ, (hn : 1 ≤ n) →
    ∀ m : ℕ, m ≤ n → 9 * n ≤ 10 * m →
      ∀ L : ℕ, (hL : n ≤ L) → ndSection7M1Window K n L →
        Tao.taoZModPowOscillation m n
            (fun y => (ndSection7FiberPMF n L
              (Nat.zero_lt_one.trans_le hn) hL y).toReal) ≤
          C / Real.rpow (n : ℝ) A

/-- Frozen-v10 positive-real FM1-core statement. -/
def NDConditionedFM1CoreStatement : Prop :=
  ∀ A : ℝ, 0 < A →
    ∀ K : ℝ, 1 ≤ K →
      ∃ C : ℝ, 0 ≤ C ∧ ndSection7ConditionedFM1CoreRealAt A K C

/-- The frozen positive-real FM1 core follows from the checked all-`n`
natural-exponent core by taking the natural ceiling of the exponent. -/
theorem ndConditionedFM1Core : NDConditionedFM1CoreStatement := by
  intro A hA K hK
  let q : ℕ := ⌈A⌉₊
  have hq : 0 < q := by
    dsimp [q]
    exact Nat.ceil_pos.mpr hA
  obtain ⟨C, hC, hnat⟩ := ndConditionedFM1CoreNat q hq K hK
  refine ⟨C, hC, ?_⟩
  intro n hn m hmn hhigh L hL hwin
  have hbound := hnat n hn m hmn hhigh L hL hwin
  have hn0 : 0 < n := Nat.zero_lt_one.trans_le hn
  have hnReal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
  have hnOne : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hAq : A ≤ (q : ℝ) := by
    dsimp [q]
    exact Nat.le_ceil A
  have hrpowPow : Real.rpow (n : ℝ) A ≤ (n : ℝ) ^ q := by
    calc
      Real.rpow (n : ℝ) A ≤ Real.rpow (n : ℝ) (q : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hnOne hAq
      _ = (n : ℝ) ^ q := Real.rpow_natCast (n : ℝ) q
  have hrpowPos : 0 < Real.rpow (n : ℝ) A :=
    Real.rpow_pos_of_pos hnReal A
  exact hbound.trans
    (div_le_div_of_nonneg_left hC hrpowPos hrpowPow)

end

end ND
end Erdos1135
