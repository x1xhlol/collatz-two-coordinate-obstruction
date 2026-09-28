import Erdos1135.ND.Fourier.FixedTotalOneStep
import Erdos1135.Tao.Section6.AdjacentOneStep
import Erdos1135.Tao.Section6.InversePowerTail

/-!
# Conditioned Fixed-Total FM1

This leaf telescopes actual marginals of one fixed conditioned parent law.
Every nonterminal adjacent step uses the checked projected-mixture theorem;
the terminal marginal is the original parent law and is handled directly by
FM1-core.  The existing inverse-power tail then gives the complete lower-scale
range without a public cutoff.
-/

open scoped BigOperators

namespace Erdos1135
namespace ND

noncomputable section

private noncomputable def ndPMFMarginal
    {r n : ℕ} (hrn : r ≤ n) (p : PMF (ZMod (3 ^ n))) :
    PMF (ZMod (3 ^ r)) :=
  p.map (Tao.taoZModThreeProjection hrn)

private theorem ndPMFMarginal_proof_irrel
    {r n : ℕ} (h h' : r ≤ n) (p : PMF (ZMod (3 ^ n))) :
    ndPMFMarginal h p = ndPMFMarginal h' p := by
  rw [Subsingleton.elim h h']

private theorem ndPMFMarginal_trans
    {r s n : ℕ} (hrs : r ≤ s) (hsn : s ≤ n)
    (p : PMF (ZMod (3 ^ n))) :
    ndPMFMarginal hrs (ndPMFMarginal hsn p) =
      ndPMFMarginal (hrs.trans hsn) p := by
  unfold ndPMFMarginal
  rw [PMF.map_comp]
  apply congrArg (fun f => p.map f)
  funext y
  exact Tao.taoZModThreeProjection_comp_apply hrs hsn y

private theorem ndPMFMarginal_trans_any
    {r s n : ℕ} (hrs : r ≤ s) (hsn : s ≤ n) (hrn : r ≤ n)
    (p : PMF (ZMod (3 ^ n))) :
    ndPMFMarginal hrs (ndPMFMarginal hsn p) =
      ndPMFMarginal hrn p := by
  rw [ndPMFMarginal_trans]

private theorem ndPMFMarginal_self
    {n : ℕ} (hnn : n ≤ n) (p : PMF (ZMod (3 ^ n))) :
    ndPMFMarginal hnn p = p := by
  rw [ndPMFMarginal_proof_irrel hnn (le_refl n)]
  unfold ndPMFMarginal
  rw [Tao.taoZModThreeProjection_refl]
  simpa only [RingHom.id_apply] using PMF.map_id p

private theorem ndZModPowFiberSum_pmfMass_eq_marginal
    {r n : ℕ} (hrn : r ≤ n) (p : PMF (ZMod (3 ^ n)))
    (y : ZMod (3 ^ n)) :
    Tao.zmodPowFiberSum r n (fun x => (p x).toReal) y =
      (ndPMFMarginal hrn p (Tao.taoZModThreeProjection hrn y)).toReal := by
  classical
  have hmap :
      (∑ x : ZMod (3 ^ n),
        if Tao.taoZModThreeProjection hrn y =
            Tao.taoZModThreeProjection hrn x then
          (p x).toReal else 0) =
        (ndPMFMarginal hrn p
          (Tao.taoZModThreeProjection hrn y)).toReal := by
    unfold ndPMFMarginal
    rw [Tao.pmf_map_apply_toReal_tsum, tsum_fintype]
  unfold Tao.zmodPowFiberSum
  calc
    (∑ x : ZMod (3 ^ n),
        if Tao.zmodSameResidueModPow r n x y then
          (p x).toReal else 0) =
      ∑ x : ZMod (3 ^ n),
        if Tao.taoZModThreeProjection hrn y =
            Tao.taoZModThreeProjection hrn x then
          (p x).toReal else 0 := by
      apply Finset.sum_congr rfl
      intro x _hx
      rw [Tao.zmodSameResidueModPow_iff_projection_eq hrn]
      by_cases hxy : Tao.taoZModThreeProjection hrn x =
          Tao.taoZModThreeProjection hrn y
      · rw [if_pos hxy, if_pos hxy.symm]
      · have hyx : ¬Tao.taoZModThreeProjection hrn y =
            Tao.taoZModThreeProjection hrn x := fun h => hxy h.symm
        rw [if_neg hxy, if_neg hyx]
    _ = _ := hmap

private theorem ndZModPowFiberAverage_pmfMass_eq_uniformLift
    {r n : ℕ} (hrn : r ≤ n) (p : PMF (ZMod (3 ^ n))) :
    Tao.zmodPowFiberAverage r n (fun x => (p x).toReal) =
      Tao.taoZModPowUniformLift hrn
        (fun x => (ndPMFMarginal hrn p x).toReal) := by
  funext y
  unfold Tao.zmodPowFiberAverage Tao.taoZModPowUniformLift
  rw [ndZModPowFiberSum_pmfMass_eq_marginal hrn p y]

private theorem ndTaoZModPowOscillation_pmf_eq_sum_abs_sub_uniformLift
    {r n : ℕ} (hrn : r ≤ n) (p : PMF (ZMod (3 ^ n))) :
    Tao.taoZModPowOscillation r n (fun y => (p y).toReal) =
      ∑ y : ZMod (3 ^ n),
        |(p y).toReal -
          Tao.taoZModPowUniformLift hrn
            (fun x => (ndPMFMarginal hrn p x).toReal) y| := by
  unfold Tao.taoZModPowOscillation
  change
    (∑ y : ZMod (3 ^ n),
      |(p y).toReal -
        Tao.zmodPowFiberAverage r n (fun x => (p x).toReal) y|) = _
  rw [ndZModPowFiberAverage_pmfMass_eq_uniformLift hrn p]

private theorem ndTaoZModPowOscillation_pmf_self
    (n : ℕ) (p : PMF (ZMod (3 ^ n))) :
    Tao.taoZModPowOscillation n n (fun y => (p y).toReal) = 0 := by
  rw [ndTaoZModPowOscillation_pmf_eq_sum_abs_sub_uniformLift
    (le_refl n) p]
  rw [ndPMFMarginal_self (le_refl n) p,
    Tao.taoZModPowUniformLift_refl]
  simp

private theorem ndTaoZModPowOscillation_pmf_le_add
    {r s n : ℕ} (hrs : r ≤ s) (hsn : s ≤ n)
    (p : PMF (ZMod (3 ^ n))) :
    Tao.taoZModPowOscillation r n (fun y => (p y).toReal) ≤
      Tao.taoZModPowOscillation r s
          (fun x => (ndPMFMarginal hsn p x).toReal) +
        Tao.taoZModPowOscillation s n (fun y => (p y).toReal) := by
  rw [ndTaoZModPowOscillation_pmf_eq_sum_abs_sub_uniformLift
      (hrs.trans hsn) p,
    ndTaoZModPowOscillation_pmf_eq_sum_abs_sub_uniformLift
      hrs (ndPMFMarginal hsn p),
    ndTaoZModPowOscillation_pmf_eq_sum_abs_sub_uniformLift hsn p]
  rw [ndPMFMarginal_trans]
  exact Tao.sum_abs_sub_uniformLift_trans_le hrs hsn
    (fun y => (p y).toReal)
    (fun x => (ndPMFMarginal hsn p x).toReal)
    (fun z => (ndPMFMarginal (hrs.trans hsn) p z).toReal)

private theorem ndTaoZModPowOscillation_pmf_le_sum_of_adjacent
    {m n : ℕ} (hmn : m ≤ n) (p : PMF (ZMod (3 ^ n)))
    (b : ℕ → ℝ)
    (hadj : ∀ r : ℕ, ∀ _hmr : m ≤ r, ∀ hrn : r < n,
      Tao.taoZModPowOscillation r (r + 1)
        (fun y => (ndPMFMarginal (Nat.succ_le_of_lt hrn) p y).toReal) ≤
        b r) :
    Tao.taoZModPowOscillation m n (fun y => (p y).toReal) ≤
      ∑ r ∈ Finset.Ico m n, b r := by
  induction n, hmn using Nat.le_induction with
  | base =>
      simp [ndTaoZModPowOscillation_pmf_self]
  | succ n hmn ih =>
      let pn : PMF (ZMod (3 ^ n)) :=
        ndPMFMarginal (Nat.le_succ n) p
      have hadj' : ∀ r : ℕ, ∀ hmr : m ≤ r, ∀ hrn : r < n,
          Tao.taoZModPowOscillation r (r + 1)
            (fun y =>
              (ndPMFMarginal (Nat.succ_le_of_lt hrn) pn y).toReal) ≤
            b r := by
        intro r hmr hrn
        have h := hadj r hmr (hrn.trans (Nat.lt_succ_self n))
        have hmarg :
            ndPMFMarginal (Nat.succ_le_of_lt hrn) pn =
              ndPMFMarginal
                (Nat.succ_le_of_lt (hrn.trans (Nat.lt_succ_self n))) p := by
          dsimp [pn]
          exact ndPMFMarginal_trans_any _ _ _ p
        rw [hmarg]
        exact h
      have ih' :
          Tao.taoZModPowOscillation m n (fun y => (pn y).toReal) ≤
            ∑ r ∈ Finset.Ico m n, b r :=
        ih pn hadj'
      have htop :
          Tao.taoZModPowOscillation n (n + 1)
              (fun y => (p y).toReal) ≤ b n := by
        have h := hadj n hmn (Nat.lt_succ_self n)
        rw [ndPMFMarginal_self] at h
        exact h
      calc
        Tao.taoZModPowOscillation m (n + 1)
            (fun y => (p y).toReal) ≤
          Tao.taoZModPowOscillation m n (fun y => (pn y).toReal) +
            Tao.taoZModPowOscillation n (n + 1)
              (fun y => (p y).toReal) := by
            simpa only [pn] using
              ndTaoZModPowOscillation_pmf_le_add hmn
                (Nat.le_succ n) p
        _ ≤ (∑ r ∈ Finset.Ico m n, b r) + b n :=
          add_le_add ih' htop
        _ = ∑ r ∈ Finset.Ico m (n + 1), b r := by
          rw [Finset.sum_Ico_succ_top hmn]

private theorem ndSection7FiberPMF_oscillation_le_terminalStep
    (A n m L : ℕ) (K Ccore : ℝ)
    (hn : 1 ≤ n) (hmn : m ≤ n) (hhigh : 9 * n ≤ 10 * m)
    (hnL : n ≤ L) (hwin : ndSection7M1Window K n L)
    (hcore : ndSection7ConditionedFM1CoreNatAt (A + 1)
      (K + Real.sqrt (63 * ((A : ℝ) + 2))) Ccore) :
    Tao.taoZModPowOscillation m n
      (fun y => (ndSection7FiberPMF n L
        (Nat.zero_lt_one.trans_le hn) hnL y).toReal) ≤
      Ccore / (n : ℝ) ^ (A + 1) := by
  have hKK' :
      K ≤ K + Real.sqrt (63 * ((A : ℝ) + 2)) :=
    le_add_of_nonneg_right (Real.sqrt_nonneg _)
  have hwin' : ndSection7M1Window
      (K + Real.sqrt (63 * ((A : ℝ) + 2))) n L := by
    unfold ndSection7M1Window at hwin ⊢
    exact hwin.trans
      (mul_le_mul_of_nonneg_right hKK' (Real.sqrt_nonneg _))
  exact hcore n hn m hmn hhigh L hnL hwin'

private theorem exists_ndSection7ConditionedFM1Nat_large
    (A : ℕ) (hA : 0 < A) (K : ℝ) (hK : 1 ≤ K) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ M0 : ℕ, 100 ≤ M0 ∧
      ∀ n : ℕ, (hn : 1 ≤ n) →
        ∀ m : ℕ, (hm : 1 ≤ m) → m ≤ n → M0 ≤ m →
          ∀ L : ℕ, (hL : n ≤ L) → ndSection7M1Window K n L →
            Tao.taoZModPowOscillation m n
                (fun y => (ndSection7FiberPMF n L
                  (Nat.zero_lt_one.trans_le hn) hL y).toReal) ≤
              C / (m : ℝ) ^ A := by
  let delta : ℝ := Real.sqrt (63 * ((A : ℝ) + 2))
  let K' : ℝ := K + delta
  have hdelta : 0 < delta := by
    dsimp [delta]
    positivity
  have hK' : 1 ≤ K' := by
    dsimp [K']
    exact hK.trans (le_add_of_nonneg_right hdelta.le)
  obtain ⟨Ccore, hCcore, hcore⟩ :=
    ndConditionedFM1CoreNat (A + 1) (by omega) K' hK'
  let D : ℝ := Ccore + 4
  have hD : 0 ≤ D := by
    dsimp [D]
    linarith
  have hKquarter : 0 < K / 4 := by
    exact div_pos (zero_lt_one.trans_le hK) (by norm_num)
  have hdeltatwelfth : 0 < delta / 12 := by
    exact div_pos hdelta (by norm_num)
  rcases Filter.eventually_atTop.1
      (eventually_four_mul_sqrt_nat_mul_log_le
        (K / 4) hKquarter) with ⟨NK, hNK⟩
  rcases Filter.eventually_atTop.1
      (eventually_four_mul_sqrt_nat_mul_log_le
        (delta / 12) hdeltatwelfth) with ⟨Ndelta, hNdelta⟩
  let M0 : ℕ := max 100 (max NK Ndelta)
  have hM100 : 100 ≤ M0 := by
    dsimp [M0]
    exact le_max_left _ _
  have hMNK : NK ≤ M0 := by
    dsimp [M0]
    exact (le_max_left NK Ndelta).trans
      (le_max_right 100 (max NK Ndelta))
  have hMNdelta : Ndelta ≤ M0 := by
    dsimp [M0]
    exact (le_max_right NK Ndelta).trans
      (le_max_right 100 (max NK Ndelta))
  refine ⟨D, hD, M0, hM100, ?_⟩
  intro n hn m hm hmn hM0m L hL hwin
  have hn0 : 0 < n := Nat.zero_lt_one.trans_le hn
  have hnNK : NK ≤ n := hMNK.trans (hM0m.trans hmn)
  have hKsqrt :
      K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) ≤ (n : ℝ) := by
    calc
      K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) =
          4 * (K / 4) *
            Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) := by ring
      _ ≤ (n : ℝ) := hNK n hnNK
  have hL3n : L ≤ 3 * n := by
    have hdisp :
        (L : ℝ) - 2 * (n : ℝ) ≤
          K * Real.sqrt ((n : ℝ) * Real.log (n : ℝ)) :=
      (le_abs_self ((L : ℝ) - 2 * (n : ℝ))).trans hwin
    have hLreal : (L : ℝ) ≤ 3 * (n : ℝ) := by linarith
    exact_mod_cast hLreal
  let p : PMF (ZMod (3 ^ n)) := ndSection7FiberPMF n L hn0 hL
  have htelescope :
      Tao.taoZModPowOscillation m n (fun y => (p y).toReal) ≤
        ∑ r ∈ Finset.Ico m n,
          D / (((r + 1 : ℕ) : ℝ) ^ (A + 1)) := by
    apply ndTaoZModPowOscillation_pmf_le_sum_of_adjacent
      hmn p (fun r => D / (((r + 1 : ℕ) : ℝ) ^ (A + 1)))
    intro r hmr hrn
    have hrM0 : M0 ≤ r := hM0m.trans hmr
    have hrTen : 10 ≤ r := (by omega : 10 ≤ M0).trans hrM0
    by_cases hjn : r + 1 < n
    · have hjNdelta : Ndelta ≤ r + 1 :=
        hMNdelta.trans (hrM0.trans (Nat.le_succ r))
      have hguard := hNdelta (r + 1) hjNdelta
      have hu3 :
          delta * Real.sqrt
              (((r + 1 : ℕ) : ℝ) * Real.log ((r + 1 : ℕ) : ℝ)) ≤
            3 * ((r + 1 : ℕ) : ℝ) := by
        calc
          delta * Real.sqrt
                (((r + 1 : ℕ) : ℝ) * Real.log ((r + 1 : ℕ) : ℝ)) =
              3 * (4 * (delta / 12) * Real.sqrt
                (((r + 1 : ℕ) : ℝ) * Real.log ((r + 1 : ℕ) : ℝ))) := by
            ring
          _ ≤ 3 * ((r + 1 : ℕ) : ℝ) :=
            mul_le_mul_of_nonneg_left hguard (by norm_num)
      have hstep :=
        ndSection7FiberPMF_projection_oscillation_le_oneStep
          A n r (r + 1) L K Ccore hCcore
          (by omega) hjn (Nat.le_succ r) (by omega)
          hL hL3n hwin (by simpa only [delta] using hu3)
          (by simpa only [K', delta] using hcore)
      simpa only [p, ndPMFMarginal, D] using hstep
    · have hjEq : r + 1 = n := by omega
      subst n
      rw [ndPMFMarginal_self]
      have hterm := ndSection7FiberPMF_oscillation_le_terminalStep
        A (r + 1) r L K Ccore (by omega) (Nat.le_succ r)
          (by omega) hL hwin
          (by simpa only [K', delta] using hcore)
      exact hterm.trans
        (div_le_div_of_nonneg_right
          (by dsimp [D]; linarith) (by positivity))
  calc
    Tao.taoZModPowOscillation m n
        (fun y => (ndSection7FiberPMF n L hn0 hL y).toReal) =
      Tao.taoZModPowOscillation m n (fun y => (p y).toReal) := by rfl
    _ ≤ ∑ r ∈ Finset.Ico m n,
        D / (((r + 1 : ℕ) : ℝ) ^ (A + 1)) := htelescope
    _ = D * (∑ r ∈ Finset.Ico m n,
        1 / (((r + 1 : ℕ) : ℝ) ^ (A + 1))) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r _hr
      ring
    _ ≤ D * (1 / (m : ℝ) ^ A) :=
      mul_le_mul_of_nonneg_left
        (Tao.sum_Ico_one_div_succ_pow_le hA hm hmn) hD
    _ = D / (m : ℝ) ^ A := by ring

/-- Conditioned fixed-total FM1 at one positive natural exponent and one
central-window constant, over the complete lower-scale range. -/
def ndSection7ConditionedFM1NatAt (A : ℕ) (K C : ℝ) : Prop :=
  ∀ n : ℕ, (hn : 1 ≤ n) →
    ∀ m : ℕ, 1 ≤ m → m ≤ n →
      ∀ L : ℕ, (hL : n ≤ L) → ndSection7M1Window K n L →
        Tao.taoZModPowOscillation m n
            (fun y => (ndSection7FiberPMF n L
              (Nat.zero_lt_one.trans_le hn) hL y).toReal) ≤
          C / (m : ℝ) ^ A

/-- Natural-exponent full-FM1 statement from the frozen source. -/
def NDConditionedFM1NatStatement : Prop :=
  ∀ A : ℕ, 0 < A →
    ∀ K : ℝ, 1 ≤ K →
      ∃ C : ℝ, 0 ≤ C ∧ ndSection7ConditionedFM1NatAt A K C

/-- Full conditioned fixed-total FM1 at every positive natural exponent. -/
theorem ndConditionedFM1Nat : NDConditionedFM1NatStatement := by
  intro A hA K hK
  obtain ⟨Clarge, hClarge, M0, _hM0, hlarge⟩ :=
    exists_ndSection7ConditionedFM1Nat_large A hA K hK
  let Csmall : ℝ := 2 * (M0 : ℝ) ^ A
  let Cfinal : ℝ := max Clarge Csmall
  have hCsmall : 0 ≤ Csmall := by
    dsimp [Csmall]
    positivity
  have hCfinal : 0 ≤ Cfinal :=
    hClarge.trans (le_max_left Clarge Csmall)
  refine ⟨Cfinal, hCfinal, ?_⟩
  intro n hn m hm hmn L hL hwin
  have hm0 : 0 < m := Nat.zero_lt_one.trans_le hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm0
  have hden : 0 < (m : ℝ) ^ A := pow_pos hmR A
  by_cases hcut : M0 ≤ m
  · have hbound := hlarge n hn m hm hmn hcut L hL hwin
    exact hbound.trans
      (div_le_div_of_nonneg_right
        (le_max_left Clarge Csmall) hden.le)
  · have hmM0 : m ≤ M0 := by omega
    have hmM0R : (m : ℝ) ≤ (M0 : ℝ) := by exact_mod_cast hmM0
    have hpow : (m : ℝ) ^ A ≤ (M0 : ℝ) ^ A :=
      pow_le_pow_left₀ hmR.le hmM0R A
    have hscaled : 2 * (m : ℝ) ^ A ≤ Cfinal := by
      calc
        2 * (m : ℝ) ^ A ≤ 2 * (M0 : ℝ) ^ A :=
          mul_le_mul_of_nonneg_left hpow (by norm_num)
        _ = Csmall := rfl
        _ ≤ Cfinal := le_max_right Clarge Csmall
    have htwo := ndSection7FiberPMF_oscillation_le_two
      m n L (Nat.zero_lt_one.trans_le hn) hmn hL
    exact htwo.trans ((le_div_iff₀ hden).2 hscaled)

/-- Conditioned full FM1 at one positive real exponent. -/
def ndSection7ConditionedFM1RealAt (A K C : ℝ) : Prop :=
  ∀ n : ℕ, (hn : 1 ≤ n) →
    ∀ m : ℕ, 1 ≤ m → m ≤ n →
      ∀ L : ℕ, (hL : n ≤ L) → ndSection7M1Window K n L →
        Tao.taoZModPowOscillation m n
            (fun y => (ndSection7FiberPMF n L
              (Nat.zero_lt_one.trans_le hn) hL y).toReal) ≤
          C / Real.rpow (m : ℝ) A

/-- Frozen-v10 positive-real full-FM1 statement. -/
def NDConditionedFM1Statement : Prop :=
  ∀ A : ℝ, 0 < A →
    ∀ K : ℝ, 1 ≤ K →
      ∃ C : ℝ, 0 ≤ C ∧ ndSection7ConditionedFM1RealAt A K C

/-- The full natural-exponent theorem implies the frozen positive-real FM1
by taking the natural ceiling of the exponent. -/
theorem ndConditionedFM1 : NDConditionedFM1Statement := by
  intro A hA K hK
  let q : ℕ := ⌈A⌉₊
  have hq : 0 < q := by
    dsimp [q]
    exact Nat.ceil_pos.mpr hA
  obtain ⟨C, hC, hnat⟩ := ndConditionedFM1Nat q hq K hK
  refine ⟨C, hC, ?_⟩
  intro n hn m hm hmn L hL hwin
  have hbound := hnat n hn m hm hmn L hL hwin
  have hm0 : 0 < m := Nat.zero_lt_one.trans_le hm
  have hmReal : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm0
  have hmOne : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hAq : A ≤ (q : ℝ) := by
    dsimp [q]
    exact Nat.le_ceil A
  have hrpowPow : Real.rpow (m : ℝ) A ≤ (m : ℝ) ^ q := by
    calc
      Real.rpow (m : ℝ) A ≤ Real.rpow (m : ℝ) (q : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hmOne hAq
      _ = (m : ℝ) ^ q := Real.rpow_natCast (m : ℝ) q
  have hrpowPos : 0 < Real.rpow (m : ℝ) A :=
    Real.rpow_pos_of_pos hmReal A
  exact hbound.trans
    (div_le_div_of_nonneg_left hC hrpowPos hrpowPow)

end

end ND
end Erdos1135
