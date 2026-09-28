import Erdos1135.ND.Fourier.FixedTotalRatioTails
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Countable Fixed-Total Ratio Normalization

This leaf normalizes a pairwise log-likelihood oscillation on an arbitrary
PMF carrier, converts it to the pointwise mass-proportional `43/25` bound,
and specializes the result to the fixed-total source and its Geom(2)
reference.  The two outside tails remain separate from the central charge.
-/

namespace Erdos1135
namespace ND

open Tao

noncomputable section

/-- PMF mass on a predicate, expressed directly as a subtype sum. -/
noncomputable def ndPMFGoodMass
    {α : Type*} (p : PMF α) (Good : α → Prop) : ℝ :=
  ∑' u : {u // Good u}, (p u).toReal

/-- The native Good and outside masses partition the complete PMF mass. -/
theorem ndPMFGoodMass_add_outsideMass_eq_one
    {α : Type*} (p : PMF α) (Good : α → Prop) :
    ndPMFGoodMass p Good + ndPMFOutsideMass p Good = 1 := by
  have hp := Tao.taoPMF_summable_toReal p
  have hsplit := hp.tsum_subtype_add_tsum_subtype_compl {u | Good u}
  have htotal : (∑' u : α, (p u).toReal) = 1 := by
    have h := congrArg ENNReal.toReal (PMF.tsum_coe p)
    rw [ENNReal.tsum_toReal_eq (PMF.apply_ne_top p)] at h
    simpa using h
  rw [ndPMFOutsideMass_eq_pmfOuterMass_compl,
    Tao.pmfOuterMass_toReal_eq_tsum_subtype]
  unfold ndPMFGoodMass
  exact hsplit.trans htotal

private theorem ndPMFOutsideMass_nonneg
    {α : Type*} (p : PMF α) (Good : α → Prop) :
    0 ≤ ndPMFOutsideMass p Good := by
  rw [ndPMFOutsideMass_eq_pmfOuterMass_compl]
  exact ENNReal.toReal_nonneg

/-- Pairwise log-ratio oscillation and two outside-mass bounds normalize the
log ratio at every requested Good atom.  No finite carrier or minimizing atom
is used. -/
theorem abs_log_pmfRatio_le_of_pairwise_oscillation
    {α : Type*} (p q : PMF α) (Good : α → Prop)
    {eps thetaP thetaQ : ℝ}
    (hpos : ∀ v, Good v →
      0 < (p v).toReal ∧ 0 < (q v).toReal)
    (hosc : ∀ v w, Good v → Good w →
      |Real.log ((p v).toReal / (q v).toReal) -
        Real.log ((p w).toReal / (q w).toReal)| ≤ eps)
    (hpOutside : ndPMFOutsideMass p Good ≤ thetaP)
    (hqOutside : ndPMFOutsideMass q Good ≤ thetaQ)
    (heta : eps + 2 * (thetaP + thetaQ) ≤ 1)
    {u : α} (hu : Good u) :
    |Real.log ((p u).toReal / (q u).toReal)| ≤
      eps + 2 * (thetaP + thetaQ) := by
  let lu : ℝ := Real.log ((p u).toReal / (q u).toReal)
  have huPos := hpos u hu
  have heps0 : 0 ≤ eps := by
    have h := hosc u u hu hu
    simpa using h
  have hthetaP0 : 0 ≤ thetaP :=
    (ndPMFOutsideMass_nonneg p Good).trans hpOutside
  have hthetaQ0 : 0 ≤ thetaQ :=
    (ndPMFOutsideMass_nonneg q Good).trans hqOutside
  have hthetaPHalf : thetaP ≤ 1 / 2 := by nlinarith
  have hthetaQHalf : thetaQ ≤ 1 / 2 := by nlinarith
  have heta0 : 0 ≤ eps + 2 * (thetaP + thetaQ) := by positivity
  have hpG : Summable fun v : {v // Good v} => (p v).toReal := by
    simpa using (Tao.taoPMF_summable_toReal p).subtype {v | Good v}
  have hqG : Summable fun v : {v // Good v} => (q v).toReal := by
    simpa using (Tao.taoPMF_summable_toReal q).subtype {v | Good v}
  have hLowerAtom : ∀ v : {v // Good v},
      Real.exp (lu - eps) * (q v).toReal ≤ (p v).toReal := by
    intro v
    have hvPos := hpos v v.property
    have hvOsc := abs_le.mp (hosc u v hu v.property)
    have hlog :
        lu - eps ≤ Real.log ((p v).toReal / (q v).toReal) := by
      dsimp [lu]
      linarith
    calc
      Real.exp (lu - eps) * (q v).toReal ≤
          Real.exp (Real.log ((p v).toReal / (q v).toReal)) *
            (q v).toReal :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hlog) hvPos.2.le
      _ = (p v).toReal := by
        rw [Real.exp_log (div_pos hvPos.1 hvPos.2)]
        field_simp [hvPos.2.ne']
  have hUpperAtom : ∀ v : {v // Good v},
      (p v).toReal ≤ Real.exp (lu + eps) * (q v).toReal := by
    intro v
    have hvPos := hpos v v.property
    have hvOsc := abs_le.mp (hosc u v hu v.property)
    have hlog :
        Real.log ((p v).toReal / (q v).toReal) ≤ lu + eps := by
      dsimp [lu]
      linarith
    calc
      (p v).toReal =
          Real.exp (Real.log ((p v).toReal / (q v).toReal)) *
            (q v).toReal := by
        rw [Real.exp_log (div_pos hvPos.1 hvPos.2)]
        field_simp [hvPos.2.ne']
      _ ≤ Real.exp (lu + eps) * (q v).toReal :=
        mul_le_mul_of_nonneg_right (Real.exp_le_exp.mpr hlog) hvPos.2.le
  have hLowerSum :
      Real.exp (lu - eps) * ndPMFGoodMass q Good ≤
        ndPMFGoodMass p Good := by
    unfold ndPMFGoodMass
    rw [← tsum_mul_left]
    exact (hqG.mul_left _).tsum_le_tsum hLowerAtom hpG
  have hUpperSum :
      ndPMFGoodMass p Good ≤
        Real.exp (lu + eps) * ndPMFGoodMass q Good := by
    unfold ndPMFGoodMass
    rw [← tsum_mul_left]
    exact hpG.tsum_le_tsum hUpperAtom (hqG.mul_left _)
  have hpSplit := ndPMFGoodMass_add_outsideMass_eq_one p Good
  have hqSplit := ndPMFGoodMass_add_outsideMass_eq_one q Good
  have hpGoodLower : 1 - thetaP ≤ ndPMFGoodMass p Good := by
    linarith
  have hqGoodLower : 1 - thetaQ ≤ ndPMFGoodMass q Good := by
    linarith
  have hpGoodLeOne : ndPMFGoodMass p Good ≤ 1 := by
    linarith [ndPMFOutsideMass_nonneg p Good]
  have hqGoodLeOne : ndPMFGoodMass q Good ≤ 1 := by
    linarith [ndPMFOutsideMass_nonneg q Good]
  have hLowerExp : Real.exp (-2 * thetaP) ≤ Real.exp (lu + eps) := by
    calc
      Real.exp (-2 * thetaP) ≤ 1 - thetaP :=
        exp_neg_two_mul_le_one_sub hthetaP0 hthetaPHalf
      _ ≤ ndPMFGoodMass p Good := hpGoodLower
      _ ≤ Real.exp (lu + eps) * ndPMFGoodMass q Good := hUpperSum
      _ ≤ Real.exp (lu + eps) * 1 :=
        mul_le_mul_of_nonneg_left hqGoodLeOne (Real.exp_pos _).le
      _ = Real.exp (lu + eps) := by ring
  have hluLower : -eps - 2 * thetaP ≤ lu := by
    have h := Real.exp_le_exp.mp hLowerExp
    linarith
  have hUpperExp : Real.exp ((lu - eps) + (-2 * thetaQ)) ≤ 1 := by
    rw [Real.exp_add]
    calc
      Real.exp (lu - eps) * Real.exp (-2 * thetaQ) ≤
          Real.exp (lu - eps) * ndPMFGoodMass q Good :=
        mul_le_mul_of_nonneg_left
          ((exp_neg_two_mul_le_one_sub hthetaQ0 hthetaQHalf).trans
            hqGoodLower)
          (Real.exp_pos _).le
      _ ≤ ndPMFGoodMass p Good := hLowerSum
      _ ≤ 1 := hpGoodLeOne
  have hluUpper : lu ≤ eps + 2 * thetaQ := by
    have h := Real.exp_le_one_iff.mp hUpperExp
    linarith
  change |lu| ≤ eps + 2 * (thetaP + thetaQ)
  exact abs_le.mpr ⟨by linarith, by linarith⟩

private theorem abs_exp_sub_one_le_fortythree_div_twentyfive
    {x eta : ℝ} (heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hx : |x| ≤ eta) :
    |Real.exp x - 1| ≤ (43 / 25 : ℝ) * eta := by
  have hExpOne : Real.exp 1 ≤ (68 / 25 : ℝ) :=
    Real.exp_one_lt_d9.le.trans (by norm_num)
  by_cases hx0 : 0 ≤ x
  · have hx1 : x ≤ 1 := (le_abs_self x).trans (hx.trans heta1)
    have hChord : Real.exp x ≤ x * Real.exp 1 + (1 - x) := by
      simpa only [smul_eq_mul, mul_one, mul_zero, add_zero,
          Real.exp_zero] using
        (convexOn_exp.2
          (Set.mem_univ (1 : ℝ)) (Set.mem_univ (0 : ℝ))
          hx0 (sub_nonneg.mpr hx1) (by ring))
    rw [abs_of_nonneg (sub_nonneg.mpr (Real.one_le_exp hx0))]
    calc
      Real.exp x - 1 ≤ (x * Real.exp 1 + (1 - x)) - 1 :=
        sub_le_sub_right hChord 1
      _ = x * (Real.exp 1 - 1) := by ring
      _ ≤ x * ((68 / 25 : ℝ) - 1) :=
        mul_le_mul_of_nonneg_left (sub_le_sub_right hExpOne 1) hx0
      _ = (43 / 25 : ℝ) * x := by ring
      _ ≤ (43 / 25 : ℝ) * eta :=
        mul_le_mul_of_nonneg_left ((le_abs_self x).trans hx) (by norm_num)
  · have hxNonpos : x ≤ 0 := le_of_not_ge hx0
    have hExpLe : Real.exp x ≤ 1 := Real.exp_le_one_iff.mpr hxNonpos
    rw [abs_of_nonpos (sub_nonpos.mpr hExpLe)]
    calc
      -(Real.exp x - 1) ≤ -x := by
        linarith [Real.add_one_le_exp x]
      _ ≤ eta := (neg_le_abs x).trans hx
      _ ≤ (43 / 25 : ℝ) * eta := by
        simpa only [one_mul] using
          mul_le_mul_of_nonneg_right
            (show (1 : ℝ) ≤ 43 / 25 by norm_num) heta0

/-- Countable R1 in the pointwise mass-proportional form needed by the
weighted central-plus-tail adapter. -/
theorem abs_pmf_sub_le_reference_of_logRatio_oscillation
    {α : Type*} (p q : PMF α) (Good : α → Prop)
    {eps thetaP thetaQ : ℝ}
    (hpos : ∀ v, Good v →
      0 < (p v).toReal ∧ 0 < (q v).toReal)
    (hosc : ∀ v w, Good v → Good w →
      |Real.log ((p v).toReal / (q v).toReal) -
        Real.log ((p w).toReal / (q w).toReal)| ≤ eps)
    (hpOutside : ndPMFOutsideMass p Good ≤ thetaP)
    (hqOutside : ndPMFOutsideMass q Good ≤ thetaQ)
    (heta : eps + 2 * (thetaP + thetaQ) ≤ 1)
    {u : α} (hu : Good u) :
    |(p u).toReal - (q u).toReal| ≤
      (43 / 25 : ℝ) * (eps + 2 * (thetaP + thetaQ)) *
        (q u).toReal := by
  let eta : ℝ := eps + 2 * (thetaP + thetaQ)
  let lu : ℝ := Real.log ((p u).toReal / (q u).toReal)
  have huPos := hpos u hu
  have hlog : |lu| ≤ eta := by
    simpa only [lu, eta] using
      abs_log_pmfRatio_le_of_pairwise_oscillation
        p q Good hpos hosc hpOutside hqOutside heta hu
  have heta0 : 0 ≤ eta := (abs_nonneg lu).trans hlog
  have hscalar :
      |Real.exp lu - 1| ≤ (43 / 25 : ℝ) * eta :=
    abs_exp_sub_one_le_fortythree_div_twentyfive heta0 heta hlog
  have hpEq : (p u).toReal = Real.exp lu * (q u).toReal := by
    dsimp [lu]
    rw [Real.exp_log (div_pos huPos.1 huPos.2)]
    field_simp [huPos.2.ne']
  rw [hpEq]
  calc
    |Real.exp lu * (q u).toReal - (q u).toReal| =
        |Real.exp lu - 1| * (q u).toReal := by
      rw [show Real.exp lu * (q u).toReal - (q u).toReal =
          (Real.exp lu - 1) * (q u).toReal by ring,
        abs_mul, abs_of_nonneg huPos.2.le]
    _ ≤ ((43 / 25 : ℝ) * eta) * (q u).toReal :=
      mul_le_mul_of_nonneg_right hscalar huPos.2.le
    _ = (43 / 25 : ℝ) * (eps + 2 * (thetaP + thetaQ)) *
        (q u).toReal := by rfl

/-- Exact fixed-total weighted SL-D-RAT endpoint.  The central error is
proportional to the full reference expectation, and the two outside tails
contribute exactly `4/j^3 * H`. -/
theorem abs_ndFixedTotalHeadTotalPMF_weightedDifference_le_ratio
    {j n L : ℕ} (hj : 150 ≤ j) (hjn : 8 * j ≤ n)
    (hD : |(L : ℝ) - 2 * (n : ℝ)| ≤ (n : ℝ) / 8)
    (hDelta :
      ndFixedTotalRatioCenterOffset j n L ≤ ndFixedTotalRatioScale j)
    (hEta : ndFixedTotalRatioEps j n L + 8 / (j : ℝ) ^ 3 ≤ 1)
    (phi : ℕ → ℝ) (H : ℝ)
    (hphi0 : ∀ u, 0 ≤ phi u) (hphiH : ∀ u, phi u ≤ H) :
    |∑' u,
        ((ndFixedTotalHeadTotalPMF j n L (by omega) (by omega)
            (ndFixedTotalRatio_n_le_L hj hjn hD) u).toReal -
          (ndGeom2EndpointPMF j u).toReal) * phi u| ≤
      (43 / 25 : ℝ) *
          (ndFixedTotalRatioEps j n L + 8 / (j : ℝ) ^ 3) *
          ndPMFWeightedExpectation (ndGeom2EndpointPMF j) phi +
        4 / (j : ℝ) ^ 3 * H := by
  let p : PMF ℕ :=
    ndFixedTotalHeadTotalPMF j n L (by omega) (by omega)
      (ndFixedTotalRatio_n_le_L hj hjn hD)
  let q : PMF ℕ := ndGeom2EndpointPMF j
  let Good : ℕ → Prop := ndFixedTotalRatioGood j
  let eps : ℝ := ndFixedTotalRatioEps j n L
  let theta : ℝ := 2 / (j : ℝ) ^ 3
  let centralCoeff : ℝ := (43 / 25 : ℝ) * (eps + 8 / (j : ℝ) ^ 3)
  have hEtaGeneric : eps + 2 * (theta + theta) ≤ 1 := by
    calc
      eps + 2 * (theta + theta) =
          ndFixedTotalRatioEps j n L + 8 / (j : ℝ) ^ 3 := by
        dsimp [eps, theta]
        ring
      _ ≤ 1 := hEta
  have hcentral : ∀ u, Good u →
      |(p u).toReal - (q u).toReal| ≤
        centralCoeff * (q u).toReal := by
    intro u hu
    have hR1 := abs_pmf_sub_le_reference_of_logRatio_oscillation
      p q Good
      (fun v hv => by
        dsimp [p, q, Good] at hv ⊢
        exact ndFixedTotalHeadTotalPMF_and_reference_pos_of_ratioGood
          hj hjn hD hv)
      (fun v w hv hw => by
        dsimp [p, q, Good] at hv hw ⊢
        exact
          abs_log_ndFixedTotalHeadTotalPMF_likelihoodRatio_sub_le_ratioEps
            hj hjn hD hv hw)
      (ndFixedTotalHeadTotalPMF_outside_ratioGood_le_two_div_cube
        hj hjn hD hDelta)
      (ndGeom2EndpointPMF_outside_ratioGood_le_two_div_cube hj)
      hEtaGeneric hu
    dsimp [centralCoeff, eps, theta]
    convert hR1 using 1 <;> ring
  have heps0 : 0 ≤ eps := by
    dsimp [eps]
    unfold ndFixedTotalRatioEps ndFixedTotalRatioCenterOffset
    have hlog : 0 ≤ Real.log (j : ℝ) :=
      Real.log_nonneg (by exact_mod_cast (show 1 ≤ j by omega))
    have hnR : (0 : ℝ) < (n : ℝ) := by
      exact_mod_cast (show 0 < n by omega)
    positivity
  have hcentralCoeff0 : 0 ≤ centralCoeff := by
    dsimp [centralCoeff]
    have hjR : (0 : ℝ) < (j : ℝ) := by positivity
    positivity
  have hH : 0 ≤ H := (hphi0 0).trans (hphiH 0)
  have hpTail : ndPMFOutsideMass p Good ≤ theta := by
    simpa only [p, Good, theta] using
      ndFixedTotalHeadTotalPMF_outside_ratioGood_le_two_div_cube
        hj hjn hD hDelta
  have hqTail : ndPMFOutsideMass q Good ≤ theta := by
    simpa only [q, Good, theta] using
      ndGeom2EndpointPMF_outside_ratioGood_le_two_div_cube hj
  have hAdapter := abs_ndPMFWeightedDifference_le_reference_add_outside
    p q Good phi H centralCoeff theta theta hH hcentralCoeff0
      hphi0 hphiH hcentral hpTail hqTail
  change |∑' u, ((p u).toReal - (q u).toReal) * phi u| ≤ _
  calc
    |∑' u, ((p u).toReal - (q u).toReal) * phi u| ≤
        centralCoeff * ndPMFWeightedExpectation q phi +
          H * (theta + theta) := hAdapter
    _ = (43 / 25 : ℝ) *
          (ndFixedTotalRatioEps j n L + 8 / (j : ℝ) ^ 3) *
          ndPMFWeightedExpectation (ndGeom2EndpointPMF j) phi +
        4 / (j : ℝ) ^ 3 * H := by
      dsimp [centralCoeff, eps, theta, q]
      ring

end

end ND
end Erdos1135
