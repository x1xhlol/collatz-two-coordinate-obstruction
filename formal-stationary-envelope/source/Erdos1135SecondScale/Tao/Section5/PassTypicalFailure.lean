/-
Compatibility modification, 8 October 2026: proof-tactic syntax and unused binder names only.
See provenance/envelope-linter-patches.json for exact source hashes and patches.
-/
/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Probability.Geom2PrefixTypical
import Erdos1135SecondScale.Tao.Probability.FullL1
import Erdos1135SecondScale.Tao.Section5.PassTypicalEvent
import Erdos1135SecondScale.Tao.Section5.Prop19Output
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-!
# Section 5 Closed-Prefix Failure Probability

This leaf identifies failure of the closed Section 5 prefix condition with
one event on the full valuation list.  It then bounds the ideal event by one
finite prefix union and transfers that whole event through Proposition 1.9
once.  It contains no passage event, affine atom, Section 6 concentration,
Fourier, or renewal argument.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

open Filter
open scoped Topology

/-- The one full-list event encoding failure at some positive prefix. -/
def taoSection5ClosedPrefixBadEvent (B : ℕ) : Set (List ℕ+) :=
  taoGeom2PrefixBadEvent
    (taoSection5TypicalSlack B) (taoSection5N0 B)

private theorem taoGeom2CenteredListWeight_take_eq
    {as : List ℕ+} {n j : ℕ} (hlen : as.length = n) (hj : j ≤ n) :
    taoGeom2CenteredListWeight (as.take j) =
      (taoTupleWeight (as.take j) : ℝ) - 2 * (j : ℝ) := by
  unfold taoGeom2CenteredListWeight
  rw [List.length_take]
  rw [hlen, Nat.min_eq_left hj]

/-- On an exact-length list, failure of closed typicality is exactly failure
at one positive prefix.  The zero prefix is excluded using positivity of the
common threshold. -/
theorem taoSection5_not_closedTypical_iff_prefixBad
    {B : ℕ} {as : List ℕ+}
    (hlen : as.length = taoSection5N0 B)
    (hslack : 0 < taoSection5TypicalSlack B) :
    ¬ taoSection5TypicalTuple B (taoSection5N0 B) as ↔
      as ∈ taoSection5ClosedPrefixBadEvent B := by
  constructor
  · intro hnot
    by_contra hnotBad
    apply hnot
    refine ⟨hlen, ?_⟩
    intro j hj
    by_cases hj0 : j = 0
    · subst j
      simp [taoTupleWeight, hslack.le]
    · let k : Fin (taoSection5N0 B) := ⟨j - 1, by omega⟩
      have hknot :
          ¬ taoSection5TypicalSlack B <
            |taoGeom2CenteredListWeight (as.take (k.1 + 1))| := by
        intro hk
        apply hnotBad
        exact ⟨k, hk⟩
      have hkj : k.1 + 1 = j := by
        dsimp [k]
        omega
      rw [hkj] at hknot
      rw [taoGeom2CenteredListWeight_take_eq hlen hj] at hknot
      exact not_lt.mp hknot
  · intro hbad htyp
    rcases hbad with ⟨j, hjbad⟩
    have hj : j.1 + 1 ≤ taoSection5N0 B := by omega
    have hbound := htyp.2 (j.1 + 1) hj
    rw [taoGeom2CenteredListWeight_take_eq hlen hj] at hjbad
    exact (not_lt_of_ge hbound) hjbad

/-- Mapping an arbitrary odd source to its full valuation list identifies the
one list event with the complement of the closed-good source event. -/
theorem taoProp19ActualValuationLaw_closedPrefixBad
    (B : ℕ) (μ : PMF TaoOddNat)
    (hslack : 0 < taoSection5TypicalSlack B) :
    (taoProp19ActualValuationLaw μ (taoSection5N0 B)).toOuterMeasure
        (taoSection5ClosedPrefixBadEvent B) =
      μ.toOuterMeasure (taoSection5ClosedGoodEvent B)ᶜ := by
  unfold taoProp19ActualValuationLaw
  rw [PMF.toOuterMeasure_map_apply]
  congr 1
  ext N
  simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_setOf_eq,
    taoSection5ClosedGoodEvent]
  exact (taoSection5_not_closedTypical_iff_prefixBad
    (syracuseValuationPNatList_length (taoSection5N0 B) N.1 N.2)
    hslack).symm

private theorem eventually_two_mul_log_mul_exp_neg_root_le_delta :
    ∀ᶠ B : ℕ in atTop,
      2 * Real.log B *
          Real.exp (-(Real.rpow (Real.log B) (1 / 5 : ℝ)) / 32) ≤
        taoSection5PowerInteriorDelta B := by
  let logB : ℕ → ℝ := fun B => Real.log (B : ℝ)
  let root : ℕ → ℝ := fun B => Real.rpow (logB B) (1 / 5 : ℝ)
  have hlog : Tendsto logB atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hroot : Tendsto root atTop atTop := by
    simpa only [root, Function.comp_def] using
      (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 5)).comp hlog
  have hdecay :
      Tendsto
        (fun x : ℝ =>
          2 * x ^ (11 / 2 : ℝ) * Real.exp (-(1 / 32 : ℝ) * x))
        atTop (𝓝 0) := by
    simpa only [mul_assoc, mul_zero] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
        (11 / 2 : ℝ) (1 / 32 : ℝ) (by norm_num)).const_mul 2
  have hsmall :
      ∀ᶠ B : ℕ in atTop,
        2 * (root B) ^ (11 / 2 : ℝ) *
            Real.exp (-(1 / 32 : ℝ) * root B) ≤ 1 :=
    (hdecay.comp hroot).eventually_le_const zero_lt_one
  filter_upwards [hlog.eventually_ge_atTop (1 : ℝ), hsmall]
    with B hlogOne hsmallB
  let L := Real.log (B : ℝ)
  let x := Real.rpow L (1 / 5 : ℝ)
  have hLpos : 0 < L := zero_lt_one.trans_le hlogOne
  have hxpos : 0 < x := Real.rpow_pos_of_pos hLpos _
  have hpowpos : 0 < Real.rpow L (1 / 10 : ℝ) :=
    Real.rpow_pos_of_pos hLpos _
  have hcombine :
      L * Real.rpow L (1 / 10 : ℝ) = x ^ (11 / 2 : ℝ) := by
    calc
      L * Real.rpow L (1 / 10 : ℝ) =
          Real.rpow L (1 : ℝ) * Real.rpow L (1 / 10 : ℝ) := by
            exact congrArg
              (fun y : ℝ => y * Real.rpow L (1 / 10 : ℝ))
              (Real.rpow_one L).symm
      _ = Real.rpow L (1 + 1 / 10 : ℝ) :=
        (Real.rpow_add hLpos (1 : ℝ) (1 / 10 : ℝ)).symm
      _ = Real.rpow L (11 / 10 : ℝ) := by norm_num
      _ = x ^ (11 / 2 : ℝ) := by
        dsimp only [x]
        convert Real.rpow_mul hLpos.le (1 / 5 : ℝ) (11 / 2 : ℝ) using 1;
          norm_num
  have hscaled :
      (2 * L * Real.exp (-x / 32)) * Real.rpow L (1 / 10 : ℝ) ≤ 1 := by
    calc
      (2 * L * Real.exp (-x / 32)) * Real.rpow L (1 / 10 : ℝ) =
          2 * x ^ (11 / 2 : ℝ) *
            Real.exp (-(1 / 32 : ℝ) * x) := by
              rw [← hcombine]
              ring
      _ ≤ 1 := by simpa only [root, logB, x, L] using hsmallB
  have hdiv :
      2 * L * Real.exp (-x / 32) ≤
        1 / Real.rpow L (1 / 10 : ℝ) :=
    (le_div_iff₀ hpowpos).2 hscaled
  have hneg :
      Real.rpow L (-1 / 10 : ℝ) =
        1 / Real.rpow L (1 / 10 : ℝ) := by
    calc
      Real.rpow L (-1 / 10 : ℝ) =
          (Real.rpow L (1 / 10 : ℝ))⁻¹ := by
            convert Real.rpow_neg hLpos.le (1 / 10 : ℝ) using 1;
              norm_num
      _ = 1 / Real.rpow L (1 / 10 : ℝ) :=
        (one_div (Real.rpow L (1 / 10 : ℝ))).symm
  change 2 * L * Real.exp (-x / 32) ≤ Real.rpow L (-1 / 10 : ℝ)
  rw [hneg]
  exact hdiv

/-- Under the ideal iid law, failure of the closed Section 5 positive-prefix
condition is eventually at most the repaired boundary scale `delta`. -/
theorem eventually_geom2PNatListPMF_closedPrefixBad_le_delta :
    ∀ᶠ B : ℕ in atTop,
      ((geom2PNatListPMF (taoSection5N0 B)).toOuterMeasure
          (taoSection5ClosedPrefixBadEvent B)).toReal ≤
        taoSection5PowerInteriorDelta B := by
  have hlog :
      Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards
    [eventually_taoSection5LogWindowProp19Output,
      hlog.eventually_ge_atTop (1 : ℝ),
      eventually_two_mul_log_mul_exp_neg_root_le_delta]
      with B prop19 hlogOne henvelope
  let L := Real.log (B : ℝ)
  let x := Real.rpow L (1 / 5 : ℝ)
  have hn0 : 0 < taoSection5N0 B := prop19.schedule.one_le_n0
  have hLpos : 0 < L := zero_lt_one.trans_le hlogOne
  have hden : (1 : ℝ) ≤ 10 * Real.log 2 := by
    have htwo := Real.log_two_gt_d9
    norm_num at htwo ⊢
    linarith
  have hnL : (taoSection5N0 B : ℝ) ≤ L := by
    calc
      (taoSection5N0 B : ℝ) ≤ L / (10 * Real.log 2) := by
        simpa only [L] using taoSection5N0_le_log_div_ten_log_two B
      _ ≤ L := div_le_self hLpos.le hden
  have hslack : 0 < taoSection5TypicalSlack B := by
    unfold taoSection5TypicalSlack
    exact Real.rpow_pos_of_pos hLpos _
  have hsq : (taoSection5TypicalSlack B) ^ 2 = x * L := by
    unfold taoSection5TypicalSlack
    calc
      (Real.rpow L (3 / 5 : ℝ)) ^ 2 =
          Real.rpow (Real.rpow L (3 / 5 : ℝ)) (2 : ℝ) :=
        (Real.rpow_natCast _ 2).symm
      _ = Real.rpow L ((3 / 5 : ℝ) * 2) :=
        (Real.rpow_mul hLpos.le (3 / 5 : ℝ) 2).symm
      _ = Real.rpow L (1 / 5 + 1 : ℝ) := by norm_num
      _ = x * L := by
        dsimp only [x]
        simpa only [Real.rpow_one] using
          Real.rpow_add hLpos (1 / 5 : ℝ) (1 : ℝ)
  have hxnonneg : 0 ≤ x := (Real.rpow_pos_of_pos hLpos _).le
  have hfrac :
      x / 32 ≤
        (taoSection5TypicalSlack B) ^ 2 /
          (32 * (taoSection5N0 B : ℝ)) := by
    rw [hsq]
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 32)
      (by positivity : (0 : ℝ) < 32 * (taoSection5N0 B : ℝ))]
    nlinarith [mul_le_mul_of_nonneg_left hnL hxnonneg]
  have hxle : x ≤ taoSection5TypicalSlack B := by
    unfold taoSection5TypicalSlack
    exact Real.rpow_le_rpow_of_exponent_le hlogOne (by norm_num)
  have hlinear : x / 32 ≤ taoSection5TypicalSlack B / 8 := by
    nlinarith [hxnonneg]
  have hmin :
      x / 32 ≤
        min
          ((taoSection5TypicalSlack B) ^ 2 /
            (32 * (taoSection5N0 B : ℝ)))
          (taoSection5TypicalSlack B / 8) :=
    le_min hfrac hlinear
  have htail := geom2PNatListPMF_prefixBad_le_nat_mul hn0 hslack
  calc
    ((geom2PNatListPMF (taoSection5N0 B)).toOuterMeasure
        (taoSection5ClosedPrefixBadEvent B)).toReal ≤
      (taoSection5N0 B : ℝ) *
        (2 * Real.exp
          (-min
            ((taoSection5TypicalSlack B) ^ 2 /
              (32 * (taoSection5N0 B : ℝ)))
            (taoSection5TypicalSlack B / 8))) := by
        simpa only [taoSection5ClosedPrefixBadEvent] using htail
    _ ≤ L *
        (2 * Real.exp
          (-min
            ((taoSection5TypicalSlack B) ^ 2 /
              (32 * (taoSection5N0 B : ℝ)))
            (taoSection5TypicalSlack B / 8))) :=
      mul_le_mul_of_nonneg_right hnL (by positivity)
    _ ≤ L * (2 * Real.exp (-(x / 32))) := by
      apply mul_le_mul_of_nonneg_left _ hLpos.le
      exact mul_le_mul_of_nonneg_left
        (Real.exp_le_exp.mpr (neg_le_neg hmin)) (by norm_num)
    _ = 2 * L * Real.exp (-x / 32) := by ring
    _ ≤ taoSection5PowerInteriorDelta B := by
      simpa only [L, x] using henvelope

private theorem eventually_four_mul_prop19_rate_le_delta :
    ∀ᶠ B : ℕ in atTop,
      4 * (2 : ℝ) ^
          (-((1 / 128 : ℝ) * (taoSection5N0 B : ℝ))) ≤
        taoSection5PowerInteriorDelta B := by
  let logB : ℕ → ℝ := fun B => Real.log (B : ℝ)
  let C : ℝ := 4 * Real.exp (Real.log 2 / 128)
  have hlog : Tendsto logB atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hdecay :
      Tendsto
        (fun L : ℝ =>
          C * L ^ (1 / 10 : ℝ) *
            Real.exp (-(1 / 1280 : ℝ) * L))
        atTop (𝓝 0) := by
    simpa only [C, mul_assoc, mul_zero] using
      (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero
        (1 / 10 : ℝ) (1 / 1280 : ℝ) (by norm_num)).const_mul C
  have hsmall :
      ∀ᶠ B : ℕ in atTop,
        C * (logB B) ^ (1 / 10 : ℝ) *
            Real.exp (-(1 / 1280 : ℝ) * logB B) ≤ 1 :=
    (hdecay.comp hlog).eventually_le_const zero_lt_one
  filter_upwards [hlog.eventually_ge_atTop (1 : ℝ), hsmall]
    with B hlogOne hsmallB
  let L := Real.log (B : ℝ)
  let ell := Real.log (2 : ℝ)
  have hLpos : 0 < L := zero_lt_one.trans_le hlogOne
  have hell : 0 < ell := Real.log_pos (by norm_num)
  have hnLower :
      L / (10 * ell) - 1 < (taoSection5N0 B : ℝ) := by
    simpa only [L, ell] using
      log_div_ten_log_two_sub_one_lt_taoSection5N0 B
  have hcoefNeg : -(ell / 128) < 0 := by
    have : 0 < ell / 128 := div_pos hell (by norm_num)
    linarith
  have hmul := mul_lt_mul_of_neg_left hnLower hcoefNeg
  have hright :
      -(ell / 128) * (L / (10 * ell) - 1) =
        ell / 128 - L / 1280 := by
    field_simp [hell.ne']
    ring
  rw [hright] at hmul
  have hexponent :
      ell * (-((1 / 128 : ℝ) * (taoSection5N0 B : ℝ))) ≤
        ell / 128 - L / 1280 := by
    nlinarith
  have hrate :
      4 * (2 : ℝ) ^
          (-((1 / 128 : ℝ) * (taoSection5N0 B : ℝ))) ≤
        4 * Real.exp (ell / 128) * Real.exp (-L / 1280) := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2)]
    calc
      4 * Real.exp
          (Real.log 2 *
            (-((1 / 128 : ℝ) * (taoSection5N0 B : ℝ)))) ≤
        4 * Real.exp (ell / 128 - L / 1280) :=
          mul_le_mul_of_nonneg_left
            (Real.exp_le_exp.mpr (by simpa only [ell] using hexponent))
            (by norm_num)
      _ = 4 * Real.exp (ell / 128) * Real.exp (-L / 1280) := by
        rw [show ell / 128 - L / 1280 = ell / 128 + (-L / 1280) by ring,
          Real.exp_add]
        ring
  have hpowpos : 0 < Real.rpow L (1 / 10 : ℝ) :=
    Real.rpow_pos_of_pos hLpos _
  have hscaled :
      (4 * Real.exp (ell / 128) * Real.exp (-L / 1280)) *
          Real.rpow L (1 / 10 : ℝ) ≤ 1 := by
    calc
      (4 * Real.exp (ell / 128) * Real.exp (-L / 1280)) *
          Real.rpow L (1 / 10 : ℝ) =
        C * Real.rpow L (1 / 10 : ℝ) *
          Real.exp (-(1 / 1280 : ℝ) * L) := by
            dsimp only [C, ell]
            ring
      _ ≤ 1 := by simpa only [logB, L] using hsmallB
  have henvelope :
      4 * Real.exp (ell / 128) * Real.exp (-L / 1280) ≤
        1 / Real.rpow L (1 / 10 : ℝ) :=
    (le_div_iff₀ hpowpos).2 hscaled
  have hneg :
      Real.rpow L (-1 / 10 : ℝ) =
        1 / Real.rpow L (1 / 10 : ℝ) := by
    calc
      Real.rpow L (-1 / 10 : ℝ) =
          (Real.rpow L (1 / 10 : ℝ))⁻¹ := by
            convert Real.rpow_neg hLpos.le (1 / 10 : ℝ) using 1;
              norm_num
      _ = 1 / Real.rpow L (1 / 10 : ℝ) :=
        (one_div (Real.rpow L (1 / 10 : ℝ))).symm
  calc
    4 * (2 : ℝ) ^
        (-((1 / 128 : ℝ) * (taoSection5N0 B : ℝ))) ≤
      4 * Real.exp (ell / 128) * Real.exp (-L / 1280) := hrate
    _ ≤ 1 / Real.rpow L (1 / 10 : ℝ) := henvelope
    _ = taoSection5PowerInteriorDelta B := by
      unfold taoSection5PowerInteriorDelta
      simp only [L, hneg]

/-- The complete closed-prefix error packet at one common threshold.  It
stores the actual Proposition 1.9 source law and the branch-uniform one-shot
event comparison. -/
structure TaoSection5PassTypicalFailureFacts (B : ℕ) : Prop where
  prop19 : TaoSection5LogWindowProp19Output B
  slack_pos : 0 < taoSection5TypicalSlack B
  ideal_le :
    ((geom2PNatListPMF (taoSection5N0 B)).toOuterMeasure
        (taoSection5ClosedPrefixBadEvent B)).toReal ≤
      taoSection5PowerInteriorDelta B
  valuation_le :
    4 * (2 : ℝ) ^
        (-((1 / 128 : ℝ) * (taoSection5N0 B : ℝ))) ≤
      taoSection5PowerInteriorDelta B
  closedGood_compl_le : ∀ branch : TaoSection5SourceBranch,
    let μ := oddLogWindowOddNatPMF
      (taoSection5SourceLo B branch)
      (taoSection5SourceHi B branch)
      (prop19.schedule.mass_pos branch)
    (μ.toOuterMeasure (taoSection5ClosedGoodEvent B)ᶜ).toReal ≤
      2 * taoSection5PowerInteriorDelta B

theorem TaoSection5PassTypicalFailureFacts.of_inputs
    {B : ℕ} (prop19 : TaoSection5LogWindowProp19Output B)
    (hslack : 0 < taoSection5TypicalSlack B)
    (hideal :
      ((geom2PNatListPMF (taoSection5N0 B)).toOuterMeasure
          (taoSection5ClosedPrefixBadEvent B)).toReal ≤
        taoSection5PowerInteriorDelta B)
    (hvaluation :
      4 * (2 : ℝ) ^
          (-((1 / 128 : ℝ) * (taoSection5N0 B : ℝ))) ≤
        taoSection5PowerInteriorDelta B) :
    TaoSection5PassTypicalFailureFacts B := by
  refine
    { prop19 := prop19
      slack_pos := hslack
      ideal_le := hideal
      valuation_le := hvaluation
      closedGood_compl_le := ?_ }
  intro branch
  let μ := oddLogWindowOddNatPMF
    (taoSection5SourceLo B branch)
    (taoSection5SourceHi B branch)
    (prop19.schedule.mass_pos branch)
  have hval := prop19.valuationBound branch
  unfold taoProp19ValuationTV at hval
  have hcompare :=
    pmfOuterMass_le_add_of_taoPMFFullL1_le
      (p := taoProp19ActualValuationLaw μ (taoSection5N0 B))
      (q := geom2PNatListPMF (taoSection5N0 B))
      (E := taoSection5ClosedPrefixBadEvent B) hval
  calc
    (μ.toOuterMeasure (taoSection5ClosedGoodEvent B)ᶜ).toReal =
        ((taoProp19ActualValuationLaw μ (taoSection5N0 B)).toOuterMeasure
          (taoSection5ClosedPrefixBadEvent B)).toReal := by
            rw [taoProp19ActualValuationLaw_closedPrefixBad B μ hslack]
    _ ≤ ((geom2PNatListPMF (taoSection5N0 B)).toOuterMeasure
          (taoSection5ClosedPrefixBadEvent B)).toReal +
        4 * (2 : ℝ) ^
          (-((1 / 128 : ℝ) * (taoSection5N0 B : ℝ))) := hcompare
    _ ≤ taoSection5PowerInteriorDelta B +
        taoSection5PowerInteriorDelta B := add_le_add hideal hvaluation
    _ = 2 * taoSection5PowerInteriorDelta B := by ring

/-- Both canonical source branches carry the closed-prefix complement bound
for all sufficiently large common thresholds. -/
theorem eventually_taoSection5PassTypicalFailureFacts :
    ∀ᶠ B : ℕ in atTop, TaoSection5PassTypicalFailureFacts B := by
  have hlog :
      Tendsto (fun B : ℕ => Real.log (B : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards
    [eventually_taoSection5LogWindowProp19Output,
      eventually_geom2PNatListPMF_closedPrefixBad_le_delta,
      eventually_four_mul_prop19_rate_le_delta,
      hlog.eventually_gt_atTop (0 : ℝ)]
      with B prop19 hideal hvaluation hlogPos
  exact TaoSection5PassTypicalFailureFacts.of_inputs prop19
    (Real.rpow_pos_of_pos hlogPos _) hideal hvaluation

end

end Tao
end Erdos1135SecondScale
