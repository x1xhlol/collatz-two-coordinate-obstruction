/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.Lemma79TailExpectationCore
import Erdos1135SecondScale.Tao.Renewal.QPrefixFactor

/-!
# Canonical First-Passage Stopped Q Approximants

This integration leaf couples the terminal-one `Q` approximants with the
canonical bounded first-passage prefix.  Its main result is the finite-horizon
squeeze needed before passing to Tao's stopped actual-Q identity `(7.45)`.
-/

open scoped BigOperators

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

open TaoSection7Case3SourceStoppingRun.Lemma79TailExpectation

/-- Real expectation against a countable PMF. -/
noncomputable def taoSection7PMFExpectation
    {α : Type*} (p : PMF α) (F : α → ℝ) : ℝ :=
  ∑' x : α, (p x).toReal * F x

theorem taoSection7PMFExpectation_summable_of_bounded01
    {α : Type*} (p : PMF α) (F : α → ℝ)
    (hF0 : ∀ x, 0 ≤ F x) (hF1 : ∀ x, F x ≤ 1) :
    Summable fun x : α => (p x).toReal * F x := by
  have hp : Summable fun x : α => (p x).toReal :=
    ENNReal.summable_toReal p.tsum_coe_ne_top
  exact Summable.of_nonneg_of_le
    (fun x => mul_nonneg ENNReal.toReal_nonneg (hF0 x))
    (fun x => by
      simpa using mul_le_mul_of_nonneg_left (hF1 x) ENNReal.toReal_nonneg)
    hp

/-- Reconstruct the consumed stopped prefix and the next `J` increments as
one deterministic take from the same master list. -/
theorem taoSection7FirstPassageFixedTailSplit_append_eq_take
    (J : ℕ) (start : TaoSection7RenewalPoint) (gap : ℕ)
    (full : List TaoSection7RenewalPoint) :
    let K := lemma79VerticalFirstPassageCut start gap full
    let pair := lemma79VerticalFirstPassageFixedTailSplit J start gap full
    pair.1 ++ pair.2 = full.take (K + J) := by
  dsimp [lemma79VerticalFirstPassageFixedTailSplit]
  exact (List.take_add (l := full)).symm

/-- The first `J` increments reconstructed from the random stopped split have
exactly the ordinary iid length-`J` Hold law. -/
theorem taoSection7RawFirstPassageFixedTailSplit_map_reconstructedTake_eq
    (J : ℕ) (start : TaoSection7RenewalPoint) (gap : ℕ) :
    (lemma79RawHoldFirstPassageFixedTailSplitPMF
        (gap + 1 + J) J start gap).map
      (fun pair => (pair.1 ++ pair.2).take J) =
        taoSection7HoldListPMF J := by
  unfold lemma79RawHoldFirstPassageFixedTailSplitPMF
  rw [PMF.map_comp]
  have hfun :
      (fun pair : List TaoSection7RenewalPoint ×
          List TaoSection7RenewalPoint => (pair.1 ++ pair.2).take J) ∘
        (fun src => lemma79VerticalFirstPassageFixedTailSplit J start gap
          (lemma79DecodeHoldSourcePrefixes src)) =
      fun src => (lemma79DecodeHoldSourcePrefixes src).take J := by
    funext src
    let full := lemma79DecodeHoldSourcePrefixes src
    let K := lemma79VerticalFirstPassageCut start gap full
    have hsplit := taoSection7FirstPassageFixedTailSplit_append_eq_take
      J start gap full
    change ((lemma79VerticalFirstPassageFixedTailSplit J start gap full).1 ++
      (lemma79VerticalFirstPassageFixedTailSplit J start gap full).2).take J =
        full.take J
    rw [hsplit]
    rw [List.take_take, Nat.min_eq_left (Nat.le_add_left J K)]
  rw [hfun]
  exact taoSection7HoldSourcePrefixListPMF_map_take_holdPoint_eq_of_le (by omega)

/-- Terminal-one approximation after a canonical stopped prefix. -/
noncomputable def taoSection7CanonicalFirstPassageStoppedApprox
    (J : ℕ) (epsilon : ℝ) (W : TaoSection7RenewalPoint → Prop)
    (start : TaoSection7RenewalPoint) (gap : ℕ) : ℝ :=
  ∑' pre : List TaoSection7RenewalPoint,
    (lemma77CanonicalFirstPassagePrefixPMF start gap pre).toReal *
      (taoSection7QPrefixFactor epsilon W start pre *
        taoSection7QFiniteTerminalOneApprox J epsilon W
          (taoSection7RenewalPathPoint start pre pre.length))

theorem taoSection7CanonicalFirstPassageStoppedApprox_summable
    {J : ℕ} {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (W : TaoSection7RenewalPoint → Prop)
    (start : TaoSection7RenewalPoint) (gap : ℕ) :
    Summable fun pre : List TaoSection7RenewalPoint =>
      (lemma77CanonicalFirstPassagePrefixPMF start gap pre).toReal *
        (taoSection7QPrefixFactor epsilon W start pre *
          taoSection7QFiniteTerminalOneApprox J epsilon W
            (taoSection7RenewalPathPoint start pre pre.length)) := by
  apply taoSection7PMFExpectation_summable_of_bounded01
  · intro pre
    exact mul_nonneg
      (taoSection7QPrefixFactor_nonneg epsilon W start pre)
      (taoSection7QFiniteTerminalOneApprox_nonneg J epsilon W _)
  · intro pre
    have hpref0 := taoSection7QPrefixFactor_nonneg epsilon W start pre
    have hpref1 := taoSection7QPrefixFactor_le_one hepsilon W start pre
    have htail0 := taoSection7QFiniteTerminalOneApprox_nonneg J epsilon W
      (taoSection7RenewalPathPoint start pre pre.length)
    have htail1 := taoSection7QFiniteTerminalOneApprox_le_one
      (K := J) hepsilon W
      (taoSection7RenewalPathPoint start pre pre.length)
    nlinarith [mul_nonneg (sub_nonneg.mpr hpref1) htail0,
      mul_nonneg hpref0 (sub_nonneg.mpr htail1)]

/-- The canonical stopped approximation is the expectation of the exact
prefix-plus-fresh-tail product under the checked raw split law. -/
theorem taoSection7CanonicalFirstPassageStoppedApprox_eq_splitExpectation
    {J : ℕ} {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (W : TaoSection7RenewalPoint → Prop)
    (start : TaoSection7RenewalPoint) (gap : ℕ) :
    taoSection7CanonicalFirstPassageStoppedApprox J epsilon W start gap =
      taoSection7PMFExpectation
        (lemma79RawHoldFirstPassageFixedTailSplitPMF
          (gap + 1 + J) J start gap)
        (fun pair =>
          taoSection7QFinite epsilon W start (pair.1 ++ pair.2)) := by
  let splitPMF := lemma79RawHoldFirstPassageFixedTailSplitPMF
    (gap + 1 + J) J start gap
  let prefixPMF := lemma77CanonicalFirstPassagePrefixPMF
    start gap
  let payload :
      List TaoSection7RenewalPoint × List TaoSection7RenewalPoint → ℝ :=
    fun pair => taoSection7QFinite epsilon W start (pair.1 ++ pair.2)
  have hpayload0 : ∀ pair, 0 ≤ payload pair := by
    intro pair
    exact taoSection7QFinite_nonneg epsilon W start (pair.1 ++ pair.2)
  have hpayload1 : ∀ pair, payload pair ≤ 1 := by
    intro pair
    exact taoSection7QFinite_le_one hepsilon W start (pair.1 ++ pair.2)
  have hpairSum : Summable fun pair =>
      (splitPMF pair).toReal * payload pair :=
    taoSection7PMFExpectation_summable_of_bounded01
      splitPMF payload hpayload0 hpayload1
  have hfiber : ∀ pre : List TaoSection7RenewalPoint,
      Summable fun tail : List TaoSection7RenewalPoint =>
        (splitPMF (pre, tail)).toReal * payload (pre, tail) := by
    intro pre
    have hinj : Function.Injective
        (fun tail : List TaoSection7RenewalPoint => (pre, tail)) := by
      intro x y hxy
      exact congrArg Prod.snd hxy
    simpa [Function.comp_apply] using hpairSum.comp_injective hinj
  rw [taoSection7CanonicalFirstPassageStoppedApprox,
    taoSection7PMFExpectation]
  change
    (∑' pre : List TaoSection7RenewalPoint,
      (prefixPMF pre).toReal *
        (taoSection7QPrefixFactor epsilon W start pre *
          taoSection7QFiniteTerminalOneApprox J epsilon W
            (taoSection7RenewalPathPoint start pre pre.length))) =
      ∑' pair, (splitPMF pair).toReal * payload pair
  rw [hpairSum.tsum_prod' hfiber]
  apply tsum_congr
  intro pre
  have hsplit := lemma79_rawHoldFirstPassageFixedTailSplitPMF_eq_bind
    J start gap
  have hprefix := lemma79_rawHoldFirstPassagePrefixPMF_eq_canonical
    J start gap
  have hpoint : ∀ tail : List TaoSection7RenewalPoint,
      (splitPMF (pre, tail)).toReal =
        (prefixPMF pre).toReal * (taoSection7HoldListPMF J tail).toReal := by
    intro tail
    rw [show splitPMF =
        (lemma79RawHoldFirstPassagePrefixPMF J start gap).bind fun pre =>
          (taoSection7HoldListPMF J).map fun tail => (pre, tail) by
        simpa [splitPMF] using hsplit]
    rw [lemma79_prefixFreshTail_bind_apply, hprefix, ENNReal.toReal_mul]
  calc
    (prefixPMF pre).toReal *
        (taoSection7QPrefixFactor epsilon W start pre *
          taoSection7QFiniteTerminalOneApprox J epsilon W
            (taoSection7RenewalPathPoint start pre pre.length)) =
      ((prefixPMF pre).toReal *
        taoSection7QPrefixFactor epsilon W start pre) *
          (∑' tail : List TaoSection7RenewalPoint,
            (taoSection7HoldListPMF J tail).toReal *
              taoSection7QFinite epsilon W
                (taoSection7RenewalPathPoint start pre pre.length) tail) := by
      unfold taoSection7QFiniteTerminalOneApprox
      ring
    _ = ∑' tail : List TaoSection7RenewalPoint,
        ((prefixPMF pre).toReal *
          taoSection7QPrefixFactor epsilon W start pre) *
            ((taoSection7HoldListPMF J tail).toReal *
              taoSection7QFinite epsilon W
                (taoSection7RenewalPathPoint start pre pre.length) tail) := by
      rw [tsum_mul_left]
    _ = ∑' tail : List TaoSection7RenewalPoint,
        (splitPMF (pre, tail)).toReal * payload (pre, tail) := by
      apply tsum_congr
      intro tail
      simp only [payload]
      rw [hpoint tail,
        taoSection7QFinite_append_eq_prefixFactor_mul_endpoint]
      ring

/-- Finite-horizon stopped approximation squeeze. -/
theorem taoSection7CanonicalFirstPassageApprox_sandwich
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (W : TaoSection7RenewalPoint → Prop)
    (start : TaoSection7RenewalPoint) (gap J : ℕ) :
    taoSection7QFiniteTerminalOneApprox (gap + 1 + J) epsilon W start ≤
        taoSection7CanonicalFirstPassageStoppedApprox J epsilon W start gap ∧
      taoSection7CanonicalFirstPassageStoppedApprox J epsilon W start gap ≤
        taoSection7QFiniteTerminalOneApprox J epsilon W start := by
  let B : ℕ := gap + 1
  let N : ℕ := B + J
  let rho := taoSection7HoldSourcePrefixListPMF N
  let decode : List (ℕ × List ℕ) → List TaoSection7RenewalPoint :=
    lemma79DecodeHoldSourcePrefixes
  let split : List (ℕ × List ℕ) →
      List TaoSection7RenewalPoint × List TaoSection7RenewalPoint :=
    fun src => lemma79VerticalFirstPassageFixedTailSplit J start gap (decode src)
  let fullPayload : List TaoSection7RenewalPoint → ℝ :=
    fun full => taoSection7QFinite epsilon W start full
  let splitPayload :
      List TaoSection7RenewalPoint × List TaoSection7RenewalPoint → ℝ :=
    fun pair => taoSection7QFinite epsilon W start (pair.1 ++ pair.2)
  let takePayload : List TaoSection7RenewalPoint → ℝ :=
    fun pre => taoSection7QFinite epsilon W start pre
  have hfull0 : ∀ full, 0 ≤ fullPayload full := by
    intro full
    exact taoSection7QFinite_nonneg epsilon W start full
  have hfull1 : ∀ full, fullPayload full ≤ 1 := by
    intro full
    exact taoSection7QFinite_le_one hepsilon W start full
  have hsplit0 : ∀ pair, 0 ≤ splitPayload pair := by
    intro pair
    exact taoSection7QFinite_nonneg epsilon W start (pair.1 ++ pair.2)
  have hsplit1 : ∀ pair, splitPayload pair ≤ 1 := by
    intro pair
    exact taoSection7QFinite_le_one hepsilon W start (pair.1 ++ pair.2)
  have htake0 : ∀ pre, 0 ≤ takePayload pre := by
    intro pre
    exact taoSection7QFinite_nonneg epsilon W start pre
  have htake1 : ∀ pre, takePayload pre ≤ 1 := by
    intro pre
    exact taoSection7QFinite_le_one hepsilon W start pre
  have hmapFull := pmf_map_weighted_tsum_toReal_eq_of_bounded01
    rho decode fullPayload hfull0 hfull1
  have hmapSplit := pmf_map_weighted_tsum_toReal_eq_of_bounded01
    rho split splitPayload hsplit0 hsplit1
  have hmapTake := pmf_map_weighted_tsum_toReal_eq_of_bounded01
    rho (fun src => (decode src).take J) takePayload htake0 htake1
  have hdecodeLaw : rho.map decode = taoSection7HoldListPMF N := by
    simpa [rho, decode, N] using
      taoSection7HoldSourcePrefixListPMF_map_holdPoint_eq N
  have hsplitLaw : rho.map split =
      lemma79RawHoldFirstPassageFixedTailSplitPMF N J start gap := by
    rfl
  have htakeLaw : rho.map (fun src => (decode src).take J) =
      taoSection7HoldListPMF J := by
    apply taoSection7HoldSourcePrefixListPMF_map_take_holdPoint_eq_of_le
    dsimp [N, B]
    omega
  have hleftEq :
      taoSection7QFiniteTerminalOneApprox N epsilon W start =
        ∑' src : List (ℕ × List ℕ),
          (rho src).toReal * fullPayload (decode src) := by
    unfold taoSection7QFiniteTerminalOneApprox
    rw [← hdecodeLaw]
    exact hmapFull.2.2
  have hmiddleEq :
      taoSection7CanonicalFirstPassageStoppedApprox J epsilon W start gap =
        ∑' src : List (ℕ × List ℕ),
          (rho src).toReal * splitPayload (split src) := by
    rw [taoSection7CanonicalFirstPassageStoppedApprox_eq_splitExpectation
      hepsilon W start gap]
    unfold taoSection7PMFExpectation
    rw [← hsplitLaw]
    exact hmapSplit.2.2
  have hrightEq :
      taoSection7QFiniteTerminalOneApprox J epsilon W start =
        ∑' src : List (ℕ × List ℕ),
          (rho src).toReal * takePayload ((decode src).take J) := by
    unfold taoSection7QFiniteTerminalOneApprox
    rw [← htakeLaw]
    exact hmapTake.2.2
  have hpoint : ∀ src : List (ℕ × List ℕ),
      fullPayload (decode src) ≤ splitPayload (split src) ∧
        splitPayload (split src) ≤ takePayload ((decode src).take J) := by
    intro src
    let full := decode src
    let K := lemma79VerticalFirstPassageCut start gap full
    have hsplitList : (split src).1 ++ (split src).2 =
        full.take (K + J) := by
      dsimp [split, full, K]
      exact (List.take_add (l := full) (i := K) (j := J)).symm
    have hfullSplit : full =
        full.take (K + J) ++ full.drop (K + J) :=
      (List.take_append_drop (K + J) full).symm
    have htakeSplit : full.take (K + J) =
        full.take J ++ (full.drop J).take K := by
      rw [Nat.add_comm]
      exact List.take_add (l := full) (i := J) (j := K)
    constructor
    · dsimp [fullPayload, splitPayload]
      calc
        taoSection7QFinite epsilon W start (decode src) =
            taoSection7QFinite epsilon W start full := by rfl
        _ = taoSection7QFinite epsilon W start
            (full.take (K + J) ++ full.drop (K + J)) := by
          exact congrArg (taoSection7QFinite epsilon W start) hfullSplit
        _ ≤ taoSection7QFinite epsilon W start (full.take (K + J)) :=
          taoSection7QFinite_append_le_left hepsilon W start
            (full.take (K + J)) (full.drop (K + J))
        _ = taoSection7QFinite epsilon W start
            ((split src).1 ++ (split src).2) := by rw [hsplitList]
    · dsimp [splitPayload, takePayload]
      calc
        taoSection7QFinite epsilon W start ((split src).1 ++ (split src).2) =
            taoSection7QFinite epsilon W start (full.take (K + J)) := by
          rw [hsplitList]
        _ = taoSection7QFinite epsilon W start
            (full.take J ++ (full.drop J).take K) := by rw [htakeSplit]
        _ ≤ taoSection7QFinite epsilon W start (full.take J) :=
          taoSection7QFinite_append_le_left hepsilon W start
            (full.take J) ((full.drop J).take K)
        _ = taoSection7QFinite epsilon W start ((decode src).take J) := by rfl
  have hfullSum := hmapFull.2.1
  have hsplitSum := hmapSplit.2.1
  have htakeSum := hmapTake.2.1
  constructor
  · rw [show gap + 1 + J = N by rfl, hleftEq, hmiddleEq]
    exact hfullSum.tsum_le_tsum
      (fun src => mul_le_mul_of_nonneg_left (hpoint src).1 ENNReal.toReal_nonneg)
      hsplitSum
  · rw [hmiddleEq, hrightEq]
    exact hsplitSum.tsum_le_tsum
      (fun src => mul_le_mul_of_nonneg_left (hpoint src).2 ENNReal.toReal_nonneg)
      htakeSum

/-- The finite stopped approximants converge to the same actual-Q limit as
the deterministic terminal-one approximants. -/
theorem taoSection7CanonicalFirstPassageStoppedApprox_tendsto_of_finiteLimit
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    {W : TaoSection7RenewalPoint → Prop}
    {Q : TaoSection7RenewalPoint → ℝ}
    (hQ : TaoSection7ActualQFiniteLimitStatement epsilon W Q)
    (start : TaoSection7RenewalPoint) (gap : ℕ) :
    Filter.Tendsto
      (fun J : ℕ =>
        taoSection7CanonicalFirstPassageStoppedApprox J epsilon W start gap)
      Filter.atTop (nhds (Q start)) := by
  have hleft : Filter.Tendsto
      (fun J : ℕ =>
        taoSection7QFiniteTerminalOneApprox (gap + 1 + J) epsilon W start)
      Filter.atTop (nhds (Q start)) := by
    have hshift := (hQ start).comp
      (Filter.tendsto_add_atTop_nat (gap + 1))
    convert hshift using 1
    funext J
    simp [Function.comp_apply, Nat.add_comm]
  exact Filter.Tendsto.squeeze hleft (hQ start)
    (fun J => (taoSection7CanonicalFirstPassageApprox_sandwich
      hepsilon W start gap J).1)
    (fun J => (taoSection7CanonicalFirstPassageApprox_sandwich
      hepsilon W start gap J).2)

/-- Canonical stopped-prefix expectation with an arbitrary continuation. -/
noncomputable def taoSection7CanonicalFirstPassageStoppedExpectation
    (epsilon : ℝ) (W : TaoSection7RenewalPoint → Prop)
    (Q : TaoSection7RenewalPoint → ℝ)
    (start : TaoSection7RenewalPoint) (gap : ℕ) : ℝ :=
  ∑' pre : List TaoSection7RenewalPoint,
    (lemma77CanonicalFirstPassagePrefixPMF start gap pre).toReal *
      (taoSection7QPrefixFactor epsilon W start pre *
        Q (taoSection7RenewalPathPoint start pre pre.length))

/-- Dominated convergence under the canonical countable stopped-prefix PMF. -/
theorem taoSection7CanonicalFirstPassageStoppedApprox_tendsto_expectation_of_finiteLimit
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    {W : TaoSection7RenewalPoint → Prop}
    {Q : TaoSection7RenewalPoint → ℝ}
    (hQ : TaoSection7ActualQFiniteLimitStatement epsilon W Q)
    (start : TaoSection7RenewalPoint) (gap : ℕ) :
    Filter.Tendsto
      (fun J : ℕ =>
        taoSection7CanonicalFirstPassageStoppedApprox J epsilon W start gap)
      Filter.atTop
      (nhds (taoSection7CanonicalFirstPassageStoppedExpectation
        epsilon W Q start gap)) := by
  let p := lemma77CanonicalFirstPassagePrefixPMF start gap
  have hpSum : Summable fun pre : List TaoSection7RenewalPoint =>
      (p pre).toReal := ENNReal.summable_toReal p.tsum_coe_ne_top
  unfold taoSection7CanonicalFirstPassageStoppedApprox
  unfold taoSection7CanonicalFirstPassageStoppedExpectation
  refine tendsto_tsum_of_dominated_convergence
    (bound := fun pre : List TaoSection7RenewalPoint => (p pre).toReal)
    hpSum ?_ ?_
  · intro pre
    have htail := hQ (taoSection7RenewalPathPoint start pre pre.length)
    exact ((htail.const_mul
      (taoSection7QPrefixFactor epsilon W start pre)).const_mul
        (p pre).toReal)
  · exact Filter.Eventually.of_forall fun J pre => by
      have hmass0 : 0 ≤ (p pre).toReal := ENNReal.toReal_nonneg
      have hpref0 := taoSection7QPrefixFactor_nonneg epsilon W start pre
      have hpref1 := taoSection7QPrefixFactor_le_one hepsilon W start pre
      have htail0 := taoSection7QFiniteTerminalOneApprox_nonneg J epsilon W
        (taoSection7RenewalPathPoint start pre pre.length)
      have htail1 := taoSection7QFiniteTerminalOneApprox_le_one
        (K := J) hepsilon W
        (taoSection7RenewalPathPoint start pre pre.length)
      have hprod0 : 0 ≤ taoSection7QPrefixFactor epsilon W start pre *
          taoSection7QFiniteTerminalOneApprox J epsilon W
            (taoSection7RenewalPathPoint start pre pre.length) :=
        mul_nonneg hpref0 htail0
      have hprod1 : taoSection7QPrefixFactor epsilon W start pre *
          taoSection7QFiniteTerminalOneApprox J epsilon W
            (taoSection7RenewalPathPoint start pre pre.length) ≤ 1 := by
        nlinarith [mul_nonneg (sub_nonneg.mpr hpref1) htail0,
          mul_nonneg hpref0 (sub_nonneg.mpr htail1)]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg hmass0 hprod0)]
      simpa using mul_le_mul_of_nonneg_left hprod1 hmass0

/-- Exact bounded first-passage identity for every actual-Q finite limit. -/
theorem taoSection7ActualQ_eq_canonicalFirstPassageExpectation_of_finiteLimit
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    {W : TaoSection7RenewalPoint → Prop}
    {Q : TaoSection7RenewalPoint → ℝ}
    (hQ : TaoSection7ActualQFiniteLimitStatement epsilon W Q)
    (start : TaoSection7RenewalPoint) (gap : ℕ) :
    Q start = taoSection7CanonicalFirstPassageStoppedExpectation
      epsilon W Q start gap := by
  exact tendsto_nhds_unique
    (taoSection7CanonicalFirstPassageStoppedApprox_tendsto_of_finiteLimit
      hepsilon hQ start gap)
    (taoSection7CanonicalFirstPassageStoppedApprox_tendsto_expectation_of_finiteLimit
      hepsilon hQ start gap)

/-- Source actual-Q specialization of the repaired stopped identity `(7.45)`. -/
theorem taoSection7SourceActualQ_eq_canonicalFirstPassageExpectation
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (start : TaoSection7RenewalPoint) (gap : ℕ) :
    taoSection7SourceActualQ n xi epsilon start =
      taoSection7CanonicalFirstPassageStoppedExpectation epsilon
        (taoSection7SourceActualW n xi epsilon)
        (taoSection7SourceActualQ n xi epsilon) start gap := by
  exact taoSection7ActualQ_eq_canonicalFirstPassageExpectation_of_finiteLimit
    hepsilon (taoSection7SourceActualQ_finiteLimit hepsilon) start gap

end

end Tao
end Erdos1135SecondScale
