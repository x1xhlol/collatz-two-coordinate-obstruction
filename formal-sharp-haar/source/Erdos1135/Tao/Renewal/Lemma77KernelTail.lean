import Erdos1135.Tao.Renewal.Lemma77HighJ
import Erdos1135.Tao.Renewal.Lemma710Complementary
import Erdos1135.Tao.Section6.Corollary63

/-!
# Lemma 7.7 Kernel-Tail Summation Support

This module records the analytic summation layer that has to sit between a
future pointwise Lemma 7.7 first-passage kernel law and the `BadPre`
centered-tail probability producer.

It does not prove Tao's Lemma 7.7, the pointwise first-passage law, source-law
production, or the `BadPre` probability bound.  The checked content is the
finite exponential tail summation, exact two-term kernel-to-envelope
domination, and deterministic margin-event inclusion needed before those
probability producers can be assembled.
-/

namespace Erdos1135
namespace Tao

open scoped BigOperators

noncomputable section

namespace TaoSection7Lemma77

/--
Tail event using an explicit positive horizontal margin `delta * m` above the
Lemma 7.7 center `s / 4`.

The landed centered-tail event uses `currentScaleHighJMargin` as this margin;
this parameterized event is the analytic surface used by the kernel-tail
summation below.
-/
def marginTailEvent
    {Ω : Type*}
    (start : Ω → TaoSection7RenewalPoint)
    (K : Ω → ℕ)
    (pre : Ω → List TaoSection7RenewalPoint)
    (s m : ℕ) (delta : ℝ) : Set Ω :=
  {ω |
    ((s : ℝ) / 4) + delta * (m : ℝ) ≤
      (prefixIncrement start K pre ω : ℝ)}

/--
The checked centered-tail event is contained in any weaker explicit-margin
tail event whose margin is at most `currentScaleHighJMargin`.
-/
theorem centeredHighTailEvent_subset_marginTailEvent_of_delta_le
    {Ω : Type*}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {s m : ℕ} {delta : ℝ}
    (hdelta : delta ≤ currentScaleHighJMargin) :
    centeredHighTailEvent start K pre s m ⊆
      marginTailEvent start K pre s m delta := by
  intro ω hω
  have hm_nonneg : 0 ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
  have hmargin :
      delta * (m : ℝ) ≤ currentScaleHighJMargin * (m : ℝ) :=
    mul_le_mul_of_nonneg_right hdelta hm_nonneg
  have hω' :
      ((s : ℝ) / 4) + currentScaleHighJMargin * (m : ℝ) ≤
        (prefixIncrement start K pre ω : ℝ) := by
    simpa [centeredHighTailEvent] using hω
  show
      ((s : ℝ) / 4) + delta * (m : ℝ) ≤
        (prefixIncrement start K pre ω : ℝ)
  calc
    ((s : ℝ) / 4) + delta * (m : ℝ)
        = delta * (m : ℝ) + ((s : ℝ) / 4) := by ring
    _ ≤ currentScaleHighJMargin * (m : ℝ) + ((s : ℝ) / 4) :=
          add_le_add_left hmargin ((s : ℝ) / 4)
    _ = ((s : ℝ) / 4) + currentScaleHighJMargin * (m : ℝ) := by ring
    _ ≤ (prefixIncrement start K pre ω : ℝ) := hω'

/--
Current-scale `(7.52)` plus any margin below the checked log gap sends the
raw high-horizontal event into the explicit-margin tail event.
-/
theorem highJEvent_subset_marginTailEvent_of_currentScale_of_delta_le
    {Ω : Type*}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {s m : ℕ} {delta : ℝ}
    (hscale : (s : ℝ) ≤ (Real.log 9 / Real.log 2) * (m : ℝ))
    (hdelta : delta ≤ currentScaleHighJMargin) :
    highJEvent start K pre m ⊆ marginTailEvent start K pre s m delta :=
  Set.Subset.trans
    (highJEvent_subset_centeredHighTailEvent_of_currentScale
      (start := start) (K := K) (pre := pre) hscale)
    (centeredHighTailEvent_subset_marginTailEvent_of_delta_le
      (start := start) (K := K) (pre := pre) (s := s) (m := m) hdelta)

/--
Finite cover socket for turning pointwise/fiber kernel estimates and a summed
kernel budget into the centered-tail probability.

This removes the direct `htail` hypothesis shape, but it is still support
only: future work must produce the cover, the pointwise Lemma 7.7 fiber
estimates, and the kernel-tail sum.
-/
theorem centeredHighTail_prob_le_of_finite_event_kernel_sum
    {Ω ι : Type*} [Fintype Ω] [DecidableEq ι] {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint} {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint} {s m : ℕ}
    (I : Finset ι) (event : ι → Set Ω) (kernelMass : ι → ℝ)
    {bPre : ℝ}
    (hcover :
      ∀ ω,
        ω ∈ centeredHighTailEvent start K pre s m →
          ∃ i, i ∈ I ∧ ω ∈ event i)
    (hfiber : ∀ i, i ∈ I → pmfProb μ (event i) ≤ kernelMass i)
    (hsum : I.sum kernelMass ≤ bPre) :
    pmfProb μ (centeredHighTailEvent start K pre s m) ≤ bPre := by
  calc
    pmfProb μ (centeredHighTailEvent start K pre s m)
        ≤ I.sum fun i => pmfProb μ (event i) :=
          TaoSection7Lemma710.pmfProb_le_finset_sum_of_subset_exists
            μ I event (centeredHighTailEvent start K pre s m) hcover
    _ ≤ I.sum kernelMass := by
          exact Finset.sum_le_sum fun i hi => hfiber i hi
    _ ≤ bPre := hsum

/--
High-horizontal probability consumer from current-scale `(7.52)`, a finite
centered-tail cover, pointwise/fiber kernel estimates, and a summed kernel
budget.

Compared with `highJ_prob_le_of_currentScale_centeredTail`, this theorem no
longer takes an opaque centered-tail probability hypothesis.
-/
theorem highJ_prob_le_of_currentScale_finite_event_kernel_sum
    {Ω ι : Type*} [Fintype Ω] [DecidableEq ι] {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint} {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint} {s m : ℕ}
    (I : Finset ι) (event : ι → Set Ω) (kernelMass : ι → ℝ)
    {bPre : ℝ}
    (hscale : (s : ℝ) ≤ (Real.log 9 / Real.log 2) * (m : ℝ))
    (hcover :
      ∀ ω,
        ω ∈ centeredHighTailEvent start K pre s m →
          ∃ i, i ∈ I ∧ ω ∈ event i)
    (hfiber : ∀ i, i ∈ I → pmfProb μ (event i) ≤ kernelMass i)
    (hsum : I.sum kernelMass ≤ bPre) :
    pmfProb μ (highJEvent start K pre m) ≤ bPre :=
  highJ_prob_le_of_currentScale_centeredTail
    (start := start) (K := K) (pre := pre) hscale
    (centeredHighTail_prob_le_of_finite_event_kernel_sum
      (start := start) (K := K) (pre := pre)
      I event kernelMass hcover hfiber hsum)

/--
Finite horizontal-tail exponential envelope after vertical overshoot summation
has been absorbed into the constant `C`.

`idx` is the horizontal overshoot beyond the explicit margin `delta * m`.
-/
def kernelTailEnvelope (C c delta : ℝ) (m N : ℕ) : ℝ :=
  ∑ idx ∈ Finset.range N,
    C * Real.exp (-c * (delta * (m : ℝ) + (idx : ℝ)))

/--
One summand of the exact two-term Lemma 7.7 kernel tail after vertical
overshoot has been absorbed into `V`.

This mirrors the `G_{1+s}` shape: a Gaussian term at scale `1+s` plus a linear
exponential tail, both multiplied by the `(1+s)^(-1/2)` horizontal marginal
factor.
-/
def exactKernelTailSummand
    (a b K V delta : ℝ) (s m idx : ℕ) : ℝ :=
  K * V * ((1 + (s : ℝ)) ^ (-(1 / 2 : ℝ))) *
    (Real.exp (-a * ((delta * (m : ℝ) + (idx : ℝ)) ^ 2 /
        (1 + (s : ℝ)))) +
      Real.exp (-b * (delta * (m : ℝ) + (idx : ℝ))))

/-- Finite exact-kernel tail envelope over horizontal overshoots. -/
def exactKernelTailEnvelope
    (a b K V delta : ℝ) (s m N : ℕ) : ℝ :=
  ∑ idx ∈ Finset.range N, exactKernelTailSummand a b K V delta s m idx

/--
Ceiling base for canonical integer bins above the explicit horizontal margin
`delta * m`.

Using the ceiling avoids lower-tail rounding loss: membership in the bin
`base + idx` implies the real displacement is at least
`s/4 + delta*m + idx`.
-/
def centeredHighTailBinBase (s m : ℕ) (delta : ℝ) : ℕ :=
  Nat.ceil ((s : ℝ) / 4 + delta * (m : ℝ))

/--
Canonical exact integer bin for the prefix increment above the explicit margin.

These bins are deterministic cover infrastructure only; the source-facing
fiber probability bound for each bin remains a separate Lemma 7.7 input.
-/
def centeredHighTailBinEvent
    {Ω : Type*}
    (start : Ω → TaoSection7RenewalPoint)
    (K : Ω → ℕ)
    (pre : Ω → List TaoSection7RenewalPoint)
    (s m : ℕ) (delta : ℝ) (idx : ℕ) : Set Ω :=
  {ω |
    prefixIncrement start K pre ω = centeredHighTailBinBase s m delta + idx}

/--
The checked centered-tail event has a finite canonical integer-bin cover once
its explicit margin is no larger than the current-scale high-`J` margin and the
prefix increment is bounded before `base + N`.
-/
theorem centeredHighTailEvent_canonicalBinCover
    {Ω : Type*}
    {start : Ω → TaoSection7RenewalPoint} {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {s m N : ℕ} {delta : ℝ}
    (hdelta_le : delta ≤ currentScaleHighJMargin)
    (hprefix_lt :
      ∀ ω,
        ω ∈ centeredHighTailEvent start K pre s m →
          prefixIncrement start K pre ω <
            centeredHighTailBinBase s m delta + N) :
    ∀ ω,
      ω ∈ centeredHighTailEvent start K pre s m →
        ∃ idx, idx ∈ Finset.range N ∧
          ω ∈ centeredHighTailBinEvent start K pre s m delta idx := by
  intro ω hω
  let base : ℕ := centeredHighTailBinBase s m delta
  let inc : ℕ := prefixIncrement start K pre ω
  have hmargin_mem : ω ∈ marginTailEvent start K pre s m delta :=
    centeredHighTailEvent_subset_marginTailEvent_of_delta_le
      (start := start) (K := K) (pre := pre) (s := s) (m := m)
      hdelta_le hω
  have hmargin : ((s : ℝ) / 4) + delta * (m : ℝ) ≤ (inc : ℝ) := by
    simpa [marginTailEvent, inc] using hmargin_mem
  have hbase_le : base ≤ inc := by
    simpa [base, inc, centeredHighTailBinBase] using Nat.ceil_le.mpr hmargin
  refine ⟨inc - base, ?_, ?_⟩
  · rw [Finset.mem_range]
    have hlt : base + (inc - base) < base + N := by
      simpa [base, inc, Nat.add_sub_of_le hbase_le] using hprefix_lt ω hω
    exact Nat.add_lt_add_iff_left.mp hlt
  · simp [centeredHighTailBinEvent, base, inc, Nat.add_sub_of_le hbase_le]

/--
Pointwise domination of the exact two-term Lemma 7.7 kernel summand by the
shifted exponential envelope.

The current-scale input `s <= alpha * m` lets the Gaussian scale `1+s` be
bounded by `(1+alpha) * m`; the positive margin `delta * m` then turns both
kernel terms into `exp (-c * (delta*m + idx))`.
-/
theorem exactKernelTailSummand_le_exp
    {a b alpha delta c K V : ℝ} {s m idx : ℕ}
    (ha : 0 < a) (halpha : 0 ≤ alpha)
    (hdelta : 0 < delta) (hm : 1 ≤ m)
    (hscale : (s : ℝ) ≤ alpha * (m : ℝ))
    (hc_gauss : c ≤ a * delta / (1 + alpha))
    (hc_lin : c ≤ b)
    (hK : 0 ≤ K) (hV : 0 ≤ V) :
    exactKernelTailSummand a b K V delta s m idx ≤
      (2 * K * V) * Real.exp (-c * (delta * (m : ℝ) + (idx : ℝ))) := by
  let x : ℝ := delta * (m : ℝ) + (idx : ℝ)
  have hm_real : 1 ≤ (m : ℝ) := by exact_mod_cast hm
  have hm_pos : 0 < (m : ℝ) := lt_of_lt_of_le zero_lt_one hm_real
  have hidx_nonneg : 0 ≤ (idx : ℝ) := by exact_mod_cast Nat.zero_le idx
  have hx_pos : 0 < x := by
    dsimp [x]
    nlinarith
  have hx_nonneg : 0 ≤ x := le_of_lt hx_pos
  have hden_pos : 0 < 1 + (s : ℝ) := by positivity
  have hone_alpha_pos : 0 < 1 + alpha := by nlinarith
  have hden_le : 1 + (s : ℝ) ≤ (1 + alpha) * (m : ℝ) := by
    nlinarith
  have hgauss_arg : c * x ≤ a * (x ^ 2 / (1 + (s : ℝ))) := by
    have hc_mul_x : c * x ≤ (a * delta / (1 + alpha)) * x := by
      exact mul_le_mul_of_nonneg_right hc_gauss hx_nonneg
    have hdelta_x_le :
        delta * x / (1 + alpha) ≤ x ^ 2 / (1 + (s : ℝ)) := by
      rw [div_le_div_iff₀ hone_alpha_pos hden_pos]
      have hleft1 :
          delta * x * (1 + (s : ℝ)) ≤
            delta * x * ((1 + alpha) * (m : ℝ)) := by
        exact
          mul_le_mul_of_nonneg_left hden_le
            (by nlinarith [hdelta, hx_pos] : 0 ≤ delta * x)
      have hx_ge_delta_m : delta * (m : ℝ) ≤ x := by
        dsimp [x]
        nlinarith
      have hright1 :
          delta * x * ((1 + alpha) * (m : ℝ)) ≤
            x ^ 2 * (1 + alpha) := by
        have hmul :=
          mul_le_mul_of_nonneg_right hx_ge_delta_m
            (mul_nonneg hx_nonneg (le_of_lt hone_alpha_pos))
        nlinarith
      exact le_trans hleft1 hright1
    have hscaled :
        (a * delta / (1 + alpha)) * x ≤
          a * (x ^ 2 / (1 + (s : ℝ))) := by
      calc
        (a * delta / (1 + alpha)) * x
            = a * (delta * x / (1 + alpha)) := by ring
        _ ≤ a * (x ^ 2 / (1 + (s : ℝ))) :=
            mul_le_mul_of_nonneg_left hdelta_x_le (le_of_lt ha)
    exact le_trans hc_mul_x hscaled
  have hgauss_exp :
      Real.exp (-a * (x ^ 2 / (1 + (s : ℝ)))) ≤ Real.exp (-c * x) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hlin_exp : Real.exp (-b * x) ≤ Real.exp (-c * x) := by
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_right hc_lin hx_nonneg
    nlinarith
  have hpref_le : ((1 + (s : ℝ)) ^ (-(1 / 2 : ℝ))) ≤ 1 := by
    have hs_nonneg : 0 ≤ (s : ℝ) := by exact_mod_cast Nat.zero_le s
    have hone : (1 : ℝ) ≤ 1 + (s : ℝ) := by nlinarith
    exact Real.rpow_le_one_of_one_le_of_nonpos hone (by norm_num)
  have hKV_nonneg : 0 ≤ K * V := mul_nonneg hK hV
  have hsum_exp :
      Real.exp (-a * (x ^ 2 / (1 + (s : ℝ)))) + Real.exp (-b * x) ≤
        2 * Real.exp (-c * x) := by
    nlinarith [hgauss_exp, hlin_exp]
  have hsum_nonneg :
      0 ≤ Real.exp (-a * (x ^ 2 / (1 + (s : ℝ)))) + Real.exp (-b * x) := by
    positivity
  have hKV_one_nonneg : 0 ≤ K * V * 1 := by nlinarith
  calc
    exactKernelTailSummand a b K V delta s m idx
        = K * V * ((1 + (s : ℝ)) ^ (-(1 / 2 : ℝ))) *
          (Real.exp (-a * (x ^ 2 / (1 + (s : ℝ)))) + Real.exp (-b * x)) := by
          dsimp [exactKernelTailSummand, x]
    _ ≤ K * V * 1 *
          (Real.exp (-a * (x ^ 2 / (1 + (s : ℝ)))) + Real.exp (-b * x)) := by
          exact
            mul_le_mul_of_nonneg_right
              (mul_le_mul_of_nonneg_left hpref_le hKV_nonneg) hsum_nonneg
    _ ≤ K * V * 1 * (2 * Real.exp (-c * x)) := by
          exact mul_le_mul_of_nonneg_left hsum_exp hKV_one_nonneg
    _ = (2 * K * V) *
          Real.exp (-c * (delta * (m : ℝ) + (idx : ℝ))) := by
          dsimp [x]
          ring

/--
Finite exact Lemma 7.7 kernel-tail envelope dominated by the shifted
exponential envelope.
-/
theorem exactKernelTailEnvelope_le_kernelTailEnvelope
    {a b alpha delta c K V : ℝ} {s m N : ℕ}
    (ha : 0 < a) (halpha : 0 ≤ alpha)
    (hdelta : 0 < delta) (hm : 1 ≤ m)
    (hscale : (s : ℝ) ≤ alpha * (m : ℝ))
    (hc_gauss : c ≤ a * delta / (1 + alpha))
    (hc_lin : c ≤ b)
    (hK : 0 ≤ K) (hV : 0 ≤ V) :
    exactKernelTailEnvelope a b K V delta s m N ≤
      kernelTailEnvelope (2 * K * V) c delta m N := by
  unfold exactKernelTailEnvelope kernelTailEnvelope
  exact Finset.sum_le_sum fun idx _hidx =>
    exactKernelTailSummand_le_exp
      (a := a) (b := b) (alpha := alpha) (delta := delta)
      (c := c) (K := K) (V := V) (s := s) (m := m) (idx := idx)
      ha halpha hdelta hm hscale hc_gauss hc_lin hK hV

/--
Finite shifted exponential tail bound for the Lemma 7.7 kernel-tail layer.

The constant `C` is deliberately abstract: later source-facing work may fill
it with the pointwise kernel constant after summing vertical overshoot.
-/
theorem kernelTailEnvelope_le
    {C c delta : ℝ} {m N : ℕ}
    (hC_nonneg : 0 ≤ C) (hc_pos : 0 < c) :
    kernelTailEnvelope C c delta m N ≤
      C * Real.exp (-c * (delta * (m : ℝ))) *
        (1 - Real.exp (-c))⁻¹ := by
  have hsum :
      (∑ idx ∈ Finset.range N,
        Real.exp (-c * (delta * (m : ℝ) + (idx : ℝ)))) ≤
        Real.exp (-c * (delta * (m : ℝ))) *
          (1 - Real.exp (-c))⁻¹ := by
    have hterm :
        (∑ idx ∈ Finset.range N,
          Real.exp (-c * (delta * (m : ℝ) + (idx : ℝ)))) =
          Real.exp (-c * (delta * (m : ℝ))) *
            (∑ idx ∈ Finset.range N, Real.exp (-c * (idx : ℝ))) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro idx _hidx
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hterm]
    exact mul_le_mul_of_nonneg_left
      (finite_exp_neg_mul_sum_le_inv_one_sub (c := c) hc_pos N)
      (le_of_lt (Real.exp_pos (-c * (delta * (m : ℝ)))))
  calc
    kernelTailEnvelope C c delta m N
        = C * (∑ idx ∈ Finset.range N,
          Real.exp (-c * (delta * (m : ℝ) + (idx : ℝ)))) := by
          rw [kernelTailEnvelope, Finset.mul_sum]
    _ ≤ C *
          (Real.exp (-c * (delta * (m : ℝ))) *
            (1 - Real.exp (-c))⁻¹) :=
          mul_le_mul_of_nonneg_left hsum hC_nonneg
    _ = C * Real.exp (-c * (delta * (m : ℝ))) *
          (1 - Real.exp (-c))⁻¹ := by ring

/--
Compare the finite kernel-tail envelope to an explicit exponential-in-`m`
budget.

This is the deterministic budget-comparison layer expected before a future
probability theorem can remove the `centeredHighTailEvent` hypothesis.
The positive `ctail` input is route-facing evidence that the final budget is a
real exponential decay budget, not only a vacuous nonpositive-rate comparison.
-/
theorem kernelTailEnvelope_le_exp_budget
    {C c delta Ctail ctail : ℝ} {m N : ℕ}
    (hC_nonneg : 0 ≤ C) (hc_pos : 0 < c)
    (hCtail_nonneg : 0 ≤ Ctail)
    (_hctail_pos : 0 < ctail)
    (hconst : C * (1 - Real.exp (-c))⁻¹ ≤ Ctail)
    (hdecay : ctail ≤ c * delta) :
    kernelTailEnvelope C c delta m N ≤
      Ctail * Real.exp (-ctail * (m : ℝ)) := by
  have hbase :=
    kernelTailEnvelope_le (C := C) (c := c) (delta := delta)
      (m := m) (N := N) hC_nonneg hc_pos
  have hexp_le :
      Real.exp (-c * (delta * (m : ℝ))) ≤
        Real.exp (-ctail * (m : ℝ)) := by
    apply Real.exp_le_exp.mpr
    have hm_nonneg : 0 ≤ (m : ℝ) := by exact_mod_cast Nat.zero_le m
    nlinarith
  calc
    kernelTailEnvelope C c delta m N
        ≤ C * Real.exp (-c * (delta * (m : ℝ))) *
            (1 - Real.exp (-c))⁻¹ := hbase
    _ = (C * (1 - Real.exp (-c))⁻¹) *
          Real.exp (-c * (delta * (m : ℝ))) := by ring
    _ ≤ Ctail * Real.exp (-c * (delta * (m : ℝ))) := by
          exact mul_le_mul_of_nonneg_right hconst (le_of_lt (Real.exp_pos _))
    _ ≤ Ctail * Real.exp (-ctail * (m : ℝ)) := by
          exact mul_le_mul_of_nonneg_left hexp_le hCtail_nonneg

/--
Exact two-term Lemma 7.7 kernel-tail envelope bounded by an explicit
exponential-in-`m` budget.

This is still deterministic analytic support: future work must connect the
pointwise first-passage law and source/fiber decomposition to this exact
kernel envelope before claiming a centered-tail probability producer.
It also assumes the positive-side shifted tail variable explicitly; absolute
value removal, integer-tail rounding, and the horizontal marginal/vertical
overshoot summation are separate caller-side gates.
-/
theorem exactKernelTailEnvelope_le_exp_budget
    {a b alpha delta c K V Ctail ctail : ℝ} {s m N : ℕ}
    (ha : 0 < a) (halpha : 0 ≤ alpha)
    (hdelta : 0 < delta) (hc_pos : 0 < c) (hm : 1 ≤ m)
    (hscale : (s : ℝ) ≤ alpha * (m : ℝ))
    (hc_gauss : c ≤ a * delta / (1 + alpha))
    (hc_lin : c ≤ b)
    (hK : 0 ≤ K) (hV : 0 ≤ V)
    (hCtail : 0 ≤ Ctail)
    (hctail_pos : 0 < ctail)
    (hconst : (2 * K * V) * (1 - Real.exp (-c))⁻¹ ≤ Ctail)
    (hdecay : ctail ≤ c * delta) :
    exactKernelTailEnvelope a b K V delta s m N ≤
      Ctail * Real.exp (-ctail * (m : ℝ)) := by
  have hC_nonneg : 0 ≤ 2 * K * V := by
    nlinarith [mul_nonneg hK hV]
  exact
    le_trans
      (exactKernelTailEnvelope_le_kernelTailEnvelope
        (a := a) (b := b) (alpha := alpha) (delta := delta)
        (c := c) (K := K) (V := V) (s := s) (m := m) (N := N)
        ha halpha hdelta hm hscale hc_gauss hc_lin hK hV)
      (kernelTailEnvelope_le_exp_budget
        (C := 2 * K * V) (c := c) (delta := delta)
        (Ctail := Ctail) (ctail := ctail) (m := m) (N := N)
        hC_nonneg hc_pos hCtail hctail_pos hconst hdecay)

/--
Finite centered-tail probability consumer with the exact two-term Lemma 7.7
kernel envelope already summed into an exponential-in-`m` budget.

This removes the generic `hsum` input from
`centeredHighTail_prob_le_of_finite_event_kernel_sum`, but it is still support
only: the caller must supply the finite cover and the pointwise/fiber kernel
estimates.
-/
theorem centeredHighTail_prob_le_of_exactKernelTailEnvelope_exp_budget
    {Ω : Type*} [Fintype Ω] {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint} {Kfirst : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {s m N : ℕ}
    {a b alpha delta c K0 V Ctail ctail : ℝ}
    (event : ℕ → Set Ω)
    (hcover :
      ∀ ω,
        ω ∈ centeredHighTailEvent start Kfirst pre s m →
          ∃ idx, idx ∈ Finset.range N ∧ ω ∈ event idx)
    (hfiber :
      ∀ idx, idx ∈ Finset.range N →
        pmfProb μ (event idx) ≤
          exactKernelTailSummand a b K0 V delta s m idx)
    (ha : 0 < a) (halpha : 0 ≤ alpha)
    (hdelta : 0 < delta) (hc_pos : 0 < c) (hm : 1 ≤ m)
    (hscale : (s : ℝ) ≤ alpha * (m : ℝ))
    (hc_gauss : c ≤ a * delta / (1 + alpha))
    (hc_lin : c ≤ b)
    (hK : 0 ≤ K0) (hV : 0 ≤ V)
    (hCtail : 0 ≤ Ctail)
    (hctail_pos : 0 < ctail)
    (hconst : (2 * K0 * V) * (1 - Real.exp (-c))⁻¹ ≤ Ctail)
    (hdecay : ctail ≤ c * delta) :
    pmfProb μ (centeredHighTailEvent start Kfirst pre s m) ≤
      Ctail * Real.exp (-ctail * (m : ℝ)) := by
  have hsum :
      (Finset.range N).sum
          (fun idx => exactKernelTailSummand a b K0 V delta s m idx) ≤
        Ctail * Real.exp (-ctail * (m : ℝ)) := by
    simpa [exactKernelTailEnvelope] using
      exactKernelTailEnvelope_le_exp_budget
        (a := a) (b := b) (alpha := alpha) (delta := delta)
        (c := c) (K := K0) (V := V) (Ctail := Ctail)
        (ctail := ctail) (s := s) (m := m) (N := N)
        ha halpha hdelta hc_pos hm hscale hc_gauss hc_lin hK hV
        hCtail hctail_pos hconst hdecay
  exact
    centeredHighTail_prob_le_of_finite_event_kernel_sum
      (μ := μ) (start := start) (K := Kfirst) (pre := pre)
      (s := s) (m := m) (I := Finset.range N) (event := event)
      (kernelMass := fun idx => exactKernelTailSummand a b K0 V delta s m idx)
      (bPre := Ctail * Real.exp (-ctail * (m : ℝ)))
      hcover hfiber hsum

/--
High-horizontal probability consumer from current-scale `(7.52)`, a finite
centered-tail cover/fiber family, and the exact two-term kernel envelope
summed into an exponential-in-`m` budget.

This removes only the generic finite-sum premise.  The finite cover and fiber
law remain the source-facing analytic producers.
-/
theorem highJ_prob_le_of_currentScale_exactKernelTailEnvelope_exp_budget
    {Ω : Type*} [Fintype Ω] {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint} {Kfirst : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {s m N : ℕ}
    {a b alpha delta c K0 V Ctail ctail : ℝ}
    (event : ℕ → Set Ω)
    (hcurrent : (s : ℝ) ≤ (Real.log 9 / Real.log 2) * (m : ℝ))
    (hcover :
      ∀ ω,
        ω ∈ centeredHighTailEvent start Kfirst pre s m →
          ∃ idx, idx ∈ Finset.range N ∧ ω ∈ event idx)
    (hfiber :
      ∀ idx, idx ∈ Finset.range N →
        pmfProb μ (event idx) ≤
          exactKernelTailSummand a b K0 V delta s m idx)
    (ha : 0 < a) (halpha : 0 ≤ alpha)
    (hdelta : 0 < delta) (hc_pos : 0 < c) (hm : 1 ≤ m)
    (hscale : (s : ℝ) ≤ alpha * (m : ℝ))
    (hc_gauss : c ≤ a * delta / (1 + alpha))
    (hc_lin : c ≤ b)
    (hK : 0 ≤ K0) (hV : 0 ≤ V)
    (hCtail : 0 ≤ Ctail)
    (hctail_pos : 0 < ctail)
    (hconst : (2 * K0 * V) * (1 - Real.exp (-c))⁻¹ ≤ Ctail)
    (hdecay : ctail ≤ c * delta) :
    pmfProb μ (highJEvent start Kfirst pre m) ≤
      Ctail * Real.exp (-ctail * (m : ℝ)) :=
  highJ_prob_le_of_currentScale_centeredTail
    (start := start) (K := Kfirst) (pre := pre) hcurrent
    (centeredHighTail_prob_le_of_exactKernelTailEnvelope_exp_budget
      (μ := μ) (start := start) (Kfirst := Kfirst) (pre := pre)
      (s := s) (m := m) (N := N) event hcover hfiber
      ha halpha hdelta hc_pos hm hscale hc_gauss hc_lin hK hV
      hCtail hctail_pos hconst hdecay)

/--
Centered-tail probability consumer using the canonical finite integer bins.

Compared with
`centeredHighTail_prob_le_of_exactKernelTailEnvelope_exp_budget`, this removes
the arbitrary finite-cover premise.  The caller supplies only the deterministic
margin/upper-bound inputs that make the canonical bins cover the tail, plus the
still-open source-facing fiber bounds for those bins.
-/
theorem centeredHighTail_prob_le_of_exactKernelCanonicalBins_exp_budget
    {Ω : Type*} [Fintype Ω] {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint} {Kfirst : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {s m N : ℕ}
    {a b alpha delta c K0 V Ctail ctail : ℝ}
    (hdelta_le : delta ≤ currentScaleHighJMargin)
    (hprefix_lt :
      ∀ ω,
        ω ∈ centeredHighTailEvent start Kfirst pre s m →
          prefixIncrement start Kfirst pre ω <
            centeredHighTailBinBase s m delta + N)
    (hfiber :
      ∀ idx, idx ∈ Finset.range N →
        pmfProb μ (centeredHighTailBinEvent start Kfirst pre s m delta idx) ≤
          exactKernelTailSummand a b K0 V delta s m idx)
    (ha : 0 < a) (halpha : 0 ≤ alpha)
    (hdelta : 0 < delta) (hc_pos : 0 < c) (hm : 1 ≤ m)
    (hscale : (s : ℝ) ≤ alpha * (m : ℝ))
    (hc_gauss : c ≤ a * delta / (1 + alpha))
    (hc_lin : c ≤ b)
    (hK : 0 ≤ K0) (hV : 0 ≤ V)
    (hCtail : 0 ≤ Ctail)
    (hctail_pos : 0 < ctail)
    (hconst : (2 * K0 * V) * (1 - Real.exp (-c))⁻¹ ≤ Ctail)
    (hdecay : ctail ≤ c * delta) :
    pmfProb μ (centeredHighTailEvent start Kfirst pre s m) ≤
      Ctail * Real.exp (-ctail * (m : ℝ)) :=
  centeredHighTail_prob_le_of_exactKernelTailEnvelope_exp_budget
    (μ := μ) (start := start) (Kfirst := Kfirst) (pre := pre)
    (s := s) (m := m) (N := N)
    (a := a) (b := b) (alpha := alpha) (delta := delta)
    (c := c) (K0 := K0) (V := V) (Ctail := Ctail)
    (ctail := ctail)
    (centeredHighTailBinEvent start Kfirst pre s m delta)
    (centeredHighTailEvent_canonicalBinCover
      (start := start) (K := Kfirst) (pre := pre) (s := s) (m := m)
      (N := N) (delta := delta) hdelta_le hprefix_lt)
    hfiber
    ha halpha hdelta hc_pos hm hscale hc_gauss hc_lin hK hV
    hCtail hctail_pos hconst hdecay

/--
High-horizontal probability consumer from current-scale `(7.52)` and the
canonical exact-kernel integer bins.

This removes the arbitrary finite-cover premise from the high-`J` exact-kernel
path.  The per-bin fiber law remains the source-facing Lemma 7.7 producer.
-/
theorem highJ_prob_le_of_currentScale_exactKernelCanonicalBins_exp_budget
    {Ω : Type*} [Fintype Ω] {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint} {Kfirst : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {s m N : ℕ}
    {a b alpha delta c K0 V Ctail ctail : ℝ}
    (hcurrent : (s : ℝ) ≤ (Real.log 9 / Real.log 2) * (m : ℝ))
    (hdelta_le : delta ≤ currentScaleHighJMargin)
    (hprefix_lt :
      ∀ ω,
        ω ∈ centeredHighTailEvent start Kfirst pre s m →
          prefixIncrement start Kfirst pre ω <
            centeredHighTailBinBase s m delta + N)
    (hfiber :
      ∀ idx, idx ∈ Finset.range N →
        pmfProb μ (centeredHighTailBinEvent start Kfirst pre s m delta idx) ≤
          exactKernelTailSummand a b K0 V delta s m idx)
    (ha : 0 < a) (halpha : 0 ≤ alpha)
    (hdelta : 0 < delta) (hc_pos : 0 < c) (hm : 1 ≤ m)
    (hscale : (s : ℝ) ≤ alpha * (m : ℝ))
    (hc_gauss : c ≤ a * delta / (1 + alpha))
    (hc_lin : c ≤ b)
    (hK : 0 ≤ K0) (hV : 0 ≤ V)
    (hCtail : 0 ≤ Ctail)
    (hctail_pos : 0 < ctail)
    (hconst : (2 * K0 * V) * (1 - Real.exp (-c))⁻¹ ≤ Ctail)
    (hdecay : ctail ≤ c * delta) :
    pmfProb μ (highJEvent start Kfirst pre m) ≤
      Ctail * Real.exp (-ctail * (m : ℝ)) :=
  highJ_prob_le_of_currentScale_centeredTail
    (start := start) (K := Kfirst) (pre := pre) hcurrent
    (centeredHighTail_prob_le_of_exactKernelCanonicalBins_exp_budget
      (μ := μ) (start := start) (Kfirst := Kfirst) (pre := pre)
      (s := s) (m := m) (N := N)
      hdelta_le hprefix_lt hfiber
      ha halpha hdelta hc_pos hm hscale hc_gauss hc_lin hK hV
      hCtail hctail_pos hconst hdecay)

/--
Source-facing package for the canonical-bin Lemma 7.7 exact-kernel layer.

Both the finite-support side condition and the per-bin source/fiber estimate
are tied to the same source PMF `ν`, sample map `sampleOf`, bin count `N`,
margin `delta`, and prefix path data.  This is still not a producer for Lemma
7.7: the `support` and `fiber` fields are the hard source-facing facts.
-/
structure ExactKernelCanonicalBinSourceInputs
    {Ωsrc Ω : Type*} [Fintype Ωsrc] [Fintype Ω]
    (ν : PMF Ωsrc) (μ : PMF Ω) (sampleOf : Ωsrc → Ω)
    (start : Ω → TaoSection7RenewalPoint) (K : Ω → ℕ)
    (pre : Ω → List TaoSection7RenewalPoint)
    (s m N : ℕ) (a b K0 V delta : ℝ) : Prop where
  sample_law : μ = ν.map sampleOf
  support :
    ∀ η,
      sampleOf η ∈ centeredHighTailEvent start K pre s m →
        prefixIncrement start K pre (sampleOf η) <
          centeredHighTailBinBase s m delta + N
  fiber :
    ∀ idx, idx ∈ Finset.range N →
      pmfProb ν
          (sampleOf ⁻¹' centeredHighTailBinEvent start K pre s m delta idx) ≤
        exactKernelTailSummand a b K0 V delta s m idx

/--
The source-facing package covers the source preimage of the centered-tail event
by the same canonical bins.  This avoids requiring a target-space upper bound
away from the image of `sampleOf`.
-/
theorem sourceCanonicalBinCover
    {Ωsrc Ω : Type*} [Fintype Ωsrc] [Fintype Ω]
    {ν : PMF Ωsrc} {μ : PMF Ω} {sampleOf : Ωsrc → Ω}
    {start : Ω → TaoSection7RenewalPoint} {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {s m N : ℕ} {a b K0 V delta : ℝ}
    (hinputs :
      ExactKernelCanonicalBinSourceInputs
        ν μ sampleOf start K pre s m N a b K0 V delta)
    (hdelta_le : delta ≤ currentScaleHighJMargin) :
    ∀ η,
      η ∈ sampleOf ⁻¹' centeredHighTailEvent start K pre s m →
        ∃ idx, idx ∈ Finset.range N ∧
          η ∈ sampleOf ⁻¹' centeredHighTailBinEvent start K pre s m delta idx := by
  intro η hη
  let base : ℕ := centeredHighTailBinBase s m delta
  let inc : ℕ := prefixIncrement start K pre (sampleOf η)
  have hmargin_mem : sampleOf η ∈ marginTailEvent start K pre s m delta :=
    centeredHighTailEvent_subset_marginTailEvent_of_delta_le
      (start := start) (K := K) (pre := pre) (s := s) (m := m)
      hdelta_le hη
  have hmargin : ((s : ℝ) / 4) + delta * (m : ℝ) ≤ (inc : ℝ) := by
    simpa [marginTailEvent, inc] using hmargin_mem
  have hbase_le : base ≤ inc := by
    simpa [base, inc, centeredHighTailBinBase] using Nat.ceil_le.mpr hmargin
  refine ⟨inc - base, ?_, ?_⟩
  · rw [Finset.mem_range]
    have hlt : base + (inc - base) < base + N := by
      simpa [base, inc, Nat.add_sub_of_le hbase_le] using hinputs.support η hη
    exact Nat.add_lt_add_iff_left.mp hlt
  · simp [centeredHighTailBinEvent, base, inc, Nat.add_sub_of_le hbase_le]

/--
Centered-tail exact-kernel consumer from a coherent source package for
canonical bins.

This removes the target-space `hprefix_lt`/`hfiber` assumptions from the
canonical-bin consumer, replacing them with the source package fields.  It is
still support only: the package fields must be proved from Lemma 7.7
first-passage/source laws in future work.
-/
theorem centeredHighTail_prob_le_of_exactKernelCanonicalBinSourceInputs_exp_budget
    {Ωsrc Ω : Type*} [Fintype Ωsrc] [Fintype Ω]
    {ν : PMF Ωsrc} {μ : PMF Ω} {sampleOf : Ωsrc → Ω}
    {start : Ω → TaoSection7RenewalPoint} {Kfirst : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {s m N : ℕ}
    {a b alpha delta c K0 V Ctail ctail : ℝ}
    (hinputs :
      ExactKernelCanonicalBinSourceInputs
        ν μ sampleOf start Kfirst pre s m N a b K0 V delta)
    (hdelta_le : delta ≤ currentScaleHighJMargin)
    (ha : 0 < a) (halpha : 0 ≤ alpha)
    (hdelta : 0 < delta) (hc_pos : 0 < c) (hm : 1 ≤ m)
    (hscale : (s : ℝ) ≤ alpha * (m : ℝ))
    (hc_gauss : c ≤ a * delta / (1 + alpha))
    (hc_lin : c ≤ b)
    (hK : 0 ≤ K0) (hV : 0 ≤ V)
    (hCtail : 0 ≤ Ctail)
    (hctail_pos : 0 < ctail)
    (hconst : (2 * K0 * V) * (1 - Real.exp (-c))⁻¹ ≤ Ctail)
    (hdecay : ctail ≤ c * delta) :
    pmfProb μ (centeredHighTailEvent start Kfirst pre s m) ≤
      Ctail * Real.exp (-ctail * (m : ℝ)) := by
  have hprob_eq :
      pmfProb μ (centeredHighTailEvent start Kfirst pre s m) =
        pmfProb ν (sampleOf ⁻¹' centeredHighTailEvent start Kfirst pre s m) := by
    rw [hinputs.sample_law]
    exact
      pmfProb_map_preimage ν sampleOf
        (centeredHighTailEvent start Kfirst pre s m)
  have hsum :
      (Finset.range N).sum
          (fun idx => exactKernelTailSummand a b K0 V delta s m idx) ≤
        Ctail * Real.exp (-ctail * (m : ℝ)) := by
    simpa [exactKernelTailEnvelope] using
      exactKernelTailEnvelope_le_exp_budget
        (a := a) (b := b) (alpha := alpha) (delta := delta)
        (c := c) (K := K0) (V := V) (Ctail := Ctail)
        (ctail := ctail) (s := s) (m := m) (N := N)
        ha halpha hdelta hc_pos hm hscale hc_gauss hc_lin hK hV
        hCtail hctail_pos hconst hdecay
  calc
    pmfProb μ (centeredHighTailEvent start Kfirst pre s m)
        = pmfProb ν (sampleOf ⁻¹' centeredHighTailEvent start Kfirst pre s m) :=
          hprob_eq
    _ ≤ (Finset.range N).sum fun idx =>
          pmfProb ν
            (sampleOf ⁻¹' centeredHighTailBinEvent start Kfirst pre s m delta idx) :=
          TaoSection7Lemma710.pmfProb_le_finset_sum_of_subset_exists
            ν (Finset.range N)
            (fun idx =>
              sampleOf ⁻¹' centeredHighTailBinEvent start Kfirst pre s m delta idx)
            (sampleOf ⁻¹' centeredHighTailEvent start Kfirst pre s m)
            (sourceCanonicalBinCover hinputs hdelta_le)
    _ ≤ (Finset.range N).sum fun idx =>
          exactKernelTailSummand a b K0 V delta s m idx := by
          exact Finset.sum_le_sum fun idx hidx => hinputs.fiber idx hidx
    _ ≤ Ctail * Real.exp (-ctail * (m : ℝ)) := hsum

/--
High-horizontal exact-kernel consumer from a coherent source package for
canonical bins.
-/
theorem highJ_prob_le_of_currentScale_exactKernelCanonicalBinSourceInputs_exp_budget
    {Ωsrc Ω : Type*} [Fintype Ωsrc] [Fintype Ω]
    {ν : PMF Ωsrc} {μ : PMF Ω} {sampleOf : Ωsrc → Ω}
    {start : Ω → TaoSection7RenewalPoint} {Kfirst : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {s m N : ℕ}
    {a b alpha delta c K0 V Ctail ctail : ℝ}
    (hinputs :
      ExactKernelCanonicalBinSourceInputs
        ν μ sampleOf start Kfirst pre s m N a b K0 V delta)
    (hcurrent : (s : ℝ) ≤ (Real.log 9 / Real.log 2) * (m : ℝ))
    (hdelta_le : delta ≤ currentScaleHighJMargin)
    (ha : 0 < a) (halpha : 0 ≤ alpha)
    (hdelta : 0 < delta) (hc_pos : 0 < c) (hm : 1 ≤ m)
    (hscale : (s : ℝ) ≤ alpha * (m : ℝ))
    (hc_gauss : c ≤ a * delta / (1 + alpha))
    (hc_lin : c ≤ b)
    (hK : 0 ≤ K0) (hV : 0 ≤ V)
    (hCtail : 0 ≤ Ctail)
    (hctail_pos : 0 < ctail)
    (hconst : (2 * K0 * V) * (1 - Real.exp (-c))⁻¹ ≤ Ctail)
    (hdecay : ctail ≤ c * delta) :
    pmfProb μ (highJEvent start Kfirst pre m) ≤
      Ctail * Real.exp (-ctail * (m : ℝ)) :=
  highJ_prob_le_of_currentScale_centeredTail
    (start := start) (K := Kfirst) (pre := pre) hcurrent
    (centeredHighTail_prob_le_of_exactKernelCanonicalBinSourceInputs_exp_budget
      (ν := ν) (sampleOf := sampleOf) (μ := μ)
      (start := start) (Kfirst := Kfirst) (pre := pre)
      (s := s) (m := m) (N := N)
      hinputs hdelta_le
      ha halpha hdelta hc_pos hm hscale hc_gauss hc_lin hK hV
      hCtail hctail_pos hconst hdecay)

end TaoSection7Lemma77

end

end Tao
end Erdos1135
