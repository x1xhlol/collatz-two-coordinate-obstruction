/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.Lemma77LocalLimit
import Erdos1135SecondScale.Tao.Renewal.Lemma77FirstPassageEndpoint

/-!
# Lemma 7.7 Endpoint Assembly Surface

This module names the thin boundary between the source-literal `(7.32)`
horizontal convolution surface and the existing pointwise first-passage
endpoint-law kernel vocabulary.

It does not prove the first-passage union bound, the terminal `Hold` tail,
the kernel-shape comparison, Lemma 7.7, `(7.48)`, `BadPre`, Proposition 7.8,
or Tao's theorem.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

namespace TaoSection7Lemma77

/-- Terminal vertical overshoot weight from Tao's Lemma 7.7 proof. -/
def lemma77EndpointOvershootWeight (gamma : ℝ) (overshoot : ℤ) : ℝ :=
  Real.exp (-gamma * (overshoot : ℝ))

/--
Source-shaped endpoint assembly mass after the horizontal `(7.32)` convolution,
before comparison to the existing pointwise endpoint kernel.
-/
def lemma77EndpointAssemblyMass
    (alpha beta gamma : ℝ) (start : TaoSection7RenewalPoint)
    (j : ℤ) (s : ℕ) (overshoot : ℤ) : ℝ :=
  lemma77EndpointOvershootWeight gamma overshoot *
    lemma77HorizontalConvolution732Mass alpha beta start j s

/-- Endpoint assembly mass with Tao's terminal-tail constant kept explicit. -/
def lemma77EndpointAssemblyMassWithConstant
    (M alpha beta gamma : ℝ) (start : TaoSection7RenewalPoint)
    (j : ℤ) (s : ℕ) (overshoot : ℤ) : ℝ :=
  M * lemma77EndpointAssemblyMass alpha beta gamma start j s overshoot

/--
Signed-coordinate pointwise endpoint kernel produced by the local-limit route.

The comparison from this source-shaped kernel to
`lemma77PointwiseEndpointKernel` is kept as an explicit input below.
-/
def lemma77SignedPointwiseEndpointKernel
    (C c gamma : ℝ) (s : ℕ) (j overshoot : ℤ) : ℝ :=
  lemma77EndpointOvershootWeight gamma overshoot *
    lemma77HeightPotentialKernel C c j s

/-- The assembled endpoint mass is bounded by the signed pointwise kernel. -/
theorem lemma77EndpointAssemblyMass_le_signedPointwiseKernel
    {C c beta C33 c33 alpha C32 c32 gamma : ℝ}
    (hheight : Lemma77HeightPotentialInput C c)
    (h733 : Lemma77VerticalSmoothing733Input C c beta C33 c33)
    (h732 : Lemma77HorizontalConvolution732Input alpha C33 c33 C32 c32)
    (start : TaoSection7RenewalPoint) (j : ℤ) (s : ℕ) (overshoot : ℤ) :
    lemma77EndpointAssemblyMass alpha beta gamma start j s overshoot ≤
      lemma77SignedPointwiseEndpointKernel C32 c32 gamma s j overshoot := by
  unfold lemma77EndpointAssemblyMass lemma77SignedPointwiseEndpointKernel
  exact mul_le_mul_of_nonneg_left
    (lemma77HorizontalConvolution732Mass_le_of_horizontalConvolution732Input
      hheight h733 h732 start j s)
    (le_of_lt (Real.exp_pos _))

/-- Scaled assembled endpoint mass is bounded by the scaled signed kernel. -/
theorem lemma77EndpointAssemblyMassWithConstant_le_signedPointwiseKernel
    {M C c beta C33 c33 alpha C32 c32 gamma : ℝ}
    (hM : 0 ≤ M)
    (hheight : Lemma77HeightPotentialInput C c)
    (h733 : Lemma77VerticalSmoothing733Input C c beta C33 c33)
    (h732 : Lemma77HorizontalConvolution732Input alpha C33 c33 C32 c32)
    (start : TaoSection7RenewalPoint) (j : ℤ) (s : ℕ) (overshoot : ℤ) :
    lemma77EndpointAssemblyMassWithConstant M alpha beta gamma start j s overshoot ≤
      lemma77SignedPointwiseEndpointKernel (M * C32) c32 gamma s j overshoot := by
  unfold lemma77EndpointAssemblyMassWithConstant
  calc
    M * lemma77EndpointAssemblyMass alpha beta gamma start j s overshoot ≤
        M * lemma77SignedPointwiseEndpointKernel C32 c32 gamma s j overshoot :=
      mul_le_mul_of_nonneg_left
        (lemma77EndpointAssemblyMass_le_signedPointwiseKernel
          hheight h733 h732 start j s overshoot)
        hM
    _ = lemma77SignedPointwiseEndpointKernel (M * C32) c32 gamma s j overshoot := by
      unfold lemma77SignedPointwiseEndpointKernel lemma77HeightPotentialKernel
      ring

/--
Input comparing the signed local-limit route kernel to the existing natural
coordinate pointwise endpoint kernel.

This is a shape/conversion input, not the first-passage endpoint law.
-/
structure Lemma77EndpointAssemblyKernelComparisonInput
    (C32 c32 gamma A B Cpt D : ℝ) : Prop where
  constants_nonnegative : 0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ Cpt ∧ 0 ≤ D
  signed_kernel_le_pointwise :
    ∀ (s r : ℕ) (overshoot : ℤ),
      0 ≤ overshoot →
        lemma77SignedPointwiseEndpointKernel C32 c32 gamma s (r : ℤ) overshoot ≤
          lemma77PointwiseEndpointKernel A B Cpt D s r overshoot

/-- Projection from the local-limit assembly plus the explicit kernel comparison. -/
theorem lemma77EndpointAssemblyMass_le_pointwiseEndpointKernel
    {C c beta C33 c33 alpha C32 c32 gamma A B Cpt D : ℝ}
    (hheight : Lemma77HeightPotentialInput C c)
    (h733 : Lemma77VerticalSmoothing733Input C c beta C33 c33)
    (h732 : Lemma77HorizontalConvolution732Input alpha C33 c33 C32 c32)
    (hcmp :
      Lemma77EndpointAssemblyKernelComparisonInput C32 c32 gamma A B Cpt D)
    (start : TaoSection7RenewalPoint) (s r : ℕ) (overshoot : ℤ)
    (hover : 0 ≤ overshoot) :
    lemma77EndpointAssemblyMass alpha beta gamma start (r : ℤ) s overshoot ≤
      lemma77PointwiseEndpointKernel A B Cpt D s r overshoot :=
  le_trans
    (lemma77EndpointAssemblyMass_le_signedPointwiseKernel
      hheight h733 h732 start (r : ℤ) s overshoot)
    (hcmp.signed_kernel_le_pointwise s r overshoot hover)

/--
Assembly inputs that turn the local-limit route plus an explicit
source/probability bridge into the existing pointwise endpoint-law socket.
-/
structure Lemma77PointwiseEndpointAssemblyInputs
    {Ω : Type*} [Fintype Ω]
    (μ : PMF Ω)
    (start : Ω → TaoSection7RenewalPoint)
    (K : Ω → ℕ)
    (pre : Ω → List TaoSection7RenewalPoint)
    (s : ℕ)
    (base : TaoSection7RenewalPoint)
    (C0 c0 beta C33 c33 alpha C32 c32 gamma A B Cpt D : ℝ) : Prop where
  source :
    Lemma77EndpointSourceProvenance μ start K pre s
  height :
    Lemma77HeightPotentialInput C0 c0
  vertical_733 :
    Lemma77VerticalSmoothing733Input C0 c0 beta C33 c33
  horizontal_732 :
    Lemma77HorizontalConvolution732Input alpha C33 c33 C32 c32
  kernel_compare :
    Lemma77EndpointAssemblyKernelComparisonInput C32 c32 gamma A B Cpt D
  endpoint_to_assembly :
    ∀ (r : ℕ) (ell : ℤ),
      (s : ℤ) < ell →
        pmfProb μ (relativeEndpointFiberEvent start K pre r ell) ≤
          lemma77EndpointAssemblyMass alpha beta gamma base (r : ℤ) s
            (relativeVerticalOvershoot s ell)

/--
Checked constructor from explicit assembly inputs to the existing pointwise
endpoint-law input surface.
-/
theorem lemma77PointwiseEndpointLawInputs_of_assembly
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {s : ℕ}
    {base : TaoSection7RenewalPoint}
    {C0 c0 beta C33 c33 alpha C32 c32 gamma A B Cpt D : ℝ}
    (h :
      Lemma77PointwiseEndpointAssemblyInputs
        μ start K pre s base C0 c0 beta C33 c33 alpha C32 c32 gamma A B Cpt D) :
    Lemma77PointwiseEndpointLawInputs μ start K pre s A B Cpt D where
  source := h.source
  constants_nonnegative := h.kernel_compare.constants_nonnegative
  pointwise_endpoint_bound := by
    intro r ell hell
    calc
      pmfProb μ (relativeEndpointFiberEvent start K pre r ell) ≤
          lemma77EndpointAssemblyMass alpha beta gamma base (r : ℤ) s
            (relativeVerticalOvershoot s ell) :=
        h.endpoint_to_assembly r ell hell
      _ ≤ lemma77PointwiseEndpointKernel A B Cpt D s r
            (relativeVerticalOvershoot s ell) :=
        lemma77EndpointAssemblyMass_le_pointwiseEndpointKernel
          h.height h.vertical_733 h.horizontal_732 h.kernel_compare
          base s r (relativeVerticalOvershoot s ell)
          (le_of_lt (relativeVerticalOvershoot_pos_of_lt hell))

/-- Projection of the unit-normalized endpoint-to-assembly field. -/
theorem relativeEndpointFiber_prob_le_endpointAssemblyMass_of_assemblyInputs
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {s : ℕ}
    {base : TaoSection7RenewalPoint}
    {C0 c0 beta C33 c33 alpha C32 c32 gamma A B Cpt D : ℝ}
    (h :
      Lemma77PointwiseEndpointAssemblyInputs
        μ start K pre s base C0 c0 beta C33 c33 alpha C32 c32 gamma A B Cpt D)
    {r : ℕ} {ell : ℤ}
    (hell : (s : ℤ) < ell) :
    pmfProb μ (relativeEndpointFiberEvent start K pre r ell) ≤
      lemma77EndpointAssemblyMass alpha beta gamma base (r : ℤ) s
        (relativeVerticalOvershoot s ell) :=
  h.endpoint_to_assembly r ell hell

/-- Point-mass exponential tail input for the terminal `Hold` increment. -/
structure Lemma77TerminalHoldPointTailInput
    (Ctail alpha : ℝ) : Prop where
  constants : 0 ≤ Ctail ∧ 0 < alpha
  point_tail :
    ∀ (jk : ℕ+) (lk : ℤ),
      (taoSection7HoldPMF
        ({ j := jk, l := lk } : TaoSection7RenewalPoint)).toReal ≤
        Ctail * Real.exp
          (-alpha * (((jk : ℕ) : ℝ) + (lk : ℝ)))

/-- Exponential weight used to derive the terminal `Hold` point-tail input. -/
def lemma77TerminalHoldExpWeight
    (alpha : ℝ) (h : TaoSection7RenewalPoint) : ℝ :=
  Real.exp (alpha * (((h.j : ℕ) : ℝ) + (h.l : ℝ)))

/--
Exponential-moment input for the terminal `Hold` law.

The hard source proof is still the moment bound itself; this surface checks the
standard one-atom domination step from a finite exponential moment to the
pointwise tail needed by Lemma 7.7.
-/
structure Lemma77TerminalHoldExpMomentInput
    (Ctail alpha : ℝ) : Prop where
  constants : 0 ≤ Ctail ∧ 0 < alpha
  summable_weighted :
    Summable fun h : TaoSection7RenewalPoint =>
      (taoSection7HoldPMF h).toReal * lemma77TerminalHoldExpWeight alpha h
  moment_le :
    (∑' h : TaoSection7RenewalPoint,
      (taoSection7HoldPMF h).toReal * lemma77TerminalHoldExpWeight alpha h) ≤
      Ctail

/--
Checked conversion from an exponential-moment bound to the terminal point-tail
input.
-/
theorem lemma77TerminalHoldPointTailInput_of_expMoment
    {Ctail alpha : ℝ}
    (h : Lemma77TerminalHoldExpMomentInput Ctail alpha) :
    Lemma77TerminalHoldPointTailInput Ctail alpha where
  constants := h.constants
  point_tail := by
    intro jk lk
    let p : TaoSection7RenewalPoint := { j := jk, l := lk }
    let x : ℝ := (((jk : ℕ) : ℝ) + (lk : ℝ))
    have hnonneg : ∀ q : TaoSection7RenewalPoint,
        0 ≤ (taoSection7HoldPMF q).toReal * lemma77TerminalHoldExpWeight alpha q := by
      intro q
      exact mul_nonneg ENNReal.toReal_nonneg (le_of_lt (Real.exp_pos _))
    have hterm_le :
        (taoSection7HoldPMF p).toReal * lemma77TerminalHoldExpWeight alpha p ≤
          ∑' q : TaoSection7RenewalPoint,
            (taoSection7HoldPMF q).toReal * lemma77TerminalHoldExpWeight alpha q := by
      exact h.summable_weighted.le_tsum p (fun q _ => hnonneg q)
    have hweighted_le :
        (taoSection7HoldPMF p).toReal * Real.exp (alpha * x) ≤ Ctail := by
      calc
        (taoSection7HoldPMF p).toReal * Real.exp (alpha * x) =
            (taoSection7HoldPMF p).toReal *
              lemma77TerminalHoldExpWeight alpha p := by
          simp [p, x, lemma77TerminalHoldExpWeight]
        _ ≤ ∑' q : TaoSection7RenewalPoint,
            (taoSection7HoldPMF q).toReal * lemma77TerminalHoldExpWeight alpha q :=
          hterm_le
        _ ≤ Ctail := h.moment_le
    have hmul :=
      mul_le_mul_of_nonneg_right hweighted_le
        (le_of_lt (Real.exp_pos (-alpha * x)))
    have hcancel : Real.exp (alpha * x) * Real.exp (-alpha * x) = 1 := by
      rw [← Real.exp_add]
      ring_nf
      simp
    calc
      (taoSection7HoldPMF { j := jk, l := lk }).toReal =
          (taoSection7HoldPMF p).toReal := by
        rfl
      _ = (taoSection7HoldPMF p).toReal * 1 := by
        ring
      _ = (taoSection7HoldPMF p).toReal *
            (Real.exp (alpha * x) * Real.exp (-alpha * x)) := by
        rw [hcancel]
      _ = ((taoSection7HoldPMF p).toReal * Real.exp (alpha * x)) *
            Real.exp (-alpha * x) := by
        ring
      _ ≤ Ctail * Real.exp (-alpha * x) := hmul
      _ = Ctail * Real.exp (-alpha * (((jk : ℕ) : ℝ) + (lk : ℝ))) := by
        simp [x]

/-- Terminal `Hold` point used by the first-passage endpoint split. -/
def lemma77TerminalHoldPoint
    (q : ℕ) (overshoot : ℤ) (lp : ℕ) : TaoSection7RenewalPoint :=
  { j := ⟨q + 1, Nat.succ_pos q⟩
    l := overshoot + (lp : ℤ) }

/--
Explicit terminal-split mass for the source/probability bridge into the
post-`(7.32)` assembly surface.

This names the two independent summation coordinates before the terminal-tail
constant and the horizontal convolution estimate are applied.
-/
def lemma77EndpointTerminalSplitMass
    (origin : TaoSection7RenewalPoint) (r s : ℕ) (overshoot : ℤ) : ℝ :=
  ∑' q : ℕ,
    ∑ lp ∈ Finset.range (s + 1),
      (taoSection7HoldPMF
        (lemma77TerminalHoldPoint q overshoot lp)).toReal *
        lemma77HeightPotentialMass origin
          (lemma77HorizontalShift732 (r : ℤ) q) (s - lp)

/--
Finite source-image cover consumer for the terminal split.

This is the probability union-bound/summation adapter after a producer has
supplied a finite set of actual terminal coordinates and per-terminal mass
bounds.  It does not prove the first-passage/source-law partition, nor the
per-terminal estimates.
-/
theorem event_prob_le_terminalSplitMass_of_finiteTerminalCover
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {origin : TaoSection7RenewalPoint}
    {s r : ℕ} {overshoot : ℤ}
    (largeEvent : Set Ω)
    (Q : Finset ℕ)
    (event : ℕ → ℕ → Set Ω)
    (hcover :
      ∀ ω, ω ∈ largeEvent →
        ∃ q, q ∈ Q ∧ ∃ lp, lp ∈ Finset.range (s + 1) ∧
          ω ∈ event q lp)
    (hfiber :
      ∀ q, q ∈ Q → ∀ lp, lp ∈ Finset.range (s + 1) →
        pmfProb μ (event q lp) ≤
          (taoSection7HoldPMF
            (lemma77TerminalHoldPoint q overshoot lp)).toReal *
          lemma77HeightPotentialMass origin
            (lemma77HorizontalShift732 (r : ℤ) q) (s - lp))
    (hsummable :
      Summable fun q : ℕ =>
        ∑ lp ∈ Finset.range (s + 1),
          (taoSection7HoldPMF
            (lemma77TerminalHoldPoint q overshoot lp)).toReal *
          lemma77HeightPotentialMass origin
            (lemma77HorizontalShift732 (r : ℤ) q) (s - lp)) :
    pmfProb μ largeEvent ≤
      lemma77EndpointTerminalSplitMass origin r s overshoot := by
  classical
  let terminalTerm : ℕ → ℝ := fun q =>
    ∑ lp ∈ Finset.range (s + 1),
      (taoSection7HoldPMF
        (lemma77TerminalHoldPoint q overshoot lp)).toReal *
      lemma77HeightPotentialMass origin
        (lemma77HorizontalShift732 (r : ℤ) q) (s - lp)
  have hterm_nonneg : ∀ q, 0 ≤ terminalTerm q := by
    intro q
    dsimp [terminalTerm]
    apply Finset.sum_nonneg
    intro lp _hlp
    exact mul_nonneg ENNReal.toReal_nonneg
      (lemma77HeightPotentialMass_nonneg origin
        (lemma77HorizontalShift732 (r : ℤ) q) (s - lp))
  have hcover_pair :
      ∀ ω,
        ω ∈ largeEvent →
          ∃ pair, pair ∈ Q.product (Finset.range (s + 1)) ∧
            ω ∈ event pair.1 pair.2 := by
    intro ω hω
    rcases hcover ω hω with ⟨q, hq, lp, hlp, hωevent⟩
    exact ⟨(q, lp), Finset.mem_product.mpr ⟨hq, hlp⟩, hωevent⟩
  calc
    pmfProb μ largeEvent ≤
        (Q.product (Finset.range (s + 1))).sum fun pair =>
          pmfProb μ (event pair.1 pair.2) :=
      TaoSection7Lemma710.pmfProb_le_finset_sum_of_subset_exists
        μ (Q.product (Finset.range (s + 1)))
        (fun pair : ℕ × ℕ => event pair.1 pair.2)
        largeEvent
        hcover_pair
    _ ≤ (Q.product (Finset.range (s + 1))).sum fun pair =>
          (taoSection7HoldPMF
            (lemma77TerminalHoldPoint pair.1 overshoot pair.2)).toReal *
          lemma77HeightPotentialMass origin
            (lemma77HorizontalShift732 (r : ℤ) pair.1) (s - pair.2) := by
      apply Finset.sum_le_sum
      intro pair hpair
      have hq : pair.1 ∈ Q := (Finset.mem_product.mp hpair).1
      have hlp : pair.2 ∈ Finset.range (s + 1) :=
        (Finset.mem_product.mp hpair).2
      exact hfiber pair.1 hq pair.2 hlp
    _ = ∑ q ∈ Q, terminalTerm q := by
      dsimp [terminalTerm]
      rw [Finset.sum_product]
    _ ≤ ∑' q : ℕ, terminalTerm q :=
      hsummable.sum_le_tsum Q (fun q _hq => hterm_nonneg q)
    _ = lemma77EndpointTerminalSplitMass origin r s overshoot := by
      unfold lemma77EndpointTerminalSplitMass
      rfl

/--
Endpoint-fiber specialization of `event_prob_le_terminalSplitMass_of_finiteTerminalCover`.
-/
theorem relativeEndpointFiber_prob_le_terminalSplitMass_of_finiteTerminalCover
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {origin : TaoSection7RenewalPoint}
    {s r : ℕ} {ell : ℤ}
    (Q : Finset ℕ)
    (event : ℕ → ℕ → Set Ω)
    (hcover :
      ∀ ω,
        ω ∈ relativeEndpointFiberEvent start K pre r ell →
          ∃ q, q ∈ Q ∧ ∃ lp, lp ∈ Finset.range (s + 1) ∧
            ω ∈ event q lp)
    (hfiber :
      ∀ q, q ∈ Q → ∀ lp, lp ∈ Finset.range (s + 1) →
        pmfProb μ (event q lp) ≤
          (taoSection7HoldPMF
            (lemma77TerminalHoldPoint q
              (relativeVerticalOvershoot s ell) lp)).toReal *
          lemma77HeightPotentialMass origin
            (lemma77HorizontalShift732 (r : ℤ) q) (s - lp))
    (hsummable :
      Summable fun q : ℕ =>
        ∑ lp ∈ Finset.range (s + 1),
          (taoSection7HoldPMF
            (lemma77TerminalHoldPoint q
              (relativeVerticalOvershoot s ell) lp)).toReal *
          lemma77HeightPotentialMass origin
            (lemma77HorizontalShift732 (r : ℤ) q) (s - lp)) :
    pmfProb μ (relativeEndpointFiberEvent start K pre r ell) ≤
      lemma77EndpointTerminalSplitMass origin r s
        (relativeVerticalOvershoot s ell) := by
  exact
    event_prob_le_terminalSplitMass_of_finiteTerminalCover
      (μ := μ) (origin := origin) (s := s) (r := r)
      (overshoot := relativeVerticalOvershoot s ell)
      (relativeEndpointFiberEvent start K pre r ell) Q event
      hcover hfiber hsummable

/--
Residual-bad version of the finite terminal-cover consumer.

The caller only covers endpoint-fiber samples outside `bad`; this adapter pays
the bad-event probability once and applies the terminal split to the good
remainder.  It does not prove that `bad` has zero mass or produce the finite
cover.
-/
theorem
    relativeEndpointFiber_prob_le_badProb_add_terminalSplitMass_of_residualFiniteTerminalCover
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {origin : TaoSection7RenewalPoint}
    {s r : ℕ} {ell : ℤ}
    (bad : Set Ω)
    (Q : Finset ℕ)
    (event : ℕ → ℕ → Set Ω)
    (hcover :
      ∀ ω,
        ω ∈ relativeEndpointFiberEvent start K pre r ell →
          ω ∉ bad →
            ∃ q, q ∈ Q ∧ ∃ lp, lp ∈ Finset.range (s + 1) ∧
              ω ∈ event q lp)
    (hfiber :
      ∀ q, q ∈ Q → ∀ lp, lp ∈ Finset.range (s + 1) →
        pmfProb μ (event q lp) ≤
          (taoSection7HoldPMF
            (lemma77TerminalHoldPoint q
              (relativeVerticalOvershoot s ell) lp)).toReal *
          lemma77HeightPotentialMass origin
            (lemma77HorizontalShift732 (r : ℤ) q) (s - lp))
    (hsummable :
      Summable fun q : ℕ =>
        ∑ lp ∈ Finset.range (s + 1),
          (taoSection7HoldPMF
            (lemma77TerminalHoldPoint q
              (relativeVerticalOvershoot s ell) lp)).toReal *
          lemma77HeightPotentialMass origin
            (lemma77HorizontalShift732 (r : ℤ) q) (s - lp)) :
    pmfProb μ (relativeEndpointFiberEvent start K pre r ell) ≤
      pmfProb μ bad +
        lemma77EndpointTerminalSplitMass origin r s
          (relativeVerticalOvershoot s ell) := by
  classical
  let endpointEvent := relativeEndpointFiberEvent start K pre r ell
  have hgood_cover :
      ∀ ω, ω ∈ endpointEvent \ bad →
        ∃ q, q ∈ Q ∧ ∃ lp, lp ∈ Finset.range (s + 1) ∧
          ω ∈ event q lp := by
    intro ω hω
    exact hcover ω hω.1 hω.2
  have hgood_le :
      pmfProb μ (endpointEvent \ bad) ≤
        lemma77EndpointTerminalSplitMass origin r s
          (relativeVerticalOvershoot s ell) :=
    event_prob_le_terminalSplitMass_of_finiteTerminalCover
      (μ := μ) (origin := origin) (s := s) (r := r)
      (overshoot := relativeVerticalOvershoot s ell)
      (endpointEvent \ bad) Q event hgood_cover hfiber hsummable
  have hdiff :
      pmfProb μ endpointEvent - pmfProb μ bad ≤
        pmfProb μ (endpointEvent \ bad) :=
    pmfProb_diff_le_of_diff_subset μ (by
      intro ω hω
      exact hω)
  linarith

/--
Zero-residual corollary of the residual-bad finite terminal-cover consumer.
-/
theorem
    relativeEndpointFiber_prob_le_terminalSplitMass_of_residualFiniteTerminalCover_of_bad_zero
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {origin : TaoSection7RenewalPoint}
    {s r : ℕ} {ell : ℤ}
    (bad : Set Ω)
    (Q : Finset ℕ)
    (event : ℕ → ℕ → Set Ω)
    (hcover :
      ∀ ω,
        ω ∈ relativeEndpointFiberEvent start K pre r ell →
          ω ∉ bad →
            ∃ q, q ∈ Q ∧ ∃ lp, lp ∈ Finset.range (s + 1) ∧
              ω ∈ event q lp)
    (hfiber :
      ∀ q, q ∈ Q → ∀ lp, lp ∈ Finset.range (s + 1) →
        pmfProb μ (event q lp) ≤
          (taoSection7HoldPMF
            (lemma77TerminalHoldPoint q
              (relativeVerticalOvershoot s ell) lp)).toReal *
          lemma77HeightPotentialMass origin
            (lemma77HorizontalShift732 (r : ℤ) q) (s - lp))
    (hsummable :
      Summable fun q : ℕ =>
        ∑ lp ∈ Finset.range (s + 1),
          (taoSection7HoldPMF
            (lemma77TerminalHoldPoint q
              (relativeVerticalOvershoot s ell) lp)).toReal *
          lemma77HeightPotentialMass origin
            (lemma77HorizontalShift732 (r : ℤ) q) (s - lp))
    (hbad_zero : pmfProb μ bad = 0) :
    pmfProb μ (relativeEndpointFiberEvent start K pre r ell) ≤
      lemma77EndpointTerminalSplitMass origin r s
        (relativeVerticalOvershoot s ell) := by
  have h :=
    relativeEndpointFiber_prob_le_badProb_add_terminalSplitMass_of_residualFiniteTerminalCover
      (μ := μ) (start := start) (K := K) (pre := pre)
      (origin := origin) (s := s) (r := r) (ell := ell)
      bad Q event hcover hfiber hsummable
  linarith

/--
Finite subfamilies of the length-restricted signed endpoint fiber have mass at
most the full iid `Hold` endpoint mass.

This is the finite-image side of the length-restricted prefix atomization; the
length condition is part of the fiber being summed.
-/
theorem lemma77HoldPrefixSignedEndpointMass_finset_le
    (start : TaoSection7RenewalPoint) (n : ℕ) (j ell : ℤ)
    (T : Finset (List TaoSection7RenewalPoint))
    (hT : ∀ hs, hs ∈ T →
      hs ∈ lemma77HoldPrefixSignedEndpointLengthEvent start n j ell) :
    (∑ hs ∈ T, (taoSection7HoldListPMF n hs).toReal) ≤
      lemma77HoldPrefixSignedEndpointMass start n j ell := by
  classical
  let E := lemma77HoldPrefixSignedEndpointLengthEvent start n j ell
  let emb : {hs // hs ∈ T} ↪ {hs // hs ∈ E} :=
    ⟨fun hs => (⟨hs.1, hT hs.1 hs.2⟩ : {hs // hs ∈ E}), by
      intro a b h
      exact Subtype.ext (congrArg (fun y : {hs // hs ∈ E} => y.1) h)⟩
  let U : Finset {hs // hs ∈ E} := Finset.univ.map emb
  have hsum_eq :
      (∑ x ∈ U, (taoSection7HoldListPMF n x.1).toReal) =
        ∑ hs ∈ T, (taoSection7HoldListPMF n hs).toReal := by
    dsimp [U]
    rw [Finset.sum_map]
    simpa [emb] using
      (Finset.sum_attach T (fun hs =>
        (taoSection7HoldListPMF n hs).toReal))
  have hfiber_summable :
      Summable fun hs : {hs // hs ∈ E} =>
        (taoSection7HoldListPMF n hs.1).toReal :=
    (taoSection7HoldListPMF_summable_toReal n).subtype E
  have hle :
      (∑ x ∈ U, (taoSection7HoldListPMF n x.1).toReal) ≤
        ∑' hs : {hs // hs ∈ E},
          (taoSection7HoldListPMF n hs.1).toReal :=
    hfiber_summable.sum_le_tsum U (fun _ _ => ENNReal.toReal_nonneg)
  calc
    (∑ hs ∈ T, (taoSection7HoldListPMF n hs).toReal) =
        ∑ x ∈ U, (taoSection7HoldListPMF n x.1).toReal := hsum_eq.symm
    _ ≤ ∑' hs : {hs // hs ∈ E},
          (taoSection7HoldListPMF n hs.1).toReal := hle
    _ = lemma77HoldPrefixSignedEndpointMass start n j ell := by
      simpa [E] using
        (lemma77HoldPrefixSignedEndpointMass_eq_tsum_length_fiber
          start n j ell).symm

/--
Finite variable-prefix subfamilies of length-restricted endpoint fibers are
bounded by the height-potential mass, once the height-potential `n`-series is
known summable.
-/
theorem lemma77HoldPrefixSignedEndpointMass_sigmaFinset_le_heightPotential
    (start : TaoSection7RenewalPoint) (j : ℤ) (s' : ℕ)
    (N : Finset ℕ) (P : ℕ → Finset (List TaoSection7RenewalPoint))
    (hP : ∀ n, n ∈ N → ∀ hs, hs ∈ P n →
      hs ∈ lemma77HoldPrefixSignedEndpointLengthEvent start n j (s' : ℤ))
    (hsummable : Summable fun n : ℕ =>
      lemma77HoldPrefixSignedEndpointMass start n j (s' : ℤ)) :
    (∑ item ∈ N.sigma P,
      (taoSection7HoldListPMF item.1 item.2).toReal) ≤
      lemma77HeightPotentialMass start j s' := by
  classical
  calc
    (∑ item ∈ N.sigma P,
      (taoSection7HoldListPMF item.1 item.2).toReal)
        = ∑ n ∈ N, ∑ hs ∈ P n,
            (taoSection7HoldListPMF n hs).toReal := by
          exact (Finset.sum_sigma' N P
            (fun n hs => (taoSection7HoldListPMF n hs).toReal)).symm
    _ ≤ ∑ n ∈ N,
        lemma77HoldPrefixSignedEndpointMass start n j (s' : ℤ) := by
          exact Finset.sum_le_sum fun n hn =>
            lemma77HoldPrefixSignedEndpointMass_finset_le
              start n j (s' : ℤ) (P n) (hP n hn)
    _ ≤ ∑' n : ℕ,
        lemma77HoldPrefixSignedEndpointMass start n j (s' : ℤ) :=
          hsummable.sum_le_tsum N (fun n _ =>
            lemma77HoldPrefixSignedEndpointMass_nonneg start n j (s' : ℤ))
    _ = lemma77HeightPotentialMass start j s' := by
      rfl

/--
Any certified positive first-passage prefix has a last increment.

This is the deterministic list-shape bridge required by the terminal source
cell decomposition; it does not identify the last increment's coordinates.
-/
theorem verticalFirstPassagePrefix_exists_snoc
    {start : TaoSection7RenewalPoint} {s K : ℕ}
    {pre : List TaoSection7RenewalPoint}
    (hfirst : TaoSection7Lemma710.VerticalFirstPassagePrefix start s K pre) :
    ∃ n pref last,
      K = n + 1 ∧ pref.length = n ∧ pre = pref ++ [last] := by
  have hpre_ne : pre ≠ [] := by
    intro hpre
    have hK0 : K = 0 := by
      simpa [hpre] using hfirst.length_eq.symm
    have hpos : 0 < K := hfirst.K_pos
    omega
  refine ⟨K - 1, pre.dropLast, pre.getLast hpre_ne, ?_, ?_, ?_⟩
  · exact (Nat.succ_pred_eq_of_pos hfirst.K_pos).symm
  · rw [List.length_dropLast, hfirst.length_eq]
  · exact (List.dropLast_append_getLast hpre_ne).symm

/-- Renewal path endpoint after consuming a snoc prefix. -/
theorem taoSection7RenewalPathPoint_snoc
    (start : TaoSection7RenewalPoint)
    (pref : List TaoSection7RenewalPoint)
    (last : TaoSection7RenewalPoint) :
    taoSection7RenewalPathPoint start (pref ++ [last]) (pref.length + 1) =
      taoSection7RenewalPathPoint start pref pref.length + last := by
  simpa [taoSection7RenewalPathPoint] using
    (TaoSection7Lemma710.renewalPathPoint_append_prefix_add
      start pref [last] 1)

/-- Vertical prefix increment across a snoc decomposition. -/
theorem lemma77HoldPrefixVerticalIncrement_snoc
    (start : TaoSection7RenewalPoint) {n : ℕ}
    {pref : List TaoSection7RenewalPoint} (last : TaoSection7RenewalPoint)
    (hlen : pref.length = n) :
    lemma77HoldPrefixVerticalIncrement start (n + 1) (pref ++ [last]) =
      lemma77HoldPrefixVerticalIncrement start n pref + last.l := by
  dsimp [lemma77HoldPrefixVerticalIncrement, prefixVerticalIncrement]
  have happ :=
    TaoSection7Lemma710.renewalPathPoint_append_prefix_add
      start pref [last] 1
  simp [hlen] at happ
  rw [happ]
  simp
  ring

/-- Horizontal prefix increment across a snoc decomposition. -/
theorem lemma77HoldPrefixIncrement_snoc
    (start : TaoSection7RenewalPoint) {n : ℕ}
    {pref : List TaoSection7RenewalPoint} (last : TaoSection7RenewalPoint)
    (hlen : pref.length = n) :
    lemma77HoldPrefixIncrement start (n + 1) (pref ++ [last]) =
      lemma77HoldPrefixIncrement start n pref + (last.j : ℕ) := by
  rw [lemma77HoldPrefixIncrement_eq_horizontalDelta]
  rw [lemma77HoldPrefixIncrement_eq_horizontalDelta]
  induction pref generalizing start n with
  | nil =>
      simp [lemma77HoldPrefixHorizontalDelta] at hlen ⊢
      omega
  | cons h hs ih =>
      cases n with
      | zero => simp at hlen
      | succ n =>
          simp [lemma77HoldPrefixHorizontalDelta] at hlen ⊢
          rw [ih (start + h) hlen]
          omega

/--
Minimality in a first-passage prefix bounds the previous snoc prefix height by
the threshold.
-/
theorem lemma77HoldPrefixVerticalIncrement_le_of_firstPassage_snoc
    {start : TaoSection7RenewalPoint} {s K n : ℕ}
    {pre pref : List TaoSection7RenewalPoint}
    {last : TaoSection7RenewalPoint}
    (hfirst : TaoSection7Lemma710.VerticalFirstPassagePrefix start s K pre)
    (hK : K = n + 1)
    (hsnoc : pre = pref ++ [last])
    (hlen : pref.length = n) :
    lemma77HoldPrefixVerticalIncrement start n pref ≤ (s : ℤ) := by
  have hn_lt : n < K := by omega
  have hmin := hfirst.minimal n hn_lt
  have hpath :
      taoSection7RenewalPathPoint start pre n =
        taoSection7RenewalPathPoint start pref n := by
    rw [hsnoc]
    simpa [hlen] using
      (TaoSection7Lemma710.renewalPathPoint_append_prefix_add
        start pref [last] 0)
  dsimp [lemma77HoldPrefixVerticalIncrement, prefixVerticalIncrement]
  rw [hpath] at hmin
  omega

/--
Deterministic terminal-coordinate split for a snoc first-passage endpoint.

The nonnegative previous-height premise is explicit: it must come from a
zero-mass/residual-bad argument before this pointwise coordinate theorem can be
used to cover arbitrary source samples.
-/
theorem lemma77EndpointFiber_snoc_terminalCoordinates
    {start origin : TaoSection7RenewalPoint}
    {s r K n : ℕ} {ell : ℤ}
    {pre pref : List TaoSection7RenewalPoint}
    {last : TaoSection7RenewalPoint}
    (hfirst : TaoSection7Lemma710.VerticalFirstPassagePrefix start s K pre)
    (hendpoint :
      lemma77HoldPrefixIncrement start K pre = r ∧
      lemma77HoldPrefixVerticalIncrement start K pre = ell)
    (horigin : start = origin)
    (hK : K = n + 1)
    (hsnoc : pre = pref ++ [last])
    (hlen : pref.length = n)
    (hprev_nonneg :
      0 ≤ lemma77HoldPrefixVerticalIncrement origin n pref) :
    ∃ q lp,
      lp ∈ Finset.range (s + 1) ∧
      last = lemma77TerminalHoldPoint q (relativeVerticalOvershoot s ell) lp ∧
      pref ∈ lemma77HoldPrefixSignedEndpointLengthEvent origin n
        (lemma77HorizontalShift732 (r : ℤ) q) ((s - lp : ℕ) : ℤ) := by
  subst origin
  let v : ℤ := lemma77HoldPrefixVerticalIncrement start n pref
  let q : ℕ := (last.j : ℕ) - 1
  let lp : ℕ := s - v.toNat
  have hprev_le : v ≤ (s : ℤ) := by
    dsimp [v]
    exact lemma77HoldPrefixVerticalIncrement_le_of_firstPassage_snoc
      hfirst hK hsnoc hlen
  have hv_nonneg : 0 ≤ v := by
    simpa [v] using hprev_nonneg
  have hv_toNat : (v.toNat : ℤ) = v := Int.toNat_of_nonneg hv_nonneg
  have hv_toNat_le_s : v.toNat ≤ s := by
    omega
  have hlp_mem : lp ∈ Finset.range (s + 1) := by
    simp [lp]
  have hlast_j_nat : (last.j : ℕ) = q + 1 := by
    dsimp [q]
    exact (Nat.succ_pred_eq_of_pos last.j.2).symm
  have hinc_full :
      lemma77HoldPrefixIncrement start (n + 1) (pref ++ [last]) = r := by
    simpa [hK, hsnoc] using hendpoint.1
  have hinc_snoc := lemma77HoldPrefixIncrement_snoc start last hlen
  rw [hinc_snoc] at hinc_full
  have hpref_j :
      (lemma77HoldPrefixIncrement start n pref : ℤ) =
        lemma77HorizontalShift732 (r : ℤ) q := by
    rw [lemma77HorizontalShift732, lemma77PositiveHorizontalIncrement]
    omega
  have hvert_full :
      lemma77HoldPrefixVerticalIncrement start (n + 1) (pref ++ [last]) =
        ell := by
    simpa [hK, hsnoc] using hendpoint.2
  have hvert_snoc := lemma77HoldPrefixVerticalIncrement_snoc start last hlen
  rw [hvert_snoc] at hvert_full
  have hlast_l : last.l = relativeVerticalOvershoot s ell + (lp : ℤ) := by
    dsimp [relativeVerticalOvershoot, lp, v] at *
    have hlp_int : ((s - v.toNat : ℕ) : ℤ) = (s : ℤ) - v := by
      omega
    omega
  have hpref_l :
      lemma77HoldPrefixVerticalIncrement start n pref =
        ((s - lp : ℕ) : ℤ) := by
    dsimp [lp, v] at *
    have hsublp : s - (s - v.toNat) = v.toNat := by
      omega
    rw [hsublp]
    exact hv_toNat.symm
  refine ⟨q, lp, hlp_mem, ?_, ?_⟩
  · ext
    · exact Subtype.ext hlast_j_nat
    · exact hlast_l
  · exact ⟨⟨hpref_j, hpref_l⟩, hlen⟩

/--
Pointwise good-sample terminal-coordinate producer for an endpoint fiber.

The previous-prefix nonnegativity assumption is kept explicit; the finite bad
cover supplies it on the residual good domain in the next source-image layer.
-/
theorem relativeEndpointFiber_terminalCoordinates_of_firstPassage_prevNonneg
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {origin : TaoSection7RenewalPoint}
    {s r : ℕ} {ell : ℤ} {ω : Ω}
    (hsrc : Lemma77EndpointSourceProvenance μ start K pre s)
    (hω : ω ∈ relativeEndpointFiberEvent start K pre r ell)
    (horigin : start ω = origin)
    (hprev_nonneg :
      ∀ (n : ℕ) (pref : List TaoSection7RenewalPoint)
        (last : TaoSection7RenewalPoint),
        K ω = n + 1 →
        pre ω = pref ++ [last] →
        pref.length = n →
        0 ≤ lemma77HoldPrefixVerticalIncrement origin n pref) :
    ∃ n pref q lp,
      lp ∈ Finset.range (s + 1) ∧
      K ω = n + 1 ∧
      pre ω =
        pref ++
          [lemma77TerminalHoldPoint q
            (relativeVerticalOvershoot s ell) lp] ∧
      pref ∈ lemma77HoldPrefixSignedEndpointLengthEvent origin n
        (lemma77HorizontalShift732 (r : ℤ) q) ((s - lp : ℕ) : ℤ) := by
  have hfirst := hsrc.first_passage ω
  rcases verticalFirstPassagePrefix_exists_snoc hfirst with
    ⟨n, pref, last, hK, hlen, hsnoc⟩
  have hendpoint :
      lemma77HoldPrefixIncrement (start ω) (K ω) (pre ω) = r ∧
        lemma77HoldPrefixVerticalIncrement (start ω) (K ω) (pre ω) = ell := by
    simpa [relativeEndpointFiberEvent, lemma77HoldPrefixIncrement,
      lemma77HoldPrefixVerticalIncrement, prefixIncrement,
      prefixVerticalIncrement] using hω
  have hprev :
      0 ≤ lemma77HoldPrefixVerticalIncrement origin n pref :=
    hprev_nonneg n pref last hK hsnoc hlen
  rcases lemma77EndpointFiber_snoc_terminalCoordinates
      (start := start ω) (origin := origin) (s := s) (r := r)
      (K := K ω) (n := n) (ell := ell)
      (pre := pre ω) (pref := pref) (last := last)
      hfirst hendpoint horigin hK hsnoc hlen hprev with
    ⟨q, lp, hlp, hlast, hpref⟩
  refine ⟨n, pref, q, lp, hlp, hK, ?_, hpref⟩
  rw [hsnoc, hlast]

/--
Samples whose previous snoc prefix has negative vertical height.

This is the source-side residual that must be covered by zero-mass bad
cylinders before terminal coordinates can be assigned on the good domain.
-/
def lemma77EndpointPrevNegSnocBad
    {Ω : Type*}
    (origin : TaoSection7RenewalPoint)
    (K : Ω → ℕ)
    (pre : Ω → List TaoSection7RenewalPoint) : Set Ω :=
  {ω | ∃ n pref last,
    K ω = n + 1 ∧
    pref.length = n ∧
    pre ω = pref ++ [last] ∧
    lemma77HoldPrefixVerticalIncrement origin n pref < 0}

/-- Chosen snoc witness for a sample in the previous-negative residual. -/
structure Lemma77EndpointPrevNegSnocWitness
    {Ω : Type*}
    (origin : TaoSection7RenewalPoint)
    (K : Ω → ℕ)
    (pre : Ω → List TaoSection7RenewalPoint)
    (ω : Ω) : Type where
  n : ℕ
  pref : List TaoSection7RenewalPoint
  last : TaoSection7RenewalPoint
  K_eq : K ω = n + 1
  length_eq : pref.length = n
  pre_eq : pre ω = pref ++ [last]
  prev_neg : lemma77HoldPrefixVerticalIncrement origin n pref < 0

/--
Classically choose a negative previous-prefix snoc witness from membership in
the previous-negative residual.
-/
noncomputable def lemma77EndpointPrevNegSnocWitness_of_mem
    {Ω : Type*}
    {origin : TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {ω : Ω}
    (hbad : ω ∈ lemma77EndpointPrevNegSnocBad origin K pre) :
    Lemma77EndpointPrevNegSnocWitness origin K pre ω := by
  classical
  let n : ℕ := Classical.choose hbad
  let hbad_n := Classical.choose_spec hbad
  let pref : List TaoSection7RenewalPoint := Classical.choose hbad_n
  let hbad_pref := Classical.choose_spec hbad_n
  let last : TaoSection7RenewalPoint := Classical.choose hbad_pref
  let hbad_last := Classical.choose_spec hbad_pref
  exact
    { n := n
      pref := pref
      last := last
      K_eq := hbad_last.1
      length_eq := hbad_last.2.1
      pre_eq := hbad_last.2.2.1
      prev_neg := hbad_last.2.2.2 }

/-- Coherent finite-prefix witness extracted from a good endpoint sample. -/
structure Lemma77EndpointGoodSampleFinitePrefixWitness
    {Ω : Type*}
    (start : Ω → TaoSection7RenewalPoint)
    (K : Ω → ℕ)
    (pre : Ω → List TaoSection7RenewalPoint)
    (origin : TaoSection7RenewalPoint)
    (s r : ℕ) (ell : ℤ) (ω : Ω) : Type where
  q : ℕ
  lp : ℕ
  n : ℕ
  pref : List TaoSection7RenewalPoint
  lp_mem : lp ∈ Finset.range (s + 1)
  K_eq : K ω = n + 1
  pre_eq :
    pre ω =
      pref ++
        [lemma77TerminalHoldPoint q
          (relativeVerticalOvershoot s ell) lp]
  prefix_mem :
    pref ∈ lemma77HoldPrefixSignedEndpointLengthEvent origin n
      (lemma77HorizontalShift732 (r : ℤ) q) ((s - lp : ℕ) : ℤ)

/--
Good endpoint samples, outside the previous-negative snoc residual, carry a
coherent terminal-coordinate finite-prefix witness.
-/
noncomputable def lemma77EndpointGoodSampleFinitePrefixWitness_of_not_prevNegSnocBad
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {origin : TaoSection7RenewalPoint}
    {s r : ℕ} {ell : ℤ} {ω : Ω}
    (hsrc : Lemma77EndpointSourceProvenance μ start K pre s)
    (hω : ω ∈ relativeEndpointFiberEvent start K pre r ell)
    (horigin : start ω = origin)
    (hgood : ω ∉ lemma77EndpointPrevNegSnocBad origin K pre) :
    Lemma77EndpointGoodSampleFinitePrefixWitness
      start K pre origin s r ell ω := by
  classical
  have hprev_nonneg :
      ∀ (n : ℕ) (pref : List TaoSection7RenewalPoint)
        (last : TaoSection7RenewalPoint),
        K ω = n + 1 →
        pre ω = pref ++ [last] →
        pref.length = n →
        0 ≤ lemma77HoldPrefixVerticalIncrement origin n pref := by
    intro n pref last hK hpre hlen
    by_contra hnot_nonneg
    exact hgood
      ⟨n, pref, last, hK, hlen, hpre, lt_of_not_ge hnot_nonneg⟩
  let hcoords :
      ∃ n pref q lp,
        lp ∈ Finset.range (s + 1) ∧
        K ω = n + 1 ∧
        pre ω =
          pref ++
            [lemma77TerminalHoldPoint q
              (relativeVerticalOvershoot s ell) lp] ∧
        pref ∈ lemma77HoldPrefixSignedEndpointLengthEvent origin n
          (lemma77HorizontalShift732 (r : ℤ) q) ((s - lp : ℕ) : ℤ) :=
      relativeEndpointFiber_terminalCoordinates_of_firstPassage_prevNonneg
        (μ := μ) (start := start) (K := K) (pre := pre)
        (origin := origin) (s := s) (r := r) (ell := ell)
        hsrc hω horigin hprev_nonneg
  let n : ℕ := Classical.choose hcoords
  let hcoords_n := Classical.choose_spec hcoords
  let pref : List TaoSection7RenewalPoint := Classical.choose hcoords_n
  let hcoords_pref := Classical.choose_spec hcoords_n
  let q : ℕ := Classical.choose hcoords_pref
  let hcoords_q := Classical.choose_spec hcoords_pref
  let lp : ℕ := Classical.choose hcoords_q
  let hcoords_lp := Classical.choose_spec hcoords_q
  exact
    { q := q
      lp := lp
      n := n
      pref := pref
      lp_mem := hcoords_lp.1
      K_eq := hcoords_lp.2.1
      pre_eq := hcoords_lp.2.2.1
      prefix_mem := hcoords_lp.2.2.2 }

/--
Residual endpoint samples have a finite terminal-coordinate source-image
cover once the previous-negative alternatives are included in `bad`.

The finite image data `Q/N/P` is still supplied explicitly.  This theorem
derives the terminal coordinates and prefix endpoint membership for every
sample outside `bad`, so callers no longer have to provide the raw endpoint
fiber cover by hand.
-/
theorem relativeEndpointFiber_finitePrefixImageCover_of_firstPassage_prevNegCover
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {origin : TaoSection7RenewalPoint}
    {s r : ℕ} {ell : ℤ}
    (hsrc : Lemma77EndpointSourceProvenance μ start K pre s)
    (bad : Set Ω)
    (Q : Finset ℕ)
    (N : ℕ → ℕ → Finset ℕ)
    (P : ℕ → ℕ → ℕ → Finset (List TaoSection7RenewalPoint))
    (horigin :
      ∀ ω, ω ∈ relativeEndpointFiberEvent start K pre r ell →
        ω ∉ bad → start ω = origin)
    (hbad_of_prev_neg :
      ∀ ω, ω ∈ relativeEndpointFiberEvent start K pre r ell →
        ∀ (n : ℕ) (pref : List TaoSection7RenewalPoint)
          (last : TaoSection7RenewalPoint),
          K ω = n + 1 →
          pre ω = pref ++ [last] →
          pref.length = n →
          lemma77HoldPrefixVerticalIncrement origin n pref < 0 →
          ω ∈ bad)
    (himage :
      ∀ ω, ω ∈ relativeEndpointFiberEvent start K pre r ell →
        ω ∉ bad →
        ∀ (n : ℕ) (pref : List TaoSection7RenewalPoint) (q lp : ℕ),
          lp ∈ Finset.range (s + 1) →
          K ω = n + 1 →
          pre ω =
            pref ++
              [lemma77TerminalHoldPoint q
                (relativeVerticalOvershoot s ell) lp] →
          pref ∈ lemma77HoldPrefixSignedEndpointLengthEvent origin n
            (lemma77HorizontalShift732 (r : ℤ) q) ((s - lp : ℕ) : ℤ) →
          q ∈ Q ∧ n ∈ N q lp ∧ pref ∈ P q lp n) :
    ∀ ω,
      ω ∈ relativeEndpointFiberEvent start K pre r ell →
        ω ∉ bad →
          ∃ q, q ∈ Q ∧ ∃ lp, lp ∈ Finset.range (s + 1) ∧
            ∃ n, n ∈ N q lp ∧ ∃ pref, pref ∈ P q lp n ∧
              K ω = n + 1 ∧
              pre ω =
                pref ++
                  [lemma77TerminalHoldPoint q
                    (relativeVerticalOvershoot s ell) lp] := by
  intro ω hω hnot_bad
  have hprev_nonneg :
      ∀ (n : ℕ) (pref : List TaoSection7RenewalPoint)
        (last : TaoSection7RenewalPoint),
        K ω = n + 1 →
        pre ω = pref ++ [last] →
        pref.length = n →
        0 ≤ lemma77HoldPrefixVerticalIncrement origin n pref := by
    intro n pref last hK hpre hlen
    by_contra hnot_nonneg
    exact hnot_bad
      (hbad_of_prev_neg ω hω n pref last hK hpre hlen
        (lt_of_not_ge hnot_nonneg))
  rcases
      relativeEndpointFiber_terminalCoordinates_of_firstPassage_prevNonneg
        (μ := μ) (start := start) (K := K) (pre := pre)
        (origin := origin) (s := s) (r := r) (ell := ell)
        hsrc hω (horigin ω hω hnot_bad) hprev_nonneg with
    ⟨n, pref, q, lp, hlp, hK, hpre, hpref⟩
  rcases himage ω hω hnot_bad n pref q lp hlp hK hpre hpref with
    ⟨hq, hn, hpref_image⟩
  exact ⟨q, hq, lp, hlp, n, hn, pref, hpref_image, hK, hpre⟩

/--
Build coherent finite `Q/N/P` images from a finite set of good samples with
chosen terminal-coordinate witnesses.

The filtered images preserve the same-sample link between `q`, `lp`, `n`, and
`pref`, which is the invariant required by the terminal split adapter.
-/
theorem lemma77EndpointFinitePrefixImageCover_of_goodSampleWitnesses
    {Ω : Type*} [Fintype Ω]
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {origin : TaoSection7RenewalPoint}
    {s r : ℕ} {ell : ℤ}
    (bad : Set Ω)
    (G : Finset Ω)
    (hG :
      ∀ ω,
        ω ∈ relativeEndpointFiberEvent start K pre r ell →
          ω ∉ bad → ω ∈ G)
    (w :
      ∀ x : {ω // ω ∈ G},
        Lemma77EndpointGoodSampleFinitePrefixWitness
          start K pre origin s r ell x.1) :
    ∃ Q : Finset ℕ,
      ∃ N : ℕ → ℕ → Finset ℕ,
        ∃ P : ℕ → ℕ → ℕ → Finset (List TaoSection7RenewalPoint),
          (∀ ω,
            ω ∈ relativeEndpointFiberEvent start K pre r ell →
              ω ∉ bad →
                ∃ q, q ∈ Q ∧ ∃ lp, lp ∈ Finset.range (s + 1) ∧
                  ∃ n, n ∈ N q lp ∧ ∃ pref, pref ∈ P q lp n ∧
                    K ω = n + 1 ∧
                    pre ω =
                      pref ++
                        [lemma77TerminalHoldPoint q
                          (relativeVerticalOvershoot s ell) lp]) ∧
          (∀ q, q ∈ Q → ∀ lp, lp ∈ Finset.range (s + 1) →
            ∀ n, n ∈ N q lp → ∀ pref, pref ∈ P q lp n →
              pref ∈ lemma77HoldPrefixSignedEndpointLengthEvent origin n
                (lemma77HorizontalShift732 (r : ℤ) q) ((s - lp : ℕ) : ℤ)) := by
  classical
  let Q : Finset ℕ := G.attach.image fun x => (w x).q
  let N : ℕ → ℕ → Finset ℕ := fun q lp =>
    (G.attach.filter fun x => (w x).q = q ∧ (w x).lp = lp).image
      fun x => (w x).n
  let P : ℕ → ℕ → ℕ → Finset (List TaoSection7RenewalPoint) :=
    fun q lp n =>
      (G.attach.filter fun x =>
        (w x).q = q ∧ (w x).lp = lp ∧ (w x).n = n).image
        fun x => (w x).pref
  refine ⟨Q, N, P, ?_, ?_⟩
  · intro ω hω hnot_bad
    let x : {ω // ω ∈ G} := ⟨ω, hG ω hω hnot_bad⟩
    let wx := w x
    have hx_attach : x ∈ G.attach := by
      simp [x]
    have hq : wx.q ∈ Q := by
      dsimp [Q, wx]
      exact Finset.mem_image.mpr ⟨x, hx_attach, rfl⟩
    have hxN :
        x ∈ G.attach.filter
          (fun y => (w y).q = wx.q ∧ (w y).lp = wx.lp) := by
      rw [Finset.mem_filter]
      exact ⟨hx_attach, rfl, rfl⟩
    have hn : wx.n ∈ N wx.q wx.lp := by
      dsimp [N, wx]
      exact Finset.mem_image.mpr ⟨x, hxN, rfl⟩
    have hxP :
        x ∈ G.attach.filter
          (fun y =>
            (w y).q = wx.q ∧ (w y).lp = wx.lp ∧ (w y).n = wx.n) := by
      rw [Finset.mem_filter]
      exact ⟨hx_attach, rfl, rfl, rfl⟩
    have hpref : wx.pref ∈ P wx.q wx.lp wx.n := by
      dsimp [P, wx]
      exact Finset.mem_image.mpr ⟨x, hxP, rfl⟩
    exact
      ⟨wx.q, hq, wx.lp, wx.lp_mem, wx.n, hn, wx.pref, hpref,
        wx.K_eq, wx.pre_eq⟩
  · intro q _hq lp _hlp n _hn pref hpref
    dsimp [P] at hpref
    rcases Finset.mem_image.mp hpref with ⟨x, hxP, hpref_eq⟩
    rw [Finset.mem_filter] at hxP
    rcases hxP with ⟨_hx_attach, hqeq, hlpeq, hneq⟩
    rw [← hpref_eq, ← hneq, ← hlpeq, ← hqeq]
    exact (w x).prefix_mem

/--
Finite source images for the residual good endpoint samples.

This specializes `lemma77EndpointFinitePrefixImageCover_of_goodSampleWitnesses`
to the actual finite set of endpoint-fiber samples outside the previous-negative
snoc residual.  The resulting `Q/N/P` data is built from same-sample terminal
coordinate witnesses, not supplied by an external image-membership oracle.
-/
theorem lemma77EndpointFinitePrefixImageCover_of_firstPassage_prevNegBad
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {origin : TaoSection7RenewalPoint}
    {s r : ℕ} {ell : ℤ}
    (hsrc : Lemma77EndpointSourceProvenance μ start K pre s)
    (horigin :
      ∀ ω, ω ∈ relativeEndpointFiberEvent start K pre r ell →
        ω ∉ lemma77EndpointPrevNegSnocBad origin K pre →
          start ω = origin) :
    ∃ Q : Finset ℕ,
      ∃ N : ℕ → ℕ → Finset ℕ,
        ∃ P : ℕ → ℕ → ℕ → Finset (List TaoSection7RenewalPoint),
          (∀ ω,
            ω ∈ relativeEndpointFiberEvent start K pre r ell →
              ω ∉ lemma77EndpointPrevNegSnocBad origin K pre →
                ∃ q, q ∈ Q ∧ ∃ lp, lp ∈ Finset.range (s + 1) ∧
                  ∃ n, n ∈ N q lp ∧ ∃ pref, pref ∈ P q lp n ∧
                    K ω = n + 1 ∧
                    pre ω =
                      pref ++
                        [lemma77TerminalHoldPoint q
                          (relativeVerticalOvershoot s ell) lp]) ∧
          (∀ q, q ∈ Q → ∀ lp, lp ∈ Finset.range (s + 1) →
            ∀ n, n ∈ N q lp → ∀ pref, pref ∈ P q lp n →
              pref ∈ lemma77HoldPrefixSignedEndpointLengthEvent origin n
                (lemma77HorizontalShift732 (r : ℤ) q) ((s - lp : ℕ) : ℤ)) := by
  classical
  let bad : Set Ω := lemma77EndpointPrevNegSnocBad origin K pre
  let G : Finset Ω := Finset.univ.filter fun ω =>
    ω ∈ relativeEndpointFiberEvent start K pre r ell ∧ ω ∉ bad
  have himage :=
    lemma77EndpointFinitePrefixImageCover_of_goodSampleWitnesses
      (start := start) (K := K) (pre := pre) (origin := origin)
      (s := s) (r := r) (ell := ell) (bad := bad) (G := G)
      (hG := by
        intro ω hω hnot_bad
        rw [Finset.mem_filter]
        exact ⟨Finset.mem_univ ω, hω, hnot_bad⟩)
      (w := by
        intro x
        have hxmem : x.1 ∈ G := x.2
        have hx :
            x.1 ∈ relativeEndpointFiberEvent start K pre r ell ∧
              x.1 ∉ bad := by
          rw [Finset.mem_filter] at hxmem
          exact hxmem.2
        exact
          lemma77EndpointGoodSampleFinitePrefixWitness_of_not_prevNegSnocBad
            (μ := μ) (start := start) (K := K) (pre := pre)
            (origin := origin) (s := s) (r := r) (ell := ell)
            hsrc hx.1 (horigin x.1 hx.1 (by simpa [bad] using hx.2))
            (by simpa [bad] using hx.2))
  simpa [bad] using himage

/--
Terminal-point specialization of the stopped-prefix snoc cylinder source
bound.

This is a singleton-cylinder source-law step toward
`endpoint_fiber_le_terminal_split`; it does not yet supply the first-passage
cover of an endpoint fiber by such cylinders.
-/
theorem lemma77EndpointSourceProvenance_terminalSnocCylinder_le
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {s n q lp : ℕ} {pref : List TaoSection7RenewalPoint}
    {overshoot : ℤ}
    (h :
      Lemma77EndpointSourceProvenance μ start K pre s)
    (hlen : pref.length = n) :
    pmfProb μ {ω | K ω = n + 1 ∧
        pre ω = pref ++ [lemma77TerminalHoldPoint q overshoot lp]} ≤
      (taoSection7HoldListPMF n pref).toReal *
        (taoSection7HoldPMF
          (lemma77TerminalHoldPoint q overshoot lp)).toReal :=
  lemma77EndpointSourceProvenance_snocCylinder_le
    (μ := μ) (start := start) (K := K) (pre := pre) (s := s)
    (n := n) (pref := pref)
    (last := lemma77TerminalHoldPoint q overshoot lp) h hlen

/--
Terminal-point specialization of the good-domain stopped-prefix snoc cylinder
source bound.
-/
theorem lemma77EndpointSourceProvenanceOnGood_terminalSnocCylinder_le
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {s n q lp : ℕ} {pref : List TaoSection7RenewalPoint}
    {overshoot : ℤ} {good : Set Ω}
    (h :
      Lemma77EndpointSourceProvenanceOnGood μ start K pre s good)
    (hlen : pref.length = n) :
    pmfProb μ {ω | ω ∈ good ∧ K ω = n + 1 ∧
        pre ω = pref ++ [lemma77TerminalHoldPoint q overshoot lp]} ≤
      (taoSection7HoldListPMF n pref).toReal *
        (taoSection7HoldPMF
          (lemma77TerminalHoldPoint q overshoot lp)).toReal :=
  lemma77EndpointSourceProvenanceOnGood_snocCylinder_le
    (μ := μ) (start := start) (K := K) (pre := pre) (s := s)
    (n := n) (pref := pref)
    (last := lemma77TerminalHoldPoint q overshoot lp) h hlen

/--
Snoc cylinders with negative previous prefix height have zero source
probability.

This isolates the residual support obstruction used by the endpoint-fiber
terminal-coordinate split: the source-law cylinder is dominated by the iid
`Hold` prefix mass, and that mass is zero when the prefix vertical height is
negative.
-/
theorem lemma77EndpointSourceProvenance_snocCylinder_prevNeg_prob_eq_zero
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {origin : TaoSection7RenewalPoint}
    {s n : ℕ} {pref : List TaoSection7RenewalPoint}
    {last : TaoSection7RenewalPoint}
    (hsrc : Lemma77EndpointSourceProvenance μ start K pre s)
    (hlen : pref.length = n)
    (hprev_neg :
      lemma77HoldPrefixVerticalIncrement origin n pref < 0) :
    pmfProb μ {ω | K ω = n + 1 ∧ pre ω = pref ++ [last]} = 0 := by
  have hpref_zero : (taoSection7HoldListPMF n pref).toReal = 0 := by
    by_contra hne
    have hnonneg :
        0 ≤ lemma77HoldPrefixVerticalIncrement origin n pref :=
      lemma77HoldPrefixVerticalIncrement_nonneg_of_holdListPMF_toReal_ne_zero
        origin hne n
    exact not_lt_of_ge hnonneg hprev_neg
  have hle :
      pmfProb μ {ω | K ω = n + 1 ∧ pre ω = pref ++ [last]} ≤ 0 := by
    simpa [hpref_zero] using
      lemma77EndpointSourceProvenance_snocCylinder_le
        (μ := μ) (start := start) (K := K) (pre := pre) (s := s)
        (n := n) (pref := pref) (last := last) hsrc hlen
  exact le_antisymm hle
    (pmfProb_nonneg μ {ω | K ω = n + 1 ∧ pre ω = pref ++ [last]})

/--
Finite bad-event cover by negative previous-height snoc cylinders has zero
source probability.

This is the finite-union lift of
`lemma77EndpointSourceProvenance_snocCylinder_prevNeg_prob_eq_zero`.  The
finite cover is supplied explicitly; producing it from endpoint-fiber samples is
a later source-image theorem.
-/
theorem lemma77EndpointSourceProvenance_prevNegFiniteBad_prob_eq_zero
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {origin : TaoSection7RenewalPoint}
    {s : ℕ}
    (hsrc : Lemma77EndpointSourceProvenance μ start K pre s)
    (bad : Set Ω)
    (B : Finset (Sigma fun _ : ℕ =>
      List TaoSection7RenewalPoint × TaoSection7RenewalPoint))
    (hcover :
      ∀ ω, ω ∈ bad →
        ∃ item, item ∈ B ∧
          K ω = item.1 + 1 ∧
          pre ω = item.2.1 ++ [item.2.2])
    (hlen :
      ∀ item, item ∈ B → item.2.1.length = item.1)
    (hprev_neg :
      ∀ item, item ∈ B →
        lemma77HoldPrefixVerticalIncrement origin item.1 item.2.1 < 0) :
    pmfProb μ bad = 0 := by
  classical
  let cylinder :
      (Sigma fun _ : ℕ =>
        List TaoSection7RenewalPoint × TaoSection7RenewalPoint) → Set Ω :=
    fun item => {ω | K ω = item.1 + 1 ∧
      pre ω = item.2.1 ++ [item.2.2]}
  have hbad_le :
      pmfProb μ bad ≤ B.sum fun item => pmfProb μ (cylinder item) :=
    TaoSection7Lemma710.pmfProb_le_finset_sum_of_subset_exists
      μ B cylinder bad (by
        intro ω hω
        rcases hcover ω hω with ⟨item, hitem, hK, hpre⟩
        exact ⟨item, hitem, hK, hpre⟩)
  have hsum_zero :
      B.sum (fun item => pmfProb μ (cylinder item)) = 0 := by
    apply Finset.sum_eq_zero
    intro item hitem
    simpa [cylinder] using
      lemma77EndpointSourceProvenance_snocCylinder_prevNeg_prob_eq_zero
        (μ := μ) (start := start) (K := K) (pre := pre) (s := s)
        (origin := origin) (n := item.1) (pref := item.2.1)
        (last := item.2.2) hsrc (hlen item hitem) (hprev_neg item hitem)
  have hle_zero : pmfProb μ bad ≤ 0 := by
    simpa [hsum_zero] using hbad_le
  exact le_antisymm hle_zero (pmfProb_nonneg μ bad)

/--
The actual previous-negative snoc residual has zero source probability.

The finite bad-cylinder cover is built from the finite subtype of bad samples
using one chosen negative snoc witness for each sample.
-/
theorem lemma77EndpointSourceProvenance_prevNegSnocBad_prob_eq_zero
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {origin : TaoSection7RenewalPoint}
    {s : ℕ}
    (hsrc : Lemma77EndpointSourceProvenance μ start K pre s) :
    pmfProb μ (lemma77EndpointPrevNegSnocBad origin K pre) = 0 := by
  classical
  let bad : Set Ω := lemma77EndpointPrevNegSnocBad origin K pre
  let w :
      (x : {ω // ω ∈ bad}) →
        Lemma77EndpointPrevNegSnocWitness origin K pre x.1 :=
    fun x =>
      lemma77EndpointPrevNegSnocWitness_of_mem
        (origin := origin) (K := K) (pre := pre)
        (ω := x.1) (by exact x.2)
  let itemOf :
      {ω // ω ∈ bad} →
        Sigma fun _ : ℕ =>
          List TaoSection7RenewalPoint × TaoSection7RenewalPoint :=
    fun x => ⟨(w x).n, ((w x).pref, (w x).last)⟩
  let B :
      Finset (Sigma fun _ : ℕ =>
        List TaoSection7RenewalPoint × TaoSection7RenewalPoint) :=
    Finset.univ.image itemOf
  have hzero :
      pmfProb μ bad = 0 :=
    lemma77EndpointSourceProvenance_prevNegFiniteBad_prob_eq_zero
      (μ := μ) (start := start) (K := K) (pre := pre)
      (origin := origin) (s := s) hsrc bad B
      (hcover := by
        intro ω hω
        let x : {ω // ω ∈ bad} := ⟨ω, hω⟩
        refine ⟨itemOf x, ?_, ?_, ?_⟩
        · exact Finset.mem_image.mpr ⟨x, Finset.mem_univ x, rfl⟩
        · dsimp [itemOf]
          exact (w x).K_eq
        · dsimp [itemOf]
          exact (w x).pre_eq)
      (hlen := by
        intro item hitem
        rcases Finset.mem_image.mp hitem with ⟨x, _hx, rfl⟩
        dsimp [itemOf]
        exact (w x).length_eq)
      (hprev_neg := by
        intro item hitem
        rcases Finset.mem_image.mp hitem with ⟨x, _hx, rfl⟩
        dsimp [itemOf]
        exact (w x).prev_neg)
  simpa [bad] using hzero

/--
Per-terminal source cell bound feeding the finite terminal-cover consumer.

The caller supplies the finite source image in `(n, pref)` coordinates for this
fixed terminal `(q, lp)` cell.  The proof uses the stopped-prefix snoc cylinder
bound and the length-restricted prefix endpoint atomization into
`lemma77HeightPotentialMass`.
-/
theorem lemma77EndpointTerminalCell_prob_le_heightPotential_of_finitePrefixImage
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {origin : TaoSection7RenewalPoint}
    {s r q lp : ℕ} {ell : ℤ}
    (hsrc : Lemma77EndpointSourceProvenance μ start K pre s)
    (event : Set Ω)
    (N : Finset ℕ)
    (P : ℕ → Finset (List TaoSection7RenewalPoint))
    (hcover :
      ∀ ω, ω ∈ event →
        ∃ n, n ∈ N ∧ ∃ pref, pref ∈ P n ∧
          K ω = n + 1 ∧
          pre ω =
            pref ++
              [lemma77TerminalHoldPoint q
                (relativeVerticalOvershoot s ell) lp])
    (hprefix :
      ∀ n, n ∈ N → ∀ pref, pref ∈ P n →
        pref ∈ lemma77HoldPrefixSignedEndpointLengthEvent origin n
          (lemma77HorizontalShift732 (r : ℤ) q) ((s - lp : ℕ) : ℤ))
    (hsummable :
      Summable fun n : ℕ =>
        lemma77HoldPrefixSignedEndpointMass origin n
          (lemma77HorizontalShift732 (r : ℤ) q) ((s - lp : ℕ) : ℤ)) :
    pmfProb μ event ≤
      (taoSection7HoldPMF
        (lemma77TerminalHoldPoint q
          (relativeVerticalOvershoot s ell) lp)).toReal *
      lemma77HeightPotentialMass origin
        (lemma77HorizontalShift732 (r : ℤ) q) (s - lp) := by
  classical
  let terminal :=
    lemma77TerminalHoldPoint q (relativeVerticalOvershoot s ell) lp
  let cellEvent : (Σ n : ℕ, List TaoSection7RenewalPoint) → Set Ω :=
    fun item => {ω | K ω = item.1 + 1 ∧ pre ω = item.2 ++ [terminal]}
  have hcover_cell :
      ∀ ω, ω ∈ event →
        ∃ item, item ∈ N.sigma P ∧ ω ∈ cellEvent item := by
    intro ω hω
    rcases hcover ω hω with ⟨n, hn, pref, hpref, hK, hpre⟩
    exact ⟨⟨n, pref⟩, Finset.mem_sigma.mpr ⟨hn, hpref⟩, hK, hpre⟩
  have hprob_le :
      pmfProb μ event ≤
        (N.sigma P).sum fun item => pmfProb μ (cellEvent item) :=
    TaoSection7Lemma710.pmfProb_le_finset_sum_of_subset_exists
      μ (N.sigma P) cellEvent event hcover_cell
  have hcell_le :
      (N.sigma P).sum (fun item => pmfProb μ (cellEvent item)) ≤
        (N.sigma P).sum fun item =>
          (taoSection7HoldListPMF item.1 item.2).toReal *
            (taoSection7HoldPMF terminal).toReal := by
    apply Finset.sum_le_sum
    intro item hitem
    exact lemma77EndpointSourceProvenance_terminalSnocCylinder_le
      (μ := μ) (start := start) (K := K) (pre := pre) (s := s)
      (n := item.1) (pref := item.2) (q := q) (lp := lp)
      (overshoot := relativeVerticalOvershoot s ell) hsrc
      ((hprefix item.1
        (Finset.mem_sigma.mp hitem).1 item.2
        (Finset.mem_sigma.mp hitem).2).2)
  have hprefix_sum_le :
      (∑ item ∈ N.sigma P,
        (taoSection7HoldListPMF item.1 item.2).toReal) ≤
        lemma77HeightPotentialMass origin
          (lemma77HorizontalShift732 (r : ℤ) q) (s - lp) :=
    lemma77HoldPrefixSignedEndpointMass_sigmaFinset_le_heightPotential
      origin (lemma77HorizontalShift732 (r : ℤ) q) (s - lp)
      N P hprefix hsummable
  have hterminal_nonneg : 0 ≤ (taoSection7HoldPMF terminal).toReal :=
    ENNReal.toReal_nonneg
  calc
    pmfProb μ event ≤
        (N.sigma P).sum fun item => pmfProb μ (cellEvent item) := hprob_le
    _ ≤ (N.sigma P).sum fun item =>
          (taoSection7HoldListPMF item.1 item.2).toReal *
            (taoSection7HoldPMF terminal).toReal := hcell_le
    _ = (∑ item ∈ N.sigma P,
          (taoSection7HoldListPMF item.1 item.2).toReal) *
          (taoSection7HoldPMF terminal).toReal := by
        rw [Finset.sum_mul]
    _ ≤ lemma77HeightPotentialMass origin
          (lemma77HorizontalShift732 (r : ℤ) q) (s - lp) *
          (taoSection7HoldPMF terminal).toReal :=
        mul_le_mul_of_nonneg_right hprefix_sum_le hterminal_nonneg
    _ = (taoSection7HoldPMF
          (lemma77TerminalHoldPoint q
            (relativeVerticalOvershoot s ell) lp)).toReal *
        lemma77HeightPotentialMass origin
          (lemma77HorizontalShift732 (r : ℤ) q) (s - lp) := by
        simp [terminal, mul_comm]

/--
Good-domain per-terminal source cell bound feeding the residual endpoint
consumer.

The event is required to lie in `good`; this is the point where the restricted
source law is applied.  Samples outside `good` must be paid by an outer
additive-bad hypothesis before reaching this theorem.
-/
theorem lemma77EndpointTerminalCell_prob_le_heightPotential_of_finitePrefixImage_onGood
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {origin : TaoSection7RenewalPoint}
    {s r q lp : ℕ} {ell : ℤ}
    {good : Set Ω}
    (hsrc : Lemma77EndpointSourceProvenanceOnGood μ start K pre s good)
    (event : Set Ω)
    (N : Finset ℕ)
    (P : ℕ → Finset (List TaoSection7RenewalPoint))
    (hevent_good : ∀ ω, ω ∈ event → ω ∈ good)
    (hcover :
      ∀ ω, ω ∈ event →
        ∃ n, n ∈ N ∧ ∃ pref, pref ∈ P n ∧
          K ω = n + 1 ∧
          pre ω =
            pref ++
              [lemma77TerminalHoldPoint q
                (relativeVerticalOvershoot s ell) lp])
    (hprefix :
      ∀ n, n ∈ N → ∀ pref, pref ∈ P n →
        pref ∈ lemma77HoldPrefixSignedEndpointLengthEvent origin n
          (lemma77HorizontalShift732 (r : ℤ) q) ((s - lp : ℕ) : ℤ))
    (hsummable :
      Summable fun n : ℕ =>
        lemma77HoldPrefixSignedEndpointMass origin n
          (lemma77HorizontalShift732 (r : ℤ) q) ((s - lp : ℕ) : ℤ)) :
    pmfProb μ event ≤
      (taoSection7HoldPMF
        (lemma77TerminalHoldPoint q
          (relativeVerticalOvershoot s ell) lp)).toReal *
      lemma77HeightPotentialMass origin
        (lemma77HorizontalShift732 (r : ℤ) q) (s - lp) := by
  classical
  let terminal :=
    lemma77TerminalHoldPoint q (relativeVerticalOvershoot s ell) lp
  let cellEvent : (Σ n : ℕ, List TaoSection7RenewalPoint) → Set Ω :=
    fun item => {ω | ω ∈ good ∧
      K ω = item.1 + 1 ∧ pre ω = item.2 ++ [terminal]}
  have hcover_cell :
      ∀ ω, ω ∈ event →
        ∃ item, item ∈ N.sigma P ∧ ω ∈ cellEvent item := by
    intro ω hω
    rcases hcover ω hω with ⟨n, hn, pref, hpref, hK, hpre⟩
    exact ⟨⟨n, pref⟩, Finset.mem_sigma.mpr ⟨hn, hpref⟩,
      hevent_good ω hω, hK, hpre⟩
  have hprob_le :
      pmfProb μ event ≤
        (N.sigma P).sum fun item => pmfProb μ (cellEvent item) :=
    TaoSection7Lemma710.pmfProb_le_finset_sum_of_subset_exists
      μ (N.sigma P) cellEvent event hcover_cell
  have hcell_le :
      (N.sigma P).sum (fun item => pmfProb μ (cellEvent item)) ≤
        (N.sigma P).sum fun item =>
          (taoSection7HoldListPMF item.1 item.2).toReal *
            (taoSection7HoldPMF terminal).toReal := by
    apply Finset.sum_le_sum
    intro item hitem
    exact lemma77EndpointSourceProvenanceOnGood_terminalSnocCylinder_le
      (μ := μ) (start := start) (K := K) (pre := pre) (s := s)
      (n := item.1) (pref := item.2) (q := q) (lp := lp)
      (overshoot := relativeVerticalOvershoot s ell) hsrc
      ((hprefix item.1
        (Finset.mem_sigma.mp hitem).1 item.2
        (Finset.mem_sigma.mp hitem).2).2)
  have hprefix_sum_le :
      (∑ item ∈ N.sigma P,
        (taoSection7HoldListPMF item.1 item.2).toReal) ≤
        lemma77HeightPotentialMass origin
          (lemma77HorizontalShift732 (r : ℤ) q) (s - lp) :=
    lemma77HoldPrefixSignedEndpointMass_sigmaFinset_le_heightPotential
      origin (lemma77HorizontalShift732 (r : ℤ) q) (s - lp)
      N P hprefix hsummable
  have hterminal_nonneg : 0 ≤ (taoSection7HoldPMF terminal).toReal :=
    ENNReal.toReal_nonneg
  calc
    pmfProb μ event ≤
        (N.sigma P).sum fun item => pmfProb μ (cellEvent item) := hprob_le
    _ ≤ (N.sigma P).sum fun item =>
          (taoSection7HoldListPMF item.1 item.2).toReal *
            (taoSection7HoldPMF terminal).toReal := hcell_le
    _ = (∑ item ∈ N.sigma P,
          (taoSection7HoldListPMF item.1 item.2).toReal) *
          (taoSection7HoldPMF terminal).toReal := by
        rw [Finset.sum_mul]
    _ ≤ lemma77HeightPotentialMass origin
          (lemma77HorizontalShift732 (r : ℤ) q) (s - lp) *
          (taoSection7HoldPMF terminal).toReal :=
        mul_le_mul_of_nonneg_right hprefix_sum_le hterminal_nonneg
    _ = (taoSection7HoldPMF
          (lemma77TerminalHoldPoint q
            (relativeVerticalOvershoot s ell) lp)).toReal *
        lemma77HeightPotentialMass origin
          (lemma77HorizontalShift732 (r : ℤ) q) (s - lp) := by
        simp [terminal, mul_comm]

/--
Local-limit version of the per-terminal source cell bound.

This removes the raw `n`-summability premise from the finite-prefix-image
terminal-cell producer by deriving it from the pointwise local-limit bound and
the scalar height-potential summability input.
-/
theorem
    lemma77EndpointTerminalCell_prob_le_heightPotential_of_finitePrefixImage_of_localLimit
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {origin : TaoSection7RenewalPoint}
    {s r q lp : ℕ} {ell : ℤ}
    {C c Csum csum : ℝ}
    (hlocal : HoldPrefixLocalLimit2DInput C c)
    (hscalar : Lemma77HeightPotentialScalarSummationInput C c Csum csum)
    (hsrc : Lemma77EndpointSourceProvenance μ start K pre s)
    (event : Set Ω)
    (N : Finset ℕ)
    (P : ℕ → Finset (List TaoSection7RenewalPoint))
    (hcover :
      ∀ ω, ω ∈ event →
        ∃ n, n ∈ N ∧ ∃ pref, pref ∈ P n ∧
          K ω = n + 1 ∧
          pre ω =
            pref ++
              [lemma77TerminalHoldPoint q
                (relativeVerticalOvershoot s ell) lp])
    (hprefix :
      ∀ n, n ∈ N → ∀ pref, pref ∈ P n →
        pref ∈ lemma77HoldPrefixSignedEndpointLengthEvent origin n
          (lemma77HorizontalShift732 (r : ℤ) q) ((s - lp : ℕ) : ℤ)) :
    pmfProb μ event ≤
      (taoSection7HoldPMF
        (lemma77TerminalHoldPoint q
          (relativeVerticalOvershoot s ell) lp)).toReal *
      lemma77HeightPotentialMass origin
        (lemma77HorizontalShift732 (r : ℤ) q) (s - lp) := by
  exact
    lemma77EndpointTerminalCell_prob_le_heightPotential_of_finitePrefixImage
      (μ := μ) (start := start) (K := K) (pre := pre) (s := s)
      (origin := origin) (r := r) (q := q) (lp := lp) (ell := ell)
      hsrc event N P hcover hprefix
      (lemma77HeightPotentialMass_summable_of_localLimit2DInput
        hlocal hscalar origin (lemma77HorizontalShift732 (r : ℤ) q) (s - lp))

/--
Local-limit version of the good-domain per-terminal source cell bound.
-/
theorem
    lemma77EndpointTerminalCell_prob_le_heightPotential_of_finitePrefixImage_onGood_of_localLimit
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {origin : TaoSection7RenewalPoint}
    {s r q lp : ℕ} {ell : ℤ}
    {C c Csum csum : ℝ}
    {good : Set Ω}
    (hlocal : HoldPrefixLocalLimit2DInput C c)
    (hscalar : Lemma77HeightPotentialScalarSummationInput C c Csum csum)
    (hsrc : Lemma77EndpointSourceProvenanceOnGood μ start K pre s good)
    (event : Set Ω)
    (N : Finset ℕ)
    (P : ℕ → Finset (List TaoSection7RenewalPoint))
    (hevent_good : ∀ ω, ω ∈ event → ω ∈ good)
    (hcover :
      ∀ ω, ω ∈ event →
        ∃ n, n ∈ N ∧ ∃ pref, pref ∈ P n ∧
          K ω = n + 1 ∧
          pre ω =
            pref ++
              [lemma77TerminalHoldPoint q
                (relativeVerticalOvershoot s ell) lp])
    (hprefix :
      ∀ n, n ∈ N → ∀ pref, pref ∈ P n →
        pref ∈ lemma77HoldPrefixSignedEndpointLengthEvent origin n
          (lemma77HorizontalShift732 (r : ℤ) q) ((s - lp : ℕ) : ℤ)) :
    pmfProb μ event ≤
      (taoSection7HoldPMF
        (lemma77TerminalHoldPoint q
          (relativeVerticalOvershoot s ell) lp)).toReal *
      lemma77HeightPotentialMass origin
        (lemma77HorizontalShift732 (r : ℤ) q) (s - lp) := by
  exact
    lemma77EndpointTerminalCell_prob_le_heightPotential_of_finitePrefixImage_onGood
      (μ := μ) (start := start) (K := K) (pre := pre) (s := s)
      (origin := origin) (r := r) (q := q) (lp := lp) (ell := ell)
      hsrc event N P hevent_good hcover hprefix
      (lemma77HeightPotentialMass_summable_of_localLimit2DInput
        hlocal hscalar origin (lemma77HorizontalShift732 (r : ℤ) q) (s - lp))

/--
Scalar exponent split behind the terminal atom comparison.

With nonnegative overshoot, weaker overshoot and leftover exponents give the
separated weight used by the endpoint assembly mass.
-/
theorem lemma77TerminalExponentCompatible_of_le
    {alpha beta gamma : ℝ}
    (hgamma : gamma ≤ alpha) (hbeta : beta ≤ alpha) :
    ∀ (q lp : ℕ) (overshoot : ℤ),
      0 ≤ overshoot →
        Real.exp
            (-alpha *
              ((((q + 1 : ℕ) : ℝ) +
                ((overshoot + (lp : ℤ) : ℤ) : ℝ)))) ≤
          Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
            Real.exp (-beta * (lp : ℝ)) *
              lemma77EndpointOvershootWeight gamma overshoot := by
  intro q lp overshoot hover
  rw [lemma77EndpointOvershootWeight]
  rw [← Real.exp_add, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have hlp_nonneg : (0 : ℝ) ≤ (lp : ℝ) := by
    exact_mod_cast Nat.zero_le lp
  have hover_real : (0 : ℝ) ≤ (overshoot : ℝ) := by
    exact_mod_cast hover
  have hmul_lp := mul_le_mul_of_nonneg_right hbeta hlp_nonneg
  have hmul_over := mul_le_mul_of_nonneg_right hgamma hover_real
  simp only [Int.cast_add, Int.cast_natCast]
  ring_nf
  nlinarith [hmul_lp, hmul_over]

/-- Convenience exponent split for the current Lemma 7.7 `gamma = alpha` route. -/
theorem lemma77TerminalExponentCompatible_of_gamma_eq_alpha
    {alpha beta gamma : ℝ}
    (hgamma : gamma = alpha) (hbeta : beta ≤ alpha) :
    ∀ (q lp : ℕ) (overshoot : ℤ),
      0 ≤ overshoot →
        Real.exp
            (-alpha *
              ((((q + 1 : ℕ) : ℝ) +
                ((overshoot + (lp : ℤ) : ℤ) : ℝ)))) ≤
          Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
            Real.exp (-beta * (lp : ℝ)) *
              lemma77EndpointOvershootWeight gamma overshoot := by
  subst gamma
  exact lemma77TerminalExponentCompatible_of_le le_rfl hbeta

/--
Pointwise terminal `Hold` atom bound after separating Tao's terminal
exponent into the horizontal, vertical-leftover, and overshoot weights used by
the `(7.32)`/`(7.33)` assembly surface.
-/
theorem lemma77TerminalHoldPointTailInput_le_separated
    {Ctail alpha beta gamma : ℝ}
    (htail : Lemma77TerminalHoldPointTailInput Ctail alpha)
    (hcompat :
      ∀ (q lp : ℕ) (overshoot : ℤ),
        0 ≤ overshoot →
          Real.exp
              (-alpha *
                ((((q + 1 : ℕ) : ℝ) +
                  ((overshoot + (lp : ℤ) : ℤ) : ℝ)))) ≤
            Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
              Real.exp (-beta * (lp : ℝ)) *
                lemma77EndpointOvershootWeight gamma overshoot)
    (q lp : ℕ) (overshoot : ℤ) (hover : 0 ≤ overshoot) :
    (taoSection7HoldPMF (lemma77TerminalHoldPoint q overshoot lp)).toReal ≤
      Ctail *
        (Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
          Real.exp (-beta * (lp : ℝ)) *
            lemma77EndpointOvershootWeight gamma overshoot) := by
  calc
    (taoSection7HoldPMF (lemma77TerminalHoldPoint q overshoot lp)).toReal ≤
        Ctail *
          Real.exp
            (-alpha *
              ((((q + 1 : ℕ) : ℝ) +
                ((overshoot + (lp : ℤ) : ℤ) : ℝ)))) := by
      simpa [lemma77TerminalHoldPoint] using
        htail.point_tail ⟨q + 1, Nat.succ_pos q⟩
          (overshoot + (lp : ℤ))
    _ ≤ Ctail *
        (Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
          Real.exp (-beta * (lp : ℝ)) *
            lemma77EndpointOvershootWeight gamma overshoot) :=
      mul_le_mul_of_nonneg_left (hcompat q lp overshoot hover)
        htail.constants.1

/--
Pointwise terminal `q`-atom bound used by the terminal split comparison.

This packages the finite `l'_k` smoothing step for one fixed horizontal terminal
coordinate `q`.
-/
theorem lemma77EndpointTerminalSplitAtom_le_scaled_of_tail
    {Ctail alpha beta gamma : ℝ}
    (htail : Lemma77TerminalHoldPointTailInput Ctail alpha)
    (hcompat :
      ∀ (q lp : ℕ) (overshoot : ℤ),
        0 ≤ overshoot →
          Real.exp
              (-alpha *
                ((((q + 1 : ℕ) : ℝ) +
                  ((overshoot + (lp : ℤ) : ℤ) : ℝ)))) ≤
            Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
              Real.exp (-beta * (lp : ℝ)) *
                lemma77EndpointOvershootWeight gamma overshoot)
    (origin : TaoSection7RenewalPoint) (r s : ℕ)
    (overshoot : ℤ) (hover : 0 ≤ overshoot) (q : ℕ) :
    (∑ lp ∈ Finset.range (s + 1),
      (taoSection7HoldPMF
        (lemma77TerminalHoldPoint q overshoot lp)).toReal *
        lemma77HeightPotentialMass origin
          (lemma77HorizontalShift732 (r : ℤ) q) (s - lp)) ≤
      Ctail * lemma77EndpointOvershootWeight gamma overshoot *
        (Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
          lemma77VerticalSmoothing733Mass beta origin
            (lemma77HorizontalShift732 (r : ℤ) q) s) := by
  have hfinite :
      (∑ lp ∈ Finset.range (s + 1),
        (taoSection7HoldPMF
          (lemma77TerminalHoldPoint q overshoot lp)).toReal *
          lemma77HeightPotentialMass origin
            (lemma77HorizontalShift732 (r : ℤ) q) (s - lp)) ≤
        ∑ lp ∈ Finset.range (s + 1),
          Ctail * lemma77EndpointOvershootWeight gamma overshoot *
            (Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
              (Real.exp (-beta * (lp : ℝ)) *
                lemma77HeightPotentialMass origin
                  (lemma77HorizontalShift732 (r : ℤ) q) (s - lp))) := by
    apply Finset.sum_le_sum
    intro lp _hlp
    have hterm :
        (taoSection7HoldPMF
          (lemma77TerminalHoldPoint q overshoot lp)).toReal ≤
          Ctail *
            (Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
              Real.exp (-beta * (lp : ℝ)) *
                lemma77EndpointOvershootWeight gamma overshoot) :=
      lemma77TerminalHoldPointTailInput_le_separated
        htail hcompat q lp overshoot hover
    have hmass_nonneg :
        0 ≤ lemma77HeightPotentialMass origin
          (lemma77HorizontalShift732 (r : ℤ) q) (s - lp) :=
      lemma77HeightPotentialMass_nonneg origin
        (lemma77HorizontalShift732 (r : ℤ) q) (s - lp)
    calc
      (taoSection7HoldPMF
          (lemma77TerminalHoldPoint q overshoot lp)).toReal *
          lemma77HeightPotentialMass origin
            (lemma77HorizontalShift732 (r : ℤ) q) (s - lp) ≤
        (Ctail *
            (Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
              Real.exp (-beta * (lp : ℝ)) *
                lemma77EndpointOvershootWeight gamma overshoot)) *
          lemma77HeightPotentialMass origin
            (lemma77HorizontalShift732 (r : ℤ) q) (s - lp) := by
          exact mul_le_mul_of_nonneg_right hterm hmass_nonneg
      _ =
        Ctail * lemma77EndpointOvershootWeight gamma overshoot *
            (Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
              (Real.exp (-beta * (lp : ℝ)) *
                lemma77HeightPotentialMass origin
                  (lemma77HorizontalShift732 (r : ℤ) q) (s - lp))) := by
          ring
  have hfinite_eval :
      (∑ lp ∈ Finset.range (s + 1),
          Ctail * lemma77EndpointOvershootWeight gamma overshoot *
            (Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
              (Real.exp (-beta * (lp : ℝ)) *
                lemma77HeightPotentialMass origin
                  (lemma77HorizontalShift732 (r : ℤ) q) (s - lp)))) =
        Ctail * lemma77EndpointOvershootWeight gamma overshoot *
          (Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
            lemma77VerticalSmoothing733Mass beta origin
              (lemma77HorizontalShift732 (r : ℤ) q) s) := by
    dsimp [lemma77VerticalSmoothing733Mass]
    calc
      (∑ lp ∈ Finset.range (s + 1),
          Ctail * lemma77EndpointOvershootWeight gamma overshoot *
            (Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
              (Real.exp (-beta * (lp : ℝ)) *
                lemma77HeightPotentialMass origin
                  (lemma77HorizontalShift732 (r : ℤ) q) (s - lp)))) =
          ∑ lp ∈ Finset.range (s + 1),
            (Ctail * lemma77EndpointOvershootWeight gamma overshoot *
                Real.exp (-alpha * (((q + 1 : ℕ) : ℝ)))) *
              (Real.exp (-beta * (lp : ℝ)) *
                lemma77HeightPotentialMass origin
                  (lemma77HorizontalShift732 (r : ℤ) q) (s - lp)) := by
        apply Finset.sum_congr rfl
        intro lp _hlp
        ring
      _ =
          (Ctail * lemma77EndpointOvershootWeight gamma overshoot *
              Real.exp (-alpha * (((q + 1 : ℕ) : ℝ)))) *
            (∑ lp ∈ Finset.range (s + 1),
              Real.exp (-beta * (lp : ℝ)) *
                lemma77HeightPotentialMass origin
                  (lemma77HorizontalShift732 (r : ℤ) q) (s - lp)) := by
        rw [Finset.mul_sum]
      _ =
          Ctail * lemma77EndpointOvershootWeight gamma overshoot *
            (Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
              (∑ lp ∈ Finset.range (s + 1),
                Real.exp (-beta * (lp : ℝ)) *
                  lemma77HeightPotentialMass origin
                    (lemma77HorizontalShift732 (r : ℤ) q) (s - lp))) := by
        ring
  exact le_trans hfinite (le_of_eq hfinite_eval)

/--
Outer terminal `q`-summability for the explicit terminal split, derived from
the terminal tail, finite smoothing, and horizontal convolution inputs.
-/
theorem lemma77EndpointTerminalSplitMass_summable_of_tail
    {C c beta C33 c33 alpha Ctail C32 c32 gamma : ℝ}
    (hheight : Lemma77HeightPotentialInput C c)
    (h733 : Lemma77VerticalSmoothing733Input C c beta C33 c33)
    (h732 : Lemma77HorizontalConvolution732Input alpha C33 c33 C32 c32)
    (htail : Lemma77TerminalHoldPointTailInput Ctail alpha)
    (hcompat :
      ∀ (q lp : ℕ) (overshoot : ℤ),
        0 ≤ overshoot →
          Real.exp
              (-alpha *
                ((((q + 1 : ℕ) : ℝ) +
                  ((overshoot + (lp : ℤ) : ℤ) : ℝ)))) ≤
            Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
              Real.exp (-beta * (lp : ℝ)) *
                lemma77EndpointOvershootWeight gamma overshoot)
    (origin : TaoSection7RenewalPoint) (r s : ℕ)
    (overshoot : ℤ) (hover : 0 ≤ overshoot) :
    Summable fun q : ℕ =>
      ∑ lp ∈ Finset.range (s + 1),
        (taoSection7HoldPMF
          (lemma77TerminalHoldPoint q overshoot lp)).toReal *
          lemma77HeightPotentialMass origin
            (lemma77HorizontalShift732 (r : ℤ) q) (s - lp) := by
  let atomMass : ℕ → ℝ := fun q =>
    ∑ lp ∈ Finset.range (s + 1),
      (taoSection7HoldPMF
        (lemma77TerminalHoldPoint q overshoot lp)).toReal *
        lemma77HeightPotentialMass origin
          (lemma77HorizontalShift732 (r : ℤ) q) (s - lp)
  let convTerm : ℕ → ℝ := fun q =>
    Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
      lemma77VerticalSmoothing733Mass beta origin
        (lemma77HorizontalShift732 (r : ℤ) q) s
  let scaledTerm : ℕ → ℝ := fun q =>
    Ctail * lemma77EndpointOvershootWeight gamma overshoot * convTerm q
  have hconv_summable : Summable convTerm := by
    simpa [convTerm] using
      lemma77HorizontalConvolution732Mass_summable_of_verticalSmoothing733Input
        hheight h733 h732 origin (r : ℤ) s
  have hscaled_summable : Summable scaledTerm := by
    simpa [scaledTerm, mul_assoc] using
      hconv_summable.mul_left
        (Ctail * lemma77EndpointOvershootWeight gamma overshoot)
  have hq_nonneg : ∀ q, 0 ≤ atomMass q := by
    intro q
    dsimp [atomMass]
    apply Finset.sum_nonneg
    intro lp _hlp
    exact mul_nonneg ENNReal.toReal_nonneg
      (lemma77HeightPotentialMass_nonneg origin
        (lemma77HorizontalShift732 (r : ℤ) q) (s - lp))
  have hq_le : ∀ q, atomMass q ≤ scaledTerm q := by
    intro q
    simpa [atomMass, scaledTerm, convTerm] using
      lemma77EndpointTerminalSplitAtom_le_scaled_of_tail
        htail hcompat origin r s overshoot hover q
  simpa [atomMass] using
    Summable.of_nonneg_of_le hq_nonneg hq_le hscaled_summable

/--
Finite terminal-cover consumer with terminal `q`-summability derived from the
analytic tail and convolution inputs.
-/
theorem event_prob_le_terminalSplitMass_of_finiteTerminalCover_of_tail
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {origin : TaoSection7RenewalPoint}
    {s r : ℕ} {overshoot : ℤ}
    {C c beta C33 c33 alpha Ctail C32 c32 gamma : ℝ}
    (hheight : Lemma77HeightPotentialInput C c)
    (h733 : Lemma77VerticalSmoothing733Input C c beta C33 c33)
    (h732 : Lemma77HorizontalConvolution732Input alpha C33 c33 C32 c32)
    (htail : Lemma77TerminalHoldPointTailInput Ctail alpha)
    (hcompat :
      ∀ (q lp : ℕ) (overshoot : ℤ),
        0 ≤ overshoot →
          Real.exp
              (-alpha *
                ((((q + 1 : ℕ) : ℝ) +
                  ((overshoot + (lp : ℤ) : ℤ) : ℝ)))) ≤
            Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
              Real.exp (-beta * (lp : ℝ)) *
                lemma77EndpointOvershootWeight gamma overshoot)
    (hover : 0 ≤ overshoot)
    (largeEvent : Set Ω)
    (Q : Finset ℕ)
    (event : ℕ → ℕ → Set Ω)
    (hcover :
      ∀ ω, ω ∈ largeEvent →
        ∃ q, q ∈ Q ∧ ∃ lp, lp ∈ Finset.range (s + 1) ∧
          ω ∈ event q lp)
    (hfiber :
      ∀ q, q ∈ Q → ∀ lp, lp ∈ Finset.range (s + 1) →
        pmfProb μ (event q lp) ≤
          (taoSection7HoldPMF
            (lemma77TerminalHoldPoint q overshoot lp)).toReal *
          lemma77HeightPotentialMass origin
            (lemma77HorizontalShift732 (r : ℤ) q) (s - lp)) :
    pmfProb μ largeEvent ≤
      lemma77EndpointTerminalSplitMass origin r s overshoot := by
  exact
    event_prob_le_terminalSplitMass_of_finiteTerminalCover
      (μ := μ) (origin := origin) (s := s) (r := r)
      (overshoot := overshoot) largeEvent Q event hcover hfiber
      (lemma77EndpointTerminalSplitMass_summable_of_tail
        hheight h733 h732 htail hcompat origin r s overshoot hover)

/--
Residual-bad finite terminal-cover consumer with outer terminal `q`
summability derived from the analytic tail and convolution inputs.
-/
theorem
    relativeEndpointFiber_prob_le_badProb_add_terminalSplitMass_of_residualFiniteTerminalCover_of_tail
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {origin : TaoSection7RenewalPoint}
    {s r : ℕ} {ell : ℤ}
    {C c beta C33 c33 alpha Ctail C32 c32 gamma : ℝ}
    (hheight : Lemma77HeightPotentialInput C c)
    (h733 : Lemma77VerticalSmoothing733Input C c beta C33 c33)
    (h732 : Lemma77HorizontalConvolution732Input alpha C33 c33 C32 c32)
    (htail : Lemma77TerminalHoldPointTailInput Ctail alpha)
    (hcompat :
      ∀ (q lp : ℕ) (overshoot : ℤ),
        0 ≤ overshoot →
          Real.exp
              (-alpha *
                ((((q + 1 : ℕ) : ℝ) +
                  ((overshoot + (lp : ℤ) : ℤ) : ℝ)))) ≤
            Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
              Real.exp (-beta * (lp : ℝ)) *
                lemma77EndpointOvershootWeight gamma overshoot)
    (hell : (s : ℤ) < ell)
    (bad : Set Ω)
    (Q : Finset ℕ)
    (event : ℕ → ℕ → Set Ω)
    (hcover :
      ∀ ω,
        ω ∈ relativeEndpointFiberEvent start K pre r ell →
          ω ∉ bad →
            ∃ q, q ∈ Q ∧ ∃ lp, lp ∈ Finset.range (s + 1) ∧
              ω ∈ event q lp)
    (hfiber :
      ∀ q, q ∈ Q → ∀ lp, lp ∈ Finset.range (s + 1) →
        pmfProb μ (event q lp) ≤
          (taoSection7HoldPMF
            (lemma77TerminalHoldPoint q
              (relativeVerticalOvershoot s ell) lp)).toReal *
          lemma77HeightPotentialMass origin
            (lemma77HorizontalShift732 (r : ℤ) q) (s - lp)) :
    pmfProb μ (relativeEndpointFiberEvent start K pre r ell) ≤
      pmfProb μ bad +
        lemma77EndpointTerminalSplitMass origin r s
          (relativeVerticalOvershoot s ell) := by
  exact
    relativeEndpointFiber_prob_le_badProb_add_terminalSplitMass_of_residualFiniteTerminalCover
      (μ := μ) (start := start) (K := K) (pre := pre)
      (origin := origin) (s := s) (r := r) (ell := ell)
      bad Q event hcover hfiber
      (lemma77EndpointTerminalSplitMass_summable_of_tail
        hheight h733 h732 htail hcompat origin r s
        (relativeVerticalOvershoot s ell)
        (le_of_lt (relativeVerticalOvershoot_pos_of_lt hell)))

/--
Zero-residual specialization of the tail-derived residual terminal-cover
consumer.
-/
theorem
    relativeEndpointFiber_prob_le_terminalSplitMass_of_residualFiniteTerminalCover_of_tail_bad_zero
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {origin : TaoSection7RenewalPoint}
    {s r : ℕ} {ell : ℤ}
    {C c beta C33 c33 alpha Ctail C32 c32 gamma : ℝ}
    (hheight : Lemma77HeightPotentialInput C c)
    (h733 : Lemma77VerticalSmoothing733Input C c beta C33 c33)
    (h732 : Lemma77HorizontalConvolution732Input alpha C33 c33 C32 c32)
    (htail : Lemma77TerminalHoldPointTailInput Ctail alpha)
    (hcompat :
      ∀ (q lp : ℕ) (overshoot : ℤ),
        0 ≤ overshoot →
          Real.exp
              (-alpha *
                ((((q + 1 : ℕ) : ℝ) +
                  ((overshoot + (lp : ℤ) : ℤ) : ℝ)))) ≤
            Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
              Real.exp (-beta * (lp : ℝ)) *
                lemma77EndpointOvershootWeight gamma overshoot)
    (hell : (s : ℤ) < ell)
    (bad : Set Ω)
    (Q : Finset ℕ)
    (event : ℕ → ℕ → Set Ω)
    (hcover :
      ∀ ω,
        ω ∈ relativeEndpointFiberEvent start K pre r ell →
          ω ∉ bad →
            ∃ q, q ∈ Q ∧ ∃ lp, lp ∈ Finset.range (s + 1) ∧
              ω ∈ event q lp)
    (hfiber :
      ∀ q, q ∈ Q → ∀ lp, lp ∈ Finset.range (s + 1) →
        pmfProb μ (event q lp) ≤
          (taoSection7HoldPMF
            (lemma77TerminalHoldPoint q
              (relativeVerticalOvershoot s ell) lp)).toReal *
          lemma77HeightPotentialMass origin
            (lemma77HorizontalShift732 (r : ℤ) q) (s - lp))
    (hbad_zero : pmfProb μ bad = 0) :
    pmfProb μ (relativeEndpointFiberEvent start K pre r ell) ≤
      lemma77EndpointTerminalSplitMass origin r s
        (relativeVerticalOvershoot s ell) := by
  have h :=
    relativeEndpointFiber_prob_le_badProb_add_terminalSplitMass_of_residualFiniteTerminalCover_of_tail
      (μ := μ) (start := start) (K := K) (pre := pre)
      (origin := origin) (s := s) (r := r) (ell := ell)
      hheight h733 h732 htail hcompat hell bad Q event hcover hfiber
  linarith

/--
Residual finite-cover adapter with per-terminal finite prefix images.

This combines the residual terminal-cover theorem, the local-limit
per-terminal finite-prefix-image mass bound, and the tail-derived outer
terminal `q` summability.  It still assumes the residual cover and the finite
`(n, pref)` images; producing those from source samples is a later theorem.
-/
theorem
    relativeEndpointFiber_prob_le_badProb_add_terminalSplitMass_of_residualFinitePrefixCover_of_localLimit_tail
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {origin : TaoSection7RenewalPoint}
    {s r : ℕ} {ell : ℤ}
    {Clocal clocal Csum csum Cheight cheight beta C33 c33 alpha Ctail C32 c32 gamma : ℝ}
    (hlocal : HoldPrefixLocalLimit2DInput Clocal clocal)
    (hscalar :
      Lemma77HeightPotentialScalarSummationInput Clocal clocal Csum csum)
    (hheight : Lemma77HeightPotentialInput Cheight cheight)
    (h733 : Lemma77VerticalSmoothing733Input Cheight cheight beta C33 c33)
    (h732 : Lemma77HorizontalConvolution732Input alpha C33 c33 C32 c32)
    (htail : Lemma77TerminalHoldPointTailInput Ctail alpha)
    (hcompat :
      ∀ (q lp : ℕ) (overshoot : ℤ),
        0 ≤ overshoot →
          Real.exp
              (-alpha *
                ((((q + 1 : ℕ) : ℝ) +
                  ((overshoot + (lp : ℤ) : ℤ) : ℝ)))) ≤
            Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
              Real.exp (-beta * (lp : ℝ)) *
                lemma77EndpointOvershootWeight gamma overshoot)
    (hsrc : Lemma77EndpointSourceProvenance μ start K pre s)
    (hell : (s : ℤ) < ell)
    (bad : Set Ω)
    (Q : Finset ℕ)
    (event : ℕ → ℕ → Set Ω)
    (N : ℕ → ℕ → Finset ℕ)
    (P : ℕ → ℕ → ℕ → Finset (List TaoSection7RenewalPoint))
    (hcover :
      ∀ ω,
        ω ∈ relativeEndpointFiberEvent start K pre r ell →
          ω ∉ bad →
            ∃ q, q ∈ Q ∧ ∃ lp, lp ∈ Finset.range (s + 1) ∧
              ω ∈ event q lp)
    (hcell_cover :
      ∀ q, q ∈ Q → ∀ lp, lp ∈ Finset.range (s + 1) →
        ∀ ω, ω ∈ event q lp →
          ∃ n, n ∈ N q lp ∧ ∃ pref, pref ∈ P q lp n ∧
            K ω = n + 1 ∧
            pre ω =
              pref ++
                [lemma77TerminalHoldPoint q
                  (relativeVerticalOvershoot s ell) lp])
    (hprefix :
      ∀ q, q ∈ Q → ∀ lp, lp ∈ Finset.range (s + 1) →
        ∀ n, n ∈ N q lp → ∀ pref, pref ∈ P q lp n →
          pref ∈ lemma77HoldPrefixSignedEndpointLengthEvent origin n
            (lemma77HorizontalShift732 (r : ℤ) q) ((s - lp : ℕ) : ℤ)) :
    pmfProb μ (relativeEndpointFiberEvent start K pre r ell) ≤
      pmfProb μ bad +
        lemma77EndpointTerminalSplitMass origin r s
          (relativeVerticalOvershoot s ell) := by
  refine
    relativeEndpointFiber_prob_le_badProb_add_terminalSplitMass_of_residualFiniteTerminalCover_of_tail
      (μ := μ) (start := start) (K := K) (pre := pre)
      (origin := origin) (s := s) (r := r) (ell := ell)
      hheight h733 h732 htail hcompat hell bad Q event hcover ?_
  intro q hq lp hlp
  exact
    lemma77EndpointTerminalCell_prob_le_heightPotential_of_finitePrefixImage_of_localLimit
      (μ := μ) (start := start) (K := K) (pre := pre) (s := s)
      (origin := origin) (r := r) (q := q) (lp := lp) (ell := ell)
      hlocal hscalar hsrc (event q lp) (N q lp) (P q lp)
      (hcell_cover q hq lp hlp)
      (hprefix q hq lp hlp)

/--
Zero-residual specialization of the finite-prefix-image residual cover adapter.
-/
theorem
    relativeEndpointFiber_prob_le_terminalSplitMass_of_residualFinitePrefixCover_of_localLimit_tail_bad_zero
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {origin : TaoSection7RenewalPoint}
    {s r : ℕ} {ell : ℤ}
    {Clocal clocal Csum csum Cheight cheight beta C33 c33 alpha Ctail C32 c32 gamma : ℝ}
    (hlocal : HoldPrefixLocalLimit2DInput Clocal clocal)
    (hscalar :
      Lemma77HeightPotentialScalarSummationInput Clocal clocal Csum csum)
    (hheight : Lemma77HeightPotentialInput Cheight cheight)
    (h733 : Lemma77VerticalSmoothing733Input Cheight cheight beta C33 c33)
    (h732 : Lemma77HorizontalConvolution732Input alpha C33 c33 C32 c32)
    (htail : Lemma77TerminalHoldPointTailInput Ctail alpha)
    (hcompat :
      ∀ (q lp : ℕ) (overshoot : ℤ),
        0 ≤ overshoot →
          Real.exp
              (-alpha *
                ((((q + 1 : ℕ) : ℝ) +
                  ((overshoot + (lp : ℤ) : ℤ) : ℝ)))) ≤
            Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
              Real.exp (-beta * (lp : ℝ)) *
                lemma77EndpointOvershootWeight gamma overshoot)
    (hsrc : Lemma77EndpointSourceProvenance μ start K pre s)
    (hell : (s : ℤ) < ell)
    (bad : Set Ω)
    (Q : Finset ℕ)
    (event : ℕ → ℕ → Set Ω)
    (N : ℕ → ℕ → Finset ℕ)
    (P : ℕ → ℕ → ℕ → Finset (List TaoSection7RenewalPoint))
    (hcover :
      ∀ ω,
        ω ∈ relativeEndpointFiberEvent start K pre r ell →
          ω ∉ bad →
            ∃ q, q ∈ Q ∧ ∃ lp, lp ∈ Finset.range (s + 1) ∧
              ω ∈ event q lp)
    (hcell_cover :
      ∀ q, q ∈ Q → ∀ lp, lp ∈ Finset.range (s + 1) →
        ∀ ω, ω ∈ event q lp →
          ∃ n, n ∈ N q lp ∧ ∃ pref, pref ∈ P q lp n ∧
            K ω = n + 1 ∧
            pre ω =
              pref ++
                [lemma77TerminalHoldPoint q
                  (relativeVerticalOvershoot s ell) lp])
    (hprefix :
      ∀ q, q ∈ Q → ∀ lp, lp ∈ Finset.range (s + 1) →
        ∀ n, n ∈ N q lp → ∀ pref, pref ∈ P q lp n →
          pref ∈ lemma77HoldPrefixSignedEndpointLengthEvent origin n
            (lemma77HorizontalShift732 (r : ℤ) q) ((s - lp : ℕ) : ℤ))
    (hbad_zero : pmfProb μ bad = 0) :
    pmfProb μ (relativeEndpointFiberEvent start K pre r ell) ≤
      lemma77EndpointTerminalSplitMass origin r s
        (relativeVerticalOvershoot s ell) := by
  have h :=
    relativeEndpointFiber_prob_le_badProb_add_terminalSplitMass_of_residualFinitePrefixCover_of_localLimit_tail
      (μ := μ) (start := start) (K := K) (pre := pre)
      (origin := origin) (s := s) (r := r) (ell := ell)
      hlocal hscalar hheight h733 h732 htail hcompat hsrc hell bad Q
      event N P hcover hcell_cover hprefix
  linarith

/--
Caller-facing residual finite-prefix-image cover adapter.

This version hides the intermediate terminal-cell event family: the caller
supplies a finite terminal coordinate set and finite `(n, pref)` images for
each terminal cell directly.
-/
theorem
    relativeEndpointFiber_prob_le_badProb_add_terminalSplitMass_of_residualFinitePrefixImageCover_of_localLimit_tail
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {origin : TaoSection7RenewalPoint}
    {s r : ℕ} {ell : ℤ}
    {Clocal clocal Csum csum Cheight cheight beta C33 c33 alpha Ctail C32 c32 gamma : ℝ}
    (hlocal : HoldPrefixLocalLimit2DInput Clocal clocal)
    (hscalar :
      Lemma77HeightPotentialScalarSummationInput Clocal clocal Csum csum)
    (hheight : Lemma77HeightPotentialInput Cheight cheight)
    (h733 : Lemma77VerticalSmoothing733Input Cheight cheight beta C33 c33)
    (h732 : Lemma77HorizontalConvolution732Input alpha C33 c33 C32 c32)
    (htail : Lemma77TerminalHoldPointTailInput Ctail alpha)
    (hcompat :
      ∀ (q lp : ℕ) (overshoot : ℤ),
        0 ≤ overshoot →
          Real.exp
              (-alpha *
                ((((q + 1 : ℕ) : ℝ) +
                  ((overshoot + (lp : ℤ) : ℤ) : ℝ)))) ≤
            Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
              Real.exp (-beta * (lp : ℝ)) *
                lemma77EndpointOvershootWeight gamma overshoot)
    (hsrc : Lemma77EndpointSourceProvenance μ start K pre s)
    (hell : (s : ℤ) < ell)
    (bad : Set Ω)
    (Q : Finset ℕ)
    (N : ℕ → ℕ → Finset ℕ)
    (P : ℕ → ℕ → ℕ → Finset (List TaoSection7RenewalPoint))
    (hcover :
      ∀ ω,
        ω ∈ relativeEndpointFiberEvent start K pre r ell →
          ω ∉ bad →
            ∃ q, q ∈ Q ∧ ∃ lp, lp ∈ Finset.range (s + 1) ∧
              ∃ n, n ∈ N q lp ∧ ∃ pref, pref ∈ P q lp n ∧
                K ω = n + 1 ∧
                pre ω =
                  pref ++
                    [lemma77TerminalHoldPoint q
                      (relativeVerticalOvershoot s ell) lp])
    (hprefix :
      ∀ q, q ∈ Q → ∀ lp, lp ∈ Finset.range (s + 1) →
        ∀ n, n ∈ N q lp → ∀ pref, pref ∈ P q lp n →
          pref ∈ lemma77HoldPrefixSignedEndpointLengthEvent origin n
            (lemma77HorizontalShift732 (r : ℤ) q) ((s - lp : ℕ) : ℤ)) :
    pmfProb μ (relativeEndpointFiberEvent start K pre r ell) ≤
      pmfProb μ bad +
        lemma77EndpointTerminalSplitMass origin r s
          (relativeVerticalOvershoot s ell) := by
  classical
  let event : ℕ → ℕ → Set Ω := fun q lp =>
    {ω |
      ∃ n, n ∈ N q lp ∧ ∃ pref, pref ∈ P q lp n ∧
        K ω = n + 1 ∧
        pre ω =
          pref ++
            [lemma77TerminalHoldPoint q
              (relativeVerticalOvershoot s ell) lp]}
  refine
    relativeEndpointFiber_prob_le_badProb_add_terminalSplitMass_of_residualFinitePrefixCover_of_localLimit_tail
      (μ := μ) (start := start) (K := K) (pre := pre)
      (origin := origin) (s := s) (r := r) (ell := ell)
      hlocal hscalar hheight h733 h732 htail hcompat hsrc hell
      bad Q event N P ?_ ?_ ?_
  · intro ω hω hnot_bad
    rcases hcover ω hω hnot_bad with
      ⟨q, hq, lp, hlp, n, hn, pref, hpref, hK, hpre⟩
    exact ⟨q, hq, lp, hlp, n, hn, pref, hpref, hK, hpre⟩
  · intro q _hq lp _hlp ω hω
    exact hω
  · exact hprefix

/--
Caller-facing residual finite-prefix-image cover adapter for a restricted
good-domain source law.

The caller covers endpoint-fiber samples outside `bad`; `hgood_of_not_bad`
then routes exactly those samples into `good`, where
`Lemma77EndpointSourceProvenanceOnGood` supplies the stopped-prefix source law.
The unrestricted complement is paid once by `pmfProb μ bad`.
-/
theorem
    relativeEndpointFiber_prob_le_badProb_add_terminalSplitMass_of_residualFinitePrefixImageCover_onGood_of_localLimit_tail
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {origin : TaoSection7RenewalPoint}
    {s r : ℕ} {ell : ℤ}
    {Clocal clocal Csum csum Cheight cheight beta C33 c33 alpha Ctail C32 c32 gamma : ℝ}
    {good : Set Ω}
    (hlocal : HoldPrefixLocalLimit2DInput Clocal clocal)
    (hscalar :
      Lemma77HeightPotentialScalarSummationInput Clocal clocal Csum csum)
    (hheight : Lemma77HeightPotentialInput Cheight cheight)
    (h733 : Lemma77VerticalSmoothing733Input Cheight cheight beta C33 c33)
    (h732 : Lemma77HorizontalConvolution732Input alpha C33 c33 C32 c32)
    (htail : Lemma77TerminalHoldPointTailInput Ctail alpha)
    (hcompat :
      ∀ (q lp : ℕ) (overshoot : ℤ),
        0 ≤ overshoot →
          Real.exp
              (-alpha *
                ((((q + 1 : ℕ) : ℝ) +
                  ((overshoot + (lp : ℤ) : ℤ) : ℝ)))) ≤
            Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
              Real.exp (-beta * (lp : ℝ)) *
                lemma77EndpointOvershootWeight gamma overshoot)
    (hsrc :
      Lemma77EndpointSourceProvenanceOnGood μ start K pre s good)
    (hell : (s : ℤ) < ell)
    (bad : Set Ω)
    (hgood_of_not_bad :
      ∀ ω,
        ω ∈ relativeEndpointFiberEvent start K pre r ell →
          ω ∉ bad →
            ω ∈ good)
    (Q : Finset ℕ)
    (N : ℕ → ℕ → Finset ℕ)
    (P : ℕ → ℕ → ℕ → Finset (List TaoSection7RenewalPoint))
    (hcover :
      ∀ ω,
        ω ∈ relativeEndpointFiberEvent start K pre r ell →
          ω ∉ bad →
            ∃ q, q ∈ Q ∧ ∃ lp, lp ∈ Finset.range (s + 1) ∧
              ∃ n, n ∈ N q lp ∧ ∃ pref, pref ∈ P q lp n ∧
                K ω = n + 1 ∧
                pre ω =
                  pref ++
                    [lemma77TerminalHoldPoint q
                      (relativeVerticalOvershoot s ell) lp])
    (hprefix :
      ∀ q, q ∈ Q → ∀ lp, lp ∈ Finset.range (s + 1) →
        ∀ n, n ∈ N q lp → ∀ pref, pref ∈ P q lp n →
          pref ∈ lemma77HoldPrefixSignedEndpointLengthEvent origin n
            (lemma77HorizontalShift732 (r : ℤ) q) ((s - lp : ℕ) : ℤ)) :
    pmfProb μ (relativeEndpointFiberEvent start K pre r ell) ≤
      pmfProb μ bad +
        lemma77EndpointTerminalSplitMass origin r s
          (relativeVerticalOvershoot s ell) := by
  classical
  let event : ℕ → ℕ → Set Ω := fun q lp =>
    {ω | ω ∈ good ∧
      ∃ n, n ∈ N q lp ∧ ∃ pref, pref ∈ P q lp n ∧
        K ω = n + 1 ∧
        pre ω =
          pref ++
            [lemma77TerminalHoldPoint q
              (relativeVerticalOvershoot s ell) lp]}
  refine
    relativeEndpointFiber_prob_le_badProb_add_terminalSplitMass_of_residualFiniteTerminalCover_of_tail
      (μ := μ) (start := start) (K := K) (pre := pre)
      (origin := origin) (s := s) (r := r) (ell := ell)
      hheight h733 h732 htail hcompat hell bad Q event ?_ ?_
  · intro ω hω hnot_bad
    rcases hcover ω hω hnot_bad with
      ⟨q, hq, lp, hlp, n, hn, pref, hpref, hK, hpre⟩
    exact ⟨q, hq, lp, hlp, hgood_of_not_bad ω hω hnot_bad,
      n, hn, pref, hpref, hK, hpre⟩
  · intro q hq lp hlp
    exact
      lemma77EndpointTerminalCell_prob_le_heightPotential_of_finitePrefixImage_onGood_of_localLimit
        (μ := μ) (start := start) (K := K) (pre := pre) (s := s)
        (origin := origin) (r := r) (q := q) (lp := lp) (ell := ell)
        hlocal hscalar hsrc (event q lp) (N q lp) (P q lp)
        (by
          intro ω hω
          exact hω.1)
        (by
          intro ω hω
          exact hω.2)
        (hprefix q hq lp hlp)

/--
Zero-bad specialization of the caller-facing finite-prefix-image cover adapter.
-/
theorem
    relativeEndpointFiber_prob_le_terminalSplitMass_of_residualFinitePrefixImageCover_of_localLimit_tail_bad_zero
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {origin : TaoSection7RenewalPoint}
    {s r : ℕ} {ell : ℤ}
    {Clocal clocal Csum csum Cheight cheight beta C33 c33 alpha Ctail C32 c32 gamma : ℝ}
    (hlocal : HoldPrefixLocalLimit2DInput Clocal clocal)
    (hscalar :
      Lemma77HeightPotentialScalarSummationInput Clocal clocal Csum csum)
    (hheight : Lemma77HeightPotentialInput Cheight cheight)
    (h733 : Lemma77VerticalSmoothing733Input Cheight cheight beta C33 c33)
    (h732 : Lemma77HorizontalConvolution732Input alpha C33 c33 C32 c32)
    (htail : Lemma77TerminalHoldPointTailInput Ctail alpha)
    (hcompat :
      ∀ (q lp : ℕ) (overshoot : ℤ),
        0 ≤ overshoot →
          Real.exp
              (-alpha *
                ((((q + 1 : ℕ) : ℝ) +
                  ((overshoot + (lp : ℤ) : ℤ) : ℝ)))) ≤
            Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
              Real.exp (-beta * (lp : ℝ)) *
                lemma77EndpointOvershootWeight gamma overshoot)
    (hsrc : Lemma77EndpointSourceProvenance μ start K pre s)
    (hell : (s : ℤ) < ell)
    (bad : Set Ω)
    (Q : Finset ℕ)
    (N : ℕ → ℕ → Finset ℕ)
    (P : ℕ → ℕ → ℕ → Finset (List TaoSection7RenewalPoint))
    (hcover :
      ∀ ω,
        ω ∈ relativeEndpointFiberEvent start K pre r ell →
          ω ∉ bad →
            ∃ q, q ∈ Q ∧ ∃ lp, lp ∈ Finset.range (s + 1) ∧
              ∃ n, n ∈ N q lp ∧ ∃ pref, pref ∈ P q lp n ∧
                K ω = n + 1 ∧
                pre ω =
                  pref ++
                    [lemma77TerminalHoldPoint q
                      (relativeVerticalOvershoot s ell) lp])
    (hprefix :
      ∀ q, q ∈ Q → ∀ lp, lp ∈ Finset.range (s + 1) →
        ∀ n, n ∈ N q lp → ∀ pref, pref ∈ P q lp n →
          pref ∈ lemma77HoldPrefixSignedEndpointLengthEvent origin n
            (lemma77HorizontalShift732 (r : ℤ) q) ((s - lp : ℕ) : ℤ))
    (hbad_zero : pmfProb μ bad = 0) :
    pmfProb μ (relativeEndpointFiberEvent start K pre r ell) ≤
      lemma77EndpointTerminalSplitMass origin r s
        (relativeVerticalOvershoot s ell) := by
  have h :=
    relativeEndpointFiber_prob_le_badProb_add_terminalSplitMass_of_residualFinitePrefixImageCover_of_localLimit_tail
      (μ := μ) (start := start) (K := K) (pre := pre)
      (origin := origin) (s := s) (r := r) (ell := ell)
      hlocal hscalar hheight h733 h732 htail hcompat hsrc hell bad Q N P
      hcover hprefix
  linarith

/--
Source-produced finite-image endpoint split into terminal mass.

This packages the previous-negative zero residual and the finite source images
of good endpoint samples before applying the local-limit/tail terminal split
adapter.  The remaining route-facing assumptions are the analytic local-limit
and tail inputs, positive overshoot, and origin alignment on the residual good
endpoint samples.
-/
theorem relativeEndpointFiber_prob_le_terminalSplitMass_of_sourceImages_prevNeg
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {origin : TaoSection7RenewalPoint}
    {s r : ℕ} {ell : ℤ}
    {Clocal clocal Csum csum Cheight cheight beta C33 c33 alpha Ctail C32 c32 gamma : ℝ}
    (hlocal : HoldPrefixLocalLimit2DInput Clocal clocal)
    (hscalar :
      Lemma77HeightPotentialScalarSummationInput Clocal clocal Csum csum)
    (hheight : Lemma77HeightPotentialInput Cheight cheight)
    (h733 : Lemma77VerticalSmoothing733Input Cheight cheight beta C33 c33)
    (h732 : Lemma77HorizontalConvolution732Input alpha C33 c33 C32 c32)
    (htail : Lemma77TerminalHoldPointTailInput Ctail alpha)
    (hcompat :
      ∀ (q lp : ℕ) (overshoot : ℤ),
        0 ≤ overshoot →
          Real.exp
              (-alpha *
                ((((q + 1 : ℕ) : ℝ) +
                  ((overshoot + (lp : ℤ) : ℤ) : ℝ)))) ≤
            Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
              Real.exp (-beta * (lp : ℝ)) *
                lemma77EndpointOvershootWeight gamma overshoot)
    (hsrc : Lemma77EndpointSourceProvenance μ start K pre s)
    (hell : (s : ℤ) < ell)
    (horigin :
      ∀ ω, ω ∈ relativeEndpointFiberEvent start K pre r ell →
        ω ∉ lemma77EndpointPrevNegSnocBad origin K pre →
          start ω = origin) :
    pmfProb μ (relativeEndpointFiberEvent start K pre r ell) ≤
      lemma77EndpointTerminalSplitMass origin r s
        (relativeVerticalOvershoot s ell) := by
  classical
  rcases
      lemma77EndpointFinitePrefixImageCover_of_firstPassage_prevNegBad
        (μ := μ) (start := start) (K := K) (pre := pre)
        (origin := origin) (s := s) (r := r) (ell := ell)
        hsrc horigin with
    ⟨Q, N, P, hcover, hprefix⟩
  exact
    relativeEndpointFiber_prob_le_terminalSplitMass_of_residualFinitePrefixImageCover_of_localLimit_tail_bad_zero
      (μ := μ) (start := start) (K := K) (pre := pre)
      (origin := origin) (s := s) (r := r) (ell := ell)
      hlocal hscalar hheight h733 h732 htail hcompat hsrc hell
      (lemma77EndpointPrevNegSnocBad origin K pre) Q N P hcover hprefix
      (lemma77EndpointSourceProvenance_prevNegSnocBad_prob_eq_zero
        (μ := μ) (start := start) (K := K) (pre := pre)
        (origin := origin) (s := s) hsrc)

/--
Analytic comparison from the explicit terminal split to the source-shaped
endpoint assembly mass.

This discharges the finite `l'_k` smoothing and horizontal `q`-convolution
once the terminal `Hold` point tail and exponent-compatibility inequality are
available.  It deliberately does not prove the first-passage/source-law bound
into `lemma77EndpointTerminalSplitMass`.
-/
theorem lemma77EndpointTerminalSplitMass_le_assembly_of_tail
    {C c beta C33 c33 alpha Ctail C32 c32 gamma : ℝ}
    (hheight : Lemma77HeightPotentialInput C c)
    (h733 : Lemma77VerticalSmoothing733Input C c beta C33 c33)
    (h732 : Lemma77HorizontalConvolution732Input alpha C33 c33 C32 c32)
    (htail : Lemma77TerminalHoldPointTailInput Ctail alpha)
    (hcompat :
      ∀ (q lp : ℕ) (overshoot : ℤ),
        0 ≤ overshoot →
          Real.exp
              (-alpha *
                ((((q + 1 : ℕ) : ℝ) +
                  ((overshoot + (lp : ℤ) : ℤ) : ℝ)))) ≤
            Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
              Real.exp (-beta * (lp : ℝ)) *
                lemma77EndpointOvershootWeight gamma overshoot)
    (origin : TaoSection7RenewalPoint) (r s : ℕ)
    (overshoot : ℤ) (hover : 0 ≤ overshoot) :
    lemma77EndpointTerminalSplitMass origin r s overshoot ≤
      Ctail * lemma77EndpointAssemblyMass alpha beta gamma origin
        (r : ℤ) s overshoot := by
  let atomMass : ℕ → ℝ := fun q =>
    ∑ lp ∈ Finset.range (s + 1),
      (taoSection7HoldPMF
        (lemma77TerminalHoldPoint q overshoot lp)).toReal *
        lemma77HeightPotentialMass origin
          (lemma77HorizontalShift732 (r : ℤ) q) (s - lp)
  let convTerm : ℕ → ℝ := fun q =>
    Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
      lemma77VerticalSmoothing733Mass beta origin
        (lemma77HorizontalShift732 (r : ℤ) q) s
  let scaledTerm : ℕ → ℝ := fun q =>
    Ctail * lemma77EndpointOvershootWeight gamma overshoot * convTerm q
  have hconv_summable : Summable convTerm := by
    simpa [convTerm] using
      lemma77HorizontalConvolution732Mass_summable_of_verticalSmoothing733Input
        hheight h733 h732 origin (r : ℤ) s
  have hscaled_summable : Summable scaledTerm := by
    simpa [scaledTerm, mul_assoc] using
      hconv_summable.mul_left
        (Ctail * lemma77EndpointOvershootWeight gamma overshoot)
  have hq_nonneg : ∀ q, 0 ≤ atomMass q := by
    intro q
    dsimp [atomMass]
    apply Finset.sum_nonneg
    intro lp _hlp
    exact mul_nonneg ENNReal.toReal_nonneg
      (lemma77HeightPotentialMass_nonneg origin
        (lemma77HorizontalShift732 (r : ℤ) q) (s - lp))
  have hq_le : ∀ q, atomMass q ≤ scaledTerm q := by
    intro q
    have hfinite :
        atomMass q ≤
          ∑ lp ∈ Finset.range (s + 1),
            Ctail * lemma77EndpointOvershootWeight gamma overshoot *
              (Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
                (Real.exp (-beta * (lp : ℝ)) *
                  lemma77HeightPotentialMass origin
                    (lemma77HorizontalShift732 (r : ℤ) q) (s - lp))) := by
      dsimp [atomMass]
      apply Finset.sum_le_sum
      intro lp _hlp
      have hterm :
          (taoSection7HoldPMF
            (lemma77TerminalHoldPoint q overshoot lp)).toReal ≤
            Ctail *
              (Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
                Real.exp (-beta * (lp : ℝ)) *
                  lemma77EndpointOvershootWeight gamma overshoot) :=
        lemma77TerminalHoldPointTailInput_le_separated
          htail hcompat q lp overshoot hover
      have hmass_nonneg :
          0 ≤ lemma77HeightPotentialMass origin
            (lemma77HorizontalShift732 (r : ℤ) q) (s - lp) :=
        lemma77HeightPotentialMass_nonneg origin
          (lemma77HorizontalShift732 (r : ℤ) q) (s - lp)
      calc
        (taoSection7HoldPMF
            (lemma77TerminalHoldPoint q overshoot lp)).toReal *
            lemma77HeightPotentialMass origin
              (lemma77HorizontalShift732 (r : ℤ) q) (s - lp) ≤
          (Ctail *
              (Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
                Real.exp (-beta * (lp : ℝ)) *
                  lemma77EndpointOvershootWeight gamma overshoot)) *
            lemma77HeightPotentialMass origin
              (lemma77HorizontalShift732 (r : ℤ) q) (s - lp) := by
            exact mul_le_mul_of_nonneg_right hterm hmass_nonneg
        _ =
          Ctail * lemma77EndpointOvershootWeight gamma overshoot *
              (Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
                (Real.exp (-beta * (lp : ℝ)) *
                  lemma77HeightPotentialMass origin
                    (lemma77HorizontalShift732 (r : ℤ) q) (s - lp))) := by
            ring
    have hfinite_eval :
        (∑ lp ∈ Finset.range (s + 1),
            Ctail * lemma77EndpointOvershootWeight gamma overshoot *
              (Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
                (Real.exp (-beta * (lp : ℝ)) *
                  lemma77HeightPotentialMass origin
                    (lemma77HorizontalShift732 (r : ℤ) q) (s - lp)))) =
          scaledTerm q := by
      dsimp [scaledTerm, convTerm, lemma77VerticalSmoothing733Mass]
      calc
        (∑ lp ∈ Finset.range (s + 1),
            Ctail * lemma77EndpointOvershootWeight gamma overshoot *
              (Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
                (Real.exp (-beta * (lp : ℝ)) *
                  lemma77HeightPotentialMass origin
                    (lemma77HorizontalShift732 (r : ℤ) q) (s - lp)))) =
            ∑ lp ∈ Finset.range (s + 1),
              (Ctail * lemma77EndpointOvershootWeight gamma overshoot *
                  Real.exp (-alpha * (((q + 1 : ℕ) : ℝ)))) *
                (Real.exp (-beta * (lp : ℝ)) *
                  lemma77HeightPotentialMass origin
                    (lemma77HorizontalShift732 (r : ℤ) q) (s - lp)) := by
          apply Finset.sum_congr rfl
          intro lp _hlp
          ring
        _ =
            (Ctail * lemma77EndpointOvershootWeight gamma overshoot *
                Real.exp (-alpha * (((q + 1 : ℕ) : ℝ)))) *
              (∑ lp ∈ Finset.range (s + 1),
                Real.exp (-beta * (lp : ℝ)) *
                  lemma77HeightPotentialMass origin
                    (lemma77HorizontalShift732 (r : ℤ) q) (s - lp)) := by
          rw [Finset.mul_sum]
        _ =
            Ctail * lemma77EndpointOvershootWeight gamma overshoot *
              (Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
                (∑ lp ∈ Finset.range (s + 1),
                  Real.exp (-beta * (lp : ℝ)) *
                    lemma77HeightPotentialMass origin
                      (lemma77HorizontalShift732 (r : ℤ) q) (s - lp))) := by
          ring
    exact le_trans hfinite (le_of_eq hfinite_eval)
  have hatom_summable : Summable atomMass :=
    Summable.of_nonneg_of_le hq_nonneg hq_le hscaled_summable
  unfold lemma77EndpointTerminalSplitMass lemma77EndpointAssemblyMass
    lemma77HorizontalConvolution732Mass
  calc
    (∑' q : ℕ,
      ∑ lp ∈ Finset.range (s + 1),
        (taoSection7HoldPMF
          (lemma77TerminalHoldPoint q overshoot lp)).toReal *
          lemma77HeightPotentialMass origin
            (lemma77HorizontalShift732 (r : ℤ) q) (s - lp)) =
        ∑' q : ℕ, atomMass q := by
      rfl
    _ ≤ ∑' q : ℕ, scaledTerm q :=
      hatom_summable.tsum_le_tsum hq_le hscaled_summable
    _ =
        Ctail * lemma77EndpointOvershootWeight gamma overshoot *
          (∑' q : ℕ, convTerm q) := by
      rw [tsum_mul_left]
    _ =
        Ctail *
          (lemma77EndpointOvershootWeight gamma overshoot *
            ∑' q : ℕ,
              Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
                lemma77VerticalSmoothing733Mass beta origin
                  (lemma77HorizontalShift732 (r : ℤ) q) s) := by
      simp [convTerm, mul_assoc]

/--
Split source/probability input below `Lemma77EndpointFiberToAssemblyMassInput`.

The first field is the first-passage/source-law/union-bound producer into the
explicit terminal split.  The second field is the analytic comparison from that
terminal split to the source-shaped assembly mass.
-/
structure Lemma77EndpointFiberTerminalSplitInput
    {Ω : Type*} [Fintype Ω]
    (μ : PMF Ω)
    (start : Ω → TaoSection7RenewalPoint)
    (K : Ω → ℕ)
    (pre : Ω → List TaoSection7RenewalPoint)
    (origin : TaoSection7RenewalPoint)
    (s : ℕ)
    (Ctail alpha beta gamma : ℝ) : Prop where
  source :
    Lemma77EndpointSourceProvenance μ start K pre s
  terminal_tail :
    Lemma77TerminalHoldPointTailInput Ctail alpha
  gamma_eq_alpha :
    gamma = alpha
  origin_alignment :
    ∀ ω, start ω = origin
  terminal_exponent_compatible :
    ∀ (q lp : ℕ) (overshoot : ℤ),
      0 ≤ overshoot →
        Real.exp
            (-alpha *
              ((((q + 1 : ℕ) : ℝ) +
                ((overshoot + (lp : ℤ) : ℤ) : ℝ)))) ≤
          Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
            Real.exp (-beta * (lp : ℝ)) *
              lemma77EndpointOvershootWeight gamma overshoot
  endpoint_fiber_le_terminal_split :
    ∀ (r : ℕ) (ell : ℤ),
      (s : ℤ) < ell →
        pmfProb μ (relativeEndpointFiberEvent start K pre r ell) ≤
          lemma77EndpointTerminalSplitMass origin r s
            (relativeVerticalOvershoot s ell)
  terminal_split_le_assembly :
    ∀ (r : ℕ) (ell : ℤ),
      (s : ℤ) < ell →
        lemma77EndpointTerminalSplitMass origin r s
            (relativeVerticalOvershoot s ell) ≤
          Ctail * lemma77EndpointAssemblyMass alpha beta gamma origin
            (r : ℤ) s (relativeVerticalOvershoot s ell)

/--
Constructor for the explicit terminal-split input when the source-law producer
has reached `lemma77EndpointTerminalSplitMass` and the analytic terminal-tail
comparison is supplied by `lemma77EndpointTerminalSplitMass_le_assembly_of_tail`.
-/
theorem lemma77EndpointFiberTerminalSplitInput_of_sourceAndTail
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {origin : TaoSection7RenewalPoint}
    {s : ℕ}
    {C c beta C33 c33 alpha Ctail C32 c32 gamma : ℝ}
    (hsource :
      Lemma77EndpointSourceProvenance μ start K pre s)
    (hheight : Lemma77HeightPotentialInput C c)
    (h733 : Lemma77VerticalSmoothing733Input C c beta C33 c33)
    (h732 : Lemma77HorizontalConvolution732Input alpha C33 c33 C32 c32)
    (htail : Lemma77TerminalHoldPointTailInput Ctail alpha)
    (hgamma : gamma = alpha)
    (horigin : ∀ ω, start ω = origin)
    (hcompat :
      ∀ (q lp : ℕ) (overshoot : ℤ),
        0 ≤ overshoot →
          Real.exp
              (-alpha *
                ((((q + 1 : ℕ) : ℝ) +
                  ((overshoot + (lp : ℤ) : ℤ) : ℝ)))) ≤
            Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
              Real.exp (-beta * (lp : ℝ)) *
                lemma77EndpointOvershootWeight gamma overshoot)
    (hendpoint :
      ∀ (r : ℕ) (ell : ℤ),
        (s : ℤ) < ell →
          pmfProb μ (relativeEndpointFiberEvent start K pre r ell) ≤
            lemma77EndpointTerminalSplitMass origin r s
              (relativeVerticalOvershoot s ell)) :
    Lemma77EndpointFiberTerminalSplitInput
      μ start K pre origin s Ctail alpha beta gamma where
  source := hsource
  terminal_tail := htail
  gamma_eq_alpha := hgamma
  origin_alignment := horigin
  terminal_exponent_compatible := hcompat
  endpoint_fiber_le_terminal_split := hendpoint
  terminal_split_le_assembly := by
    intro r ell hell
    exact lemma77EndpointTerminalSplitMass_le_assembly_of_tail
      hheight h733 h732 htail hcompat origin r s
      (relativeVerticalOvershoot s ell)
      (le_of_lt (relativeVerticalOvershoot_pos_of_lt hell))

/--
Terminal-split input constructor using the source-produced finite images and
previous-negative zero residual.

This removes the external fixed-fiber terminal-split premise from
`lemma77EndpointFiberTerminalSplitInput_of_sourceAndTail` by supplying it from
`relativeEndpointFiber_prob_le_terminalSplitMass_of_sourceImages_prevNeg`.
-/
theorem lemma77EndpointFiberTerminalSplitInput_of_sourceImages_prevNeg
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {origin : TaoSection7RenewalPoint}
    {s : ℕ}
    {Clocal clocal Csum csum Cheight cheight beta C33 c33 alpha Ctail C32 c32 gamma : ℝ}
    (hsource :
      Lemma77EndpointSourceProvenance μ start K pre s)
    (hlocal : HoldPrefixLocalLimit2DInput Clocal clocal)
    (hscalar :
      Lemma77HeightPotentialScalarSummationInput Clocal clocal Csum csum)
    (hheight : Lemma77HeightPotentialInput Cheight cheight)
    (h733 : Lemma77VerticalSmoothing733Input Cheight cheight beta C33 c33)
    (h732 : Lemma77HorizontalConvolution732Input alpha C33 c33 C32 c32)
    (htail : Lemma77TerminalHoldPointTailInput Ctail alpha)
    (hgamma : gamma = alpha)
    (horigin : ∀ ω, start ω = origin)
    (hcompat :
      ∀ (q lp : ℕ) (overshoot : ℤ),
        0 ≤ overshoot →
          Real.exp
              (-alpha *
                ((((q + 1 : ℕ) : ℝ) +
                  ((overshoot + (lp : ℤ) : ℤ) : ℝ)))) ≤
            Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
              Real.exp (-beta * (lp : ℝ)) *
                lemma77EndpointOvershootWeight gamma overshoot) :
    Lemma77EndpointFiberTerminalSplitInput
      μ start K pre origin s Ctail alpha beta gamma :=
  lemma77EndpointFiberTerminalSplitInput_of_sourceAndTail
    (μ := μ) (start := start) (K := K) (pre := pre)
    (origin := origin) (s := s)
    (C := Cheight) (c := cheight) (beta := beta) (C33 := C33)
    (c33 := c33) (alpha := alpha) (Ctail := Ctail) (C32 := C32)
    (c32 := c32) (gamma := gamma)
    hsource hheight h733 h732 htail hgamma horigin hcompat
    (fun r ell hell =>
      relativeEndpointFiber_prob_le_terminalSplitMass_of_sourceImages_prevNeg
        (μ := μ) (start := start) (K := K) (pre := pre)
        (origin := origin) (s := s) (r := r) (ell := ell)
        hlocal hscalar hheight h733 h732 htail hcompat hsource hell
        (fun ω _hω _hnot_bad => horigin ω))

/--
Source/probability input from a stopped first-passage endpoint fiber to the
post-`(7.32)` assembly mass.

The `endpoint_fiber_le_assembly` field is the remaining Tao source step:
first-passage minimality, union bound, terminal `Hold` independence and tail,
and the `0 ≤ l'_k ≤ s` support cutoff belong here.  It is an input, not
proved in this module.
-/
structure Lemma77EndpointFiberToAssemblyMassInput
    {Ω : Type*} [Fintype Ω]
    (μ : PMF Ω)
    (start : Ω → TaoSection7RenewalPoint)
    (K : Ω → ℕ)
    (pre : Ω → List TaoSection7RenewalPoint)
    (origin : TaoSection7RenewalPoint)
    (s : ℕ)
    (Ctail alpha beta gamma : ℝ) : Prop where
  source :
    Lemma77EndpointSourceProvenance μ start K pre s
  terminal_tail :
    Lemma77TerminalHoldPointTailInput Ctail alpha
  gamma_eq_alpha :
    gamma = alpha
  endpoint_fiber_le_assembly :
    ∀ (r : ℕ) (ell : ℤ),
      (s : ℤ) < ell →
        pmfProb μ (relativeEndpointFiberEvent start K pre r ell) ≤
          Ctail * lemma77EndpointAssemblyMass alpha beta gamma origin
            (r : ℤ) s (relativeVerticalOvershoot s ell)

/--
Checked projection from the explicit terminal-split bridge to the existing
endpoint-fiber-to-assembly input surface.
-/
theorem lemma77EndpointFiberToAssemblyMassInput_of_terminalSplit
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {origin : TaoSection7RenewalPoint}
    {s : ℕ}
    {Ctail alpha beta gamma : ℝ}
    (h :
      Lemma77EndpointFiberTerminalSplitInput
        μ start K pre origin s Ctail alpha beta gamma) :
    Lemma77EndpointFiberToAssemblyMassInput
      μ start K pre origin s Ctail alpha beta gamma where
  source := h.source
  terminal_tail := h.terminal_tail
  gamma_eq_alpha := h.gamma_eq_alpha
  endpoint_fiber_le_assembly := by
    intro r ell hell
    exact le_trans
      (h.endpoint_fiber_le_terminal_split r ell hell)
      (h.terminal_split_le_assembly r ell hell)

/--
Endpoint-fiber-to-assembly input from source-produced terminal split.

This composes the source-image/previous-negative terminal-split constructor
with the checked terminal-split-to-assembly projection.
-/
theorem lemma77EndpointFiberToAssemblyMassInput_of_sourceImages_prevNeg
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {origin : TaoSection7RenewalPoint}
    {s : ℕ}
    {Clocal clocal Csum csum Cheight cheight beta C33 c33 alpha Ctail C32 c32 gamma : ℝ}
    (hsource :
      Lemma77EndpointSourceProvenance μ start K pre s)
    (hlocal : HoldPrefixLocalLimit2DInput Clocal clocal)
    (hscalar :
      Lemma77HeightPotentialScalarSummationInput Clocal clocal Csum csum)
    (hheight : Lemma77HeightPotentialInput Cheight cheight)
    (h733 : Lemma77VerticalSmoothing733Input Cheight cheight beta C33 c33)
    (h732 : Lemma77HorizontalConvolution732Input alpha C33 c33 C32 c32)
    (htail : Lemma77TerminalHoldPointTailInput Ctail alpha)
    (hgamma : gamma = alpha)
    (horigin : ∀ ω, start ω = origin)
    (hcompat :
      ∀ (q lp : ℕ) (overshoot : ℤ),
        0 ≤ overshoot →
          Real.exp
              (-alpha *
                ((((q + 1 : ℕ) : ℝ) +
                  ((overshoot + (lp : ℤ) : ℤ) : ℝ)))) ≤
            Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
              Real.exp (-beta * (lp : ℝ)) *
                lemma77EndpointOvershootWeight gamma overshoot) :
    Lemma77EndpointFiberToAssemblyMassInput
      μ start K pre origin s Ctail alpha beta gamma :=
  lemma77EndpointFiberToAssemblyMassInput_of_terminalSplit
    (lemma77EndpointFiberTerminalSplitInput_of_sourceImages_prevNeg
      (μ := μ) (start := start) (K := K) (pre := pre)
      (origin := origin) (s := s)
      (Clocal := Clocal) (clocal := clocal) (Csum := Csum)
      (csum := csum) (Cheight := Cheight) (cheight := cheight)
      (beta := beta) (C33 := C33) (c33 := c33) (alpha := alpha)
      (Ctail := Ctail) (C32 := C32) (c32 := c32) (gamma := gamma)
      hsource hlocal hscalar hheight h733 h732 htail hgamma horigin hcompat)

/--
Scaled comparison from the source-probability assembly kernel to the existing
pointwise endpoint kernel.

The terminal-tail constant is kept visible rather than silently absorbed into
an endpoint-law premise.
-/
structure Lemma77ScaledEndpointAssemblyKernelComparisonInput
    (Ctail C32 c32 gamma A B Cpt D : ℝ) : Prop where
  constants_nonnegative : 0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ Cpt ∧ 0 ≤ D
  scaled_signed_kernel_le_pointwise :
    ∀ (s r : ℕ) (overshoot : ℤ),
      0 ≤ overshoot →
        Ctail * lemma77SignedPointwiseEndpointKernel C32 c32 gamma s
          (r : ℤ) overshoot ≤
          lemma77PointwiseEndpointKernel A B Cpt D s r overshoot

/--
Turn an unscaled comparison for the rescaled height-potential constant into the
constant-bearing comparison used after the terminal-tail factor is exposed.
-/
theorem lemma77ScaledEndpointAssemblyKernelComparisonInput_of_rescaled
    {Ctail C32 c32 gamma A B Cpt D : ℝ}
    (hcmp :
      Lemma77EndpointAssemblyKernelComparisonInput
        (Ctail * C32) c32 gamma A B Cpt D) :
    Lemma77ScaledEndpointAssemblyKernelComparisonInput
      Ctail C32 c32 gamma A B Cpt D where
  constants_nonnegative := hcmp.constants_nonnegative
  scaled_signed_kernel_le_pointwise := by
    intro s r overshoot hover
    calc
      Ctail * lemma77SignedPointwiseEndpointKernel C32 c32 gamma s
          (r : ℤ) overshoot =
        lemma77SignedPointwiseEndpointKernel (Ctail * C32) c32 gamma s
          (r : ℤ) overshoot := by
          unfold lemma77SignedPointwiseEndpointKernel
            lemma77HeightPotentialKernel
          ring
      _ ≤ lemma77PointwiseEndpointKernel A B Cpt D s r overshoot :=
        hcmp.signed_kernel_le_pointwise s r overshoot hover

/--
Natural kernel-shape comparison for the source-image endpoint route.

For the constants generated by the local-limit route, the scaled signed kernel
is exactly the existing pointwise endpoint kernel shape.
-/
theorem lemma77ScaledEndpointAssemblyKernelComparisonInput_natural
    {Ctail C32 c32 gamma : ℝ}
    (hCtail : 0 ≤ Ctail) (hC32 : 0 ≤ C32)
    (hc32 : 0 < c32) (hgamma : 0 ≤ gamma) :
    Lemma77ScaledEndpointAssemblyKernelComparisonInput
      Ctail C32 c32 gamma (c32 ^ 2) c32 (Ctail * C32) gamma where
  constants_nonnegative :=
    ⟨sq_nonneg c32, hc32.le, mul_nonneg hCtail hC32, hgamma⟩
  scaled_signed_kernel_le_pointwise := by
    intro s r overshoot _hover
    apply le_of_eq
    unfold lemma77SignedPointwiseEndpointKernel lemma77HeightPotentialKernel
      lemma77PointwiseEndpointKernel lemma77EndpointOvershootWeight
    simp [taoLemma22GaussianWeight, lemma77CenteredHorizontalDisplacement,
      abs_mul, abs_of_nonneg hc32.le]
    ring_nf

/--
Constant-bearing assembly inputs for the direct endpoint-to-assembly route.

This is the source-faithful variant of `Lemma77PointwiseEndpointAssemblyInputs`
when Tao's terminal-tail constant has not been normalized to one.
-/
structure Lemma77PointwiseEndpointAssemblyWithTailConstantInputs
    {Ω : Type*} [Fintype Ω]
    (μ : PMF Ω)
    (start : Ω → TaoSection7RenewalPoint)
    (K : Ω → ℕ)
    (pre : Ω → List TaoSection7RenewalPoint)
    (s : ℕ)
    (base : TaoSection7RenewalPoint)
    (M C0 c0 beta C33 c33 alpha C32 c32 gamma A B Cpt D : ℝ) : Prop where
  source :
    Lemma77EndpointSourceProvenance μ start K pre s
  tail_constant_nonneg :
    0 ≤ M
  height :
    Lemma77HeightPotentialInput C0 c0
  vertical_733 :
    Lemma77VerticalSmoothing733Input C0 c0 beta C33 c33
  horizontal_732 :
    Lemma77HorizontalConvolution732Input alpha C33 c33 C32 c32
  kernel_compare :
    Lemma77ScaledEndpointAssemblyKernelComparisonInput M C32 c32 gamma A B Cpt D
  endpoint_to_assembly_with_constant :
    ∀ (r : ℕ) (ell : ℤ),
      (s : ℤ) < ell →
        pmfProb μ (relativeEndpointFiberEvent start K pre r ell) ≤
          lemma77EndpointAssemblyMassWithConstant M alpha beta gamma base
            (r : ℤ) s (relativeVerticalOvershoot s ell)

/--
Checked constructor from the constant-bearing assembly route into the existing
pointwise endpoint-law input surface.
-/
theorem lemma77PointwiseEndpointLawInputs_of_assemblyWithTailConstant
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {s : ℕ}
    {base : TaoSection7RenewalPoint}
    {M C0 c0 beta C33 c33 alpha C32 c32 gamma A B Cpt D : ℝ}
    (h :
      Lemma77PointwiseEndpointAssemblyWithTailConstantInputs
        μ start K pre s base M C0 c0 beta C33 c33 alpha C32 c32 gamma A B Cpt D) :
    Lemma77PointwiseEndpointLawInputs μ start K pre s A B Cpt D where
  source := h.source
  constants_nonnegative := h.kernel_compare.constants_nonnegative
  pointwise_endpoint_bound := by
    intro r ell hell
    calc
      pmfProb μ (relativeEndpointFiberEvent start K pre r ell) ≤
          lemma77EndpointAssemblyMassWithConstant M alpha beta gamma base
            (r : ℤ) s (relativeVerticalOvershoot s ell) :=
        h.endpoint_to_assembly_with_constant r ell hell
      _ ≤ lemma77SignedPointwiseEndpointKernel (M * C32) c32 gamma s
            (r : ℤ) (relativeVerticalOvershoot s ell) :=
        lemma77EndpointAssemblyMassWithConstant_le_signedPointwiseKernel
          h.tail_constant_nonneg h.height h.vertical_733 h.horizontal_732
          base (r : ℤ) s (relativeVerticalOvershoot s ell)
      _ = M * lemma77SignedPointwiseEndpointKernel C32 c32 gamma s
            (r : ℤ) (relativeVerticalOvershoot s ell) := by
        unfold lemma77SignedPointwiseEndpointKernel lemma77HeightPotentialKernel
        ring
      _ ≤ lemma77PointwiseEndpointKernel A B Cpt D s r
            (relativeVerticalOvershoot s ell) :=
        h.kernel_compare.scaled_signed_kernel_le_pointwise s r
          (relativeVerticalOvershoot s ell)
          (le_of_lt (relativeVerticalOvershoot_pos_of_lt hell))

/--
Checked constructor from the source/probability bridge plus the analytic
convolution inputs into the existing pointwise endpoint-law input surface.
-/
theorem lemma77PointwiseEndpointLawInputs_of_endpointFiberToAssembly
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {origin : TaoSection7RenewalPoint}
    {s : ℕ}
    {C c beta C33 c33 alpha Ctail C32 c32 gamma A B Cpt D : ℝ}
    (hheight : Lemma77HeightPotentialInput C c)
    (h733 : Lemma77VerticalSmoothing733Input C c beta C33 c33)
    (h732 : Lemma77HorizontalConvolution732Input alpha C33 c33 C32 c32)
    (hsrc :
      Lemma77EndpointFiberToAssemblyMassInput
        μ start K pre origin s Ctail alpha beta gamma)
    (hcmp :
      Lemma77ScaledEndpointAssemblyKernelComparisonInput
        Ctail C32 c32 gamma A B Cpt D) :
    Lemma77PointwiseEndpointLawInputs μ start K pre s A B Cpt D where
  source := hsrc.source
  constants_nonnegative := hcmp.constants_nonnegative
  pointwise_endpoint_bound := by
    intro r ell hell
    calc
      pmfProb μ (relativeEndpointFiberEvent start K pre r ell) ≤
          Ctail * lemma77EndpointAssemblyMass alpha beta gamma origin
            (r : ℤ) s (relativeVerticalOvershoot s ell) :=
        hsrc.endpoint_fiber_le_assembly r ell hell
      _ ≤ Ctail * lemma77SignedPointwiseEndpointKernel C32 c32 gamma s
            (r : ℤ) (relativeVerticalOvershoot s ell) := by
        exact mul_le_mul_of_nonneg_left
          (lemma77EndpointAssemblyMass_le_signedPointwiseKernel
            hheight h733 h732 origin (r : ℤ) s
              (relativeVerticalOvershoot s ell))
          hsrc.terminal_tail.constants.1
      _ ≤ lemma77PointwiseEndpointKernel A B Cpt D s r
            (relativeVerticalOvershoot s ell) :=
        hcmp.scaled_signed_kernel_le_pointwise s r
          (relativeVerticalOvershoot s ell)
          (le_of_lt (relativeVerticalOvershoot_pos_of_lt hell))

/--
Pointwise endpoint-law input surface from the source-produced terminal split.

The endpoint source/image side is discharged by
`lemma77EndpointFiberToAssemblyMassInput_of_sourceImages_prevNeg`; the analytic
local-limit, terminal-tail, exponent-compatibility, and scaled kernel
comparison inputs remain explicit.
-/
theorem lemma77PointwiseEndpointLawInputs_of_sourceImages_prevNeg
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {origin : TaoSection7RenewalPoint}
    {s : ℕ}
    {Clocal clocal Csum csum Cheight cheight beta C33 c33 alpha Ctail C32 c32 gamma A B Cpt D : ℝ}
    (hsource :
      Lemma77EndpointSourceProvenance μ start K pre s)
    (hlocal : HoldPrefixLocalLimit2DInput Clocal clocal)
    (hscalar :
      Lemma77HeightPotentialScalarSummationInput Clocal clocal Csum csum)
    (hheight : Lemma77HeightPotentialInput Cheight cheight)
    (h733 : Lemma77VerticalSmoothing733Input Cheight cheight beta C33 c33)
    (h732 : Lemma77HorizontalConvolution732Input alpha C33 c33 C32 c32)
    (htail : Lemma77TerminalHoldPointTailInput Ctail alpha)
    (hgamma : gamma = alpha)
    (horigin : ∀ ω, start ω = origin)
    (hcompat :
      ∀ (q lp : ℕ) (overshoot : ℤ),
        0 ≤ overshoot →
          Real.exp
              (-alpha *
                ((((q + 1 : ℕ) : ℝ) +
                  ((overshoot + (lp : ℤ) : ℤ) : ℝ)))) ≤
            Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
              Real.exp (-beta * (lp : ℝ)) *
                lemma77EndpointOvershootWeight gamma overshoot)
    (hcmp :
      Lemma77ScaledEndpointAssemblyKernelComparisonInput
        Ctail C32 c32 gamma A B Cpt D) :
    Lemma77PointwiseEndpointLawInputs μ start K pre s A B Cpt D :=
  lemma77PointwiseEndpointLawInputs_of_endpointFiberToAssembly
    (μ := μ) (start := start) (K := K) (pre := pre)
    (origin := origin) (s := s)
    (C := Cheight) (c := cheight) (beta := beta) (C33 := C33)
    (c33 := c33) (alpha := alpha) (Ctail := Ctail) (C32 := C32)
    (c32 := c32) (gamma := gamma) (A := A) (B := B) (Cpt := Cpt)
    (D := D)
    hheight h733 h732
    (lemma77EndpointFiberToAssemblyMassInput_of_sourceImages_prevNeg
      (μ := μ) (start := start) (K := K) (pre := pre)
      (origin := origin) (s := s)
      (Clocal := Clocal) (clocal := clocal) (Csum := Csum)
      (csum := csum) (Cheight := Cheight) (cheight := cheight)
      (beta := beta) (C33 := C33) (c33 := c33) (alpha := alpha)
      (Ctail := Ctail) (C32 := C32) (c32 := c32) (gamma := gamma)
      hsource hlocal hscalar hheight h733 h732 htail hgamma horigin
      hcompat)
    hcmp

/--
Variant of `lemma77PointwiseEndpointLawInputs_of_sourceImages_prevNeg` using
the unscaled kernel-comparison input at the rescaled constant `Ctail * C32`.
-/
theorem lemma77PointwiseEndpointLawInputs_of_sourceImages_prevNeg_rescaledKernel
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {origin : TaoSection7RenewalPoint}
    {s : ℕ}
    {Clocal clocal Csum csum Cheight cheight beta C33 c33 alpha Ctail C32 c32 gamma A B Cpt D : ℝ}
    (hsource :
      Lemma77EndpointSourceProvenance μ start K pre s)
    (hlocal : HoldPrefixLocalLimit2DInput Clocal clocal)
    (hscalar :
      Lemma77HeightPotentialScalarSummationInput Clocal clocal Csum csum)
    (hheight : Lemma77HeightPotentialInput Cheight cheight)
    (h733 : Lemma77VerticalSmoothing733Input Cheight cheight beta C33 c33)
    (h732 : Lemma77HorizontalConvolution732Input alpha C33 c33 C32 c32)
    (htail : Lemma77TerminalHoldPointTailInput Ctail alpha)
    (hgamma : gamma = alpha)
    (horigin : ∀ ω, start ω = origin)
    (hcompat :
      ∀ (q lp : ℕ) (overshoot : ℤ),
        0 ≤ overshoot →
          Real.exp
              (-alpha *
                ((((q + 1 : ℕ) : ℝ) +
                  ((overshoot + (lp : ℤ) : ℤ) : ℝ)))) ≤
            Real.exp (-alpha * (((q + 1 : ℕ) : ℝ))) *
              Real.exp (-beta * (lp : ℝ)) *
                lemma77EndpointOvershootWeight gamma overshoot)
    (hcmp :
      Lemma77EndpointAssemblyKernelComparisonInput
        (Ctail * C32) c32 gamma A B Cpt D) :
    Lemma77PointwiseEndpointLawInputs μ start K pre s A B Cpt D :=
  lemma77PointwiseEndpointLawInputs_of_sourceImages_prevNeg
    (μ := μ) (start := start) (K := K) (pre := pre)
    (origin := origin) (s := s)
    (Clocal := Clocal) (clocal := clocal) (Csum := Csum)
    (csum := csum) (Cheight := Cheight) (cheight := cheight)
    (beta := beta) (C33 := C33) (c33 := c33) (alpha := alpha)
    (Ctail := Ctail) (C32 := C32) (c32 := c32) (gamma := gamma)
    (A := A) (B := B) (Cpt := Cpt) (D := D)
    hsource hlocal hscalar hheight h733 h732 htail hgamma horigin hcompat
    (lemma77ScaledEndpointAssemblyKernelComparisonInput_of_rescaled hcmp)

/--
Natural-constant variant of the source-image pointwise endpoint-law input
constructor.

This removes the explicit exponent-compatibility and scaled-kernel comparison
premises using `gamma = alpha`, `beta ≤ alpha`, and the constants already
carried by the terminal-tail and horizontal convolution inputs.
-/
theorem lemma77PointwiseEndpointLawInputs_of_sourceImages_prevNeg_naturalKernel
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {origin : TaoSection7RenewalPoint}
    {s : ℕ}
    {Clocal clocal Csum csum Cheight cheight beta C33 c33 alpha Ctail C32 c32 gamma : ℝ}
    (hsource :
      Lemma77EndpointSourceProvenance μ start K pre s)
    (hlocal : HoldPrefixLocalLimit2DInput Clocal clocal)
    (hscalar :
      Lemma77HeightPotentialScalarSummationInput Clocal clocal Csum csum)
    (hheight : Lemma77HeightPotentialInput Cheight cheight)
    (h733 : Lemma77VerticalSmoothing733Input Cheight cheight beta C33 c33)
    (h732 : Lemma77HorizontalConvolution732Input alpha C33 c33 C32 c32)
    (htail : Lemma77TerminalHoldPointTailInput Ctail alpha)
    (hgamma : gamma = alpha)
    (hbeta : beta ≤ alpha)
    (horigin : ∀ ω, start ω = origin) :
    Lemma77PointwiseEndpointLawInputs μ start K pre s
      (c32 ^ 2) c32 (Ctail * C32) gamma :=
  lemma77PointwiseEndpointLawInputs_of_sourceImages_prevNeg
    (μ := μ) (start := start) (K := K) (pre := pre)
    (origin := origin) (s := s)
    (Clocal := Clocal) (clocal := clocal) (Csum := Csum)
    (csum := csum) (Cheight := Cheight) (cheight := cheight)
    (beta := beta) (C33 := C33) (c33 := c33) (alpha := alpha)
    (Ctail := Ctail) (C32 := C32) (c32 := c32) (gamma := gamma)
    (A := c32 ^ 2) (B := c32) (Cpt := Ctail * C32) (D := gamma)
    hsource hlocal hscalar hheight h733 h732 htail hgamma horigin
    (lemma77TerminalExponentCompatible_of_gamma_eq_alpha hgamma hbeta)
    (lemma77ScaledEndpointAssemblyKernelComparisonInput_natural
      htail.constants.1 h732.constants.2.1 h732.constants.2.2
      (by rw [hgamma]; exact htail.constants.2.le))

/--
Natural-kernel source-image input constructor with the height-potential input
derived from the local-limit and scalar summation inputs.

This is a stop/go API gate for the scalar-summation route: the theorem has no
independent `Lemma77HeightPotentialInput` hypothesis, so constants must flow
from `HoldPrefixLocalLimit2DInput` through
`Lemma77HeightPotentialScalarSummationInput`.
-/
theorem lemma77PointwiseEndpointLawInputs_of_sourceImages_prevNeg_naturalKernel_fromLocalScalar
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {origin : TaoSection7RenewalPoint}
    {s : ℕ}
    {Clocal clocal Csum csum beta C33 c33 alpha Ctail C32 c32 gamma : ℝ}
    (hsource :
      Lemma77EndpointSourceProvenance μ start K pre s)
    (hlocal : HoldPrefixLocalLimit2DInput Clocal clocal)
    (hscalar :
      Lemma77HeightPotentialScalarSummationInput Clocal clocal Csum csum)
    (h733 : Lemma77VerticalSmoothing733Input Csum csum beta C33 c33)
    (h732 : Lemma77HorizontalConvolution732Input alpha C33 c33 C32 c32)
    (htail : Lemma77TerminalHoldPointTailInput Ctail alpha)
    (hgamma : gamma = alpha)
    (hbeta : beta ≤ alpha)
    (horigin : ∀ ω, start ω = origin) :
    Lemma77PointwiseEndpointLawInputs μ start K pre s
      (c32 ^ 2) c32 (Ctail * C32) gamma :=
  lemma77PointwiseEndpointLawInputs_of_sourceImages_prevNeg_naturalKernel
    (μ := μ) (start := start) (K := K) (pre := pre)
    (origin := origin) (s := s)
    (Clocal := Clocal) (clocal := clocal) (Csum := Csum)
    (csum := csum) (Cheight := Csum) (cheight := csum)
    (beta := beta) (C33 := C33) (c33 := c33) (alpha := alpha)
    (Ctail := Ctail) (C32 := C32) (c32 := c32) (gamma := gamma)
    hsource hlocal hscalar
    (lemma77HeightPotentialInput_of_localLimit2DInput hlocal hscalar)
    h733 h732 htail hgamma hbeta horigin

/--
Natural-kernel source-image input constructor with the `(7.33)` and `(7.32)`
analytic convolution inputs produced internally.

The remaining explicit assumptions are the local-limit/scalar input, terminal
tail, terminal exponent compatibility, source provenance, and origin
alignment.
-/
theorem
    lemma77PointwiseEndpointLawInputs_of_sourceImages_prevNeg_naturalKernel_fromLocalScalar_convolution
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {origin : TaoSection7RenewalPoint}
    {s : ℕ}
    {Clocal clocal Csum csum beta alpha Ctail gamma : ℝ}
    (hsource :
      Lemma77EndpointSourceProvenance μ start K pre s)
    (hlocal : HoldPrefixLocalLimit2DInput Clocal clocal)
    (hscalar :
      Lemma77HeightPotentialScalarSummationInput Clocal clocal Csum csum)
    (htail : Lemma77TerminalHoldPointTailInput Ctail alpha)
    (hgamma : gamma = alpha)
    (hbeta_pos : 0 < beta)
    (hbeta : beta ≤ alpha)
    (horigin : ∀ ω, start ω = origin) :
    ∃ C32 : ℝ, ∃ c32 : ℝ,
      Lemma77PointwiseEndpointLawInputs μ start K pre s
        (c32 ^ 2) c32 (Ctail * C32) gamma := by
  obtain ⟨C33, c33, h733⟩ :=
    lemma77VerticalSmoothing733Input_of_kernel_convolution
      hscalar.constants.1 hscalar.constants.2 hbeta_pos
  obtain ⟨C32, c32, h732⟩ :=
    lemma77HorizontalConvolution732Input_of_kernel_convolution
      htail.constants.2 h733.constants.2.1 h733.constants.2.2
  refine ⟨C32, c32, ?_⟩
  exact
    lemma77PointwiseEndpointLawInputs_of_sourceImages_prevNeg_naturalKernel_fromLocalScalar
      (μ := μ) (start := start) (K := K) (pre := pre)
      (origin := origin) (s := s)
      (Clocal := Clocal) (clocal := clocal) (Csum := Csum)
      (csum := csum) (beta := beta) (C33 := C33) (c33 := c33)
      (alpha := alpha) (Ctail := Ctail) (C32 := C32) (c32 := c32)
      (gamma := gamma)
      hsource hlocal hscalar h733 h732 htail hgamma hbeta horigin

/--
Natural-rate endpoint source-image constructor with `(7.33)`/`(7.32)`
convolution inputs produced internally.

This is the same route as
`lemma77PointwiseEndpointLawInputs_of_sourceImages_prevNeg_naturalKernel_fromLocalScalar_convolution`,
specialized to `beta = gamma = alpha`, so the endpoint caller does not need to
carry separate exponent-compatibility parameters.
-/
theorem
    lemma77PointwiseEndpointLawInputs_of_sourceImages_prevNeg_naturalKernel_fromLocalScalar_convolution_alpha
    {Ω : Type*} [Fintype Ω]
    {μ : PMF Ω}
    {start : Ω → TaoSection7RenewalPoint}
    {K : Ω → ℕ}
    {pre : Ω → List TaoSection7RenewalPoint}
    {origin : TaoSection7RenewalPoint}
    {s : ℕ}
    {Clocal clocal Csum csum alpha Ctail : ℝ}
    (hsource :
      Lemma77EndpointSourceProvenance μ start K pre s)
    (hlocal : HoldPrefixLocalLimit2DInput Clocal clocal)
    (hscalar :
      Lemma77HeightPotentialScalarSummationInput Clocal clocal Csum csum)
    (htail : Lemma77TerminalHoldPointTailInput Ctail alpha)
    (horigin : ∀ ω, start ω = origin) :
    ∃ C32 : ℝ, ∃ c32 : ℝ,
      Lemma77PointwiseEndpointLawInputs μ start K pre s
        (c32 ^ 2) c32 (Ctail * C32) alpha := by
  exact
    lemma77PointwiseEndpointLawInputs_of_sourceImages_prevNeg_naturalKernel_fromLocalScalar_convolution
      (μ := μ) (start := start) (K := K) (pre := pre)
      (origin := origin) (s := s)
      (Clocal := Clocal) (clocal := clocal) (Csum := Csum)
      (csum := csum) (beta := alpha) (alpha := alpha)
      (Ctail := Ctail) (gamma := alpha)
      hsource hlocal hscalar htail rfl htail.constants.2 le_rfl horigin

end TaoSection7Lemma77

end

end Tao
end Erdos1135SecondScale
