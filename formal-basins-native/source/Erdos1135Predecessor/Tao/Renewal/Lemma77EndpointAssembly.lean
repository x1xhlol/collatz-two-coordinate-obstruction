/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.Lemma77FirstPassageEndpoint
import Erdos1135Predecessor.Tao.Renewal.Lemma77LocalLimit

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

namespace TaoSection7Lemma77

def lemma77EndpointOvershootWeight (gamma : ℝ) (overshoot : ℤ) : ℝ :=
  Real.exp (-gamma * (overshoot : ℝ))

def lemma77EndpointAssemblyMass
    (alpha beta gamma : ℝ) (start : TaoSection7RenewalPoint)
    (j : ℤ) (s : ℕ) (overshoot : ℤ) : ℝ :=
  lemma77EndpointOvershootWeight gamma overshoot *
    lemma77HorizontalConvolution732Mass alpha beta start j s

def lemma77SignedPointwiseEndpointKernel
    (C c gamma : ℝ) (s : ℕ) (j overshoot : ℤ) : ℝ :=
  lemma77EndpointOvershootWeight gamma overshoot *
    lemma77HeightPotentialKernel C c j s

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

structure Lemma77TerminalHoldPointTailInput
    (Ctail alpha : ℝ) : Prop where
  constants : 0 ≤ Ctail ∧ 0 < alpha
  point_tail :
    ∀ (jk : ℕ+) (lk : ℤ),
      (taoSection7HoldPMF
        ({ j := jk, l := lk } : TaoSection7RenewalPoint)).toReal ≤
        Ctail * Real.exp
          (-alpha * (((jk : ℕ) : ℝ) + (lk : ℝ)))

def lemma77TerminalHoldExpWeight
    (alpha : ℝ) (h : TaoSection7RenewalPoint) : ℝ :=
  Real.exp (alpha * (((h.j : ℕ) : ℝ) + (h.l : ℝ)))

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

def lemma77TerminalHoldPoint
    (q : ℕ) (overshoot : ℤ) (lp : ℕ) : TaoSection7RenewalPoint :=
  { j := ⟨q + 1, Nat.succ_pos q⟩
    l := overshoot + (lp : ℤ) }

def lemma77EndpointTerminalSplitMass
    (origin : TaoSection7RenewalPoint) (r s : ℕ) (overshoot : ℤ) : ℝ :=
  ∑' q : ℕ,
    ∑ lp ∈ Finset.range (s + 1),
      (taoSection7HoldPMF
        (lemma77TerminalHoldPoint q overshoot lp)).toReal *
        lemma77HeightPotentialMass origin
          (lemma77HorizontalShift732 (r : ℤ) q) (s - lp)

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

structure Lemma77ScaledEndpointAssemblyKernelComparisonInput
    (Ctail C32 c32 gamma A B Cpt D : ℝ) : Prop where
  constants_nonnegative : 0 ≤ A ∧ 0 ≤ B ∧ 0 ≤ Cpt ∧ 0 ≤ D
  scaled_signed_kernel_le_pointwise :
    ∀ (s r : ℕ) (overshoot : ℤ),
      0 ≤ overshoot →
        Ctail * lemma77SignedPointwiseEndpointKernel C32 c32 gamma s
          (r : ℤ) overshoot ≤
          lemma77PointwiseEndpointKernel A B Cpt D s r overshoot

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

end TaoSection7Lemma77

end

end Tao

end Erdos1135Predecessor
