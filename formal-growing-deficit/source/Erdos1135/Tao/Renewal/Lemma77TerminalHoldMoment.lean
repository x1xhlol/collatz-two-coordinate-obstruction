import Erdos1135.Tao.Probability.HoldExpWeight
import Erdos1135.Tao.Renewal.Lemma77EndpointAssembly

/-!
# Lemma 7.7 Terminal Hold Moment Adapters

This module records the first algebraic adapters for the terminal `Hold` MGF
route.  It connects the endpoint-facing terminal exponential weight to the
probability-side pre-Hold exponential-weight algebra.

It proves the fixed-rate terminal `HoldPMF` exponential-moment and point-tail
input used by the endpoint sockets.  It does not prove full Lemma 7.6, Lemma
7.7, Proposition 7.8, or Tao's theorem.
-/

namespace Erdos1135
namespace Tao

namespace TaoSection7Lemma77

/--
On the concrete `Hold` point emitted by a source prefix, the terminal
endpoint-facing exponential weight is exactly the pre-Hold exponential weight.
-/
theorem lemma77TerminalHoldExpWeight_pointOfPrefix_eq_preHoldExpWeight
    (alpha : ℝ) (pre : List ℕ) :
    lemma77TerminalHoldExpWeight alpha
        (taoSection7HoldPointOfPrefix pre.length pre) =
      taoSection7PreHoldExpWeight alpha alpha pre := by
  unfold lemma77TerminalHoldExpWeight taoSection7PreHoldExpWeight
  simp [taoSection7HoldPointOfPrefix, taoSection7HoldTerminalSum]
  have hsum :
      (List.map (Int.cast ∘ Nat.cast) pre).sum =
        (List.map Nat.cast pre : List ℝ).sum := by
    induction pre with
    | nil => simp
    | cons b bs ih => simp [ih]
  rw [hsum]
  ring_nf

/--
Source path mass times the terminal `Hold` exponential weight factors into the
successful-hit prefactor and the Pascal-prime weighted path mass.
-/
theorem taoSection7PascalPrimeSourcePathMass_mul_terminalHoldExpWeight_pointOfPrefix_eq
    (alpha : ℝ) (pre : List ℕ) :
    taoSection7PascalPrimeSourcePathMass pre *
        lemma77TerminalHoldExpWeight alpha
          (taoSection7HoldPointOfPrefix pre.length pre) =
      Real.exp (4 * alpha) *
        taoSection7PascalPrimeWeightedPathMass alpha alpha pre := by
  rw [lemma77TerminalHoldExpWeight_pointOfPrefix_eq_preHoldExpWeight]
  exact
    taoSection7PascalPrimeSourcePathMass_mul_preHoldExpWeight_eq_exp_mul_weightedPathMass
      alpha pre

theorem taoSection7SourceListPMF_mul_terminalHoldExpWeight_eq_preHoldExpWeight
    (alpha : ℝ) (m : ℕ) (pre : List ℕ) :
    (taoSection7PascalPrimeSourceListPMF m pre).toReal *
        lemma77TerminalHoldExpWeight alpha
          (taoSection7HoldPointOfPrefix m pre) =
      (taoSection7PascalPrimeSourceListPMF m pre).toReal *
        taoSection7PreHoldExpWeight alpha alpha pre := by
  by_cases hlen : pre.length = m
  · have hm : m = pre.length := hlen.symm
    subst hm
    rw [lemma77TerminalHoldExpWeight_pointOfPrefix_eq_preHoldExpWeight]
  · have hpmf :
        (taoSection7PascalPrimeSourceListPMF m pre).toReal = 0 := by
      rw [taoSection7PascalPrimeSourceListPMF_apply_eq_zero_of_length_ne
        m pre hlen]
      simp
    simp [hpmf]

theorem tsum_taoSection7SourceListPMF_terminalHoldExpWeight_eq_exp_mul_stepMoment_pow
    {alpha : ℝ}
    (hs : Summable fun b : ℕ =>
      taoSection7PascalPrimeSourceMass b *
        taoSection7PascalPrimeStepExpWeight alpha alpha b)
    (m : ℕ) :
    (∑' pre : List ℕ,
      (taoSection7PascalPrimeSourceListPMF m pre).toReal *
        lemma77TerminalHoldExpWeight alpha
          (taoSection7HoldPointOfPrefix m pre)) =
      Real.exp (4 * alpha) *
        (taoSection7PascalPrimeStepMoment alpha) ^ m := by
  calc
    (∑' pre : List ℕ,
      (taoSection7PascalPrimeSourceListPMF m pre).toReal *
        lemma77TerminalHoldExpWeight alpha
          (taoSection7HoldPointOfPrefix m pre))
        =
      ∑' pre : List ℕ,
        (taoSection7PascalPrimeSourceListPMF m pre).toReal *
          taoSection7PreHoldExpWeight alpha alpha pre := by
          apply tsum_congr
          intro pre
          exact
            taoSection7SourceListPMF_mul_terminalHoldExpWeight_eq_preHoldExpWeight
              alpha m pre
    _ =
      Real.exp (4 * alpha) *
        (taoSection7PascalPrimeStepMoment alpha) ^ m := by
          exact
            tsum_taoSection7PascalPrimeSourceListPMF_preHoldExpWeight_eq_exp_mul_stepMoment_pow
              hs m

theorem taoSection7SourceListPMF_mul_preHoldExpWeight_eq_exp_weightedPathMass
    (alpha : ℝ) (m : ℕ) (pre : List ℕ) :
    (taoSection7PascalPrimeSourceListPMF m pre).toReal *
        taoSection7PreHoldExpWeight alpha alpha pre =
      if pre.length = m then
        Real.exp (4 * alpha) *
          taoSection7PascalPrimeWeightedPathMass alpha alpha pre
      else 0 := by
  by_cases hlen : pre.length = m
  · have hpmf :
        (taoSection7PascalPrimeSourceListPMF m pre).toReal =
          taoSection7PascalPrimeSourcePathMass pre := by
      rw [← hlen]
      exact
        taoSection7PascalPrimeSourceListPMF_apply_length_toReal_eq_sourcePathMass
          pre
    rw [ite_eq_left hlen, hpmf]
    exact
      taoSection7PascalPrimeSourcePathMass_mul_preHoldExpWeight_eq_exp_mul_weightedPathMass
        alpha pre
  · have hpmf :
        (taoSection7PascalPrimeSourceListPMF m pre).toReal = 0 := by
      rw [taoSection7PascalPrimeSourceListPMF_apply_eq_zero_of_length_ne
        m pre hlen]
      simp
    simp [hlen, hpmf]

theorem summable_taoSection7SourceListPMF_terminalHoldExpWeight
    {alpha : ℝ}
    (hs : Summable fun b : ℕ =>
      taoSection7PascalPrimeSourceMass b *
        taoSection7PascalPrimeStepExpWeight alpha alpha b)
    (m : ℕ) :
    Summable fun pre : List ℕ =>
      (taoSection7PascalPrimeSourceListPMF m pre).toReal *
        lemma77TerminalHoldExpWeight alpha
          (taoSection7HoldPointOfPrefix m pre) := by
  have hweighted := summable_taoSection7PascalPrimeWeightedPathMass_length hs m
  have hscaled : Summable fun pre : List ℕ =>
      Real.exp (4 * alpha) *
        (if pre.length = m then
          taoSection7PascalPrimeWeightedPathMass alpha alpha pre
        else 0) :=
    hweighted.mul_left (Real.exp (4 * alpha))
  refine hscaled.congr ?_
  intro pre
  by_cases hlen : pre.length = m
  · rw [taoSection7SourceListPMF_mul_terminalHoldExpWeight_eq_preHoldExpWeight]
    rw [taoSection7SourceListPMF_mul_preHoldExpWeight_eq_exp_weightedPathMass]
    simp [hlen]
  · rw [taoSection7SourceListPMF_mul_terminalHoldExpWeight_eq_preHoldExpWeight]
    rw [taoSection7SourceListPMF_mul_preHoldExpWeight_eq_exp_weightedPathMass]
    simp [hlen]

theorem taoSection7HoldSourcePrefixPMF_mul_terminalHoldExpWeight_eq
    (alpha : ℝ) (m : ℕ) (pre : List ℕ) :
    (taoSection7HoldSourcePrefixPMF (m, pre)).toReal *
        lemma77TerminalHoldExpWeight alpha
          (taoSection7HoldPointOfPrefix m pre) =
      taoSection7Geom4MissMass m *
        ((taoSection7PascalPrimeSourceListPMF m pre).toReal *
          taoSection7PreHoldExpWeight alpha alpha pre) := by
  calc
    (taoSection7HoldSourcePrefixPMF (m, pre)).toReal *
        lemma77TerminalHoldExpWeight alpha
          (taoSection7HoldPointOfPrefix m pre)
        =
      taoSection7Geom4MissMass m *
        ((taoSection7PascalPrimeSourceListPMF m pre).toReal *
          lemma77TerminalHoldExpWeight alpha
            (taoSection7HoldPointOfPrefix m pre)) := by
          rw [taoSection7HoldSourcePrefixPMF_apply_toReal]
          ring
    _ =
      taoSection7Geom4MissMass m *
        ((taoSection7PascalPrimeSourceListPMF m pre).toReal *
          taoSection7PreHoldExpWeight alpha alpha pre) := by
          rw [taoSection7SourceListPMF_mul_terminalHoldExpWeight_eq_preHoldExpWeight]

theorem summable_taoSection7HoldSourcePrefixPMF_terminalHoldExpWeight_row
    {alpha : ℝ}
    (hs : Summable fun b : ℕ =>
      taoSection7PascalPrimeSourceMass b *
        taoSection7PascalPrimeStepExpWeight alpha alpha b)
    (m : ℕ) :
    Summable fun pre : List ℕ =>
      (taoSection7HoldSourcePrefixPMF (m, pre)).toReal *
        lemma77TerminalHoldExpWeight alpha
          (taoSection7HoldPointOfPrefix m pre) := by
  have hrow := summable_taoSection7SourceListPMF_terminalHoldExpWeight hs m
  have hscaled : Summable fun pre : List ℕ =>
      taoSection7Geom4MissMass m *
        ((taoSection7PascalPrimeSourceListPMF m pre).toReal *
          lemma77TerminalHoldExpWeight alpha
            (taoSection7HoldPointOfPrefix m pre)) :=
    hrow.mul_left (taoSection7Geom4MissMass m)
  refine hscaled.congr ?_
  intro pre
  calc
    taoSection7Geom4MissMass m *
        ((taoSection7PascalPrimeSourceListPMF m pre).toReal *
          lemma77TerminalHoldExpWeight alpha
            (taoSection7HoldPointOfPrefix m pre))
        = (taoSection7HoldSourcePrefixPMF (m, pre)).toReal *
            lemma77TerminalHoldExpWeight alpha
              (taoSection7HoldPointOfPrefix m pre) := by
          rw [taoSection7HoldSourcePrefixPMF_apply_toReal]
          ring

/--
Fixed miss-count row of the terminal `Hold` MGF after expanding the source-prefix
PMF.  This is still before summing over all `m` and before transporting the
total expectation through the non-injective `taoSection7HoldPMF` pushforward.
-/
theorem taoSection7HoldSourcePrefixPMF_terminalHoldExpWeight_row_tsum
    {alpha : ℝ}
    (hs : Summable fun b : ℕ =>
      taoSection7PascalPrimeSourceMass b *
        taoSection7PascalPrimeStepExpWeight alpha alpha b)
    (m : ℕ) :
    (∑' pre : List ℕ,
      (taoSection7HoldSourcePrefixPMF (m, pre)).toReal *
        lemma77TerminalHoldExpWeight alpha
          (taoSection7HoldPointOfPrefix m pre)) =
      taoSection7Geom4MissMass m *
        (Real.exp (4 * alpha) *
          (taoSection7PascalPrimeStepMoment alpha) ^ m) := by
  calc
    (∑' pre : List ℕ,
      (taoSection7HoldSourcePrefixPMF (m, pre)).toReal *
        lemma77TerminalHoldExpWeight alpha
          (taoSection7HoldPointOfPrefix m pre))
        =
      ∑' pre : List ℕ,
        taoSection7Geom4MissMass m *
          ((taoSection7PascalPrimeSourceListPMF m pre).toReal *
            taoSection7PreHoldExpWeight alpha alpha pre) := by
          apply tsum_congr
          intro pre
          exact taoSection7HoldSourcePrefixPMF_mul_terminalHoldExpWeight_eq
            alpha m pre
    _ =
      taoSection7Geom4MissMass m *
        (∑' pre : List ℕ,
          (taoSection7PascalPrimeSourceListPMF m pre).toReal *
            taoSection7PreHoldExpWeight alpha alpha pre) := by
          rw [tsum_mul_left]
    _ =
      taoSection7Geom4MissMass m *
        (Real.exp (4 * alpha) *
          (taoSection7PascalPrimeStepMoment alpha) ^ m) := by
          rw [
            tsum_taoSection7PascalPrimeSourceListPMF_preHoldExpWeight_eq_exp_mul_stepMoment_pow
              hs m]

/--
Weighted expectation transport for a PMF pushforward, stated in `ENNReal` so
the non-injective fibers are handled before any real-valued summability
conversion.
-/
theorem pmf_map_tsum_mul_ofReal
    {α β : Type*} (p : PMF α) (f : α → β) (W : β → ℝ) :
    (∑' b : β, (p.map f b) * ENNReal.ofReal (W b)) =
      ∑' a : α, p a * ENNReal.ofReal (W (f a)) := by
  classical
  calc
    (∑' b : β, (p.map f b) * ENNReal.ofReal (W b)) =
        ∑' b : β, (∑' a : α, if b = f a then p a else 0) *
          ENNReal.ofReal (W b) := by
          apply tsum_congr
          intro b
          rw [PMF.map_apply]
    _ = ∑' b : β, ∑' a : α,
        (if b = f a then p a else 0) * ENNReal.ofReal (W b) := by
          apply tsum_congr
          intro b
          rw [ENNReal.tsum_mul_right]
    _ = ∑' a : α, ∑' b : β,
        (if b = f a then p a else 0) * ENNReal.ofReal (W b) := by
          rw [ENNReal.tsum_comm]
    _ = ∑' a : α, p a * ENNReal.ofReal (W (f a)) := by
          apply tsum_congr
          intro a
          rw [tsum_eq_single (f a)]
          · simp
          · intro b hb
            have hne : ¬ b = f a := hb
            simp [hne]

/--
Real-valued summability/equality wrapper for `pmf_map_tsum_mul_ofReal`, after a
finite source-side `ENNReal` weighted sum is known.
-/
theorem pmf_map_weighted_tsum_toReal_eq_of_finite
    {α β : Type*} (p : PMF α) (f : α → β) (W : β → ℝ)
    (hW : ∀ b, 0 ≤ W b)
    (hfinite :
      ((∑' a : α, p a * ENNReal.ofReal (W (f a))) : ENNReal) ≠ ⊤) :
    (Summable fun b : β => ((p.map f) b).toReal * W b) ∧
    (Summable fun a : α => (p a).toReal * W (f a)) ∧
    (∑' b : β, ((p.map f) b).toReal * W b) =
      ∑' a : α, (p a).toReal * W (f a) := by
  classical
  let gB : β → ENNReal := fun b => (p.map f b) * ENNReal.ofReal (W b)
  let gA : α → ENNReal := fun a => p a * ENNReal.ofReal (W (f a))
  have hENN : (∑' b : β, gB b) = ∑' a : α, gA a := by
    simpa [gB, gA] using pmf_map_tsum_mul_ofReal p f W
  have hBfinite : (∑' b : β, gB b) ≠ ⊤ := by
    rw [hENN]
    exact hfinite
  have hsumB_toReal : Summable fun b : β => (gB b).toReal :=
    ENNReal.summable_toReal hBfinite
  have hsumA_toReal : Summable fun a : α => (gA a).toReal :=
    ENNReal.summable_toReal hfinite
  have htermB : ∀ b : β, ((p.map f) b).toReal * W b = (gB b).toReal := by
    intro b
    simp [gB, ENNReal.toReal_mul, ENNReal.toReal_ofReal (hW b)]
  have htermA : ∀ a : α, (p a).toReal * W (f a) = (gA a).toReal := by
    intro a
    simp [gA, ENNReal.toReal_mul, ENNReal.toReal_ofReal (hW (f a))]
  refine ⟨?_, ?_, ?_⟩
  · exact hsumB_toReal.congr (fun b => (htermB b).symm)
  · exact hsumA_toReal.congr (fun a => (htermA a).symm)
  · calc
      (∑' b : β, ((p.map f) b).toReal * W b)
          = ∑' b : β, (gB b).toReal := by
            apply tsum_congr
            intro b
            exact htermB b
      _ = (∑' b : β, gB b).toReal := by
            rw [ENNReal.tsum_toReal_eq]
            intro b
            exact ENNReal.mul_ne_top (PMF.apply_ne_top (p.map f) b)
              ENNReal.ofReal_ne_top
      _ = (∑' a : α, gA a).toReal := by
            rw [hENN]
      _ = ∑' a : α, (gA a).toReal := by
            rw [ENNReal.tsum_toReal_eq]
            intro a
            exact ENNReal.mul_ne_top (PMF.apply_ne_top p a)
              ENNReal.ofReal_ne_top
      _ = ∑' a : α, (p a).toReal * W (f a) := by
            apply tsum_congr
            intro a
            exact (htermA a).symm

/--
Transport the terminal exponential-weight expectation from the non-injective
`Hold` pushforward back to the source-prefix PMF.  The finite source-side
`ENNReal` premise is the remaining total-MGF/summability input; this theorem
does not prove the geometric scalar bound.
-/
theorem taoSection7HoldPMF_terminalExpWeight_tsum_eq_sourcePrefix
    {alpha : ℝ}
    (hfinite :
      ((∑' x : ℕ × List ℕ,
        taoSection7HoldSourcePrefixPMF x *
          ENNReal.ofReal
            (lemma77TerminalHoldExpWeight alpha
              (taoSection7HoldPointOfPrefix x.1 x.2))) : ENNReal) ≠ ⊤) :
    (Summable fun h : TaoSection7RenewalPoint =>
      (taoSection7HoldPMF h).toReal * lemma77TerminalHoldExpWeight alpha h) ∧
    (Summable fun x : ℕ × List ℕ =>
      (taoSection7HoldSourcePrefixPMF x).toReal *
        lemma77TerminalHoldExpWeight alpha
          (taoSection7HoldPointOfPrefix x.1 x.2)) ∧
    (∑' h : TaoSection7RenewalPoint,
      (taoSection7HoldPMF h).toReal * lemma77TerminalHoldExpWeight alpha h) =
    ∑' x : ℕ × List ℕ,
      (taoSection7HoldSourcePrefixPMF x).toReal *
        lemma77TerminalHoldExpWeight alpha
          (taoSection7HoldPointOfPrefix x.1 x.2) := by
  classical
  let f : ℕ × List ℕ → TaoSection7RenewalPoint :=
    fun x => taoSection7HoldPointOfPrefix x.1 x.2
  let W : TaoSection7RenewalPoint → ℝ := lemma77TerminalHoldExpWeight alpha
  have hW : ∀ h : TaoSection7RenewalPoint, 0 ≤ W h := by
    intro h
    exact le_of_lt (Real.exp_pos _)
  have htransport :=
    pmf_map_weighted_tsum_toReal_eq_of_finite
      taoSection7HoldSourcePrefixPMF f W hW (by simpa [f, W] using hfinite)
  rcases htransport with ⟨hsumMap, hsumSource, heq⟩
  refine ⟨?_, ?_, ?_⟩
  · simpa [f, W, ← taoSection7HoldPMF_eq_sourcePrefixPMF_map] using hsumMap
  · simpa [f, W] using hsumSource
  · simpa [f, W, ← taoSection7HoldPMF_eq_sourcePrefixPMF_map] using heq

theorem summable_taoSection7HoldSourcePrefixPMF_terminalHoldExpWeight_of_summable_missSeries
    {alpha : ℝ}
    (hs : Summable fun b : ℕ =>
      taoSection7PascalPrimeSourceMass b *
        taoSection7PascalPrimeStepExpWeight alpha alpha b)
    (houter : Summable fun m : ℕ =>
      taoSection7Geom4MissMass m *
        (Real.exp (4 * alpha) *
          (taoSection7PascalPrimeStepMoment alpha) ^ m)) :
    Summable fun x : ℕ × List ℕ =>
      (taoSection7HoldSourcePrefixPMF x).toReal *
        lemma77TerminalHoldExpWeight alpha
          (taoSection7HoldPointOfPrefix x.1 x.2) := by
  have hnonneg : 0 ≤ fun x : ℕ × List ℕ =>
      (taoSection7HoldSourcePrefixPMF x).toReal *
        lemma77TerminalHoldExpWeight alpha
          (taoSection7HoldPointOfPrefix x.1 x.2) := by
    intro x
    exact mul_nonneg ENNReal.toReal_nonneg (le_of_lt (Real.exp_pos _))
  refine (summable_prod_of_nonneg (α := ℕ) (β := List ℕ) hnonneg).2 ?_
  constructor
  · intro m
    exact summable_taoSection7HoldSourcePrefixPMF_terminalHoldExpWeight_row hs m
  · refine houter.congr ?_
    intro m
    exact (taoSection7HoldSourcePrefixPMF_terminalHoldExpWeight_row_tsum hs m).symm

theorem tsum_taoSection7HoldSourcePrefixPMF_terminalHoldExpWeight_eq_missSeries_of_summable
    {alpha : ℝ}
    (hs : Summable fun b : ℕ =>
      taoSection7PascalPrimeSourceMass b *
        taoSection7PascalPrimeStepExpWeight alpha alpha b)
    (houter : Summable fun m : ℕ =>
      taoSection7Geom4MissMass m *
        (Real.exp (4 * alpha) *
          (taoSection7PascalPrimeStepMoment alpha) ^ m)) :
    (∑' x : ℕ × List ℕ,
      (taoSection7HoldSourcePrefixPMF x).toReal *
        lemma77TerminalHoldExpWeight alpha
          (taoSection7HoldPointOfPrefix x.1 x.2)) =
      ∑' m : ℕ,
        taoSection7Geom4MissMass m *
          (Real.exp (4 * alpha) *
            (taoSection7PascalPrimeStepMoment alpha) ^ m) := by
  have htotal :=
    summable_taoSection7HoldSourcePrefixPMF_terminalHoldExpWeight_of_summable_missSeries
      hs houter
  rw [Summable.tsum_prod htotal]
  apply tsum_congr
  intro m
  exact taoSection7HoldSourcePrefixPMF_terminalHoldExpWeight_row_tsum hs m

theorem summable_taoSection7TerminalHoldMissSeries_log_21_div_20 :
    Summable fun m : ℕ =>
      taoSection7Geom4MissMass m *
        (Real.exp (4 * Real.log (21 / 20 : ℝ)) *
          (taoSection7PascalPrimeStepMoment
            (Real.log (21 / 20 : ℝ))) ^ m) := by
  have hgeom : Summable fun m : ℕ =>
      ((1 / 4 : ℝ) * Real.exp (4 * Real.log (21 / 20 : ℝ))) *
        (((3 / 4 : ℝ) * (75381453 / 57760000 : ℝ)) ^ m) :=
    (summable_geometric_of_lt_one
      (by norm_num :
        0 ≤ ((3 / 4 : ℝ) * (75381453 / 57760000 : ℝ)))
      (by norm_num :
        ((3 / 4 : ℝ) * (75381453 / 57760000 : ℝ)) < 1)).mul_left
        ((1 / 4 : ℝ) * Real.exp (4 * Real.log (21 / 20 : ℝ)))
  refine hgeom.congr ?_
  intro m
  unfold taoSection7Geom4MissMass
  rw [taoSection7PascalPrimeStepMoment_log_21_div_20_eq]
  rw [mul_pow]
  ring

theorem summable_taoSection7HoldSourcePrefixPMF_terminalHoldExpWeight_log_21_div_20 :
    Summable fun x : ℕ × List ℕ =>
      (taoSection7HoldSourcePrefixPMF x).toReal *
        lemma77TerminalHoldExpWeight (Real.log (21 / 20 : ℝ))
          (taoSection7HoldPointOfPrefix x.1 x.2) :=
  summable_taoSection7HoldSourcePrefixPMF_terminalHoldExpWeight_of_summable_missSeries
    summable_taoSection7PascalPrimeStepMoment_log_21_div_20
    summable_taoSection7TerminalHoldMissSeries_log_21_div_20

theorem tsum_taoSection7HoldSourcePrefixPMF_terminalHoldExpWeight_log_21_div_20_eq_missSeries :
    (∑' x : ℕ × List ℕ,
      (taoSection7HoldSourcePrefixPMF x).toReal *
        lemma77TerminalHoldExpWeight (Real.log (21 / 20 : ℝ))
          (taoSection7HoldPointOfPrefix x.1 x.2)) =
      ∑' m : ℕ,
        taoSection7Geom4MissMass m *
          (Real.exp (4 * Real.log (21 / 20 : ℝ)) *
            (taoSection7PascalPrimeStepMoment
              (Real.log (21 / 20 : ℝ))) ^ m) :=
  tsum_taoSection7HoldSourcePrefixPMF_terminalHoldExpWeight_eq_missSeries_of_summable
    summable_taoSection7PascalPrimeStepMoment_log_21_div_20
    summable_taoSection7TerminalHoldMissSeries_log_21_div_20

theorem tsum_taoSection7TerminalHoldMissSeries_log_21_div_20_eq :
    (∑' m : ℕ,
      taoSection7Geom4MissMass m *
        (Real.exp (4 * Real.log (21 / 20 : ℝ)) *
          (taoSection7PascalPrimeStepMoment
            (Real.log (21 / 20 : ℝ))) ^ m)) =
      70207641 / 4895641 := by
  have hExp : Real.exp (4 * Real.log (21 / 20 : ℝ)) = (21 / 20 : ℝ) ^ 4 := by
    rw [show 4 * Real.log (21 / 20 : ℝ) =
        ((4 : ℕ) : ℝ) * Real.log (21 / 20 : ℝ) by norm_num]
    rw [Real.exp_nat_mul]
    rw [Real.exp_log]
    norm_num
  calc
    (∑' m : ℕ,
      taoSection7Geom4MissMass m *
        (Real.exp (4 * Real.log (21 / 20 : ℝ)) *
          (taoSection7PascalPrimeStepMoment
            (Real.log (21 / 20 : ℝ))) ^ m))
        = ∑' m : ℕ,
            ((1 / 4 : ℝ) * Real.exp (4 * Real.log (21 / 20 : ℝ))) *
              (((3 / 4 : ℝ) * (75381453 / 57760000 : ℝ)) ^ m) := by
          apply tsum_congr
          intro m
          unfold taoSection7Geom4MissMass
          rw [taoSection7PascalPrimeStepMoment_log_21_div_20_eq]
          rw [mul_pow]
          ring
    _ = ((1 / 4 : ℝ) * Real.exp (4 * Real.log (21 / 20 : ℝ))) *
          (∑' m : ℕ,
            (((3 / 4 : ℝ) * (75381453 / 57760000 : ℝ)) ^ m)) := by
          rw [tsum_mul_left]
    _ = ((1 / 4 : ℝ) * ((21 / 20 : ℝ) ^ 4)) *
          (∑' m : ℕ,
            (((3 / 4 : ℝ) * (75381453 / 57760000 : ℝ)) ^ m)) := by
          rw [hExp]
    _ = 70207641 / 4895641 := by
          rw [tsum_geometric_of_lt_one
            (by norm_num :
              0 ≤ ((3 / 4 : ℝ) * (75381453 / 57760000 : ℝ)))
            (by norm_num :
              ((3 / 4 : ℝ) * (75381453 / 57760000 : ℝ)) < 1)]
          norm_num

theorem tsum_taoSection7TerminalHoldMissSeries_log_21_div_20_le_583443_div_40000 :
    (∑' m : ℕ,
      taoSection7Geom4MissMass m *
        (Real.exp (4 * Real.log (21 / 20 : ℝ)) *
          (taoSection7PascalPrimeStepMoment
            (Real.log (21 / 20 : ℝ))) ^ m)) ≤
      583443 / 40000 := by
  rw [tsum_taoSection7TerminalHoldMissSeries_log_21_div_20_eq]
  norm_num

theorem tsum_taoSection7HoldSourcePrefixPMF_terminalHoldExpWeight_log_21_div_20_le_583443_div_40000 :
    (∑' x : ℕ × List ℕ,
      (taoSection7HoldSourcePrefixPMF x).toReal *
        lemma77TerminalHoldExpWeight (Real.log (21 / 20 : ℝ))
          (taoSection7HoldPointOfPrefix x.1 x.2)) ≤
      583443 / 40000 := by
  rw [tsum_taoSection7HoldSourcePrefixPMF_terminalHoldExpWeight_log_21_div_20_eq_missSeries]
  exact tsum_taoSection7TerminalHoldMissSeries_log_21_div_20_le_583443_div_40000

theorem tsum_taoSection7HoldSourcePrefixPMF_terminalHoldExpWeight_log_21_div_20_ne_top :
    ((∑' x : ℕ × List ℕ,
      taoSection7HoldSourcePrefixPMF x *
        ENNReal.ofReal
          (lemma77TerminalHoldExpWeight (Real.log (21 / 20 : ℝ))
            (taoSection7HoldPointOfPrefix x.1 x.2))) : ENNReal) ≠ ⊤ := by
  have hsum :=
    summable_taoSection7HoldSourcePrefixPMF_terminalHoldExpWeight_log_21_div_20
  rw [show (∑' x : ℕ × List ℕ,
      taoSection7HoldSourcePrefixPMF x *
        ENNReal.ofReal
          (lemma77TerminalHoldExpWeight (Real.log (21 / 20 : ℝ))
            (taoSection7HoldPointOfPrefix x.1 x.2))) =
      ∑' x : ℕ × List ℕ,
        ENNReal.ofReal
          ((taoSection7HoldSourcePrefixPMF x).toReal *
            lemma77TerminalHoldExpWeight (Real.log (21 / 20 : ℝ))
              (taoSection7HoldPointOfPrefix x.1 x.2)) by
        apply tsum_congr
        intro x
        calc
          taoSection7HoldSourcePrefixPMF x *
              ENNReal.ofReal
                (lemma77TerminalHoldExpWeight (Real.log (21 / 20 : ℝ))
                  (taoSection7HoldPointOfPrefix x.1 x.2))
              = ENNReal.ofReal (taoSection7HoldSourcePrefixPMF x).toReal *
                  ENNReal.ofReal
                    (lemma77TerminalHoldExpWeight (Real.log (21 / 20 : ℝ))
                      (taoSection7HoldPointOfPrefix x.1 x.2)) := by
                rw [
                  ENNReal.ofReal_toReal
                    (PMF.apply_ne_top taoSection7HoldSourcePrefixPMF x)]
          _ = ENNReal.ofReal
                ((taoSection7HoldSourcePrefixPMF x).toReal *
                  lemma77TerminalHoldExpWeight (Real.log (21 / 20 : ℝ))
                    (taoSection7HoldPointOfPrefix x.1 x.2)) := by
                rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg]]
  exact hsum.tsum_ofReal_ne_top

theorem summable_taoSection7HoldPMF_terminalHoldExpWeight_log_21_div_20 :
    Summable fun h : TaoSection7RenewalPoint =>
      (taoSection7HoldPMF h).toReal *
        lemma77TerminalHoldExpWeight (Real.log (21 / 20 : ℝ)) h :=
  (taoSection7HoldPMF_terminalExpWeight_tsum_eq_sourcePrefix
    tsum_taoSection7HoldSourcePrefixPMF_terminalHoldExpWeight_log_21_div_20_ne_top).1

theorem tsum_taoSection7HoldPMF_terminalHoldExpWeight_log_21_div_20_eq_sourcePrefix :
    (∑' h : TaoSection7RenewalPoint,
      (taoSection7HoldPMF h).toReal *
        lemma77TerminalHoldExpWeight (Real.log (21 / 20 : ℝ)) h) =
    ∑' x : ℕ × List ℕ,
      (taoSection7HoldSourcePrefixPMF x).toReal *
        lemma77TerminalHoldExpWeight (Real.log (21 / 20 : ℝ))
          (taoSection7HoldPointOfPrefix x.1 x.2) :=
  (taoSection7HoldPMF_terminalExpWeight_tsum_eq_sourcePrefix
    tsum_taoSection7HoldSourcePrefixPMF_terminalHoldExpWeight_log_21_div_20_ne_top).2.2

theorem tsum_taoSection7HoldPMF_terminalHoldExpWeight_log_21_div_20_le_15 :
    (∑' h : TaoSection7RenewalPoint,
      (taoSection7HoldPMF h).toReal *
        lemma77TerminalHoldExpWeight (Real.log (21 / 20 : ℝ)) h) ≤
      15 := by
  rw [tsum_taoSection7HoldPMF_terminalHoldExpWeight_log_21_div_20_eq_sourcePrefix]
  exact
    tsum_taoSection7HoldSourcePrefixPMF_terminalHoldExpWeight_log_21_div_20_le_583443_div_40000.trans
      (by norm_num : (583443 / 40000 : ℝ) ≤ 15)

theorem lemma77TerminalHoldExpMomentInput_log_21_div_20 :
    Lemma77TerminalHoldExpMomentInput
      (15 : ℝ) (Real.log (21 / 20 : ℝ)) where
  constants := by
    constructor
    · norm_num
    · exact Real.log_pos (by norm_num : (1 : ℝ) < 21 / 20)
  summable_weighted :=
    summable_taoSection7HoldPMF_terminalHoldExpWeight_log_21_div_20
  moment_le :=
    tsum_taoSection7HoldPMF_terminalHoldExpWeight_log_21_div_20_le_15

theorem lemma77TerminalHoldPointTailInput_log_21_div_20 :
    Lemma77TerminalHoldPointTailInput
      (15 : ℝ) (Real.log (21 / 20 : ℝ)) :=
  lemma77TerminalHoldPointTailInput_of_expMoment
    lemma77TerminalHoldExpMomentInput_log_21_div_20

end TaoSection7Lemma77

end Tao
end Erdos1135
