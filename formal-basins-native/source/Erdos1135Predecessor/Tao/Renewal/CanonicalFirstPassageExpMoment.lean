/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.CanonicalFirstPassageEndpoint
import Erdos1135Predecessor.Tao.Renewal.HoldListHorizontalMoment
import Erdos1135Predecessor.Tao.Renewal.Lemma77TerminalHoldMoment

open scoped BigOperators

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

namespace TaoSection7Lemma77

open TaoSection7Case3SourceStoppingRun.Lemma79TailExpectation

def lemma77CanonicalStoppedEndpoint
    (start : TaoSection7RenewalPoint) (s : ℕ)
    (full : List TaoSection7RenewalPoint) : ℕ × ℤ :=
  lemma77EndpointOfPrefix start
    (full.take (lemma79VerticalFirstPassageCut start s full))

theorem lemma77CanonicalFirstPassageEndpointPMF_eq_holdList_map
    (start : TaoSection7RenewalPoint) (s : ℕ) :
    lemma77CanonicalFirstPassageEndpointPMF start s =
      (taoSection7HoldListPMF (s + 1)).map
        (lemma77CanonicalStoppedEndpoint start s) := by
  unfold lemma77CanonicalFirstPassageEndpointPMF
    lemma77CanonicalFirstPassagePrefixPMF
    lemma77CanonicalStoppedEndpoint
  rw [PMF.map_comp]
  rw [← taoSection7HoldSourcePrefixListPMF_map_holdPoint_eq (s + 1)]
  rw [PMF.map_comp]
  rfl

theorem lemma77HoldPrefixHorizontalDelta_take_le
    (K : ℕ) (full : List TaoSection7RenewalPoint) :
    lemma77HoldPrefixHorizontalDelta (full.take K).length (full.take K) ≤
      lemma77HoldPrefixHorizontalDelta full.length full := by
  induction full generalizing K with
  | nil => simp [lemma77HoldPrefixHorizontalDelta]
  | cons h hs ih =>
      cases K with
      | zero => simp [lemma77HoldPrefixHorizontalDelta]
      | succ K =>
          have htail := ih K
          simp [lemma77HoldPrefixHorizontalDelta] at htail ⊢
          omega

theorem lemma77CanonicalStoppedEndpoint_fst_le_fullHorizontalDelta
    (start : TaoSection7RenewalPoint) (s : ℕ)
    (full : List TaoSection7RenewalPoint) :
    (lemma77CanonicalStoppedEndpoint start s full).1 ≤
      lemma77HoldPrefixHorizontalDelta full.length full := by
  unfold lemma77CanonicalStoppedEndpoint lemma77EndpointOfPrefix
  rw [lemma77HoldPrefixIncrement_eq_horizontalDelta]
  exact lemma77HoldPrefixHorizontalDelta_take_le _ _

theorem lemma77CanonicalFirstPassageEndpointPMF_horizontalExpMoment_le
    (start : TaoSection7RenewalPoint) (s : ℕ) {t : ℝ}
    (ht : 0 ≤ t) (hadm : 3 * Real.exp t < 4) :
    Summable (fun x : ℕ × ℤ =>
      (lemma77CanonicalFirstPassageEndpointPMF start s x).toReal *
        Real.exp (t * (x.1 : ℝ))) ∧
    (∑' x : ℕ × ℤ,
      (lemma77CanonicalFirstPassageEndpointPMF start s x).toReal *
        Real.exp (t * (x.1 : ℝ))) ≤
      taoSection7Geom4ExpMoment t ^ (s + 1) := by
  let p := taoSection7HoldListPMF (s + 1)
  let f := lemma77CanonicalStoppedEndpoint start s
  let W : ℕ × ℤ → ℝ := fun x => Real.exp (t * (x.1 : ℝ))
  let fullWeight : List TaoSection7RenewalPoint → ℝ := fun full =>
    Real.exp
      (t * (lemma77HoldPrefixHorizontalDelta (s + 1) full : ℝ))
  have hmaster :=
    taoSection7HoldListPMF_horizontalExpMoment (s + 1) hadm
  have hpoint : ∀ full : List TaoSection7RenewalPoint,
      (p full).toReal * W (f full) ≤
        (p full).toReal * fullWeight full := by
    intro full
    by_cases hlen : full.length = s + 1
    · apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      apply Real.exp_le_exp.mpr
      apply mul_le_mul_of_nonneg_left _ ht
      have hdelta :=
        lemma77CanonicalStoppedEndpoint_fst_le_fullHorizontalDelta
          start s full
      rw [hlen] at hdelta
      exact_mod_cast hdelta
    · have hzero : p full = 0 := by
        exact taoSection7HoldListPMF_apply_eq_zero_of_length_ne
          (s + 1) full hlen
      simp [hzero]
  have hmaster' : Summable fun full =>
      (p full).toReal * fullWeight full := by
    simpa [p, fullWeight] using hmaster.1
  have hstopped : Summable fun full =>
      (p full).toReal * W (f full) :=
    Summable.of_nonneg_of_le
      (fun full => mul_nonneg ENNReal.toReal_nonneg (Real.exp_pos _).le)
      hpoint hmaster'
  have hstopped_le :
      (∑' full, (p full).toReal * W (f full)) ≤
        taoSection7Geom4ExpMoment t ^ (s + 1) := by
    calc
      (∑' full, (p full).toReal * W (f full)) ≤
          ∑' full, (p full).toReal * fullWeight full :=
        hstopped.tsum_le_tsum hpoint hmaster'
      _ = taoSection7Geom4ExpMoment t ^ (s + 1) := by
        simpa [p, fullWeight] using hmaster.2
  have hfinite :
      ((∑' full, p full * ENNReal.ofReal (W (f full))) : ENNReal) ≠ ⊤ := by
    have heq :
        (∑' full, p full * ENNReal.ofReal (W (f full))) =
          ∑' full, ENNReal.ofReal ((p full).toReal * W (f full)) := by
      apply tsum_congr
      intro full
      rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal (PMF.apply_ne_top p full)]
    rw [heq]
    exact hstopped.tsum_ofReal_ne_top
  have htransport := pmf_map_weighted_tsum_toReal_eq_of_finite
    p f W (fun _ => (Real.exp_pos _).le) hfinite
  rw [lemma77CanonicalFirstPassageEndpointPMF_eq_holdList_map start s]
  have hsumEq :
      (∑' x, ((p.map f) x).toReal * W x) =
        ∑' full, (p full).toReal * W (f full) := htransport.2.2
  exact ⟨by simpa [p, f, W] using htransport.1,
    hsumEq.trans_le hstopped_le⟩

end TaoSection7Lemma77

end

end Tao

end Erdos1135Predecessor
