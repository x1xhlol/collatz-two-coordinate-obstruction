/- This local copy changes proof tactics only to satisfy the pinned toolchain linters.
   The theorem statements are unchanged; see provenance/native-linter-patches.json. -/

import Erdos1135.Tao.Renewal.HoldIID
import Erdos1135.Tao.Renewal.RenewalPathBasic
import Mathlib.Tactic

/-!
# Lemma 7.7 Height-Potential Core

This low module owns the shared renewal-prefix increments, signed endpoint
mass atomization, and height-potential vocabulary used by both the Pascal
producer and the higher local-limit consumers.  It has no dependency on the
endpoint-marginal, kernel-tail, Lemma 7.10, or geometry branches.
-/

namespace Erdos1135
namespace Tao

open scoped BigOperators

noncomputable section

namespace TaoSection7Lemma77

/-- Generic horizontal increment selected by a sample-dependent prefix time. -/
def prefixIncrement
    {Ω : Type*}
    (start : Ω → TaoSection7RenewalPoint)
    (K : Ω → ℕ)
    (pre : Ω → List TaoSection7RenewalPoint)
    (ω : Ω) : ℕ :=
  ((taoSection7RenewalPathPoint (start ω) (pre ω) (K ω)).j : ℕ) -
    ((start ω).j : ℕ)

/-- Generic vertical increment selected by a sample-dependent prefix time. -/
def prefixVerticalIncrement
    {Ω : Type*}
    (start : Ω → TaoSection7RenewalPoint)
    (K : Ω → ℕ)
    (pre : Ω → List TaoSection7RenewalPoint)
    (ω : Ω) : ℤ :=
  (taoSection7RenewalPathPoint (start ω) (pre ω) (K ω)).l -
    (start ω).l

/-- Tao's two-term one-dimensional `G_n` weight. -/
def taoLemma22GaussianWeight (n : ℕ) (x : ℝ) : ℝ :=
  if n = 0 then
    Real.exp (-|x|)
  else
    Real.exp (-(x ^ 2 / (n : ℝ))) + Real.exp (-|x|)

/-- Horizontal increment of a fixed iid `Hold` prefix from a fixed start. -/
def lemma77HoldPrefixIncrement
    (start : TaoSection7RenewalPoint)
    (n : ℕ)
    (hs : List TaoSection7RenewalPoint) : ℕ :=
  prefixIncrement
    (fun _ : List TaoSection7RenewalPoint => start)
    (fun _ => n)
    (fun hs => hs)
    hs

/-- Vertical increment of a fixed iid `Hold` prefix from a fixed start. -/
def lemma77HoldPrefixVerticalIncrement
    (start : TaoSection7RenewalPoint)
    (n : ℕ)
    (hs : List TaoSection7RenewalPoint) : ℤ :=
  prefixVerticalIncrement
    (fun _ : List TaoSection7RenewalPoint => start)
    (fun _ => n)
    (fun hs => hs)
    hs

/-- Horizontal displacement accumulated by the first `n` iid `Hold` increments. -/
def lemma77HoldPrefixHorizontalDelta : ℕ → List TaoSection7RenewalPoint → ℕ
  | 0, _ => 0
  | _n + 1, [] => 0
  | n + 1, h :: hs => (h.j : ℕ) + lemma77HoldPrefixHorizontalDelta n hs

/-- Every available Hold increment advances the horizontal coordinate. -/
theorem lemma77HoldPrefixHorizontalDelta_ge_steps
    {q : ℕ} {full : List TaoSection7RenewalPoint}
    (hq : q ≤ full.length) :
    q ≤ lemma77HoldPrefixHorizontalDelta q full := by
  induction q generalizing full with
  | zero => simp
  | succ q ih =>
      cases full with
      | nil => simp at hq
      | cons h hs =>
          have hq_tail : q ≤ hs.length := by
            simpa using Nat.le_of_succ_le_succ hq
          have hdelta := ih hq_tail
          have hj : 1 ≤ (h.j : ℕ) := h.j.2
          simp only [lemma77HoldPrefixHorizontalDelta]
          omega

/-- The renewal path's horizontal coordinate is the start plus the raw prefix delta. -/
theorem lemma77RenewalPathPoint_j_eq_start_add_horizontalDelta
    (start : TaoSection7RenewalPoint) :
    ∀ (n : ℕ) (hs : List TaoSection7RenewalPoint),
      ((taoSection7RenewalPathPoint start hs n).j : ℕ) =
        (start.j : ℕ) + lemma77HoldPrefixHorizontalDelta n hs := by
  intro n
  induction n generalizing start with
  | zero =>
      intro hs
      simp [lemma77HoldPrefixHorizontalDelta]
  | succ n ih =>
      intro hs
      cases hs with
      | nil =>
          simp [lemma77HoldPrefixHorizontalDelta]
      | cons h hs =>
          have hih := ih (start + h) hs
          simp [taoSection7RenewalPathPoint,
            lemma77HoldPrefixHorizontalDelta] at hih ⊢
          omega

/-- The checked relative horizontal prefix increment is the raw prefix delta. -/
theorem lemma77HoldPrefixIncrement_eq_horizontalDelta
    (start : TaoSection7RenewalPoint) (n : ℕ)
    (hs : List TaoSection7RenewalPoint) :
    lemma77HoldPrefixIncrement start n hs =
      lemma77HoldPrefixHorizontalDelta n hs := by
  simp [lemma77HoldPrefixIncrement, prefixIncrement,
    lemma77RenewalPathPoint_j_eq_start_add_horizontalDelta]

/-- Relative horizontal prefix coordinates are independent of the dummy start. -/
theorem lemma77HoldPrefixIncrement_start_eq
    (start start' : TaoSection7RenewalPoint) (n : ℕ)
    (hs : List TaoSection7RenewalPoint) :
    lemma77HoldPrefixIncrement start n hs =
      lemma77HoldPrefixIncrement start' n hs := by
  rw [lemma77HoldPrefixIncrement_eq_horizontalDelta,
    lemma77HoldPrefixIncrement_eq_horizontalDelta]

/-- Relative vertical prefix coordinates are independent of the dummy start. -/
theorem lemma77HoldPrefixVerticalIncrement_start_eq
    (start start' : TaoSection7RenewalPoint) (n : ℕ)
    (hs : List TaoSection7RenewalPoint) :
    lemma77HoldPrefixVerticalIncrement start n hs =
      lemma77HoldPrefixVerticalIncrement start' n hs := by
  induction n generalizing start start' hs with
  | zero =>
      simp [lemma77HoldPrefixVerticalIncrement, prefixVerticalIncrement]
  | succ n ih =>
      cases hs with
      | nil =>
          simp [lemma77HoldPrefixVerticalIncrement, prefixVerticalIncrement]
      | cons h hs =>
          have hih := ih (start + h) (start' + h) hs
          simp [lemma77HoldPrefixVerticalIncrement, prefixVerticalIncrement,
            taoSection7RenewalPathPoint] at hih ⊢
          omega

/-- Nonnegative Hold increments give nonnegative relative vertical prefix height. -/
theorem lemma77HoldPrefixVerticalIncrement_nonneg_of_all_l_nonneg
    (origin : TaoSection7RenewalPoint) :
    ∀ (k : ℕ) (hs : List TaoSection7RenewalPoint),
      (∀ h, h ∈ hs → 0 ≤ h.l) →
        0 ≤ lemma77HoldPrefixVerticalIncrement origin k hs := by
  intro k
  induction k generalizing origin with
  | zero =>
      intro hs _hall
      simp [lemma77HoldPrefixVerticalIncrement, prefixVerticalIncrement]
  | succ k ih =>
      intro hs hall
      cases hs with
      | nil =>
          simp [lemma77HoldPrefixVerticalIncrement, prefixVerticalIncrement]
      | cons h hs =>
          have hhead : 0 ≤ h.l := hall h (by simp)
          have htail : ∀ h', h' ∈ hs → 0 ≤ h'.l := by
            intro h' hh'
            exact hall h' (by simp [hh'])
          have hrec :
              0 ≤ lemma77HoldPrefixVerticalIncrement (origin + h) k hs :=
            ih (origin + h) hs htail
          dsimp [lemma77HoldPrefixVerticalIncrement, prefixVerticalIncrement]
            at hrec ⊢
          simp [taoSection7RenewalPathPoint] at hrec ⊢
          omega

/-- Nonzero iid `Hold` list mass supplies nonnegative vertical prefix height. -/
theorem lemma77HoldPrefixVerticalIncrement_nonneg_of_holdListPMF_toReal_ne_zero
    (origin : TaoSection7RenewalPoint)
    {n : ℕ} {hs : List TaoSection7RenewalPoint}
    (hmass : (taoSection7HoldListPMF n hs).toReal ≠ 0)
    (k : ℕ) :
    0 ≤ lemma77HoldPrefixVerticalIncrement origin k hs :=
  lemma77HoldPrefixVerticalIncrement_nonneg_of_all_l_nonneg origin k hs
    (taoSection7HoldListPMF_ne_zero_all_l_nonneg hmass)

/-- Signed endpoint event for an iid `Hold` prefix. -/
def lemma77HoldPrefixSignedEndpointEvent
    (start : TaoSection7RenewalPoint) (n : ℕ) (j ell : ℤ) :
    Set (List TaoSection7RenewalPoint) :=
  {hs |
    (lemma77HoldPrefixIncrement start n hs : ℤ) = j ∧
      lemma77HoldPrefixVerticalIncrement start n hs = ell}

/-- Signed endpoint events are independent of the dummy start. -/
theorem lemma77HoldPrefixSignedEndpointEvent_start_eq
    (start start' : TaoSection7RenewalPoint) (n : ℕ) (j ell : ℤ) :
    lemma77HoldPrefixSignedEndpointEvent start n j ell =
      lemma77HoldPrefixSignedEndpointEvent start' n j ell := by
  ext hs
  simp [lemma77HoldPrefixSignedEndpointEvent,
    lemma77HoldPrefixIncrement_start_eq start start' n hs,
    lemma77HoldPrefixVerticalIncrement_start_eq start start' n hs]

/-- Mass of a signed `Hold` prefix endpoint event under the iid list law. -/
def lemma77HoldPrefixSignedEndpointMass
    (start : TaoSection7RenewalPoint) (n : ℕ) (j ell : ℤ) : ℝ :=
  ((taoSection7HoldListPMF n).toOuterMeasure
      (lemma77HoldPrefixSignedEndpointEvent start n j ell)).toReal

/-- Signed endpoint masses are independent of the dummy start. -/
theorem lemma77HoldPrefixSignedEndpointMass_start_eq
    (start start' : TaoSection7RenewalPoint) (n : ℕ) (j ell : ℤ) :
    lemma77HoldPrefixSignedEndpointMass start n j ell =
      lemma77HoldPrefixSignedEndpointMass start' n j ell := by
  rw [lemma77HoldPrefixSignedEndpointMass,
    lemma77HoldPrefixSignedEndpointMass,
    lemma77HoldPrefixSignedEndpointEvent_start_eq start start' n j ell]

/-- Local alias for the iid `Hold` list law's length support. -/
theorem lemma77HoldListPMF_apply_eq_zero_of_length_ne
    {n : ℕ} {hs : List TaoSection7RenewalPoint}
    (h : hs.length ≠ n) :
    taoSection7HoldListPMF n hs = 0 :=
  taoSection7HoldListPMF_apply_eq_zero_of_length_ne n hs h

/-- Real point masses of the iid `Hold` list law vanish off length `n`. -/
theorem lemma77HoldListPMF_toReal_eq_zero_of_length_ne
    {n : ℕ} {hs : List TaoSection7RenewalPoint}
    (h : hs.length ≠ n) :
    (taoSection7HoldListPMF n hs).toReal = 0 := by
  rw [lemma77HoldListPMF_apply_eq_zero_of_length_ne h]
  simp

/-- Real atomization of a PMF event mass over an arbitrary sample type. -/
theorem pmf_toOuterMeasure_toReal_eq_tsum_indicator
    {α : Type*} (p : PMF α) (E : Set α) :
    (p.toOuterMeasure E).toReal =
      ∑' a : α, E.indicator (fun a => (p a).toReal) a := by
  classical
  rw [PMF.toOuterMeasure_apply]
  rw [ENNReal.tsum_toReal_eq]
  · apply tsum_congr
    intro a
    by_cases h : a ∈ E <;> simp [Set.indicator, h]
  · intro a
    by_cases h : a ∈ E <;> simp [Set.indicator, h, PMF.apply_ne_top p a]

/-- Signed endpoint event with the iid list-law length support explicit. -/
def lemma77HoldPrefixSignedEndpointLengthEvent
    (start : TaoSection7RenewalPoint) (n : ℕ) (j ell : ℤ) :
    Set (List TaoSection7RenewalPoint) :=
  {hs | hs ∈ lemma77HoldPrefixSignedEndpointEvent start n j ell ∧ hs.length = n}

/-- Atomization of signed endpoint mass over the exact-length endpoint fiber. -/
theorem lemma77HoldPrefixSignedEndpointMass_eq_tsum_length_fiber
    (start : TaoSection7RenewalPoint) (n : ℕ) (j ell : ℤ) :
    lemma77HoldPrefixSignedEndpointMass start n j ell =
      ∑' hs : {hs : List TaoSection7RenewalPoint //
          hs ∈ lemma77HoldPrefixSignedEndpointLengthEvent start n j ell},
        (taoSection7HoldListPMF n hs.1).toReal := by
  classical
  rw [lemma77HoldPrefixSignedEndpointMass,
    pmf_toOuterMeasure_toReal_eq_tsum_indicator]
  trans ∑' hs : List TaoSection7RenewalPoint,
      (lemma77HoldPrefixSignedEndpointLengthEvent start n j ell).indicator
        (fun hs : List TaoSection7RenewalPoint =>
          (taoSection7HoldListPMF n hs).toReal) hs
  · apply tsum_congr
    intro hs
    by_cases hmem :
        hs ∈ lemma77HoldPrefixSignedEndpointEvent start n j ell
    · by_cases hlen : hs.length = n
      · have hmemLen :
            hs ∈ lemma77HoldPrefixSignedEndpointLengthEvent start n j ell :=
          ⟨hmem, hlen⟩
        simp [Set.indicator, hmem, hmemLen]
      · have hnotMemLen :
            hs ∉ lemma77HoldPrefixSignedEndpointLengthEvent start n j ell := by
          intro h
          exact hlen h.2
        simp [Set.indicator, hmem, hnotMemLen,
          lemma77HoldListPMF_toReal_eq_zero_of_length_ne hlen]
    · have hnotMemLen :
          hs ∉ lemma77HoldPrefixSignedEndpointLengthEvent start n j ell := by
        intro h
        exact hmem h.1
      simp [Set.indicator, hmem, hnotMemLen]
  · exact (tsum_subtype
      (lemma77HoldPrefixSignedEndpointLengthEvent start n j ell)
      (fun hs : List TaoSection7RenewalPoint =>
        (taoSection7HoldListPMF n hs).toReal)).symm

/-- Signed endpoint fibers with negative horizontal coordinate are empty. -/
theorem lemma77HoldPrefixSignedEndpointEvent_eq_empty_of_j_neg
    {start : TaoSection7RenewalPoint} {n : ℕ} {j ell : ℤ}
    (hj : j < 0) :
    lemma77HoldPrefixSignedEndpointEvent start n j ell = ∅ := by
  ext hs
  constructor
  · intro h
    have hnonneg : (0 : ℤ) ≤ j := by
      rw [← h.1]
      exact Int.natCast_nonneg _
    omega
  · intro h
    cases h

/-- Signed endpoint masses vanish at negative horizontal coordinate. -/
theorem lemma77HoldPrefixSignedEndpointMass_eq_zero_of_j_neg
    {start : TaoSection7RenewalPoint} {n : ℕ} {j ell : ℤ}
    (hj : j < 0) :
    lemma77HoldPrefixSignedEndpointMass start n j ell = 0 := by
  rw [lemma77HoldPrefixSignedEndpointMass,
    lemma77HoldPrefixSignedEndpointEvent_eq_empty_of_j_neg hj]
  simp

/-- An endpoint at horizontal displacement `j` cannot use more than `j` Hold steps. -/
theorem lemma77HoldPrefixSignedEndpointMass_eq_zero_of_lt_epoch
    (start : TaoSection7RenewalPoint) {n : ℕ} {j ell : ℤ}
    (hjn : j < (n : ℤ)) :
    lemma77HoldPrefixSignedEndpointMass start n j ell = 0 := by
  rw [lemma77HoldPrefixSignedEndpointMass_eq_tsum_length_fiber]
  letI : IsEmpty
      {hs : List TaoSection7RenewalPoint //
        hs ∈ lemma77HoldPrefixSignedEndpointLengthEvent start n j ell} :=
    ⟨by
      intro hs
      have hendpoint :
          (lemma77HoldPrefixIncrement start n hs.1 : ℤ) = j := hs.2.1.1
      rw [lemma77HoldPrefixIncrement_eq_horizontalDelta] at hendpoint
      have hge := lemma77HoldPrefixHorizontalDelta_ge_steps
        (q := n) (full := hs.1) (Nat.le_of_eq hs.2.2.symm)
      omega⟩
  simp

/-- Horizontal coordinate centered on Tao's potential line `j = s'/4`. -/
def lemma77ScalarCenteredHorizontal (j : ℤ) (s' : ℕ) : ℝ :=
  (j : ℝ) - (s' : ℝ) / 4

/-- Height-potential mass from Tao's summation over prefix lengths. -/
def lemma77HeightPotentialMass
    (start : TaoSection7RenewalPoint) (j : ℤ) (s' : ℕ) : ℝ :=
  ∑' n : ℕ, lemma77HoldPrefixSignedEndpointMass start n j (s' : ℤ)

/-- The epoch sum defining height-potential mass has finite support. -/
theorem lemma77HeightPotentialMass_summable
    (start : TaoSection7RenewalPoint) (j ell : ℤ) :
    Summable (fun n => lemma77HoldPrefixSignedEndpointMass start n j ell) := by
  by_cases hj : j < 0
  · have hz : ∀ n, lemma77HoldPrefixSignedEndpointMass start n j ell = 0 := by
      intro n
      exact lemma77HoldPrefixSignedEndpointMass_eq_zero_of_j_neg hj
    simp [hz]
  · apply summable_of_ne_finset_zero (s := Finset.range (j.toNat + 1))
    intro n hn
    apply lemma77HoldPrefixSignedEndpointMass_eq_zero_of_lt_epoch
    have hj_nonneg : 0 ≤ j := le_of_not_gt hj
    have hj_cast : (j.toNat : ℤ) = j := Int.toNat_of_nonneg hj_nonneg
    have hn_large : j.toNat < n := by
      simpa [Finset.mem_range] using hn
    omega

/-- Source-shaped height-potential kernel centered on `j = s'/4`. -/
def lemma77HeightPotentialKernel
    (C c : ℝ) (j : ℤ) (s' : ℕ) : ℝ :=
  C * ((1 + (s' : ℝ)) ^ (-(1 / 2 : ℝ))) *
    taoLemma22GaussianWeight (1 + s')
      (c * ((j : ℝ) - (s' : ℝ) / 4))

/-- Tao's one-dimensional `G_n` weight is nonnegative. -/
theorem taoLemma22GaussianWeight_nonneg (n : ℕ) (x : ℝ) :
    0 ≤ taoLemma22GaussianWeight n x := by
  unfold taoLemma22GaussianWeight
  split <;> positivity

/-- The height-potential kernel is nonnegative for nonnegative constant. -/
theorem lemma77HeightPotentialKernel_nonneg
    {C c : ℝ} (hC : 0 ≤ C) (j : ℤ) (s' : ℕ) :
    0 ≤ lemma77HeightPotentialKernel C c j s' := by
  unfold lemma77HeightPotentialKernel
  exact mul_nonneg (mul_nonneg hC (by positivity))
    (taoLemma22GaussianWeight_nonneg (1 + s')
      (c * ((j : ℝ) - (s' : ℝ) / 4)))

/-- Height-potential input surface for the summation before Tao's `(7.33)`. -/
structure Lemma77HeightPotentialInput (C c : ℝ) : Prop where
  constants : 0 ≤ C ∧ 0 < c
  height_potential :
    ∀ start j s',
      lemma77HeightPotentialMass start j s' ≤
        lemma77HeightPotentialKernel C c j s'

/-- Projection of the height-potential estimate from its explicit input surface. -/
theorem lemma77HeightPotentialMass_le_of_heightPotentialInput
    {C c : ℝ}
    (h : Lemma77HeightPotentialInput C c)
    (start : TaoSection7RenewalPoint) (j : ℤ) (s' : ℕ) :
    lemma77HeightPotentialMass start j s' ≤
      lemma77HeightPotentialKernel C c j s' :=
  h.height_potential start j s'

end TaoSection7Lemma77

end


end Tao
end Erdos1135
