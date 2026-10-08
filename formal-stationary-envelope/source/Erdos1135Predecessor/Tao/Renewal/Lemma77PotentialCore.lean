/-
Compatibility modification, 8 October 2026: proof-tactic syntax and unused binder names only.
See provenance/envelope-linter-patches.json for exact source hashes and patches.
-/
/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.HoldIID
import Erdos1135Predecessor.Tao.Renewal.RenewalPathBasic
import Mathlib.Tactic

namespace Erdos1135Predecessor

namespace Tao

open scoped BigOperators

noncomputable section

namespace TaoSection7Lemma77

def prefixIncrement
    {Ω : Type*}
    (start : Ω → TaoSection7RenewalPoint)
    (K : Ω → ℕ)
    (pre : Ω → List TaoSection7RenewalPoint)
    (ω : Ω) : ℕ :=
  ((taoSection7RenewalPathPoint (start ω) (pre ω) (K ω)).j : ℕ) -
    ((start ω).j : ℕ)

def prefixVerticalIncrement
    {Ω : Type*}
    (start : Ω → TaoSection7RenewalPoint)
    (K : Ω → ℕ)
    (pre : Ω → List TaoSection7RenewalPoint)
    (ω : Ω) : ℤ :=
  (taoSection7RenewalPathPoint (start ω) (pre ω) (K ω)).l -
    (start ω).l

def taoLemma22GaussianWeight (n : ℕ) (x : ℝ) : ℝ :=
  if n = 0 then
    Real.exp (-|x|)
  else
    Real.exp (-(x ^ 2 / (n : ℝ))) + Real.exp (-|x|)

def lemma77HoldPrefixIncrement
    (start : TaoSection7RenewalPoint)
    (n : ℕ)
    (hs : List TaoSection7RenewalPoint) : ℕ :=
  prefixIncrement
    (fun _ : List TaoSection7RenewalPoint => start)
    (fun _ => n)
    (fun hs => hs)
    hs

def lemma77HoldPrefixVerticalIncrement
    (start : TaoSection7RenewalPoint)
    (n : ℕ)
    (hs : List TaoSection7RenewalPoint) : ℤ :=
  prefixVerticalIncrement
    (fun _ : List TaoSection7RenewalPoint => start)
    (fun _ => n)
    (fun hs => hs)
    hs

def lemma77HoldPrefixHorizontalDelta : ℕ → List TaoSection7RenewalPoint → ℕ
  | 0, _ => 0
  | _n + 1, [] => 0
  | n + 1, h :: hs => (h.j : ℕ) + lemma77HoldPrefixHorizontalDelta n hs

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

theorem lemma77HoldPrefixIncrement_eq_horizontalDelta
    (start : TaoSection7RenewalPoint) (n : ℕ)
    (hs : List TaoSection7RenewalPoint) :
    lemma77HoldPrefixIncrement start n hs =
      lemma77HoldPrefixHorizontalDelta n hs := by
  simp [lemma77HoldPrefixIncrement, prefixIncrement,
    lemma77RenewalPathPoint_j_eq_start_add_horizontalDelta]

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

def lemma77HoldPrefixSignedEndpointEvent
    (start : TaoSection7RenewalPoint) (n : ℕ) (j ell : ℤ) :
    Set (List TaoSection7RenewalPoint) :=
  {hs |
    (lemma77HoldPrefixIncrement start n hs : ℤ) = j ∧
      lemma77HoldPrefixVerticalIncrement start n hs = ell}

def lemma77HoldPrefixSignedEndpointMass
    (start : TaoSection7RenewalPoint) (n : ℕ) (j ell : ℤ) : ℝ :=
  ((taoSection7HoldListPMF n).toOuterMeasure
      (lemma77HoldPrefixSignedEndpointEvent start n j ell)).toReal

theorem lemma77HoldListPMF_apply_eq_zero_of_length_ne
    {n : ℕ} {hs : List TaoSection7RenewalPoint}
    (h : hs.length ≠ n) :
    taoSection7HoldListPMF n hs = 0 :=
  taoSection7HoldListPMF_apply_eq_zero_of_length_ne n hs h

theorem lemma77HoldListPMF_toReal_eq_zero_of_length_ne
    {n : ℕ} {hs : List TaoSection7RenewalPoint}
    (h : hs.length ≠ n) :
    (taoSection7HoldListPMF n hs).toReal = 0 := by
  rw [lemma77HoldListPMF_apply_eq_zero_of_length_ne h]
  simp

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

def lemma77HoldPrefixSignedEndpointLengthEvent
    (start : TaoSection7RenewalPoint) (n : ℕ) (j ell : ℤ) :
    Set (List TaoSection7RenewalPoint) :=
  {hs | hs ∈ lemma77HoldPrefixSignedEndpointEvent start n j ell ∧ hs.length = n}

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

theorem lemma77HoldPrefixSignedEndpointMass_eq_zero_of_j_neg
    {start : TaoSection7RenewalPoint} {n : ℕ} {j ell : ℤ}
    (hj : j < 0) :
    lemma77HoldPrefixSignedEndpointMass start n j ell = 0 := by
  rw [lemma77HoldPrefixSignedEndpointMass,
    lemma77HoldPrefixSignedEndpointEvent_eq_empty_of_j_neg hj]
  simp

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

def lemma77ScalarCenteredHorizontal (j : ℤ) (s' : ℕ) : ℝ :=
  (j : ℝ) - (s' : ℝ) / 4

def lemma77HeightPotentialMass
    (start : TaoSection7RenewalPoint) (j : ℤ) (s' : ℕ) : ℝ :=
  ∑' n : ℕ, lemma77HoldPrefixSignedEndpointMass start n j (s' : ℤ)

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

def lemma77HeightPotentialKernel
    (C c : ℝ) (j : ℤ) (s' : ℕ) : ℝ :=
  C * ((1 + (s' : ℝ)) ^ (-(1 / 2 : ℝ))) *
    taoLemma22GaussianWeight (1 + s')
      (c * ((j : ℝ) - (s' : ℝ) / 4))

theorem taoLemma22GaussianWeight_nonneg (n : ℕ) (x : ℝ) :
    0 ≤ taoLemma22GaussianWeight n x := by
  unfold taoLemma22GaussianWeight
  split <;> positivity

theorem lemma77HeightPotentialKernel_nonneg
    {C c : ℝ} (hC : 0 ≤ C) (j : ℤ) (s' : ℕ) :
    0 ≤ lemma77HeightPotentialKernel C c j s' := by
  unfold lemma77HeightPotentialKernel
  exact mul_nonneg (mul_nonneg hC (by positivity))
    (taoLemma22GaussianWeight_nonneg (1 + s')
      (c * ((j : ℝ) - (s' : ℝ) / 4)))

structure Lemma77HeightPotentialInput (C c : ℝ) : Prop where
  constants : 0 ≤ C ∧ 0 < c
  height_potential :
    ∀ start j s',
      lemma77HeightPotentialMass start j s' ≤
        lemma77HeightPotentialKernel C c j s'

end TaoSection7Lemma77

end

end Tao

end Erdos1135Predecessor
