/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.PathGrowth
import Erdos1135Predecessor.Tao.Renewal.Prop78Case3CutoffAlignment
import Mathlib.Tactic

namespace Erdos1135Predecessor

namespace Tao

def TaoSection7Case3AfterTriangleHit
    (pointAt : ℕ → TaoSection7Point)
    (family : Set TaoSection7Triangle)
    (old : TaoSection7Triangle) (t : ℕ) : Prop :=
  old.cornerL < (pointAt t).l ∧
    ∃ Γ : TaoSection7Triangle, Γ ∈ family ∧ Γ.Mem (pointAt t)

def TaoSection7Case3FirstAfterTriangleHitFrom
    (pointAt : ℕ → TaoSection7Point)
    (family : Set TaoSection7Triangle)
    (old : TaoSection7Triangle) (q t : ℕ) : Prop :=
  q < t ∧
    TaoSection7Case3AfterTriangleHit pointAt family old t ∧
      ∀ s : ℕ, q < s → s < t →
        ¬ TaoSection7Case3AfterTriangleHit pointAt family old s

theorem taoSection7Case3_afterTriangleHit_new_triangle
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {old : TaoSection7Triangle} {t : ℕ}
    (hhit : TaoSection7Case3AfterTriangleHit pointAt family old t) :
    ∃ Γ : TaoSection7Triangle,
      Γ ∈ family ∧ Γ.Mem (pointAt t) ∧ Γ ≠ old := by
  rcases hhit with ⟨hexit_height, Γ, hΓ, hmemΓ⟩
  refine ⟨Γ, hΓ, hmemΓ, ?_⟩
  intro hΓ_eq
  subst hΓ_eq
  exact taoSection7Case3_not_mem_of_cornerL_lt hexit_height hmemΓ

def taoSection7Lemma710CurrentM (n : ℕ) (p : TaoSection7Point) : ℝ :=
  ((n / 2 - (p.j : ℕ) : ℕ) : ℝ)

theorem taoSection7Lemma710_verticalDepth_le_log9_div_log2_mul_currentM_of_domain
    {n : ℕ} {old : TaoSection7Triangle} {p : TaoSection7Point}
    (hmem : old.Mem p)
    (hdomain : taoSection7SourcePointInDomain (n / 2) p)
    (hright :
      TaoSection7TriangleRightEdgeInStrip ((n / 2 : ℕ) : ℝ) old) :
    ((old.verticalDepth p : ℤ) : ℝ) ≤
      (Real.log 9 / Real.log 2) * taoSection7Lemma710CurrentM n p := by
  refine
    TaoSection7Triangle.verticalDepth_le_log9_div_log2_mul_rightGap_of_mem_rightEdge
      (old := old) (p := p) (S := ((old.verticalDepth p : ℤ) : ℝ))
      (M := taoSection7Lemma710CurrentM n p) (cutoff := ((n / 2 : ℕ) : ℝ))
      hmem rfl hright ?_
  unfold taoSection7Lemma710CurrentM
  dsimp [TaoSection7Point.jReal]
  rw [Nat.cast_sub hdomain]

structure TaoSection7Lemma710CurrentScaleControls
    (n : ℕ) (old : TaoSection7Triangle) (p : TaoSection7Point)
    (M S : ℝ) : Prop where
  M_def : M = taoSection7Lemma710CurrentM n p
  S_def : S = ((old.verticalDepth p : ℤ) : ℝ)
  domain : taoSection7SourcePointInDomain (n / 2) p
  M_large : 1 < M
  logM_pos : 0 < Real.log M
  S_nonneg : 0 ≤ S
  hMlower : M / (Real.log M)^2 ≤ S
  upper_752 : S ≤ (Real.log 9 / Real.log 2) * M

namespace TaoSection7Lemma710CurrentScaleControls

end TaoSection7Lemma710CurrentScaleControls

namespace TaoSection7Case3AllWindowSourceFacts

end TaoSection7Case3AllWindowSourceFacts

namespace TaoSection7Case3RecursiveEncounterChain

end TaoSection7Case3RecursiveEncounterChain

namespace TaoSection7Case3RecursiveFirstHitChain

def tR? : List (ℕ × TaoSection7Triangle) → ℕ → Option ℕ
  | [], _ => none
  | _step :: _rest, 0 => none
  | step :: _rest, 1 => some step.1
  | _step :: rest, R + 2 => tR? rest (R + 1)

end TaoSection7Case3RecursiveFirstHitChain

def TaoSection7Case3TriangleHit
    (pointAt : ℕ → TaoSection7Point)
    (family : Set TaoSection7Triangle) (t : ℕ) : Prop :=
  ∃ Γ : TaoSection7Triangle, Γ ∈ family ∧ Γ.Mem (pointAt t)

structure TaoSection7Case3StoppingTransition
    (pointAt : ℕ → TaoSection7Point)
    (family : Set TaoSection7Triangle)
    (q : ℕ) (old : TaoSection7Triangle)
    (first : ℕ) (Γ : TaoSection7Triangle) : Prop where
  first_after_exit :
    TaoSection7Case3FirstAfterTriangleHitFrom pointAt family old q first
  new_mem_family : Γ ∈ family
  new_mem : Γ.Mem (pointAt first)
  new_ne_old : Γ ≠ old

theorem taoSection7Case3_firstAfterTriangleHitFrom_time_eq
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {old : TaoSection7Triangle} {q first first' : ℕ}
    (hfirst :
      TaoSection7Case3FirstAfterTriangleHitFrom
        pointAt family old q first)
    (hfirst' :
      TaoSection7Case3FirstAfterTriangleHitFrom
        pointAt family old q first') :
    first = first' := by
  by_contra hne
  by_cases hlt : first < first'
  · exact hfirst'.2.2 first hfirst.1 hlt hfirst.2.1
  · have hgt : first' < first := by omega
    exact hfirst.2.2 first' hfirst'.1 hgt hfirst'.2.1

theorem taoSection7Triangle_eq_of_familyPairwiseDisjoint_mem
    {family : Set TaoSection7Triangle}
    {Δ Γ : TaoSection7Triangle} {p : TaoSection7Point}
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hΔ : Δ ∈ family) (hΓ : Γ ∈ family)
    (hΔ_mem : Δ.Mem p) (hΓ_mem : Γ.Mem p) :
    Δ = Γ := by
  by_contra hne
  exact
    TaoSection7TriangleFamilyPairwiseDisjoint.no_common_mem
      hpair hΔ hΓ hne hΔ_mem hΓ_mem

namespace TaoSection7Case3StoppingTransition

theorem pair_eq_of_pairwiseDisjoint
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {q : ℕ} {old Γ Γ' : TaoSection7Triangle}
    {first first' : ℕ}
    (hpair : TaoSection7TriangleFamilyPairwiseDisjoint family)
    (hstep :
      TaoSection7Case3StoppingTransition
        pointAt family q old first Γ)
    (hstep' :
      TaoSection7Case3StoppingTransition
        pointAt family q old first' Γ') :
    (first, Γ) = (first', Γ') := by
  have hfirst_eq : first = first' :=
    taoSection7Case3_firstAfterTriangleHitFrom_time_eq
      hstep.first_after_exit hstep'.first_after_exit
  subst hfirst_eq
  have hΓ_eq : Γ = Γ' :=
    taoSection7Triangle_eq_of_familyPairwiseDisjoint_mem
      hpair hstep.new_mem_family hstep'.new_mem_family
      hstep.new_mem hstep'.new_mem
  subst hΓ_eq
  rfl

end TaoSection7Case3StoppingTransition

namespace TaoSection7Case3InitialStoppingStep

end TaoSection7Case3InitialStoppingStep

namespace TaoSection7Case3FirstHitSourceProvenance

end TaoSection7Case3FirstHitSourceProvenance

namespace TaoSection7Case3FirstHitAcceptedTransition

end TaoSection7Case3FirstHitAcceptedTransition

namespace TaoSection7Case3StoppingTransition

end TaoSection7Case3StoppingTransition

inductive TaoSection7Case3StoppingTail
    (pointAt : ℕ → TaoSection7Point)
    (family : Set TaoSection7Triangle) :
    ℕ → TaoSection7Triangle → List (ℕ × TaoSection7Triangle) → Prop
  | nil (q : ℕ) (old : TaoSection7Triangle) :
      TaoSection7Case3StoppingTail pointAt family q old []
  | cons {q first : ℕ} {old Γ : TaoSection7Triangle}
      {rest : List (ℕ × TaoSection7Triangle)}
      (hstep :
        TaoSection7Case3StoppingTransition
          pointAt family q old first Γ)
      (htail :
        TaoSection7Case3StoppingTail pointAt family first Γ rest) :
      TaoSection7Case3StoppingTail
        pointAt family q old ((first, Γ) :: rest)

namespace TaoSection7Case3NoLaterBlackAfterExit

end TaoSection7Case3NoLaterBlackAfterExit

def TaoSection7Case3StoppingLast? :
    List (ℕ × TaoSection7Triangle) → Option (ℕ × TaoSection7Triangle)
  | [] => none
  | [step] => some step
  | _step :: rest => TaoSection7Case3StoppingLast? rest

namespace TaoSection7Case3StoppingTerminal

end TaoSection7Case3StoppingTerminal

namespace TaoSection7Case3RecursiveEncounterChain

end TaoSection7Case3RecursiveEncounterChain

namespace TaoSection7Case3StoppingTail

theorem head_step
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {q first : ℕ} {old Γ : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (htail :
      TaoSection7Case3StoppingTail
        pointAt family q old ((first, Γ) :: rest)) :
    TaoSection7Case3StoppingTransition pointAt family q old first Γ := by
  cases htail with
  | cons hstep _htail => exact hstep

theorem tail
    {pointAt : ℕ → TaoSection7Point}
    {family : Set TaoSection7Triangle}
    {q first : ℕ} {old Γ : TaoSection7Triangle}
    {rest : List (ℕ × TaoSection7Triangle)}
    (htail :
      TaoSection7Case3StoppingTail
        pointAt family q old ((first, Γ) :: rest)) :
    TaoSection7Case3StoppingTail pointAt family first Γ rest := by
  cases htail with
  | cons _hstep htail => exact htail

end TaoSection7Case3StoppingTail

namespace TaoSection7Case3StoppingPrefix

end TaoSection7Case3StoppingPrefix

namespace TaoSection7Case3SourceStoppingRun

def r (steps : List (ℕ × TaoSection7Triangle)) : ℕ :=
  steps.length

def tR? : List (ℕ × TaoSection7Triangle) → ℕ → Option ℕ
  | [], _ => none
  | _step :: _rest, 0 => none
  | step :: _rest, 1 => some step.1
  | _step :: rest, R + 2 => tR? rest (R + 1)

def HasAtLeast (steps : List (ℕ × TaoSection7Triangle)) (R : ℕ) : Prop :=
  R ≤ r steps

def HasTWithinWindow
    (steps : List (ℕ × TaoSection7Triangle)) (R P : ℕ) : Prop :=
  ∃ t : ℕ, tR? steps R = some t ∧ t < P

theorem tR?_some_length_le
    {steps : List (ℕ × TaoSection7Triangle)} {R tR : ℕ}
    (htR : tR? steps R = some tR) :
    R ≤ steps.length := by
  induction steps generalizing R tR with
  | nil =>
      cases R <;> simp [tR?] at htR
  | cons step rest ih =>
      cases R with
      | zero =>
          simp
      | succ Rpred =>
          cases Rpred with
          | zero =>
              simp
          | succ Rtail =>
              have hrest :
                  Rtail + 1 ≤ rest.length :=
                ih (R := Rtail + 1) (tR := tR) (by
                  simpa [tR?] using htR)
              simp
              omega

theorem tR?_isSome_pos
    {steps : List (ℕ × TaoSection7Triangle)} {R : ℕ}
    (h : (tR? steps R).isSome = true) :
    0 < R := by
  cases R with
  | zero =>
      cases steps <;> simp [tR?] at h
  | succ R =>
      exact Nat.succ_pos R

theorem hasTWithinWindow_of_hasAtLeast_all_ltP
    {steps : List (ℕ × TaoSection7Triangle)} {R P : ℕ}
    (hRpos : 0 < R)
    (hR : HasAtLeast steps R)
    (hall : ∀ step ∈ steps, step.1 < P) :
    HasTWithinWindow steps R P := by
  induction steps generalizing R with
  | nil =>
      simp [HasAtLeast, r] at hR
      omega
  | cons step rest ih =>
      cases R with
      | zero =>
          omega
      | succ Rpred =>
          cases Rpred with
          | zero =>
              refine ⟨step.1, ?_, ?_⟩
              · simp [tR?]
              · exact hall step (by simp)
          | succ Rtail =>
              have hRtail_pos : 0 < Rtail + 1 := by omega
              have hRtail :
                  HasAtLeast rest (Rtail + 1) := by
                simp [HasAtLeast, r] at hR ⊢
                omega
              have hall_tail : ∀ tailStep ∈ rest, tailStep.1 < P := by
                intro tailStep htailStep
                exact hall tailStep (by simp [htailStep])
              rcases ih hRtail_pos hRtail hall_tail with
                ⟨t, htR, htP⟩
              refine ⟨t, ?_, htP⟩
              simpa [tR?] using htR

namespace PrefixWindowData

end PrefixWindowData

end TaoSection7Case3SourceStoppingRun

namespace TaoSection7Case3ActualRunSourceIdentity

end TaoSection7Case3ActualRunSourceIdentity

namespace TaoSection7Case3ConstructedSourceStoppingRunData

end TaoSection7Case3ConstructedSourceStoppingRunData

namespace TaoSection7Case3StoppingPrefix

end TaoSection7Case3StoppingPrefix

namespace TaoSection7Case3PrefixRInputs

end TaoSection7Case3PrefixRInputs

namespace TaoSection7Case3ActualRunSourceIdentity

end TaoSection7Case3ActualRunSourceIdentity

namespace TaoSection7Case3IndexedRebasedSourceUpdateWithGap

end TaoSection7Case3IndexedRebasedSourceUpdateWithGap

namespace TaoSection7Case3OneStepRebasedSourceUpdateWithGap

end TaoSection7Case3OneStepRebasedSourceUpdateWithGap

namespace TaoSection7Case3ChosenActiveStepWithGap

end TaoSection7Case3ChosenActiveStepWithGap

namespace TaoSection7Case3ChosenActiveLocalUsedStepWithGap

end TaoSection7Case3ChosenActiveLocalUsedStepWithGap

namespace TaoSection7Case3BoundedLocalUsedTrace

end TaoSection7Case3BoundedLocalUsedTrace

namespace TaoSection7Case3ActualRunSourceIdentity

end TaoSection7Case3ActualRunSourceIdentity

namespace TaoSection7Case3StoppingTail

end TaoSection7Case3StoppingTail

namespace TaoSection7Case3StoppingPrefix

end TaoSection7Case3StoppingPrefix

namespace TaoSection7Case3SourceStoppingRun

namespace Lemma79MarkovSourceWhiteMinBound

end Lemma79MarkovSourceWhiteMinBound

namespace Lemma79RepairedTailOnRGeR

end Lemma79RepairedTailOnRGeR

namespace Lemma79SourceFSlackMomentPacket

end Lemma79SourceFSlackMomentPacket

namespace Lemma79MarkovSourceWhiteMinBoundInputs

end Lemma79MarkovSourceWhiteMinBoundInputs

end TaoSection7Case3SourceStoppingRun

namespace TaoSection7Case3ActualRunSourceIdentity

end TaoSection7Case3ActualRunSourceIdentity

namespace TaoSection7Case3SourceStoppingRun

namespace Lemma79SourceFSlackMomentPacket

end Lemma79SourceFSlackMomentPacket

end TaoSection7Case3SourceStoppingRun

namespace TaoSection7Case3ActiveSourceStateWithGap

end TaoSection7Case3ActiveSourceStateWithGap

namespace TaoSection7Case3ActiveSourceTraceWithGap

end TaoSection7Case3ActiveSourceTraceWithGap

end Tao

end Erdos1135Predecessor
