/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Fourier.Section7SourceDomain
import Erdos1135Predecessor.Tao.Probability.Finite
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Tactic

namespace Erdos1135Predecessor

namespace Tao

open Finset

open scoped BigOperators

noncomputable def taoSection7Case3WindowWhiteCount
    (W : ℕ → Prop) [DecidablePred W] (P : ℕ) : ℕ :=
  (Finset.range P).sum fun p => if W p then 1 else 0

noncomputable def taoSection7Case3PositiveWhiteCount
    (W : ℕ → Prop) [DecidablePred W] (t : ℕ) : ℕ :=
  (Finset.Icc 1 t).sum fun p => if W p then 1 else 0

theorem taoSection7Case3_positiveOffsets_subset_window
    {P t : ℕ} (ht : t < P) :
    Finset.Icc 1 t ⊆ Finset.range P := by
  intro p hp
  exact Finset.mem_range.2 (lt_of_le_of_lt (Finset.mem_Icc.1 hp).2 ht)

theorem taoSection7Case3_positiveWhiteCount_le_window
    (W : ℕ → Prop) [DecidablePred W] {P t : ℕ} (ht : t < P) :
    taoSection7Case3PositiveWhiteCount W t ≤
      taoSection7Case3WindowWhiteCount W P := by
  unfold taoSection7Case3PositiveWhiteCount taoSection7Case3WindowWhiteCount
  exact Finset.sum_le_sum_of_subset
    (taoSection7Case3_positiveOffsets_subset_window ht)

theorem taoSection7Case3_low_window_forces_nonwhite_in_block
    (W : ℕ → Prop) [DecidablePred W] {P start threshold : ℕ}
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hblock : start + threshold < P) :
    ∃ q : ℕ, q ∈ Finset.Icc start (start + threshold) ∧ ¬ W q := by
  by_contra hnone
  have hall : ∀ q : ℕ, q ∈ Finset.Icc start (start + threshold) → W q := by
    intro q hq
    by_contra hW
    exact hnone ⟨q, hq, hW⟩
  let f : ℕ → ℕ := fun q => if W q then 1 else 0
  have hsub : Finset.Icc start (start + threshold) ⊆ Finset.range P := by
    intro q hq
    exact Finset.mem_range.2 (lt_of_le_of_lt (Finset.mem_Icc.1 hq).2 hblock)
  have hsum_card :
      (Finset.Icc start (start + threshold)).sum f =
        (Finset.Icc start (start + threshold)).card := by
    calc
      (Finset.Icc start (start + threshold)).sum f =
          (Finset.Icc start (start + threshold)).sum
            (fun _q : ℕ => (1 : ℕ)) := by
            refine Finset.sum_congr rfl ?_
            intro q hq
            simp [f, hall q hq]
      _ = (Finset.Icc start (start + threshold)).card := by
        simp
  have hcard :
      (Finset.Icc start (start + threshold)).card = threshold + 1 := by
    rw [Nat.card_Icc]
    omega
  have hle_window :
      (Finset.Icc start (start + threshold)).sum f ≤
        taoSection7Case3WindowWhiteCount W P := by
    unfold taoSection7Case3WindowWhiteCount
    exact Finset.sum_le_sum_of_subset hsub
  have hbad : threshold + 1 ≤ threshold := by
    calc
      threshold + 1 =
          (Finset.Icc start (start + threshold)).sum f := by
            rw [hsum_card, hcard]
      _ ≤ taoSection7Case3WindowWhiteCount W P := hle_window
      _ ≤ threshold := hlow
  omega

def taoSection7Case3LargeTriangleEvent
    (pointAt : ℕ → TaoSection7Point)
    (family : Set TaoSection7Triangle)
    (p : ℕ) (s' : ℝ) : Prop :=
  ∃ Δ : TaoSection7Triangle, Δ ∈ family ∧ Δ.Mem (pointAt p) ∧ s' ≤ Δ.size

noncomputable def taoSection7Case3LargeTriangleBoundWithBase
    (base : ℝ) (A p : ℕ) : ℝ :=
  base ^ A * (1 + (p : ℝ)) ^ 3

def TaoSection7Case3EStarUsedOffsetAdmissible
    (m p : ℕ) (s' : ℝ) : Prop :=
  (p : ℝ) ≤ Real.rpow (m : ℝ) ((1 : ℝ) / 10) ∧
    1 ≤ s' ∧
      s' ≤ Real.rpow (m : ℝ) ((2 : ℝ) / 5)

theorem taoSection7SourceBlackPoint_of_not_sourceWhitePoint
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {p : TaoSection7Point}
    (hnotWhite : ¬ taoSection7SourceWhitePoint n xi epsilon p) :
    taoSection7SourceBlackPoint n xi epsilon p := by
  unfold taoSection7SourceWhitePoint at hnotWhite
  unfold taoSection7SourceBlackPoint
  by_contra hnotBlack
  exact hnotWhite
    ((taoSection7White_iff_not_black epsilon
      (taoSection7ThetaResidue n xi p.j p.l)).2 hnotBlack)

theorem taoSection7SourceBlackInDomain_of_not_sourceWhitePoint
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {p : TaoSection7Point}
    (hdomain : taoSection7SourcePointInDomain J p)
    (hnotWhite : ¬ taoSection7SourceWhitePoint n xi epsilon p) :
    taoSection7SourceBlackInDomain n xi epsilon J p :=
  ⟨hdomain, taoSection7SourceBlackPoint_of_not_sourceWhitePoint hnotWhite⟩

theorem taoSection7Case3_low_window_produces_source_triangle_offset
    (W : ℕ → Prop) [DecidablePred W]
    (pointAt : ℕ → TaoSection7Point)
    {n J : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {family : Set TaoSection7Triangle} {P start threshold : ℕ}
    (hlow : taoSection7Case3WindowWhiteCount W P ≤ threshold)
    (hblock : start + threshold < P)
    (hWwhite :
      ∀ q : ℕ, q ∈ Finset.Icc start (start + threshold) →
        (W q ↔ taoSection7SourceWhitePoint n xi epsilon (pointAt q)))
    (hdomain :
      ∀ q : ℕ, q ∈ Finset.Icc start (start + threshold) →
        taoSection7SourcePointInDomain J (pointAt q))
    (hcover :
      TaoSection7TriangleFamilyCoverBlack
        (taoSection7SourceBlackInDomain n xi epsilon J) family) :
    ∃ q : ℕ, q ∈ Finset.Icc start (start + threshold) ∧ ¬ W q ∧
      ∃ Δ : TaoSection7Triangle, Δ ∈ family ∧ Δ.Mem (pointAt q) := by
  rcases taoSection7Case3_low_window_forces_nonwhite_in_block
      W hlow hblock with ⟨q, hq, hnotW⟩
  refine ⟨q, hq, hnotW, ?_⟩
  exact (hcover (pointAt q)).1
    (taoSection7SourceBlackInDomain_of_not_sourceWhitePoint
      (hdomain q hq)
      (by
        intro hwhite
        exact hnotW ((hWwhite q hq).2 hwhite)))

def taoSection7Case3HeightExitBound
    (gapBound : ℕ → ℕ) (q : ℕ) : ℕ :=
  q + gapBound q

def taoSection7Case3ExitGapBoundWithBase (base A q : ℕ) : ℕ :=
  10 * base ^ A * (q + 1) ^ 3

theorem taoSection7Case3ExitGapBoundWithBase_mono (base A : ℕ) :
    Monotone (taoSection7Case3ExitGapBoundWithBase base A) := by
  intro q r hqr
  dsimp [taoSection7Case3ExitGapBoundWithBase]
  gcongr

theorem taoSection7Case3_one_le_ten_mul_log_two :
    (1 : ℝ) ≤ 10 * Real.log 2 := by
  have hlog : (1 / 10 : ℝ) < Real.log 2 :=
    (by norm_num : (1 / 10 : ℝ) < 0.6931471803).trans
      Real.log_two_gt_d9
  nlinarith

theorem taoSection7Case3_exitGapBoundWithBase_real_eq
    (base A q : ℕ) :
    (taoSection7Case3ExitGapBoundWithBase base A q : ℝ) =
      10 * taoSection7Case3LargeTriangleBoundWithBase (base : ℝ) A q := by
  simp [taoSection7Case3ExitGapBoundWithBase,
    taoSection7Case3LargeTriangleBoundWithBase]
  ring

theorem taoSection7Case3_largeTriangleBoundWithBase_le_exitGapBoundWithBase_log_two
    (base A q : ℕ) :
    taoSection7Case3LargeTriangleBoundWithBase (base : ℝ) A q ≤
      (taoSection7Case3ExitGapBoundWithBase base A q : ℝ) * Real.log 2 := by
  have hnonneg :
      0 ≤ taoSection7Case3LargeTriangleBoundWithBase (base : ℝ) A q := by
    simp [taoSection7Case3LargeTriangleBoundWithBase]
    positivity
  have hscale :
      taoSection7Case3LargeTriangleBoundWithBase (base : ℝ) A q ≤
        taoSection7Case3LargeTriangleBoundWithBase (base : ℝ) A q *
          (10 * Real.log 2) := by
    calc
      taoSection7Case3LargeTriangleBoundWithBase (base : ℝ) A q =
          taoSection7Case3LargeTriangleBoundWithBase (base : ℝ) A q * 1 := by
            ring
      _ ≤
          taoSection7Case3LargeTriangleBoundWithBase (base : ℝ) A q *
            (10 * Real.log 2) :=
          mul_le_mul_of_nonneg_left
            taoSection7Case3_one_le_ten_mul_log_two hnonneg
  calc
    taoSection7Case3LargeTriangleBoundWithBase (base : ℝ) A q
        ≤
          taoSection7Case3LargeTriangleBoundWithBase (base : ℝ) A q *
            (10 * Real.log 2) := hscale
    _ = (taoSection7Case3ExitGapBoundWithBase base A q : ℝ) *
          Real.log 2 := by
      rw [taoSection7Case3_exitGapBoundWithBase_real_eq]
      ring

structure TaoSection7Case3RecurrenceScale
    (bound : ℕ → ℝ) (gapBound : ℕ → ℕ) : Prop where
  gap_mono : Monotone gapBound
  sufficient : ∀ q, bound q ≤ (gapBound q : ℝ) * Real.log 2

theorem taoSection7Case3RecurrenceScale_baseKcut
    (base Kcut : ℕ) :
    TaoSection7Case3RecurrenceScale
      (taoSection7Case3LargeTriangleBoundWithBase (base : ℝ) Kcut)
      (taoSection7Case3ExitGapBoundWithBase base Kcut) where
  gap_mono := taoSection7Case3ExitGapBoundWithBase_mono base Kcut
  sufficient :=
    taoSection7Case3_largeTriangleBoundWithBase_le_exitGapBoundWithBase_log_two
      base Kcut

def taoSection7Case3LaterSearchStart
    (gapBound : ℕ → ℕ) (q : ℕ) : ℕ :=
  taoSection7Case3HeightExitBound gapBound q + 1

def taoSection7Case3LaterSearchBound
    (gapBound : ℕ → ℕ) (threshold q : ℕ) : ℕ :=
  taoSection7Case3LaterSearchStart gapBound q + threshold

def taoSection7Case3BaseKcutNextBound (base Kcut T q : ℕ) : ℕ :=
  taoSection7Case3LaterSearchBound
    (taoSection7Case3ExitGapBoundWithBase base Kcut) T q

theorem taoSection7Case3BaseKcutNextBound_mono (base Kcut T : ℕ) :
    Monotone (taoSection7Case3BaseKcutNextBound base Kcut T) := by
  intro q r hqr
  have hgap :
      taoSection7Case3ExitGapBoundWithBase base Kcut q ≤
        taoSection7Case3ExitGapBoundWithBase base Kcut r :=
    taoSection7Case3ExitGapBoundWithBase_mono base Kcut hqr
  dsimp [taoSection7Case3BaseKcutNextBound,
    taoSection7Case3LaterSearchBound,
    taoSection7Case3LaterSearchStart,
    taoSection7Case3HeightExitBound]
  omega

theorem taoSection7Case3_le_baseKcutNextBound (base Kcut T q : ℕ) :
    q ≤ taoSection7Case3BaseKcutNextBound base Kcut T q := by
  dsimp [taoSection7Case3BaseKcutNextBound,
    taoSection7Case3LaterSearchBound,
    taoSection7Case3LaterSearchStart,
    taoSection7Case3HeightExitBound]
  omega

def taoSection7Case3IterateRoom
    (Next : ℕ → ℕ) (R start P : ℕ) : Prop :=
  (Next^[R]) start < P

theorem taoSection7Case3_le_iterate_of_le_self
    (Next : ℕ → ℕ) (hnext : ∀ q : ℕ, q ≤ Next q)
    (R start : ℕ) :
    start ≤ (Next^[R]) start := by
  induction R with
  | zero =>
      simp
  | succ R ih =>
      rw [Function.iterate_succ_apply']
      exact le_trans ih (hnext _)

theorem taoSection7Case3_iterate_le_iterate_of_le
    (Next : ℕ → ℕ) (hnext : ∀ q : ℕ, q ≤ Next q)
    {i R start : ℕ} (hi : i ≤ R) :
    (Next^[i]) start ≤ (Next^[R]) start := by
  obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hi
  subst R
  rw [Nat.add_comm i k, Function.iterate_add_apply]
  exact
    taoSection7Case3_le_iterate_of_le_self
      Next hnext k ((Next^[i]) start)

theorem taoSection7Case3_baseKcutNextBound_iterate_le_iterate_of_le
    {base Kcut T i R start : ℕ} (hi : i ≤ R) :
    ((taoSection7Case3BaseKcutNextBound base Kcut T)^[i]) start ≤
      ((taoSection7Case3BaseKcutNextBound base Kcut T)^[R]) start :=
  taoSection7Case3_iterate_le_iterate_of_le
    (taoSection7Case3BaseKcutNextBound base Kcut T)
    (taoSection7Case3_le_baseKcutNextBound base Kcut T) hi

def taoSection7Case3BaseKcutNextBoundIterateRoom
    (base Kcut T R start P : ℕ) : Prop :=
  taoSection7Case3IterateRoom
    (taoSection7Case3BaseKcutNextBound base Kcut T) R start P

theorem taoSection7Case3_baseKcutNextBound_iterate_lt_of_iterateRoom
    {base Kcut T R start P i : ℕ}
    (hroom :
      taoSection7Case3BaseKcutNextBoundIterateRoom
        base Kcut T R start P)
    (hi : i ≤ R) :
    ((taoSection7Case3BaseKcutNextBound base Kcut T)^[i]) start < P :=
  lt_of_le_of_lt
    (taoSection7Case3_baseKcutNextBound_iterate_le_iterate_of_le
      (base := base) (Kcut := Kcut) (T := T) (start := start) hi)
    hroom

def taoSection7Case3LowWhite
    (W : ℕ → Prop) [DecidablePred W] (P T : ℕ) : Prop :=
  taoSection7Case3WindowWhiteCount W P ≤ T

noncomputable def taoSection7Case3LowWhiteEvent
    {Ω : Type*} (W : Ω → ℕ → Prop) [∀ ω, DecidablePred (W ω)]
    (P T : ℕ) : Set Ω :=
  {ω | taoSection7Case3LowWhite (W ω) P T}

theorem taoSection7Case3WindowWhiteCount_succ_le_of_not_lowWhiteEvent
    {Ω : Type*} {W : Ω → ℕ → Prop} [∀ ω, DecidablePred (W ω)]
    {P T : ℕ} {ω : Ω}
    (hnotLow : ω ∉ taoSection7Case3LowWhiteEvent W P T) :
    T + 1 ≤ taoSection7Case3WindowWhiteCount (W ω) P := by
  have hnot :
      ¬ taoSection7Case3WindowWhiteCount (W ω) P ≤ T := by
    simpa [taoSection7Case3LowWhiteEvent, taoSection7Case3LowWhite]
      using hnotLow
  omega

theorem taoSection7Case3_inner756_nat_Aweight_prefactor_le
    {Aweight : ℕ} (hA : 3 ≤ Aweight) :
    1000 * Aweight ^ 2 * 10 ^ Aweight ≤ 9 * 256 ^ Aweight := by
  induction Aweight, hA using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
      have hratio : 10 * (n + 1) ^ 2 ≤ 256 * n ^ 2 := by
        nlinarith [sq_nonneg (n : ℤ)]
      calc
        1000 * (n + 1) ^ 2 * 10 ^ (n + 1)
            = (1000 * 10 ^ n) * (10 * (n + 1) ^ 2) := by
              ring_nf
        _ ≤ (1000 * 10 ^ n) * (256 * n ^ 2) :=
              Nat.mul_le_mul_left _ hratio
        _ = 256 * (1000 * n ^ 2 * 10 ^ n) := by
              ring
        _ ≤ 256 * (9 * 256 ^ n) := Nat.mul_le_mul_left 256 ih
        _ = 9 * 256 ^ (n + 1) := by
              ring_nf

theorem taoSection7Case3_inner756_AweightPrefactor_Kcut_Ebudget
    {Aweight Kcut : ℕ}
    (hA : 3 ≤ Aweight) (hK : 4 * Aweight ≤ Kcut) :
    (Aweight : ℝ) ^ 2 / ((4 : ℝ) ^ Kcut) ≤
      (9 : ℝ) / (1000 * (10 : ℝ) ^ Aweight) := by
  have hcore :=
    taoSection7Case3_inner756_nat_Aweight_prefactor_le
      (Aweight := Aweight) hA
  have hpow256 : 256 ^ Aweight = 4 ^ (4 * Aweight) := by
    rw [show 256 = 4 ^ 4 by norm_num, pow_mul]
  have h4mono : 4 ^ (4 * Aweight) ≤ 4 ^ Kcut :=
    Nat.pow_le_pow_right (by decide) hK
  have hnat : 1000 * Aweight ^ 2 * 10 ^ Aweight ≤ 9 * 4 ^ Kcut := by
    calc
      1000 * Aweight ^ 2 * 10 ^ Aweight ≤ 9 * 256 ^ Aweight := hcore
      _ = 9 * 4 ^ (4 * Aweight) := by rw [hpow256]
      _ ≤ 9 * 4 ^ Kcut := Nat.mul_le_mul_left 9 h4mono
  have hreal :
      (1000 : ℝ) * (Aweight : ℝ) ^ 2 * (10 : ℝ) ^ Aweight ≤
        (9 : ℝ) * (4 : ℝ) ^ Kcut := by
    exact_mod_cast hnat
  have h4pos : 0 < (4 : ℝ) ^ Kcut := pow_pos (by norm_num) Kcut
  have hdenpos : 0 < (1000 : ℝ) * (10 : ℝ) ^ Aweight := by positivity
  rw [div_le_div_iff₀ h4pos hdenpos]
  simpa [mul_assoc, mul_left_comm, mul_comm] using hreal

theorem taoSection7Case3_inner756_AweightPrefactor_Kcut_FSlack_budget
    {Aweight Kcut : ℕ}
    (hA : 3 ≤ Aweight) (hK : 4 * Aweight ≤ Kcut) :
    (Aweight : ℝ) ^ 2 / ((4 : ℝ) ^ Kcut) +
        1 / ((10 : ℝ) ^ (Aweight + 3)) ≤
      1 / ((10 : ℝ) ^ (Aweight + 2)) := by
  have hE :=
    taoSection7Case3_inner756_AweightPrefactor_Kcut_Ebudget
      (Aweight := Aweight) (Kcut := Kcut) hA hK
  have hden :
      (1000 : ℝ) * (10 : ℝ) ^ Aweight =
        (10 : ℝ) ^ (Aweight + 3) := by
    rw [show Aweight + 3 = 3 + Aweight by omega, pow_add]
    norm_num
  have hsum :
      (9 : ℝ) / (1000 * (10 : ℝ) ^ Aweight) +
          1 / ((10 : ℝ) ^ (Aweight + 3)) =
        1 / ((10 : ℝ) ^ (Aweight + 2)) := by
    rw [hden]
    have h10 :
        (10 : ℝ) ^ (Aweight + 3) =
          (10 : ℝ) ^ (Aweight + 2) * 10 := by
      rw [show Aweight + 3 = Aweight + 2 + 1 by omega, pow_succ]
    rw [h10]
    field_simp [pow_ne_zero _ (by norm_num : (10 : ℝ) ≠ 0)]
    ring
  calc
    (Aweight : ℝ) ^ 2 / ((4 : ℝ) ^ Kcut) +
        1 / ((10 : ℝ) ^ (Aweight + 3))
        ≤ (9 : ℝ) / (1000 * (10 : ℝ) ^ Aweight) +
          1 / ((10 : ℝ) ^ (Aweight + 3)) := by
            exact add_le_add hE le_rfl
    _ = 1 / ((10 : ℝ) ^ (Aweight + 2)) := hsum

end Tao

end Erdos1135Predecessor
