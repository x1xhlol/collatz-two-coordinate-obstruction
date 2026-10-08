/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

/-
Modified 2026-09-28 for the independent alpha = 2001/2000 replay of
Mazur's Proposition 1.11 formalization, pinned at ca3dd0d63920.
The changes are documented in alpha-2001-2000.patch and the replay report.
Original copyright and license notices are retained; see LICENSE and NOTICE.
-/

import Erdos1135SecondScale.Tao.Section5.Schedule
import Erdos1135SecondScale.Tao.Section5.PassLocationStepBack
import Erdos1135SecondScale.Tao.Syracuse.TruncatedValuationPacking

/-!
# Section 5 First-Passage Schedule

This leaf constructs the corrected finite schedule used before the
Proposition 5.2 event partition. The first-passage interval depends on the
source branch, while the step-back time, typicality rule, and target `EPrime`
depend only on the common threshold.

The power interior below replaces the printed additive interior. An additive
displacement of order `log(B)^0.8` is too small after taking a logarithm to
force the required passage-time margin of that same order.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

/-- Tao's common step-back time from equation (5.2). -/
noncomputable def taoSection5M0 (B : ℕ) : ℕ :=
  Nat.floor (((taoAlpha - 1) / 100) * Real.log B)

theorem taoSection5M0_eq_floor_log (B : ℕ) :
    taoSection5M0 B = Nat.floor (Real.log B / 200000) := by
  unfold taoSection5M0 taoAlpha
  congr 1
  ring

/-- The lower real endpoint of the branch-specific interval `I_y` in (5.9). -/
noncomputable def taoSection5PassLower
    (B : ℕ) (branch : TaoSection5SourceBranch) : ℝ :=
  Real.log (taoSection5SourceY B branch / (B : ℝ)) /
      Real.log (4 / 3 : ℝ) +
    Real.rpow (Real.log B) (4 / 5 : ℝ)

/-- The upper real endpoint of the branch-specific interval `I_y` in (5.9). -/
noncomputable def taoSection5PassUpper
    (B : ℕ) (branch : TaoSection5SourceBranch) : ℝ :=
  Real.log
      (Real.rpow (taoSection5SourceY B branch) taoAlpha / (B : ℝ)) /
      Real.log (4 / 3 : ℝ) -
    Real.rpow (Real.log B) (4 / 5 : ℝ)

/-- The inclusive natural first-passage times in the real interval `I_y`. -/
noncomputable def taoSection5PassTimes
    (B : ℕ) (branch : TaoSection5SourceBranch) : Finset ℕ :=
  Finset.Icc (Nat.ceil (taoSection5PassLower B branch))
    (Nat.floor (taoSection5PassUpper B branch))

theorem mem_taoSection5PassTimes_iff
    {B n : ℕ} {branch : TaoSection5SourceBranch} :
    n ∈ taoSection5PassTimes B branch ↔
      Nat.ceil (taoSection5PassLower B branch) ≤ n ∧
        n ≤ Nat.floor (taoSection5PassUpper B branch) := by
  simp [taoSection5PassTimes]

/-- The strict prefix-weight slack `log(B)^0.6` from equation (5.11). -/
noncomputable def taoSection5TypicalSlack (B : ℕ) : ℝ :=
  Real.rpow (Real.log B) (3 / 5 : ℝ)

/-- Tao's strict prefix typicality condition (5.11). -/
def taoSection5SourceTypicalTuple
    (B r : ℕ) (as : List ℕ+) : Prop :=
  as.length = r ∧
    ∀ j ≤ r,
      |(taoTupleWeight (as.take j) : ℝ) - 2 * (j : ℝ)| <
        taoSection5TypicalSlack B

/-- The closed enlargement of (5.11), matching the available tail boundary. -/
def taoSection5TypicalTuple
    (B r : ℕ) (as : List ℕ+) : Prop :=
  as.length = r ∧
    ∀ j ≤ r,
      |(taoTupleWeight (as.take j) : ℝ) - 2 * (j : ℝ)| ≤
        taoSection5TypicalSlack B

theorem TaoSection5SourceTypicalTuple.to_closed
    {B r : ℕ} {as : List ℕ+}
    (has : taoSection5SourceTypicalTuple B r as) :
    taoSection5TypicalTuple B r as :=
  ⟨has.1, fun j hj => (has.2 j hj).le⟩

/-- A strict natural cutoff large enough to contain every typical tuple. -/
noncomputable def taoSection5TypicalCutoff (B r : ℕ) : ℕ :=
  Nat.ceil (2 * (r : ℝ) + taoSection5TypicalSlack B) + 1

/-- The finite family `A^(r)` of all length-`r` tuples satisfying (5.11). -/
noncomputable def taoSection5TypicalTuples
    (B r : ℕ) : Finset (List ℕ+) := by
  classical
  exact
    (Finset.univ.image
      (BoundedValuationTuple.toList
        (n := r) (M := taoSection5TypicalCutoff B r))).filter
      (taoSection5TypicalTuple B r)

private theorem taoSection5TypicalTuple_weight_lt_cutoff
    {B r : ℕ} {as : List ℕ+}
    (has : taoSection5TypicalTuple B r as) :
    taoTupleWeight as < taoSection5TypicalCutoff B r := by
  have htake : as.take r = as := by
    rw [← has.1]
    exact List.take_length
  have hprefix := has.2 r le_rfl
  rw [htake] at hprefix
  have hreal :
      (taoTupleWeight as : ℝ) ≤
        2 * (r : ℝ) + taoSection5TypicalSlack B := by
    have hupper := (abs_le.mp hprefix).2
    linarith
  have hceilReal :
      (taoTupleWeight as : ℝ) ≤
        (Nat.ceil (2 * (r : ℝ) + taoSection5TypicalSlack B) : ℝ) :=
    hreal.trans (Nat.le_ceil _)
  have hceilNat :
      taoTupleWeight as ≤
        Nat.ceil (2 * (r : ℝ) + taoSection5TypicalSlack B) := by
    exact_mod_cast hceilReal
  unfold taoSection5TypicalCutoff
  omega

theorem mem_taoSection5TypicalTuples_iff
    {B r : ℕ} {as : List ℕ+} :
    as ∈ taoSection5TypicalTuples B r ↔
      taoSection5TypicalTuple B r as := by
  classical
  constructor
  · intro has
    exact (Finset.mem_filter.mp has).2
  · intro has
    apply Finset.mem_filter.mpr
    refine ⟨?_, has⟩
    apply Finset.mem_image.mpr
    let v : BoundedValuationTuple r (taoSection5TypicalCutoff B r) :=
      BoundedValuationTuple.ofList as has.1
        (taoSection5TypicalTuple_weight_lt_cutoff has)
    exact ⟨v, by simp [v]⟩

theorem TaoSection5TypicalTuple.take
    {B r : ℕ} {as : List ℕ+}
    (has : taoSection5TypicalTuple B r as) {j : ℕ} (hj : j ≤ r) :
    taoSection5TypicalTuple B j (as.take j) := by
  constructor
  · simp [List.length_take, has.1, Nat.min_eq_left hj]
  · intro i hi
    rw [List.take_take, Nat.min_eq_left hi]
    exact has.2 i (hi.trans hj)

/-- The repaired power-interior loss `log(B)^(-0.1)`. -/
noncomputable def taoSection5PowerInteriorDelta (B : ℕ) : ℝ :=
  Real.rpow (Real.log B) (-1 / 10 : ℝ)

/-- Lower endpoint `y^(1+delta)` of the branch source interior. -/
noncomputable def taoSection5PowerInteriorLower
    (B : ℕ) (branch : TaoSection5SourceBranch) : ℝ :=
  Real.rpow (taoSection5SourceY B branch)
    (1 + taoSection5PowerInteriorDelta B)

/-- Upper endpoint `y^(alpha-delta)` of the branch source interior. -/
noncomputable def taoSection5PowerInteriorUpper
    (B : ℕ) (branch : TaoSection5SourceBranch) : ℝ :=
  Real.rpow (taoSection5SourceY B branch)
    (taoAlpha - taoSection5PowerInteriorDelta B)

/-- Odd natural sources in the repaired branch interior. -/
noncomputable def taoSection5PowerInterior
    (B : ℕ) (branch : TaoSection5SourceBranch) : Finset ℕ :=
  oddLogWindow (Nat.ceil (taoSection5PowerInteriorLower B branch))
    (Nat.floor (taoSection5PowerInteriorUpper B branch))

theorem mem_taoSection5PowerInterior_iff
    {B N : ℕ} {branch : TaoSection5SourceBranch} :
    N ∈ taoSection5PowerInterior B branch ↔
      Nat.ceil (taoSection5PowerInteriorLower B branch) ≤ N ∧
        N ≤ Nat.floor (taoSection5PowerInteriorUpper B branch) ∧
          N % 2 = 1 := by
  simp [taoSection5PowerInterior, oddLogWindow, and_assoc]

/-- The logarithmic multiplicative slack in the common lost window (5.10). -/
noncomputable def taoSection5CanonicalLostSlack (B : ℕ) : ℝ :=
  Real.rpow (Real.log B) (7 / 10 : ℝ)

/-- The branch-free central scale `(4/3)^m0 * B` in (5.10). -/
noncomputable def taoSection5CanonicalLostScale (B : ℕ) : ℝ :=
  (4 / 3 : ℝ) ^ taoSection5M0 B * B

noncomputable def taoSection5CanonicalLostLower (B : ℕ) : ℝ :=
  Real.exp (-taoSection5CanonicalLostSlack B) *
    taoSection5CanonicalLostScale B

noncomputable def taoSection5CanonicalLostUpper (B : ℕ) : ℝ :=
  Real.exp (taoSection5CanonicalLostSlack B) *
    taoSection5CanonicalLostScale B

/-- The finite natural window supporting the common target `EPrime`. -/
noncomputable def taoSection5CanonicalLostWindow (B : ℕ) : Finset ℕ :=
  Finset.Icc (Nat.ceil (taoSection5CanonicalLostLower B))
    (Nat.floor (taoSection5CanonicalLostUpper B))

/--
The exact target `EPrime` from (5.10). It has no source-branch parameter:
both Section 5 source branches use this same finite set definitionally.
-/
noncomputable def taoSection5EPrime
    (B : ℕ) (E : Set ℕ) : Finset ℕ := by
  classical
  exact (taoSection5CanonicalLostWindow B).filter fun M =>
    Odd M ∧
      syracuseFirstHitAtMost B M (taoSection5M0 B) ∧
        (syracuse^[taoSection5M0 B]) M ∈ E

theorem mem_taoSection5EPrime_iff
    {B M : ℕ} {E : Set ℕ} :
    M ∈ taoSection5EPrime B E ↔
      Nat.ceil (taoSection5CanonicalLostLower B) ≤ M ∧
        M ≤ Nat.floor (taoSection5CanonicalLostUpper B) ∧
          Odd M ∧
            syracuseFirstHitAtMost B M (taoSection5M0 B) ∧
              (syracuse^[taoSection5M0 B]) M ∈ E := by
  classical
  simp [taoSection5EPrime, taoSection5CanonicalLostWindow, and_assoc]

theorem taoSection5EPrime_empty (B : ℕ) :
    taoSection5EPrime B ∅ = ∅ := by
  classical
  ext M
  simp [mem_taoSection5EPrime_iff]

example : taoSection5M0 0 = 0 := by
  norm_num [taoSection5M0, taoAlpha]

example : taoSection5M0 1 = 0 := by
  norm_num [taoSection5M0, taoAlpha]

example : taoSection5TypicalTuple 2 0 [] := by
  constructor
  · rfl
  · intro j hj
    have hj0 : j = 0 := by omega
    subst j
    simp [taoTupleWeight, taoSection5TypicalSlack]
    exact (Real.rpow_pos_of_pos (Real.log_pos (by norm_num)) _).le

end

end Tao
end Erdos1135SecondScale
