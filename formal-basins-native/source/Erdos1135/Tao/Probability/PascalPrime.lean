import Erdos1135.Tao.Probability.Pascal
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic

/-!
# Section 7 Pascal-Prime Distribution

This module records the Section 7 conditioning step that deletes the Pascal
atom `b = 3` and renormalizes the remaining source values by `4 / 3`.
-/

open scoped BigOperators

namespace Erdos1135
namespace Tao

/-- Reindex the Pascal pair mass by `b = n + 2`, the positive support of the
sum of two positive `Geom(2)` variables. -/
noncomputable def taoSection7PascalMassOn (n : ℕ) : ℝ :=
  pascalGeom2PairMass (n + 2)

/-- Pascal-prime mass on the same `n`-parameter: delete `b = 3`, i.e. `n = 1`,
and renormalize by `4 / 3`. -/
noncomputable def taoSection7PascalPrimeMassOn (n : ℕ) : ℝ :=
  if n = 1 then 0 else (4 / 3 : ℝ) * taoSection7PascalMassOn n

theorem taoSection7_arithGeom_half_tsum :
    (∑' n : ℕ, (((n + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ n)) = 4 := by
  have h :=
    tsum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1
      (r := (1 / 2 : ℝ)) (by norm_num)
  convert h using 1
  · apply tsum_congr
    intro n
    simp
  · norm_num

theorem taoSection7PascalMassOn_eq (n : ℕ) :
    taoSection7PascalMassOn n =
      (((n + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ (n + 2)) := by
  unfold taoSection7PascalMassOn
  rw [pascalGeom2PairMass_eq (n + 2) (by omega)]
  have hsub : n + 2 - 1 = n + 1 := by omega
  rw [hsub]

theorem taoSection7PascalMassOn_eq_quarter_mul (n : ℕ) :
    taoSection7PascalMassOn n =
      (1 / 4 : ℝ) * (((n + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ n) := by
  rw [taoSection7PascalMassOn_eq]
  rw [show (1 / 2 : ℝ) ^ (n + 2) =
      (1 / 2 : ℝ) ^ n * (1 / 2 : ℝ) ^ 2 by
    rw [pow_add]]
  ring

theorem taoSection7PascalMassOn_nonneg (n : ℕ) :
    0 ≤ taoSection7PascalMassOn n := by
  rw [taoSection7PascalMassOn_eq_quarter_mul]
  positivity

theorem taoSection7PascalMassOn_zero :
    taoSection7PascalMassOn 0 = (1 / 4 : ℝ) := by
  norm_num [taoSection7PascalMassOn_eq]

theorem taoSection7PascalMassOn_one :
    taoSection7PascalMassOn 1 = (1 / 4 : ℝ) := by
  norm_num [taoSection7PascalMassOn_eq]

theorem summable_taoSection7PascalMassOn :
    Summable taoSection7PascalMassOn := by
  have hbase :
      Summable fun n : ℕ => (((n + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ n) := by
    have h :=
      summable_choose_mul_geometric_of_norm_lt_one (R := ℝ) 1
        (r := (1 / 2 : ℝ)) (by norm_num)
    convert h using 1
    ext n
    simp
  convert hbase.mul_left (1 / 4 : ℝ) using 1
  ext n
  rw [taoSection7PascalMassOn_eq_quarter_mul]

theorem tsum_taoSection7PascalMassOn :
    (∑' n : ℕ, taoSection7PascalMassOn n) = 1 := by
  calc
    (∑' n : ℕ, taoSection7PascalMassOn n)
        = ∑' n : ℕ,
            (1 / 4 : ℝ) * (((n + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ n) := by
          apply tsum_congr
          intro n
          exact taoSection7PascalMassOn_eq_quarter_mul n
    _ = (1 / 4 : ℝ) *
          (∑' n : ℕ, (((n + 1 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ n)) := by
          rw [tsum_mul_left]
    _ = 1 := by
          rw [taoSection7_arithGeom_half_tsum]
          norm_num

theorem taoSection7PascalPrimeMassOn_zero :
    taoSection7PascalPrimeMassOn 0 = (1 / 3 : ℝ) := by
  norm_num [taoSection7PascalPrimeMassOn, taoSection7PascalMassOn_zero]

theorem taoSection7PascalPrimeMassOn_one :
    taoSection7PascalPrimeMassOn 1 = 0 := by
  simp [taoSection7PascalPrimeMassOn]

theorem taoSection7PascalPrimeMassOn_succ_succ (n : ℕ) :
    taoSection7PascalPrimeMassOn (n + 2) =
      (4 / 3 : ℝ) * taoSection7PascalMassOn (n + 2) := by
  simp [taoSection7PascalPrimeMassOn]

theorem taoSection7PascalPrimeMassOn_nonneg (n : ℕ) :
    0 ≤ taoSection7PascalPrimeMassOn n := by
  unfold taoSection7PascalPrimeMassOn
  split_ifs
  · norm_num
  · have hmass : 0 ≤ taoSection7PascalMassOn n :=
      taoSection7PascalMassOn_nonneg n
    positivity

theorem summable_taoSection7PascalPrimeMassOn :
    Summable taoSection7PascalPrimeMassOn := by
  apply (summable_nat_add_iff 2).1
  have htailMass : Summable fun n : ℕ => taoSection7PascalMassOn (n + 2) := by
    exact (summable_nat_add_iff 2).2 summable_taoSection7PascalMassOn
  refine (htailMass.mul_left (4 / 3 : ℝ)).congr ?_
  intro n
  rw [taoSection7PascalPrimeMassOn_succ_succ]

theorem tsum_taoSection7PascalPrimeMassOn :
    (∑' n : ℕ, taoSection7PascalPrimeMassOn n) = 1 := by
  have hsum := summable_taoSection7PascalPrimeMassOn
  have hmass := summable_taoSection7PascalMassOn
  have hsplitPrime :
      (∑' n : ℕ, taoSection7PascalPrimeMassOn n) =
        taoSection7PascalPrimeMassOn 0 + taoSection7PascalPrimeMassOn 1 +
          ∑' n : ℕ, taoSection7PascalPrimeMassOn (n + 2) := by
    rw [hsum.tsum_eq_zero_add]
    have htail : Summable fun n : ℕ => taoSection7PascalPrimeMassOn (n + 1) := by
      simpa using (summable_nat_add_iff 1).2 hsum
    rw [htail.tsum_eq_zero_add]
    ring
  have hsplitMass :
      (∑' n : ℕ, taoSection7PascalMassOn n) =
        taoSection7PascalMassOn 0 + taoSection7PascalMassOn 1 +
          ∑' n : ℕ, taoSection7PascalMassOn (n + 2) := by
    rw [hmass.tsum_eq_zero_add]
    have htail : Summable fun n : ℕ => taoSection7PascalMassOn (n + 1) := by
      simpa using (summable_nat_add_iff 1).2 hmass
    rw [htail.tsum_eq_zero_add]
    ring
  have htailEq :
      (∑' n : ℕ, taoSection7PascalPrimeMassOn (n + 2)) =
        (4 / 3 : ℝ) * ∑' n : ℕ, taoSection7PascalMassOn (n + 2) := by
    calc
      (∑' n : ℕ, taoSection7PascalPrimeMassOn (n + 2))
          = ∑' n : ℕ, (4 / 3 : ℝ) * taoSection7PascalMassOn (n + 2) := by
            apply tsum_congr
            intro n
            exact taoSection7PascalPrimeMassOn_succ_succ n
      _ = (4 / 3 : ℝ) * ∑' n : ℕ, taoSection7PascalMassOn (n + 2) := by
            rw [tsum_mul_left]
  have htailMass :
      (∑' n : ℕ, taoSection7PascalMassOn (n + 2)) = (1 / 2 : ℝ) := by
    have hmain := tsum_taoSection7PascalMassOn
    rw [hsplitMass, taoSection7PascalMassOn_zero, taoSection7PascalMassOn_one] at hmain
    linarith
  rw [hsplitPrime, taoSection7PascalPrimeMassOn_zero,
    taoSection7PascalPrimeMassOn_one, htailEq, htailMass]
  norm_num

/-- The normalized Section 7 Pascal-prime law on the parameter `n` with
source total value `b = n + 2`. The deleted source atom `b = 3` is `n = 1`. -/
noncomputable def taoSection7PascalPrimePMF : PMF ℕ :=
  ⟨fun n => ENNReal.ofReal (taoSection7PascalPrimeMassOn n), by
    apply ENNReal.hasSum_coe.mpr
    have hreal : HasSum taoSection7PascalPrimeMassOn 1 := by
      simpa [tsum_taoSection7PascalPrimeMassOn] using
        summable_taoSection7PascalPrimeMassOn.hasSum
    simpa [Real.toNNReal_one, ENNReal.toNNReal_one] using
      hreal.toNNReal taoSection7PascalPrimeMassOn_nonneg⟩

theorem taoSection7PascalPrimePMF_apply_toReal (n : ℕ) :
    (taoSection7PascalPrimePMF n).toReal =
      taoSection7PascalPrimeMassOn n := by
  change (ENNReal.ofReal (taoSection7PascalPrimeMassOn n)).toReal =
    taoSection7PascalPrimeMassOn n
  exact ENNReal.toReal_ofReal (taoSection7PascalPrimeMassOn_nonneg n)

theorem taoSection7PascalPrimePMF_zero_toReal :
    (taoSection7PascalPrimePMF 0).toReal = (1 / 3 : ℝ) := by
  rw [taoSection7PascalPrimePMF_apply_toReal, taoSection7PascalPrimeMassOn_zero]

theorem taoSection7PascalPrimePMF_one_toReal :
    (taoSection7PascalPrimePMF 1).toReal = 0 := by
  rw [taoSection7PascalPrimePMF_apply_toReal, taoSection7PascalPrimeMassOn_one]

/-- Source-indexed Pascal-prime mass on the original total value `b`. -/
noncomputable def taoSection7PascalPrimeSourceMass (b : ℕ) : ℝ :=
  if b = 3 then 0 else (4 / 3 : ℝ) * pascalGeom2PairMass b

theorem taoSection7PascalPrimeSourceMass_three :
    taoSection7PascalPrimeSourceMass 3 = 0 := by
  simp [taoSection7PascalPrimeSourceMass]

theorem taoSection7PascalPrimeSourceMass_of_ne_three
    {b : ℕ} (hb : b ≠ 3) :
    taoSection7PascalPrimeSourceMass b =
      (4 / 3 : ℝ) * pascalGeom2PairMass b := by
  simp [taoSection7PascalPrimeSourceMass, hb]

theorem taoSection7PascalPrimeMassOn_sub_two_eq_source
    {b : ℕ} (hb2 : 2 ≤ b) :
    taoSection7PascalPrimeMassOn (b - 2) =
      taoSection7PascalPrimeSourceMass b := by
  by_cases hb3 : b = 3
  · subst b
    simp [taoSection7PascalPrimeMassOn_one,
      taoSection7PascalPrimeSourceMass_three]
  · have hne : b - 2 ≠ 1 := by omega
    have hadd : b - 2 + 2 = b := by omega
    simp [taoSection7PascalPrimeMassOn, taoSection7PascalPrimeSourceMass,
      hb3, hne]
    simp [taoSection7PascalMassOn, hadd]

theorem taoSection7PascalPrimePMF_source_toReal
    {b : ℕ} (hb2 : 2 ≤ b) :
    (taoSection7PascalPrimePMF (b - 2)).toReal =
      taoSection7PascalPrimeSourceMass b := by
  rw [taoSection7PascalPrimePMF_apply_toReal]
  exact taoSection7PascalPrimeMassOn_sub_two_eq_source hb2

theorem taoSection7PascalPrimePMF_source_toReal_of_ne_three
    {b : ℕ} (hb2 : 2 ≤ b) (hb3 : b ≠ 3) :
    (taoSection7PascalPrimePMF (b - 2)).toReal =
      (4 / 3 : ℝ) * pascalGeom2PairMass b := by
  rw [taoSection7PascalPrimePMF_source_toReal hb2,
    taoSection7PascalPrimeSourceMass_of_ne_three hb3]

/-- Every source total in a finite prefix is in the support range `b >= 2`. -/
def taoSection7AllGeTwo (bs : List ℕ) : Prop :=
  ∀ b ∈ bs, 2 ≤ b

/-- A finite source prefix contains no `b = 3` hit. -/
def taoSection7NoThree (bs : List ℕ) : Prop :=
  ∀ b ∈ bs, b ≠ 3

/-- Product of Pascal-prime PMF point masses along a source-valued finite path. -/
noncomputable def taoSection7PascalPrimePMFSourcePathMass
    (pre : List ℕ) : ℝ :=
  (pre.map fun b => (taoSection7PascalPrimePMF (b - 2)).toReal).prod

/-- Product of source-indexed Pascal-prime real masses along a finite path. -/
noncomputable def taoSection7PascalPrimeSourcePathMass
    (pre : List ℕ) : ℝ :=
  (pre.map taoSection7PascalPrimeSourceMass).prod

theorem taoSection7PascalPrimePMFSourcePathMass_nil :
    taoSection7PascalPrimePMFSourcePathMass [] = 1 := by
  simp [taoSection7PascalPrimePMFSourcePathMass]

theorem taoSection7PascalPrimePMFSourcePathMass_cons
    (b : ℕ) (pre : List ℕ) :
    taoSection7PascalPrimePMFSourcePathMass (b :: pre) =
      (taoSection7PascalPrimePMF (b - 2)).toReal *
        taoSection7PascalPrimePMFSourcePathMass pre := by
  simp [taoSection7PascalPrimePMFSourcePathMass]

theorem taoSection7PascalPrimePMFSourcePathMass_eq_source
    {pre : List ℕ} (h2 : taoSection7AllGeTwo pre) :
    taoSection7PascalPrimePMFSourcePathMass pre =
      taoSection7PascalPrimeSourcePathMass pre := by
  induction pre with
  | nil =>
      simp [taoSection7PascalPrimePMFSourcePathMass,
        taoSection7PascalPrimeSourcePathMass]
  | cons b pre ih =>
      have hb2 : 2 ≤ b := h2 b (by simp)
      have htail : taoSection7AllGeTwo pre := by
        intro x hx
        exact h2 x (by simp [hx])
      rw [taoSection7PascalPrimePMFSourcePathMass_cons]
      simp [taoSection7PascalPrimeSourcePathMass,
        taoSection7PascalPrimePMF_source_toReal hb2, ih htail]

private theorem taoSection7Geom4MissMass_succ_local (n : ℕ) :
    taoSection7Geom4MissMass (n + 1) =
      (3 / 4 : ℝ) * taoSection7Geom4MissMass n := by
  unfold taoSection7Geom4MissMass
  rw [pow_succ]
  ring

/-- Probability-style mass of a finite block: misses `pre`, then the first hit `3`. -/
noncomputable def taoSection7FinitePreHitBlockPMFMass
    (pre : List ℕ) : ℝ :=
  taoSection7Geom4MissMass pre.length *
    taoSection7PascalPrimePMFSourcePathMass pre

/-- Unconditioned mass of seeing `pre` and then the final hit value `3`. -/
noncomputable def taoSection7UnconditionedPreHitPathMass
    (pre : List ℕ) : ℝ :=
  (pre.map pascalGeom2PairMass).prod * pascalGeom2PairMass 3

theorem taoSection7UnconditionedPreHitPathMass_nil :
    taoSection7UnconditionedPreHitPathMass [] = (1 / 4 : ℝ) := by
  simp [taoSection7UnconditionedPreHitPathMass, pascalGeom2PairMass_three]

theorem taoSection7UnconditionedPreHitPathMass_cons
    (b : ℕ) (pre : List ℕ) :
    taoSection7UnconditionedPreHitPathMass (b :: pre) =
      pascalGeom2PairMass b *
        taoSection7UnconditionedPreHitPathMass pre := by
  simp [taoSection7UnconditionedPreHitPathMass, mul_assoc]

theorem taoSection7FinitePreHitBlockPMFMass_nil :
    taoSection7FinitePreHitBlockPMFMass [] = (1 / 4 : ℝ) := by
  simp [taoSection7FinitePreHitBlockPMFMass,
    taoSection7Geom4MissMass, taoSection7PascalPrimePMFSourcePathMass_nil]

theorem taoSection7FinitePreHitBlockPMFMass_cons_miss
    {b : ℕ} (hb2 : 2 ≤ b) (hb3 : b ≠ 3) (pre : List ℕ) :
    taoSection7FinitePreHitBlockPMFMass (b :: pre) =
      pascalGeom2PairMass b *
        taoSection7FinitePreHitBlockPMFMass pre := by
  rw [taoSection7FinitePreHitBlockPMFMass,
    taoSection7PascalPrimePMFSourcePathMass_cons]
  rw [show List.length (b :: pre) = pre.length + 1 by rfl]
  rw [taoSection7Geom4MissMass_succ_local]
  rw [taoSection7PascalPrimePMF_source_toReal_of_ne_three hb2 hb3]
  rw [taoSection7FinitePreHitBlockPMFMass]
  ring

theorem taoSection7FinitePreHitBlockPMFMass_eq_unconditioned
    {pre : List ℕ}
    (h2 : taoSection7AllGeTwo pre) (hpre : taoSection7NoThree pre) :
    taoSection7FinitePreHitBlockPMFMass pre =
      taoSection7UnconditionedPreHitPathMass pre := by
  induction pre with
  | nil =>
      rw [taoSection7FinitePreHitBlockPMFMass_nil,
        taoSection7UnconditionedPreHitPathMass_nil]
  | cons b pre ih =>
      have hb2 : 2 ≤ b := h2 b (by simp)
      have hb3 : b ≠ 3 := hpre b (by simp)
      have h2tail : taoSection7AllGeTwo pre := by
        intro x hx
        exact h2 x (by simp [hx])
      have htail : taoSection7NoThree pre := by
        intro x hx
        exact hpre x (by simp [hx])
      rw [taoSection7FinitePreHitBlockPMFMass_cons_miss hb2 hb3,
        taoSection7UnconditionedPreHitPathMass_cons, ih h2tail htail]

theorem taoSection7_arithGeom_half_second_weight_tsum :
    (∑' n : ℕ,
        (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ) *
          (1 / 2 : ℝ) ^ n)) = 16 := by
  have hchoose :
      (∑' n : ℕ,
          (((n + 2).choose 2 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ n) = 8 := by
    have h :=
      tsum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 2
        (r := (1 / 2 : ℝ)) (by norm_num)
    norm_num at h
    exact h
  calc
    (∑' n : ℕ,
        (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ) *
          (1 / 2 : ℝ) ^ n))
        = ∑' n : ℕ,
            (2 : ℝ) * ((((n + 2).choose 2 : ℕ) : ℝ) *
              (1 / 2 : ℝ) ^ n) := by
          apply tsum_congr
          intro n
          rw [Nat.cast_choose_two]
          norm_num
          ring
    _ = (2 : ℝ) *
          (∑' n : ℕ,
            (((n + 2).choose 2 : ℕ) : ℝ) * (1 / 2 : ℝ) ^ n) := by
          rw [tsum_mul_left]
    _ = 16 := by
          rw [hchoose]
          norm_num

theorem summable_taoSection7PascalMassOn_weighted :
    Summable fun n : ℕ =>
      taoSection7PascalMassOn n * (((n + 2 : ℕ) : ℝ)) := by
  have hbase :
      Summable fun n : ℕ =>
        (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ) *
          (1 / 2 : ℝ) ^ n) := by
    have hchoose :=
      (summable_choose_mul_geometric_of_norm_lt_one (R := ℝ) 2
        (r := (1 / 2 : ℝ)) (by norm_num)).mul_left (2 : ℝ)
    convert hchoose using 1
    ext n
    rw [Nat.cast_choose_two]
    norm_num
    ring
  convert hbase.mul_left (1 / 4 : ℝ) using 1
  ext n
  rw [taoSection7PascalMassOn_eq_quarter_mul]
  ring

theorem tsum_taoSection7PascalMassOn_weighted :
    (∑' n : ℕ,
      taoSection7PascalMassOn n * (((n + 2 : ℕ) : ℝ))) = 4 := by
  calc
    (∑' n : ℕ,
      taoSection7PascalMassOn n * (((n + 2 : ℕ) : ℝ)))
        = ∑' n : ℕ,
            (1 / 4 : ℝ) *
              ((((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ) *
                (1 / 2 : ℝ) ^ n)) := by
          apply tsum_congr
          intro n
          rw [taoSection7PascalMassOn_eq_quarter_mul]
          ring
    _ = (1 / 4 : ℝ) *
          (∑' n : ℕ,
            (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ) *
              (1 / 2 : ℝ) ^ n)) := by
          rw [tsum_mul_left]
    _ = 4 := by
          rw [taoSection7_arithGeom_half_second_weight_tsum]
          norm_num

theorem summable_taoSection7PascalPrimeMassOn_weighted :
    Summable fun n : ℕ =>
      taoSection7PascalPrimeMassOn n * (((n + 2 : ℕ) : ℝ)) := by
  apply (summable_nat_add_iff 2).1
  have htail :
      Summable fun n : ℕ =>
        taoSection7PascalMassOn (n + 2) * ((((n + 2) + 2 : ℕ) : ℝ)) := by
    exact (summable_nat_add_iff 2).2 summable_taoSection7PascalMassOn_weighted
  refine (htail.mul_left (4 / 3 : ℝ)).congr ?_
  intro n
  rw [taoSection7PascalPrimeMassOn_succ_succ]
  ring

theorem tsum_taoSection7PascalPrimeMassOn_weighted :
    (∑' n : ℕ,
      taoSection7PascalPrimeMassOn n * (((n + 2 : ℕ) : ℝ))) = 13 / 3 := by
  have hprime := summable_taoSection7PascalPrimeMassOn_weighted
  have hpascal := summable_taoSection7PascalMassOn_weighted
  have hsplitPrime :
      (∑' n : ℕ,
        taoSection7PascalPrimeMassOn n * (((n + 2 : ℕ) : ℝ))) =
        taoSection7PascalPrimeMassOn 0 * (2 : ℝ) +
          taoSection7PascalPrimeMassOn 1 * (3 : ℝ) +
          ∑' n : ℕ,
            taoSection7PascalPrimeMassOn (n + 2) *
              ((((n + 2) + 2 : ℕ) : ℝ)) := by
    rw [hprime.tsum_eq_zero_add]
    have htail :
        Summable fun n : ℕ =>
          taoSection7PascalPrimeMassOn (n + 1) *
            ((((n + 1) + 2 : ℕ) : ℝ)) := by
      simpa using (summable_nat_add_iff 1).2 hprime
    rw [htail.tsum_eq_zero_add]
    ring
  have hsplitPascal :
      (∑' n : ℕ,
        taoSection7PascalMassOn n * (((n + 2 : ℕ) : ℝ))) =
        taoSection7PascalMassOn 0 * (2 : ℝ) +
          taoSection7PascalMassOn 1 * (3 : ℝ) +
          ∑' n : ℕ,
            taoSection7PascalMassOn (n + 2) *
              ((((n + 2) + 2 : ℕ) : ℝ)) := by
    rw [hpascal.tsum_eq_zero_add]
    have htail :
        Summable fun n : ℕ =>
          taoSection7PascalMassOn (n + 1) *
            ((((n + 1) + 2 : ℕ) : ℝ)) := by
      simpa using (summable_nat_add_iff 1).2 hpascal
    rw [htail.tsum_eq_zero_add]
    ring
  have htailEq :
      (∑' n : ℕ,
        taoSection7PascalPrimeMassOn (n + 2) *
          ((((n + 2) + 2 : ℕ) : ℝ))) =
        (4 / 3 : ℝ) *
          ∑' n : ℕ,
            taoSection7PascalMassOn (n + 2) *
              ((((n + 2) + 2 : ℕ) : ℝ)) := by
    calc
      (∑' n : ℕ,
        taoSection7PascalPrimeMassOn (n + 2) *
          ((((n + 2) + 2 : ℕ) : ℝ)))
          =
        ∑' n : ℕ,
          (4 / 3 : ℝ) *
            (taoSection7PascalMassOn (n + 2) *
              ((((n + 2) + 2 : ℕ) : ℝ))) := by
            apply tsum_congr
            intro n
            rw [taoSection7PascalPrimeMassOn_succ_succ]
            ring
      _ = (4 / 3 : ℝ) *
          ∑' n : ℕ,
            taoSection7PascalMassOn (n + 2) *
              ((((n + 2) + 2 : ℕ) : ℝ)) := by
            rw [tsum_mul_left]
  have hpascal0 :
      taoSection7PascalMassOn 0 * (2 : ℝ) = (1 / 2 : ℝ) := by
    norm_num [taoSection7PascalMassOn_eq_quarter_mul]
  have hpascal1 :
      taoSection7PascalMassOn 1 * (3 : ℝ) = (3 / 4 : ℝ) := by
    norm_num [taoSection7PascalMassOn_eq_quarter_mul]
  have htailPascal :
      (∑' n : ℕ,
        taoSection7PascalMassOn (n + 2) *
          ((((n + 2) + 2 : ℕ) : ℝ))) = (11 / 4 : ℝ) := by
    have hmain := tsum_taoSection7PascalMassOn_weighted
    rw [hsplitPascal, hpascal0, hpascal1] at hmain
    linarith
  rw [hsplitPrime, taoSection7PascalPrimeMassOn_zero,
    taoSection7PascalPrimeMassOn_one, htailEq, htailPascal]
  norm_num

theorem taoSection7PascalPrimeSourceMass_zero :
    taoSection7PascalPrimeSourceMass 0 = 0 := by
  norm_num [taoSection7PascalPrimeSourceMass, pascalGeom2PairMass]

theorem taoSection7PascalPrimeSourceMass_one :
    taoSection7PascalPrimeSourceMass 1 = 0 := by
  norm_num [taoSection7PascalPrimeSourceMass, pascalGeom2PairMass]

theorem taoSection7PascalPrimeSourceMass_add_two (n : ℕ) :
    taoSection7PascalPrimeSourceMass (n + 2) =
      taoSection7PascalPrimeMassOn n := by
  have hb2 : 2 ≤ n + 2 := by omega
  rw [← taoSection7PascalPrimeMassOn_sub_two_eq_source hb2]
  congr 1

theorem summable_taoSection7PascalPrimeSourceMass_weighted :
    Summable fun b : ℕ =>
      taoSection7PascalPrimeSourceMass b * (b : ℝ) := by
  apply (summable_nat_add_iff 2).1
  have htail :
      Summable fun n : ℕ =>
        taoSection7PascalPrimeMassOn n *
          (((n + 2 : ℕ) : ℝ)) :=
    summable_taoSection7PascalPrimeMassOn_weighted
  refine htail.congr ?_
  intro n
  rw [taoSection7PascalPrimeSourceMass_add_two]

theorem tsum_taoSection7PascalPrimeSourceMass_weighted :
    (∑' b : ℕ,
      taoSection7PascalPrimeSourceMass b * (b : ℝ)) = 13 / 3 := by
  have hsrc := summable_taoSection7PascalPrimeSourceMass_weighted
  have htail :
      Summable fun n : ℕ =>
        taoSection7PascalPrimeSourceMass (n + 1) *
          (((n + 1 : ℕ) : ℝ)) := by
    simpa using (summable_nat_add_iff 1).2 hsrc
  have hsplit :
      (∑' b : ℕ, taoSection7PascalPrimeSourceMass b * (b : ℝ)) =
        taoSection7PascalPrimeSourceMass 0 * (0 : ℝ) +
          taoSection7PascalPrimeSourceMass 1 * (1 : ℝ) +
          ∑' n : ℕ,
            taoSection7PascalPrimeSourceMass (n + 2) *
              (((n + 2 : ℕ) : ℝ)) := by
    rw [hsrc.tsum_eq_zero_add]
    rw [htail.tsum_eq_zero_add]
    ring
  have htailEq :
      (∑' n : ℕ,
        taoSection7PascalPrimeSourceMass (n + 2) *
          (((n + 2 : ℕ) : ℝ))) =
        ∑' n : ℕ,
          taoSection7PascalPrimeMassOn n *
            (((n + 2 : ℕ) : ℝ)) := by
    apply tsum_congr
    intro n
    rw [taoSection7PascalPrimeSourceMass_add_two]
  rw [hsplit, taoSection7PascalPrimeSourceMass_zero,
    taoSection7PascalPrimeSourceMass_one, htailEq,
    tsum_taoSection7PascalPrimeMassOn_weighted]
  norm_num

/--
Shifted arithmetico-geometric series used by the terminal `Hold` exponential
moment route after the deleted `b = 3` atom is separated.
-/
theorem taoSection7_arithGeom_three_tsum (r : ℝ) (hr : ‖r‖ < 1) :
    (∑' n : ℕ, (((n : ℕ) : ℝ) + 3) * r ^ n) =
      1 / (1 - r) ^ 2 + 2 * (1 / (1 - r)) := by
  have hn1 : Summable fun n : ℕ => (((n : ℕ) : ℝ) + 1) * r ^ n := by
    simpa using
      (summable_choose_mul_geometric_of_norm_lt_one (R := ℝ) 1 (r := r) hr)
  have hc : Summable fun n : ℕ => (2 : ℝ) * r ^ n :=
    (summable_geometric_of_norm_lt_one hr).mul_left 2
  have hchoose :
      (∑' n : ℕ, (((n : ℕ) : ℝ) + 1) * r ^ n) =
        1 / (1 - r) ^ 2 := by
    have h :=
      tsum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) 1 (r := r) hr
    norm_num at h
    rw [h]
    ring
  calc
    (∑' n : ℕ, (((n : ℕ) : ℝ) + 3) * r ^ n)
        = ∑' n : ℕ,
            ((((n : ℕ) : ℝ) + 1) * r ^ n + (2 : ℝ) * r ^ n) := by
          apply tsum_congr
          intro n
          ring
    _ = (∑' n : ℕ, (((n : ℕ) : ℝ) + 1) * r ^ n) +
          ∑' n : ℕ, (2 : ℝ) * r ^ n := by
          rw [hn1.tsum_add hc]
    _ = 1 / (1 - r) ^ 2 + 2 * (1 / (1 - r)) := by
          rw [hchoose]
          rw [tsum_mul_left]
          rw [tsum_geometric_of_norm_lt_one hr]
          ring

/-- Tail term identity for the `21/20` Pascal-prime source exponential moment. -/
theorem taoSection7PascalPrimeMassOn_tail_pow_21_div_20
    (n : ℕ) :
    taoSection7PascalPrimeMassOn (n + 2) * (21 / 20 : ℝ) ^ (n + 2 + 2) =
      (4 / 3 : ℝ) * (21 / 40 : ℝ) ^ 4 *
        ((((n : ℕ) : ℝ) + 3) * (21 / 40 : ℝ) ^ n) := by
  rw [taoSection7PascalPrimeMassOn_succ_succ]
  rw [taoSection7PascalMassOn_eq]
  rw [show n + 2 + 2 = n + 4 by omega]
  rw [show (1 / 2 : ℝ) ^ (n + 4) =
      (1 / 2 : ℝ) ^ n * (1 / 2 : ℝ) ^ 4 by rw [pow_add]]
  rw [show (21 / 20 : ℝ) ^ (n + 4) =
      (21 / 20 : ℝ) ^ n * (21 / 20 : ℝ) ^ 4 by rw [pow_add]]
  have hpow :
      (1 / 2 : ℝ) ^ n * (21 / 20 : ℝ) ^ n =
        (21 / 40 : ℝ) ^ n := by
    rw [← mul_pow]
    norm_num
  have hpow4 :
      (1 / 2 : ℝ) ^ 4 * (21 / 20 : ℝ) ^ 4 =
        (21 / 40 : ℝ) ^ 4 := by
    rw [← mul_pow]
    norm_num
  calc
    (4 / 3 : ℝ) *
          (((n + 2 + 1 : ℕ) : ℝ) *
            ((1 / 2 : ℝ) ^ n * (1 / 2 : ℝ) ^ 4)) *
        ((21 / 20 : ℝ) ^ n * (21 / 20 : ℝ) ^ 4)
        = (4 / 3 : ℝ) * (((n : ℕ) : ℝ) + 3) *
          (((1 / 2 : ℝ) ^ n * (21 / 20 : ℝ) ^ n) *
            ((1 / 2 : ℝ) ^ 4 * (21 / 20 : ℝ) ^ 4)) := by
          norm_num
          ring
    _ = (4 / 3 : ℝ) * (((n : ℕ) : ℝ) + 3) *
          ((21 / 40 : ℝ) ^ n * (21 / 40 : ℝ) ^ 4) := by
          rw [hpow, hpow4]
    _ = (4 / 3 : ℝ) * (21 / 40 : ℝ) ^ 4 *
        ((((n : ℕ) : ℝ) + 3) * (21 / 40 : ℝ) ^ n) := by
          ring

/-- Summability of the Pascal-prime source exponential moment at ratio `21/20`. -/
theorem summable_taoSection7PascalPrimeSourceMass_pow_21_div_20 :
    Summable fun b : ℕ =>
      taoSection7PascalPrimeSourceMass b * (21 / 20 : ℝ) ^ b := by
  apply (summable_nat_add_iff 2).1
  have hr : ‖(21 / 40 : ℝ)‖ < 1 := by norm_num
  have hn1 :
      Summable fun n : ℕ =>
        (((n : ℕ) : ℝ) + 1) * (21 / 40 : ℝ) ^ n := by
    simpa using
      (summable_choose_mul_geometric_of_norm_lt_one
        (R := ℝ) 1 (r := (21 / 40 : ℝ)) hr)
  have hc : Summable fun n : ℕ => (2 : ℝ) * (21 / 40 : ℝ) ^ n :=
    (summable_geometric_of_norm_lt_one hr).mul_left 2
  have hbase :
      Summable fun n : ℕ =>
        (((n : ℕ) : ℝ) + 3) * (21 / 40 : ℝ) ^ n := by
    refine (hn1.add hc).congr ?_
    intro n
    ring
  have htail :
      Summable fun n : ℕ =>
        taoSection7PascalPrimeMassOn (n + 2) *
          (21 / 20 : ℝ) ^ (n + 2 + 2) := by
    refine (hbase.mul_left ((4 / 3 : ℝ) * (21 / 40 : ℝ) ^ 4)).congr ?_
    intro n
    exact (taoSection7PascalPrimeMassOn_tail_pow_21_div_20 n).symm
  have hprime :
      Summable fun n : ℕ =>
        taoSection7PascalPrimeMassOn n * (21 / 20 : ℝ) ^ (n + 2) := by
    apply (summable_nat_add_iff 2).1
    simpa using htail
  have hsource_tail :
      Summable fun n : ℕ =>
        taoSection7PascalPrimeSourceMass (n + 2) *
          (21 / 20 : ℝ) ^ (n + 2) := by
    refine hprime.congr ?_
    intro n
    rw [taoSection7PascalPrimeSourceMass_add_two]
  simpa using hsource_tail

/-- Exact Pascal-prime source exponential moment at ratio `21/20`. -/
theorem tsum_taoSection7PascalPrimeSourceMass_pow_21_div_20 :
    (∑' b : ℕ,
      taoSection7PascalPrimeSourceMass b * (21 / 20 : ℝ) ^ b) =
      3589593 / 2888000 := by
  let f : ℕ → ℝ :=
    fun b => taoSection7PascalPrimeSourceMass b * (21 / 20 : ℝ) ^ b
  have hsrc : Summable f :=
    summable_taoSection7PascalPrimeSourceMass_pow_21_div_20
  have htail_src : Summable fun n : ℕ => f (n + 1) := by
    simpa using (summable_nat_add_iff 1).2 hsrc
  have hsplit_src :
      (∑' b : ℕ, f b) = f 0 + f 1 + ∑' n : ℕ, f (n + 2) := by
    rw [hsrc.tsum_eq_zero_add]
    rw [htail_src.tsum_eq_zero_add]
    ring
  have hsource_to_prime :
      (∑' n : ℕ, f (n + 2)) =
        ∑' n : ℕ,
          taoSection7PascalPrimeMassOn n * (21 / 20 : ℝ) ^ (n + 2) := by
    apply tsum_congr
    intro n
    dsimp [f]
    rw [taoSection7PascalPrimeSourceMass_add_two]
  have hsource_tail_summ : Summable fun n : ℕ => f (n + 2) := by
    simpa using (summable_nat_add_iff 2).2 hsrc
  have hprime_summ :
      Summable fun n : ℕ =>
        taoSection7PascalPrimeMassOn n * (21 / 20 : ℝ) ^ (n + 2) := by
    refine hsource_tail_summ.congr ?_
    intro n
    dsimp [f]
    rw [taoSection7PascalPrimeSourceMass_add_two]
  have hprime_tail1 :
      Summable fun n : ℕ =>
        taoSection7PascalPrimeMassOn (n + 1) *
          (21 / 20 : ℝ) ^ (n + 1 + 2) := by
    simpa using (summable_nat_add_iff 1).2 hprime_summ
  have hsplit_prime :
      (∑' n : ℕ,
        taoSection7PascalPrimeMassOn n * (21 / 20 : ℝ) ^ (n + 2)) =
        taoSection7PascalPrimeMassOn 0 * (21 / 20 : ℝ) ^ (0 + 2) +
          taoSection7PascalPrimeMassOn 1 * (21 / 20 : ℝ) ^ (1 + 2) +
          ∑' n : ℕ,
            taoSection7PascalPrimeMassOn (n + 2) *
              (21 / 20 : ℝ) ^ (n + 2 + 2) := by
    rw [hprime_summ.tsum_eq_zero_add]
    rw [hprime_tail1.tsum_eq_zero_add]
    ring
  have hr : ‖(21 / 40 : ℝ)‖ < 1 := by norm_num
  have htail_exact :
      (∑' n : ℕ,
        taoSection7PascalPrimeMassOn (n + 2) *
          (21 / 20 : ℝ) ^ (n + 2 + 2)) =
        (4 / 3 : ℝ) * (21 / 40 : ℝ) ^ 4 *
          (1 / (1 - (21 / 40 : ℝ)) ^ 2 +
            2 * (1 / (1 - (21 / 40 : ℝ)))) := by
    calc
      (∑' n : ℕ,
        taoSection7PascalPrimeMassOn (n + 2) *
          (21 / 20 : ℝ) ^ (n + 2 + 2))
          = ∑' n : ℕ,
              (4 / 3 : ℝ) * (21 / 40 : ℝ) ^ 4 *
                ((((n : ℕ) : ℝ) + 3) * (21 / 40 : ℝ) ^ n) := by
            apply tsum_congr
            intro n
            exact taoSection7PascalPrimeMassOn_tail_pow_21_div_20 n
      _ = (4 / 3 : ℝ) * (21 / 40 : ℝ) ^ 4 *
            (∑' n : ℕ, (((n : ℕ) : ℝ) + 3) * (21 / 40 : ℝ) ^ n) := by
            rw [tsum_mul_left]
      _ = (4 / 3 : ℝ) * (21 / 40 : ℝ) ^ 4 *
          (1 / (1 - (21 / 40 : ℝ)) ^ 2 +
            2 * (1 / (1 - (21 / 40 : ℝ)))) := by
            rw [taoSection7_arithGeom_three_tsum (21 / 40 : ℝ) hr]
  rw [hsplit_src, hsource_to_prime, hsplit_prime, htail_exact]
  norm_num [f, taoSection7PascalPrimeSourceMass_zero,
    taoSection7PascalPrimeSourceMass_one,
    taoSection7PascalPrimeMassOn_zero, taoSection7PascalPrimeMassOn_one]

/-- The Pascal-prime source exponential moment at ratio `21/20` is below `5/4`. -/
theorem taoSection7PascalPrimeSourceMass_pow_21_div_20_le_five_four :
    (∑' b : ℕ,
      taoSection7PascalPrimeSourceMass b * (21 / 20 : ℝ) ^ b) ≤
      5 / 4 := by
  rw [tsum_taoSection7PascalPrimeSourceMass_pow_21_div_20]
  norm_num

theorem taoSection7_exp_log_21_div_20_nat (b : ℕ) :
    Real.exp (Real.log (21 / 20 : ℝ) * (b : ℝ)) =
      (21 / 20 : ℝ) ^ b := by
  rw [show Real.log (21 / 20 : ℝ) * (b : ℝ) =
      (b : ℝ) * Real.log (21 / 20 : ℝ) by ring]
  rw [Real.exp_nat_mul]
  rw [Real.exp_log]
  norm_num

/--
Summability form of the Pascal-prime source exponential moment at
`alpha = log (21/20)`.
-/
theorem summable_taoSection7PascalPrimeSourceMass_exp_log_21_div_20 :
    Summable fun b : ℕ =>
      taoSection7PascalPrimeSourceMass b *
        Real.exp (Real.log (21 / 20 : ℝ) * (b : ℝ)) := by
  refine summable_taoSection7PascalPrimeSourceMass_pow_21_div_20.congr ?_
  intro b
  rw [taoSection7_exp_log_21_div_20_nat]

/--
Pascal-prime source exponential-moment bound used as the first terminal-tail
MGF producer.
-/
theorem taoSection7PascalPrimeSourceMass_exp_log_21_div_20_le :
    (∑' b : ℕ,
      taoSection7PascalPrimeSourceMass b *
        Real.exp (Real.log (21 / 20 : ℝ) * (b : ℝ))) ≤
      5 / 4 := by
  calc
    (∑' b : ℕ,
      taoSection7PascalPrimeSourceMass b *
        Real.exp (Real.log (21 / 20 : ℝ) * (b : ℝ)))
        = ∑' b : ℕ,
            taoSection7PascalPrimeSourceMass b * (21 / 20 : ℝ) ^ b := by
          apply tsum_congr
          intro b
          rw [taoSection7_exp_log_21_div_20_nat]
    _ ≤ 5 / 4 :=
      taoSection7PascalPrimeSourceMass_pow_21_div_20_le_five_four

end Tao
end Erdos1135
