import Erdos1135.Tao.Probability.GatedSubmassComplement
import Erdos1135.Tao.Section6.FiberAverageDFT

/-!
# Algebra of Tao's Fine-Scale Oscillation

This leaf proves linearity, finite-sum subadditivity, contraction of the
normalized reduction-fiber average, and the sharp uniform factor-two event
replacement bound.  Only contraction and its consequences require `m ≤ n`.
-/

open scoped BigOperators
open scoped ZMod

namespace Erdos1135
namespace Tao

noncomputable section

/-- Normalized averaging over one reduction fiber. -/
noncomputable def zmodPowFiberAverage (m n : ℕ)
    (c : ZMod (3 ^ n) → ℝ) (y : ZMod (3 ^ n)) : ℝ :=
  zmodPowFiberAverageScale m n * zmodPowFiberSum m n c y

theorem zmodPowFiberSum_add (m n : ℕ)
    (c d : ZMod (3 ^ n) → ℝ) (y : ZMod (3 ^ n)) :
    zmodPowFiberSum m n (fun x => c x + d x) y =
      zmodPowFiberSum m n c y + zmodPowFiberSum m n d y := by
  classical
  unfold zmodPowFiberSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hxy : zmodSameResidueModPow m n x y <;> simp [hxy]

theorem zmodPowFiberSum_sub (m n : ℕ)
    (c d : ZMod (3 ^ n) → ℝ) (y : ZMod (3 ^ n)) :
    zmodPowFiberSum m n (fun x => c x - d x) y =
      zmodPowFiberSum m n c y - zmodPowFiberSum m n d y := by
  classical
  unfold zmodPowFiberSum
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hxy : zmodSameResidueModPow m n x y <;> simp [hxy]

theorem zmodPowFiberSum_sum
    {ι : Type*} [Fintype ι] (m n : ℕ)
    (c : ι → ZMod (3 ^ n) → ℝ) (y : ZMod (3 ^ n)) :
    zmodPowFiberSum m n (fun x => ∑ i, c i x) y =
      ∑ i, zmodPowFiberSum m n (c i) y := by
  classical
  unfold zmodPowFiberSum
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x hx
  by_cases hxy : zmodSameResidueModPow m n x y <;> simp [hxy]

theorem zmodPowFiberAverage_add (m n : ℕ)
    (c d : ZMod (3 ^ n) → ℝ) (y : ZMod (3 ^ n)) :
    zmodPowFiberAverage m n (fun x => c x + d x) y =
      zmodPowFiberAverage m n c y + zmodPowFiberAverage m n d y := by
  unfold zmodPowFiberAverage
  rw [zmodPowFiberSum_add]
  ring

theorem zmodPowFiberAverage_sub (m n : ℕ)
    (c d : ZMod (3 ^ n) → ℝ) (y : ZMod (3 ^ n)) :
    zmodPowFiberAverage m n (fun x => c x - d x) y =
      zmodPowFiberAverage m n c y - zmodPowFiberAverage m n d y := by
  unfold zmodPowFiberAverage
  rw [zmodPowFiberSum_sub]
  ring

theorem zmodPowFiberAverage_sum
    {ι : Type*} [Fintype ι] (m n : ℕ)
    (c : ι → ZMod (3 ^ n) → ℝ) (y : ZMod (3 ^ n)) :
    zmodPowFiberAverage m n (fun x => ∑ i, c i x) y =
      ∑ i, zmodPowFiberAverage m n (c i) y := by
  classical
  unfold zmodPowFiberAverage
  rw [zmodPowFiberSum_sum, Finset.mul_sum]

/-- The normalized repeated-ambient fiber average is an `L1` contraction. -/
theorem zmodPowFiberAverage_sum_abs_le
    {m n : ℕ} (hmn : m ≤ n) (c : ZMod (3 ^ n) → ℝ) :
    (∑ y : ZMod (3 ^ n), |zmodPowFiberAverage m n c y|) ≤
      ∑ y : ZMod (3 ^ n), |c y| := by
  classical
  let K := (taoZModThreeProjection hmn).toAddMonoidHom.ker
  have hscale : 0 ≤ zmodPowFiberAverageScale m n := by
    unfold zmodPowFiberAverageScale
    positivity
  have hcard : Fintype.card K = 3 ^ (n - m) := by
    rw [← Nat.card_eq_fintype_card]
    exact zmodPowProjectionKer_card hmn
  have hcancel :
      zmodPowFiberAverageScale m n * (Fintype.card K : ℝ) = 1 := by
    rw [hcard]
    simpa only [Nat.cast_pow, Nat.cast_ofNat] using
      zmodPowFiberAverageScale_mul_card hmn
  simp_rw [zmodPowFiberAverage, zmodPowFiberSum_eq_sum_projection_ker hmn]
  calc
    (∑ y : ZMod (3 ^ n),
        |zmodPowFiberAverageScale m n *
          ∑ h : K, c (y + h.1)|) ≤
      ∑ y : ZMod (3 ^ n),
        zmodPowFiberAverageScale m n *
          ∑ h : K, |c (y + h.1)| := by
            apply Finset.sum_le_sum
            intro y hy
            rw [abs_mul, abs_of_nonneg hscale]
            exact mul_le_mul_of_nonneg_left
              (Finset.abs_sum_le_sum_abs _ _) hscale
    _ = zmodPowFiberAverageScale m n *
        ∑ y : ZMod (3 ^ n), ∑ h : K, |c (y + h.1)| := by
          rw [Finset.mul_sum]
    _ = zmodPowFiberAverageScale m n *
        ∑ h : K, ∑ y : ZMod (3 ^ n), |c (y + h.1)| := by
          rw [Finset.sum_comm]
    _ = zmodPowFiberAverageScale m n *
        ∑ h : K, ∑ y : ZMod (3 ^ n), |c y| := by
          congr 1
          apply Finset.sum_congr rfl
          intro h hh
          apply Fintype.sum_equiv (Equiv.addRight h.1)
          intro y
          simp
    _ = zmodPowFiberAverageScale m n *
        (Fintype.card K : ℝ) * ∑ y : ZMod (3 ^ n), |c y| := by
          simp
          ring
    _ = ∑ y : ZMod (3 ^ n), |c y| := by
          rw [hcancel, one_mul]

/-- Binary subadditivity of oscillation; no scale-order hypothesis is needed. -/
theorem taoZModPowOscillation_add_le
    (m n : ℕ) (c d : ZMod (3 ^ n) → ℝ) :
    taoZModPowOscillation m n (fun y => c y + d y) ≤
      taoZModPowOscillation m n c + taoZModPowOscillation m n d := by
  classical
  unfold taoZModPowOscillation
  calc
    (∑ y : ZMod (3 ^ n),
        |c y + d y - zmodPowFiberAverageScale m n *
          zmodPowFiberSum m n (fun x => c x + d x) y|) =
      ∑ y : ZMod (3 ^ n),
        |(c y - zmodPowFiberAverageScale m n * zmodPowFiberSum m n c y) +
          (d y - zmodPowFiberAverageScale m n * zmodPowFiberSum m n d y)| := by
            apply Finset.sum_congr rfl
            intro y hy
            rw [zmodPowFiberSum_add]
            ring
    _ ≤ ∑ y : ZMod (3 ^ n),
        (|c y - zmodPowFiberAverageScale m n * zmodPowFiberSum m n c y| +
          |d y - zmodPowFiberAverageScale m n * zmodPowFiberSum m n d y|) := by
            apply Finset.sum_le_sum
            intro y hy
            exact abs_add_le _ _
    _ = (∑ y : ZMod (3 ^ n),
          |c y - zmodPowFiberAverageScale m n * zmodPowFiberSum m n c y|) +
        ∑ y : ZMod (3 ^ n),
          |d y - zmodPowFiberAverageScale m n * zmodPowFiberSum m n d y| := by
            rw [Finset.sum_add_distrib]

/-- Finite-sum subadditivity of oscillation. -/
theorem taoZModPowOscillation_sum_le_sum
    {ι : Type*} [Fintype ι] (m n : ℕ)
    (c : ι → ZMod (3 ^ n) → ℝ) :
    taoZModPowOscillation m n (fun y => ∑ i, c i y) ≤
      ∑ i, taoZModPowOscillation m n (c i) := by
  classical
  unfold taoZModPowOscillation
  calc
    (∑ y : ZMod (3 ^ n),
        |(∑ i, c i y) - zmodPowFiberAverageScale m n *
          zmodPowFiberSum m n (fun x => ∑ i, c i x) y|) =
      ∑ y : ZMod (3 ^ n),
        |∑ i, (c i y - zmodPowFiberAverageScale m n *
          zmodPowFiberSum m n (c i) y)| := by
            apply Finset.sum_congr rfl
            intro y hy
            rw [zmodPowFiberSum_sum, Finset.mul_sum,
              ← Finset.sum_sub_distrib]
    _ ≤ ∑ y : ZMod (3 ^ n),
        ∑ i, |c i y - zmodPowFiberAverageScale m n *
          zmodPowFiberSum m n (c i) y| := by
            apply Finset.sum_le_sum
            intro y hy
            exact Finset.abs_sum_le_sum_abs _ _
    _ = ∑ i, ∑ y : ZMod (3 ^ n),
        |c i y - zmodPowFiberAverageScale m n *
          zmodPowFiberSum m n (c i) y| := by
            rw [Finset.sum_comm]

/-- Oscillation is controlled by twice the full `L1` mass. -/
theorem taoZModPowOscillation_le_two_mul_sum_abs
    {m n : ℕ} (hmn : m ≤ n) (c : ZMod (3 ^ n) → ℝ) :
    taoZModPowOscillation m n c ≤ 2 * ∑ y, |c y| := by
  classical
  unfold taoZModPowOscillation
  calc
    (∑ y : ZMod (3 ^ n),
        |c y - zmodPowFiberAverage m n c y|) ≤
      ∑ y : ZMod (3 ^ n), (|c y| + |zmodPowFiberAverage m n c y|) := by
        apply Finset.sum_le_sum
        intro y hy
        exact abs_sub _ _
    _ = (∑ y : ZMod (3 ^ n), |c y|) +
        ∑ y : ZMod (3 ^ n), |zmodPowFiberAverage m n c y| := by
          rw [Finset.sum_add_distrib]
    _ ≤ (∑ y : ZMod (3 ^ n), |c y|) +
        ∑ y : ZMod (3 ^ n), |c y| := by
          exact add_le_add (le_refl _) (zmodPowFiberAverage_sum_abs_le hmn c)
    _ = 2 * ∑ y : ZMod (3 ^ n), |c y| := by ring

/-- Uniform factor-two Lipschitz replacement for oscillation. -/
theorem taoZModPowOscillation_le_add_two_mul_sum_abs_sub
    {m n : ℕ} (hmn : m ≤ n)
    (c d : ZMod (3 ^ n) → ℝ) :
    taoZModPowOscillation m n c ≤
      taoZModPowOscillation m n d + 2 * ∑ y, |c y - d y| := by
  calc
    taoZModPowOscillation m n c =
        taoZModPowOscillation m n (fun y => d y + (c y - d y)) := by
          congr 1
          funext y
          ring
    _ ≤ taoZModPowOscillation m n d +
        taoZModPowOscillation m n (fun y => c y - d y) :=
      taoZModPowOscillation_add_le m n d (fun y => c y - d y)
    _ ≤ taoZModPowOscillation m n d + 2 * ∑ y, |c y - d y| := by
      exact add_le_add (le_refl _)
        (taoZModPowOscillation_le_two_mul_sum_abs hmn
          (fun y => c y - d y))

/-- A mapped PMF differs from its gated submass by at most twice the one-time
parent rejected mass. -/
theorem taoZModPowOscillation_map_le_gated_add_two_rejected
    {α : Type*} (p : PMF α) (G : α → Prop)
    {m n : ℕ} (hmn : m ≤ n) (f : α → ZMod (3 ^ n)) :
    taoZModPowOscillation m n (fun y => ((p.map f) y).toReal) ≤
      taoZModPowOscillation m n (taoGatedSubmass p G f) +
        2 * taoGatedRejectedMass p G f := by
  have hdiff :
      (∑ y : ZMod (3 ^ n),
          |((p.map f) y).toReal - taoGatedSubmass p G f y|) =
        taoGatedRejectedMass p G f := by
    calc
      (∑ y : ZMod (3 ^ n),
          |((p.map f) y).toReal - taoGatedSubmass p G f y|) =
        ∑ y : ZMod (3 ^ n),
          taoGatedSubmass p (fun a => ¬ G a) f y := by
            apply Finset.sum_congr rfl
            intro y hy
            rw [taoGatedSubmass_map_apply_split]
            rw [add_sub_cancel_left]
            exact abs_of_nonneg
              (taoGatedSubmass_nonneg p (fun a => ¬ G a) f y)
      _ = taoGatedRejectedMass p G f :=
        taoGatedSubmass_complement_sum_eq_rejectedMass p G f
  calc
    taoZModPowOscillation m n (fun y => ((p.map f) y).toReal) ≤
        taoZModPowOscillation m n (taoGatedSubmass p G f) +
          2 * ∑ y, |((p.map f) y).toReal - taoGatedSubmass p G f y| :=
      taoZModPowOscillation_le_add_two_mul_sum_abs_sub hmn _ _
    _ = taoZModPowOscillation m n (taoGatedSubmass p G f) +
        2 * taoGatedRejectedMass p G f := by rw [hdiff]

end

end Tao
end Erdos1135
