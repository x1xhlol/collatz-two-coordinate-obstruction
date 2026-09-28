import Erdos1135.ND.Fourier.FixedTotalBadWindow
import Erdos1135.ND.Fourier.FiberFM1Core

/-!
# Fixed-Total Projected One-Step Oscillation

This leaf rewrites one nonterminal projection of a conditioned fixed-total
fiber using normalized T2.  FM1-core controls the enlarged-window mixture
components, while the checked T3/T4 bad-window probability and the full-L1
cap two control the complement.

The result is the endpoint-shaped high-regime step consumed by the later
FM1 telescope.  It does not handle the terminal projection or install a
generic public PMF/telescope framework.
-/

open scoped BigOperators

namespace Erdos1135
namespace ND

noncomputable section

private theorem ndPMF_bind_apply_toReal_eq_sum
    {α β : Type*} [Fintype α]
    (p : PMF α) (q : α → PMF β) (y : β) :
    ((p.bind q) y).toReal =
      ∑ s, (p s).toReal * (q s y).toReal := by
  rw [PMF.bind_apply, tsum_fintype, ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_mul]
  · intro s _hs
    exact ENNReal.mul_ne_top (p.apply_ne_top s) ((q s).apply_ne_top y)

private theorem ndTaoZModPowOscillation_bind_le_sum
    {n : ℕ} {α : Type*} [Fintype α]
    (p : PMF α) (q : α → PMF (ZMod (3 ^ n))) (m : ℕ) :
    Tao.taoZModPowOscillation m n
        (fun y => ((p.bind q) y).toReal) ≤
      ∑ s, (p s).toReal *
        Tao.taoZModPowOscillation m n
          (fun y => (q s y).toReal) := by
  calc
    Tao.taoZModPowOscillation m n
        (fun y => ((p.bind q) y).toReal) =
      Tao.taoZModPowOscillation m n
        (fun y => ∑ s, (p s).toReal * (q s y).toReal) := by
          congr 1
          funext y
          exact ndPMF_bind_apply_toReal_eq_sum p q y
    _ ≤ ∑ s, Tao.taoZModPowOscillation m n
          (fun y => (p s).toReal * (q s y).toReal) :=
      Tao.taoZModPowOscillation_sum_le_sum m n
        (fun s => fun y => (p s).toReal * (q s y).toReal)
    _ = ∑ s, (p s).toReal *
        Tao.taoZModPowOscillation m n
          (fun y => (q s y).toReal) := by
      apply Finset.sum_congr rfl
      intro s _hs
      exact ndTaoZModPowOscillation_mul_nonneg
        m n (p s).toReal ENNReal.toReal_nonneg
          (fun y => (q s y).toReal)

/-- One nonterminal high-regime projection of a conditioned length-`n`
fiber has the natural-exponent rate supplied by FM1-core and the checked
bad-window charge.  The projected law remains the marginal of the original
length-`n`, total-`L` fiber; it is not replaced by one conditioned child. -/
theorem ndSection7FiberPMF_projection_oscillation_le_oneStep
    (A n m j L : ℕ) (K Ccore : ℝ)
    (hCcore : 0 ≤ Ccore)
    (hj : 3 ≤ j) (hjn : j < n)
    (hmj : m ≤ j) (hhigh : 9 * j ≤ 10 * m)
    (hnL : n ≤ L) (hL3n : L ≤ 3 * n)
    (hwin : ndSection7M1Window K n L)
    (hu3 :
      Real.sqrt (63 * ((A : ℝ) + 2)) *
          Real.sqrt ((j : ℝ) * Real.log (j : ℝ)) ≤
        3 * (j : ℝ))
    (hcore : ndSection7ConditionedFM1CoreNatAt (A + 1)
      (K + Real.sqrt (63 * ((A : ℝ) + 2))) Ccore) :
    Tao.taoZModPowOscillation m j
      (fun y => (((ndSection7FiberPMF n L (by omega) hnL).map
        (Tao.taoZModThreeProjection hjn.le)) y).toReal) ≤
      (Ccore + 4) / (j : ℝ) ^ (A + 1) := by
  classical
  letI : Fintype (NDFixedTotalSplitIndex j (n - j) L) :=
    ndFixedTotalSplitIndexFintypeOfLe j (n - j) L (by omega)
  let p : PMF (NDFixedTotalSplitIndex j (n - j) L) :=
    ndFixedTotalSplitIndexPMF j (n - j) L (by omega) (by omega)
  let q : NDFixedTotalSplitIndex j (n - j) L → PMF (ZMod (3 ^ j)) :=
    fun s => ndSection7FiberPMF j s.headTotal (by omega) s.headLength_le
  let Good : NDFixedTotalSplitIndex j (n - j) L → Prop :=
    fun s => ndSection7M1Window
      (K + Real.sqrt (63 * ((A : ℝ) + 2))) j s.headTotal
  have hmix :
      (ndSection7FiberPMF n L (by omega) hnL).map
          (Tao.taoZModThreeProjection hjn.le) =
        p.bind q := by
    have hparent :
        (ndSection7FiberPMF n L (by omega) hnL).map
            (Tao.taoZModThreeProjection hjn.le) =
          (ndSection7FiberPMF (j + (n - j)) L (by omega) (by omega)).map
            (Tao.taoZModThreeProjection
              (Nat.le_add_right j (n - j))) := by
      have hcongr : ∀ (a b : ℕ), a = b →
          ∀ (ha : 0 < a) (hb : 0 < b) (haL : a ≤ L) (hbL : b ≤ L)
            (hja : j ≤ a) (hjb : j ≤ b),
            (ndSection7FiberPMF a L ha haL).map
                (Tao.taoZModThreeProjection hja) =
              (ndSection7FiberPMF b L hb hbL).map
                (Tao.taoZModThreeProjection hjb) := by
        intro a b hab ha hb haL hbL hja hjb
        subst b
        rfl
      exact hcongr n (j + (n - j))
        (Nat.add_sub_of_le hjn.le).symm
        (by omega) (by omega) hnL (by omega)
        hjn.le (Nat.le_add_right j (n - j))
    exact hparent.trans
      (ndSection7FiberPMF_map_projection_eq_splitBind
        j (n - j) L (by omega) (by omega))
  have hbad :
      Tao.pmfProb p {s | ¬ Good s} ≤
        2 / (j : ℝ) ^ (A + 2) := by
    rw [Tao.pmfProb_eq_toOuterMeasure_toReal]
    simpa only [p, Good] using
      (ndFixedTotalSplitIndexPMF_badWindow_le
        A n j L K hj hjn hnL hL3n hwin hu3)
  have hcoreDenom : 0 ≤ Ccore / (j : ℝ) ^ (A + 1) := by
    exact div_nonneg hCcore (by positivity)
  have hbadSum :
      (∑ s, (p s).toReal * (if Good s then 0 else 2)) =
        2 * Tao.pmfProb p {s | ¬ Good s} := by
    unfold Tao.pmfProb
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s _hs
    by_cases hs : Good s
    · simp [hs]
    · simp [hs]
      ring
  rw [hmix]
  calc
    Tao.taoZModPowOscillation m j
        (fun y => ((p.bind q) y).toReal) ≤
      ∑ s, (p s).toReal *
        Tao.taoZModPowOscillation m j
          (fun y => (q s y).toReal) :=
      ndTaoZModPowOscillation_bind_le_sum p q m
    _ ≤ ∑ s, (p s).toReal *
        (Ccore / (j : ℝ) ^ (A + 1) +
          if Good s then 0 else 2) := by
      apply Finset.sum_le_sum
      intro s _hs
      apply mul_le_mul_of_nonneg_left _ ENNReal.toReal_nonneg
      by_cases hs : Good s
      · rw [if_pos hs, add_zero]
        exact hcore j (by omega) m hmj hhigh
          s.headTotal s.headLength_le hs
      · rw [if_neg hs]
        have htwo :
            Tao.taoZModPowOscillation m j
                (fun y => (q s y).toReal) ≤ 2 := by
          simpa only [q] using
            (ndSection7FiberPMF_oscillation_le_two
              m j s.headTotal (by omega) hmj s.headLength_le)
        exact htwo.trans (by linarith)
    _ = Ccore / (j : ℝ) ^ (A + 1) +
        2 * Tao.pmfProb p {s | ¬ Good s} := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul,
        Tao.pmf_sum_toReal p, one_mul, hbadSum]
    _ ≤ Ccore / (j : ℝ) ^ (A + 1) +
        2 * (2 / (j : ℝ) ^ (A + 2)) := by
      exact add_le_add le_rfl
        (mul_le_mul_of_nonneg_left hbad (by norm_num : (0 : ℝ) ≤ 2))
    _ = Ccore / (j : ℝ) ^ (A + 1) +
        4 / (j : ℝ) ^ (A + 2) := by ring
    _ ≤ Ccore / (j : ℝ) ^ (A + 1) +
        4 / (j : ℝ) ^ (A + 1) := by
      have hjR : (0 : ℝ) < (j : ℝ) := by positivity
      have hjOne : (1 : ℝ) ≤ (j : ℝ) := by
        exact_mod_cast (show 1 ≤ j by omega)
      have hpow :
          (j : ℝ) ^ (A + 1) ≤ (j : ℝ) ^ (A + 2) := by
        calc
          (j : ℝ) ^ (A + 1) = (j : ℝ) ^ (A + 1) * 1 := by ring
          _ ≤ (j : ℝ) ^ (A + 1) * (j : ℝ) :=
            mul_le_mul_of_nonneg_left hjOne (pow_nonneg hjR.le _)
          _ = (j : ℝ) ^ ((A + 1) + 1) := (pow_succ _ _).symm
          _ = (j : ℝ) ^ (A + 2) := by congr 1
      exact add_le_add le_rfl
        (div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 4)
          (pow_pos hjR _) hpow)
    _ = (Ccore + 4) / (j : ℝ) ^ (A + 1) := by ring

end

end ND
end Erdos1135
