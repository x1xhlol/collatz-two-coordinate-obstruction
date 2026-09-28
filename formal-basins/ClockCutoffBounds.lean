import LogarithmicCumulative
import ClockMeanSqueeze
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

open Filter Topology
open CollatzCanonical.DirichletAbelian

namespace CollatzCanonical.ClockSqueeze

noncomputable def logTerm (w : ℕ → ℝ) (t : ℝ) (n : ℕ) : ℝ :=
  if Real.log (n + 1 : ℕ) ≤ t then w (n + 1) / (n + 1 : ℕ) else 0

noncomputable def clockTerm (w : ℕ → ℝ) (d : ℕ → ℕ) (K n : ℕ) : ℝ :=
  if d (n + 1) ≤ K then w (n + 1) / (n + 1 : ℕ) else 0

noncomputable def clockBadWeight (w : ℕ → ℝ) (d : ℕ → ℕ)
    (lam ε : ℝ) (q : ℕ) : ℝ :=
  if (1 - ε) * Real.log (q : ℝ) / lam ≤ (d q : ℝ) ∧
      (d q : ℝ) ≤ (1 + ε) * Real.log (q : ℝ) / lam then 0 else w q

theorem logTerm_nonneg {w : ℕ → ℝ} (hw : ∀ q, 0 ≤ w q) (t : ℝ) (n : ℕ) :
    0 ≤ logTerm w t n := by
  unfold logTerm
  split_ifs
  · exact div_nonneg (hw _) (by positivity)
  · exact le_rfl

theorem logTerm_summable (w : ℕ → ℝ) (t : ℝ) : Summable (logTerm w t) := by
  apply summable_of_ne_finset_zero (s := Finset.range ⌊Real.exp t⌋₊)
  intro n hn
  unfold logTerm
  apply if_neg
  intro h
  apply hn
  rw [Finset.mem_range, Nat.lt_iff_add_one_le, Nat.le_floor_iff (Real.exp_pos t).le,
    ← Real.log_le_iff_le_exp (by positivity)]
  exact h

theorem logTerm_tsum (w : ℕ → ℝ) (t : ℝ) :
    (∑' n, logTerm w t n) = logarithmicCumulative w t :=
  (logarithmicCumulative_eq_tsum w t).symm

theorem clockTerm_nonneg {w : ℕ → ℝ} (hw : ∀ q, 0 ≤ w q)
    (d : ℕ → ℕ) (K n : ℕ) : 0 ≤ clockTerm w d K n := by
  unfold clockTerm
  split_ifs
  · exact div_nonneg (hw _) (by positivity)
  · exact le_rfl

theorem clockBadWeight_nonneg {w : ℕ → ℝ} (hw : ∀ q, 0 ≤ w q)
    (d : ℕ → ℕ) (lam ε : ℝ) (q : ℕ) : 0 ≤ clockBadWeight w d lam ε q := by
  unfold clockBadWeight
  split_ifs
  · exact le_rfl
  · exact hw q

theorem clock_lower_term {w : ℕ → ℝ} (hw : ∀ q, 0 ≤ w q)
    (d : ℕ → ℕ) {lam ε : ℝ} (hlam : 0 < lam) (hε : 0 < ε) (K n : ℕ) :
    logTerm w ((lam / (1 + ε)) * (K : ℝ)) n ≤ clockTerm w d K n +
      logTerm (clockBadWeight w d lam ε) ((lam / (1 + ε)) * (K : ℝ)) n := by
  by_cases hlog : Real.log (n + 1 : ℕ) ≤ (lam / (1 + ε)) * (K : ℝ)
  · simp only [logTerm, if_pos hlog]
    by_cases hgood : (1 - ε) * Real.log (n + 1 : ℕ) / lam ≤ (d (n + 1) : ℝ) ∧
        (d (n + 1) : ℝ) ≤ (1 + ε) * Real.log (n + 1 : ℕ) / lam
    · have hp : 0 < 1 + ε := by linarith
      have hm := mul_le_mul_of_nonneg_left hlog hp.le
      have he : (1 + ε) * ((lam / (1 + ε)) * (K : ℝ)) = lam * K := by field_simp
      rw [he] at hm
      have hd := (le_div_iff₀ hlam).mp hgood.2
      have hdK : d (n + 1) ≤ K := by exact_mod_cast (show (d (n + 1) : ℝ) ≤ K by nlinarith)
      simp only [clockTerm, if_pos hdK, clockBadWeight, if_pos hgood, zero_div, add_zero]
      exact le_rfl
    · simp only [clockBadWeight, if_neg hgood]
      exact le_add_of_nonneg_left (clockTerm_nonneg hw d K n)
  · simp only [logTerm, if_neg hlog, add_zero]
    exact clockTerm_nonneg hw d K n

theorem clock_lower_cumulative {w : ℕ → ℝ} (hw : ∀ q, 0 ≤ w q)
    (d : ℕ → ℕ) {lam ε : ℝ} (hlam : 0 < lam) (hε : 0 < ε) (K : ℕ)
    (hs : Summable (clockTerm w d K)) :
    logarithmicCumulative w ((lam / (1 + ε)) * (K : ℝ)) -
      logarithmicCumulative (clockBadWeight w d lam ε) ((lam / (1 + ε)) * (K : ℝ)) ≤
      ∑' n, clockTerm w d K n := by
  have h := Summable.tsum_le_tsum (clock_lower_term hw d hlam hε K)
    (logTerm_summable _ _) (hs.add (logTerm_summable _ _))
  rw [Summable.tsum_add hs (logTerm_summable _ _), logTerm_tsum, logTerm_tsum] at h
  linarith

theorem clockTerm_le_weight {w : ℕ → ℝ} (hw : ∀ q, 0 ≤ w q)
    (d : ℕ → ℕ) (K n : ℕ) : clockTerm w d K n ≤ w (n + 1) / (n + 1 : ℕ) := by
  unfold clockTerm
  split_ifs
  · exact le_rfl
  · exact div_nonneg (hw _) (by positivity)

theorem clock_upper_head_term {w : ℕ → ℝ} (hw : ∀ q, 0 ≤ w q)
    (d : ℕ → ℕ) {lam ε : ℝ} (hlam : 0 < lam) (hε : ε < 1)
    (K n : ℕ) (t : ℝ) :
    (if Real.log (n + 1 : ℕ) ≤ t then clockTerm w d K n else 0) ≤
      logTerm w ((lam / (1 - ε)) * (K : ℝ)) n +
      logTerm (clockBadWeight w d lam ε) t n := by
  by_cases ht : Real.log (n + 1 : ℕ) ≤ t
  · rw [if_pos ht]
    by_cases hgood : (1 - ε) * Real.log (n + 1 : ℕ) / lam ≤ (d (n + 1) : ℝ) ∧
        (d (n + 1) : ℝ) ≤ (1 + ε) * Real.log (n + 1 : ℕ) / lam
    · by_cases hK : d (n + 1) ≤ K
      · have hp : 0 < 1 - ε := by linarith
        have hd : (d (n + 1) : ℝ) ≤ K := by exact_mod_cast hK
        have hm := mul_le_mul_of_nonneg_right hd hlam.le
        have he : (1 - ε) * ((lam / (1 - ε)) * (K : ℝ)) = (K : ℝ) * lam := by field_simp
        have hl := (div_le_iff₀ hlam).mp hgood.1
        have hlog : Real.log (n + 1 : ℕ) ≤ (lam / (1 - ε)) * (K : ℝ) := by nlinarith
        simp only [clockTerm, if_pos hK, logTerm, if_pos ht, if_pos hlog,
          clockBadWeight, if_pos hgood, zero_div, add_zero]
        exact le_rfl
      · rw [clockTerm, if_neg hK]
        exact add_nonneg (logTerm_nonneg hw _ _)
          (logTerm_nonneg (clockBadWeight_nonneg hw d lam ε) _ _)
    · have hb : logTerm (clockBadWeight w d lam ε) t n = w (n + 1) / (n + 1 : ℕ) := by
        simp only [logTerm, if_pos ht, clockBadWeight, if_neg hgood]
      rw [hb]
      exact (clockTerm_le_weight hw d K n).trans
        (le_add_of_nonneg_left (logTerm_nonneg hw _ _))
  · rw [if_neg ht]
    exact add_nonneg (logTerm_nonneg hw _ _)
      (logTerm_nonneg (clockBadWeight_nonneg hw d lam ε) _ _)

theorem clock_upper_cumulative {w : ℕ → ℝ} (hw : ∀ q, 0 ≤ w q)
    (d : ℕ → ℕ) {lam ε : ℝ} (hlam : 0 < lam) (hε : ε < 1)
    (K : ℕ) (t : ℝ) (hs : Summable (clockTerm w d K)) :
    (∑' n, clockTerm w d K n) ≤
      logarithmicCumulative w ((lam / (1 - ε)) * (K : ℝ)) +
      logarithmicCumulative (clockBadWeight w d lam ε) t +
      ∑' n, if t < Real.log (n + 1 : ℕ) then clockTerm w d K n else 0 := by
  let head : ℕ → ℝ := fun n => if Real.log (n + 1 : ℕ) ≤ t then clockTerm w d K n else 0
  let tail : ℕ → ℝ := fun n => if t < Real.log (n + 1 : ℕ) then clockTerm w d K n else 0
  have hh : Summable head := by
    apply Summable.of_nonneg_of_le _ _ hs
    · intro n
      dsimp only [head]
      split_ifs
      · exact clockTerm_nonneg hw d K n
      · exact le_rfl
    · intro n
      dsimp only [head]
      split_ifs
      · exact le_rfl
      · exact clockTerm_nonneg hw d K n
  have ht : Summable tail := by
    apply Summable.of_nonneg_of_le _ _ hs
    · intro n
      dsimp only [tail]
      split_ifs
      · exact clockTerm_nonneg hw d K n
      · exact le_rfl
    · intro n
      dsimp only [tail]
      split_ifs
      · exact le_rfl
      · exact clockTerm_nonneg hw d K n
  have hsplit : clockTerm w d K = fun n => head n + tail n := by
    funext n
    dsimp only [head, tail]
    by_cases h : Real.log (n + 1 : ℕ) ≤ t
    · simp only [if_pos h, if_neg (not_lt.mpr h), add_zero]
    · simp only [if_neg h, if_pos (lt_of_not_ge h), zero_add]
  have hb := Summable.tsum_le_tsum (fun n => clock_upper_head_term hw d hlam hε K n t)
    hh ((logTerm_summable _ _).add (logTerm_summable _ _))
  rw [Summable.tsum_add (logTerm_summable _ _) (logTerm_summable _ _),
    logTerm_tsum, logTerm_tsum] at hb
  calc
    (∑' n, clockTerm w d K n) = (∑' n, head n) + ∑' n, tail n := by
      rw [hsplit, Summable.tsum_add hh ht]
    _ ≤ _ := add_le_add hb le_rfl

end CollatzCanonical.ClockSqueeze
