import HittingTimeClassification
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

namespace CollatzCylinderPacking.Arithmetic

/-- Multiplicative shortcut weight through n steps. -/
noncomputable def orbitRatio (n q : ℕ) : ℝ :=
  (3 : ℝ) ^ oddCount n q / (2 : ℝ) ^ n

theorem orbitRatio_pos (n q : ℕ) : 0 < orbitRatio n q := by
  unfold orbitRatio
  positivity

/-- Exact multiplicativity under concatenating actual shortcut paths. -/
theorem orbitRatio_add (a b q : ℕ) :
    orbitRatio (a + b) q = orbitRatio a q * orbitRatio b (iterate a q) := by
  simp only [orbitRatio, oddCount_add, pow_add]
  rw [div_mul_div_comm]

/-- A positive periodic target must encounter an odd source in each period. -/
theorem positive_cycle_oddCount_pos {N r : ℕ} (hN : 0 < N) (hr : 0 < r)
    (hreturn : iterate r N = N) : 0 < oddCount r N := by
  by_contra h
  have hz : oddCount r N = 0 := by omega
  have hb := (scaled_bounds r N).2
  rw [hreturn, hz] at hb
  simp only [pow_zero, one_mul, Nat.sub_zero] at hb
  have htwo : 2 ≤ (2 : ℕ) ^ r := by
    simpa using Nat.pow_le_pow_right (by decide : 1 ≤ (2 : ℕ)) hr
  nlinarith

theorem exists_odd_source_of_oddCount_pos {n q : ℕ} (h : 0 < oddCount n q) :
    ∃ i : ℕ, i < n ∧ iterate i q % 2 = 1 := by
  induction n with
  | zero => simp [oddCount] at h
  | succ n ih =>
    by_cases hn : 0 < oddCount n q
    · obtain ⟨i, hi, ho⟩ := ih hn
      exact ⟨i, by omega, ho⟩
    · have hz : oddCount n q = 0 := by omega
      simp only [oddCount, hz, Nat.zero_add] at h
      exact ⟨n, by omega, by omega⟩

theorem pathCorrection_gt_one_of_oddCount_pos {n q : ℕ} (hq : 0 < q)
    (hodd : 0 < oddCount n q) : 1 < pathCorrection n q := by
  obtain ⟨i, hi, ho⟩ := exists_odd_source_of_oddCount_pos hodd
  unfold pathCorrection
  have hone : (1 : ℝ) = ∏ _j ∈ Finset.range n, (1 : ℝ) := by simp
  conv_lhs => rw [hone]
  apply Finset.prod_lt_prod (fun _ _ => by norm_num)
  · intro j _
    linarith [CollatzCanonical.Correction.oddCorrection_nonneg (iterate j q)]
  · refine ⟨i, Finset.mem_range.mpr hi, ?_⟩
    have hp : 0 < (iterate i q : ℝ) := by
      exact_mod_cast CollatzCanonical.Correction.iterate_pos i hq
    simp only [CollatzCanonical.Correction.oddCorrection, ho, if_true]
    have hinv : 0 < (3 * (iterate i q : ℝ))⁻¹ := by positivity
    linarith

/-- On an actual cycle the shortcut ratio equals reciprocal correction. -/
theorem cycle_ratio_eq_pathWeight {N r : ℕ} (hN : 0 < N)
    (hreturn : iterate r N = N) : orbitRatio r N = pathWeight r N := by
  have h := hitting_path_weight hN hreturn
  have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hN
  rw [one_div_pow, mul_one_div] at h
  change orbitRatio r N = _ at h
  convert h using 1
  field_simp

/-- The loop weight is strictly between zero and one for every actual
positive cycle; contraction is derived, not supplied as an assumption. -/
theorem positive_cycle_ratio_bounds {N r : ℕ} (hN : 0 < N) (hr : 0 < r)
    (hreturn : iterate r N = N) : 0 < orbitRatio r N ∧ orbitRatio r N < 1 := by
  refine ⟨orbitRatio_pos r N, ?_⟩
  rw [cycle_ratio_eq_pathWeight hN hreturn, pathWeight]
  exact inv_lt_one_of_one_lt₀ (pathCorrection_gt_one_of_oddCount_pos hN
    (positive_cycle_oddCount_pos hN hr hreturn))

/-- Repeating an actual period raises its loop weight to the repeat count. -/
theorem orbitRatio_mul_period {N r : ℕ} (hreturn : iterate r N = N) (j : ℕ) :
    orbitRatio (j * r) N = (orbitRatio r N) ^ j := by
  induction j with
  | zero => simp [orbitRatio, oddCount]
  | succ j ih =>
    rw [Nat.succ_mul, orbitRatio_add, iterate_mul_period hreturn, ih, pow_succ]

/-- Exact weight of a hitting prefix followed by j complete period loops. -/
theorem orbitRatio_hit_plus_periods {q N τ r : ℕ} (hhit : iterate τ q = N)
    (hreturn : iterate r N = N) (j : ℕ) :
    orbitRatio (τ + j * r) q = orbitRatio τ q * (orbitRatio r N) ^ j := by
  rw [orbitRatio_add, hhit, orbitRatio_mul_period hreturn]

theorem orbitRatio_hit_plus_periods_rpow {q N τ r : ℕ} (hhit : iterate τ q = N)
    (hreturn : iterate r N = N) (j : ℕ) (s : ℝ) :
    (orbitRatio (τ + j * r) q) ^ s =
      (orbitRatio τ q) ^ s * ((orbitRatio r N) ^ s) ^ j := by
  rw [orbitRatio_hit_plus_periods hhit hreturn j,
    Real.mul_rpow (orbitRatio_pos τ q).le (pow_nonneg (orbitRatio_pos r N).le j),
    ← Real.rpow_pow_comm (orbitRatio_pos r N).le s j]

/-- The actual per-endpoint all-hit series is geometric when its target is
periodic. The least-period and first-hit predicates identify all its times. -/
theorem first_hit_loop_rpow_hasSum {q N τ r : ℕ} (hN : 0 < N)
    (hfirst : FirstHit q N τ) (hperiod : LeastPositivePeriod N r)
    {s : ℝ} (hs : 0 < s) :
    HasSum (fun j : ℕ => (orbitRatio (τ + j * r) q) ^ s)
      ((orbitRatio τ q) ^ s / (1 - (orbitRatio r N) ^ s)) := by
  have hb := positive_cycle_ratio_bounds hN hperiod.positive hperiod.returns
  have hb0 : 0 ≤ (orbitRatio r N) ^ s := (Real.rpow_pos_of_pos hb.1 s).le
  have hb1 : (orbitRatio r N) ^ s < 1 := Real.rpow_lt_one hb.1.le hb.2 hs
  have hgeom := (hasSum_geometric_of_lt_one hb0 hb1).mul_left ((orbitRatio τ q) ^ s)
  have he : (fun j : ℕ => (orbitRatio (τ + j * r) q) ^ s) =
      (fun j : ℕ => (orbitRatio τ q) ^ s * ((orbitRatio r N) ^ s) ^ j) := by
    funext j
    exact orbitRatio_hit_plus_periods_rpow hfirst.1 hperiod.returns j s
  rw [he]
  simpa only [div_eq_mul_inv] using hgeom

theorem first_hit_loop_rpow_tsum {q N τ r : ℕ} (hN : 0 < N)
    (hfirst : FirstHit q N τ) (hperiod : LeastPositivePeriod N r)
    {s : ℝ} (hs : 0 < s) :
    (∑' j : ℕ, (orbitRatio (τ + j * r) q) ^ s) =
      (orbitRatio τ q) ^ s / (1 - (orbitRatio r N) ^ s) :=
  (first_hit_loop_rpow_hasSum hN hfirst hperiod hs).tsum_eq

/-- The first-hit scalar in the geometric formula is the paper's N w_N(q)/q. -/
theorem orbitRatio_first_hit {q N τ : ℕ} (hq : 0 < q) (hfirst : FirstHit q N τ) :
    orbitRatio τ q = (N : ℝ) * firstHitWeight N q / q := by
  have h := first_hit_weight hq hfirst
  rw [one_div_pow, mul_one_div] at h
  exact h

/-- Green's per-endpoint geometric factor using the actual first-hit weight. -/
theorem first_hit_weight_loop_rpow_hasSum {q N τ r : ℕ} (hq : 0 < q) (hN : 0 < N)
    (hfirst : FirstHit q N τ) (hperiod : LeastPositivePeriod N r)
    {s : ℝ} (hs : 0 < s) :
    HasSum (fun j : ℕ => (orbitRatio (τ + j * r) q) ^ s)
      (((N : ℝ) * firstHitWeight N q / q) ^ s / (1 - (orbitRatio r N) ^ s)) := by
  rw [← orbitRatio_first_hit hq hfirst]
  exact first_hit_loop_rpow_hasSum hN hfirst hperiod hs

/-- Contribution at a specified shortcut time to the all-hit Green series. -/
noncomputable def allHitTerm (s : ℝ) (q N n : ℕ) : ℝ :=
  if iterate n q = N then (orbitRatio n q) ^ s else 0

/-- Reindex the actual all-hit series by its unique period-loop index. -/
theorem all_hit_rpow_hasSum {q N τ r : ℕ} (hN : 0 < N)
    (hfirst : FirstHit q N τ) (hperiod : LeastPositivePeriod N r)
    {s : ℝ} (hs : 0 < s) :
    HasSum (allHitTerm s q N)
      ((orbitRatio τ q) ^ s / (1 - (orbitRatio r N) ^ s)) := by
  let g : ℕ → ℕ := fun j => τ + j * r
  have hg : Function.Injective g := by
    intro i j he
    dsimp only [g] at he
    exact Nat.eq_of_mul_eq_mul_right hperiod.positive (Nat.add_left_cancel he)
  have hz (n : ℕ) (hn : n ∉ Set.range g) : allHitTerm s q N n = 0 := by
    unfold allHitTerm
    apply if_neg
    intro hh
    obtain ⟨j, hj⟩ := (hitting_time_iff_first_plus_periods hfirst hperiod).mp hh
    exact hn ⟨j, hj.symm⟩
  apply (hg.hasSum_iff hz).mp
  have he : allHitTerm s q N ∘ g = (fun j : ℕ => (orbitRatio (τ + j * r) q) ^ s) := by
    funext j
    dsimp only [Function.comp_def, g]
    have hh : iterate (τ + j * r) q = N :=
      (hitting_time_iff_first_plus_periods hfirst hperiod).mpr ⟨j, rfl⟩
    simp only [allHitTerm, if_pos hh]
  rw [he]
  exact first_hit_loop_rpow_hasSum hN hfirst hperiod hs

/-- Exact Green contribution of one endpoint of a positive periodic target. -/
theorem all_hit_weight_rpow_hasSum {q N τ r : ℕ} (hq : 0 < q) (hN : 0 < N)
    (hfirst : FirstHit q N τ) (hperiod : LeastPositivePeriod N r)
    {s : ℝ} (hs : 0 < s) :
    HasSum (allHitTerm s q N)
      (((N : ℝ) * firstHitWeight N q / q) ^ s / (1 - (orbitRatio r N) ^ s)) := by
  rw [← orbitRatio_first_hit hq hfirst]
  exact all_hit_rpow_hasSum hN hfirst hperiod hs

/-- At a nonperiodic target, the all-hit series consists of its first-hit term. -/
theorem all_hit_rpow_hasSum_of_no_return {q N τ : ℕ} (hfirst : FirstHit q N τ)
    (hno : ∀ d : ℕ, 0 < d → iterate d N ≠ N) (s : ℝ) :
    HasSum (allHitTerm s q N) ((orbitRatio τ q) ^ s) := by
  have hh : allHitTerm s q N τ = (orbitRatio τ q) ^ s := by
    simp only [allHitTerm, if_pos hfirst.1]
  rw [← hh]
  apply hasSum_single τ
  intro n hn
  unfold allHitTerm
  exact if_neg (fun h => hn ((hitting_time_iff_eq_first_of_no_return hfirst hno).mp h))

/-- An endpoint outside the target's basin contributes zero at every time. -/
theorem all_hit_rpow_hasSum_of_no_hit {q N : ℕ}
    (hno : ¬ ∃ n, iterate n q = N) (s : ℝ) :
    HasSum (allHitTerm s q N) 0 := by
  have he : allHitTerm s q N = fun _ => (0 : ℝ) := by
    funext n
    exact if_neg (fun h => hno ⟨n, h⟩)
  rw [he]
  exact hasSum_zero

end CollatzCylinderPacking.Arithmetic
