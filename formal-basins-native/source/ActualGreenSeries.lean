import ActualInverseOperator
import Mathlib.Analysis.PSeries

set_option autoImplicit false

namespace CollatzCylinderPacking.Arithmetic

/-- The actual weighted basin Dirichlet term; q=0 contributes zero. -/
noncomputable def weightedDirichletTerm (s : ℝ) (N q : ℕ) : ℝ :=
  (firstHitWeight N q) ^ s / (q : ℝ) ^ s

theorem weightedDirichletTerm_nonneg (s : ℝ) (N q : ℕ) :
    0 ≤ weightedDirichletTerm s N q := by
  unfold weightedDirichletTerm
  exact div_nonneg (Real.rpow_nonneg (firstHitWeight_bounds N q).1 _)
    (Real.rpow_nonneg (Nat.cast_nonneg q) _)

theorem weightedDirichletTerm_le (s : ℝ) (hs : 0 ≤ s) (N q : ℕ) :
    weightedDirichletTerm s N q ≤ 1 / (q : ℝ) ^ s := by
  have hw := firstHitWeight_bounds N q
  have hp : (firstHitWeight N q) ^ s ≤ 1 := by
    simpa only [Real.one_rpow] using Real.rpow_le_rpow hw.1 hw.2 hs
  exact div_le_div_of_nonneg_right hp (Real.rpow_nonneg (Nat.cast_nonneg q) _)

/-- Absolute summability follows from the ordinary p-series, since 0≤w_N≤1. -/
theorem weightedDirichlet_summable {s : ℝ} (hs : 1 < s) (N : ℕ) :
    Summable (weightedDirichletTerm s N) := by
  apply Summable.of_nonneg_of_le (weightedDirichletTerm_nonneg s N)
    (weightedDirichletTerm_le s (by linarith) N)
  exact Real.summable_one_div_nat_rpow.mpr hs

theorem firstHit_scalar_rpow (s : ℝ) (N q : ℕ) :
    ((N : ℝ) * firstHitWeight N q / q) ^ s =
      (N : ℝ) ^ s * weightedDirichletTerm s N q := by
  rw [Real.div_rpow (mul_nonneg (Nat.cast_nonneg N) (firstHitWeight_bounds N q).1)
    (Nat.cast_nonneg q), Real.mul_rpow (Nat.cast_nonneg N) (firstHitWeight_bounds N q).1]
  unfold weightedDirichletTerm
  ring

theorem allHitTerm_nonneg (s : ℝ) (q N n : ℕ) : 0 ≤ allHitTerm s q N n := by
  unfold allHitTerm
  split_ifs
  · exact (Real.rpow_pos_of_pos (orbitRatio_pos n q) s).le
  · exact le_rfl

/-- Nonnegative Fubini for the proved actual fixed-depth inverse expansion. -/
theorem inverseIterate_hasSum_of_endpoint_hasSum {s : ℝ} {N : ℕ} (hN : 0 < N)
    {L : ℕ → ℝ} (hL : Summable L)
    (hendpoint : ∀ q : ℕ, HasSum (allHitTerm s q N) (L q)) :
    HasSum (fun A : ℕ => inverseIterate s A N) (∑' q : ℕ, L q) := by
  have hnonneg : 0 ≤ (fun p : ℕ × ℕ => allHitTerm s p.1 N p.2) :=
    fun p => allHitTerm_nonneg s p.1 N p.2
  have hjoint : Summable (fun p : ℕ × ℕ => allHitTerm s p.1 N p.2) := by
    apply (summable_prod_of_nonneg hnonneg).mpr
    refine ⟨fun q => (hendpoint q).summable, ?_⟩
    convert hL using 1
    funext q
    exact (hendpoint q).tsum_eq
  have htime : Summable (fun A : ℕ => ∑' q : ℕ, allHitTerm s q N A) :=
    ((summable_prod_of_nonneg (fun p : ℕ × ℕ => allHitTerm_nonneg s p.2 N p.1)).mp
      hjoint.prod_symm).2
  have he : (fun A : ℕ => ∑' q : ℕ, allHitTerm s q N A) =
      (fun A : ℕ => inverseIterate s A N) := by
    funext A
    exact (inverseIterate_tsum s A hN).symm
  rw [he] at htime
  have hsum : (∑' A : ℕ, inverseIterate s A N) = ∑' q : ℕ, L q := by
    calc
      (∑' A : ℕ, inverseIterate s A N) = ∑' A : ℕ, ∑' q : ℕ, allHitTerm s q N A := by
        apply tsum_congr
        intro A
        exact inverseIterate_tsum s A hN
      _ = ∑' q : ℕ, ∑' A : ℕ, allHitTerm s q N A :=
        Summable.tsum_comm (f := fun q A : ℕ => allHitTerm s q N A) hjoint
      _ = ∑' q : ℕ, L q := tsum_congr (fun q => (hendpoint q).tsum_eq)
  rw [← hsum]
  exact htime.hasSum

theorem positive_of_hit_positive_target {q N : ℕ} (hN : 0 < N)
    (hhit : ∃ A, iterate A q = N) : 0 < q := by
  by_contra h
  have hq : q = 0 := by omega
  obtain ⟨A, hA⟩ := hhit
  rw [hq, iterate_zero] at hA
  omega

theorem endpoint_periodic_hasSum {s : ℝ} (hs : 0 < s) {N r : ℕ} (hN : 0 < N)
    (hperiod : LeastPositivePeriod N r) (q : ℕ) :
    HasSum (allHitTerm s q N)
      (((N : ℝ) ^ s / (1 - (orbitRatio r N) ^ s)) * weightedDirichletTerm s N q) := by
  classical
  by_cases hh : ∃ A, iterate A q = N
  · have hq := positive_of_hit_positive_target hN hh
    have hfirst := firstHit_find hh
    have hsum := all_hit_weight_rpow_hasSum hq hN hfirst hperiod hs
    rw [firstHit_scalar_rpow] at hsum
    convert hsum using 1
    ring
  · have hw : firstHitWeight N q = 0 := by simp only [firstHitWeight, dif_neg hh]
    simp only [weightedDirichletTerm, hw, Real.zero_rpow hs.ne', zero_div, mul_zero]
    exact all_hit_rpow_hasSum_of_no_hit hh s

theorem endpoint_nonperiodic_hasSum {s : ℝ} (hs : 0 < s) {N : ℕ} (hN : 0 < N)
    (hno : ∀ d : ℕ, 0 < d → iterate d N ≠ N) (q : ℕ) :
    HasSum (allHitTerm s q N) ((N : ℝ) ^ s * weightedDirichletTerm s N q) := by
  classical
  by_cases hh : ∃ A, iterate A q = N
  · have hq := positive_of_hit_positive_target hN hh
    have hfirst := firstHit_find hh
    have hsum := all_hit_rpow_hasSum_of_no_return hfirst hno s
    rwa [orbitRatio_first_hit hq hfirst, firstHit_scalar_rpow] at hsum
  · have hw : firstHitWeight N q = 0 := by simp only [firstHitWeight, dif_neg hh]
    simp only [weightedDirichletTerm, hw, Real.zero_rpow hs.ne', zero_div, mul_zero]
    exact all_hit_rpow_hasSum_of_no_hit hh s

/-- Exact finite Green sum for a periodic target, from actual arithmetic data. -/
theorem periodic_green_hasSum {s : ℝ} (hs : 1 < s) {N r : ℕ} (hN : 0 < N)
    (hperiod : LeastPositivePeriod N r) :
    HasSum (fun A : ℕ => inverseIterate s A N)
      (((N : ℝ) ^ s / (1 - (orbitRatio r N) ^ s)) *
        ∑' q : ℕ, weightedDirichletTerm s N q) := by
  have hD := (weightedDirichlet_summable hs N).mul_left
    ((N : ℝ) ^ s / (1 - (orbitRatio r N) ^ s))
  have hsum := inverseIterate_hasSum_of_endpoint_hasSum hN hD
    (endpoint_periodic_hasSum (by linarith) hN hperiod)
  simpa only [tsum_mul_left] using hsum

/-- Exact finite Green sum for a target with no positive return. -/
theorem nonperiodic_green_hasSum {s : ℝ} (hs : 1 < s) {N : ℕ} (hN : 0 < N)
    (hno : ∀ d : ℕ, 0 < d → iterate d N ≠ N) :
    HasSum (fun A : ℕ => inverseIterate s A N)
      ((N : ℝ) ^ s * ∑' q : ℕ, weightedDirichletTerm s N q) := by
  have hD := (weightedDirichlet_summable hs N).mul_left ((N : ℝ) ^ s)
  have hsum := inverseIterate_hasSum_of_endpoint_hasSum hN hD
    (endpoint_nonperiodic_hasSum (by linarith) hN hno)
  simpa only [tsum_mul_left] using hsum

/-- The Green series is summable for every positive target and every s>1. -/
theorem actual_green_summable {s : ℝ} (hs : 1 < s) {N : ℕ} (hN : 0 < N) :
    Summable (fun A : ℕ => inverseIterate s A N) := by
  by_cases hret : ∃ r : ℕ, 0 < r ∧ iterate r N = N
  · obtain ⟨r, hp⟩ := exists_least_positive_period hret
    exact (periodic_green_hasSum hs hN hp).summable
  · apply (nonperiodic_green_hasSum hs hN _).summable
    intro d hd hhit
    exact hret ⟨d, hd, hhit⟩

/-- The actual target's cycle factor, with value one off the periodic set. -/
noncomputable def greenCycleFactor (s : ℝ) (N : ℕ) : ℝ := by
  classical
  exact if hret : ∃ r : ℕ, 0 < r ∧ iterate r N = N then
    (1 - (orbitRatio (Nat.find hret) N) ^ s)⁻¹ else 1

/-- The full exact Green formula and finiteness, with both target cases resolved. -/
theorem actual_green_hasSum {s : ℝ} (hs : 1 < s) {N : ℕ} (hN : 0 < N) :
    HasSum (fun A : ℕ => inverseIterate s A N)
      (greenCycleFactor s N * (N : ℝ) ^ s * ∑' q : ℕ, weightedDirichletTerm s N q) := by
  classical
  by_cases hret : ∃ r : ℕ, 0 < r ∧ iterate r N = N
  · let r := Nat.find hret
    have hp : LeastPositivePeriod N r := by
      refine ⟨(Nat.find_spec hret).1, (Nat.find_spec hret).2, ?_⟩
      intro d hd hhit
      exact Nat.find_min' hret ⟨hd, hhit⟩
    have hsum := periodic_green_hasSum hs hN hp
    simp only [greenCycleFactor, dif_pos hret]
    convert hsum using 1
    dsimp only [r]
    ring
  · have hno : ∀ d : ℕ, 0 < d → iterate d N ≠ N := by
      intro d hd hhit
      exact hret ⟨d, hd, hhit⟩
    simpa only [greenCycleFactor, dif_neg hret, one_mul] using nonperiodic_green_hasSum hs hN hno

theorem actual_green_tsum {s : ℝ} (hs : 1 < s) {N : ℕ} (hN : 0 < N) :
    (∑' A : ℕ, inverseIterate s A N) =
      greenCycleFactor s N * (N : ℝ) ^ s * ∑' q : ℕ, weightedDirichletTerm s N q :=
  (actual_green_hasSum hs hN).tsum_eq

end CollatzCylinderPacking.Arithmetic
