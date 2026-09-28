import ActualCycleWeights

set_option autoImplicit false

namespace CollatzCylinderPacking.Arithmetic

/-- The arithmetic odd predecessor, when the residue condition permits it. -/
def oddPredecessor (N : ℕ) : ℕ := (2 * N - 1) / 3

theorem oddPredecessor_spec {N : ℕ} (hres : N % 3 = 2) :
    0 < oddPredecessor N ∧ oddPredecessor N % 2 = 1 ∧ step (oddPredecessor N) = N := by
  have he : 3 * oddPredecessor N + 1 = 2 * N := by unfold oddPredecessor; omega
  have ho : oddPredecessor N % 2 = 1 := by omega
  have hs := step_odd ho
  exact ⟨by omega, ho, by omega⟩

/-- Exact positive-target predecessor classification for the actual shortcut map. -/
theorem step_preimage_iff {q N : ℕ} :
    step q = N ↔ q = 2 * N ∨ N % 3 = 2 ∧ q = oddPredecessor N := by
  constructor
  · intro hh
    by_cases he : q % 2 = 0
    · have hs := step_even he
      rw [hh] at hs
      exact Or.inl hs.symm
    · have ho : q % 2 = 1 := by omega
      have hs := step_odd ho
      rw [hh] at hs
      refine Or.inr ⟨by omega, ?_⟩
      unfold oddPredecessor
      omega
  · rintro (rfl | ⟨hres, rfl⟩)
    · exact step_two_mul N
    · exact (oddPredecessor_spec hres).2.2

/-- Uniform finite support of a shortcut inverse fiber. -/
theorem start_le_scaled_endpoint (A q : ℕ) : q ≤ 2 ^ A * iterate A q := by
  have hb := (scaled_bounds A q).1
  have hp : 1 ≤ (3 : ℕ) ^ oddCount A q := Nat.one_le_pow _ _ (by decide)
  have hm := Nat.mul_le_mul_right q hp
  omega

noncomputable def hittingFiber (A N : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ A * N + 1)).filter (fun q => 0 < q ∧ iterate A q = N)

theorem mem_hittingFiber (A N q : ℕ) :
    q ∈ hittingFiber A N ↔ 0 < q ∧ iterate A q = N := by
  simp only [hittingFiber, Finset.mem_filter, Finset.mem_range]
  constructor
  · exact And.right
  · intro hh
    have hb := start_le_scaled_endpoint A q
    rw [hh.2] at hb
    exact ⟨by omega, hh⟩

theorem hittingFiber_zero {N : ℕ} (hN : 0 < N) : hittingFiber 0 N = {N} := by
  ext q
  simp only [mem_hittingFiber, iterate, Finset.mem_singleton]
  exact ⟨And.right, fun h => ⟨by omega, h⟩⟩

theorem hittingFiber_succ (A N : ℕ) :
    hittingFiber (A + 1) N = hittingFiber A (2 * N) ∪
      if N % 3 = 2 then hittingFiber A (oddPredecessor N) else ∅ := by
  ext q
  rw [mem_hittingFiber, Finset.mem_union, mem_hittingFiber]
  by_cases hres : N % 3 = 2
  · rw [if_pos hres, mem_hittingFiber]
    simp only [iterate, step_preimage_iff, hres, true_and]
    tauto
  · rw [if_neg hres]
    simp only [Finset.notMem_empty, or_false, iterate, step_preimage_iff, hres, false_and,
      or_false]

theorem hittingFiber_branches_disjoint (A N : ℕ) (hres : N % 3 = 2) :
    Disjoint (hittingFiber A (2 * N)) (hittingFiber A (oddPredecessor N)) := by
  apply Finset.disjoint_left.mpr
  intro q he ho
  have he' := ((mem_hittingFiber A (2 * N) q).mp he).2
  have ho' := ((mem_hittingFiber A (oddPredecessor N) q).mp ho).2
  have hp := (oddPredecessor_spec hres).2.1
  omega

/-- The paper's actual inverse operator, including its residue guard. -/
noncomputable def inverseOperator (s : ℝ) (f : ℕ → ℝ) (N : ℕ) : ℝ :=
  (2 : ℝ) ^ (-s) * f (2 * N) +
    (3 / 2 : ℝ) ^ s * (if N % 3 = 2 then f (oddPredecessor N) else 0)

/-- Iteration of the actual inverse operator on the constant function one. -/
noncomputable def inverseIterate (s : ℝ) : ℕ → ℕ → ℝ
  | 0, _ => 1
  | A + 1, N => inverseOperator s (inverseIterate s A) N

theorem orbitRatio_one_even (N : ℕ) : orbitRatio 1 (2 * N) = (1 / 2 : ℝ) := by
  simp [orbitRatio, oddCount, iterate]

theorem orbitRatio_one_odd {m : ℕ} (hm : m % 2 = 1) :
    orbitRatio 1 m = (3 / 2 : ℝ) := by
  simp [orbitRatio, oddCount, iterate, hm]

theorem half_rpow (s : ℝ) : (1 / 2 : ℝ) ^ s = (2 : ℝ) ^ (-s) := by
  rw [Real.rpow_neg_eq_inv_rpow, one_div]

theorem orbitRatio_succ_even_rpow {A q N : ℕ} (hhit : iterate A q = 2 * N) (s : ℝ) :
    (orbitRatio (A + 1) q) ^ s = (2 : ℝ) ^ (-s) * (orbitRatio A q) ^ s := by
  rw [orbitRatio_add, hhit, orbitRatio_one_even,
    Real.mul_rpow (orbitRatio_pos A q).le (by norm_num), half_rpow, mul_comm]

theorem orbitRatio_succ_odd_rpow {A q N : ℕ} (hres : N % 3 = 2)
    (hhit : iterate A q = oddPredecessor N) (s : ℝ) :
    (orbitRatio (A + 1) q) ^ s = (3 / 2 : ℝ) ^ s * (orbitRatio A q) ^ s := by
  rw [orbitRatio_add, hhit, orbitRatio_one_odd (oddPredecessor_spec hres).2.1,
    Real.mul_rpow (orbitRatio_pos A q).le (by norm_num), mul_comm]

/-- Fixed-depth inverse operator expansion over the actual finite positive
integer fiber. No word expansion or predecessor formula is assumed. -/
theorem inverseIterate_fiber_sum (s : ℝ) (A : ℕ) {N : ℕ} (hN : 0 < N) :
    inverseIterate s A N = ∑ q ∈ hittingFiber A N, (orbitRatio A q) ^ s := by
  induction A generalizing N with
  | zero => simp [inverseIterate, hittingFiber_zero hN, orbitRatio, oddCount]
  | succ A ih =>
    rw [inverseIterate, inverseOperator, ih (by omega : 0 < 2 * N), hittingFiber_succ]
    by_cases hres : N % 3 = 2
    · rw [if_pos hres, if_pos hres, ih (oddPredecessor_spec hres).1,
        Finset.sum_union (hittingFiber_branches_disjoint A N hres), Finset.mul_sum, Finset.mul_sum]
      congr 1
      · apply Finset.sum_congr rfl
        intro q hq
        exact (orbitRatio_succ_even_rpow ((mem_hittingFiber A (2 * N) q).mp hq).2 s).symm
      · apply Finset.sum_congr rfl
        intro q hq
        exact (orbitRatio_succ_odd_rpow hres ((mem_hittingFiber A (oddPredecessor N) q).mp hq).2 s).symm
    · rw [if_neg hres, if_neg hres]
      simp only [mul_zero, add_zero, Finset.union_empty, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro q hq
      exact (orbitRatio_succ_even_rpow ((mem_hittingFiber A (2 * N) q).mp hq).2 s).symm

theorem iterate_zero (A : ℕ) : iterate A 0 = 0 := by
  induction A with
  | zero => rfl
  | succ A ih => simp [iterate, ih, step]

/-- Each fixed shortcut depth has a genuine finite-support sum over endpoints. -/
theorem allHitTerm_fixed_depth_hasSum (s : ℝ) (A : ℕ) {N : ℕ} (hN : 0 < N) :
    HasSum (fun q : ℕ => allHitTerm s q N A) (inverseIterate s A N) := by
  classical
  rw [inverseIterate_fiber_sum s A hN]
  have hzero (q : ℕ) (hq : q ∉ hittingFiber A N) : allHitTerm s q N A = 0 := by
    unfold allHitTerm
    apply if_neg
    intro hh
    apply hq
    rw [mem_hittingFiber]
    refine ⟨?_, hh⟩
    by_contra hp
    have hq0 : q = 0 := by omega
    rw [hq0, iterate_zero] at hh
    omega
  have hf : HasSum (fun q : ℕ => allHitTerm s q N A)
      (∑ q ∈ hittingFiber A N, allHitTerm s q N A) := hasSum_sum_of_ne_finset_zero hzero
  convert hf using 1
  apply Finset.sum_congr rfl
  intro q hq
  exact (if_pos ((mem_hittingFiber A N q).mp hq).2).symm

theorem inverseIterate_tsum (s : ℝ) (A : ℕ) {N : ℕ} (hN : 0 < N) :
    inverseIterate s A N = ∑' q : ℕ, allHitTerm s q N A :=
  (allHitTerm_fixed_depth_hasSum s A hN).tsum_eq.symm

end CollatzCylinderPacking.Arithmetic
