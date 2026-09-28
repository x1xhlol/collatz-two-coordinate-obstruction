import ActualGreenSeries

set_option autoImplicit false
open Classical

namespace CollatzCylinderPacking.Arithmetic

noncomputable def oddGreenHitTerm (s : ℝ) (N : ℕ) (p : ℕ × ℕ) : ℝ :=
  if p.1 % 2 = 1 then allHitTerm s p.1 N p.2 else 0

noncomputable def evenGreenHitTerm (s : ℝ) (N : ℕ) (p : ℕ × ℕ) : ℝ :=
  if p.1 % 2 = 0 then allHitTerm s p.1 N p.2 else 0

theorem allHitTerm_joint_summable {s : ℝ} (hs : 1 < s) {N : ℕ} (hN : 0 < N) :
    Summable (fun p : ℕ × ℕ => allHitTerm s p.1 N p.2) := by
  have hj : Summable (fun p : ℕ × ℕ => allHitTerm s p.2 N p.1) := by
    apply (summable_prod_of_nonneg (fun p => allHitTerm_nonneg s p.2 N p.1)).mpr
    refine ⟨fun A => (allHitTerm_fixed_depth_hasSum s A hN).summable, ?_⟩
    simpa only [← inverseIterate_tsum s _ hN] using actual_green_summable hs hN
  exact hj.prod_symm

theorem allHitTerm_joint_tsum {s : ℝ} (hs : 1 < s) {N : ℕ} (hN : 0 < N) :
    (∑' p : ℕ × ℕ, allHitTerm s p.1 N p.2) = ∑' A : ℕ, inverseIterate s A N := by
  rw [(allHitTerm_joint_summable hs hN).tsum_prod,
    ← Summable.tsum_comm (f := fun q A : ℕ => allHitTerm s q N A)
      (allHitTerm_joint_summable hs hN)]
  exact tsum_congr (fun A => (inverseIterate_tsum s A hN).symm)

theorem oddGreenHitTerm_nonneg (s : ℝ) (N : ℕ) (p : ℕ × ℕ) :
    0 ≤ oddGreenHitTerm s N p := by
  unfold oddGreenHitTerm
  split_ifs
  · exact allHitTerm_nonneg _ _ _ _
  · exact le_rfl

theorem evenGreenHitTerm_nonneg (s : ℝ) (N : ℕ) (p : ℕ × ℕ) :
    0 ≤ evenGreenHitTerm s N p := by
  unfold evenGreenHitTerm
  split_ifs
  · exact allHitTerm_nonneg _ _ _ _
  · exact le_rfl

theorem oddGreenHitTerm_summable {s : ℝ} (hs : 1 < s) {N : ℕ} (hN : 0 < N) :
    Summable (oddGreenHitTerm s N) := by
  apply Summable.of_nonneg_of_le (oddGreenHitTerm_nonneg s N) _ (allHitTerm_joint_summable hs hN)
  intro p
  unfold oddGreenHitTerm
  split_ifs
  · exact le_rfl
  · exact allHitTerm_nonneg _ _ _ _

theorem evenGreenHitTerm_summable {s : ℝ} (hs : 1 < s) {N : ℕ} (hN : 0 < N) :
    Summable (evenGreenHitTerm s N) := by
  apply Summable.of_nonneg_of_le (evenGreenHitTerm_nonneg s N) _ (allHitTerm_joint_summable hs hN)
  intro p
  unfold evenGreenHitTerm
  split_ifs
  · exact le_rfl
  · exact allHitTerm_nonneg _ _ _ _

theorem iterate_initial_even (A q : ℕ) : iterate (A + 1) (2 * q) = iterate A q := by
  rw [show A + 1 = 1 + A by omega, iterate_add]
  simp only [iterate, step_two_mul]

theorem orbitRatio_initial_even (A q : ℕ) :
    orbitRatio (A + 1) (2 * q) = (1 / 2 : ℝ) * orbitRatio A q := by
  rw [show A + 1 = 1 + A by omega, orbitRatio_add, orbitRatio_one_even]
  simp only [iterate, step_two_mul]

theorem allHitTerm_initial_even (s : ℝ) (N A q : ℕ) :
    allHitTerm s (2 * q) N (A + 1) = (2 : ℝ) ^ (-s) * allHitTerm s q N A := by
  unfold allHitTerm
  rw [iterate_initial_even]
  split_ifs
  · rw [orbitRatio_initial_even, Real.mul_rpow (by norm_num) (orbitRatio_pos _ _).le, half_rpow]
  · ring

theorem evenGreenHitTerm_succ_hasSum (s : ℝ) {N : ℕ} (hN : 0 < N) (A : ℕ) :
    HasSum (fun q : ℕ => evenGreenHitTerm s N (q, A + 1))
      ((2 : ℝ) ^ (-s) * inverseIterate s A N) := by
  let g : ℕ → ℕ := fun q => 2 * q
  have hg : Function.Injective g := by intro a b h; dsimp only [g] at h; omega
  have hz (q : ℕ) (hq : q ∉ Set.range g) : evenGreenHitTerm s N (q, A + 1) = 0 := by
    have ho : q % 2 ≠ 0 := by intro he; exact hq ⟨q / 2, by dsimp only [g]; omega⟩
    simp only [evenGreenHitTerm, ho, if_false]
  apply (hg.hasSum_iff hz).mp
  have h := (allHitTerm_fixed_depth_hasSum s A hN).mul_left ((2 : ℝ) ^ (-s))
  convert h using 1
  funext q
  simp only [Function.comp_def, g, evenGreenHitTerm, Nat.mul_mod_right, if_true,
    allHitTerm_initial_even]

theorem evenGreenHitTerm_zero_hasSum (s : ℝ) (N : ℕ) :
    HasSum (fun q : ℕ => evenGreenHitTerm s N (q, 0)) (if N % 2 = 0 then (1 : ℝ) else 0) := by
  have hv : evenGreenHitTerm s N (N, 0) = if N % 2 = 0 then (1 : ℝ) else 0 := by
    simp [evenGreenHitTerm, allHitTerm, iterate, orbitRatio, oddCount]
  rw [← hv]
  apply hasSum_single N
  intro q hq
  simp [evenGreenHitTerm, allHitTerm, iterate, hq]

theorem evenGreenHitTerm_tsum {s : ℝ} (hs : 1 < s) {N : ℕ} (hN : 0 < N) :
    (∑' p : ℕ × ℕ, evenGreenHitTerm s N p) =
      (if N % 2 = 0 then (1 : ℝ) else 0) +
        (2 : ℝ) ^ (-s) * ∑' A : ℕ, inverseIterate s A N := by
  rw [(evenGreenHitTerm_summable hs hN).tsum_prod,
    ← Summable.tsum_comm (f := fun q A : ℕ => evenGreenHitTerm s N (q, A))
      (evenGreenHitTerm_summable hs hN)]
  have hrow : Summable (fun A : ℕ => ∑' q : ℕ, evenGreenHitTerm s N (q, A)) :=
    (evenGreenHitTerm_summable hs hN).prod_symm.prod
  rw [hrow.tsum_eq_zero_add, (evenGreenHitTerm_zero_hasSum s N).tsum_eq]
  congr 1
  calc
    (∑' A : ℕ, ∑' q : ℕ, evenGreenHitTerm s N (q, A + 1)) =
        ∑' A : ℕ, (2 : ℝ) ^ (-s) * inverseIterate s A N := by
      exact tsum_congr (fun A => (evenGreenHitTerm_succ_hasSum s hN A).tsum_eq)
    _ = _ := tsum_mul_left

/-- Splitting actual hitting endpoints into odd and even starts gives the
exact geometric factor for removing initial even steps. -/
theorem green_odd_endpoint_normalization {s : ℝ} (hs : 1 < s) {N : ℕ} (hN : 0 < N) :
    (1 - (2 : ℝ) ^ (-s)) * (∑' A : ℕ, inverseIterate s A N) =
      (if N % 2 = 0 then (1 : ℝ) else 0) + ∑' p : ℕ × ℕ, oddGreenHitTerm s N p := by
  have he (p : ℕ × ℕ) : allHitTerm s p.1 N p.2 =
      oddGreenHitTerm s N p + evenGreenHitTerm s N p := by
    unfold oddGreenHitTerm evenGreenHitTerm
    rcases (show p.1 % 2 = 0 ∨ p.1 % 2 = 1 by omega) with h | h <;> simp [h]
  have h := allHitTerm_joint_tsum hs hN
  simp_rw [he] at h
  rw [(oddGreenHitTerm_summable hs hN).tsum_add (evenGreenHitTerm_summable hs hN),
    evenGreenHitTerm_tsum hs hN] at h
  linarith

#print axioms allHitTerm_joint_summable
#print axioms green_odd_endpoint_normalization

end CollatzCylinderPacking.Arithmetic
