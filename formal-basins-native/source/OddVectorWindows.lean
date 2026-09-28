import ClosedOddWindowPassage

set_option autoImplicit false
open Filter Topology
open scoped BigOperators

namespace CollatzCanonical.BanachWindow
open CollatzCanonical.DirichletAbelian

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def oddVectorTerm (F : ℕ → V) (n : ℕ) : V :=
  if (n + 1) % 2 = 1 then (1 / (n + 1 : ℕ) : ℝ) • F (n + 1) else 0

noncomputable def oddVectorCumulative (F : ℕ → V) (t : ℝ) : V :=
  ∑ n ∈ Finset.range ⌊Real.exp t⌋₊, oddVectorTerm F n

noncomputable def oddVectorWindowNumerator (F : ℕ → V) (s t : ℝ) : V :=
  oddVectorCumulative F t - oddVectorCumulative F s

noncomputable def oddVectorWindowExpectation (F : ℕ → V) (s t : ℝ) : V :=
  (oddWindowMass s t)⁻¹ • oddVectorWindowNumerator F s t

noncomputable def closedOddVectorNumerator (F : ℕ → V) (s t : ℝ) : V :=
  ∑ q ∈ closedOddWindowValues s t, (1 / (q : ℝ)) • F q

noncomputable def closedOddVectorExpectation (F : ℕ → V) (s t : ℝ) : V :=
  (closedOddWindowMass s t)⁻¹ • closedOddVectorNumerator F s t

theorem norm_reciprocal_smul_le {F : ℕ → V} (hF : ∀ q, ‖F q‖ ≤ 1) (q : ℕ) :
    ‖(1 / (q : ℝ)) • F q‖ ≤ 1 / (q : ℝ) := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (1 : ℝ) / q)]
  exact mul_le_of_le_one_right (by positivity) (hF q)

theorem oddVectorTerm_norm_le {F : ℕ → V} (hF : ∀ q, ‖F q‖ ≤ 1) (n : ℕ) :
    ‖oddVectorTerm F n‖ ≤ (if (n + 1) % 2 = 1 then (1 : ℝ) else 0) / (n + 1 : ℕ) := by
  unfold oddVectorTerm
  split_ifs
  · exact norm_reciprocal_smul_le hF _
  · simp

theorem oddVectorCumulative_norm_le_mass {F : ℕ → V} (hF : ∀ q, ‖F q‖ ≤ 1) (t : ℝ) :
    ‖oddVectorCumulative F t‖ ≤ oddLogarithmicCumulative (fun _ => 1) t := by
  calc
    ‖oddVectorCumulative F t‖ ≤ ∑ n ∈ Finset.range ⌊Real.exp t⌋₊, ‖oddVectorTerm F n‖ :=
      norm_sum_le _ _
    _ ≤ _ := Finset.sum_le_sum (fun n _ => oddVectorTerm_norm_le hF n)

theorem oddVectorCumulative_growth {F : ℕ → V} (hF : ∀ q, ‖F q‖ ≤ 1)
    {t : ℝ} (ht : 0 ≤ t) : ‖oddVectorCumulative F t‖ ≤ t + 1 := by
  have hb := logarithmicCumulative_linear_bound
    (w := fun n => if n % 2 = 1 then (1 : ℝ) else 0)
    (fun n => by dsimp only; split_ifs <;> norm_num)
    (fun n => by dsimp only; split_ifs <;> norm_num) ht
  exact (oddVectorCumulative_norm_le_mass hF t).trans ((le_abs_self _).trans hb)

theorem oddVectorWindowNumerator_eq_sum (F : ℕ → V) {s t : ℝ} (hst : s ≤ t) :
    oddVectorWindowNumerator F s t =
      ∑ n ∈ Finset.Ico ⌊Real.exp s⌋₊ ⌊Real.exp t⌋₊, oddVectorTerm F n := by
  unfold oddVectorWindowNumerator oddVectorCumulative
  rw [Finset.sum_Ico_eq_sub _ (Nat.floor_mono (Real.exp_le_exp.mpr hst))]

theorem oddVectorWindowNumerator_norm_le_mass {F : ℕ → V}
    (hF : ∀ q, ‖F q‖ ≤ 1) {s t : ℝ} (hst : s ≤ t) :
    ‖oddVectorWindowNumerator F s t‖ ≤ oddWindowMass s t := by
  rw [oddVectorWindowNumerator_eq_sum F hst]
  calc
    ‖∑ n ∈ Finset.Ico ⌊Real.exp s⌋₊ ⌊Real.exp t⌋₊, oddVectorTerm F n‖ ≤
        ∑ n ∈ Finset.Ico ⌊Real.exp s⌋₊ ⌊Real.exp t⌋₊, ‖oddVectorTerm F n‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.Ico ⌊Real.exp s⌋₊ ⌊Real.exp t⌋₊,
        (if (n + 1) % 2 = 1 then (1 : ℝ) else 0) / (n + 1 : ℕ) :=
      Finset.sum_le_sum (fun n _ => oddVectorTerm_norm_le hF n)
    _ = _ := by
      rw [Finset.sum_Ico_eq_sub _ (Nat.floor_mono (Real.exp_le_exp.mpr hst))]
      rfl

theorem oddVectorCumulative_increment {F : ℕ → V} (hF : ∀ q, ‖F q‖ ≤ 1)
    {t z : ℝ} (ht : 0 ≤ t) (hz : 0 ≤ z) :
    ‖oddVectorCumulative F (t + z) - oddVectorCumulative F t‖ ≤ z + 1 := by
  have hb := logarithmicCumulative_increment_bound
    (w := fun n => if n % 2 = 1 then (1 : ℝ) else 0)
    (fun n => by dsimp only; split_ifs <;> norm_num)
    (fun n => by dsimp only; split_ifs <;> norm_num) ht hz
  exact (oddVectorWindowNumerator_norm_le_mass hF (by linarith : t ≤ t + z)).trans
    ((le_abs_self _).trans hb)

theorem closedOddVectorNumerator_eq_index_sum (F : ℕ → V) {s t : ℝ} (hs : 0 ≤ s) :
    closedOddVectorNumerator F s t =
      ∑ n ∈ Finset.Ico (⌈Real.exp s⌉₊ - 1) ⌊Real.exp t⌋₊, oddVectorTerm F n := by
  have hf : 1 ≤ ⌊Real.exp s⌋₊ :=
    (Nat.one_le_floor_iff _).mpr (Real.one_le_exp_iff.mpr hs)
  have hc : 1 ≤ ⌈Real.exp s⌉₊ := hf.trans (Nat.floor_le_ceil _)
  unfold closedOddVectorNumerator closedOddWindowValues oddVectorTerm
  rw [Finset.sum_Ico_add' (fun q : ℕ => if q % 2 = 1 then (1 / (q : ℝ)) • F q else 0)
    (⌈Real.exp s⌉₊ - 1) ⌊Real.exp t⌋₊ 1,
    Nat.sub_add_cancel hc, Finset.Ico_add_one_right_eq_Icc, Finset.sum_filter]

theorem closedOddVectorNumerator_norm_le_mass {F : ℕ → V}
    (hF : ∀ q, ‖F q‖ ≤ 1) {s t : ℝ} (hs : 0 ≤ s) :
    ‖closedOddVectorNumerator F s t‖ ≤ closedOddWindowMass s t := by
  rw [closedOddVectorNumerator_eq_index_sum F hs]
  calc
    _ ≤ ∑ n ∈ Finset.Ico (⌈Real.exp s⌉₊ - 1) ⌊Real.exp t⌋₊, ‖oddVectorTerm F n‖ :=
      norm_sum_le _ _
    _ ≤ _ := Finset.sum_le_sum (fun n _ => oddVectorTerm_norm_le hF n)

theorem closedOddVectorExpectation_norm_le_one {F : ℕ → V}
    (hF : ∀ q, ‖F q‖ ≤ 1) {s t : ℝ} (hs : 0 ≤ s)
    (hmass : 0 < closedOddWindowMass s t) : ‖closedOddVectorExpectation F s t‖ ≤ 1 := by
  unfold closedOddVectorExpectation
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (inv_nonneg.mpr hmass.le)]
  calc
    _ ≤ (closedOddWindowMass s t)⁻¹ * closedOddWindowMass s t :=
      mul_le_mul_of_nonneg_left (closedOddVectorNumerator_norm_le_mass hF hs)
        (inv_nonneg.mpr hmass.le)
    _ = 1 := inv_mul_cancel₀ hmass.ne'

end CollatzCanonical.BanachWindow

#print axioms CollatzCanonical.BanachWindow.oddVectorCumulative_growth
#print axioms CollatzCanonical.BanachWindow.oddVectorCumulative_increment
#print axioms CollatzCanonical.BanachWindow.closedOddVectorNumerator_eq_index_sum
#print axioms CollatzCanonical.BanachWindow.closedOddVectorExpectation_norm_le_one
