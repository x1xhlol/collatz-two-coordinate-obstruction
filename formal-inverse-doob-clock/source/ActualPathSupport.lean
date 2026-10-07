import NonperiodicFiniteCylinder

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Preorder Filter

namespace CollatzCylinderPacking.Arithmetic.InverseDoob

theorem transitionPMF_support_ae (n : ℕ) :
    ∀ᵐ q ∂(transitionPMF n).toMeasure, q ∈ (transitionPMF n).support := by
  apply (mem_ae_iff_prob_eq_one (transitionPMF n).support_countable.measurableSet).mpr
  exact ((transitionPMF n).toMeasure_apply_eq_one_iff
    (transitionPMF n).support_countable.measurableSet).mpr (Set.Subset.refl _)

theorem pathLaw_step_support_ae (n k : ℕ) :
    ∀ᵐ x ∂pathLaw n, x (k + 1) ∈ (transitionPMF (x k)).support := by
  let p : ((Π _ : Finset.Iic k, ℕ) × ℕ) → Prop :=
    fun z => z.2 ∈ (transitionPMF (z.1 ⟨k, Finset.mem_Iic.mpr le_rfl⟩)).support
  have hp : MeasurableSet {z | p z} := (Set.to_countable _).measurableSet
  have hcond : ∀ᵐ z ∂((pathLaw n).map (frestrictLe (π := fun _ : ℕ => ℕ) k)),
      ∀ᵐ q ∂historyKernel k z, p (z, q) := by
    exact Eventually.of_forall (fun z => transitionPMF_support_ae _)
  have hj := Measure.ae_compProd_of_ae_ae hp hcond
  rw [pathLaw_history_successor n k] at hj
  exact ae_of_ae_map (by fun_prop) hj

theorem pathLaw_all_step_support_ae (n : ℕ) :
    ∀ᵐ x ∂pathLaw n, ∀ k, x (k + 1) ∈ (transitionPMF (x k)).support :=
  ae_all_iff.mpr (pathLaw_step_support_ae n)

theorem pathLaw_initial_ae (n : ℕ) : ∀ᵐ x ∂pathLaw n, x 0 = n := by
  have h : ∀ᵐ x ∂pathLaw n, x ∈ prefixSet 0 (fun _ => n) :=
    (mem_ae_iff_prob_eq_one (measurableSet_prefixSet 0 (fun _ => n))).mpr
    (pathLaw_prefix_zero (fun _ => n) rfl)
  exact h.mono (fun x hx => hx 0 le_rfl)

theorem pathLaw_actual_steps_ae {n : ℕ} (hn : 0 < n) (hu : n % 3 ≠ 0) :
    ∀ᵐ x ∂pathLaw n,
      x 0 = n ∧ (∀ k, 0 < x k ∧ x k % 3 ≠ 0) ∧
        ∀ k, ∃ a, (2 ^ a * x k) % 3 = 2 ∧ x (k + 1) = inverseEndpoint (x k) a := by
  filter_upwards [pathLaw_initial_ae n, pathLaw_all_step_support_ae n] with x hx hs
  have hunit (k : ℕ) : 0 < x k ∧ x k % 3 ≠ 0 := by
    induction k with
    | zero => simpa only [hx] using And.intro hn hu
    | succ k ih =>
      have h := transitionPMF_support ih.1 ih.2 (hs k)
      exact ⟨h.1, h.2.2.1⟩
  refine ⟨hx, hunit, ?_⟩
  intro k
  exact (transitionPMF_support (hunit k).1 (hunit k).2 (hs k)).2.2.2

theorem pathLaw_validPrefix_ae {n : ℕ} (hn : 0 < n) (hu : n % 3 ≠ 0) (k : ℕ) :
    ∀ᵐ x ∂pathLaw n, ValidPrefix n k x := by
  filter_upwards [pathLaw_actual_steps_ae hn hu] with x hx
  exact ⟨hx.1, fun i _ => hx.2.1 i, fun i _ => hx.2.2 i⟩

end CollatzCylinderPacking.Arithmetic.InverseDoob
