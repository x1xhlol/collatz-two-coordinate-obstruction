import InverseBranchCylinder

set_option autoImplicit false

open MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

namespace CollatzCylinderPacking.Arithmetic.InverseDoob

theorem pathLaw_eq_traj (n : ℕ) :
    pathLaw n = Kernel.traj (X := fun _ : ℕ => ℕ) historyKernel 0 (fun _ => n) := by
  rw [pathLaw, Kernel.trajMeasure, Measure.map_dirac]
  exact Measure.dirac_bind (Kernel.traj (X := fun _ : ℕ => ℕ) historyKernel 0).measurable _

theorem pathLaw_finite_projection (n k : ℕ) :
    (pathLaw n).map (frestrictLe (π := fun _ : ℕ => ℕ) k) = Kernel.partialTraj (X := fun _ : ℕ => ℕ) historyKernel 0 k (fun _ => n) := by
  rw [pathLaw_eq_traj]
  exact Kernel.traj_map_frestrictLe_apply 0 k _

def prefixSet (k : ℕ) (x : ℕ → ℕ) : Set (ℕ → ℕ) :=
  {z | ∀ i ≤ k, z i = x i}

theorem prefixSet_eq_preimage (k : ℕ) (x : ℕ → ℕ) :
    prefixSet k x = (frestrictLe (π := fun _ : ℕ => ℕ) k) ⁻¹' {frestrictLe (π := fun _ : ℕ => ℕ) k x} := by
  ext z
  change (∀ i ≤ k, z i = x i) ↔ frestrictLe (π := fun _ : ℕ => ℕ) k z = frestrictLe (π := fun _ : ℕ => ℕ) k x
  constructor
  · intro h
    funext i
    exact h i (Finset.mem_Iic.mp i.2)
  · intro h i hi
    exact congrFun h ⟨i, Finset.mem_Iic.mpr hi⟩

theorem measurableSet_prefixSet (k : ℕ) (x : ℕ → ℕ) : MeasurableSet (prefixSet k x) := by
  rw [prefixSet_eq_preimage]
  exact (measurableSet_singleton _).preimage (measurable_frestrictLe (X := fun _ : ℕ => ℕ) k)

theorem pathLaw_prefix_zero {n : ℕ} (x : ℕ → ℕ) (hx : x 0 = n) :
    pathLaw n (prefixSet 0 x) = 1 := by
  rw [prefixSet_eq_preimage, ← Measure.map_apply (measurable_frestrictLe (X := fun _ : ℕ => ℕ) 0)
    (measurableSet_singleton _), pathLaw_finite_projection, Kernel.partialTraj_self]
  change Measure.dirac (fun _ : Finset.Iic 0 => n) {frestrictLe (π := fun _ : ℕ => ℕ) 0 x} = 1
  have he : frestrictLe (π := fun _ : ℕ => ℕ) 0 x = fun _ : Finset.Iic 0 => n := by
    funext i
    have hi : (i : ℕ) = 0 := by have := Finset.mem_Iic.mp i.2; omega
    simpa only [frestrictLe_apply, hi] using hx
  rw [he]
  simp

theorem pathLaw_prefix_succ (n k : ℕ) (x : ℕ → ℕ) :
    pathLaw n (prefixSet (k + 1) x) =
      pathLaw n (prefixSet k x) * transitionPMF (x k) (x (k + 1)) := by
  have h := congrArg (fun μ : Measure ((Π _ : Finset.Iic k, ℕ) × ℕ) =>
    μ ({frestrictLe (π := fun _ : ℕ => ℕ) k x} ×ˢ {x (k + 1)})) (pathLaw_history_successor n k)
  dsimp only at h
  rw [Measure.compProd_apply_prod (measurableSet_singleton _) (measurableSet_singleton _),
    lintegral_singleton, Measure.map_apply (by fun_prop)
      ((measurableSet_singleton _).prod (measurableSet_singleton _))] at h
  have he : (fun z : ℕ → ℕ => (frestrictLe (π := fun _ : ℕ => ℕ) k z, z (k + 1))) ⁻¹'
      ({frestrictLe (π := fun _ : ℕ => ℕ) k x} ×ˢ {x (k + 1)}) = prefixSet (k + 1) x := by
    ext z
    change (frestrictLe (π := fun _ : ℕ => ℕ) k z = frestrictLe (π := fun _ : ℕ => ℕ) k x ∧ z (k + 1) = x (k + 1)) ↔
      ∀ i ≤ k + 1, z i = x i
    rw [← show (∀ i ≤ k, z i = x i) ↔ frestrictLe (π := fun _ : ℕ => ℕ) k z = frestrictLe (π := fun _ : ℕ => ℕ) k x by
      exact Set.ext_iff.mp (prefixSet_eq_preimage k x) z]
    constructor
    · rintro ⟨hprev, hlast⟩ i hi
      obtain hle | rfl := Nat.le_add_one_iff.mp hi
      · exact hprev i hle
      · exact hlast
    · intro hall
      exact ⟨fun i hi => hall i (by omega), hall _ le_rfl⟩
  rw [he] at h
  rw [Measure.map_apply (measurable_frestrictLe (X := fun _ : ℕ => ℕ) k) (measurableSet_singleton _),
    ← prefixSet_eq_preimage] at h
  have hk : historyKernel k (frestrictLe (π := fun _ : ℕ => ℕ) k x) {x (k + 1)} =
      transitionPMF (x k) (x (k + 1)) := by
    change (transitionPMF (x k)).toMeasure {x (k + 1)} = _
    exact PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _)
  rw [hk] at h
  exact h.symm.trans (mul_comm _ _)

theorem pathLaw_prefix_product {n : ℕ} (k : ℕ) (x : ℕ → ℕ) (hx : x 0 = n) :
    pathLaw n (prefixSet k x) =
      ∏ i ∈ Finset.range k, transitionPMF (x i) (x (i + 1)) := by
  induction k with
  | zero => simpa using pathLaw_prefix_zero x hx
  | succ k ih => rw [pathLaw_prefix_succ, ih, Finset.prod_range_succ]

end CollatzCylinderPacking.Arithmetic.InverseDoob
