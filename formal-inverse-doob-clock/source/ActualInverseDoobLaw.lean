import ActualOddInverseRow
import Mathlib.Probability.Kernel.IonescuTulcea.Traj

set_option autoImplicit false

open Filter Topology MeasureTheory ProbabilityTheory Preorder
open scoped ENNReal

namespace CollatzCylinderPacking.Arithmetic.InverseDoob

noncomputable def exponentPMF (n : ℕ) (hn : 0 < n) (hp : 0 < potential n) : PMF ℕ :=
  ⟨fun a => ENNReal.ofReal (inverseRowMass n a / potential n), by
    apply ENNReal.summable.hasSum_iff.mpr
    rw [← ENNReal.ofReal_tsum_of_nonneg
      (fun a => div_nonneg (inverseRowMass_nonneg n a) hp.le)
      ((inverseRowMass_hasSum hn).summable.div_const (potential n)),
      ((inverseRowMass_hasSum hn).div_const (potential n)).tsum_eq,
      div_self hp.ne', ENNReal.ofReal_one]⟩

theorem exponentPMF_apply (n : ℕ) (hn : 0 < n) (hp : 0 < potential n) (a : ℕ) :
    exponentPMF n hn hp a = ENNReal.ofReal (inverseRowMass n a / potential n) := rfl

theorem exponentPMF_support {n a : ℕ} (hn : 0 < n) (hp : 0 < potential n)
    (ha : a ∈ (exponentPMF n hn hp).support) :
    (2 ^ a * n) % 3 = 2 ∧ 0 < inverseEndpoint n a ∧
      inverseEndpoint n a % 2 = 1 ∧ inverseEndpoint n a % 3 ≠ 0 := by
  have hmass : 0 < inverseRowMass n a / potential n :=
    ENNReal.ofReal_pos.mp (((exponentPMF n hn hp).apply_pos_iff a).mpr ha)
  have hr : 0 < inverseRowMass n a := (div_pos_iff_of_pos_right hp).mp hmass
  have hguard : (2 ^ a * n) % 3 = 2 := by
    by_contra h
    simp only [inverseRowMass, if_neg h] at hr
    exact lt_irrefl _ hr
  have hspec := oddPredecessor_spec hguard
  have hq : 0 < potential (inverseEndpoint n a) := by
    rw [inverseRowMass, if_pos hguard] at hr
    have ht := (div_pos_iff_of_pos_right (by positivity : 0 < (2 : ℝ) ^ a)).mp hr
    nlinarith
  exact ⟨hguard, hspec.1, hspec.2.1, (actual_trace_positive_iff_unit hspec.1).mp hq⟩

noncomputable def transitionPMF (n : ℕ) : PMF ℕ :=
  if h : 0 < n ∧ n % 3 ≠ 0 then
    (exponentPMF n h.1 (potential_pos_of_unit h.1 h.2)).map (inverseEndpoint n)
  else PMF.pure n

theorem transitionPMF_of_unit {n : ℕ} (hn : 0 < n) (hu : n % 3 ≠ 0) :
    transitionPMF n =
      (exponentPMF n hn (potential_pos_of_unit hn hu)).map (inverseEndpoint n) := by
  simp only [transitionPMF, dif_pos (show 0 < n ∧ n % 3 ≠ 0 from ⟨hn, hu⟩)]

theorem transitionPMF_support {n q : ℕ} (hn : 0 < n) (hu : n % 3 ≠ 0)
    (hq : q ∈ (transitionPMF n).support) :
    0 < q ∧ q % 2 = 1 ∧ q % 3 ≠ 0 ∧
      ∃ a : ℕ, (2 ^ a * n) % 3 = 2 ∧ q = inverseEndpoint n a := by
  rw [transitionPMF_of_unit hn hu, PMF.mem_support_map_iff] at hq
  obtain ⟨a, ha, rfl⟩ := hq
  obtain ⟨hg, hpos, hodd, hunit⟩ :=
    exponentPMF_support hn (potential_pos_of_unit hn hu) ha
  exact ⟨hpos, hodd, hunit, a, hg, rfl⟩

noncomputable def transitionKernel : Kernel ℕ ℕ where
  toFun := fun n => (transitionPMF n).toMeasure
  measurable' := measurable_of_countable _

instance transitionKernel_isMarkov : IsMarkovKernel transitionKernel where
  isProbabilityMeasure n := by change IsProbabilityMeasure (transitionPMF n).toMeasure; infer_instance

noncomputable def historyKernel (k : ℕ) : Kernel (Π _ : Finset.Iic k, ℕ) ℕ where
  toFun := fun x => transitionKernel (x ⟨k, Finset.mem_Iic.mpr le_rfl⟩)
  measurable' := transitionKernel.measurable.comp (measurable_pi_apply _)

instance historyKernel_isMarkov (k : ℕ) : IsMarkovKernel (historyKernel k) where
  isProbabilityMeasure x := by change IsProbabilityMeasure (transitionKernel _); infer_instance

noncomputable def pathLaw (n : ℕ) : Measure (ℕ → ℕ) :=
  Kernel.trajMeasure (Measure.dirac n) historyKernel

instance pathLaw_isProbability (n : ℕ) : IsProbabilityMeasure (pathLaw n) := by
  unfold pathLaw
  infer_instance

theorem pathLaw_history_successor (n k : ℕ) :
    (pathLaw n).map (frestrictLe k) ⊗ₘ historyKernel k =
      (pathLaw n).map (fun x => (frestrictLe k x, x (k + 1))) :=
  Kernel.map_frestrictLe_trajMeasure_compProd_eq_map_trajMeasure

end CollatzCylinderPacking.Arithmetic.InverseDoob
