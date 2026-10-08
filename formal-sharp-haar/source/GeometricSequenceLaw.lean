import CompatibleSyracuseResidues
import Mathlib.Probability.Distributions.Geometric
import Mathlib.Probability.Independence.InfinitePi

set_option autoImplicit false

open MeasureTheory

namespace CollatzCylinderPacking.Arithmetic

noncomputable def halfGeometricMeasure : Measure ℕ :=
  ProbabilityTheory.geometricMeasure (p := (1 / 2 : ℝ)) (by norm_num) (by norm_num)

instance halfGeometricProbability : IsProbabilityMeasure halfGeometricMeasure :=
  ProbabilityTheory.isProbabilityMeasure_geometricMeasure (by norm_num) (by norm_num)

noncomputable def geometricSequenceMeasure : Measure (ℕ → ℕ) :=
  Measure.infinitePi (fun _ : ℕ => halfGeometricMeasure)

instance geometricSequenceProbability : IsProbabilityMeasure geometricSequenceMeasure := by
  unfold geometricSequenceMeasure
  infer_instance

theorem half_geometric_singleton (a : ℕ) :
    halfGeometricMeasure {a} = ENNReal.ofReal ((1 / 2 : ℝ) ^ (a + 1)) := by
  rw [halfGeometricMeasure, ProbabilityTheory.geometricMeasure,
    PMF.toMeasure_apply_singleton _ a (measurableSet_singleton a)]
  change ENNReal.ofReal ((1 - (1 / 2 : ℝ)) ^ a * (1 / 2)) = _
  congr 1
  norm_num only
  rw [pow_succ]

def wordCoordinate : (k : ℕ) → GeometricWord k → ℕ → ℕ
  | 0, _, _ => 0
  | _k + 1, (a, _w), 0 => a
  | k + 1, (_a, w), i + 1 => wordCoordinate k w i

theorem sequenceWord_eq_iff (k : ℕ) (f : ℕ → ℕ) (w : GeometricWord k) :
    sequenceWord k f = w ↔ ∀ i < k, f i = wordCoordinate k w i := by
  induction k generalizing f with
  | zero => cases w; simp [sequenceWord]
  | succ k ih =>
    rcases w with ⟨a, w⟩
    constructor
    · intro he
      change (f 0, sequenceWord k (fun i => f (i + 1))) = (a, w) at he
      have hp := Prod.mk.inj he
      intro i hi
      cases i with
      | zero => exact hp.1
      | succ i => exact (ih (fun j => f (j + 1)) w).mp hp.2 i (by omega)
    · intro he
      have ha := he 0 (by omega)
      have hw : sequenceWord k (fun i => f (i + 1)) = w := by
        apply (ih (fun j => f (j + 1)) w).mpr
        intro i hi
        exact he (i + 1) (by omega)
      change (f 0, sequenceWord k (fun i => f (i + 1))) = (a, w)
      rw [hw]
      exact congrArg (fun b => (b, w)) ha

theorem sum_word_coordinates (k : ℕ) (w : GeometricWord k) :
    (∑ i ∈ Finset.range k, (wordCoordinate k w i + 1)) = wordLength k w := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rcases w with ⟨a, w⟩
    rw [Finset.sum_range_succ']
    simp only [wordCoordinate, wordLength, ih]
    omega

theorem sequenceWord_event (k : ℕ) (w : GeometricWord k) :
    {f : ℕ → ℕ | sequenceWord k f = w} =
      Set.pi (Finset.range k) (fun i => {wordCoordinate k w i}) := by
  ext f
  simp only [Set.mem_setOf_eq, sequenceWord_eq_iff, Set.mem_pi,
    Finset.mem_coe, Finset.mem_range, Set.mem_singleton_iff]

/-- The actual infinite product measure gives every prefix word its full
independent geometric weight. -/
theorem sequenceWord_probability (k : ℕ) (w : GeometricWord k) :
    geometricSequenceMeasure {f : ℕ → ℕ | sequenceWord k f = w} =
      ENNReal.ofReal ((1 / 2 : ℝ) ^ wordLength k w) := by
  rw [sequenceWord_event]
  unfold geometricSequenceMeasure
  rw [Measure.infinitePi_pi _ (fun i _ => measurableSet_singleton (wordCoordinate k w i))]
  simp_rw [half_geometric_singleton]
  rw [← ENNReal.ofReal_prod_of_nonneg (fun i _ => by positivity),
    Finset.prod_pow_eq_pow_sum, sum_word_coordinates]

#print axioms sequenceWord_eq_iff
#print axioms sequenceWord_probability

end CollatzCylinderPacking.Arithmetic
