import NaturalProjectivePassageLaw

set_option autoImplicit false
open Filter
open scoped Topology BigOperators ENNReal lp

namespace CollatzCanonical.LabelLaw
open Erdos1135.Tao

noncomputable def realFixedPassageLimitPMF (x : ℝ) (hx : 1 ≤ x) :
    PMF {n : ℕ // n ≤ ⌊x⌋₊} :=
  fixedPassageLimitPMF ⌊x⌋₊ (one_le_floor_of_one_le hx)

theorem real_fixed_passage_logarithmic_odd_fullL1 (x : ℝ) (hx : 1 ≤ x) :
    Tendsto (fun t => ∑' i,
      |oddLabelLaw (fun q => syracusePassLocationRealFloorOrOne x q hx) t i -
        (realFixedPassageLimitPMF x hx i).toReal|) atTop (𝓝 0) :=
  fixedPassageLimitPMF_fullL1 ⌊x⌋₊ (one_le_floor_of_one_le hx)

theorem real_fixed_passage_logarithmic_all_start_fullL1 (x : ℝ) (hx : 1 ≤ x) :
    Tendsto (fun t => ∑' i,
      |fullLabelLaw (oddPartLabel (fun q => syracusePassLocationRealFloorOrOne x q hx)) t i -
        (realFixedPassageLimitPMF x hx i).toReal|) atTop (𝓝 0) :=
  fixedPassageLimitPMF_all_start_fullL1 ⌊x⌋₊ (one_le_floor_of_one_le hx)

theorem real_fixed_passage_natural_odd_fullL1 (x : ℝ) (hx : 1 ≤ x) :
    Tendsto (fun X => ∑' i,
      |naturalOddLabelLaw (fun q => syracusePassLocationRealFloorOrOne x q hx) X i -
        (realFixedPassageLimitPMF x hx i).toReal|) atTop (𝓝 0) :=
  fixedPassageLimitPMF_natural_odd_fullL1 ⌊x⌋₊ (one_le_floor_of_one_le hx)

theorem real_fixed_passage_natural_all_start_fullL1 (x : ℝ) (hx : 1 ≤ x) :
    Tendsto (fun X => ∑' i,
      |naturalFullLabelLaw (oddPartLabel (fun q => syracusePassLocationRealFloorOrOne x q hx)) X i -
        (realFixedPassageLimitPMF x hx i).toReal|) atTop (𝓝 0) :=
  fixedPassageLimitPMF_natural_all_start_fullL1 ⌊x⌋₊ (one_le_floor_of_one_le hx)

theorem real_fixed_passage_limit_projective {x y : ℝ}
    (hx : 1 ≤ x) (hxy : x ≤ y) (hy : 1 ≤ y) :
    (realFixedPassageLimitPMF y hy).map
      (fun z => syracusePassLocationRealFloorOrOne x z.1 hx) =
        realFixedPassageLimitPMF x hx :=
  fixed_passage_limit_projective (one_le_floor_of_one_le hx) (Nat.floor_le_floor hxy)
    (one_le_floor_of_one_le hy)

#print axioms real_fixed_passage_logarithmic_odd_fullL1
#print axioms real_fixed_passage_logarithmic_all_start_fullL1
#print axioms real_fixed_passage_natural_odd_fullL1
#print axioms real_fixed_passage_natural_all_start_fullL1
#print axioms real_fixed_passage_limit_projective

end CollatzCanonical.LabelLaw
