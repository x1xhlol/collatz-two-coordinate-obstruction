import ReversedRealNormalization

namespace CollatzCertificate

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def coordinateChange (S T : Mat ι) (F : Affine ι) : Affine ι :=
  ⟨S * F.matrix * T, S *ᵥ F.offset⟩

def inputChange (T : Mat ι) (D : Affine ι) : Affine ι :=
  ⟨D.matrix * T, D.offset⟩

theorem coordinateChange_comp (S T : Mat ι) (hTS : T * S = 1) (F G : Affine ι) :
    (coordinateChange S T F).comp (coordinateChange S T G) = coordinateChange S T (F.comp G) := by
  have hm (M : Mat ι) : T * (S * M) = M := by rw [← mul_assoc, hTS, one_mul]
  simp only [coordinateChange, Affine.comp, mul_assoc, hm, mulVec_mulVec, mulVec_add, hTS, mul_one]

theorem inputChange_comp (S T : Mat ι) (hTS : T * S = 1) (D F : Affine ι) :
    (inputChange T D).comp (coordinateChange S T F) = inputChange T (D.comp F) := by
  have hm (M : Mat ι) : T * (S * M) = M := by rw [← mul_assoc, hTS, one_mul]
  simp only [inputChange, coordinateChange, Affine.comp, mul_assoc, hm, mulVec_mulVec, hTS, mul_one]

omit [DecidableEq ι] in
theorem coordinateChange_nonnegative (S T : Mat ι) (hS : EntrywiseLE 0 S) (hT : EntrywiseLE 0 T)
    (F : Affine ι) (hF : F.Nonnegative) : (coordinateChange S T F).Nonnegative := by
  constructor
  · intro i j
    change 0 ≤ ∑ k, (∑ l, S i l * F.matrix l k) * T k j
    exact Finset.sum_nonneg (fun k _ => mul_nonneg
      (Finset.sum_nonneg (fun l _ => mul_nonneg (hS i l) (hF.1 l k))) (hT k j))
  · intro i
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (hS i j) (hF.2 j))

omit [DecidableEq ι] in
theorem inputChange_nonnegative (T : Mat ι) (hT : EntrywiseLE 0 T)
    (D : Affine ι) (hD : D.Nonnegative) : (inputChange T D).Nonnegative := by
  constructor
  · intro i j
    exact Finset.sum_nonneg (fun k _ => mul_nonneg (hD.1 i k) (hT k j))
  · exact hD.2

omit [DecidableEq ι] in
theorem coordinateChange_weak (S T : Mat ι) (hS : EntrywiseLE 0 S) (hT : EntrywiseLE 0 T)
    {F G : Affine ι} (h : F.Weak G) : (coordinateChange S T F).Weak (coordinateChange S T G) := by
  constructor
  · intro i j
    change (∑ k, (∑ l, S i l * G.matrix l k) * T k j) ≤
      ∑ k, (∑ l, S i l * F.matrix l k) * T k j
    exact Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right
      (Finset.sum_le_sum (fun l _ => mul_le_mul_of_nonneg_left (h.1 l k) (hS i l))) (hT k j))
  · intro i
    exact Finset.sum_le_sum (fun j _ => mul_le_mul_of_nonneg_left (h.2 j) (hS i j))

omit [DecidableEq ι] in
theorem inputChange_weak (T : Mat ι) (hT : EntrywiseLE 0 T)
    {F G : Affine ι} (h : F.Weak G) : (inputChange T F).Weak (inputChange T G) := by
  constructor
  · intro i j
    exact Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right (h.1 i k) (hT k j))
  · exact h.2

theorem coordinateChange_reversed_weak (S T : Mat ι)
    (hS : EntrywiseLE 0 S) (hT : EntrywiseLE 0 T) (hTS : T * S = 1)
    (A B C D E F G : Affine ι) (h : ReversedRealWeak A B C D E F G) :
    ReversedRealWeak (coordinateChange S T A) (coordinateChange S T B)
      (coordinateChange S T C) (inputChange T D) (coordinateChange S T E)
      (coordinateChange S T F) (coordinateChange S T G) := by
  constructor
  · simpa only [inputChange_comp S T hTS] using inputChange_weak T hT h.da
  · simpa only [inputChange_comp S T hTS] using inputChange_weak T hT h.db
  · simpa only [coordinateChange_comp S T hTS] using coordinateChange_weak S T hS hT h.ea
  · simpa only [coordinateChange_comp S T hTS] using coordinateChange_weak S T hS hT h.fa
  · simpa only [coordinateChange_comp S T hTS] using coordinateChange_weak S T hS hT h.ga
  · simpa only [coordinateChange_comp S T hTS] using coordinateChange_weak S T hS hT h.eb
  · simpa only [coordinateChange_comp S T hTS] using coordinateChange_weak S T hS hT h.fb
  · simpa only [coordinateChange_comp S T hTS] using coordinateChange_weak S T hS hT h.gb
  · simpa only [coordinateChange_comp S T hTS] using coordinateChange_weak S T hS hT h.ec
  · simpa only [coordinateChange_comp S T hTS] using coordinateChange_weak S T hS hT h.fc
  · simpa only [coordinateChange_comp S T hTS] using coordinateChange_weak S T hS hT h.gc

theorem inputChange_comp_offset (S T : Mat ι) (hTS : T * S = 1) (D F : Affine ι) :
    ((inputChange T D).comp (coordinateChange S T F)).offset = (D.comp F).offset := by
  rw [inputChange_comp S T hTS]
  rfl

noncomputable def readoutScale (r : Vec ι) (j : ι) : ℝ := if r j = 0 then 1 else r j

omit [Fintype ι] [DecidableEq ι] in
theorem readoutScale_pos (r : Vec ι) (hr : 0 ≤ r) (j : ι) : 0 < readoutScale r j := by
  by_cases hz : r j = 0
  · simp [readoutScale, hz]
  · simpa only [readoutScale, hz, ↓reduceIte] using lt_of_le_of_ne (hr j) (Ne.symm hz)

omit [Fintype ι] in
theorem diagonal_entrywise_nonnegative (z : Vec ι) (hz : 0 ≤ z) : EntrywiseLE 0 (diagonal z) := by
  intro i j
  by_cases heq : i = j
  · subst j
    simpa using hz i
  · simp [Matrix.diagonal, heq]

theorem readoutScale_inverse (r : Vec ι) (hr : 0 ≤ r) :
    diagonal (fun j => (readoutScale r j)⁻¹) * diagonal (readoutScale r) = (1 : Mat ι) := by
  rw [diagonal_mul_diagonal]
  have heq : (fun j => (readoutScale r j)⁻¹ * readoutScale r j) = fun _ => (1 : ℝ) := by
    funext j
    exact inv_mul_cancel₀ (ne_of_gt (readoutScale_pos r hr j))
  rw [heq, diagonal_one]

theorem inputChange_readout_boolean (D : Affine ι) (i₀ j : ι) :
    (inputChange (diagonal (fun k => (readoutScale (D.matrix i₀) k)⁻¹)) D).matrix i₀ j =
      if D.matrix i₀ j = 0 then 0 else 1 := by
  by_cases hz : D.matrix i₀ j = 0
  · simp [inputChange, mul_diagonal, readoutScale, hz]
  · simp [inputChange, mul_diagonal, readoutScale, hz]

theorem coordinateChange_root_gaps (S T : Mat ι) (hTS : T * S = 1)
    (A B D G : Affine ι) (i₀ : ι) :
    (((inputChange T D).comp (coordinateChange S T A)).offset - (inputChange T D).offset) i₀ =
      ((D.comp A).offset - D.offset) i₀ ∧
    (((inputChange T D).comp (coordinateChange S T B)).offset -
      ((inputChange T D).comp (coordinateChange S T G)).offset) i₀ =
      ((D.comp B).offset - (D.comp G).offset) i₀ := by
  simp only [inputChange_comp_offset S T hTS]
  exact ⟨rfl, trivial⟩

omit [DecidableEq ι] in
theorem coordinateChange_preserves_zero_initial_matrix (S T : Mat ι)
    (C : Affine ι) (hC : C.matrix = 0) : (coordinateChange S T C).matrix = 0 := by
  simp [coordinateChange, hC]

omit [DecidableEq ι] in
theorem inputChange_preserves_zero_other_rows (T : Mat ι) (D : Affine ι) (i₀ : ι)
    (hD : ∀ i j, i ≠ i₀ → D.matrix i j = 0) :
    ∀ i j, i ≠ i₀ → (inputChange T D).matrix i j = 0 := by
  intro i j hi
  simp [inputChange, mul_apply, hD i _ hi]

theorem exists_boolean_readout_change (D : Affine ι) (i₀ : ι) (hD : D.Nonnegative) :
    ∃ S T : Mat ι, EntrywiseLE 0 S ∧ EntrywiseLE 0 T ∧ T * S = 1 ∧
      ∀ j, (inputChange T D).matrix i₀ j = 0 ∨ (inputChange T D).matrix i₀ j = 1 := by
  let r := D.matrix i₀
  have hr : 0 ≤ r := fun j => hD.1 i₀ j
  refine ⟨diagonal (readoutScale r), diagonal (fun j => (readoutScale r j)⁻¹),
    diagonal_entrywise_nonnegative _ (fun j => (readoutScale_pos r hr j).le),
    diagonal_entrywise_nonnegative _ (fun j => (inv_pos.mpr (readoutScale_pos r hr j)).le),
    readoutScale_inverse r hr, ?_⟩
  intro j
  change (inputChange (diagonal (fun j => (readoutScale (D.matrix i₀) j)⁻¹)) D).matrix i₀ j = 0 ∨
    (inputChange (diagonal (fun j => (readoutScale (D.matrix i₀) j)⁻¹)) D).matrix i₀ j = 1
  rw [inputChange_readout_boolean]
  split <;> simp

#print axioms coordinateChange_comp
#print axioms inputChange_comp
#print axioms coordinateChange_nonnegative
#print axioms inputChange_nonnegative
#print axioms coordinateChange_weak
#print axioms inputChange_weak
#print axioms coordinateChange_reversed_weak
#print axioms inputChange_comp_offset
#print axioms readoutScale_pos
#print axioms diagonal_entrywise_nonnegative
#print axioms readoutScale_inverse
#print axioms inputChange_readout_boolean
#print axioms coordinateChange_root_gaps
#print axioms coordinateChange_preserves_zero_initial_matrix
#print axioms inputChange_preserves_zero_other_rows
#print axioms exists_boolean_readout_change

end CollatzCertificate
