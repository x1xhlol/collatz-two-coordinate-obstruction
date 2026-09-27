import CollatzReversedRealMixedGrowth
import CollatzReversedRealPowerContraction

namespace CollatzResearch.RealSupportFamily

open Matrix CollatzCertificate RealMixedGrowth

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def rowSupport (r : Vec ι) : Finset ι := by
  classical
  exact Finset.univ.filter (fun i => 0 < r i)

noncomputable def successor (M : Mat ι) (S : Finset ι) : Finset ι := by
  classical
  exact Finset.univ.filter (fun j => ∃ i ∈ S, 0 < M i j)

noncomputable def sourceGood (B : Mat ι) (t : Vec ι) : Finset ι :=
  (Finset.Ico (Fintype.card ι) (2 * Fintype.card ι)).biUnion (fun k => rowSupport (B ^ k *ᵥ t))

omit [DecidableEq ι] in
theorem support_vecMul (r : Vec ι) (M : Mat ι) (hr : 0 ≤ r) (hM : EntrywiseLE 0 M) :
    rowSupport (r ᵥ* M) = successor M (rowSupport r) := by
  classical
  ext j
  simp only [rowSupport, successor, Finset.mem_filter, Finset.mem_univ, true_and,
    Matrix.vecMul, dotProduct]
  rw [Finset.sum_pos_iff_of_nonneg (fun i _ => mul_nonneg (hr i) (hM i j))]
  constructor
  · rintro ⟨i, _, hi⟩
    exact ⟨i, pos_of_mul_pos_left hi (hM i j), pos_of_mul_pos_right hi (hr i)⟩
  · rintro ⟨i, hri, hmi⟩
    exact ⟨i, Finset.mem_univ i, mul_pos hri hmi⟩

theorem matrixWord_append (maps : MixedSupport.Digit → Mat ι) (v w : List MixedSupport.Digit) :
    matrixWord maps (v ++ w) = matrixWord maps v * matrixWord maps w := by
  induction v with
  | nil => simp [matrixWord]
  | cons k v ih => simp only [List.cons_append, matrixWord, ih, Matrix.mul_assoc]

theorem source_support_intersection (B : Mat ι) (r t : Vec ι)
    (hB : EntrywiseLE 0 B) (hr : 0 ≤ r) (ht : 0 ≤ t)
    (h : ∃ k : ℕ, Fintype.card ι ≤ k ∧ k < 2 * Fintype.card ι ∧
      0 < (r ᵥ* B ^ k) ⬝ᵥ t) :
    ∃ i ∈ rowSupport r, i ∈ sourceGood B t := by
  classical
  obtain ⟨k, hk, hkd, hp⟩ := h
  have ht' := RealContraction.nonnegative_matrix_power_mulVec B hB t ht k
  rw [← dotProduct_mulVec] at hp
  obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun j _ =>
    mul_nonneg (hr j) (ht' j))).mp hp
  refine ⟨i, ?_, ?_⟩
  · simp only [rowSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    exact pos_of_mul_pos_left hi (ht' i)
  · simp only [sourceGood, Finset.mem_biUnion, Finset.mem_Ico, rowSupport,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨k, ⟨hk, hkd⟩, pos_of_mul_pos_right hi (hr i)⟩

theorem reversed_real_closed_safe_family
    (A B C D E F G : Affine ι) (i₀ : ι)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀) :
    ∃ family : Finset (Finset ι), rowSupport (D.matrix i₀) ∈ family ∧
      ∀ S ∈ family, (∀ k : MixedSupport.Digit, successor (affineDigit A B E F G k).matrix S ∈ family) ∧
        ∃ i ∈ S, i ∈ sourceGood B.matrix (C.offset + B.offset) := by
  classical
  let maps := fun k => (affineDigit A B E F G k).matrix
  have hm : ∀ k, EntrywiseLE 0 (maps k) := by
    intro k
    cases k
    · exact hA.1
    · exact hB.1
    · exact hE.1
    · exact hF.1
    · exact hG.1
  have hrw (w : List MixedSupport.Digit) : 0 ≤ D.matrix i₀ ᵥ* matrixWord maps w :=
    rowMul_nonneg (fun j => hD.1 i₀ j) (matrixWord_nonnegative maps hm w)
  let family : Finset (Finset ι) := Finset.univ.filter (fun S =>
    ∃ w : List MixedSupport.Digit, rowSupport (D.matrix i₀ ᵥ* matrixWord maps w) = S)
  have hfamily (S : Finset ι) : S ∈ family ↔
      ∃ w : List MixedSupport.Digit, rowSupport (D.matrix i₀ ᵥ* matrixWord maps w) = S := by
    simp only [family, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨family, ?_, ?_⟩
  · rw [hfamily]
    exact ⟨[], by simp [matrixWord]⟩
  · intro S hS
    obtain ⟨w, rfl⟩ := (hfamily S).mp hS
    constructor
    · intro k
      rw [hfamily]
      refine ⟨w ++ [k], ?_⟩
      rw [matrixWord_append]
      simp only [matrixWord, Matrix.mul_one]
      rw [← vecMul_vecMul]
      exact support_vecMul _ _ (hrw w) (hm k)
    · exact source_support_intersection B.matrix _ _ hB.1 (hrw w)
        (fun i => add_nonneg (hC.2 i) (hB.2 i))
        (real_mixed_source_support A B C D E F G i₀ hA hB hC hD hE hF hG h hstrict w)

#print axioms support_vecMul
#print axioms matrixWord_append
#print axioms source_support_intersection
#print axioms reversed_real_closed_safe_family

end CollatzResearch.RealSupportFamily
