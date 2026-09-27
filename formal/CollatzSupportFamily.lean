import CollatzFiniteSourceSupport

namespace CollatzResearch.SupportFamily

open Matrix RankGrowth ReversedNaturalConditions

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def rowSupport (r : ι → ℕ) : Finset ι := Finset.univ.filter (fun i => 0 < r i)

def successor (M : Matrix ι ι ℕ) (S : Finset ι) : Finset ι :=
  Finset.univ.filter (fun j => ∃ i ∈ S, 0 < M i j)

def sourceGood (B : Matrix ι ι ℕ) (t : ι → ℕ) : Finset ι :=
  (Finset.Ico (Fintype.card ι) (2 * Fintype.card ι)).biUnion (fun k => rowSupport (B ^ k *ᵥ t))

omit [DecidableEq ι] in
theorem support_vecMul (r : ι → ℕ) (M : Matrix ι ι ℕ) :
    rowSupport (r ᵥ* M) = successor M (rowSupport r) := by
  ext j
  simp only [rowSupport, successor, Finset.mem_filter, Finset.mem_univ, true_and,
    Matrix.vecMul, dotProduct]
  rw [Finset.sum_pos_iff_of_nonneg (fun i _ => Nat.zero_le _)]
  constructor
  · rintro ⟨i, _, hi⟩
    exact ⟨i, Nat.pos_of_mul_pos_right hi, Nat.pos_of_mul_pos_left hi⟩
  · rintro ⟨i, hri, hmi⟩
    exact ⟨i, Finset.mem_univ i, Nat.mul_pos hri hmi⟩

theorem wordMatrix_append (A B : Matrix ι ι ℕ) (v w : List Bool) :
    wordMatrix A B (v ++ w) = wordMatrix A B v * wordMatrix A B w := by
  induction v with
  | nil => simp [wordMatrix]
  | cons bit v ih => simp only [List.cons_append, wordMatrix, ih, Matrix.mul_assoc]

theorem source_support_intersection (B : Matrix ι ι ℕ) (r t : ι → ℕ)
    (h : ∃ k : ℕ, Fintype.card ι ≤ k ∧ k < 2 * Fintype.card ι ∧
      0 < (r ᵥ* B ^ k) ⬝ᵥ t) :
    ∃ i ∈ rowSupport r, i ∈ sourceGood B t := by
  obtain ⟨k, hk, hkd, hp⟩ := h
  rw [← dotProduct_mulVec] at hp
  obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg (fun j _ =>
    Nat.zero_le (r j * (B ^ k *ᵥ t) j))).mp hp
  refine ⟨i, ?_, ?_⟩
  · simp only [rowSupport, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Nat.pos_of_mul_pos_right hi
  · simp only [sourceGood, Finset.mem_biUnion, Finset.mem_Ico, rowSupport,
      Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨k, ⟨hk, hkd⟩, Nat.pos_of_mul_pos_left hi⟩

theorem reversed_closed_safe_family (m : Model ι) (i₀ : ι) (h : WeakRules m)
    (hs : StrictOffset m i₀) :
    ∃ F : Finset (Finset ι), rowSupport (m.d.matrix i₀) ∈ F ∧
      ∀ S ∈ F, successor m.a.matrix S ∈ F ∧ successor m.b.matrix S ∈ F ∧
        ∃ i ∈ S, i ∈ sourceGood m.b.matrix (m.c.offset + m.b.offset) := by
  classical
  let F : Finset (Finset ι) := Finset.univ.filter (fun S =>
    ∃ w : List Bool, rowSupport (m.d.matrix i₀ ᵥ* wordMatrix m.a.matrix m.b.matrix w) = S)
  have hF (S : Finset ι) : S ∈ F ↔
      ∃ w : List Bool, rowSupport (m.d.matrix i₀ ᵥ* wordMatrix m.a.matrix m.b.matrix w) = S := by
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨F, ?_, ?_⟩
  · rw [hF]
    exact ⟨[], by simp [wordMatrix]⟩
  · intro S hS
    obtain ⟨w, rfl⟩ := (hF S).mp hS
    refine ⟨?_, ?_, ?_⟩
    · rw [hF]
      refine ⟨w ++ [false], ?_⟩
      rw [wordMatrix_append]
      simp only [wordMatrix, Bool.false_eq_true, ↓reduceIte, Matrix.mul_one]
      rw [← vecMul_vecMul, support_vecMul]
    · rw [hF]
      refine ⟨w ++ [true], ?_⟩
      rw [wordMatrix_append]
      simp only [wordMatrix, ↓reduceIte, Matrix.mul_one]
      rw [← vecMul_vecMul, support_vecMul]
    · exact source_support_intersection m.b.matrix _ _
        (FiniteSourceSupport.reversed_all_prefix_source_support m i₀ h hs w)

#print axioms support_vecMul
#print axioms wordMatrix_append
#print axioms source_support_intersection
#print axioms reversed_closed_safe_family

end CollatzResearch.SupportFamily
