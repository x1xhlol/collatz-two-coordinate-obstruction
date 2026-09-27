import CollatzRankPositiveOffsets
import CollatzReversedRealSupportFamily

namespace CollatzResearch.RealPositiveOffsets

open Matrix CollatzCertificate RealAffine RealGrowth RealMixedGrowth RealSupportFamily

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem real_reversed_mixed_b_a_growth
    (A B C D E F G : Affine ι) (i₀ : ι)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀)
    (w : List MixedSupport.Digit) (K : ℝ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      K < eval D (MixedSupport.eval (fun k => eval (affineDigit A B E F G k)) w (eval B ((eval A)^[n] C.offset))) i₀ := by
  obtain ⟨δ, hδ, hgap⟩ : ∃ δ : ℝ, 0 < δ ∧
      (δ ≤ (D.comp A).offset i₀ - D.offset i₀ ∨
        δ ≤ (D.comp B).offset i₀ - (D.comp G).offset i₀) := by
    rcases hstrict with hs | hs
    · exact ⟨_, sub_pos.mpr hs, Or.inl le_rfl⟩
    · exact ⟨_, sub_pos.mpr hs, Or.inr le_rfl⟩
  let c : ReversedCertificate.Data {x : Vec ι // 0 ≤ x} := {
    a := fun x => ⟨eval A x.1, eval_nonnegative hA x.2⟩
    b := fun x => ⟨eval B x.1, eval_nonnegative hB x.2⟩
    e := fun x => ⟨eval E x.1, eval_nonnegative hE x.2⟩
    f := fun x => ⟨eval F x.1, eval_nonnegative hF x.2⟩
    g := fun x => ⟨eval G x.1, eval_nonnegative hG x.2⟩
    readout := fun x => Nat.floor (eval D x.1 i₀ / δ)
    initial := ⟨C.offset, hC.2⟩
    a_monotone := fun _ _ hx => eval_monotone hA.1 hx
    b_monotone := fun _ _ hx => eval_monotone hB.1 hx
    readout_monotone := fun _ _ hx => Nat.floor_mono
      (div_le_div_of_nonneg_right (eval_monotone hD.1 hx i₀) hδ.le)
    ea := fun x => by simpa only [eval_comp] using eval_weak h.ea x.2
    fa := fun x => by simpa only [eval_comp] using eval_weak h.fa x.2
    ga := fun x => by simpa only [eval_comp] using eval_weak h.ga x.2
    eb := fun x => by simpa only [eval_comp] using eval_weak h.eb x.2
    fb := fun x => by simpa only [eval_comp] using eval_weak h.fb x.2
    gb := fun x => by simpa only [eval_comp] using eval_weak h.gb x.2
    ec := h.ec.2
    fc := h.fc.2
    gc := h.gc.2
  }
  have hda : ∀ x, c.readout x ≤ c.readout (c.a x) := by
    intro x
    apply Nat.floor_mono
    apply div_le_div_of_nonneg_right _ hδ.le
    simpa only [eval_comp] using eval_weak h.da x.2 i₀
  have hdb : ∀ x, c.readout (c.g x) ≤ c.readout (c.b x) := by
    intro x
    apply Nat.floor_mono
    apply div_le_div_of_nonneg_right _ hδ.le
    simpa only [eval_comp] using eval_weak h.db x.2 i₀
  have hs : (∀ x, c.readout x < c.readout (c.a x)) ∨
      (∀ x, c.readout (c.g x) < c.readout (c.b x)) := by
    rcases hgap with hg | hg
    · left
      intro x
      apply floor_scaled_gap (eval_nonnegative hD x.2 i₀) hδ
      have hi := eval_offset_gap h.da i₀ x.2
      rw [eval_comp] at hi
      change eval D x.1 i₀ + δ ≤ eval D (eval A x.1) i₀
      linarith
    · right
      intro x
      apply floor_scaled_gap (eval_nonnegative hD (eval_nonnegative hG x.2) i₀) hδ
      have hi := eval_offset_gap h.db i₀ x.2
      simp only [eval_comp] at hi
      change eval D (eval G x.1) i₀ + δ ≤ eval D (eval B x.1) i₀
      linarith
  have hmono : ∀ k, Monotone (MixedSupport.digitMap c k) := by
    intro k
    cases k
    · exact fun _ _ hx => eval_monotone hA.1 hx
    · exact fun _ _ hx => eval_monotone hB.1 hx
    · exact fun _ _ hx => eval_monotone hE.1 hx
    · exact fun _ _ hx => eval_monotone hF.1 hx
    · exact fun _ _ hx => eval_monotone hG.1 hx
  obtain ⟨N, hN⟩ := RankPositiveOffsets.reversed_mixed_b_a_growth c hmono hda hdb hs w (Nat.ceil (K / δ))
  refine ⟨N, ?_⟩
  intro n hn
  let x := MixedSupport.eval (MixedSupport.digitMap c) w (c.b (c.a^[n] c.initial))
  have hg : (Nat.ceil (K / δ) : ℝ) < (c.readout x : ℝ) := by
    exact_mod_cast hN n hn
  have hf : (c.readout x : ℝ) ≤ eval D x.val i₀ / δ :=
    Nat.floor_le (div_nonneg (eval_nonnegative hD x.property i₀) hδ.le)
  have hgt : K < eval D x.val i₀ := (div_lt_div_iff_of_pos_right hδ).mp
    (lt_of_le_of_lt (Nat.le_ceil (K / δ)) (lt_of_lt_of_le hg hf))
  have hx : x.val = MixedSupport.eval (fun k => eval (affineDigit A B E F G k)) w (eval B ((eval A)^[n] C.offset)) := by
    dsimp only [x]
    have hm (k : MixedSupport.Digit) (y : {x : Vec ι // 0 ≤ x}) :
        (MixedSupport.digitMap c k y).val = eval (affineDigit A B E F G k) y.val := by
      cases k <;> rfl
    rw [map_mixedEval Subtype.val (MixedSupport.digitMap c)
      (fun k => eval (affineDigit A B E F G k)) hm]
    change MixedSupport.eval (fun k => eval (affineDigit A B E F G k)) w
      (eval B ((c.a^[n] c.initial).val)) = _
    rw [map_iterate Subtype.val c.a (eval A) (fun _ => rfl)]
  rwa [hx] at hgt

theorem real_mixed_first_row_growth
    (A B C D E F G : Affine ι) (i₀ : ι)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀)
    (w : List MixedSupport.Digit) (K : ℝ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      K < ((D.matrix i₀ ᵥ* matrixWord (fun k => (affineDigit A B E F G k).matrix) w) ᵥ* B.matrix) ⬝ᵥ
        ((eval A)^[n] C.offset) := by
  obtain ⟨N, hN⟩ := real_reversed_mixed_b_a_growth A B C D E F G i₀
    hA hB hC hD hE hF hG h hstrict w
    (K + (D.matrix i₀ ᵥ* matrixWord (fun k => (affineDigit A B E F G k).matrix) w) ⬝ᵥ B.offset +
      eval D (MixedSupport.eval (fun k => eval (affineDigit A B E F G k)) w 0) i₀)
  refine ⟨N, ?_⟩
  intro n hn
  have hg := hN n hn
  rw [observed_mixedEval D (affineDigit A B E F G) i₀ w (eval B ((eval A)^[n] C.offset))] at hg
  change _ < (D.matrix i₀ ᵥ* matrixWord (fun k => (affineDigit A B E F G k).matrix) w) ⬝ᵥ
    (B.matrix *ᵥ ((eval A)^[n] C.offset) + B.offset) + _ at hg
  rw [dotProduct_add, dotProduct_mulVec] at hg
  linarith

theorem real_mixed_first_source_support
    (A B C D E F G : Affine ι) (i₀ : ι)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀) (w : List MixedSupport.Digit) :
    ∃ k : ℕ, Fintype.card ι ≤ k ∧ k < 2 * Fintype.card ι ∧
      (((D.matrix i₀ ᵥ* matrixWord (fun k => (affineDigit A B E F G k).matrix) w) ᵥ* B.matrix) ᵥ*
        A.matrix ^ k) ⬝ᵥ (C.offset + A.offset) > 0 := by
  letI : Nonempty ι := ⟨i₀⟩
  have hm : ∀ k, EntrywiseLE 0 (affineDigit A B E F G k).matrix := by
    intro k
    cases k
    · exact hA.1
    · exact hB.1
    · exact hE.1
    · exact hF.1
    · exact hG.1
  apply RealSource.unbounded_iterates_have_finite_source_support A _ C.offset hA
    (rowMul_nonneg (rowMul_nonneg (fun j => hD.1 i₀ j) (matrixWord_nonnegative _ hm w)) hB.1) hC.2
  exact real_mixed_first_row_growth A B C D E F G i₀ hA hB hC hD hE hF hG h hstrict w

theorem reversed_real_two_source_family
    (A B C D E F G : Affine ι) (i₀ : ι)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀) :
    ∃ family : Finset (Finset ι), rowSupport (D.matrix i₀) ∈ family ∧
      ∀ S ∈ family, (∀ k : MixedSupport.Digit, successor (affineDigit A B E F G k).matrix S ∈ family) ∧
        (∃ i ∈ S, i ∈ sourceGood B.matrix (C.offset + B.offset)) ∧
        ∃ j ∈ successor B.matrix S, j ∈ sourceGood A.matrix (C.offset + A.offset) := by
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
    refine ⟨?_, ?_, ?_⟩
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
    · have hs := source_support_intersection A.matrix _ _ hA.1 (rowMul_nonneg (hrw w) hB.1)
        (fun i => add_nonneg (hC.2 i) (hA.2 i))
        (real_mixed_first_source_support A B C D E F G i₀ hA hB hC hD hE hF hG h hstrict w)
      rw [support_vecMul _ _ (hrw w) hB.1] at hs
      exact hs

#print axioms real_reversed_mixed_b_a_growth
#print axioms real_mixed_first_row_growth
#print axioms real_mixed_first_source_support
#print axioms reversed_real_two_source_family

end CollatzResearch.RealPositiveOffsets
