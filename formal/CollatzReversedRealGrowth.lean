import ReversedRealNormalization
import CollatzRankGrowth

namespace CollatzResearch.RealGrowth

open Matrix CollatzCertificate RealAffine

theorem map_iterate {α β : Type*} (f : α → β) (a : α → α) (b : β → β)
    (h : ∀ x, f (a x) = b (f x)) (n : ℕ) (x : α) :
    f (a^[n] x) = b^[n] (f x) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [Function.iterate_succ_apply', h, ih]

theorem map_wordEval {α β : Type*} (f : α → β) (a b : α → α) (A B : β → β)
    (ha : ∀ x, f (a x) = A (f x)) (hb : ∀ x, f (b x) = B (f x))
    (w : List Bool) (x : α) :
    f (RankGrowth.wordEval a b w x) = RankGrowth.wordEval A B w (f x) := by
  induction w with
  | nil => rfl
  | cons bit w ih =>
    cases bit <;> simp only [RankGrowth.wordEval, Bool.false_eq_true, ↓reduceIte, ha, hb, ih]

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def wordMatrix (A B : Mat ι) : List Bool → Mat ι
  | [] => 1
  | bit :: w => (if bit then B else A) * wordMatrix A B w

theorem wordEval_affine (A B : Affine ι) (w : List Bool) (x : Vec ι) :
    RankGrowth.wordEval (eval A) (eval B) w x =
      wordMatrix A.matrix B.matrix w *ᵥ x + RankGrowth.wordEval (eval A) (eval B) w 0 := by
  induction w with
  | nil => simp [RankGrowth.wordEval, wordMatrix]
  | cons bit w ih =>
    cases bit <;> simp only [RankGrowth.wordEval, wordMatrix, Bool.false_eq_true, ↓reduceIte]
    all_goals rw [ih]
    all_goals simp only [eval, Matrix.mulVec_add, Matrix.mulVec_mulVec, add_assoc]

theorem observed_wordEval (D A B : Affine ι) (i₀ : ι) (w : List Bool) (x : Vec ι) :
    eval D (RankGrowth.wordEval (eval A) (eval B) w x) i₀ =
      (D.matrix i₀ ᵥ* wordMatrix A.matrix B.matrix w) ⬝ᵥ x +
        eval D (RankGrowth.wordEval (eval A) (eval B) w 0) i₀ := by
  change D.matrix i₀ ⬝ᵥ RankGrowth.wordEval (eval A) (eval B) w x + D.offset i₀ =
    (D.matrix i₀ ᵥ* wordMatrix A.matrix B.matrix w) ⬝ᵥ x +
      (D.matrix i₀ ⬝ᵥ RankGrowth.wordEval (eval A) (eval B) w 0 + D.offset i₀)
  rw [wordEval_affine A B w x, dotProduct_add, dotProduct_mulVec, add_assoc]

omit [DecidableEq ι] in
theorem real_reversed_word_b_growth
    (A B C D E F G : Affine ι) (i₀ : ι)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀)
    (w : List Bool) (K : ℝ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      K < eval D (RankGrowth.wordEval (eval A) (eval B) w ((eval B)^[n] C.offset)) i₀ := by
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
  obtain ⟨N, hN⟩ := RankGrowth.reversed_word_b_growth c hda hdb hs w (Nat.ceil (K / δ))
  refine ⟨N, ?_⟩
  intro n hn
  let x := RankGrowth.wordEval c.a c.b w (c.b^[n] c.initial)
  have hg : (Nat.ceil (K / δ) : ℝ) < (c.readout x : ℝ) := by
    exact_mod_cast hN n hn
  have hf : (c.readout x : ℝ) ≤ eval D x.val i₀ / δ :=
    Nat.floor_le (div_nonneg (eval_nonnegative hD x.property i₀) hδ.le)
  have hgt : K < eval D x.val i₀ := (div_lt_div_iff_of_pos_right hδ).mp
    (lt_of_le_of_lt (Nat.le_ceil (K / δ)) (lt_of_lt_of_le hg hf))
  have hx : x.val = RankGrowth.wordEval (eval A) (eval B) w ((eval B)^[n] C.offset) := by
    dsimp only [x]
    rw [map_wordEval Subtype.val c.a c.b (eval A) (eval B) (fun _ => rfl) (fun _ => rfl)]
    rw [map_iterate Subtype.val c.b (eval B) (fun _ => rfl)]
  rwa [hx] at hgt

theorem real_reversed_word_row_growth
    (A B C D E F G : Affine ι) (i₀ : ι)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀)
    (w : List Bool) (K : ℝ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      K < (D.matrix i₀ ᵥ* wordMatrix A.matrix B.matrix w) ⬝ᵥ ((eval B)^[n] C.offset) := by
  obtain ⟨N, hN⟩ := real_reversed_word_b_growth A B C D E F G i₀
    hA hB hC hD hE hF hG h hstrict w
    (K + eval D (RankGrowth.wordEval (eval A) (eval B) w 0) i₀)
  refine ⟨N, ?_⟩
  intro n hn
  have hg := hN n hn
  rw [observed_wordEval D A B i₀ w ((eval B)^[n] C.offset)] at hg
  linarith

#print axioms map_iterate
#print axioms map_wordEval
#print axioms wordEval_affine
#print axioms observed_wordEval
#print axioms real_reversed_word_b_growth
#print axioms real_reversed_word_row_growth

end CollatzResearch.RealGrowth
