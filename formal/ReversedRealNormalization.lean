import CollatzReversedRealCertificate

namespace CollatzCertificate

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def normalizedInitial (C : Affine ι) : Affine ι := ⟨0, C.offset⟩

def normalizedReadout (D : Affine ι) (i₀ j₀ : ι) (k : ℝ) : Affine ι :=
  ⟨fun i j => if i = j₀ then k * D.matrix i₀ j else 0, 0⟩

omit [Fintype ι] [DecidableEq ι] in
theorem normalized_initial_nonnegative {C : Affine ι} (hC : C.Nonnegative) :
    (normalizedInitial C).Nonnegative := by
  exact ⟨fun _ _ => le_rfl, hC.2⟩

omit [Fintype ι] in
theorem normalized_readout_nonnegative {D : Affine ι} (hD : D.Nonnegative)
    (i₀ j₀ : ι) {k : ℝ} (hk : 0 ≤ k) :
    (normalizedReadout D i₀ j₀ k).Nonnegative := by
  constructor
  · intro i j
    by_cases hi : i = j₀
    · simpa [normalizedReadout, hi] using mul_nonneg hk (hD.1 i₀ j)
    · simp [normalizedReadout, hi]
  · exact le_rfl

omit [DecidableEq ι] in
theorem normalized_initial_preserves_weak {X Y C : Affine ι}
    (h : (X.comp C).Weak (Y.comp C)) :
    (X.comp (normalizedInitial C)).Weak (Y.comp (normalizedInitial C)) := by
  constructor
  · simp [normalizedInitial, Affine.comp, EntrywiseLE]
  · exact h.2

theorem normalized_readout_preserves_da {A D : Affine ι}
    (hA : A.Nonnegative) (hD : D.Nonnegative)
    (h : (D.comp A).Weak D) (i₀ j₀ : ι) {k : ℝ} (hk : 0 ≤ k) :
    ((normalizedReadout D i₀ j₀ k).comp A).Weak (normalizedReadout D i₀ j₀ k) := by
  constructor
  · intro i j
    by_cases hi : i = j₀
    · subst i
      simpa [normalizedReadout, Affine.comp, Matrix.mul_apply, Finset.mul_sum, mul_assoc] using
        mul_le_mul_of_nonneg_left (h.1 i₀ j) hk
    · simp [normalizedReadout, Affine.comp, Matrix.mul_apply, hi]
  · exact CollatzResearch.RealAffine.eval_nonnegative
      (normalized_readout_nonnegative hD i₀ j₀ hk) hA.2

theorem normalized_readout_preserves_db {B D G : Affine ι}
    (h : (D.comp B).Weak (D.comp G)) (i₀ j₀ : ι) {k : ℝ} (hk : 0 ≤ k) :
    ((normalizedReadout D i₀ j₀ k).comp B).Weak ((normalizedReadout D i₀ j₀ k).comp G) := by
  constructor
  · intro i j
    by_cases hi : i = j₀
    · subst i
      simpa [normalizedReadout, Affine.comp, Matrix.mul_apply, Finset.mul_sum, mul_assoc] using
        mul_le_mul_of_nonneg_left (h.1 i₀ j) hk
    · simp [normalizedReadout, Affine.comp, Matrix.mul_apply, hi]
  · intro i
    by_cases hi : i = j₀
    · subst i
      have hoff := h.2 i₀
      change (D.matrix *ᵥ G.offset) i₀ + D.offset i₀ ≤
        (D.matrix *ᵥ B.offset) i₀ + D.offset i₀ at hoff
      have hh := (add_le_add_iff_right (D.offset i₀)).mp hoff
      simpa [normalizedReadout, Affine.comp, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc] using
        mul_le_mul_of_nonneg_left hh hk
    · simp [normalizedReadout, Affine.comp, Matrix.mulVec, dotProduct, hi]

theorem normalized_readout_gap_da (A D : Affine ι) (i₀ j₀ : ι) (k : ℝ) :
    (((normalizedReadout D i₀ j₀ k).comp A).offset - (normalizedReadout D i₀ j₀ k).offset) j₀ =
      k * ((D.comp A).offset i₀ - D.offset i₀) := by
  simp [normalizedReadout, Affine.comp, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc]

theorem normalized_readout_gap_db (B D G : Affine ι) (i₀ j₀ : ι) (k : ℝ) :
    (((normalizedReadout D i₀ j₀ k).comp B).offset - ((normalizedReadout D i₀ j₀ k).comp G).offset) j₀ =
      k * ((D.comp B).offset i₀ - (D.comp G).offset i₀) := by
  simp [normalizedReadout, Affine.comp, Matrix.mulVec, dotProduct, Finset.mul_sum, mul_assoc, mul_sub]

structure ReversedRealWeak (A B C D E F G : Affine ι) : Prop where
  da : (D.comp A).Weak D
  db : (D.comp B).Weak (D.comp G)
  ea : (E.comp A).Weak (A.comp E)
  fa : (F.comp A).Weak (B.comp E)
  ga : (G.comp A).Weak (A.comp F)
  eb : (E.comp B).Weak (B.comp F)
  fb : (F.comp B).Weak (A.comp G)
  gb : (G.comp B).Weak (B.comp G)
  ec : (E.comp C).Weak (B.comp C)
  fc : (F.comp C).Weak (A.comp (A.comp C))
  gc : (G.comp C).Weak (B.comp (A.comp C))

theorem normalize_reversed_real_rules
    (A B C D E F G : Affine ι) (i₀ j₀ : ι)
    (hA : A.Nonnegative) (hC : C.Nonnegative) (hD : D.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀) :
    ∃ k : ℝ, 0 < k ∧
      (normalizedInitial C).Nonnegative ∧
      (normalizedReadout D i₀ j₀ k).Nonnegative ∧
      ReversedRealWeak A B (normalizedInitial C) (normalizedReadout D i₀ j₀ k) E F G ∧
      (1 ≤ (((normalizedReadout D i₀ j₀ k).comp A).offset -
        (normalizedReadout D i₀ j₀ k).offset) j₀ ∨
       1 ≤ (((normalizedReadout D i₀ j₀ k).comp B).offset -
        ((normalizedReadout D i₀ j₀ k).comp G).offset) j₀) := by
  obtain ⟨δ, hδ, hgap⟩ : ∃ δ : ℝ, 0 < δ ∧
      (δ = (D.comp A).offset i₀ - D.offset i₀ ∨
        δ = (D.comp B).offset i₀ - (D.comp G).offset i₀) := by
    rcases hstrict with hs | hs
    · exact ⟨_, sub_pos.mpr hs, Or.inl rfl⟩
    · exact ⟨_, sub_pos.mpr hs, Or.inr rfl⟩
  have hk : 0 < δ⁻¹ := inv_pos.mpr hδ
  refine ⟨δ⁻¹, hk, normalized_initial_nonnegative hC,
    normalized_readout_nonnegative hD i₀ j₀ hk.le, ?_, ?_⟩
  · refine ⟨normalized_readout_preserves_da hA hD h.da i₀ j₀ hk.le,
      normalized_readout_preserves_db h.db i₀ j₀ hk.le,
      h.ea, h.fa, h.ga, h.eb, h.fb, h.gb,
      normalized_initial_preserves_weak h.ec, ?_, ?_⟩
    · constructor
      · simp [normalizedInitial, Affine.comp, EntrywiseLE]
      · exact h.fc.2
    · constructor
      · simp [normalizedInitial, Affine.comp, EntrywiseLE]
      · exact h.gc.2
  · rcases hgap with hg | hg
    · left
      rw [normalized_readout_gap_da, ← hg, inv_mul_cancel₀ (ne_of_gt hδ)]
    · right
      rw [normalized_readout_gap_db, ← hg, inv_mul_cancel₀ (ne_of_gt hδ)]

omit [DecidableEq ι] in
theorem normalized_real_rules_imply_collatz
    (A B C D E F G : Affine ι) (i₀ : ι)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hgap : 1 ≤ (D.comp A).offset i₀ - D.offset i₀ ∨
      1 ≤ (D.comp B).offset i₀ - (D.comp G).offset i₀) :
    CollatzResearch.CollatzConjecture := by
  apply CollatzResearch.RealAffine.reversed_real_first_removal_implies_collatz
    A B C D E F G i₀ hA hB hC hD hE hF hG
    h.da h.db h.ea h.fa h.ga h.eb h.fb h.gb h.ec h.fc h.gc
  rcases hgap with hg | hg
  · left
    linarith
  · right
    linarith

#print axioms normalized_initial_nonnegative
#print axioms normalized_readout_nonnegative
#print axioms normalized_initial_preserves_weak
#print axioms normalized_readout_preserves_da
#print axioms normalized_readout_preserves_db
#print axioms normalized_readout_gap_da
#print axioms normalized_readout_gap_db
#print axioms normalize_reversed_real_rules
#print axioms normalized_real_rules_imply_collatz

end CollatzCertificate
