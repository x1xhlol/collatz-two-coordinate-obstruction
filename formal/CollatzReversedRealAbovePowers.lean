import CollatzReversedRealGrowth
import CollatzRankAbovePowers
import ReversedTwoStepReadout
import ReversedReadoutIndependence

namespace CollatzResearch.RealAbovePowers

open Matrix CollatzCertificate RealAffine RealGrowth

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
theorem real_reversed_b_a_growth
    (A B C D E F G : Affine ι) (i₀ : ι)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀)
    (K : ℝ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      K < eval D (eval B ((eval A)^[n] C.offset)) i₀ := by
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
  obtain ⟨N, hN⟩ := RankAbovePowers.reversed_b_a_growth c hda hdb hs (Nat.ceil (K / δ))
  refine ⟨N, ?_⟩
  intro n hn
  let x := c.b (c.a^[n] c.initial)
  have hg : (Nat.ceil (K / δ) : ℝ) < (c.readout x : ℝ) := by
    exact_mod_cast hN n hn
  have hf : (c.readout x : ℝ) ≤ eval D x.val i₀ / δ :=
    Nat.floor_le (div_nonneg (eval_nonnegative hD x.property i₀) hδ.le)
  have hgt : K < eval D x.val i₀ := (div_lt_div_iff_of_pos_right hδ).mp
    (lt_of_le_of_lt (Nat.le_ceil (K / δ)) (lt_of_lt_of_le hg hf))
  have hx : x.val = eval B ((eval A)^[n] C.offset) := by
    change eval B ((c.a^[n] c.initial).val) = eval B ((eval A)^[n] C.offset)
    rw [map_iterate Subtype.val c.a (eval A) (fun _ => rfl)]
  rwa [hx] at hgt

omit [DecidableEq ι] in
theorem real_reversed_b_a_row_growth
    (A B C D E F G : Affine ι) (i₀ : ι)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀)
    (K : ℝ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      K < (D.matrix i₀ ᵥ* B.matrix) ⬝ᵥ ((eval A)^[n] C.offset) := by
  obtain ⟨N, hN⟩ := real_reversed_b_a_growth A B C D E F G i₀
    hA hB hC hD hE hF hG h hstrict (K + D.matrix i₀ ⬝ᵥ B.offset + D.offset i₀)
  refine ⟨N, ?_⟩
  intro n hn
  have hg := hN n hn
  change K + D.matrix i₀ ⬝ᵥ B.offset + D.offset i₀ <
    D.matrix i₀ ⬝ᵥ (B.matrix *ᵥ ((eval A)^[n] C.offset) + B.offset) + D.offset i₀ at hg
  rw [dotProduct_add, dotProduct_mulVec] at hg
  linarith

omit [DecidableEq ι] in
theorem contracting_eigenrow_iterates_bounded (A : Affine ι) (q γ : Vec ι) (β : ℝ)
    (hq : 0 ≤ q) (hγ : 0 ≤ γ) (ha : 0 ≤ A.offset) (hβ : 0 ≤ β) (hβone : β < 1)
    (heigen : q ᵥ* A.matrix = β • q) :
    ∃ L : ℝ, ∀ n : ℕ, q ⬝ᵥ ((eval A)^[n] γ) ≤ L := by
  let L := q ⬝ᵥ γ + (q ⬝ᵥ A.offset) / (1 - β)
  have hden : 0 < 1 - β := sub_pos.mpr hβone
  have hqγ := dotProduct_nonneg_of_nonneg hq hγ
  have hqa := dotProduct_nonneg_of_nonneg hq ha
  have hbase : q ⬝ᵥ γ ≤ L := by
    dsimp [L]
    linarith [div_nonneg hqa hden.le]
  have hstep : β * L + q ⬝ᵥ A.offset ≤ L := by
    have heq := div_mul_cancel₀ (q ⬝ᵥ A.offset) (ne_of_gt hden)
    dsimp [L]
    nlinarith
  refine ⟨L, ?_⟩
  intro n
  induction n with
  | zero => exact hbase
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    change q ⬝ᵥ (A.matrix *ᵥ ((eval A)^[n] γ) + A.offset) ≤ L
    rw [dotProduct_add, dotProduct_mulVec, heigen, smul_dotProduct]
    change β * (q ⬝ᵥ ((eval A)^[n] γ)) + q ⬝ᵥ A.offset ≤ L
    have hmul := mul_le_mul_of_nonneg_left ih hβ
    linarith

omit [DecidableEq ι] in
theorem real_second_row_not_first_eigenrow
    (A B C D E F G : Affine ι) (i₀ : ι)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀)
    (β : ℝ) (hβ : 0 ≤ β)
    (heigen : (D.matrix i₀ ᵥ* B.matrix) ᵥ* A.matrix = β • (D.matrix i₀ ᵥ* B.matrix)) :
    False := by
  by_cases hβone : β < 1
  · obtain ⟨L, hL⟩ := contracting_eigenrow_iterates_bounded A (D.matrix i₀ ᵥ* B.matrix)
      C.offset β (rowMul_nonneg (fun j => hD.1 i₀ j) hB.1) hC.2 hA.2 hβ hβone heigen
    obtain ⟨N, hN⟩ := real_reversed_b_a_row_growth A B C D E F G i₀
      hA hB hC hD hE hF hG h hstrict L
    exact (not_lt_of_ge (hL N)) (hN N le_rfl)
  · have hz := five_affine_rules_gaps_zero_of_second_row_first_eigenrow A B C D E F G i₀ β
      hA hB hC hD hE hF hG h.da h.db h.fa h.ga h.gc (le_of_not_gt hβone) heigen
    change (D.comp A).offset i₀ - D.offset i₀ = 0 ∧
      (D.comp B).offset i₀ - (D.comp G).offset i₀ = 0 at hz
    rcases hstrict with hs | hs <;> linarith [hz.1, hz.2]

omit [DecidableEq ι] in
theorem real_second_row_first_minor_nonzero
    (A B C D E F G : Affine ι) (i₀ : ι)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀) :
    ∃ i j, (D.matrix i₀ ᵥ* B.matrix) i * ((D.matrix i₀ ᵥ* B.matrix) ᵥ* A.matrix) j ≠
      (D.matrix i₀ ᵥ* B.matrix) j * ((D.matrix i₀ ᵥ* B.matrix) ᵥ* A.matrix) i := by
  classical
  by_contra hn
  have hz : ∀ i j,
      (D.matrix i₀ ᵥ* B.matrix) i * ((D.matrix i₀ ᵥ* B.matrix) ᵥ* A.matrix) j =
        (D.matrix i₀ ᵥ* B.matrix) j * ((D.matrix i₀ ᵥ* B.matrix) ᵥ* A.matrix) i := by
    intro i j
    by_contra hne
    exact hn ⟨i, j, hne⟩
  obtain ⟨β, hβ, heigen⟩ := eigenrow_of_zero_minors (D.matrix i₀ ᵥ* B.matrix) A.matrix
    (rowMul_nonneg (fun j => hD.1 i₀ j) hB.1) hA.1 hz
  exact real_second_row_not_first_eigenrow A B C D E F G i₀
    hA hB hC hD hE hF hG h hstrict β hβ heigen

#print axioms real_reversed_b_a_growth
#print axioms real_reversed_b_a_row_growth
#print axioms contracting_eigenrow_iterates_bounded
#print axioms real_second_row_not_first_eigenrow
#print axioms real_second_row_first_minor_nonzero

end CollatzResearch.RealAbovePowers
