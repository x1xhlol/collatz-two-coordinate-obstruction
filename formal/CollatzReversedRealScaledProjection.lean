import CollatzReversedRealCriticalReadout

namespace CollatzResearch.RealScaledProjection

open Matrix CollatzCertificate RealAffine RealCriticalReadout

theorem scaled_offset_constraints
    (l m u v x y e f rb rg sb : ℝ)
    (hl : 1 ≤ l) (hm : 0 ≤ m) (hml : m ≤ l)
    (hu : 0 ≤ u) (hv : 0 ≤ v) (hx : 0 ≤ x)
    (he : 0 ≤ e) (hf : 0 ≤ f) (hsb : 0 ≤ sb)
    (hdb : rg ≤ rb)
    (hfa : l * e + rb ≤ m * u + f)
    (hga : l * f + u ≤ m * v + rg)
    (hfc : l ^ 2 * x + (l + 1) * u ≤ m * x + f)
    (hgc : l ^ 2 * x + l * v + rb ≤ m * y + rg)
    (hec : l * y + sb ≤ m * x + e) :
    rb = rg ∧ (u = 0 ∨ l = 1 ∧ m = 1) := by
  have hl0 : 0 ≤ l := le_trans (by norm_num) hl
  have hl2 : 0 ≤ l ^ 2 - m := by nlinarith only [hl, hml, sq_nonneg (l - 1)]
  have hl3 : 0 ≤ l ^ 3 - m ^ 2 := by
    have h1 := mul_nonneg (sub_nonneg.mpr hml) (add_nonneg hl0 hm)
    have h2 := mul_nonneg (sq_nonneg l) (sub_nonneg.mpr hl)
    nlinarith only [h1, h2]
  have hn1 := mul_nonneg (mul_nonneg hm hl2) hu
  have hn2 := mul_nonneg hl3 hv
  have hn3 := mul_nonneg
    (add_nonneg (mul_nonneg hl0 hl3)
      (mul_nonneg (mul_nonneg hm (sub_nonneg.mpr hl)) hl2)) hx
  have hn4 := mul_nonneg (add_nonneg (sq_nonneg l) hm) (sub_nonneg.mpr hdb)
  have hn5 := mul_nonneg (mul_nonneg hl0 hm) hsb
  have hweight : 0 ≤ m * (l - 1) := mul_nonneg hm (sub_nonneg.mpr hl)
  have hsum : m * (l ^ 2 - m) * u + (l ^ 3 - m ^ 2) * v +
      (l * (l ^ 3 - m ^ 2) + m * (l - 1) * (l ^ 2 - m)) * x +
      (l ^ 2 + m) * (rb - rg) + l * m * sb ≤ 0 := by
    linear_combination m * hfa + m * hga + m * (l - 1) * hfc +
      l ^ 2 * hgc + l * m * hec
  have hz4 : (l ^ 2 + m) * (rb - rg) = 0 := by
    linarith only [hsum, hn1, hn2, hn3, hn4, hn5]
  have hz1 : m * (l ^ 2 - m) * u = 0 := by
    linarith only [hsum, hn1, hn2, hn3, hn4, hn5]
  have hcoeff : 0 < l ^ 2 + m := by nlinarith only [hl, hm, sq_nonneg (l - 1)]
  have hgap : rb = rg := sub_eq_zero.mp
    ((mul_eq_zero.mp hz4).resolve_left (ne_of_gt hcoeff))
  refine ⟨hgap, ?_⟩
  by_cases hmz : m = 0
  · left
    simp only [hmz, zero_mul, zero_add] at hfa hga
    have hef : 0 ≤ l * e := mul_nonneg hl0 he
    have hlf : f ≤ l * f := by nlinarith only [mul_nonneg (sub_nonneg.mpr hl) hf]
    linarith only [hfa, hga, hgap, hef, hlf, hu]
  · by_cases huz : u = 0
    · exact Or.inl huz
    · right
      have hlm : l ^ 2 = m := sub_eq_zero.mp
        ((mul_eq_zero.mp ((mul_eq_zero.mp hz1).resolve_right huz)).resolve_left hmz)
      have hle : l ≤ 1 := by nlinarith only [hlm, hml, hl]
      have hleq : l = 1 := le_antisymm hle hl
      exact ⟨hleq, by nlinarith only [hlm, hleq]⟩

variable {ι : Type*} [Fintype ι]

theorem scaled_readout_offset_constraints
    (A B C D E F G : Affine ι) (i₀ : ι) (s : Vec ι) (l m : ℝ)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hs : 0 ≤ s) (hl : 1 ≤ l) (hm : 0 ≤ m) (hml : m ≤ l)
    (hrA : D.matrix i₀ ᵥ* A.matrix = l • D.matrix i₀)
    (hrB : D.matrix i₀ ᵥ* B.matrix = l • s)
    (hsA : s ᵥ* A.matrix = l • D.matrix i₀)
    (hsB : s ᵥ* B.matrix = l • s)
    (hrF : D.matrix i₀ ᵥ* F.matrix = m • D.matrix i₀)
    (hrG : D.matrix i₀ ᵥ* G.matrix = m • s)
    (hsE : s ᵥ* E.matrix = m • D.matrix i₀) :
    D.matrix i₀ ⬝ᵥ B.offset = D.matrix i₀ ⬝ᵥ G.offset ∧
      (D.matrix i₀ ⬝ᵥ A.offset = 0 ∨ l = 1 ∧ m = 1) := by
  let r : Vec ι := D.matrix i₀
  have hr : 0 ≤ r := fun j => hD.1 i₀ j
  have hdb : r ⬝ᵥ G.offset ≤ r ⬝ᵥ B.offset := by
    have hi := h.db.2 i₀
    change r ⬝ᵥ G.offset + D.offset i₀ ≤ r ⬝ᵥ B.offset + D.offset i₀ at hi
    linarith only [hi]
  have hfa := dotProduct_le_dotProduct_of_nonneg_left h.fa.2 hr
  have hga := dotProduct_le_dotProduct_of_nonneg_left h.ga.2 hr
  have hfc := dotProduct_le_dotProduct_of_nonneg_left h.fc.2 hr
  have hgc := dotProduct_le_dotProduct_of_nonneg_left h.gc.2 hr
  have hec := dotProduct_le_dotProduct_of_nonneg_left h.ec.2 hs
  change r ⬝ᵥ (B.matrix *ᵥ E.offset + B.offset) ≤
    r ⬝ᵥ (F.matrix *ᵥ A.offset + F.offset) at hfa
  change r ⬝ᵥ (A.matrix *ᵥ F.offset + A.offset) ≤
    r ⬝ᵥ (G.matrix *ᵥ A.offset + G.offset) at hga
  change r ⬝ᵥ (A.matrix *ᵥ (A.matrix *ᵥ C.offset + A.offset) + A.offset) ≤
    r ⬝ᵥ (F.matrix *ᵥ C.offset + F.offset) at hfc
  change r ⬝ᵥ (B.matrix *ᵥ (A.matrix *ᵥ C.offset + A.offset) + B.offset) ≤
    r ⬝ᵥ (G.matrix *ᵥ C.offset + G.offset) at hgc
  change s ⬝ᵥ (B.matrix *ᵥ C.offset + B.offset) ≤
    s ⬝ᵥ (E.matrix *ᵥ C.offset + E.offset) at hec
  simp only [r, dotProduct_add, dotProduct_mulVec, hrA, hrB, hsA, hsB,
    hrF, hrG, hsE, smul_vecMul, smul_dotProduct, smul_eq_mul] at hfa hga hfc hgc hec
  have hfc' : l ^ 2 * (r ⬝ᵥ C.offset) + (l + 1) * (r ⬝ᵥ A.offset) ≤
      m * (r ⬝ᵥ C.offset) + r ⬝ᵥ F.offset := by
    dsimp [r]
    nlinarith only [hfc]
  have hgc' : l ^ 2 * (r ⬝ᵥ C.offset) + l * (s ⬝ᵥ A.offset) + r ⬝ᵥ B.offset ≤
      m * (s ⬝ᵥ C.offset) + r ⬝ᵥ G.offset := by
    dsimp [r]
    nlinarith only [hgc]
  exact scaled_offset_constraints l m (r ⬝ᵥ A.offset) (s ⬝ᵥ A.offset)
    (r ⬝ᵥ C.offset) (s ⬝ᵥ C.offset) (s ⬝ᵥ E.offset) (r ⬝ᵥ F.offset)
    (r ⬝ᵥ B.offset) (r ⬝ᵥ G.offset) (s ⬝ᵥ B.offset) hl hm hml
    (dotProduct_nonneg_of_nonneg hr hA.2) (dotProduct_nonneg_of_nonneg hs hA.2)
    (dotProduct_nonneg_of_nonneg hr hC.2) (dotProduct_nonneg_of_nonneg hs hE.2)
    (dotProduct_nonneg_of_nonneg hr hF.2) (dotProduct_nonneg_of_nonneg hs hB.2)
    hdb hfa hga hfc' hgc' hec

theorem readout_scale_bounds
    (A B F G : Mat ι) (r s : Vec ι) (l m : ℝ)
    (hr : 0 ≤ r) (hrpos : ∃ j, 0 < r j)
    (hB : EntrywiseLE 0 B) (hF : EntrywiseLE 0 F)
    (hda : r ≤ r ᵥ* A) (hdb : r ᵥ* G ≤ r ᵥ* B)
    (hrA : r ᵥ* A = l • r) (hrB : r ᵥ* B = l • s)
    (hsA : s ᵥ* A = l • r)
    (hrF : r ᵥ* F = m • r) (hrG : r ᵥ* G = m • s) :
    0 ≤ s ∧ 1 ≤ l ∧ 0 ≤ m ∧ m ≤ l := by
  obtain ⟨j, hj⟩ := hrpos
  have hlj := hda j
  rw [hrA] at hlj
  change r j ≤ l * r j at hlj
  have hl : 1 ≤ l := by nlinarith only [hlj, hj]
  have hfj := rowMul_nonneg hr hF j
  rw [hrF] at hfj
  change 0 ≤ m * r j at hfj
  have hm : 0 ≤ m := by nlinarith only [hfj, hj]
  have hs : 0 ≤ s := by
    intro k
    change 0 ≤ s k
    have hbk := rowMul_nonneg hr hB k
    rw [hrB] at hbk
    change 0 ≤ l * s k at hbk
    nlinarith only [hbk, hl]
  have hsp : ∃ k, 0 < s k := by
    by_contra hn
    have hsz : s = 0 := funext (fun k =>
      le_antisymm (not_lt.mp ((not_exists.mp hn) k)) (hs k))
    have hj' := congrFun hsA j
    rw [hsz, zero_vecMul] at hj'
    change 0 = l * r j at hj'
    nlinarith only [hj', hl, hj]
  obtain ⟨k, hk⟩ := hsp
  have hmk := hdb k
  rw [hrG, hrB] at hmk
  change m * s k ≤ l * s k at hmk
  exact ⟨hs, hl, hm, by nlinarith only [hmk, hk]⟩

variable [DecidableEq ι]

theorem scaled_readout_excludes_strict
    (A B C D E F G : Affine ι) (i₀ : ι) (s : Vec ι) (l m : ℝ)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀)
    (hs : 0 ≤ s) (hl : 1 ≤ l) (hm : 0 ≤ m) (hml : m ≤ l)
    (hrA : D.matrix i₀ ᵥ* A.matrix = l • D.matrix i₀)
    (hrB : D.matrix i₀ ᵥ* B.matrix = l • s)
    (hsA : s ᵥ* A.matrix = l • D.matrix i₀)
    (hsB : s ᵥ* B.matrix = l • s)
    (hrF : D.matrix i₀ ᵥ* F.matrix = m • D.matrix i₀)
    (hrG : D.matrix i₀ ᵥ* G.matrix = m • s)
    (hsE : s ᵥ* E.matrix = m • D.matrix i₀) : False := by
  obtain ⟨hgap, hu | ⟨hl1, hm1⟩⟩ := scaled_readout_offset_constraints A B C D E F G i₀
    s l m hA hB hC hD hE hF h hs hl hm hml hrA hrB hsA hsB hrF hrG hsE
  · rcases hstrict with ha | hb
    · change D.offset i₀ < D.matrix i₀ ⬝ᵥ A.offset + D.offset i₀ at ha
      linarith only [ha, hu]
    · change D.matrix i₀ ⬝ᵥ G.offset + D.offset i₀ <
        D.matrix i₀ ⬝ᵥ B.offset + D.offset i₀ at hb
      linarith only [hb, hgap]
  · subst l m
    simp only [one_smul] at hrA hrB hsA hsB hrF hsE
    apply critical_readout_excludes_strict A B C D E F G i₀
      hA hB hC hD hE hF hG h hstrict
    · rw [hrB, hsA]
    · rw [hrB, hsB]
    · rw [hrB, hsE]
    · rw [hrF]

theorem scaled_readout_gaps_zero
    (A B C D E F G : Affine ι) (i₀ : ι) (s : Vec ι) (l m : ℝ)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hrA : D.matrix i₀ ᵥ* A.matrix = l • D.matrix i₀)
    (hrB : D.matrix i₀ ᵥ* B.matrix = l • s)
    (hsA : s ᵥ* A.matrix = l • D.matrix i₀)
    (hsB : s ᵥ* B.matrix = l • s)
    (hrF : D.matrix i₀ ᵥ* F.matrix = m • D.matrix i₀)
    (hrG : D.matrix i₀ ᵥ* G.matrix = m • s)
    (hsE : s ᵥ* E.matrix = m • D.matrix i₀) :
    (D.comp A).offset i₀ = D.offset i₀ ∧
      (D.comp B).offset i₀ = (D.comp G).offset i₀ := by
  by_cases hpos : ∃ j, 0 < D.matrix i₀ j
  · obtain ⟨hs, hl, hm, hml⟩ := readout_scale_bounds A.matrix B.matrix F.matrix G.matrix
      (D.matrix i₀) s l m (fun j => hD.1 i₀ j) hpos hB.1 hF.1
      (fun j => h.da.1 i₀ j) (fun j => h.db.1 i₀ j) hrA hrB hsA hrF hrG
    have hn := scaled_readout_excludes_strict A B C D E F G i₀ s l m
      hA hB hC hD hE hF hG h
    constructor
    · apply le_antisymm _ (h.da.2 i₀)
      by_contra hp
      exact hn (Or.inl (lt_of_not_ge hp)) hs hl hm hml hrA hrB hsA hsB hrF hrG hsE
    · apply le_antisymm _ (h.db.2 i₀)
      by_contra hp
      exact hn (Or.inr (lt_of_not_ge hp)) hs hl hm hml hrA hrB hsA hsB hrF hrG hsE
  · have hrz : D.matrix i₀ = 0 := funext (fun j =>
      le_antisymm (not_lt.mp ((not_exists.mp hpos) j)) (hD.1 i₀ j))
    change D.matrix i₀ ⬝ᵥ A.offset + D.offset i₀ = D.offset i₀ ∧
      D.matrix i₀ ⬝ᵥ B.offset + D.offset i₀ = D.matrix i₀ ⬝ᵥ G.offset + D.offset i₀
    simp only [hrz, zero_dotProduct, zero_add, and_self]

#print axioms scaled_offset_constraints
#print axioms scaled_readout_offset_constraints
#print axioms readout_scale_bounds
#print axioms scaled_readout_excludes_strict
#print axioms scaled_readout_gaps_zero

end CollatzResearch.RealScaledProjection
