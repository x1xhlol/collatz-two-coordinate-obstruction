import ReversedTwoDimensionalUnitEigen
import CollatzReversedRealNonsingularEigen

namespace CollatzResearch.RealUnitEigen

open Matrix CollatzCertificate RealAffine
open TwoDimensionalInvertibleMiddle TwoDimensionalNonsingularEigen TwoDimensionalUnitEigen

set_option maxHeartbeats 1000000

theorem reversed_aggregate_offset_inequality
    (A B C D E F G : Affine (Fin 2)) (h : ReversedRealWeak A B C D E F G) :
    (3 : ℝ) • (A.offset+B.offset) +
      (A.matrix+B.matrix) *ᵥ (E.offset+F.offset+G.offset) ≤
    (E.matrix+F.matrix+G.matrix) *ᵥ (A.offset+B.offset) +
      (2 : ℝ) • (E.offset+F.offset+G.offset) := by
  intro i
  have hea := h.ea.2 i
  have hfa := h.fa.2 i
  have hga := h.ga.2 i
  have heb := h.eb.2 i
  have hfb := h.fb.2 i
  have hgb := h.gb.2 i
  change (A.matrix *ᵥ E.offset) i+A.offset i ≤ (E.matrix *ᵥ A.offset) i+E.offset i at hea
  change (B.matrix *ᵥ E.offset) i+B.offset i ≤ (F.matrix *ᵥ A.offset) i+F.offset i at hfa
  change (A.matrix *ᵥ F.offset) i+A.offset i ≤ (G.matrix *ᵥ A.offset) i+G.offset i at hga
  change (B.matrix *ᵥ F.offset) i+B.offset i ≤ (E.matrix *ᵥ B.offset) i+E.offset i at heb
  change (A.matrix *ᵥ G.offset) i+A.offset i ≤ (F.matrix *ᵥ B.offset) i+F.offset i at hfb
  change (B.matrix *ᵥ G.offset) i+B.offset i ≤ (G.matrix *ᵥ B.offset) i+G.offset i at hgb
  simp only [add_mulVec,mulVec_add,Pi.add_apply,Pi.smul_apply,smul_eq_mul]
  linarith only [hea,hfa,hga,heb,hfb,hgb]

theorem subcritical_aggregate_binary_offsets_zero
    (A B C D E F G : Affine (Fin 2)) (w : Vec (Fin 2)) (m : ℝ)
    (hA : A.Nonnegative) (hB : B.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hw : ∀ i, 0 < w i) (hm : m < 1)
    (hwP : w ᵥ* (A.matrix+B.matrix)=(2 : ℝ) • w)
    (hwT : w ᵥ* (E.matrix+F.matrix+G.matrix)=(3*m) • w) :
    A.offset=0 ∧ B.offset=0 := by
  have hi := dotProduct_le_dotProduct_of_nonneg_left
    (reversed_aggregate_offset_inequality A B C D E F G h) (fun i => (hw i).le)
  simp only [dotProduct_add,dotProduct_smul,dotProduct_mulVec,hwP,hwT,
    smul_dotProduct,smul_eq_mul] at hi
  have ha : 0 ≤ w ⬝ᵥ A.offset := dotProduct_nonneg_of_nonneg (fun i => (hw i).le) hA.2
  have hb : 0 ≤ w ⬝ᵥ B.offset := dotProduct_nonneg_of_nonneg (fun i => (hw i).le) hB.2
  have hsum : w ⬝ᵥ A.offset+w ⬝ᵥ B.offset=0 := by nlinarith only [hi,ha,hb,hm]
  have hwa : w ⬝ᵥ A.offset=0 := by linarith only [hsum,ha,hb]
  have hwb : w ⬝ᵥ B.offset=0 := by linarith only [hsum,ha,hb]
  constructor
  · funext i
    have hn (j : Fin 2) : 0 ≤ w j*A.offset j := mul_nonneg (hw j).le (hA.2 j)
    have hz := congrFun ((Fintype.sum_eq_zero_iff_of_nonneg hn).mp hwa) i
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt (hw i))
  · funext i
    have hn (j : Fin 2) : 0 ≤ w j*B.offset j := mul_nonneg (hw j).le (hB.2 j)
    have hz := congrFun ((Fintype.sum_eq_zero_iff_of_nonneg hn).mp hwb) i
    exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt (hw i))

theorem strict_reversed_unit_common_eigenvalue_impossible
    (A B C D E F G : Affine (Fin 2)) (i₀ : Fin 2)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀)
    (hreturn : ∀ i j : Fin 2, ∃ k : ℕ,
      0 < (((A.matrix+B.matrix)+(E.matrix+F.matrix+G.matrix))^k) j i)
    (u : Vec (Fin 2)) (hu : ∀ i, 0 < u i)
    (hAu : A.matrix *ᵥ u=u) (hBu : B.matrix *ᵥ u=u) : False := by
  have hf := RealMiddleRankExtension.strict_reversed_middle_invertible_of_returns
    A B C D E F G i₀ hA hB hC hD hE hF hG h hstrict hreturn
  have ha := (RealSingularBinary.strict_reversed_binary_matrices_invertible_of_returns
    A B C D E F G i₀ hA hB hC hD hE hF hG h hstrict hreturn).1
  have hs : ReversedExactSwaps A.matrix B.matrix E.matrix F.matrix G.matrix :=
    reversed_swap_equalities_of_all_returns A.matrix B.matrix E.matrix F.matrix G.matrix
      hA.1 hB.1 hE.1 hF.1 hG.1 h.ea.1 h.fa.1 h.ga.1 h.eb.1 h.fb.1 h.gb.1 hreturn
  have hne : A.matrix*B.matrix ≠ B.matrix*A.matrix := by
    intro hc
    apply RealOrderedTwo.ordered_binary_matrices_exclude_two_dimensions
      A B C D E F G i₀ hA hB hC hD hE hF hG h hstrict
    intro i j
    rw [hc]
  obtain ⟨μ,t,hμ,_ht,htrA,htrB,hdetA,hdetB,hAN,hNA,he,hfshape,hg⟩ :=
    reversed_nonsingular_unequal_shape A.matrix B.matrix E.matrix F.matrix G.matrix
      hs hA.1 hB.1 hE.1 hF.1 hG.1 ha hf hne
  have hH : EntrywiseLE 0 ((A.matrix+B.matrix)+(E.matrix+F.matrix+G.matrix)) := fun i j =>
    add_nonneg (add_nonneg (hA.1 i j) (hB.1 i j))
      (add_nonneg (add_nonneg (hE.1 i j) (hF.1 i j)) (hG.1 i j))
  have h01 := positive_offdiagonal_of_return _ hH 0 1 (by decide) (hreturn 1 0)
  have h10 := positive_offdiagonal_of_return _ hH 1 0 (by decide) (hreturn 0 1)
  obtain ⟨w,hw,hwP,hwT⟩ := nonsingular_shape_positive_left_aggregate
    A.matrix B.matrix E.matrix F.matrix G.matrix μ t hμ hA.1 hB.1
      htrA htrB hdetA hdetB hAN hNA he hfshape hg h01 h10
  have hwu : 0 < w ⬝ᵥ u := by
    simp only [dotProduct,Fin.sum_univ_two]
    exact add_pos (mul_pos (hw 0) (hu 0)) (mul_pos (hw 1) (hu 1))
  have heigen := congrArg (fun x : Vec (Fin 2) => x ⬝ᵥ u) hwP
  dsimp only at heigen
  rw [← dotProduct_mulVec,add_mulVec,hAu,hBu,dotProduct_add,
    smul_dotProduct,smul_eq_mul] at heigen
  have hμhalf : μ=1/2 := by nlinarith only [heigen,hwu]
  have hGu : G.matrix *ᵥ u=(3*t*μ) • u := by
    rw [hg,smul_mulVec,sub_mulVec,smul_mulVec,smul_mulVec,one_mulVec,hBu]
    funext i
    simp only [Pi.smul_apply,Pi.sub_apply,smul_eq_mul,two_smul,Pi.add_apply]
    rw [hμhalf]
    ring
  let r : Vec (Fin 2) := D.matrix i₀
  have hr : 0 ≤ r := fun j => hD.1 i₀ j
  have hrne : r ≠ 0 := by
    intro hz
    have hda : (D.comp A).offset i₀=D.offset i₀ := by
      change r ⬝ᵥ A.offset+D.offset i₀=D.offset i₀
      rw [hz,zero_dotProduct,zero_add]
    have hdb : (D.comp B).offset i₀=(D.comp G).offset i₀ := by
      change r ⬝ᵥ B.offset+D.offset i₀=r ⬝ᵥ G.offset+D.offset i₀
      rw [hz,zero_dotProduct,zero_dotProduct]
    rcases hstrict with ht | ht
    · exact (ne_of_gt ht) hda
    · exact (ne_of_gt ht) hdb
  have hml := (positive_common_eigenvalue_bounds A.matrix B.matrix G.matrix r u 1 (3*t*μ)
    hr hrne hu (fun j => h.da.1 i₀ j) (fun j => h.db.1 i₀ j)
      (by simpa only [one_smul] using hAu) (by simpa only [one_smul] using hBu) hGu).2
  by_cases hcrit : 3*t*μ=1
  · have htval : t=2/3 := by rw [hμhalf] at hcrit; nlinarith only [hcrit]
    have hGu1 : G.matrix *ᵥ u=u := by rw [hGu,hcrit,one_smul]
    have hrA : r ᵥ* A.matrix=r :=
      RealCriticalReadout.row_nondecrease_fixed_by_positive_vector A.matrix r u hu hAu
        (fun j => h.da.1 i₀ j)
    have hrG : r ᵥ* G.matrix=r ᵥ* B.matrix := by
      apply ordered_rows_equal_of_positive_dot (r ᵥ* G.matrix) (r ᵥ* B.matrix) u
        (fun j => h.db.1 i₀ j) hu
      rw [← dotProduct_mulVec,← dotProduct_mulVec,hGu1,hBu]
    have hrB : r ᵥ* B.matrix=r := by
      funext i
      have hi := congrFun hrG i
      rw [hg,vecMul_smul,vecMul_sub,vecMul_smul,vecMul_smul,vecMul_one] at hi
      simp only [Pi.smul_apply,Pi.sub_apply,smul_eq_mul,two_smul,Pi.add_apply] at hi
      rw [hμhalf,htval] at hi
      linarith only [hi]
    apply RealAbovePowers.real_second_row_not_first_eigenrow A B C D E F G i₀
      hA hB hC hD hE hF hG h hstrict 1 (by norm_num)
    change (r ᵥ* B.matrix) ᵥ* A.matrix=1 • (r ᵥ* B.matrix)
    rw [hrB,hrA,one_smul]
  · have hm : 3*t*μ < 1 := lt_of_le_of_ne hml hcrit
    have hwP2 : w ᵥ* (A.matrix+B.matrix)=(2 : ℝ) • w := by
      rw [hμhalf] at hwP
      norm_num at hwP
      exact hwP
    have hwT3 : w ᵥ* (E.matrix+F.matrix+G.matrix)=(3*(3*t*μ)) • w := by
      have hcoeff : 3*(3*t*μ)=9*t*μ := by ring
      simpa only [hcoeff] using hwT
    obtain ⟨ha0,hb0⟩ := subcritical_aggregate_binary_offsets_zero A B C D E F G w (3*t*μ)
      hA hB h hw hm hwP2 hwT3
    have hda0 : (D.comp A).offset i₀=D.offset i₀ := by
      change r ⬝ᵥ A.offset+D.offset i₀=D.offset i₀
      rw [ha0,dotProduct_zero,zero_add]
    have hdb0 : (D.comp B).offset i₀=D.offset i₀ := by
      change r ⬝ᵥ B.offset+D.offset i₀=D.offset i₀
      rw [hb0,dotProduct_zero,zero_add]
    have hgpos : D.offset i₀ ≤ (D.comp G).offset i₀ := by
      change D.offset i₀ ≤ r ⬝ᵥ G.offset+D.offset i₀
      exact le_add_of_nonneg_left (dotProduct_nonneg_of_nonneg hr hG.2)
    rcases hstrict with ht | ht
    · exact (ne_of_gt ht) hda0
    · linarith only [ht,hdb0,hgpos]

theorem strict_reversed_expanding_common_eigenvector_of_returns
    (A B C D E F G : Affine (Fin 2)) (i₀ : Fin 2)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀)
    (hreturn : ∀ i j : Fin 2, ∃ k : ℕ,
      0 < (((A.matrix+B.matrix)+(E.matrix+F.matrix+G.matrix))^k) j i) :
    ∃ l m : ℝ, ∃ u : Vec (Fin 2), 1 < l ∧ 0 < m ∧ m ≤ l ∧ (∀ i, 0 < u i) ∧
      A.matrix *ᵥ u=l • u ∧ B.matrix *ᵥ u=l • u ∧
      E.matrix *ᵥ u=m • u ∧ F.matrix *ᵥ u=m • u ∧ G.matrix *ᵥ u=m • u := by
  obtain ⟨l,m,u,hl,hm,hml,hu,hAu,hBu,hEu,hFu,hGu⟩ :=
    RealNonsingularEigen.strict_reversed_common_positive_eigenvector_of_returns
      A B C D E F G i₀ hA hB hC hD hE hF hG h hstrict hreturn
  have hlex : 1 < l := by
    by_contra hn
    have hl1 : l=1 := le_antisymm (le_of_not_gt hn) hl
    subst l
    exact strict_reversed_unit_common_eigenvalue_impossible A B C D E F G i₀
      hA hB hC hD hE hF hG h hstrict hreturn u hu
        (by simpa only [one_smul] using hAu) (by simpa only [one_smul] using hBu)
  exact ⟨l,m,u,hlex,hm,hml,hu,hAu,hBu,hEu,hFu,hGu⟩

end CollatzResearch.RealUnitEigen

#print axioms CollatzResearch.RealUnitEigen.reversed_aggregate_offset_inequality
#print axioms CollatzResearch.RealUnitEigen.subcritical_aggregate_binary_offsets_zero
#print axioms CollatzResearch.RealUnitEigen.strict_reversed_unit_common_eigenvalue_impossible
#print axioms CollatzResearch.RealUnitEigen.strict_reversed_expanding_common_eigenvector_of_returns
