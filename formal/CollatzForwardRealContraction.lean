import CollatzReversedRealCertificate

namespace CollatzResearch.ForwardRealContraction

open Matrix CollatzCertificate RealAffine

variable {ι : Type*} [Fintype ι]

theorem iterate_nonnegative (A : Affine ι) (hA : A.Nonnegative)
    (x : Vec ι) (hx : 0 ≤ x) (n : ℕ) : 0 ≤ (eval A)^[n] x := by
  induction n with
  | zero => exact hx
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact eval_nonnegative hA ih

theorem iterate_swap_right (A E : Affine ι)
    (hE : E.Nonnegative)
    (hAE : (A.comp E).Weak (E.comp A))
    (n : ℕ) (x : Vec ι) (hx : 0 ≤ x) :
    (eval E)^[n] (eval A x) ≤ eval A ((eval E)^[n] x) := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact (eval_monotone hE.1 ih).trans (by
      simpa only [eval_comp] using eval_weak hAE (iterate_nonnegative E hE x hx n))

theorem iterate_swap (A E : Affine ι)
    (hA : A.Nonnegative) (hE : E.Nonnegative)
    (hAE : (A.comp E).Weak (E.comp A))
    (m n : ℕ) (x : Vec ι) (hx : 0 ≤ x) :
    (eval E)^[n] ((eval A)^[m] x) ≤ (eval A)^[m] ((eval E)^[n] x) := by
  induction m with
  | zero => exact le_rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    exact (iterate_swap_right A E hE hAE n _
      (iterate_nonnegative A hA x hx m)).trans (eval_monotone hA.1 ih)

theorem weighted_eval_le (A : Affine ι) (w : Vec ι) (l : ℝ)
    (hc : w ᵥ* A.matrix ≤ l • w) (x : Vec ι) (hx : 0 ≤ x) :
    w ⬝ᵥ eval A x ≤ l * (w ⬝ᵥ x) + w ⬝ᵥ A.offset := by
  rw [eval, dotProduct_add, dotProduct_mulVec]
  have hi := Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) =>
    mul_le_mul_of_nonneg_right (hc i) (hx i))
  have ht : (l • w) ⬝ᵥ x = l * (w ⬝ᵥ x) := by
    simp only [smul_dotProduct, smul_eq_mul]
  exact add_le_add (hi.trans_eq ht) le_rfl

theorem weighted_iterate_le (A : Affine ι) (hA : A.Nonnegative)
    (w : Vec ι) (hw : 0 ≤ w) (l : ℝ) (hl : 0 ≤ l) (hl1 : l < 1)
    (hc : w ᵥ* A.matrix ≤ l • w) (x : Vec ι) (hx : 0 ≤ x) (n : ℕ) :
    w ⬝ᵥ ((eval A)^[n] x) ≤ l ^ n * (w ⬝ᵥ x) + (w ⬝ᵥ A.offset) / (1 - l) := by
  let K := (w ⬝ᵥ A.offset) / (1 - l)
  have hK : 0 ≤ K := div_nonneg
    (Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (hA.2 i))) (by linarith)
  have hfix : l * K + w ⬝ᵥ A.offset = K := by
    have hi : K * (1 - l) = w ⬝ᵥ A.offset :=
      div_mul_cancel₀ _ (ne_of_gt (sub_pos.mpr hl1))
    nlinarith
  change w ⬝ᵥ ((eval A)^[n] x) ≤ l ^ n * (w ⬝ᵥ x) + K
  induction n with
  | zero =>
    change w ⬝ᵥ x ≤ l ^ 0 * (w ⬝ᵥ x) + K
    simp only [pow_zero, one_mul]
    linarith
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    calc
      w ⬝ᵥ eval A ((eval A)^[n] x) ≤
          l * (w ⬝ᵥ ((eval A)^[n] x)) + w ⬝ᵥ A.offset :=
        weighted_eval_le A w l hc _ (iterate_nonnegative A hA x hx n)
      _ ≤ l * (l ^ n * (w ⬝ᵥ x) + K) + w ⬝ᵥ A.offset :=
        add_le_add (mul_le_mul_of_nonneg_left ih hl) le_rfl
      _ = l ^ (n + 1) * (w ⬝ᵥ x) + K := by
        rw [mul_add, add_assoc, hfix, pow_succ]
        ring

theorem observed_ternary_iterates_bounded (A E : Affine ι)
    (hA : A.Nonnegative) (hE : E.Nonnegative)
    (hAE : (A.comp E).Weak (E.comp A))
    (r w : Vec ι) (hr : 0 ≤ r) (hw : 0 ≤ w) (hrw : r ≤ w)
    (l : ℝ) (hl : 0 ≤ l) (hl1 : l < 1)
    (hc : w ᵥ* A.matrix ≤ l • w) (n : ℕ) :
    r ⬝ᵥ ((eval E)^[n] 0) ≤ (w ⬝ᵥ A.offset) / (1 - l) := by
  let x := (eval E)^[n] (0 : Vec ι)
  have hx : 0 ≤ x := iterate_nonnegative E hE 0 le_rfl n
  have hbound (m : ℕ) : r ⬝ᵥ x ≤
      l ^ m * (w ⬝ᵥ x) + (w ⬝ᵥ A.offset) / (1 - l) := by
    have hle : x ≤ (eval A)^[m] x :=
      ((eval_monotone hE.1).iterate n (iterate_nonnegative A hA 0 le_rfl m)).trans
        (iterate_swap A E hA hE hAE m n 0 le_rfl)
    calc
      r ⬝ᵥ x ≤ r ⬝ᵥ ((eval A)^[m] x) :=
        Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hle i) (hr i))
      _ ≤ w ⬝ᵥ ((eval A)^[m] x) := Finset.sum_le_sum (fun i _ =>
        mul_le_mul_of_nonneg_right (hrw i) (iterate_nonnegative A hA x hx m i))
      _ ≤ _ := weighted_iterate_le A hA w hw l hl hl1 hc x hx m
  by_contra hn
  have hgap : 0 < r ⬝ᵥ x - (w ⬝ᵥ A.offset) / (1 - l) :=
    sub_pos.mpr (lt_of_not_ge hn)
  have hwx : 0 ≤ w ⬝ᵥ x :=
    Finset.sum_nonneg (fun i _ => mul_nonneg (hw i) (hx i))
  obtain ⟨m, hm⟩ := exists_pow_lt_of_lt_one
    (div_pos hgap (show 0 < w ⬝ᵥ x + 1 by linarith)) hl1
  have hi := (lt_div_iff₀ (show 0 < w ⬝ᵥ x + 1 by linarith)).mp hm
  nlinarith [hbound m, pow_nonneg hl m]

theorem observed_ternary_bounded_of_positive_subeigenrow [Nonempty ι]
    (A E : Affine ι) (hA : A.Nonnegative) (hE : E.Nonnegative)
    (hAE : (A.comp E).Weak (E.comp A))
    (r w : Vec ι) (hr : 0 ≤ r) (hw : ∀ i, 0 < w i)
    (l : ℝ) (hl : 0 ≤ l) (hl1 : l < 1)
    (hc : w ᵥ* A.matrix ≤ l • w) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ n : ℕ, r ⬝ᵥ ((eval E)^[n] 0) ≤ K := by
  classical
  let M := max 0 (Finset.univ.sup' Finset.univ_nonempty (fun i => r i / w i)) + 1
  have hM : 0 ≤ M := by dsimp only [M]; positivity
  have hdom : r ≤ M • w := by
    intro i
    have hi : r i / w i ≤ M := by
      have hle := Finset.le_sup' (fun j => r j / w j) (Finset.mem_univ i)
      exact hle.trans ((le_max_right _ _).trans (by
        dsimp only [M]
        exact le_add_of_nonneg_right zero_le_one))
    exact (div_le_iff₀ (hw i)).mp hi
  have hMw : 0 ≤ M • w := fun i => mul_nonneg hM (hw i).le
  have hcontract : (M • w) ᵥ* A.matrix ≤ l • (M • w) := by
    rw [smul_vecMul]
    intro i
    have hi := mul_le_mul_of_nonneg_left (hc i) hM
    change M * (w ᵥ* A.matrix) i ≤ l * (M * w i)
    change M * (w ᵥ* A.matrix) i ≤ M * (l * w i) at hi
    calc
      M * (w ᵥ* A.matrix) i ≤ M * (l * w i) := hi
      _ = l * (M * w i) := by ring
  refine ⟨((M • w) ⬝ᵥ A.offset) / (1 - l), ?_, ?_⟩
  · exact div_nonneg (Finset.sum_nonneg (fun i _ => mul_nonneg (hMw i) (hA.2 i)))
      (sub_pos.mpr hl1).le
  · exact observed_ternary_iterates_bounded A E hA hE hAE r (M • w) hr hMw hdom
      l hl hl1 hcontract

end CollatzResearch.ForwardRealContraction

#print axioms CollatzResearch.ForwardRealContraction.iterate_nonnegative
#print axioms CollatzResearch.ForwardRealContraction.iterate_swap_right
#print axioms CollatzResearch.ForwardRealContraction.iterate_swap
#print axioms CollatzResearch.ForwardRealContraction.weighted_eval_le
#print axioms CollatzResearch.ForwardRealContraction.weighted_iterate_le
#print axioms CollatzResearch.ForwardRealContraction.observed_ternary_iterates_bounded
#print axioms CollatzResearch.ForwardRealContraction.observed_ternary_bounded_of_positive_subeigenrow
