import CollatzReversedRealContraction

namespace CollatzResearch.RealContraction

open Matrix CollatzCertificate

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem nonnegative_matrix_power_mulVec (B : Mat ι) (hB : EntrywiseLE 0 B)
    (v : Vec ι) (hv : 0 ≤ v) (k : ℕ) : 0 ≤ B ^ k *ᵥ v := by
  induction k with
  | zero => simpa using hv
  | succ k ih =>
    rw [pow_succ', ← mulVec_mulVec]
    intro i
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (hB i j) (ih j))

theorem matrix_power_sum_telescopes (B : Mat ι) (v : Vec ι) (k : ℕ) :
    B *ᵥ (∑ j ∈ Finset.range k, B ^ j *ᵥ v) + v =
      (∑ j ∈ Finset.range k, B ^ j *ᵥ v) + B ^ k *ᵥ v := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mulVec_add, mulVec_mulVec, ← pow_succ']
    ext i
    have hi := congrFun ih i
    simp only [Pi.add_apply] at hi ⊢
    linarith

theorem positive_contraction_of_matrix_power
    (B : Mat ι) (hB : EntrywiseLE 0 B) (v : Vec ι) (hv : ∀ i, 0 < v i)
    (k : ℕ) (hk : 0 < k) (hc : ∀ i, (B ^ k *ᵥ v) i < v i) :
    ∃ w : Vec ι, (∀ i, 0 < w i) ∧ ∀ i, (B *ᵥ w) i < w i := by
  let w : Vec ι := ∑ j ∈ Finset.range k, B ^ j *ᵥ v
  have hle (i : ι) : v i ≤ w i := by
    change v i ≤ (∑ j ∈ Finset.range k, B ^ j *ᵥ v) i
    rw [Finset.sum_apply]
    calc
      v i = (B ^ 0 *ᵥ v) i := by simp
      _ ≤ ∑ j ∈ Finset.range k, (B ^ j *ᵥ v) i :=
        Finset.single_le_sum (fun j _ => nonnegative_matrix_power_mulVec B hB v
          (fun i => (hv i).le) j i) (Finset.mem_range.mpr hk)
  refine ⟨w, fun i => (hv i).trans_le (hle i), ?_⟩
  intro i
  have hi := congrFun (matrix_power_sum_telescopes B v k) i
  change (B *ᵥ w) i + v i = w i + (B ^ k *ᵥ v) i at hi
  linarith [hc i]

theorem reversed_real_excludes_positive_power_contraction
    (A B C D E F G : Affine ι) (i₀ : ι)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀)
    (v : Vec ι) (hv : ∀ i, 0 < v i) (k : ℕ) (hk : 0 < k) :
    ∃ i, v i ≤ (B.matrix ^ k *ᵥ v) i := by
  by_contra hn
  have hc : ∀ i, (B.matrix ^ k *ᵥ v) i < v i := by
    intro i
    by_contra hi
    exact hn ⟨i, le_of_not_gt hi⟩
  obtain ⟨w, hw, hBw⟩ := positive_contraction_of_matrix_power B.matrix hB.1 v hv k hk hc
  obtain ⟨i, hi⟩ := reversed_real_excludes_positive_contraction A B C D E F G i₀
    hA hB hC hD hE hF hG h hstrict w hw
  exact not_lt_of_ge hi (hBw i)

theorem reversed_real_second_binary_power_row_sum_bound
    (A B C D E F G : Affine ι) (i₀ : ι)
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hD : D.Nonnegative) (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (hstrict : D.offset i₀ < (D.comp A).offset i₀ ∨
      (D.comp G).offset i₀ < (D.comp B).offset i₀) (k : ℕ) (hk : 0 < k) :
    ∃ i, 1 ≤ ∑ j, (B.matrix ^ k) i j := by
  obtain ⟨i, hi⟩ := reversed_real_excludes_positive_power_contraction A B C D E F G i₀
    hA hB hC hD hE hF hG h hstrict (fun _ => 1) (fun _ => zero_lt_one) k hk
  exact ⟨i, by simpa only [mulVec, dotProduct, mul_one] using hi⟩

#print axioms nonnegative_matrix_power_mulVec
#print axioms matrix_power_sum_telescopes
#print axioms positive_contraction_of_matrix_power
#print axioms reversed_real_excludes_positive_power_contraction
#print axioms reversed_real_second_binary_power_row_sum_bound

end CollatzResearch.RealContraction
