import CountableLabelLawCorollaries

open Filter
open scoped Topology BigOperators ENNReal lp

namespace CollatzCanonical.LabelLaw
open CollatzCanonical.BanachWindow
variable {I : Type*}

theorem label_pow_two_eq_of_halving (F : ℕ → I)
    (hhalf : ∀ q : ℕ, 0 < q → F (2 * q) = F q) {q : ℕ} (hq : 0 < q) (a : ℕ) :
    F (2 ^ a * q) = F q := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [pow_succ, show 2 ^ a * 2 * q = 2 * (2 ^ a * q) by ring,
      hhalf _ (by positivity)]
    exact ih

theorem oddPartLabel_eq_of_halving (F : ℕ → I)
    (hhalf : ∀ q : ℕ, 0 < q → F (2 * q) = F q) {q : ℕ} (hq : 0 < q) :
    oddPartLabel F q = F q := by
  have h := label_pow_two_eq_of_halving F hhalf (Nat.ordCompl_pos 2 hq.ne')
    (q.factorization 2)
  rw [Nat.ordProj_mul_ordCompl_eq_self] at h
  exact h.symm

theorem fullLabelLaw_eq_of_halving (F : ℕ → I)
    (hhalf : ∀ q : ℕ, 0 < q → F (2 * q) = F q) (t : ℝ) :
    fullLabelLaw (oddPartLabel F) t = fullLabelLaw F t := by
  unfold fullLabelLaw
  congr 1
  apply fullVectorCumulative_congr_positive
  intro q hq
  exact congrArg labelAtom (oddPartLabel_eq_of_halving F hhalf hq)

theorem actual_halving_invariant_label_law (F : ℕ → I)
    (hpass : EventuallyLabelPassageInvariant F)
    (hhalf : ∀ q : ℕ, 0 < q → F (2 * q) = F q) :
    ∃ p : LabelVector I, IsProbabilityVector p ∧
      Tendsto (oddLabelLaw F) atTop (𝓝 p) ∧ Tendsto (fullLabelLaw F) atTop (𝓝 p) := by
  obtain ⟨p, hp, ho, hf⟩ := actual_odd_and_all_start_label_law F hpass
  have he : fullLabelLaw (oddPartLabel F) = fullLabelLaw F :=
    funext (fullLabelLaw_eq_of_halving F hhalf)
  rw [he] at hf
  exact ⟨p, hp, ho, hf⟩

end CollatzCanonical.LabelLaw

#print axioms CollatzCanonical.LabelLaw.oddPartLabel_eq_of_halving
#print axioms CollatzCanonical.LabelLaw.actual_halving_invariant_label_law
