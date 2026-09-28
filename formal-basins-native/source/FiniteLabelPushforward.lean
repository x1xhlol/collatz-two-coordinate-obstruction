import SyracuseLabelInvariance

set_option autoImplicit false
open Filter
open scoped Topology BigOperators ENNReal lp

namespace CollatzCanonical.LabelLaw
open CollatzCanonical.BanachWindow CollatzCanonical.DirichletAbelian

theorem oddLabelLaw_coordinate {I : Type*} [DecidableEq I] (F : ℕ → I) (t : ℝ) (i : I) :
    oddLabelLaw F t i = (oddLogarithmicCumulative (fun _ => 1) t)⁻¹ *
      ∑ n ∈ Finset.range ⌊Real.exp t⌋₊,
        if (n + 1) % 2 = 1 then (1 / (n + 1 : ℕ) : ℝ) *
          (if F (n + 1) = i then 1 else 0) else 0 := by
  classical
  unfold oddLabelLaw oddVectorCumulative
  rw [lp.coeFn_smul, Pi.smul_apply, smul_eq_mul, lp.coeFn_sum, Finset.sum_apply]
  congr 1
  apply Finset.sum_congr rfl
  intro n _
  by_cases hn : (n + 1) % 2 = 1
  · simp only [oddVectorTerm, if_pos hn, Function.comp_apply, lp.coeFn_smul,
      Pi.smul_apply, smul_eq_mul]
    congr 1
    by_cases hi : F (n + 1) = i
    · rw [hi]
      simp [labelAtom]
    · simp [labelAtom, hi, Ne.symm hi]
  · simp only [oddVectorTerm, if_neg hn, lp.coeFn_zero, Pi.zero_apply]

theorem odd_label_law_finite_pushforward {I J : Type*} [Fintype I] [DecidableEq J]
    (F : ℕ → I) (φ : I → J) (t : ℝ) (j : J) :
    oddLabelLaw (φ ∘ F) t j = ∑ i, if φ i = j then oddLabelLaw F t i else 0 := by
  classical
  have hfiber (k : I) (c : ℝ) :
      (∑ i, if φ i = j then c * (if k = i then (1 : ℝ) else 0) else 0) =
        c * (if φ k = j then 1 else 0) := by
    calc
      _ = ∑ i, if i = k then (if φ k = j then c else 0) else 0 := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : i = k
        · subst i; simp
        · simp [hi, Ne.symm hi]
      _ = _ := by simp [mul_ite]
  simp_rw [oddLabelLaw_coordinate]
  symm
  calc
    _ = (oddLogarithmicCumulative (fun _ => 1) t)⁻¹ *
        ∑ i, ∑ n ∈ Finset.range ⌊Real.exp t⌋₊,
          if φ i = j then
            (if (n + 1) % 2 = 1 then (1 / (n + 1 : ℕ) : ℝ) *
              (if F (n + 1) = i then 1 else 0) else 0) else 0 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      by_cases hi : φ i = j <;> simp [hi]
    _ = _ := by
      rw [Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro n _
      by_cases hn : (n + 1) % 2 = 1
      · simp only [if_pos hn, Function.comp_apply]
        exact hfiber (F (n + 1)) _
      · simp only [if_neg hn, ite_self, Finset.sum_const_zero]

theorem finite_label_probability_pushforward {I J : Type*} [Fintype I]
    (F : ℕ → I) (φ : I → J) (p : LabelVector I) (q : LabelVector J)
    (hp : IsProbabilityVector p) (hq : IsProbabilityVector q)
    (hlimp : Tendsto (oddLabelLaw F) atTop (𝓝 p))
    (hlimq : Tendsto (oddLabelLaw (φ ∘ F)) atTop (𝓝 q)) :
    (probabilityVectorPMF p hp).map φ = probabilityVectorPMF q hq := by
  classical
  symm
  apply Erdos1135.Tao.pmf_eq_map_of_fiber_prob_toReal
  intro j
  rw [probabilityVectorPMF_toReal]
  have hcoord := ((lp.evalCLM ℝ (fun _ : J => ℝ) 1 j).continuous.tendsto q).comp hlimq
  change Tendsto (fun t => oddLabelLaw (φ ∘ F) t j) atTop (𝓝 (q j)) at hcoord
  have hsum : Tendsto (fun t => ∑ i, if φ i = j then oddLabelLaw F t i else 0)
      atTop (𝓝 (∑ i, if φ i = j then p i else 0)) := by
    apply tendsto_finset_sum
    intro i _
    by_cases hi : φ i = j
    · simp only [if_pos hi]
      exact ((lp.evalCLM ℝ (fun _ : I => ℝ) 1 i).continuous.tendsto p).comp hlimp
    · simp only [if_neg hi]
      exact tendsto_const_nhds
  have he : q j = ∑ i, if φ i = j then p i else 0 :=
    tendsto_nhds_unique hcoord (by simpa only [odd_label_law_finite_pushforward] using hsum)
  rw [he]
  simp only [Erdos1135.Tao.pmfProb, Set.mem_setOf_eq, probabilityVectorPMF_toReal]

#print axioms finite_label_probability_pushforward

end CollatzCanonical.LabelLaw
