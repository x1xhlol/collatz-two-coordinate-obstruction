import Erdos1135.ND.Fourier.FixedTotalMGF

/-!
# Fixed-Total Bars Upper Prefix-Count Tail

This leaf applies an inclusive finite Markov argument to the checked centered
MGF.  The public event retains its equality boundary, as required by the
order-statistic event in T3.
-/

open scoped BigOperators

namespace Erdos1135
namespace ND

private theorem ndPmfProb_le_of_subset_expectation_le_mul
    {α : Type*} [Fintype α]
    (p : PMF α) (E : Set α) (X : α → ℝ)
    {cutoff budget : ℝ}
    (hX_nonneg : ∀ a, 0 ≤ X a)
    (hcutoff : 0 < cutoff)
    (hE : E ⊆ {a | cutoff ≤ X a})
    (hmean : Tao.pmfExpectation p X ≤ cutoff * budget) :
    Tao.pmfProb p E ≤ budget := by
  classical
  have hcut_prob_le_expect :
      cutoff * Tao.pmfProb p E ≤ Tao.pmfExpectation p X := by
    unfold Tao.pmfProb Tao.pmfExpectation
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro a _ha
    by_cases ha : a ∈ E
    · have hcut : cutoff ≤ X a := hE ha
      have hw : 0 ≤ (p a).toReal := ENNReal.toReal_nonneg
      simpa [ha, mul_comm, mul_left_comm, mul_assoc] using
        (mul_le_mul_of_nonneg_left hcut hw)
    · have hterm : 0 ≤ (p a).toReal * X a :=
        mul_nonneg ENNReal.toReal_nonneg (hX_nonneg a)
      simpa [ha] using hterm
  exact le_of_mul_le_mul_left
    (hcut_prob_le_expect.trans hmean) hcutoff

/-- Inclusive upper tail for the actual fixed-bars prefix count. -/
theorem ndFixedTotalBarsPMF_prefixCount_upperTail_le
    (n L q : ℕ) (hn : 0 < n) (hL : n ≤ L)
    (hqL : q ≤ L - 1) (hq : 0 < q)
    (tau : ℝ) (htau : 0 ≤ tau) :
    Tao.pmfProb (ndFixedTotalBarsPMF n L hn hL)
      {B | tau ≤ (ndBarsPrefixCount B.1 q : ℝ) -
        (q : ℝ) *
          (((n - 1 : ℕ) : ℝ) / ((L - 1 : ℕ) : ℝ))} ≤
      Real.exp (-2 * tau ^ 2 / (q : ℝ)) := by
  have hL1 : 1 < L := by omega
  let rho : ℝ :=
    (((n - 1 : ℕ) : ℝ) / ((L - 1 : ℕ) : ℝ))
  let lambda : ℝ := 4 * tau / (q : ℝ)
  have hqR : 0 < (q : ℝ) := by
    exact_mod_cast hq
  have hlambda : 0 ≤ lambda := by
    dsimp [lambda]
    exact div_nonneg (mul_nonneg (by norm_num) htau) (le_of_lt hqR)
  have hmgf := ndFixedTotalBarsPMF_centered_mgf_le
    n L q hn hL hL1 hqL lambda hlambda
  change
    Tao.pmfProb (ndFixedTotalBarsPMF n L hn hL)
        {B | tau ≤
          (ndBarsPrefixCount B.1 q : ℝ) - (q : ℝ) * rho} ≤
      Real.exp (-2 * tau ^ 2 / (q : ℝ))
  change
    Tao.pmfExpectation (ndFixedTotalBarsPMF n L hn hL)
        (fun B =>
          Real.exp
            (lambda * ((ndBarsPrefixCount B.1 q : ℝ) -
              (q : ℝ) * rho))) ≤
      Real.exp ((q : ℝ) * lambda ^ 2 / 8) at hmgf
  apply ndPmfProb_le_of_subset_expectation_le_mul
    (X := fun B =>
      Real.exp
        (lambda * ((ndBarsPrefixCount B.1 q : ℝ) -
          (q : ℝ) * rho)))
    (cutoff := Real.exp (lambda * tau))
  · intro B
    exact Real.exp_nonneg _
  · exact Real.exp_pos _
  · intro B hB
    apply Real.exp_le_exp.mpr
    exact mul_le_mul_of_nonneg_left hB hlambda
  · calc
      Tao.pmfExpectation (ndFixedTotalBarsPMF n L hn hL)
          (fun B =>
            Real.exp
              (lambda * ((ndBarsPrefixCount B.1 q : ℝ) -
                (q : ℝ) * rho))) ≤
          Real.exp ((q : ℝ) * lambda ^ 2 / 8) := hmgf
      _ = Real.exp (lambda * tau) *
          Real.exp (-2 * tau ^ 2 / (q : ℝ)) := by
        dsimp [lambda]
        rw [← Real.exp_add]
        congr 1
        field_simp [ne_of_gt hqR]
        ring

/-- Inclusive lower tail for the actual fixed-bars prefix count, obtained by
complementing the bar set and applying the upper-tail theorem. -/
theorem ndFixedTotalBarsPMF_prefixCount_lowerTail_le
    (n L q : ℕ) (hn : 0 < n) (hL : n ≤ L)
    (hqL : q ≤ L - 1) (hq : 0 < q)
    (tau : ℝ) (htau : 0 ≤ tau) :
    Tao.pmfProb (ndFixedTotalBarsPMF n L hn hL)
      {B | tau ≤
        (q : ℝ) *
            (((n - 1 : ℕ) : ℝ) / ((L - 1 : ℕ) : ℝ)) -
          (ndBarsPrefixCount B.1 q : ℝ)} ≤
      Real.exp (-2 * tau ^ 2 / (q : ℝ)) := by
  let nc : ℕ := L - n + 1
  have hnc : 0 < nc := by omega
  have hLc : nc ≤ L := by omega
  have hL1 : 1 < L := by omega
  let e : NDFixedTotalBars n L ≃ NDFixedTotalBars nc L :=
    ndFixedTotalBarsComplEquiv n L hn hL
  let lowerEvent : Set (NDFixedTotalBars n L) :=
    {B | tau ≤ (q : ℝ) *
      (((n - 1 : ℕ) : ℝ) / ((L - 1 : ℕ) : ℝ)) -
        (ndBarsPrefixCount B.1 q : ℝ)}
  let upperEvent : Set (NDFixedTotalBars nc L) :=
    {C | tau ≤ (ndBarsPrefixCount C.1 q : ℝ) -
      (q : ℝ) * (((nc - 1 : ℕ) : ℝ) / ((L - 1 : ℕ) : ℝ))}
  have hcenter (B : NDFixedTotalBars n L) :
      (ndBarsPrefixCount (e B).1 q : ℝ) -
          (q : ℝ) * (((nc - 1 : ℕ) : ℝ) / ((L - 1 : ℕ) : ℝ)) =
        (q : ℝ) * (((n - 1 : ℕ) : ℝ) / ((L - 1 : ℕ) : ℝ)) -
          (ndBarsPrefixCount B.1 q : ℝ) := by
    have hcount := ndBarsPrefixCount_add_compl n L q hn hL B
    change ndBarsPrefixCount B.1 q + ndBarsPrefixCount (e B).1 q =
      min (L - 1) q at hcount
    rw [min_eq_right hqL] at hcount
    have hcountR :
        (ndBarsPrefixCount B.1 q : ℝ) +
            (ndBarsPrefixCount (e B).1 q : ℝ) = (q : ℝ) := by
      exact_mod_cast hcount
    have hHc :
        (ndBarsPrefixCount (e B).1 q : ℝ) =
          (q : ℝ) - (ndBarsPrefixCount B.1 q : ℝ) := by
      linarith
    have hpartsNat : (L - n) + (n - 1) = L - 1 := by omega
    have hpartsR :
        ((L - n : ℕ) : ℝ) + ((n - 1 : ℕ) : ℝ) =
          ((L - 1 : ℕ) : ℝ) := by
      exact_mod_cast hpartsNat
    have hdenPos : 0 < ((L - 1 : ℕ) : ℝ) := by
      exact_mod_cast (Nat.sub_pos_of_lt hL1)
    have hden : ((L - 1 : ℕ) : ℝ) ≠ 0 := ne_of_gt hdenPos
    have hpadd :
        ((L - n : ℕ) : ℝ) / ((L - 1 : ℕ) : ℝ) +
            ((n - 1 : ℕ) : ℝ) / ((L - 1 : ℕ) : ℝ) = 1 := by
      rw [← add_div, hpartsR, div_self hden]
    have hpcomp :
        ((L - n : ℕ) : ℝ) / ((L - 1 : ℕ) : ℝ) =
          1 - ((n - 1 : ℕ) : ℝ) / ((L - 1 : ℕ) : ℝ) := by
      linarith
    rw [show nc - 1 = L - n by omega, hHc, hpcomp]
    ring
  have hevent : e ⁻¹' upperEvent = lowerEvent := by
    ext B
    change tau ≤
        (ndBarsPrefixCount (e B).1 q : ℝ) -
          (q : ℝ) * (((nc - 1 : ℕ) : ℝ) / ((L - 1 : ℕ) : ℝ)) ↔
      tau ≤
        (q : ℝ) * (((n - 1 : ℕ) : ℝ) / ((L - 1 : ℕ) : ℝ)) -
          (ndBarsPrefixCount B.1 q : ℝ)
    rw [hcenter B]
  have htail := ndFixedTotalBarsPMF_prefixCount_upperTail_le
    nc L q hnc hLc hqL hq tau htau
  change Tao.pmfProb (ndFixedTotalBarsPMF nc L hnc hLc) upperEvent ≤
    Real.exp (-2 * tau ^ 2 / (q : ℝ)) at htail
  rw [← ndFixedTotalBarsPMF_map_compl n L hn hL,
    Tao.pmfProb_map_preimage, hevent] at htail
  exact htail

end ND
end Erdos1135
