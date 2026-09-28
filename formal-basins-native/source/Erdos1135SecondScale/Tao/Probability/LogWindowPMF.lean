/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Probability.Finite
import Erdos1135SecondScale.Tao.Probability.LogWindow

/-!
# Finite Logarithmic Window PMFs

This module packages the finite logarithmic source-window real ratios from
`Probability.LogWindow` as PMFs on finite subtype supports.  It keeps concrete
Tao `N_y` endpoint conventions and first-passage laws out of the probability
wrapper.
-/

namespace Erdos1135SecondScale
namespace Tao

open scoped BigOperators

/-- Finite logarithmic PMF on the subtype supported by a positive-mass finite set. -/
noncomputable def logFinsetPMF (S : Finset ℕ)
    (hmass : 0 < logFinsetMass S) : PMF {n : ℕ // n ∈ S} :=
  PMF.ofFintype
    (fun n : {n : ℕ // n ∈ S} =>
      ENNReal.ofReal (logNatWeight n.1 / logFinsetMass S))
    (by
      classical
      rw [← ENNReal.ofReal_sum_of_nonneg]
      · have hsum :
            (∑ n ∈ S.attach, logNatWeight (n : ℕ)) =
              logFinsetMass S := by
          unfold logFinsetMass
          exact Finset.sum_attach S (fun n => logNatWeight n)
        have hsum_div :
            (∑ n ∈ S.attach,
              logNatWeight (n : ℕ) / logFinsetMass S) = 1 := by
          rw [← Finset.sum_div, hsum]
          exact div_self hmass.ne'
        have hsum_div_univ :
            (∑ n : {n : ℕ // n ∈ S},
              logNatWeight n.1 / logFinsetMass S) = 1 := by
          rw [show (Finset.univ : Finset {n : ℕ // n ∈ S}) = S.attach by
            exact Finset.univ_eq_attach S]
          exact hsum_div
        rw [hsum_div_univ]
        norm_num
      · intro n _hn
        exact div_nonneg (logNatWeight_nonneg n.1) hmass.le)

theorem logFinsetPMF_apply_toReal {S : Finset ℕ}
    (hmass : 0 < logFinsetMass S) (n : {n : ℕ // n ∈ S}) :
    (logFinsetPMF S hmass n).toReal =
      logNatWeight n.1 / logFinsetMass S := by
  rw [logFinsetPMF, PMF.ofFintype_apply]
  exact ENNReal.toReal_ofReal
    (div_nonneg (logNatWeight_nonneg n.1) hmass.le)

theorem pmfProb_logFinsetPMF (S : Finset ℕ)
    (hmass : 0 < logFinsetMass S) (E : Set ℕ) :
    pmfProb (logFinsetPMF S hmass)
      {x : {n : ℕ // n ∈ S} | (x : ℕ) ∈ E} =
        logFinsetProb S E := by
  classical
  unfold pmfProb logFinsetProb
  simp only [Set.mem_setOf_eq]
  have hattach :
      (∑ x : {n : ℕ // n ∈ S},
        if (x : ℕ) ∈ E then (logFinsetPMF S hmass x).toReal else 0) =
      ∑ n ∈ S, if n ∈ E then
        logNatWeight n / logFinsetMass S else 0 := by
    rw [show (Finset.univ : Finset {n : ℕ // n ∈ S}) = S.attach by
      exact Finset.univ_eq_attach S]
    simpa [logFinsetPMF_apply_toReal hmass] using
      (Finset.sum_attach S
        (fun n => if n ∈ E then logNatWeight n / logFinsetMass S else 0))
  calc
    (∑ x : {n : ℕ // n ∈ S},
      if (x : ℕ) ∈ E then (logFinsetPMF S hmass x).toReal else 0)
        = ∑ n ∈ S, if n ∈ E then
            logNatWeight n / logFinsetMass S else 0 := hattach
    _ = (∑ n ∈ S.filter (fun n => n ∈ E), logNatWeight n) /
          logFinsetMass S := by
        rw [Finset.sum_filter, Finset.sum_div]
        exact Finset.sum_congr rfl fun n _hn => by
          by_cases hnE : n ∈ E
          · simp [hnE]
          · simp [hnE]

theorem logFinsetMass_oddLogWindow_pos_of_mem {lo hi n : ℕ}
    (hn : n ∈ oddLogWindow lo hi) :
    0 < logFinsetMass (oddLogWindow lo hi) := by
  have hnpos : 0 < n := by
    cases n with
    | zero =>
        simp [oddLogWindow] at hn
    | succ n =>
        exact Nat.succ_pos n
  exact logFinsetMass_pos_of_mem_pos hn hnpos

/-- Finite logarithmic PMF on an inclusive odd window. -/
noncomputable def oddLogWindowPMF (lo hi : ℕ)
    (hmass : 0 < logFinsetMass (oddLogWindow lo hi)) :
    PMF {n : ℕ // n ∈ oddLogWindow lo hi} :=
  logFinsetPMF (oddLogWindow lo hi) hmass

theorem oddLogWindowPMF_apply_toReal {lo hi : ℕ}
    (hmass : 0 < logFinsetMass (oddLogWindow lo hi))
    (n : {n : ℕ // n ∈ oddLogWindow lo hi}) :
    (oddLogWindowPMF lo hi hmass n).toReal =
      logNatWeight n.1 / logFinsetMass (oddLogWindow lo hi) :=
  logFinsetPMF_apply_toReal hmass n

theorem pmfProb_oddLogWindowPMF (lo hi : ℕ)
    (hmass : 0 < logFinsetMass (oddLogWindow lo hi)) (E : Set ℕ) :
    pmfProb (oddLogWindowPMF lo hi hmass)
      {x : {n : ℕ // n ∈ oddLogWindow lo hi} | (x : ℕ) ∈ E} =
        logFinsetProb (oddLogWindow lo hi) E :=
  pmfProb_logFinsetPMF (oddLogWindow lo hi) hmass E

end Tao
end Erdos1135SecondScale
