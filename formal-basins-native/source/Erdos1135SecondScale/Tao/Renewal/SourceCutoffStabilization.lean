/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Renewal.SourceActualQ

/-!
# Section 7 Source Cutoff Stabilization

This leaf proves that terminal-one approximants are eventually constant once
their horizontal horizon reaches the source cutoff. It then identifies that
constant value with the actual-Q finite limit.
-/

namespace Erdos1135SecondScale
namespace Tao

open scoped Topology

private theorem taoSection7HoldExpectationFull_one :
    taoSection7HoldExpectationFull
        (fun _h : TaoSection7RenewalPoint => (1 : ℝ)) = 1 := by
  unfold taoSection7HoldExpectationFull
  simpa using taoSection7HoldPMF_tsum_toReal

theorem taoSection7SourceActualW_false_of_cutoff_lt
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    {p : TaoSection7RenewalPoint}
    (hp : n / 2 < (p.j : ℕ)) :
    ¬ taoSection7SourceActualW n xi epsilon p := by
  unfold taoSection7SourceActualW taoSection7SourceWhiteRenewal
  exact taoSection7SourceWhiteWCutoff_false_of_lt hp

theorem taoSection7QFiniteTerminalOneApprox_source_eq_one_of_cutoff_lt
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (K : ℕ)
    (p : TaoSection7RenewalPoint)
    (hp : n / 2 < (p.j : ℕ)) :
    taoSection7QFiniteTerminalOneApprox K epsilon
        (taoSection7SourceActualW n xi epsilon) p = 1 := by
  induction K generalizing p with
  | zero =>
      rw [taoSection7QFiniteTerminalOneApprox_zero]
      simp [taoSection7QWhiteFactor,
        taoSection7SourceActualW_false_of_cutoff_lt hp]
  | succ K ih =>
      rw [taoSection7QFiniteTerminalOneApprox_succ hepsilon]
      have hfactor :
          taoSection7QWhiteFactor epsilon
              (taoSection7SourceActualW n xi epsilon) p = 1 := by
        simp [taoSection7QWhiteFactor,
          taoSection7SourceActualW_false_of_cutoff_lt hp]
      rw [hfactor]
      have hnext :
          (fun h : TaoSection7RenewalPoint =>
              taoSection7QFiniteTerminalOneApprox K epsilon
                (taoSection7SourceActualW n xi epsilon) (p + h)) =
            fun _h => 1 := by
        funext h
        apply ih
        have hj :
            (p.j : ℕ) < ((p + h).j : ℕ) := by
          simp [PNat.add_coe]
        omega
      rw [hnext, taoSection7HoldExpectationFull_one]
      norm_num

theorem taoSection7QFiniteTerminalOneApprox_source_add_eq_left_of_le
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon) (K D : ℕ)
    (p : TaoSection7RenewalPoint)
    (horizon : n / 2 ≤ (p.j : ℕ) + K) :
    taoSection7QFiniteTerminalOneApprox (K + D) epsilon
        (taoSection7SourceActualW n xi epsilon) p =
      taoSection7QFiniteTerminalOneApprox K epsilon
        (taoSection7SourceActualW n xi epsilon) p := by
  induction K generalizing p with
  | zero =>
      cases D with
      | zero => simp
      | succ D =>
          rw [Nat.zero_add,
            taoSection7QFiniteTerminalOneApprox_succ hepsilon,
            taoSection7QFiniteTerminalOneApprox_zero]
          have hnext :
              (fun h : TaoSection7RenewalPoint =>
                  taoSection7QFiniteTerminalOneApprox D epsilon
                    (taoSection7SourceActualW n xi epsilon) (p + h)) =
                fun _h => 1 := by
            funext h
            apply taoSection7QFiniteTerminalOneApprox_source_eq_one_of_cutoff_lt
              hepsilon
            have hj : (p.j : ℕ) < ((p + h).j : ℕ) := by
              simp [PNat.add_coe]
            omega
          rw [hnext, taoSection7HoldExpectationFull_one]
          ring
  | succ K ih =>
      have hindex : K + 1 + D = (K + D) + 1 := by omega
      rw [hindex,
        taoSection7QFiniteTerminalOneApprox_succ hepsilon,
        taoSection7QFiniteTerminalOneApprox_succ hepsilon]
      congr 1
      unfold taoSection7HoldExpectationFull
      apply tsum_congr
      intro h
      congr 1
      apply ih
      have hj : (p.j : ℕ) < ((p + h).j : ℕ) := by
        simp [PNat.add_coe]
      omega

/-- Once the terminal-one depth reaches the inclusive source cutoff horizon,
the finite approximant is already the actual-Q limit. -/
theorem taoSection7SourceActualQ_eq_terminalOneApprox_of_le
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (p : TaoSection7RenewalPoint) (K : ℕ)
    (horizon : n / 2 ≤ (p.j : ℕ) + K) :
    taoSection7SourceActualQ n xi epsilon p =
      taoSection7QFiniteTerminalOneApprox K epsilon
        (taoSection7SourceActualW n xi epsilon) p := by
  have hconst :
      Filter.Tendsto
        (fun L : ℕ =>
          taoSection7QFiniteTerminalOneApprox L epsilon
            (taoSection7SourceActualW n xi epsilon) p)
        Filter.atTop
        (𝓝 (taoSection7QFiniteTerminalOneApprox K epsilon
          (taoSection7SourceActualW n xi epsilon) p)) :=
    tendsto_atTop_of_eventually_const (i₀ := K) fun L hKL => by
      obtain ⟨D, rfl⟩ := Nat.exists_eq_add_of_le hKL
      exact taoSection7QFiniteTerminalOneApprox_source_add_eq_left_of_le
        (xi := xi) hepsilon K D p horizon
  exact tendsto_nhds_unique
    (taoSection7SourceActualQ_finiteLimit hepsilon p) hconst

/-- A renewal point already strictly beyond the source cutoff has actual-Q
value one. -/
theorem taoSection7SourceActualQ_eq_one_of_cutoff_lt
    {n : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 ≤ epsilon)
    (p : TaoSection7RenewalPoint)
    (hp : n / 2 < (p.j : ℕ)) :
    taoSection7SourceActualQ n xi epsilon p = 1 := by
  rw [taoSection7SourceActualQ_eq_terminalOneApprox_of_le
      hepsilon p 0 (by omega),
    taoSection7QFiniteTerminalOneApprox_zero]
  simp [taoSection7QWhiteFactor,
    taoSection7SourceActualW_false_of_cutoff_lt hp]

end Tao
end Erdos1135SecondScale
