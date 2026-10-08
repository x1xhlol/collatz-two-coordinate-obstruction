/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Section6.ConductorDFT

/-!
# Section 6 Conductor Index Arithmetic

This leaf packages the subtraction-free natural-number arithmetic used when
Tao's stopped tail has length `T = r + j`.  The structural hypotheses identify
the tail and its conductor; the two coarse linear bounds record the numerical
separation needed to compare decay in `r` with decay in the ambient level `n`.

No stopping event, frequency factorization, or Fourier estimate is proved here.
-/

namespace Erdos1135SecondScale
namespace Tao

/-- The additive conductor convention expected by `ConductorDFT`, together
with positivity of the reduced level. -/
theorem taoSection6_conductor_add_eq_tail_and_positive
    {n m k T j r : ℕ}
    (htail : k + 1 + T = n) (hconductor : j + r = T)
    (hhead : k + 1 ≤ m) (hfrequency : j < n - m) :
    r + j = T ∧ 1 ≤ r := by
  omega

/-- A frequency excluded from the level-`m` fiber average leaves at least
`m-k` digits in the reduced conductor. -/
theorem taoSection6_m_sub_k_le_conductor
    {n m k T j r : ℕ}
    (htail : k + 1 + T = n) (hconductor : j + r = T)
    (hhead : k + 1 ≤ m) (hfrequency : j < n - m) :
    m - k ≤ r := by
  omega

/-- Combined source indexing for a stopped head of length `k+1`, a discarded
frequency valuation `j`, and a reduced conductor `r`. -/
theorem taoSection6_head_add_frequency_add_conductor_eq
    {n k T j r : ℕ}
    (htail : k + 1 + T = n) (hconductor : j + r = T) :
    k + j + 1 + r = n := by
  omega

/-- The coarse source-regime bounds `m ≥ 0.9n` and `k ≤ 0.85n` leave a gap
of at least `n/20` between `m` and `k`. -/
theorem taoSection6_n_le_twenty_mul_m_sub_k
    {n m k : ℕ} (hhead : k + 1 ≤ m)
    (hm : 9 * n ≤ 10 * m) (hk : 20 * k ≤ 17 * n) :
    n ≤ 20 * (m - k) := by
  omega

/-- Complete additive conductor-index packet for the later stopped-tail decay
consumer.  In particular, the checked primitive estimate at level `r` is
available and `r` is at least a fixed positive fraction of `n`. -/
theorem taoSection6_conductor_index_bounds
    {n m k T j r : ℕ}
    (htail : k + 1 + T = n) (hconductor : j + r = T)
    (hhead : k + 1 ≤ m) (hfrequency : j < n - m)
    (hm : 9 * n ≤ 10 * m) (hk : 20 * k ≤ 17 * n) :
    r + j = T ∧
      1 ≤ r ∧
      m - k ≤ r ∧
      n ≤ 20 * (m - k) ∧
      n ≤ 20 * r := by
  have hadd_pos :=
    taoSection6_conductor_add_eq_tail_and_positive
      htail hconductor hhead hfrequency
  have hmkr :=
    taoSection6_m_sub_k_le_conductor
      htail hconductor hhead hfrequency
  have hnmk := taoSection6_n_le_twenty_mul_m_sub_k hhead hm hk
  omega

end Tao
end Erdos1135SecondScale
