/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Section6.ConductorDFT

namespace Erdos1135Predecessor

namespace Tao

theorem taoSection6_conductor_add_eq_tail_and_positive
    {n m k T j r : ℕ}
    (htail : k + 1 + T = n) (hconductor : j + r = T)
    (hhead : k + 1 ≤ m) (hfrequency : j < n - m) :
    r + j = T ∧ 1 ≤ r := by
  omega

theorem taoSection6_m_sub_k_le_conductor
    {n m k T j r : ℕ}
    (htail : k + 1 + T = n) (hconductor : j + r = T)
    (hhead : k + 1 ≤ m) (hfrequency : j < n - m) :
    m - k ≤ r := by
  omega

theorem taoSection6_head_add_frequency_add_conductor_eq
    {n k T j r : ℕ}
    (htail : k + 1 + T = n) (hconductor : j + r = T) :
    k + j + 1 + r = n := by
  omega

theorem taoSection6_n_le_twenty_mul_m_sub_k
    {n m k : ℕ} (hhead : k + 1 ≤ m)
    (hm : 9 * n ≤ 10 * m) (hk : 20 * k ≤ 17 * n) :
    n ≤ 20 * (m - k) := by
  omega

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

end Erdos1135Predecessor
