/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Renewal.Prop78Case3Event

namespace Erdos1135Predecessor

namespace Tao

open scoped BigOperators

noncomputable section

structure TaoSection7Lemma710Constants where
  C710 : ℝ
  c710 : ℝ
  C710_nonneg : 0 ≤ C710
  c710_pos : 0 < c710

structure TaoSection7Case3BaseKcutAdmissibilitySchedule
    (allowed : Finset ℕ) (base m Kcut : ℕ) : Prop where
  base_ge_four : 4 ≤ base
  p_range :
    ∀ p, p ∈ allowed →
      (p : ℝ) ≤ Real.rpow (m : ℝ) ((1 : ℝ) / 10)
  bound_pos :
    ∀ p, p ∈ allowed →
      1 ≤ taoSection7Case3LargeTriangleBoundWithBase (base : ℝ) Kcut p
  bound_le_m :
    ∀ p, p ∈ allowed →
      taoSection7Case3LargeTriangleBoundWithBase (base : ℝ) Kcut p ≤
        Real.rpow (m : ℝ) ((2 : ℝ) / 5)

theorem TaoSection7Case3BaseKcutAdmissibilitySchedule.admissible
    {allowed : Finset ℕ} {base m Kcut p : ℕ}
    (h : TaoSection7Case3BaseKcutAdmissibilitySchedule allowed base m Kcut)
    (hp : p ∈ allowed) :
    TaoSection7Case3EStarUsedOffsetAdmissible m p
      (taoSection7Case3LargeTriangleBoundWithBase (base : ℝ) Kcut p) :=
  ⟨h.p_range p hp, h.bound_pos p hp, h.bound_le_m p hp⟩

theorem taoSection7Case3LargeTriangleBoundWithBase_mono_p
    {base : ℝ} (hbase : 0 ≤ base) (Kcut : ℕ) :
    Monotone (taoSection7Case3LargeTriangleBoundWithBase base Kcut) := by
  intro p q hpq
  dsimp [taoSection7Case3LargeTriangleBoundWithBase]
  gcongr

theorem taoSection7Case3LargeTriangleBoundWithBase_one_le
    {base : ℕ} (hbase : 1 ≤ base) (Kcut p : ℕ) :
    1 ≤ taoSection7Case3LargeTriangleBoundWithBase (base : ℝ) Kcut p := by
  dsimp [taoSection7Case3LargeTriangleBoundWithBase]
  have hbase_real : (1 : ℝ) ≤ (base : ℝ) := by
    exact_mod_cast hbase
  have hpow : (1 : ℝ) ≤ (base : ℝ) ^ Kcut := one_le_pow₀ hbase_real
  have hp_nonneg : 0 ≤ (p : ℝ) := by
    exact_mod_cast Nat.zero_le p
  have honep : (1 : ℝ) ≤ 1 + (p : ℝ) := by
    nlinarith
  have hcube : (1 : ℝ) ≤ (1 + (p : ℝ)) ^ 3 := one_le_pow₀ honep
  have hpow_nonneg : 0 ≤ (base : ℝ) ^ Kcut := le_trans zero_le_one hpow
  have hmul :
      (1 : ℝ) * 1 ≤ (base : ℝ) ^ Kcut * (1 + (p : ℝ)) ^ 3 :=
    mul_le_mul hpow hcube zero_le_one hpow_nonneg
  simpa using hmul

structure TaoSection7Case3BaseKcutAllowedCapAdmissibility
    (allowed : Finset ℕ) (base m Kcut Pmax : ℕ) : Prop where
  base_ge_four : 4 ≤ base
  allowed_le_Pmax : ∀ p, p ∈ allowed → p ≤ Pmax
  Pmax_range :
    (Pmax : ℝ) ≤ Real.rpow (m : ℝ) ((1 : ℝ) / 10)
  bound_le_m_at_Pmax :
    taoSection7Case3LargeTriangleBoundWithBase (base : ℝ) Kcut Pmax ≤
      Real.rpow (m : ℝ) ((2 : ℝ) / 5)

theorem TaoSection7Case3BaseKcutAllowedCapAdmissibility.to_admissibilitySchedule
    {allowed : Finset ℕ} {base m Kcut Pmax : ℕ}
    (h :
      TaoSection7Case3BaseKcutAllowedCapAdmissibility
        allowed base m Kcut Pmax) :
    TaoSection7Case3BaseKcutAdmissibilitySchedule allowed base m Kcut where
  base_ge_four := h.base_ge_four
  p_range := by
    intro p hp
    have hp_le_Pmax : (p : ℝ) ≤ (Pmax : ℝ) := by
      exact_mod_cast h.allowed_le_Pmax p hp
    exact hp_le_Pmax.trans h.Pmax_range
  bound_pos := by
    intro p _hp
    have hbase_one : 1 ≤ base :=
      le_trans (by norm_num : 1 ≤ 4) h.base_ge_four
    exact
      taoSection7Case3LargeTriangleBoundWithBase_one_le
        (base := base) hbase_one Kcut p
  bound_le_m := by
    intro p hp
    have hbase_nonneg : 0 ≤ (base : ℝ) := by
      exact_mod_cast Nat.zero_le base
    exact
      ((taoSection7Case3LargeTriangleBoundWithBase_mono_p
          (base := (base : ℝ)) hbase_nonneg Kcut)
        (h.allowed_le_Pmax p hp)).trans h.bound_le_m_at_Pmax

end

end Tao

end Erdos1135Predecessor
