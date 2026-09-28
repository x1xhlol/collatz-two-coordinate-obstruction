import Erdos1135.Tao.Renewal.Prop78Case1Scalar

/-!
# Outer (7.54) Horizontal Factor

Lightweight ownership for the large-horizontal event and denominator factor
used in Tao's outer Case 3 split.
-/

namespace Erdos1135
namespace Tao

noncomputable section

/-- Large-horizontal event for the outer `(7.54)` split, avoiding decimals. -/
def taoSection7Case3Outer754LargeHorizontalEvent
    {Omega : Type*} (Jtot : Omega -> ℕ) (m : ℕ) : Set Omega :=
  {omega | 9 * m <= 10 * Jtot omega}

/-- Horizontal denominator factor in Tao's outer `(7.54)` weight. -/
noncomputable def taoSection7Case3Outer754HorizontalScalar
    (A m Jtot : ℕ) : ℝ :=
  (((max (1 - (Jtot : ℝ) / (m : ℝ)) ((m : ℝ)⁻¹)) ^ A)⁻¹)

/-- Sample-indexed form of the outer `(7.54)` horizontal scalar. -/
noncomputable def taoSection7Case3Outer754HorizontalFactor
    {Omega : Type*} (A m : ℕ) (Jtot : Omega -> ℕ) : Omega -> ℝ :=
  fun omega => taoSection7Case3Outer754HorizontalScalar A m (Jtot omega)

theorem taoSection7Case3Outer754HorizontalFactor_nonneg
    {Omega : Type*} {A m : ℕ} {Jtot : Omega -> ℕ} :
    ∀ omega : Omega,
      0 <= taoSection7Case3Outer754HorizontalFactor A m Jtot omega := by
  intro omega
  unfold taoSection7Case3Outer754HorizontalFactor
    taoSection7Case3Outer754HorizontalScalar
  positivity

theorem taoSection7Case3Outer754HorizontalFactor_le_m_pow
    {Omega : Type*} {A m : ℕ} {Jtot : Omega -> ℕ}
    (hm : 1 <= m) :
    ∀ omega : Omega,
      taoSection7Case3Outer754HorizontalFactor A m Jtot omega <=
        (m : ℝ) ^ A := by
  intro omega
  unfold taoSection7Case3Outer754HorizontalFactor
    taoSection7Case3Outer754HorizontalScalar
  let x : ℝ := max (1 - (Jtot omega : ℝ) / (m : ℝ)) ((m : ℝ)⁻¹)
  have hmpos_nat : 0 < m := lt_of_lt_of_le Nat.zero_lt_one hm
  have hmpos : 0 < (m : ℝ) := Nat.cast_pos.mpr hmpos_nat
  have hminv_pos : 0 < ((m : ℝ)⁻¹) := inv_pos.mpr hmpos
  have hbase_lb : ((m : ℝ)⁻¹) <= x := by
    dsimp [x]
    exact le_max_right _ _
  have hbase_pos : 0 < x := lt_of_lt_of_le hminv_pos hbase_lb
  have hinv_le : x⁻¹ <= (m : ℝ) := by
    have h := (inv_le_inv₀ hbase_pos hminv_pos).mpr hbase_lb
    simpa using h
  have hinv_nonneg : 0 <= x⁻¹ := inv_nonneg.mpr (le_of_lt hbase_pos)
  calc
    (x ^ A)⁻¹ = x⁻¹ ^ A := by rw [inv_pow]
    _ <= (m : ℝ) ^ A := pow_le_pow_left₀ hinv_nonneg hinv_le A

theorem taoSection7Case3Outer754HorizontalFactor_le_ten_pow_of_not_largeHorizontal
    {Omega : Type*} {A m : ℕ} {Jtot : Omega -> ℕ}
    (hm : 1 <= m) :
    ∀ omega : Omega,
      omega ∉ taoSection7Case3Outer754LargeHorizontalEvent Jtot m ->
        taoSection7Case3Outer754HorizontalFactor A m Jtot omega <=
          (10 : ℝ) ^ A := by
  intro omega hnot
  unfold taoSection7Case3Outer754HorizontalFactor
    taoSection7Case3Outer754HorizontalScalar
  let x : ℝ := max (1 - (Jtot omega : ℝ) / (m : ℝ)) ((m : ℝ)⁻¹)
  have hmpos_nat : 0 < m := lt_of_lt_of_le Nat.zero_lt_one hm
  have hmpos : 0 < (m : ℝ) := Nat.cast_pos.mpr hmpos_nat
  have hnot_le : ¬ 9 * m <= 10 * Jtot omega := by
    simpa [taoSection7Case3Outer754LargeHorizontalEvent] using hnot
  have hnat_lt : 10 * Jtot omega < 9 * m := Nat.lt_of_not_ge hnot_le
  have hreal_lt : (10 : ℝ) * (Jtot omega : ℝ) < 9 * (m : ℝ) := by
    exact_mod_cast hnat_lt
  have hdiv_lt : (Jtot omega : ℝ) / (m : ℝ) < (9 : ℝ) / 10 := by
    rw [div_lt_iff₀' hmpos]
    nlinarith
  have hbase_lb : (1 / 10 : ℝ) <= x := by
    dsimp [x]
    apply le_max_of_le_left
    nlinarith
  have hbase_pos : 0 < x :=
    lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1 / 10) hbase_lb
  have hinv_le : x⁻¹ <= (10 : ℝ) := by
    have h :=
      (inv_le_inv₀ hbase_pos (by norm_num : (0 : ℝ) < 1 / 10)).mpr hbase_lb
    norm_num at h
    exact h
  have hinv_nonneg : 0 <= x⁻¹ := inv_nonneg.mpr (le_of_lt hbase_pos)
  calc
    (x ^ A)⁻¹ = x⁻¹ ^ A := by rw [inv_pow]
    _ <= (10 : ℝ) ^ A := pow_le_pow_left₀ hinv_nonneg hinv_le A

end

end Tao
end Erdos1135
