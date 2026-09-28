import Erdos1135.Tao.Renewal.Outer754HorizontalFactor
import Erdos1135.Tao.Renewal.Prop78Case1White

/-!
# Zero-Safe Q_m Horizontal Normalization

This leaf identifies the saturated Case 1 inverse-power factor with Tao's
dimensionless outer `(7.54)` horizontal factor and applies that identity to a
general endpoint with positive horizontal advance.  No cancellation by the
previous `Q_m` value is used.
-/

namespace Erdos1135
namespace Tao

noncomputable section

/-- Exact saturated normalization of the Case 1 inverse-power factor. -/
theorem taoSection7Case1InvPow_eq_inv_m_pow_mul_outer754HorizontalScalar
    (A m : ℕ) (r : ℕ+) (hm : 1 <= m) :
    taoSection7Case1InvPow A m r =
      ((m : ℝ) ^ A)⁻¹ *
        taoSection7Case3Outer754HorizontalScalar A m (r : ℕ) := by
  have hmposNat : 0 < m := lt_of_lt_of_le Nat.zero_lt_one hm
  have hmpos : 0 < (m : ℝ) := Nat.cast_pos.mpr hmposNat
  by_cases hrm : (r : ℕ) < m
  · have hsub : 1 <= m - (r : ℕ) := by omega
    have hsubposNat : 0 < m - (r : ℕ) := by omega
    have hsubpos : 0 < (((m - (r : ℕ) : ℕ) : ℝ)) := by
      exact_mod_cast hsubposNat
    have hbase :
        1 - (r : ℝ) / (m : ℝ) =
          ((m - (r : ℕ) : ℕ) : ℝ) / (m : ℝ) := by
      rw [Nat.cast_sub hrm.le]
      field_simp [hmpos.ne']
    have hfloor :
        (m : ℝ)⁻¹ <= 1 - (r : ℝ) / (m : ℝ) := by
      rw [hbase, inv_eq_one_div]
      exact (div_le_div_iff_of_pos_right hmpos).2 (by
        exact_mod_cast hsub)
    have hmax :
        max (1 - (r : ℝ) / (m : ℝ)) ((m : ℝ)⁻¹) =
          ((m - (r : ℕ) : ℕ) : ℝ) / (m : ℝ) := by
      rw [max_eq_left hfloor, hbase]
    unfold taoSection7Case1InvPow
      taoSection7Case3Outer754HorizontalScalar
    rw [max_eq_left hsub, hmax, ← inv_pow, ← inv_pow, ← mul_pow]
    apply congrArg (fun x : ℝ => x ^ A)
    field_simp [hmpos.ne', hsubpos.ne']
  · have hmr : m <= (r : ℕ) := by omega
    have hnatMax : max (m - (r : ℕ)) 1 = 1 := by omega
    have hratio : (1 : ℝ) <= (r : ℝ) / (m : ℝ) := by
      apply (le_div_iff₀ hmpos).2
      simpa using (show (m : ℝ) <= (r : ℝ) by exact_mod_cast hmr)
    have hfloor :
        1 - (r : ℝ) / (m : ℝ) <= (m : ℝ)⁻¹ :=
      (sub_nonpos.mpr hratio).trans (inv_nonneg.mpr hmpos.le)
    unfold taoSection7Case1InvPow
      taoSection7Case3Outer754HorizontalScalar
    rw [hnatMax, max_eq_right hfloor]
    norm_num only [Nat.cast_one, inv_one, one_pow]
    rw [← inv_pow, ← inv_pow, inv_inv, ← mul_pow,
      inv_mul_cancel₀ hmpos.ne', one_pow]

/-- Pointwise actual-`Q` normalization after any positive horizontal advance
from a `Q_m` boundary.  The previous `Q_m` value may be zero. -/
theorem taoSection7SourceActualQ_horizontalAdvance_le_normalized
    {Omega : Type*} {n A m : ℕ} {xi : ZMod (3 ^ n)} {epsilon : ℝ}
    (hepsilon : 0 <= epsilon) (hm : 1 <= m)
    {start : TaoSection7RenewalPoint}
    (hstart : taoSection7QmBoundary (n / 2) m start)
    (endpoint : Omega -> TaoSection7RenewalPoint)
    (Jtot : Omega -> ℕ) (omega : Omega)
    (hJtot : 1 <= Jtot omega)
    (hendpoint_j :
      ((endpoint omega).j : ℕ) = (start.j : ℕ) + Jtot omega) :
    taoSection7SourceActualQ n xi epsilon (endpoint omega) <=
      ((m : ℝ) ^ A)⁻¹ *
          taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon *
        taoSection7Case3Outer754HorizontalFactor A m Jtot omega := by
  let r : ℕ+ := ⟨Jtot omega, hJtot⟩
  let h : TaoSection7RenewalPoint :=
    { j := r, l := (endpoint omega).l - start.l }
  have hendpoint : endpoint omega = start + h := by
    ext
    · apply PNat.eq
      simpa [h, r] using hendpoint_j
    · simp [h]
  have hQ := taoSection7SourceActualQ_add_hold_le_case1InvPow_mul_qmPrev
    (n := n) (A := A) (m := m) (xi := xi) (epsilon := epsilon)
    hepsilon hstart h
  have hnormalize :=
    taoSection7Case1InvPow_eq_inv_m_pow_mul_outer754HorizontalScalar
      A m r hm
  rw [hendpoint]
  calc
    taoSection7SourceActualQ n xi epsilon (start + h) <=
        taoSection7Case1InvPow A m r *
          taoSection7SourceActualQmAtCutoff
            n A (m - 1) xi epsilon := by
      simpa [h] using hQ
    _ = ((m : ℝ) ^ A)⁻¹ *
          taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon *
        taoSection7Case3Outer754HorizontalFactor A m Jtot omega := by
      rw [hnormalize]
      unfold taoSection7Case3Outer754HorizontalFactor
      dsimp [r]
      change ((m : ℝ) ^ A)⁻¹ *
          taoSection7Case3Outer754HorizontalScalar A m (Jtot omega) *
            taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon =
        ((m : ℝ) ^ A)⁻¹ *
            taoSection7SourceActualQmAtCutoff n A (m - 1) xi epsilon *
          taoSection7Case3Outer754HorizontalScalar A m (Jtot omega)
      ring

end

end Tao
end Erdos1135
