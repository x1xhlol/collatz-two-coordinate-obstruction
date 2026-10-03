import TerminalFanEnvelope
import PeriodicSourceMean

set_option autoImplicit false

namespace CollatzCanonical.PeriodicCensusFloor
open Erdos1135Predecessor.ND.PositiveDensity
open Filter Topology
open scoped BigOperators

noncomputable section

def oddTerminalFan (m q : ℕ) : ℝ :=
  if Odd q then terminalFanEnvelope m (q : ZMod (3 ^ m)) else 0

theorem oddTerminalFan_nonneg (m q : ℕ) : 0 ≤ oddTerminalFan m q := by
  unfold oddTerminalFan
  split_ifs
  · exact terminalFanEnvelope_nonneg _ _
  · exact le_rfl

theorem oddTerminalFan_le (m q : ℕ) :
    oddTerminalFan m q ≤ (8 / 9 : ℝ) * ((3 ^ m : ℕ) : ℝ) := by
  unfold oddTerminalFan
  split_ifs
  · exact terminalFanEnvelope_le _ _
  · positivity

theorem oddTerminalFan_periodic (m : ℕ) :
    Function.Periodic (oddTerminalFan m) (2 * 3 ^ m) := by
  intro q
  have ho : Odd (q + 2 * 3 ^ m) ↔ Odd q := by
    rw [Nat.odd_iff, Nat.odd_iff]
    omega
  have hc : ((q + 2 * 3 ^ m : ℕ) : ZMod (3 ^ m)) = (q : ZMod (3 ^ m)) := by
    simp
  simp only [oddTerminalFan, ho, hc]

theorem oddTerminalFan_paired (m q : ℕ) :
    oddTerminalFan m q + oddTerminalFan m (3 ^ m + q) =
      terminalFanEnvelope m (q : ZMod (3 ^ m)) := by
  have hodd : (3 ^ m) % 2 = 1 :=
    Nat.odd_iff.mp ((by decide : Odd (3 : ℕ)).pow)
  have ho : Odd (3 ^ m + q) ↔ ¬Odd q := by
    rw [Nat.odd_iff, Nat.odd_iff]
    omega
  have hc : ((3 ^ m + q : ℕ) : ZMod (3 ^ m)) = (q : ZMod (3 ^ m)) := by
    simp
  by_cases hq : Odd q <;> simp [oddTerminalFan, ho, hc, hq]

theorem terminalFanEnvelope_nat_sum (m : ℕ) :
    (∑ q ∈ Finset.range (3 ^ m), terminalFanEnvelope m (q : ZMod (3 ^ m))) =
      ∑ y : ZMod (3 ^ m), terminalFanEnvelope m y := by
  let e : Fin (3 ^ m) ≃ ZMod (3 ^ m) :=
    { toFun := fun q => (q.val : ZMod (3 ^ m))
      invFun := fun y => ⟨y.val, ZMod.val_lt y⟩
      left_inv := fun q => Fin.ext (ZMod.val_natCast_of_lt q.isLt)
      right_inv := fun y => ZMod.natCast_zmod_val y }
  have h := e.sum_comp (terminalFanEnvelope m)
  change (∑ q : Fin (3 ^ m), terminalFanEnvelope m (q.val : ZMod (3 ^ m))) = _ at h
  rw [Fin.sum_univ_eq_sum_range (fun q : ℕ => terminalFanEnvelope m (q : ZMod (3 ^ m)))] at h
  exact h

theorem oddTerminalFan_sum (m : ℕ) :
    (∑ q ∈ Finset.range (2 * 3 ^ m), oddTerminalFan m q) =
      ∑ y : ZMod (3 ^ m), terminalFanEnvelope m y := by
  rw [two_mul, Finset.sum_range_add, ← Finset.sum_add_distrib]
  simp_rw [oddTerminalFan_paired]
  exact terminalFanEnvelope_nat_sum m

theorem oddTerminalFan_mean (m : ℕ) :
    (∑ q ∈ Finset.range (2 * 3 ^ m), oddTerminalFan m q) /
      ((2 * 3 ^ m : ℕ) : ℝ) = 4 / 9 := by
  rw [oddTerminalFan_sum]
  have hm := terminalFanEnvelope_fullMean m
  unfold ndTernaryUniformMean ndTernaryUniformScale at hm
  rw [one_div_mul_eq_div] at hm
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  calc
    _ = ((∑ y : ZMod (3 ^ m), terminalFanEnvelope m y) /
      ((3 ^ m : ℕ) : ℝ)) / 2 := by ring
    _ = 4 / 9 := by rw [hm]; norm_num

theorem oddTerminalFan_weighted_mean (w : ℕ → ℝ) (m : ℕ)
    (hw : ∀ q, |w q| ≤ 1)
    (hvar : Tendsto (fun X => adjacentVariation w X / (X : ℝ)) atTop (𝓝 0))
    {d : ℝ} (hmean : Tendsto (sourceMean w) atTop (𝓝 d)) :
    Tendsto (sourceMean (fun q => w q * oddTerminalFan m q)) atTop
      (𝓝 (d * (4 / 9))) := by
  simpa only [oddTerminalFan_mean] using
    periodic_weighted_mean w (oddTerminalFan m) (2 * 3 ^ m) (by positivity)
      (oddTerminalFan_periodic m) hw hvar hmean

theorem oddTerminalFan_scaled_source_limit (w : ℕ → ℝ) (m : ℕ) (r : ℝ)
    (hw : ∀ q, |w q| ≤ 1)
    (hvar : Tendsto (fun X => adjacentVariation w X / (X : ℝ)) atTop (𝓝 0))
    {d : ℝ} (hmean : Tendsto (sourceMean w) atTop (𝓝 d)) :
    Tendsto (fun X : ℕ => (r / (X : ℝ)) *
      ∑ q ∈ Finset.range (32 * X), w q * oddTerminalFan m q) atTop
      (𝓝 ((128 * r / 9) * d)) := by
  have h32 : Tendsto (fun X : ℕ => 32 * X) atTop atTop := by
    apply tendsto_atTop.2
    intro b
    exact eventually_atTop.2 ⟨b, fun X hX => by omega⟩
  have h := ((oddTerminalFan_weighted_mean w m hw hvar hmean).comp h32).const_mul
    (32 * r)
  have heq (X : ℕ) : (r / (X : ℝ)) *
      (∑ q ∈ Finset.range (32 * X), w q * oddTerminalFan m q) =
      32 * r * sourceMean (fun q => w q * oddTerminalFan m q) (32 * X) := by
    simp only [sourceMean, Nat.cast_mul, Nat.cast_ofNat, div_eq_mul_inv,
      mul_inv_rev]
    norm_num
    ring
  have hc : 32 * r * (d * (4 / 9)) = (128 * r / 9) * d := by ring
  simpa only [← heq, hc, Function.comp_def] using h

#print axioms oddTerminalFan_nonneg
#print axioms oddTerminalFan_le
#print axioms oddTerminalFan_periodic
#print axioms oddTerminalFan_mean
#print axioms oddTerminalFan_weighted_mean
#print axioms oddTerminalFan_scaled_source_limit

end
end CollatzCanonical.PeriodicCensusFloor
