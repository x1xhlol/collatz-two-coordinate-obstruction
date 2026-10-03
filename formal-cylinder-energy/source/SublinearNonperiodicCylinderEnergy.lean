import NonperiodicSyracuseSpine
import FiniteCylinderEnergyImplication
import ShiftedCesaroEnergyExclusion

set_option autoImplicit false
open Filter Topology Classical
open scoped BigOperators

namespace CollatzCanonical.PeriodicCensusFloor
open CollatzCylinderPacking CollatzCylinderPacking.Arithmetic
open CollatzCanonical.NativeTao CollatzCanonical.ForwardComponent
open CollatzCanonical.CesaroAbel Erdos1135

noncomputable section

/-- The positive odd representatives that are themselves nonperiodic at cylinder depth k. -/
def positiveOddNonperiodicCylinderHead (k : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (3 ^ k)).filter (fun n => Odd n ∧
    ¬ ∃ r : ℕ, 0 < r ∧ iterate r n = n)

/-- Finite square energy at the positive odd nonperiodic representatives 1 through 3^k. -/
def positiveOddNonperiodicCylinderSquareEnergy (k : ℕ) : ℝ :=
  ∑ n ∈ positiveOddNonperiodicCylinderHead k, (canonicalRho k n / (n : ℝ)) ^ 2

/-- Exact-depth propagation packs K+1 different states of one actual divergent spine. -/
theorem nonperiodic_cylinder_spine_energy_lower {c : ℝ} (hc : 0 < c)
    (hprop : ∀ u : ℕ, Odd u → Function.Injective (fun i => iterate i u) →
      ∀ k j : ℕ, 0 < k → c * (canonicalRho k u / (u : ℝ)) ≤
        canonicalRho (k + j) ((Tao.syracuse^[j]) u) / ((Tao.syracuse^[j]) u : ℝ))
    {u : ℕ} (hu : Odd u) (hinj : Function.Injective (fun i => iterate i u))
    {C : ℕ} (hCpos : 0 < C) (hC : u ≤ 3 ^ C) (K : ℕ) :
    c ^ 2 * (∑ j ∈ Finset.range (K + 1),
      (canonicalRho (K + C - j) u / (u : ℝ)) ^ 2) ≤
      positiveOddNonperiodicCylinderSquareEnergy (K + C) := by
  let spine : ℕ → ℕ := fun j => (Tao.syracuse^[j]) u
  let points := (Finset.range (K + 1)).image spine
  have hsub : points ⊆ positiveOddNonperiodicCylinderHead (K + C) := by
    intro n hn
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hn
    have hjK : j ≤ K := by simpa using Finset.mem_range.mp hj
    have hodd : Odd (spine j) := Tao.syracuse_iterate_odd j u hu
    have hpos : 0 < spine j := by obtain ⟨t, ht⟩ := hodd; omega
    unfold positiveOddNonperiodicCylinderHead
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨hpos, syracuse_spine_head_bound hu hC hjK⟩,
      hodd, syracuse_spine_nonperiodic hu hinj j⟩
  have hpoint (j : ℕ) (hj : j ∈ Finset.range (K + 1)) :
      c ^ 2 * (canonicalRho (K + C - j) u / (u : ℝ)) ^ 2 ≤
        (canonicalRho (K + C) (spine j) / (spine j : ℝ)) ^ 2 := by
    have hjK : j ≤ K := by simpa using Finset.mem_range.mp hj
    have hk : 0 < K + C - j := by omega
    have h := hprop u hu hinj (K + C - j) j hk
    rw [Nat.sub_add_cancel (by omega : j ≤ K + C)] at h
    have hl : 0 ≤ c * (canonicalRho (K + C - j) u / (u : ℝ)) :=
      mul_nonneg hc.le (div_nonneg (canonicalRho_nonneg _ _) (Nat.cast_nonneg _))
    have hr : 0 ≤ canonicalRho (K + C) (spine j) / (spine j : ℝ) :=
      div_nonneg (canonicalRho_nonneg _ _) (Nat.cast_nonneg _)
    simpa only [mul_pow] using (sq_le_sq₀ hl hr).mpr h
  calc
    _ = ∑ j ∈ Finset.range (K + 1),
        c ^ 2 * (canonicalRho (K + C - j) u / (u : ℝ)) ^ 2 :=
      Finset.mul_sum _ _ _
    _ ≤ ∑ j ∈ Finset.range (K + 1),
        (canonicalRho (K + C) (spine j) / (spine j : ℝ)) ^ 2 :=
      Finset.sum_le_sum hpoint
    _ = ∑ n ∈ points, (canonicalRho (K + C) n / (n : ℝ)) ^ 2 :=
      (Finset.sum_image (s := Finset.range (K + 1))
        (f := fun n => (canonicalRho (K + C) n / (n : ℝ)) ^ 2)
        (syracuse_spine_injective hu hinj).injOn).symm
    _ ≤ positiveOddNonperiodicCylinderSquareEnergy (K + C) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)

/-- The energy decay is an explicit hypothesis; the conclusion permits any number of cycles. -/
theorem universal_eventual_periodicity_of_sublinear_odd_nonperiodic_energy
    (henergy : Tendsto (fun k =>
      positiveOddNonperiodicCylinderSquareEnergy k / ((k : ℝ) + 1)) atTop (𝓝 0)) :
    UniversalEventualPeriodicity := by
  intro n hn
  apply (shortcut_noninjective_iff_hits_periodic n).mp
  intro hinj
  obtain ⟨u, hu, hunit, huinj⟩ := exists_odd_unit_injective_root hn hinj
  have hup : 0 < u := by obtain ⟨t, ht⟩ := hu; omega
  have huR : (0 : ℝ) < u := by exact_mod_cast hup
  obtain ⟨c, hc, hprop⟩ := exists_uniform_syracuse_cylinder_survival
  have hlim : Tendsto (cesaroMean (fun k => canonicalRho k u / (u : ℝ))) atTop
      (𝓝 (actualDensityValue actualFirstHitDensity u / (u : ℝ))) := by
    have he : u - 1 + 1 = u := by omega
    simpa only [he] using actual_normalized_cylinder_cesaro (u - 1)
  have htrace : 0 < actualDensityValue actualFirstHitDensity u / (u : ℝ) :=
    div_pos ((actual_trace_positive_iff_unit hup).mpr hunit) huR
  exact sublinear_energy_excludes_diagonal_cesaro
    (fun k => canonicalRho k u / (u : ℝ)) positiveOddNonperiodicCylinderSquareEnergy
    u c (actualDensityValue actualFirstHitDensity u / (u : ℝ)) hc htrace hlim henergy
    (fun K => nonperiodic_cylinder_spine_energy_lower hc hprop hu huinj hup
      (Nat.lt_pow_self (by decide : 1 < 3)).le K)

#print axioms nonperiodic_cylinder_spine_energy_lower
#print axioms universal_eventual_periodicity_of_sublinear_odd_nonperiodic_energy
end
end CollatzCanonical.PeriodicCensusFloor
