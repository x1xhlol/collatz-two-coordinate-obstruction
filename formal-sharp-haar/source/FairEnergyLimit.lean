import FairEnergyWordCore

set_option autoImplicit false

namespace CollatzCylinderPacking.Arithmetic.FairEnergy

open Filter
open scoped Topology

theorem residue_energy_le_of_finite (k : ℕ) (B : ℝ)
    (hB : ∀ s : Finset (GeometricWord k),
      (3 : ℝ) ^ k * ∑ v : ZMod (3 ^ k), (∑ w ∈ s, residueTerm k v w) ^ 2 ≤ B) :
    (3 : ℝ) ^ k * ∑ v : ZMod (3 ^ k), (residueMass k v) ^ 2 ≤ B := by
  classical
  have hv (v : ZMod (3 ^ k)) :
      Tendsto (fun s : Finset (GeometricWord k) => ∑ w ∈ s, residueTerm k v w)
        atTop (𝓝 (residueMass k v)) :=
    (residueTerm_summable k v).hasSum
  have ht : Tendsto
      (fun s : Finset (GeometricWord k) =>
        (3 : ℝ) ^ k * ∑ v : ZMod (3 ^ k), (∑ w ∈ s, residueTerm k v w) ^ 2)
      atTop (𝓝 ((3 : ℝ) ^ k * ∑ v : ZMod (3 ^ k), (residueMass k v) ^ 2)) := by
    apply tendsto_const_nhds.mul
    exact tendsto_finset_sum Finset.univ (fun v _ => (hv v).pow 2)
  exact le_of_tendsto' ht hB

end CollatzCylinderPacking.Arithmetic.FairEnergy
