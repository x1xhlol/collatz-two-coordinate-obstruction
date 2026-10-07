import InverseBranchCylinder

set_option autoImplicit false

namespace CollatzCylinderPacking.Arithmetic.InverseDoob

theorem inverseEndpoint_injective_on_guard {n a b : ℕ} (hn : 0 < n)
    (ha : (2 ^ a * n) % 3 = 2) (hb : (2 ^ b * n) % 3 = 2)
    (he : inverseEndpoint n a = inverseEndpoint n b) : a = b := by
  have hsa := (oddPredecessor_spec ha).2.2
  have hsb := (oddPredecessor_spec hb).2.2
  change step (inverseEndpoint n a) = 2 ^ a * n at hsa
  change step (inverseEndpoint n b) = 2 ^ b * n at hsb
  rw [he, hsb] at hsa
  exact (Nat.pow_right_injective (by decide : 2 ≤ (2 : ℕ)))
    (Nat.eq_of_mul_eq_mul_right hn hsa.symm)

theorem transitionPMF_inverseEndpoint {n a : ℕ} (hn : 0 < n) (hu : n % 3 ≠ 0)
    (ha : (2 ^ a * n) % 3 = 2) :
    transitionPMF n (inverseEndpoint n a) = exponentPMF n hn (potential_pos_of_unit hn hu) a := by
  rw [transitionPMF_of_unit hn hu, PMF.map_apply]
  rw [tsum_eq_single a]
  · simp
  · intro b hba
    by_cases hmass : exponentPMF n hn (potential_pos_of_unit hn hu) b = 0
    · simp only [hmass, ite_self]
    · have hb := (exponentPMF_support hn (potential_pos_of_unit hn hu) hmass).1
      have hne : inverseEndpoint n a ≠ inverseEndpoint n b := by
        intro he
        exact hba (inverseEndpoint_injective_on_guard hn hb ha he.symm)
      simp only [if_neg hne]

theorem transitionPMF_nonperiodic_atom {n a : ℕ} (hn : 0 < n) (hu : n % 3 ≠ 0)
    (hnp : Nonperiodic n) (ha : (2 ^ a * n) % 3 = 2) :
    transitionPMF n (inverseEndpoint n a) =
      ENNReal.ofReal (firstHitWeight n (inverseEndpoint n a) *
        actualFirstHitDensity (inverseEndpoint n a) / actualFirstHitDensity n) := by
  rw [transitionPMF_inverseEndpoint hn hu ha, exponentPMF_nonperiodic_cylinder hn hu hnp ha]

end CollatzCylinderPacking.Arithmetic.InverseDoob
