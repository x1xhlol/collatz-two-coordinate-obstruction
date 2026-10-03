import CylinderGrowthHeadTransport
import OddDyadicReciprocalBudget
import GammaFreeFirstHitCoefficient
import UniformBasinBoundaryFunction

set_option autoImplicit false
open Filter Topology Classical
open scoped BigOperators

namespace CollatzCanonical.PeriodicCensusFloor
open CollatzCylinderPacking CollatzCylinderPacking.Arithmetic Erdos1135

noncomputable section

def cylinderHeadL1Budget (K : ℕ) : ℝ :=
  2 + 3 * (K : ℝ) + (64 / 81 : ℝ) ^ K * (1 + 2 * (K : ℝ))

theorem finite_odd_cylinderHead_mass_bound (Q : Finset ℕ) {K : ℕ} (hK : 0 < K)
    (hodd : ∀ N ∈ Q, Odd N) (hheight : ∀ N ∈ Q, N ≤ 3 ^ K) :
    (∑ N ∈ Q, canonicalRho K N / (N : ℝ)) ≤ cylinderHeadL1Budget K := by
  obtain ⟨R, hR, htransport⟩ := finite_cylinderGrowthHead_transport Q hK hodd hheight
  have hhead := htransport.trans (finite_odd_dyadic_reciprocal_budget R K
    (fun q hq => (hR q hq).2) (fun q hq => Nat.odd_iff.mp (hR q hq).1))
  have htail := finite_ternary_reciprocal_budget Q K hheight
  calc
    _ ≤ ∑ N ∈ Q, (cylinderGrowthHead K N + (64 / 81 : ℝ) ^ K / (N : ℝ)) :=
      Finset.sum_le_sum (fun N hN => cylinder_le_growthHead_add_tail (hodd N hN).pos)
    _ = (∑ N ∈ Q, cylinderGrowthHead K N) +
        (64 / 81 : ℝ) ^ K * (∑ N ∈ Q, 1 / (N : ℝ)) := by
      rw [Finset.sum_add_distrib, Finset.mul_sum]
      simp only [mul_one_div]
    _ ≤ (2 + 3 * (K : ℝ)) + (64 / 81 : ℝ) ^ K * (1 + 2 * (K : ℝ)) :=
      add_le_add hhead (mul_le_mul_of_nonneg_left htail (by positivity))
    _ = cylinderHeadL1Budget K := rfl

theorem finite_odd_cylinderHead_energy_of_amplitude (Q : Finset ℕ) {K : ℕ}
    (hK : 0 < K) (hodd : ∀ N ∈ Q, Odd N) (hheight : ∀ N ∈ Q, N ≤ 3 ^ K)
    {H : ℝ} (hH : 0 ≤ H)
    (hamp : ∀ N ∈ Q, canonicalRho K N / (N : ℝ) ≤ H) :
    (∑ N ∈ Q, (canonicalRho K N / (N : ℝ)) ^ 2) ≤ H * cylinderHeadL1Budget K := by
  calc
    _ ≤ ∑ N ∈ Q, H * (canonicalRho K N / (N : ℝ)) := by
      apply Finset.sum_le_sum
      intro N hN
      have h0 := (cylinderGrowthHead_nonneg K N).trans
        (cylinderGrowthHead_le_cylinder (hodd N hN).pos)
      have h := mul_le_mul_of_nonneg_right (hamp N hN) h0
      simpa only [pow_two] using h
    _ = H * (∑ N ∈ Q, canonicalRho K N / (N : ℝ)) := (Finset.mul_sum _ _ _).symm
    _ ≤ H * cylinderHeadL1Budget K :=
      mul_le_mul_of_nonneg_left (finite_odd_cylinderHead_mass_bound Q hK hodd hheight) hH

/-- The no-return mask includes cycles whose odd period exceeds K. -/
theorem exists_uniform_masked_cylinderHead_energy_bound :
    ∃ L : ℝ, 0 < L ∧ ∀ (Q : Finset ℕ) (K : ℕ), 0 < K →
      (∀ N ∈ Q, Odd N) → (∀ N ∈ Q, N ≤ 3 ^ K) →
      (∀ N ∈ Q, ∀ j : ℕ, 0 < j → j ≤ K → (Tao.syracuse^[j]) N ≠ N) →
      ∀ H : ℝ, 0 ≤ H → (∀ N ∈ Q, actualFirstHitDensity N ≤ H) →
        (∑ N ∈ Q, (canonicalRho K N / (N : ℝ)) ^ 2) ≤
          L * H * cylinderHeadL1Budget K := by
  obtain ⟨L, hL, hbound⟩ := exists_uniform_odd_masked_cylinder_bound
  refine ⟨L, hL, ?_⟩
  intro Q K hK hodd hheight hmask H hH hD
  apply finite_odd_cylinderHead_energy_of_amplitude Q hK hodd hheight (mul_nonneg hL.le hH)
  intro N hN
  have hp : (0 : ℝ) < N := by exact_mod_cast (hodd N hN).pos
  have h := hbound N (hodd N hN) K hK (hmask N hN)
  have hnorm : canonicalRho K N / (N : ℝ) ≤ L * actualFirstHitDensity N :=
    (div_le_iff₀ hp).mpr (by nlinarith only [h])
  exact hnorm.trans (mul_le_mul_of_nonneg_left (hD N hN) hL.le)

theorem exists_uniform_noSmallAncestor_masked_energy_bound :
    ∃ L : ℝ, 0 < L ∧ ∃ ε : ℝ → ℝ,
      (∀ M, 0 ≤ ε M) ∧ Tendsto ε atTop (𝓝 0) ∧
      (∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧
        ∀ᶠ M : ℝ in atTop, ε M = C * (Real.log M) ^ (-c)) ∧
      ∀ (Q : Finset ℕ) (K : ℕ) (M : ℝ), 0 < K →
        (∀ N ∈ Q, Odd N) → (∀ N ∈ Q, N ≤ 3 ^ K) →
        (∀ N ∈ Q, ∀ j : ℕ, 0 < j → j ≤ K → (Tao.syracuse^[j]) N ≠ N) →
        (∀ N ∈ Q, NoSmallAncestor N M) →
        (∑ N ∈ Q, (canonicalRho K N / (N : ℝ)) ^ 2) ≤
          L * ε M * cylinderHeadL1Budget K := by
  obtain ⟨L, hL, henergy⟩ := exists_uniform_masked_cylinderHead_energy_bound
  obtain ⟨ε, hε, hεlim, hεrate, hbasin⟩ := exists_uniform_basin_boundary_function
  obtain ⟨P, _, hcompare⟩ := actual_basin_and_weighted_density_comparison
  refine ⟨L, hL, ε, hε, hεlim, hεrate, ?_⟩
  intro Q K M hK hodd hheight hmask hno
  apply henergy Q K hK hodd hheight hmask (ε M) (hε M)
  intro N hN
  exact (hcompare N).1.trans (hbasin M N (hodd N hN).pos (hno N hN))

def maskedOddCylinderHead (K : ℕ) : Finset ℕ :=
  (Finset.range (3 ^ K)).filter (fun N => Odd N ∧
    ∀ j : ℕ, 0 < j → j ≤ K → (Tao.syracuse^[j]) N ≠ N)

def maskedCylinderHeadEnergy (K : ℕ) : ℝ :=
  ∑ N ∈ maskedOddCylinderHead K, (canonicalRho K N / (N : ℝ)) ^ 2

def maskedNoSmallAncestorEnergy (K : ℕ) (M : ℝ) : ℝ :=
  ∑ N ∈ (maskedOddCylinderHead K).filter (fun N => NoSmallAncestor N M),
    (canonicalRho K N / (N : ℝ)) ^ 2

def maskedSmallAncestorEnergy (K : ℕ) (M : ℝ) : ℝ :=
  ∑ N ∈ (maskedOddCylinderHead K).filter (fun N => ¬ NoSmallAncestor N M),
    (canonicalRho K N / (N : ℝ)) ^ 2

theorem maskedCylinderHeadEnergy_split (K : ℕ) (M : ℝ) :
    maskedCylinderHeadEnergy K =
      maskedNoSmallAncestorEnergy K M + maskedSmallAncestorEnergy K M := by
  unfold maskedCylinderHeadEnergy maskedNoSmallAncestorEnergy maskedSmallAncestorEnergy
  exact (Finset.sum_filter_add_sum_filter_not _ _ _).symm

/-- The entire remaining term is the energy on actual forward orbits of
positive seeds at most M. No estimate on that exceptional term is assumed. -/
theorem exists_uniform_maskedEnergy_decomposition :
    ∃ L : ℝ, 0 < L ∧ ∃ ε : ℝ → ℝ,
      (∀ M, 0 ≤ ε M) ∧ Tendsto ε atTop (𝓝 0) ∧
      (∃ C c : ℝ, 0 ≤ C ∧ 0 < c ∧
        ∀ᶠ M : ℝ in atTop, ε M = C * (Real.log M) ^ (-c)) ∧
      ∀ K : ℕ, 0 < K → ∀ M : ℝ,
        maskedNoSmallAncestorEnergy K M ≤ L * ε M * cylinderHeadL1Budget K ∧
        maskedCylinderHeadEnergy K ≤ maskedSmallAncestorEnergy K M +
          L * ε M * cylinderHeadL1Budget K := by
  obtain ⟨L, hL, ε, hε, hεlim, hεrate, hfinite⟩ :=
    exists_uniform_noSmallAncestor_masked_energy_bound
  refine ⟨L, hL, ε, hε, hεlim, hεrate, ?_⟩
  intro K hK M
  let Q := (maskedOddCylinderHead K).filter (fun N => NoSmallAncestor N M)
  have hmem (N : ℕ) (hN : N ∈ Q) :
      N < 3 ^ K ∧ Odd N ∧
      (∀ j : ℕ, 0 < j → j ≤ K → (Tao.syracuse^[j]) N ≠ N) ∧
      NoSmallAncestor N M := by
    obtain ⟨hh, hno⟩ := Finset.mem_filter.mp hN
    obtain ⟨hh, hodd, hmask⟩ := Finset.mem_filter.mp hh
    exact ⟨Finset.mem_range.mp hh, hodd, hmask, hno⟩
  have hbound := hfinite Q K M hK (fun N hN => (hmem N hN).2.1)
    (fun N hN => (hmem N hN).1.le) (fun N hN => (hmem N hN).2.2.1)
    (fun N hN => (hmem N hN).2.2.2)
  change maskedNoSmallAncestorEnergy K M ≤ L * ε M * cylinderHeadL1Budget K at hbound
  refine ⟨hbound, ?_⟩
  rw [maskedCylinderHeadEnergy_split]
  linarith

#print axioms finite_odd_cylinderHead_mass_bound
#print axioms exists_uniform_noSmallAncestor_masked_energy_bound
#print axioms maskedCylinderHeadEnergy_split
#print axioms exists_uniform_maskedEnergy_decomposition
end
end CollatzCanonical.PeriodicCensusFloor
