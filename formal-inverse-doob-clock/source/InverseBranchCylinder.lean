import NonperiodicCylinderSource

set_option autoImplicit false

open Filter Topology

namespace CollatzCylinderPacking.Arithmetic.InverseDoob
open CollatzCanonical.GreenKernelScalars

theorem inverseEndpoint_block {n a : ℕ} (h : (2 ^ a * n) % 3 = 2) :
    inverseEndpoint n a % 2 = 1 ∧
      iterate (a + 1) (inverseEndpoint n a) = n ∧
      oddCount (a + 1) (inverseEndpoint n a) = 1 := by
  have hs := oddPredecessor_spec h
  have he : 3 * inverseEndpoint n a + 1 = 2 ^ (a + 1) * n := by
    have ho := step_odd hs.2.1
    rw [hs.2.2] at ho
    change 3 * oddPredecessor (2 ^ a * n) + 1 = _
    rw [pow_succ]
    nlinarith
  have hb := block_path (by omega : 0 < a + 1) he
  exact ⟨hb.1, hb.2.1, hb.2.2.1⟩

theorem potential_of_nonperiodic {n : ℕ} (hn : Nonperiodic n) :
    potential n = delta * n * actualFirstHitDensity n := by
  simp only [potential, actualDensityValue, greenCycleFactor, dif_neg hn, mul_one]

theorem inverseRowMass_eq_weighted_density {n a : ℕ} (hn : Nonperiodic n)
    (h : (2 ^ a * n) % 3 = 2) :
    inverseRowMass n a = delta * n *
      (firstHitWeight n (inverseEndpoint n a) * actualFirstHitDensity (inverseEndpoint n a)) := by
  have hpos := (oddPredecessor_spec h).1
  obtain ⟨_, hhit, hcount⟩ := inverseEndpoint_block h
  have hfirst := firstHit_of_nonperiodic hn hhit
  have hw := orbitRatio_first_hit (q := inverseEndpoint n a) hpos hfirst
  rw [orbitRatio, hcount, pow_one] at hw
  rw [inverseRowMass, if_pos h, potential_of_nonperiodic (nonperiodic_ancestor hn hhit)]
  have hq0 : (inverseEndpoint n a : ℝ) ≠ 0 := by exact_mod_cast hpos.ne'
  have heq : (3 : ℝ) * inverseEndpoint n a =
      (n : ℝ) * firstHitWeight n (inverseEndpoint n a) * 2 ^ (a + 1) := by
    apply (div_eq_div_iff (by positivity) hq0).mp at hw
    exact hw
  have hw' : (3 : ℝ) * inverseEndpoint n a / 2 ^ (a + 1) =
      (n : ℝ) * firstHitWeight n (inverseEndpoint n a) := by
    exact (div_eq_iff (by positivity)).mpr heq
  calc
    _ = delta * actualFirstHitDensity (inverseEndpoint n a) *
        ((3 : ℝ) * inverseEndpoint n a / 2 ^ (a + 1)) := by rw [pow_succ]; ring
    _ = _ := by rw [hw']; ring

theorem exponentPMF_nonperiodic_cylinder {n a : ℕ} (hn : 0 < n) (hu : n % 3 ≠ 0)
    (hnp : Nonperiodic n) (h : (2 ^ a * n) % 3 = 2) :
    exponentPMF n hn (potential_pos_of_unit hn hu) a =
      ENNReal.ofReal (firstHitWeight n (inverseEndpoint n a) *
        actualFirstHitDensity (inverseEndpoint n a) / actualFirstHitDensity n) := by
  rw [exponentPMF_apply, inverseRowMass_eq_weighted_density hnp h,
    potential_of_nonperiodic hnp]
  congr 1
  have hδ : delta ≠ 0 := delta_pos.ne'
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  field_simp

theorem exponentPMF_source_limit {n a : ℕ} (hn : 0 < n) (hu : n % 3 ≠ 0)
    (hnp : Nonperiodic n) (h : (2 ^ a * n) % 3 = 2) :
    Tendsto (fun t : ℝ => (2 / actualFirstHitDensity n) *
      (CollatzCanonical.DirichletAbelian.logarithmicCumulative
        (fun q => if q % 2 = 1 then suffixSourceWeight n (inverseEndpoint n a) q else 0) t / t))
      atTop (𝓝 (exponentPMF n hn (potential_pos_of_unit hn hu) a).toReal) := by
  rw [exponentPMF_nonperiodic_cylinder hn hu hnp h, ENNReal.toReal_ofReal]
  · exact normalized_suffixSourceWeight_mean hnp (inverseEndpoint_block h).2.1
  · exact div_nonneg (mul_nonneg (firstHitWeight_bounds _ _).1
      (actualFirstHitDensity_nonneg _)) (actualFirstHitDensity_nonneg _)

end CollatzCylinderPacking.Arithmetic.InverseDoob
