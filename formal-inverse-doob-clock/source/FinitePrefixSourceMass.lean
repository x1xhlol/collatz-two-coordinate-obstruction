import FinitePrefixIndex
import CountableScheffe

set_option autoImplicit false

open Filter Topology

namespace CollatzCylinderPacking.Arithmetic.InverseDoob
open CollatzCanonical.DirichletAbelian

noncomputable def prefixSourceWeight (n k : ℕ) (p : PrefixIndex k) (q : ℕ) : ℝ := by
  classical
  exact if ValidPrefix n k (prefixExtend k p) ∧
    (∃ B, iterate B q = prefixExtend k p k) then oddFirstHitWeight n q else 0

theorem prefixSourceWeight_nonneg (n k : ℕ) (p : PrefixIndex k) (q : ℕ) :
    0 ≤ prefixSourceWeight n k p q := by
  unfold prefixSourceWeight
  split_ifs
  · unfold oddFirstHitWeight
    split_ifs
    · exact (firstHitWeight_bounds _ _).1
    · exact le_rfl
  · exact le_rfl

theorem prefixSourceWeight_of_valid {n k : ℕ} {p : PrefixIndex k}
    (h : ValidPrefix n k (prefixExtend k p)) :
    prefixSourceWeight n k p = fun q =>
      if q % 2 = 1 then suffixSourceWeight n (prefixExtend k p k) q else 0 := by
  classical
  funext q
  simp only [prefixSourceWeight, h, true_and, suffixSourceWeight, oddFirstHitWeight]
  split_ifs <;> rfl

theorem prefixSourceWeight_of_invalid {n k : ℕ} {p : PrefixIndex k}
    (h : ¬ ValidPrefix n k (prefixExtend k p)) : prefixSourceWeight n k p = 0 := by
  funext q
  simp only [prefixSourceWeight, h, false_and, if_false, Pi.zero_apply]

noncomputable def prefixSourceMass (n k : ℕ) (t : ℝ) (p : PrefixIndex k) : ℝ :=
  if 0 < t then (2 / actualFirstHitDensity n) *
    (logarithmicCumulative (prefixSourceWeight n k p) t / t) else 0

noncomputable def fullSourceMass (n : ℕ) (t : ℝ) : ℝ :=
  if 0 < t then (2 / actualFirstHitDensity n) *
    (logarithmicCumulative (oddFirstHitWeight n) t / t) else 0

theorem prefixSourceMass_nonneg (n k : ℕ) (t : ℝ) (p : PrefixIndex k) :
    0 ≤ prefixSourceMass n k t p := by
  unfold prefixSourceMass
  split_ifs with ht
  · exact mul_nonneg (div_nonneg (by norm_num) (actualFirstHitDensity_nonneg n))
      (div_nonneg (logarithmicCumulative_nonneg (prefixSourceWeight_nonneg n k p) t) ht.le)
  · exact le_rfl

theorem prefixSourceMass_tendsto {n : ℕ} (hn : 0 < n) (hu : n % 3 ≠ 0)
    (hnp : Nonperiodic n) (k : ℕ) (p : PrefixIndex k) :
    Tendsto (fun t => prefixSourceMass n k t p) atTop
      (𝓝 (finitePrefixPMF n k p).toReal) := by
  classical
  by_cases h : ValidPrefix n k (prefixExtend k p)
  · have he : (fun t => prefixSourceMass n k t p) =ᶠ[atTop]
        (fun t => (2 / actualFirstHitDensity n) *
          (logarithmicCumulative
            (fun q => if q % 2 = 1 then suffixSourceWeight n (prefixExtend k p k) q else 0) t / t)) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
      rw [prefixSourceMass, if_pos ht, prefixSourceWeight_of_valid h]
    rw [finitePrefixPMF_apply]
    exact (pathLaw_validPrefix_source_limit hnp k (prefixExtend k p) h).congr' he.symm
  · rw [finitePrefixPMF_eq_zero_of_invalid hn hu p h, ENNReal.toReal_zero]
    have he : (fun t => prefixSourceMass n k t p) = fun _ => 0 := by
      funext t
      rw [prefixSourceMass, prefixSourceWeight_of_invalid h]
      simp [logarithmicCumulative]
    rw [he]
    exact tendsto_const_nhds

theorem fullSourceMass_tendsto {n : ℕ} (hn : 0 < n) (hu : n % 3 ≠ 0) :
    Tendsto (fullSourceMass n) atTop (𝓝 1) := by
  have hD := (actual_weighted_density_positive_iff_unit hn).mpr hu
  have hh := (actual_firstHitWeight_odd_mean n).const_mul (2 / actualFirstHitDensity n)
  have hnorm : (2 / actualFirstHitDensity n) * (actualFirstHitDensity n / 2) = 1 := by
    field_simp
  rw [hnorm] at hh
  apply hh.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  exact (if_pos ht).symm

theorem logarithmicCumulative_sum {ι : Type*} (S : Finset ι) (w : ι → ℕ → ℝ) (t : ℝ) :
    logarithmicCumulative (fun q => ∑ i ∈ S, w i q) t =
      ∑ i ∈ S, logarithmicCumulative (w i) t := by
  classical
  unfold logarithmicCumulative
  simp_rw [Finset.sum_div]
  exact Finset.sum_comm

end CollatzCylinderPacking.Arithmetic.InverseDoob
