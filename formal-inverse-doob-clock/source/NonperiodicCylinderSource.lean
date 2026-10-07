import ActualInverseDoobLaw
import FirstHitWeightTransport

set_option autoImplicit false

open Filter Topology

namespace CollatzCylinderPacking.Arithmetic.InverseDoob
open CollatzCanonical.DirichletAbelian

def Nonperiodic (n : ℕ) : Prop := ¬ ∃ r : ℕ, 0 < r ∧ iterate r n = n

theorem nonperiodic_ancestor {n y A : ℕ} (hn : Nonperiodic n)
    (hy : iterate A y = n) : Nonperiodic y := by
  rintro ⟨r, hr, hret⟩
  apply hn
  refine ⟨r, hr, ?_⟩
  rw [← hy, ← iterate_add, Nat.add_comm A r, iterate_add, hret]

theorem firstHit_of_nonperiodic {n q A : ℕ} (hn : Nonperiodic n)
    (hhit : iterate A q = n) : FirstHit q n A := by
  have hf := firstHit_find (show ∃ B, iterate B q = n from ⟨A, hhit⟩)
  have he := (hitting_time_iff_eq_first_of_no_return hf
    (fun r hr hret => hn ⟨r, hr, hret⟩)).mp hhit
  simpa only [he] using hf

theorem firstHitWeight_through_nonperiodic {n y q A B : ℕ} (hn : Nonperiodic n)
    (hy : iterate A y = n) (hq : iterate B q = y) :
    firstHitWeight n q = firstHitWeight n y * firstHitWeight y q := by
  have htotal : iterate (B + A) q = n := by rw [iterate_add, hq, hy]
  rw [firstHitWeight_eq_pathWeight (firstHit_of_nonperiodic hn htotal),
    firstHitWeight_eq_pathWeight (firstHit_of_nonperiodic hn hy),
    firstHitWeight_eq_pathWeight (firstHit_of_nonperiodic (nonperiodic_ancestor hn hy) hq),
    pathWeight_add, hq, mul_comm]

noncomputable def suffixSourceWeight (n y q : ℕ) : ℝ := by
  classical
  exact if ∃ B, iterate B q = y then firstHitWeight n q else 0

theorem suffixSourceWeight_factor {n y A : ℕ} (hn : Nonperiodic n)
    (hy : iterate A y = n) (q : ℕ) :
    suffixSourceWeight n y q = firstHitWeight n y * firstHitWeight y q := by
  classical
  by_cases hq : ∃ B, iterate B q = y
  · obtain ⟨B, hB⟩ := hq
    rw [suffixSourceWeight, if_pos (show ∃ B, iterate B q = y from ⟨B, hB⟩)]
    exact firstHitWeight_through_nonperiodic hn hy hB
  · simp only [suffixSourceWeight, if_neg hq, firstHitWeight, dif_neg hq, mul_zero]

theorem odd_suffixSourceWeight_mean {n y A : ℕ} (hn : Nonperiodic n)
    (hy : iterate A y = n) :
    Tendsto (fun t : ℝ => logarithmicCumulative
      (fun q => if q % 2 = 1 then suffixSourceWeight n y q else 0) t / t)
      atTop (𝓝 (firstHitWeight n y * actualFirstHitDensity y / 2)) := by
  have he : (fun q => if q % 2 = 1 then suffixSourceWeight n y q else 0) =
      fun q => firstHitWeight n y * oddFirstHitWeight y q := by
    funext q
    rw [suffixSourceWeight_factor hn hy q]
    unfold oddFirstHitWeight
    split_ifs <;> simp
  rw [he]
  have hlim := (actual_firstHitWeight_odd_mean y).const_mul (firstHitWeight n y)
  convert hlim using 1
  · ext t
    rw [logarithmicCumulative_const_mul]
    ring
  · ring

theorem normalized_suffixSourceWeight_mean {n y A : ℕ} (hn : Nonperiodic n)
    (hy : iterate A y = n) :
    Tendsto (fun t : ℝ => (2 / actualFirstHitDensity n) *
      (logarithmicCumulative
        (fun q => if q % 2 = 1 then suffixSourceWeight n y q else 0) t / t))
      atTop (𝓝 (firstHitWeight n y * actualFirstHitDensity y / actualFirstHitDensity n)) := by
  convert (odd_suffixSourceWeight_mean hn hy).const_mul (2 / actualFirstHitDensity n) using 1
  ring

end CollatzCylinderPacking.Arithmetic.InverseDoob
