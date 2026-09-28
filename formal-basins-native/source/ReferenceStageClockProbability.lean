import ActualReferencePassageLaw
import SyracuseStageClock

namespace CollatzClockAudit
open Erdos1135.Tao
open scoped BigOperators

theorem pmf_outer_mass_ne_top {α : Type*} (μ : PMF α) (S : Set α) :
    μ.toOuterMeasure S ≠ ⊤ := by
  apply ne_of_lt
  calc
    μ.toOuterMeasure S ≤ μ.toOuterMeasure Set.univ := μ.toOuterMeasure.mono (Set.subset_univ _)
    _ = 1 := (μ.toOuterMeasure_apply_eq_one_iff Set.univ).2 (Set.subset_univ _)
    _ < ⊤ := ENNReal.one_lt_top

theorem pmf_outer_probability_union_le {α : Type*} (μ : PMF α) (S T : Set α) :
    (μ.toOuterMeasure (S ∪ T)).toReal ≤
      (μ.toOuterMeasure S).toReal + (μ.toOuterMeasure T).toReal := by
  calc
    (μ.toOuterMeasure (S ∪ T)).toReal ≤ (μ.toOuterMeasure S + μ.toOuterMeasure T).toReal :=
      ENNReal.toReal_mono (ENNReal.add_ne_top.mpr
        ⟨pmf_outer_mass_ne_top μ S, pmf_outer_mass_ne_top μ T⟩)
        (MeasureTheory.measure_union_le (μ := μ.toOuterMeasure) S T)
    _ = _ := ENNReal.toReal_add (pmf_outer_mass_ne_top μ S) (pmf_outer_mass_ne_top μ T)

theorem pmf_outer_probability_biUnion_le {α ι : Type*} (μ : PMF α)
    (I : Finset ι) (S : ι → Set α) :
    (μ.toOuterMeasure (⋃ i ∈ I, S i)).toReal ≤
      ∑ i ∈ I, (μ.toOuterMeasure (S i)).toReal := by
  have hf : (∑ i ∈ I, μ.toOuterMeasure (S i)) ≠ ⊤ := by
    exact ENNReal.sum_ne_top.mpr (fun i hi => pmf_outer_mass_ne_top μ (S i))
  calc
    (μ.toOuterMeasure (⋃ i ∈ I, S i)).toReal ≤ (∑ i ∈ I, μ.toOuterMeasure (S i)).toReal :=
      ENNReal.toReal_mono hf (MeasureTheory.measure_biUnion_finset_le (μ := μ.toOuterMeasure) I S)
    _ = _ := ENNReal.toReal_sum (fun i hi => pmf_outer_mass_ne_top μ (S i))

/-- A stage is centered at the difference of its barrier logarithms, rather
than at the possibly overshooting actual upper landing. -/
def stageClockGoodEvent (x y : ℝ) : Set ℕ :=
  {u | ∃ t, syracuseFirstHitAtMostReal y u t ∧
    |(t : ℝ) - (Real.log x - Real.log y) / clockDrift| ≤
      40 * (Real.log x) ^ (3 / 5 : ℝ)}

theorem reference_stage_good_of_two_local_clocks {x y : ℝ} (hx : 1 ≤ x)
    (hy : 1 ≤ y) (hyx : y ≤ x) (q : TaoOddNat)
    (hqx : q ∈ realLocalClockGoodEvent x) (hqy : q ∈ realLocalClockGoodEvent y) :
    (syracusePassLocationRealFloorOrOne x q.1 hx).1 ∈ stageClockGoodEvent x y := by
  obtain ⟨r, hr, her⟩ := hqx
  obtain ⟨t, ht, het⟩ := hqy
  have hdiff := real_first_hit_difference_clock hyx hr ht her het
  have hlogy : 0 ≤ Real.log y := Real.log_nonneg hy
  have hlogle : Real.log y ≤ Real.log x := Real.log_le_log (by linarith) hyx
  have hpow : (Real.log y) ^ (3 / 5 : ℝ) ≤ (Real.log x) ^ (3 / 5 : ℝ) :=
    Real.rpow_le_rpow hlogy hlogle (by norm_num)
  rw [real_pass_value_eq_of_first_hit hx hr]
  refine ⟨t - r, hdiff.1, ?_⟩
  linarith [hdiff.2]

/-- The reference stage event uses the same actual source at the adjacent
thresholds. Its failure pays the two local errors only. -/
theorem reference_stage_clock_bad_probability {C c y : ℝ} (hy : 1 < y)
    (lower : RealClockScaleFacts C c y) (upper : RealClockScaleFacts C c (y ^ taoAlpha))
    (hmass : 0 < logFinsetMass
      (oddLogWindow (realClockSourceLo (y ^ taoAlpha) .alpha)
        (realClockSourceHi (y ^ taoAlpha) .alpha))) :
    pmfProb (realClockPassageLaw (y ^ taoAlpha) upper.one_le_x .alpha hmass)
      {u | u.1 ∉ stageClockGoodEvent (y ^ taoAlpha) y} ≤
        400000 * (Real.log y) ^ (-(1 / 10 : ℝ)) := by
  let x := y ^ taoAlpha
  let μ := oddLogWindowOddNatPMF (realClockSourceLo x .alpha) (realClockSourceHi x .alpha) hmass
  have hy0 : 0 ≤ y := by linarith
  have hyx : y ≤ x := Real.self_le_rpow_of_one_le hy.le taoAlpha_one_lt.le
  have hmass₂ : 0 < logFinsetMass
      (oddLogWindow (realClockSourceLo y .alphaSq) (realClockSourceHi y .alphaSq)) := by
    simpa only [adjacent_real_sourceLo hy0, adjacent_real_sourceHi hy0] using hmass
  have hxerr : (μ.toOuterMeasure (realLocalClockGoodEvent x)ᶜ).toReal ≤
      200000 * (Real.log x) ^ (-(1 / 10 : ℝ)) := upper.clock_bound .alpha hmass
  have hyerr : (μ.toOuterMeasure (realLocalClockGoodEvent y)ᶜ).toReal ≤
      200000 * (Real.log y) ^ (-(1 / 10 : ℝ)) := by
    simpa only [μ, x, adjacent_real_sourceLo hy0, adjacent_real_sourceHi hy0] using
      lower.clock_bound .alphaSq hmass₂
  have hmono : (Real.log x) ^ (-(1 / 10 : ℝ)) ≤ (Real.log y) ^ (-(1 / 10 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos (Real.log_pos hy)
      (Real.log_le_log (by linarith) hyx) (by norm_num)
  have hsubset :
      {q : TaoOddNat | (syracusePassLocationRealFloorOrOne x q.1 upper.one_le_x).1 ∉ stageClockGoodEvent x y} ⊆
        (realLocalClockGoodEvent x)ᶜ ∪ (realLocalClockGoodEvent y)ᶜ := by
    intro q hq
    by_cases hqx : q ∈ realLocalClockGoodEvent x
    · right
      intro hqy
      exact hq (reference_stage_good_of_two_local_clocks upper.one_le_x lower.one_le_x hyx q hqx hqy)
    · exact Or.inl hqx
  rw [pmfProb_eq_toOuterMeasure_toReal, ← real_odd_source_map_passage_eq,
    PMF.toOuterMeasure_map_apply]
  change (μ.toOuterMeasure
    {q : TaoOddNat | (syracusePassLocationRealFloorOrOne x q.1 upper.one_le_x).1 ∉ stageClockGoodEvent x y}).toReal ≤ _
  have h1 := pmf_outer_probability_mono_support μ
    (fun q hq => hsubset hq.1)
  have h2 := pmf_outer_probability_union_le μ (realLocalClockGoodEvent x)ᶜ (realLocalClockGoodEvent y)ᶜ
  nlinarith

end CollatzClockAudit

#print axioms CollatzClockAudit.pmf_outer_mass_ne_top
#print axioms CollatzClockAudit.pmf_outer_probability_union_le
#print axioms CollatzClockAudit.pmf_outer_probability_biUnion_le
#print axioms CollatzClockAudit.reference_stage_good_of_two_local_clocks
#print axioms CollatzClockAudit.reference_stage_clock_bad_probability
