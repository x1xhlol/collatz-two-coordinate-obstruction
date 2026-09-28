import Erdos1135.Tao.Probability.Geom2CenteredMoment
import Erdos1135.Tao.Syracuse.TruncatedValuationGeom2

/-!
# Ideal Geom(2) overflow tail for Proposition 1.9

This leaf identifies the strict truncation overflow atom with the exact
Geom(2) weight event on PMF support and proves its positive-length
real-exponential decay under the Proposition 1.9 scale relation.
-/

namespace Erdos1135
namespace Tao

noncomputable section

/-- Chernoff parameter used by the Proposition 1.9 ideal overflow tail. -/
noncomputable def taoProp19TailParameter (c0 : ℝ) : ℝ :=
  min (c0 / 32) (1 / 4)

/-- Output decay exponent, depending only on the input scale gap `c0`. -/
noncomputable def taoProp19DecayExponent (c0 : ℝ) : ℝ :=
  c0 * taoProp19TailParameter c0 / 4

theorem taoProp19TailParameter_pos {c0 : ℝ} (hc0 : 0 < c0) :
    0 < taoProp19TailParameter c0 := by
  rw [taoProp19TailParameter, lt_min_iff]
  constructor <;> positivity

theorem taoProp19TailParameter_le_quarter (c0 : ℝ) :
    taoProp19TailParameter c0 ≤ 1 / 4 := by
  exact min_le_right _ _

theorem taoProp19TailParameter_le_div_thirtyTwo (c0 : ℝ) :
    taoProp19TailParameter c0 ≤ c0 / 32 := by
  exact min_le_left _ _

theorem taoProp19DecayExponent_pos {c0 : ℝ} (hc0 : 0 < c0) :
    0 < taoProp19DecayExponent c0 := by
  unfold taoProp19DecayExponent
  exact div_pos (mul_pos hc0 (taoProp19TailParameter_pos hc0)) (by norm_num)

theorem truncateValuationList_eq_none_iff_of_geom2_support
    {n M : ℕ} {as : List ℕ+}
    (has : as ∈ (geom2PNatListPMF n).support) :
    truncateValuationList n M as = none ↔
      M ≤ taoTupleWeight as := by
  exact truncateValuationList_eq_none_iff_of_length
    (geom2PNatListPMF_support_length_eq has)

/-- The ideal strict-overflow atom is exactly the Geom(2) mass of total
valuation weight at least the cutoff.  The support intersection is essential:
wrong-length lists also pack to `none`, but have zero ideal mass. -/
theorem truncatedValuationTupleGeom2PMF_apply_none_eq_weightEvent
    (n M : ℕ) :
    truncatedValuationTupleGeom2PMF n M none =
      (geom2PNatListPMF n).toOuterMeasure
        {as : List ℕ+ | M ≤ taoTupleWeight as} := by
  rw [← geom2PNatListPMF_map_truncateValuationList n M]
  rw [← PMF.toOuterMeasure_apply_singleton]
  rw [PMF.toOuterMeasure_map_apply]
  apply (geom2PNatListPMF n).toOuterMeasure_apply_eq_of_inter_support_eq
  ext as
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff,
    Set.mem_setOf_eq]
  constructor
  · rintro ⟨hpack, has⟩
    exact ⟨(truncateValuationList_eq_none_iff_of_geom2_support has).mp hpack,
      has⟩
  · rintro ⟨hweight, has⟩
    exact ⟨(truncateValuationList_eq_none_iff_of_geom2_support has).mpr hweight,
      has⟩

/-- On exact-length support, strict overflow enters a strict centered tail at
half the available `c0*n` gap. -/
theorem taoProp19_supported_overflow_centeredWeight_gt
    {c0 : ℝ} {n M : ℕ} (hc0 : 0 < c0) (hn : 0 < n)
    (hscale : ((2 : ℝ) + c0) * (n : ℝ) ≤ (M : ℝ))
    {as : List ℕ+} (has : as ∈ (geom2PNatListPMF n).support)
    (hoverflow : M ≤ taoTupleWeight as) :
    (c0 / 2) * (n : ℝ) < taoGeom2CenteredListWeight as := by
  have hlength : as.length = n := geom2PNatListPMF_support_length_eq has
  have hoverflowReal : (M : ℝ) ≤ (taoTupleWeight as : ℕ) := by
    exact_mod_cast hoverflow
  have hnReal : 0 < (n : ℝ) := by exact_mod_cast hn
  have hgap : 0 < c0 * (n : ℝ) := mul_pos hc0 hnReal
  unfold taoGeom2CenteredListWeight
  rw [hlength]
  nlinarith

private theorem taoProp19TailExponent_le
    {c0 : ℝ} (hc0 : 0 < c0) (n : ℕ) :
    -taoProp19TailParameter c0 * ((c0 / 2) * (n : ℝ)) +
        8 * taoProp19TailParameter c0 ^ 2 * (n : ℝ) ≤
      -(taoProp19DecayExponent c0 * (n : ℝ)) := by
  let t := taoProp19TailParameter c0
  have ht : 0 ≤ t := (taoProp19TailParameter_pos hc0).le
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hcoef : 8 * t ≤ c0 / 4 := by
    have htbound : t ≤ c0 / 32 := by
      simpa [t] using taoProp19TailParameter_le_div_thirtyTwo c0
    nlinarith
  have hnonpos : t * (n : ℝ) * (8 * t - c0 / 4) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (mul_nonneg ht hn)
      (sub_nonpos.mpr hcoef)
  change -t * ((c0 / 2) * (n : ℝ)) + 8 * t ^ 2 * (n : ℝ) ≤
    -(c0 * t / 4 * (n : ℝ))
  nlinarith

/-- Positive-length ideal overflow bound at the source scale. -/
theorem truncatedValuationTupleGeom2PMF_none_le_exp
    {c0 : ℝ} {n M : ℕ} (hc0 : 0 < c0) (hn : 0 < n)
    (hscale : ((2 : ℝ) + c0) * (n : ℝ) ≤ (M : ℝ)) :
    (truncatedValuationTupleGeom2PMF n M none).toReal ≤
      Real.exp (-(taoProp19DecayExponent c0 * (n : ℝ))) := by
  let E : Set (List ℕ+) :=
    {as | (c0 / 2) * (n : ℝ) < taoGeom2CenteredListWeight as}
  have hfinite : (geom2PNatListPMF n).toOuterMeasure E ≠ ⊤ := by
    apply ne_of_lt
    calc
      (geom2PNatListPMF n).toOuterMeasure E ≤
          (geom2PNatListPMF n).toOuterMeasure Set.univ :=
        (geom2PNatListPMF n).toOuterMeasure.mono (Set.subset_univ E)
      _ = 1 := ((geom2PNatListPMF n).toOuterMeasure_apply_eq_one_iff
        Set.univ).2 (Set.subset_univ _)
      _ < ⊤ := ENNReal.one_lt_top
  have hnative :
      (geom2PNatListPMF n).toOuterMeasure
          {as : List ℕ+ | M ≤ taoTupleWeight as} ≤
        (geom2PNatListPMF n).toOuterMeasure E := by
    apply (geom2PNatListPMF n).toOuterMeasure_mono
    rintro as ⟨hoverflow, has⟩
    exact taoProp19_supported_overflow_centeredWeight_gt
      hc0 hn hscale has hoverflow
  have hreal := ENNReal.toReal_mono hfinite hnative
  rw [← truncatedValuationTupleGeom2PMF_apply_none_eq_weightEvent n M] at hreal
  have htail := geom2PNatListPMF_centeredWeight_upperTail_le
    n (t := taoProp19TailParameter c0)
      (lambda := (c0 / 2) * (n : ℝ))
      (taoProp19TailParameter_pos hc0)
      (taoProp19TailParameter_le_quarter c0)
  change ((geom2PNatListPMF n).toOuterMeasure E).toReal ≤ _ at htail
  exact hreal.trans (htail.trans (Real.exp_le_exp.mpr
    (taoProp19TailExponent_le hc0 n)))

theorem taoProp19TailParameter_one :
    taoProp19TailParameter 1 = 1 / 32 := by
  norm_num [taoProp19TailParameter]

theorem taoProp19TailParameter_eight :
    taoProp19TailParameter 8 = 1 / 4 := by
  norm_num [taoProp19TailParameter]

theorem taoProp19DecayExponent_one :
    taoProp19DecayExponent 1 = 1 / 128 := by
  norm_num [taoProp19DecayExponent, taoProp19TailParameter]

/-- Minimal source-scale pilot: at `n=1`, `c0=1`, the cutoff `M=3`
retains the strict equality-overflow boundary and yields the quadratic rate. -/
theorem truncatedValuationTupleGeom2PMF_one_three_none_le_exp :
    (truncatedValuationTupleGeom2PMF 1 3 none).toReal ≤
      Real.exp (-(1 / 128 : ℝ)) := by
  simpa [taoProp19DecayExponent_one] using
    (truncatedValuationTupleGeom2PMF_none_le_exp
      (c0 := (1 : ℝ)) (n := 1) (M := 3) (by norm_num) (by norm_num)
      (by norm_num))

end

end Tao
end Erdos1135
