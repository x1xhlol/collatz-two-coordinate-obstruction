/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Probability.Geom2CenteredMoment
import Erdos1135SecondScale.Tao.Probability.Geom2ListProjectivity
import Erdos1135SecondScale.Tao.Section6.EventAggregation

/-!
# Geom(2) Concentration for Section 6 Intervals

This leaf transports the native centered Geom(2) tail to contiguous blocks,
indexes every nonempty half-open interval exactly once, and bounds the repaired
global typical-event failure mass.  The source list type remains infinite.
-/

open scoped BigOperators

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

/-- Dropping an iid prefix leaves the iid suffix law. -/
theorem geom2PNatListPMF_map_drop_eq (K N : ℕ) :
    (geom2PNatListPMF (K + N)).map (fun full => full.drop K) =
      geom2PNatListPMF N :=
  geom2PNatListPMF_map_drop_low_eq K N

/-- Every contiguous block inside a length-`n` iid list has its own iid law. -/
theorem geom2PNatListPMF_map_drop_take_eq_of_add_le
    {i r n : ℕ} (h : i + r ≤ n) :
    (geom2PNatListPMF n).map
        (fun full => (full.drop i).take r) =
      geom2PNatListPMF r := by
  have hi : i ≤ n := le_trans (Nat.le_add_right i r) h
  have hr : r ≤ n - i := Nat.le_sub_of_add_le (by omega)
  calc
    (geom2PNatListPMF n).map (fun full => (full.drop i).take r) =
        ((geom2PNatListPMF n).map (fun full => full.drop i)).map
          (fun block => block.take r) := by
            rw [PMF.map_comp]
            rfl
    _ = ((geom2PNatListPMF (i + (n - i))).map
          (fun full => full.drop i)).map (fun block => block.take r) := by
            rw [Nat.add_sub_of_le hi]
    _ = (geom2PNatListPMF (n - i)).map (fun block => block.take r) := by
      rw [geom2PNatListPMF_map_drop_eq]
    _ = geom2PNatListPMF r := geom2PNatListPMF_map_take_low_eq_of_le hr

/-- Zero-width interior-block marginal canary. -/
theorem geom2PNatListPMF_map_drop_take_zero
    (i n : ℕ) (hi : i ≤ n) :
    (geom2PNatListPMF n).map
        (fun full => (full.drop i).take 0) = geom2PNatListPMF 0 := by
  exact geom2PNatListPMF_map_drop_take_eq_of_add_le (by simpa using hi)

/-- Full-block marginal canary. -/
theorem geom2PNatListPMF_map_drop_take_full (n : ℕ) :
    (geom2PNatListPMF n).map
        (fun full => (full.drop 0).take n) = geom2PNatListPMF n := by
  exact geom2PNatListPMF_map_drop_take_eq_of_add_le (by simp)

/-- Length-one terminal-block canary. -/
theorem geom2PNatListPMF_map_drop_take_one :
    (geom2PNatListPMF 1).map
        (fun full => (full.drop 0).take 1) = geom2PNatListPMF 1 := by
  exact geom2PNatListPMF_map_drop_take_full 1

/-- Non-prefix direct-order pilot: retain the last two entries of a
length-three iid source list. -/
theorem geom2PNatListPMF_map_drop_one_take_two :
    (geom2PNatListPMF 3).map
        (fun full => (full.drop 1).take 2) = geom2PNatListPMF 2 := by
  exact geom2PNatListPMF_map_drop_take_eq_of_add_le (by norm_num)

/-- Failure mass of one iid block against the repaired Section 6 threshold. -/
noncomputable def taoSection6BlockFailureMass
    (CA : ℝ) (n r : ℕ) : ℝ :=
  ((geom2PNatListPMF r).toOuterMeasure
    {block | taoCor63PrefixError CA n r <
      |taoGeom2CenteredListWeight block|}).toReal

theorem taoSection6BlockFailureMass_nonneg (CA : ℝ) (n r : ℕ) :
    0 ≤ taoSection6BlockFailureMass CA n r :=
  ENNReal.toReal_nonneg

/-- Native Bernstein-form concentration for one nonempty block. -/
theorem taoSection6BlockFailureMass_le_min
    {CA : ℝ} {n r : ℕ} (hr : 0 < r)
    (herror : 0 < taoCor63PrefixError CA n r) :
    taoSection6BlockFailureMass CA n r ≤
      2 * Real.exp
        (-min
          (taoCor63PrefixError CA n r ^ 2 / (32 * (r : ℝ)))
          (taoCor63PrefixError CA n r / 8)) := by
  unfold taoSection6BlockFailureMass
  exact geom2PNatListPMF_centeredWeight_absTail_le_min hr herror

/-- The repaired square-root-plus-log threshold gives a uniform per-block
power exponent. -/
theorem taoSection6BlockFailureMass_le_exp
    {CA : ℝ} (hCA : 4 ≤ CA) {n r : ℕ} (hn : 2 ≤ n)
    (hr : 0 < r) :
    taoSection6BlockFailureMass CA n r ≤
      2 * Real.exp (-(CA * Real.log (n : ℝ) / 8)) := by
  have hlog : 0 < Real.log (n : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hrR : (0 : ℝ) < r := by exact_mod_cast hr
  let s : ℝ := Real.sqrt ((r : ℝ) * Real.log (n : ℝ))
  let lambda : ℝ := taoCor63PrefixError CA n r
  have hCA0 : 0 ≤ CA := by linarith
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hsSq : s ^ 2 = (r : ℝ) * Real.log (n : ℝ) := by
    dsimp [s]
    rw [Real.sq_sqrt]
    positivity
  have hlambda : lambda = CA * (s + Real.log (n : ℝ)) := by
    rfl
  have hlambda0 : 0 < lambda := by
    rw [hlambda]
    positivity
  have hlambdaLower : CA * s ≤ lambda := by
    rw [hlambda]
    nlinarith [mul_nonneg hCA0 hlog.le]
  have hlambdaSq : (CA * s) ^ 2 ≤ lambda ^ 2 :=
    pow_le_pow_left₀ (mul_nonneg hCA0 hs0) hlambdaLower 2
  have hCAsq : 4 * CA ≤ CA ^ 2 := by nlinarith
  have hbase :
      4 * CA * ((r : ℝ) * Real.log (n : ℝ)) ≤ (CA * s) ^ 2 := by
    calc
      4 * CA * ((r : ℝ) * Real.log (n : ℝ)) ≤
          CA ^ 2 * ((r : ℝ) * Real.log (n : ℝ)) := by
        exact mul_le_mul_of_nonneg_right hCAsq
          (mul_nonneg hrR.le hlog.le)
      _ = (CA * s) ^ 2 := by
        rw [mul_pow, hsSq]
  have hquadratic : CA * Real.log (n : ℝ) / 8 ≤
      lambda ^ 2 / (32 * (r : ℝ)) := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 8)
      (by positivity : (0 : ℝ) < 32 * r)]
    nlinarith [hbase.trans hlambdaSq]
  have hlinear : CA * Real.log (n : ℝ) / 8 ≤ lambda / 8 := by
    rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 8)
      (by norm_num : (0 : ℝ) < 8)]
    rw [hlambda]
    nlinarith [mul_nonneg hCA0 hs0]
  have hmin : CA * Real.log (n : ℝ) / 8 ≤
      min (lambda ^ 2 / (32 * (r : ℝ))) (lambda / 8) :=
    le_min hquadratic hlinear
  calc
    taoSection6BlockFailureMass CA n r ≤
        2 * Real.exp
          (-min (lambda ^ 2 / (32 * (r : ℝ))) (lambda / 8)) := by
      simpa [lambda] using taoSection6BlockFailureMass_le_min hr hlambda0
    _ ≤ 2 * Real.exp (-(CA * Real.log (n : ℝ) / 8)) := by
      apply mul_le_mul_of_nonneg_left _ (by norm_num)
      exact Real.exp_le_exp.mpr (by linarith)

/-- Length-first index for every nonempty interval in `[0,n)`.  Width `q+1`
has exactly `n-q` possible starts. -/
abbrev taoSection6IntervalIndex (n : ℕ) :=
  Σ q : Fin n, Fin (n - q.1)

namespace taoSection6IntervalIndex

def width {n : ℕ} (u : taoSection6IntervalIndex n) : ℕ := u.1.1 + 1

def start {n : ℕ} (u : taoSection6IntervalIndex n) : ℕ := u.2.1

def block {n : ℕ} (u : taoSection6IntervalIndex n)
    (full : List ℕ+) : List ℕ+ :=
  (full.drop u.start).take u.width

theorem start_add_width_le {n : ℕ} (u : taoSection6IntervalIndex n) :
    u.start + u.width ≤ n := by
  have hq := u.1.2
  have hs := u.2.2
  dsimp [start, width] at *
  omega

theorem width_pos {n : ℕ} (u : taoSection6IntervalIndex n) :
    0 < u.width := by
  simp [width]

end taoSection6IntervalIndex

/-- Centering a retained interior block agrees with the source interval
weight when the full list has its supported length. -/
theorem taoGeom2CenteredListWeight_drop_take
    {full : List ℕ+} {i r n : ℕ} (hlen : full.length = n)
    (hir : i + r ≤ n) :
    taoGeom2CenteredListWeight ((full.drop i).take r) =
      ((taoSection6IntervalWeight full i (i + r) : ℕ) : ℝ) -
        2 * (r : ℝ) := by
  have hi : i ≤ full.length := by omega
  have hr : r ≤ (full.drop i).length := by
    simp [List.length_drop, hlen]
    omega
  have hweight :
      taoTupleWeight ((full.drop i).take r) =
        taoSection6IntervalWeight full i (i + r) := by
    unfold taoTupleWeight taoSection6IntervalWeight
    rw [Nat.add_sub_cancel_left]
    rw [List.bind_eq_flatMap]
    rw [show (fun a : ℕ => a) = id by rfl, List.map_id]
    change
      (List.flatMap (fun a : ℕ+ => [(a : ℕ)])
        ((full.drop i).take r)).sum = _
    rw [← List.map_eq_flatMap]
  unfold taoGeom2CenteredListWeight
  rw [hweight]
  rw [List.length_take_of_le hr]

/-- Bad-event predicate for one indexed interval. -/
noncomputable def taoSection6IntervalBad
    (CA : ℝ) (n : ℕ) (u : taoSection6IntervalIndex n)
    (full : List ℕ+) : Prop :=
  taoCor63PrefixError CA n u.width <
    |taoGeom2CenteredListWeight (u.block full)|

/-- Every indexed block has the corresponding iid block law. -/
theorem geom2PNatListPMF_map_intervalBlock_eq
    {n : ℕ} (u : taoSection6IntervalIndex n) :
    (geom2PNatListPMF n).map u.block =
      geom2PNatListPMF u.width := by
  exact geom2PNatListPMF_map_drop_take_eq_of_add_le u.start_add_width_le

/-- One indexed interval has exactly the width-only block failure mass. -/
theorem taoSection6IntervalBad_outerMeasure_toReal
    (CA : ℝ) {n : ℕ} (u : taoSection6IntervalIndex n) :
    ((geom2PNatListPMF n).toOuterMeasure
        {full | taoSection6IntervalBad CA n u full}).toReal =
      taoSection6BlockFailureMass CA n u.width := by
  unfold taoSection6BlockFailureMass taoSection6IntervalBad
  rw [← geom2PNatListPMF_map_intervalBlock_eq u]
  rw [PMF.toOuterMeasure_map_apply]
  rfl

/-- The iid exact-length law gives zero mass to the wrong-length branch of
the global event complement. -/
theorem geom2PNatListPMF_wrongLength_outerMeasure_zero (n : ℕ) :
    (geom2PNatListPMF n).toOuterMeasure
        {full : List ℕ+ | full.length ≠ n} = 0 := by
  rw [PMF.toOuterMeasure_apply_eq_zero_iff]
  rw [Set.disjoint_left]
  intro full hsupport hlength
  have hne : geom2PNatListPMF n full ≠ 0 :=
    ((geom2PNatListPMF n).mem_support_iff full).mp hsupport
  exact hne (geom2PNatListPMF_apply_eq_zero_of_length_ne n full hlength)

/-- The complement of global typicality is covered by the zero-mass
wrong-length event and the finite family of indexed bad intervals. -/
theorem taoSection6GlobalTypical_compl_subset
    (CA : ℝ) (n : ℕ) :
    {full | ¬ taoSection6GlobalTypical CA n full} ⊆
      {full : List ℕ+ | full.length ≠ n} ∪
        ⋃ u : taoSection6IntervalIndex n,
          {full | taoSection6IntervalBad CA n u full} := by
  intro full hfail
  by_cases hlen : full.length = n
  · right
    have hntyp : ¬ taoCor63StarInclusiveTypical CA n full := by
      intro htyp
      exact hfail ⟨hlen, htyp⟩
    simp only [taoCor63StarInclusiveTypical] at hntyp
    push_neg at hntyp
    obtain ⟨i, j, hij, hj, hbad⟩ := hntyp
    let r : ℕ := j - i
    have hr : 0 < r := Nat.sub_pos_of_lt hij
    have hir : i + r = j := Nat.add_sub_of_le hij.le
    let q : Fin n := ⟨r - 1, by omega⟩
    let s : Fin (n - q.1) := ⟨i, by
      dsimp [q]
      omega⟩
    let u : taoSection6IntervalIndex n := ⟨q, s⟩
    apply Set.mem_iUnion.mpr
    refine ⟨u, ?_⟩
    have huwidth : u.width = r := by
      dsimp [u, q, taoSection6IntervalIndex.width]
      omega
    have hustart : u.start = i := by rfl
    change taoCor63PrefixError CA n u.width <
      |taoGeom2CenteredListWeight (u.block full)|
    rw [huwidth]
    rw [show u.block full = (full.drop i).take r by
      simp [taoSection6IntervalIndex.block, hustart, huwidth]]
    rw [taoGeom2CenteredListWeight_drop_take hlen (by omega)]
    simpa [taoCor63PrefixError,
      Real.sqrt_mul (show 0 ≤ (r : ℝ) by positivity), r, hir] using hbad
  · exact Set.mem_union_left _ hlen

/-- Global failure mass is at most the finite sum of width-indexed block
failure masses. -/
theorem taoSection6GlobalFailureMass_le_intervalSum
    (CA : ℝ) (n : ℕ) :
    taoSection6GlobalFailureMass CA n ≤
      ∑ u : taoSection6IntervalIndex n,
        taoSection6BlockFailureMass CA n u.width := by
  let p := geom2PNatListPMF n
  let Wrong : Set (List ℕ+) := {full | full.length ≠ n}
  let Bad : taoSection6IntervalIndex n → Set (List ℕ+) :=
    fun u => {full | taoSection6IntervalBad CA n u full}
  have hnative :
      p.toOuterMeasure {full | ¬ taoSection6GlobalTypical CA n full} ≤
        ∑ u : taoSection6IntervalIndex n, p.toOuterMeasure (Bad u) := by
    calc
      p.toOuterMeasure {full | ¬ taoSection6GlobalTypical CA n full} ≤
          p.toOuterMeasure (Wrong ∪ ⋃ u, Bad u) :=
        p.toOuterMeasure.mono (by
          simpa [p, Wrong, Bad] using
            taoSection6GlobalTypical_compl_subset CA n)
      _ ≤ p.toOuterMeasure Wrong + p.toOuterMeasure (⋃ u, Bad u) :=
        MeasureTheory.measure_union_le _ _
      _ = p.toOuterMeasure (⋃ u, Bad u) := by
        rw [show p.toOuterMeasure Wrong = 0 by
          simpa [p, Wrong] using
            geom2PNatListPMF_wrongLength_outerMeasure_zero n]
        simp
      _ ≤ ∑ u : taoSection6IntervalIndex n, p.toOuterMeasure (Bad u) :=
        MeasureTheory.measure_iUnion_fintype_le _ _
  have htermfinite (u : taoSection6IntervalIndex n) :
      p.toOuterMeasure (Bad u) ≠ ⊤ := by
    apply ne_of_lt
    calc
      p.toOuterMeasure (Bad u) ≤ p.toOuterMeasure Set.univ :=
        p.toOuterMeasure.mono (Set.subset_univ _)
      _ = 1 := (p.toOuterMeasure_apply_eq_one_iff Set.univ).2
        (Set.subset_univ _)
      _ < ⊤ := ENNReal.one_lt_top
  have hfinite :
      (∑ u : taoSection6IntervalIndex n, p.toOuterMeasure (Bad u)) ≠ ⊤ := by
    rw [ENNReal.sum_ne_top]
    intro u hu
    exact htermfinite u
  have hreal := ENNReal.toReal_mono hfinite hnative
  have hsumReal :
      (∑ u : taoSection6IntervalIndex n, p.toOuterMeasure (Bad u)).toReal =
        ∑ u : taoSection6IntervalIndex n,
          (p.toOuterMeasure (Bad u)).toReal := by
    rw [ENNReal.toReal_sum]
    intro u hu
    exact htermfinite u
  rw [hsumReal] at hreal
  unfold taoSection6GlobalFailureMass
  calc
    ((geom2PNatListPMF n).toOuterMeasure
        {full | ¬ taoSection6GlobalTypical CA n full}).toReal ≤
      ∑ u : taoSection6IntervalIndex n,
        (p.toOuterMeasure (Bad u)).toReal := by
          simpa [ENNReal.toReal_sum] using hreal
    _ = ∑ u : taoSection6IntervalIndex n,
        taoSection6BlockFailureMass CA n u.width := by
      apply Finset.sum_congr rfl
      intro u hu
      simpa [p, Bad] using taoSection6IntervalBad_outerMeasure_toReal CA u

/-- There are at most `n^2` nonempty half-open intervals in `[0,n)`. -/
theorem taoSection6IntervalIndex_card_le_sq (n : ℕ) :
    Fintype.card (taoSection6IntervalIndex n) ≤ n ^ 2 := by
  rw [Fintype.card_sigma]
  simp only [Fintype.card_fin]
  calc
    ∑ q : Fin n, (n - q.1) ≤ ∑ _q : Fin n, n := by
      apply Finset.sum_le_sum
      intro q hq
      omega
    _ = n ^ 2 := by simp [pow_two]

/-- Union over all nonempty intervals costs at most the coarse `n^2` ledger. -/
theorem taoSection6GlobalFailureMass_le_sq_mul_exp
    {CA : ℝ} (hCA : 4 ≤ CA) {n : ℕ} (hn : 2 ≤ n) :
    taoSection6GlobalFailureMass CA n ≤
      (n : ℝ) ^ 2 * (2 * Real.exp (-(CA * Real.log (n : ℝ) / 8))) := by
  let B : ℝ := 2 * Real.exp (-(CA * Real.log (n : ℝ) / 8))
  have hcard :
      ((Fintype.card (taoSection6IntervalIndex n) : ℕ) : ℝ) ≤
        (n : ℝ) ^ 2 := by
    exact_mod_cast taoSection6IntervalIndex_card_le_sq n
  calc
    taoSection6GlobalFailureMass CA n ≤
        ∑ u : taoSection6IntervalIndex n,
          taoSection6BlockFailureMass CA n u.width :=
      taoSection6GlobalFailureMass_le_intervalSum CA n
    _ ≤ ∑ _u : taoSection6IntervalIndex n, B := by
      apply Finset.sum_le_sum
      intro u hu
      exact taoSection6BlockFailureMass_le_exp hCA hn u.width_pos
    _ = ((Fintype.card (taoSection6IntervalIndex n) : ℕ) : ℝ) * B := by
      simp
    _ ≤ (n : ℝ) ^ 2 * B :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = (n : ℝ) ^ 2 *
        (2 * Real.exp (-(CA * Real.log (n : ℝ) / 8))) := rfl

/-- Choosing `C_A = 8(A+4)` absorbs the interval ledger and gives an arbitrary
natural power of exceptional-mass decay. -/
theorem taoSection6GlobalFailureMass_le_inv_pow
    (A : ℕ) {n : ℕ} (hn : 2 ≤ n) :
    taoSection6GlobalFailureMass (8 * ((A : ℝ) + 4)) n ≤
      1 / (n : ℝ) ^ (A + 1) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hA0 : (0 : ℝ) ≤ A := Nat.cast_nonneg A
  have hCA : (4 : ℝ) ≤ 8 * ((A : ℝ) + 4) := by nlinarith
  have hexp :
      Real.exp
          (-((8 * ((A : ℝ) + 4)) * Real.log (n : ℝ) / 8)) =
        1 / (n : ℝ) ^ (A + 4) := by
    rw [show
      -((8 * ((A : ℝ) + 4)) * Real.log (n : ℝ) / 8) =
        -(((A + 4 : ℕ) : ℝ) * Real.log (n : ℝ)) by
          push_cast
          ring]
    rw [Real.exp_neg, Real.exp_nat_mul, Real.exp_log hnR]
    simp [one_div]
  have hpow4 : (0 : ℝ) < (n : ℝ) ^ (A + 4) := pow_pos hnR _
  have hpow1 : (0 : ℝ) < (n : ℝ) ^ (A + 1) := pow_pos hnR _
  have hpowSplit :
      (n : ℝ) ^ (A + 4) =
        (n : ℝ) ^ (A + 1) * (n : ℝ) ^ 3 := by
    rw [show A + 4 = (A + 1) + 3 by omega, pow_add]
  calc
    taoSection6GlobalFailureMass (8 * ((A : ℝ) + 4)) n ≤
        (n : ℝ) ^ 2 *
          (2 * Real.exp
            (-((8 * ((A : ℝ) + 4)) * Real.log (n : ℝ) / 8))) :=
      taoSection6GlobalFailureMass_le_sq_mul_exp hCA hn
    _ = (2 * (n : ℝ) ^ 2) / (n : ℝ) ^ (A + 4) := by
      rw [hexp]
      ring
    _ ≤ 1 / (n : ℝ) ^ (A + 1) := by
      rw [div_le_div_iff₀ hpow4 hpow1]
      have hnTwo : (2 : ℝ) ≤ n := by exact_mod_cast hn
      have hbase : 2 * (n : ℝ) ^ 2 ≤ (n : ℝ) ^ 3 := by
        nlinarith [sq_nonneg (n : ℝ)]
      calc
        (2 * (n : ℝ) ^ 2) * (n : ℝ) ^ (A + 1) =
            (n : ℝ) ^ (A + 1) * (2 * (n : ℝ) ^ 2) := by ring
        _ ≤ (n : ℝ) ^ (A + 1) * (n : ℝ) ^ 3 :=
          mul_le_mul_of_nonneg_left hbase hpow1.le
        _ = 1 * (n : ℝ) ^ (A + 4) := by rw [hpowSplit]; ring

end

end Tao
end Erdos1135SecondScale
