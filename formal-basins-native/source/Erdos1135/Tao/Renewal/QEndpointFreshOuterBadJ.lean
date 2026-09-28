import Erdos1135.Tao.Renewal.HoldListHorizontalTail
import Erdos1135.Tao.Renewal.QEndpointFreshMarginals
import Erdos1135.Tao.Renewal.CanonicalFirstPassageTails
import Erdos1135.Tao.Fourier.Section7Geometry

/-!
# Canonical Endpoint/Fresh Large-Horizontal Tail

This leaf transports the canonical first-passage and iid Hold-list horizontal
tails to the prefix and fresh suffix of the endpoint/fresh carrier, then
combines them into the inclusive outer (7.54) event.
-/

namespace Erdos1135
namespace Tao

noncomputable section

open TaoSection7Lemma77

namespace TaoSection7Case3SourceStoppingRun
namespace Lemma79TailExpectation

/-- The exact positive margin between the outer `(7.54)` prefix threshold
`4m/5` and the Lemma 7.7 first-passage center. -/
theorem lemma79CanonicalPreHorizontalMargin_pos :
    0 < (4 / 5 : ℝ) - (Real.log 9 / Real.log 2) / 4 :=
  sub_pos.mpr taoSection7_log9_div_log2_div_four_lt_four_fifths

/-- Under Tao's current-scale gap bound, the inclusive prefix part of the
outer `(7.54)` split lies in the canonical two-sided horizontal tail. -/
theorem lemma79CanonicalPreHorizontalEvent_subset_deviation
    {gap m : ℕ}
    (hgap :
      (gap : ℝ) ≤ (Real.log 9 / Real.log 2) * (m : ℝ)) :
    {r : ℕ | 4 * m ≤ 5 * r} ⊆
      lemma77CanonicalHorizontalDeviationEvent gap
        (((4 / 5 : ℝ) - (Real.log 9 / Real.log 2) / 4) * (m : ℝ)) := by
  intro r hr
  have hrReal : (4 : ℝ) * (m : ℝ) ≤ 5 * (r : ℝ) := by
    exact_mod_cast hr
  have hcenter :
      ((4 / 5 : ℝ) - (Real.log 9 / Real.log 2) / 4) * (m : ℝ) ≤
        (r : ℝ) - (gap : ℝ) / 4 := by
    nlinarith
  change
    ((4 / 5 : ℝ) - (Real.log 9 / Real.log 2) / 4) * (m : ℝ) ≤
      |(r : ℝ) - (gap : ℝ) / 4|
  exact hcenter.trans (le_abs_self _)

/-- Canonical first-passage prefix tail on the endpoint/fresh carrier. -/
theorem lemma79CanonicalEndpointFreshPMF_preHorizontalTail_outerMeasure_le :
    ∃ Kh ah bh : ℝ, 0 < Kh ∧ 0 < ah ∧ 0 < bh ∧
      ∀ (J : ℕ) (entry : TaoSection7RenewalPoint) (gap m : ℕ),
        (gap : ℝ) ≤ (Real.log 9 / Real.log 2) * (m : ℝ) →
        (lemma79CanonicalEndpointFreshPMF J entry gap).toOuterMeasure
            {atom | 4 * m ≤ 5 * atom.1.1} ≤
          ENNReal.ofReal
            (Kh *
              (Real.exp
                  (-ah *
                    ((((4 / 5 : ℝ) - (Real.log 9 / Real.log 2) / 4) *
                        (m : ℝ)) ^ 2 / (1 + (gap : ℝ)))) +
                Real.exp
                  (-bh *
                    (((4 / 5 : ℝ) - (Real.log 9 / Real.log 2) / 4) *
                      (m : ℝ))))) := by
  rcases lemma77CanonicalFirstPassageHorizontalPMF_deviationTail_commonConstants
    with ⟨Kh, ah, bh, hKh, hah, hbh, htail⟩
  refine ⟨Kh, ah, bh, hKh, hah, hbh, ?_⟩
  intro J entry gap m hgap
  let t : ℝ :=
    ((4 / 5 : ℝ) - (Real.log 9 / Real.log 2) / 4) * (m : ℝ)
  let project : ((ℕ × ℤ) × List TaoSection7RenewalPoint) → ℕ :=
    fun atom => atom.1.1
  have ht : 0 ≤ t := by
    dsimp [t]
    exact mul_nonneg lemma79CanonicalPreHorizontalMargin_pos.le
      (Nat.cast_nonneg m)
  have hsubset :
      {atom : (ℕ × ℤ) × List TaoSection7RenewalPoint |
          4 * m ≤ 5 * atom.1.1} ⊆
        project ⁻¹' lemma77CanonicalHorizontalDeviationEvent gap t := by
    intro atom hatom
    exact lemma79CanonicalPreHorizontalEvent_subset_deviation hgap hatom
  calc
    (lemma79CanonicalEndpointFreshPMF J entry gap).toOuterMeasure
        {atom | 4 * m ≤ 5 * atom.1.1} ≤
      (lemma79CanonicalEndpointFreshPMF J entry gap).toOuterMeasure
        (project ⁻¹' lemma77CanonicalHorizontalDeviationEvent gap t) :=
      (lemma79CanonicalEndpointFreshPMF J entry gap).toOuterMeasure.mono hsubset
    _ = (lemma77CanonicalFirstPassageHorizontalPMF entry gap).toOuterMeasure
        (lemma77CanonicalHorizontalDeviationEvent gap t) := by
      rw [← PMF.toOuterMeasure_map_apply]
      rw [show (lemma79CanonicalEndpointFreshPMF J entry gap).map project =
          lemma77CanonicalFirstPassageHorizontalPMF entry gap by
        simpa [project] using
          lemma79CanonicalEndpointFreshPMF_map_horizontal_eq J entry gap]
    _ ≤ ENNReal.ofReal
        (Kh *
          (Real.exp (-ah * (t ^ 2 / (1 + (gap : ℝ)))) +
            Real.exp (-bh * t))) := htail entry gap t ht
    _ = ENNReal.ofReal
        (Kh *
          (Real.exp
              (-ah *
                ((((4 / 5 : ℝ) - (Real.log 9 / Real.log 2) / 4) *
                    (m : ℝ)) ^ 2 / (1 + (gap : ℝ)))) +
            Real.exp
              (-bh *
                (((4 / 5 : ℝ) - (Real.log 9 / Real.log 2) / 4) *
                  (m : ℝ))))) := by rfl

theorem lemma79CanonicalEndpointFreshPMF_suffixHorizontalTail_outerMeasure_le
    {P J : ℕ} (hPJ : P ≤ J)
    (entry : TaoSection7RenewalPoint) (gap m : ℕ) :
    (lemma79CanonicalEndpointFreshPMF J entry gap).toOuterMeasure
        {atom |
          m ≤ 10 * lemma77HoldPrefixHorizontalDelta P atom.2} ≤
      ENNReal.ofReal
        (Real.exp (((P : ℝ) / 2) - ((m : ℝ) / 160))) := by
  let project : ((ℕ × ℤ) × List TaoSection7RenewalPoint) →
      List TaoSection7RenewalPoint := fun atom => atom.2.take P
  let Event : Set (List TaoSection7RenewalPoint) :=
    {fresh | m ≤ 10 * lemma77HoldPrefixHorizontalDelta P fresh}
  have hset :
      {atom : (ℕ × ℤ) × List TaoSection7RenewalPoint |
          m ≤ 10 * lemma77HoldPrefixHorizontalDelta P atom.2} =
        project ⁻¹' Event := by
    ext atom
    simp only [Set.mem_setOf_eq, Set.mem_preimage]
    exact iff_of_eq (congrArg (fun q => m ≤ 10 * q)
      (lemma79HoldPrefixHorizontalDelta_take P atom.2).symm)
  rw [hset]
  rw [← PMF.toOuterMeasure_map_apply]
  rw [show (lemma79CanonicalEndpointFreshPMF J entry gap).map project =
      taoSection7HoldListPMF P by
    simpa [project] using
      (lemma79CanonicalEndpointFreshPMF_map_fresh_take_eq_of_le
        hPJ entry gap)]
  exact taoSection7HoldListPMF_horizontalTail_outerMeasure_le P m

theorem lemma79CanonicalEndpointFreshPMF_suffixHorizontalTail_toReal_le
    {P J : ℕ} (hPJ : P ≤ J)
    (entry : TaoSection7RenewalPoint) (gap m : ℕ) :
    ((lemma79CanonicalEndpointFreshPMF J entry gap).toOuterMeasure
        {atom |
          m ≤ 10 * lemma77HoldPrefixHorizontalDelta P atom.2}).toReal ≤
      Real.exp (((P : ℝ) / 2) - ((m : ℝ) / 160)) := by
  calc
    ((lemma79CanonicalEndpointFreshPMF J entry gap).toOuterMeasure
        {atom |
          m ≤ 10 * lemma77HoldPrefixHorizontalDelta P atom.2}).toReal ≤
      (ENNReal.ofReal
        (Real.exp (((P : ℝ) / 2) - ((m : ℝ) / 160)))).toReal :=
      ENNReal.toReal_mono ENNReal.ofReal_ne_top
        (lemma79CanonicalEndpointFreshPMF_suffixHorizontalTail_outerMeasure_le
          hPJ entry gap m)
    _ = Real.exp (((P : ℝ) / 2) - ((m : ℝ) / 160)) :=
      ENNReal.toReal_ofReal (Real.exp_nonneg _)

/-- Full inclusive outer `(7.54)` large-horizontal event on the canonical
endpoint/fresh carrier, bounded by its prefix and fresh-suffix tails. -/
theorem lemma79CanonicalEndpointFreshPMF_outerBadJ_outerMeasure_le :
    ∃ Kh ah bh : ℝ, 0 < Kh ∧ 0 < ah ∧ 0 < bh ∧
      ∀ {P J : ℕ}, P ≤ J →
        ∀ (entry : TaoSection7RenewalPoint) (gap m : ℕ),
          (gap : ℝ) ≤ (Real.log 9 / Real.log 2) * (m : ℝ) →
          (lemma79CanonicalEndpointFreshPMF J entry gap).toOuterMeasure
              {atom |
                9 * m ≤ 10 *
                  (atom.1.1 + lemma77HoldPrefixHorizontalDelta P atom.2)} ≤
            ENNReal.ofReal
                (Kh *
                  (Real.exp
                      (-ah *
                        ((((4 / 5 : ℝ) -
                              (Real.log 9 / Real.log 2) / 4) * (m : ℝ)) ^ 2 /
                          (1 + (gap : ℝ)))) +
                    Real.exp
                      (-bh *
                        (((4 / 5 : ℝ) -
                            (Real.log 9 / Real.log 2) / 4) * (m : ℝ))))) +
              ENNReal.ofReal
                (Real.exp (((P : ℝ) / 2) - ((m : ℝ) / 160))) := by
  rcases lemma79CanonicalEndpointFreshPMF_preHorizontalTail_outerMeasure_le
    with ⟨Kh, ah, bh, hKh, hah, hbh, hpre⟩
  refine ⟨Kh, ah, bh, hKh, hah, hbh, ?_⟩
  intro P J hPJ entry gap m hgap
  let μ := lemma79CanonicalEndpointFreshPMF J entry gap
  let OuterBadJ : Set ((ℕ × ℤ) × List TaoSection7RenewalPoint) :=
    {atom |
      9 * m ≤ 10 *
        (atom.1.1 + lemma77HoldPrefixHorizontalDelta P atom.2)}
  let BadPre : Set ((ℕ × ℤ) × List TaoSection7RenewalPoint) :=
    {atom | 4 * m ≤ 5 * atom.1.1}
  let BadSuf : Set ((ℕ × ℤ) × List TaoSection7RenewalPoint) :=
    {atom | m ≤ 10 * lemma77HoldPrefixHorizontalDelta P atom.2}
  have hsubset : OuterBadJ ⊆ BadPre ∪ BadSuf := by
    intro atom hatom
    by_cases hbadPre : 4 * m ≤ 5 * atom.1.1
    · exact Or.inl hbadPre
    · right
      dsimp [OuterBadJ] at hatom
      dsimp [BadSuf]
      omega
  calc
    μ.toOuterMeasure OuterBadJ ≤ μ.toOuterMeasure (BadPre ∪ BadSuf) :=
      μ.toOuterMeasure.mono hsubset
    _ ≤ μ.toOuterMeasure BadPre + μ.toOuterMeasure BadSuf :=
      MeasureTheory.measure_union_le BadPre BadSuf
    _ ≤ ENNReal.ofReal
            (Kh *
              (Real.exp
                  (-ah *
                    ((((4 / 5 : ℝ) - (Real.log 9 / Real.log 2) / 4) *
                        (m : ℝ)) ^ 2 / (1 + (gap : ℝ)))) +
                Real.exp
                  (-bh *
                    (((4 / 5 : ℝ) - (Real.log 9 / Real.log 2) / 4) *
                      (m : ℝ))))) +
          ENNReal.ofReal
            (Real.exp (((P : ℝ) / 2) - ((m : ℝ) / 160))) := by
      exact add_le_add
        (by simpa [μ, BadPre] using hpre J entry gap m hgap)
        (by simpa [μ, BadSuf] using
          (lemma79CanonicalEndpointFreshPMF_suffixHorizontalTail_outerMeasure_le
            (P := P) (J := J) hPJ entry gap m))
    _ = ENNReal.ofReal
            (Kh *
              (Real.exp
                  (-ah *
                    ((((4 / 5 : ℝ) -
                          (Real.log 9 / Real.log 2) / 4) * (m : ℝ)) ^ 2 /
                      (1 + (gap : ℝ)))) +
                Real.exp
                  (-bh *
                    (((4 / 5 : ℝ) -
                        (Real.log 9 / Real.log 2) / 4) * (m : ℝ))))) +
          ENNReal.ofReal
            (Real.exp (((P : ℝ) / 2) - ((m : ℝ) / 160))) := by rfl

/-- Safe real projection of the full canonical outer (7.54) bound. -/
theorem lemma79CanonicalEndpointFreshPMF_outerBadJ_toReal_le :
    ∃ Kh ah bh : ℝ, 0 < Kh ∧ 0 < ah ∧ 0 < bh ∧
      ∀ {P J : ℕ}, P ≤ J →
        ∀ (entry : TaoSection7RenewalPoint) (gap m : ℕ),
          (gap : ℝ) ≤ (Real.log 9 / Real.log 2) * (m : ℝ) →
          ((lemma79CanonicalEndpointFreshPMF J entry gap).toOuterMeasure
              {atom |
                9 * m ≤ 10 *
                  (atom.1.1 +
                    lemma77HoldPrefixHorizontalDelta P atom.2)}).toReal ≤
            Kh *
                (Real.exp
                    (-ah *
                      ((((4 / 5 : ℝ) -
                            (Real.log 9 / Real.log 2) / 4) * (m : ℝ)) ^ 2 /
                        (1 + (gap : ℝ)))) +
                  Real.exp
                    (-bh *
                      (((4 / 5 : ℝ) -
                          (Real.log 9 / Real.log 2) / 4) * (m : ℝ)))) +
              Real.exp (((P : ℝ) / 2) - ((m : ℝ) / 160)) := by
  rcases lemma79CanonicalEndpointFreshPMF_outerBadJ_outerMeasure_le with
    ⟨Kh, ah, bh, hKh, hah, hbh, hnative⟩
  refine ⟨Kh, ah, bh, hKh, hah, hbh, ?_⟩
  intro P J hPJ entry gap m hgap
  let preBound : ℝ :=
    Kh *
      (Real.exp
          (-ah *
            ((((4 / 5 : ℝ) - (Real.log 9 / Real.log 2) / 4) * (m : ℝ)) ^ 2 /
              (1 + (gap : ℝ)))) +
        Real.exp
          (-bh *
            (((4 / 5 : ℝ) - (Real.log 9 / Real.log 2) / 4) * (m : ℝ))))
  let sufBound : ℝ :=
    Real.exp (((P : ℝ) / 2) - ((m : ℝ) / 160))
  have hpre : 0 ≤ preBound := by
    dsimp [preBound]
    positivity
  have hsuf : 0 ≤ sufBound := by
    dsimp [sufBound]
    positivity
  calc
    ((lemma79CanonicalEndpointFreshPMF J entry gap).toOuterMeasure
        {atom |
          9 * m ≤ 10 *
            (atom.1.1 +
              lemma77HoldPrefixHorizontalDelta P atom.2)}).toReal ≤
      (ENNReal.ofReal preBound + ENNReal.ofReal sufBound).toReal :=
        ENNReal.toReal_mono (by simp)
          (by simpa [preBound, sufBound] using
            hnative hPJ entry gap m hgap)
    _ = preBound + sufBound := by
      rw [ENNReal.toReal_add ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top]
      simp [hpre, hsuf]
    _ = Kh *
            (Real.exp
                (-ah *
                  ((((4 / 5 : ℝ) -
                        (Real.log 9 / Real.log 2) / 4) * (m : ℝ)) ^ 2 /
                    (1 + (gap : ℝ)))) +
              Real.exp
                (-bh *
                  (((4 / 5 : ℝ) -
                      (Real.log 9 / Real.log 2) / 4) * (m : ℝ)))) +
          Real.exp (((P : ℝ) / 2) - ((m : ℝ) / 160)) := by rfl

/-- The Gaussian denominator in the prefix tail still leaves a fixed linear
rate once the current-scale gap bound and `1 ≤ m` are supplied. -/
theorem lemma79CanonicalPreHorizontalQuadraticRate_le
    {gap m : ℕ} (hm : 1 ≤ m)
    (hgap :
      (gap : ℝ) ≤ (Real.log 9 / Real.log 2) * (m : ℝ)) :
    (5 / 21 : ℝ) *
          ((4 / 5 : ℝ) - (Real.log 9 / Real.log 2) / 4) ^ 2 *
          (m : ℝ) ≤
      ((((4 / 5 : ℝ) - (Real.log 9 / Real.log 2) / 4) * (m : ℝ)) ^ 2 /
        (1 + (gap : ℝ))) := by
  let eta : ℝ := (4 / 5 : ℝ) - (Real.log 9 / Real.log 2) / 4
  have hmReal : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  have hratio :
      Real.log 9 / Real.log 2 ≤ (16 / 5 : ℝ) :=
    taoSection7_log9_div_log2_lt_sixteen_fifths.le
  have hgap' : (gap : ℝ) ≤ (16 / 5 : ℝ) * (m : ℝ) :=
    hgap.trans
      (mul_le_mul_of_nonneg_right hratio (Nat.cast_nonneg m))
  have hden :
      1 + (gap : ℝ) ≤ (21 / 5 : ℝ) * (m : ℝ) := by
    nlinarith
  have hgapDen : 0 < 1 + (gap : ℝ) := by positivity
  change (5 / 21 : ℝ) * eta ^ 2 * (m : ℝ) ≤
    (eta * (m : ℝ)) ^ 2 / (1 + (gap : ℝ))
  rw [show (5 / 21 : ℝ) * eta ^ 2 * (m : ℝ) =
      (eta ^ 2 * (m : ℝ)) / (21 / 5 : ℝ) by ring]
  rw [div_le_div_iff₀ (by norm_num : (0 : ℝ) < 21 / 5) hgapDen]
  calc
    eta ^ 2 * (m : ℝ) * (1 + (gap : ℝ)) ≤
        eta ^ 2 * (m : ℝ) * ((21 / 5 : ℝ) * (m : ℝ)) :=
      mul_le_mul_of_nonneg_left hden
        (mul_nonneg (sq_nonneg eta) (Nat.cast_nonneg m))
    _ = (eta * (m : ℝ)) ^ 2 * (21 / 5 : ℝ) := by ring

/-- Source-facing one-rate form of the full canonical outer (7.54) tail.
The constant is absolute apart from the explicit `exp(P/2)` contribution. -/
theorem lemma79CanonicalEndpointFreshPMF_outerBadJ_singleRate_toReal_le :
    ∃ K c : ℝ, 0 < K ∧ 0 < c ∧
      ∀ {P J : ℕ}, P ≤ J →
        ∀ (entry : TaoSection7RenewalPoint) (gap m : ℕ), 1 ≤ m →
          (gap : ℝ) ≤ (Real.log 9 / Real.log 2) * (m : ℝ) →
          ((lemma79CanonicalEndpointFreshPMF J entry gap).toOuterMeasure
              {atom |
                9 * m ≤ 10 *
                  (atom.1.1 +
                    lemma77HoldPrefixHorizontalDelta P atom.2)}).toReal ≤
            (K + Real.exp ((P : ℝ) / 2)) *
              Real.exp (-c * (m : ℝ)) := by
  rcases lemma79CanonicalEndpointFreshPMF_outerBadJ_toReal_le with
    ⟨Kh, ah, bh, hKh, hah, hbh, hraw⟩
  let eta : ℝ := (4 / 5 : ℝ) - (Real.log 9 / Real.log 2) / 4
  let cg : ℝ := ah * (5 / 21 : ℝ) * eta ^ 2
  let cl : ℝ := bh * eta
  let c : ℝ := min (min cg cl) (1 / 160 : ℝ)
  let K : ℝ := 2 * Kh
  have heta : 0 < eta := by
    simpa [eta] using lemma79CanonicalPreHorizontalMargin_pos
  have hcg : 0 < cg := by
    dsimp [cg]
    positivity
  have hcl : 0 < cl := by
    dsimp [cl]
    positivity
  have hc : 0 < c := by
    dsimp [c]
    exact lt_min (lt_min hcg hcl) (by norm_num)
  have hK : 0 < K := by
    dsimp [K]
    positivity
  refine ⟨K, c, hK, hc, ?_⟩
  intro P J hPJ entry gap m hm hgap
  have hquad :
      (5 / 21 : ℝ) * eta ^ 2 * (m : ℝ) ≤
        (eta * (m : ℝ)) ^ 2 / (1 + (gap : ℝ)) := by
    simpa [eta] using
      lemma79CanonicalPreHorizontalQuadraticRate_le hm hgap
  have hc_cg : c ≤ cg := by
    exact (min_le_left (min cg cl) (1 / 160 : ℝ)).trans
      (min_le_left cg cl)
  have hc_cl : c ≤ cl := by
    exact (min_le_left (min cg cl) (1 / 160 : ℝ)).trans
      (min_le_right cg cl)
  have hc_suf : c ≤ (1 / 160 : ℝ) :=
    min_le_right (min cg cl) (1 / 160 : ℝ)
  have hgaussArg :
      c * (m : ℝ) ≤
        ah * ((eta * (m : ℝ)) ^ 2 / (1 + (gap : ℝ))) := by
    calc
      c * (m : ℝ) ≤ cg * (m : ℝ) :=
        mul_le_mul_of_nonneg_right hc_cg (Nat.cast_nonneg m)
      _ = ah * ((5 / 21 : ℝ) * eta ^ 2 * (m : ℝ)) := by
        dsimp [cg]
        ring
      _ ≤ ah * ((eta * (m : ℝ)) ^ 2 / (1 + (gap : ℝ))) :=
        mul_le_mul_of_nonneg_left hquad hah.le
  have hlinearArg :
      c * (m : ℝ) ≤ bh * (eta * (m : ℝ)) := by
    calc
      c * (m : ℝ) ≤ cl * (m : ℝ) :=
        mul_le_mul_of_nonneg_right hc_cl (Nat.cast_nonneg m)
      _ = bh * (eta * (m : ℝ)) := by
        dsimp [cl]
        ring
  have hsufArg :
      c * (m : ℝ) ≤ (1 / 160 : ℝ) * (m : ℝ) :=
    mul_le_mul_of_nonneg_right hc_suf (Nat.cast_nonneg m)
  have hgauss :
      Real.exp
          (-ah * ((eta * (m : ℝ)) ^ 2 / (1 + (gap : ℝ)))) ≤
        Real.exp (-c * (m : ℝ)) := by
    rw [Real.exp_le_exp]
    linarith
  have hlinear :
      Real.exp (-bh * (eta * (m : ℝ))) ≤
        Real.exp (-c * (m : ℝ)) := by
    rw [Real.exp_le_exp]
    linarith
  have hsuf :
      Real.exp (((P : ℝ) / 2) - ((m : ℝ) / 160)) ≤
        Real.exp ((P : ℝ) / 2) * Real.exp (-c * (m : ℝ)) := by
    calc
      Real.exp (((P : ℝ) / 2) - ((m : ℝ) / 160)) =
          Real.exp ((P : ℝ) / 2) *
            Real.exp (-(1 / 160 : ℝ) * (m : ℝ)) := by
        rw [← Real.exp_add]
        congr 1
        ring
      _ ≤ Real.exp ((P : ℝ) / 2) * Real.exp (-c * (m : ℝ)) := by
        gcongr
  calc
    ((lemma79CanonicalEndpointFreshPMF J entry gap).toOuterMeasure
        {atom |
          9 * m ≤ 10 *
            (atom.1.1 +
              lemma77HoldPrefixHorizontalDelta P atom.2)}).toReal ≤
      Kh *
          (Real.exp
              (-ah *
                ((((4 / 5 : ℝ) -
                      (Real.log 9 / Real.log 2) / 4) * (m : ℝ)) ^ 2 /
                  (1 + (gap : ℝ)))) +
            Real.exp
              (-bh *
                (((4 / 5 : ℝ) -
                    (Real.log 9 / Real.log 2) / 4) * (m : ℝ)))) +
        Real.exp (((P : ℝ) / 2) - ((m : ℝ) / 160)) :=
      hraw hPJ entry gap m hgap
    _ ≤ Kh *
          (Real.exp (-c * (m : ℝ)) + Real.exp (-c * (m : ℝ))) +
        Real.exp ((P : ℝ) / 2) * Real.exp (-c * (m : ℝ)) := by
      simpa [eta] using
        add_le_add
          (mul_le_mul_of_nonneg_left
            (add_le_add hgauss hlinear) hKh.le)
          hsuf
    _ = (K + Real.exp ((P : ℝ) / 2)) *
          Real.exp (-c * (m : ℝ)) := by
      dsimp [K]
      ring

end Lemma79TailExpectation
end TaoSection7Case3SourceStoppingRun

end

end Tao
end Erdos1135
