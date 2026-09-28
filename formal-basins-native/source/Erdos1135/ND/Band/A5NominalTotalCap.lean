import Erdos1135.ND.Band.A5TerminalAtomNominalization

/-!
# A5 Nominal Terminal-Total Cap

This leaf turns the checked harmonic and flat nominalization errors into one
common upper bound for the two nominal terminal sums in a fixed band.
-/

namespace Erdos1135
namespace ND

noncomputable section

/-- The real mass of a PMF event is at most one. -/
private theorem ndPMFEventMass_toReal_le_one
    {Ω : Type*} (μ : PMF Ω) (S : Set Ω) :
    (μ.toOuterMeasure S).toReal ≤ 1 := by
  have huniv : μ.toOuterMeasure Set.univ = 1 :=
    (μ.toOuterMeasure_apply_eq_one_iff Set.univ).2 (Set.subset_univ _)
  have hmono :
      (μ.toOuterMeasure S).toReal ≤
        (μ.toOuterMeasure Set.univ).toReal :=
    ENNReal.toReal_mono (by simp [huniv])
      (μ.toOuterMeasure.mono (Set.subset_univ S))
  simpa [huniv] using hmono

/-- One harmonic nominal terminal atom is nonnegative. -/
theorem ndA5HarmonicTerminalAtomNominalIdealMass_nonneg
    {B : ℕ} (facts : Tao.TaoSection5AffineSourceScaleFacts B)
    {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (hcount : 0 < ndA5BandCount B branch)
    (i : NDA5TerminalAtomIndex B branch C j E)
    (ht2 : NDA5T2ScaleFacts B i.1.1 C) :
    0 ≤ ndA5HarmonicTerminalAtomNominalIdealMass i := by
  unfold ndA5HarmonicTerminalAtomNominalIdealMass
  by_cases hnom : ndA5TerminalAtomNominalSupported i
  · rw [if_pos hnom]
    exact div_nonneg
      (ndA5HarmonicTerminalAtomMWeight_nonneg_le_one_div_candidate
        facts i ht2 hnom.1).1
      (logFinsetMass_ndA5OddBand_pos
        facts.schedule.one_le_B j hcount).le
  · simp [hnom]

/-- One flat nominal terminal atom is nonnegative. -/
theorem ndA5FlatTerminalAtomNominalIdealMass_nonneg
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (hB : 1 ≤ B)
    (i : NDA5TerminalAtomIndex B branch C j E) :
    0 ≤ ndA5FlatTerminalAtomNominalIdealMass i := by
  rw [ndA5FlatTerminalAtomNominalIdealMass_eq_ite hB i]
  positivity

/-- The two literal nominal sums in one retained `(n,L)` cell are
nonnegative.  This is the sign adapter consumed before true absorption; it
retains the terminal endpoint rather than reindexing to physical residues. -/
theorem ndA5NominalFixedCell_sums_nonneg
    {B : ℕ} (facts : Tao.TaoSection5AffineSourceScaleFacts B)
    {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (hcount : 0 < ndA5BandCount B branch)
    (n : {n // n ∈ ndA5PaddedBandWindow B branch C j})
    (L : {L // L ∈ ndA5TerminalTotals B C n.1})
    (ht2 : NDA5T2ScaleFacts B n.1 C) :
    let nu := n.1 - Tao.taoSection5M0 B
    0 ≤ ∑ M : {M // M ∈ Tao.taoSection5EPrime B E},
      ∑ u : Sym (Fin nu) (L.1 - nu),
        ndA5HarmonicTerminalAtomNominalIdealMass
          (⟨n, ⟨L, (u, M)⟩⟩ :
            NDA5TerminalAtomIndex B branch C j E) ∧
    0 ≤ ∑ M : {M // M ∈ Tao.taoSection5EPrime B E},
      ∑ u : Sym (Fin nu) (L.1 - nu),
        ndA5FlatTerminalAtomNominalIdealMass
          (⟨n, ⟨L, (u, M)⟩⟩ :
            NDA5TerminalAtomIndex B branch C j E) := by
  classical
  dsimp only
  constructor
  · apply Finset.sum_nonneg
    intro M _hM
    apply Finset.sum_nonneg
    intro u _hu
    exact ndA5HarmonicTerminalAtomNominalIdealMass_nonneg
      facts hcount _ ht2
  · apply Finset.sum_nonneg
    intro M _hM
    apply Finset.sum_nonneg
    intro u _hu
    exact ndA5FlatTerminalAtomNominalIdealMass_nonneg
      facts.schedule.one_le_B _

/-- Both fixed-band nominal terminal sums obey the same cap consumed by true
absorption.  The harmonic estimate is internally sharper (`1 + 6 eps`), but
the common `1 + 11 eps` interface avoids a law-dependent downstream bound. -/
theorem ndA5NominalTerminalIdealMass_sums_le_commonCap
    {B : ℕ} (facts : Tao.TaoSection5AffineSourceScaleFacts B)
    {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (hlogB : (300000 : ℝ) ≤ Real.log B)
    (hcount : 0 < ndA5BandCount B branch)
    (ht2 : ∀ i : NDA5TerminalAtomIndex B branch C j E,
      NDA5T2ScaleFacts B i.1.1 C)
    (htime : ∀ n ∈ ndA5PaddedBandWindow B branch C j,
      Tao.taoSection5M0 B < n)
    (hdiam : ∀ n ∈ ndA5PaddedBandWindow B branch C j,
      ∀ n' ∈ ndA5PaddedBandWindow B branch C j,
        n ≤ n' → n' - n ≤ Tao.taoSection5M0 B) :
    (∑ i : NDA5TerminalAtomIndex B branch C j E,
        ndA5HarmonicTerminalAtomNominalIdealMass i) ≤
        1 + 11 * (B : ℝ) ^ (-(9 / 10 : ℝ)) ∧
      (∑ i : NDA5TerminalAtomIndex B branch C j E,
        ndA5FlatTerminalAtomNominalIdealMass i) ≤
        1 + 11 * (B : ℝ) ^ (-(9 / 10 : ℝ)) := by
  let eps : ℝ := (B : ℝ) ^ (-(9 / 10 : ℝ))
  let strong : ℝ := (B : ℝ) ^ (-(19749 / 20000 : ℝ))
  let μh := ndA5HarmonicBandPMF B branch j
    facts.schedule.one_le_B hcount
  let μf := ndA5FlatBandPMF B branch j
    facts.schedule.one_le_B hcount
  let U_h := (μh.toOuterMeasure
    (ndA5TerminalAtomUnion B branch C j E)).toReal
  let U_f := (μf.toOuterMeasure
    (ndA5TerminalAtomUnion B branch C j E)).toReal
  let I_h := ∑ i : NDA5TerminalAtomIndex B branch C j E,
    ndA5HarmonicTerminalAtomNominalIdealMass i
  let I_f := ∑ i : NDA5TerminalAtomIndex B branch C j E,
    ndA5FlatTerminalAtomNominalIdealMass i
  have hUh : U_h ≤ 1 := by
    exact ndPMFEventMass_toReal_le_one μh _
  have hUf : U_f ≤ 1 := by
    exact ndPMFEventMass_toReal_le_one μf _
  have hUh0 : 0 ≤ U_h := ENNReal.toReal_nonneg
  have heps0 : 0 ≤ eps := Real.rpow_nonneg (by positivity) _
  have hstrong0 : 0 ≤ strong := Real.rpow_nonneg (by positivity) _
  have hbase : (1 : ℝ) ≤ (B : ℝ) := by
    exact_mod_cast facts.schedule.one_le_B
  have hstrongEps : strong ≤ eps := by
    dsimp [strong, eps]
    apply Real.rpow_le_rpow_of_exponent_le hbase
    norm_num
  have hstrongMass : strong * U_h ≤ eps := by
    calc
      strong * U_h ≤ strong * 1 :=
        mul_le_mul_of_nonneg_left hUh hstrong0
      _ = strong := mul_one strong
      _ ≤ eps := hstrongEps
  have hharm :=
    ndA5HarmonicTerminalAtomUnionMass_sub_nominalIdealSum_abs_le
      facts hlogB hcount ht2 htime hdiam
  have hflat :=
    abs_ndA5FlatTerminalAtomUnionMass_sub_nominalIdealSum_lt
      facts hlogB hcount ht2 htime hdiam
  change |U_h - I_h| ≤ strong * U_h + 5 * eps at hharm
  change |U_f - I_f| < 11 * eps at hflat
  have hIhSub : I_h - U_h ≤ |U_h - I_h| := by
    rw [abs_sub_comm]
    exact le_abs_self (I_h - U_h)
  have hIfSub : I_f - U_f ≤ |U_f - I_f| := by
    rw [abs_sub_comm]
    exact le_abs_self (I_f - U_f)
  have hIhSix : I_h ≤ 1 + 6 * eps := by
    linarith
  have hIh : I_h ≤ 1 + 11 * eps := by
    linarith
  have hIf : I_f ≤ 1 + 11 * eps := by
    linarith
  simpa [I_h, I_f, eps] using And.intro hIh hIf

end

end ND
end Erdos1135
