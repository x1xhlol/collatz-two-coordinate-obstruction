import Erdos1135.ND.Band.A5AffinePosition
import Erdos1135.ND.Band.A5TerminalAtomDenominatorComparison
import Erdos1135.ND.Band.A5TerminalBoundaryShell

/-!
# A5 Fixed-Band Weighted Terminal Nominalization

This leaf compares the physical support of the finite terminal atoms with the
strict nominal affine support used by the two phase profiles.  Candidate
injectivity charges every support mismatch once to the two physical boundary
shells; no terminal-index cardinality enters either comparison.
-/

open scoped BigOperators

namespace Erdos1135
namespace ND

noncomputable section

/-- Strict nominal support of one fixed-band terminal equation.  Compatibility
remains visible because it is also the guard for the affine source candidate. -/
noncomputable def ndA5TerminalAtomNominalSupported
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (i : NDA5TerminalAtomIndex B branch C j E) : Prop :=
  ndA5TerminalAtomCompatible i ∧
    ndA5NominalStrictBandLevel
      (ndA5BandBeta B branch)
      (ndA5PhysicalPhase (ndA5BandLower B branch j) i.2.2.2.1)
      (i.1.1 - Tao.taoSection5M0 B) (i.2.1.1 : ℤ)

noncomputable instance ndA5TerminalAtomNominalSupportedDecidable
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (i : NDA5TerminalAtomIndex B branch C j E) :
    Decidable (ndA5TerminalAtomNominalSupported i) :=
  Classical.propDecidable _

/-- The denominator-simplified affine weight `K/M`, before either band
normalizer is applied. -/
noncomputable def ndA5HarmonicTerminalAtomMWeight
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (i : NDA5TerminalAtomIndex B branch C j E) : ℝ :=
  ((3 : ℝ) ^ (i.1.1 - Tao.taoSection5M0 B) *
      Tao.geom2PNatListMass (ndA5TerminalAtomValuations i)) /
    (i.2.2.2.1 : ℝ)

/-- The factorized flat nominal term.  The displayed `K/M`, source scale,
and exponential position are retained for the later phase-profile regrouping. -/
noncomputable def ndA5FlatTerminalAtomNominalIdealMass
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (i : NDA5TerminalAtomIndex B branch C j E) : ℝ :=
  if ndA5TerminalAtomNominalSupported i then
    (ndA5HarmonicTerminalAtomMWeight i *
        (ndA5BandLower B branch j *
          Real.exp (ndA5NominalAffinePosition
            (ndA5BandLower B branch j) i.2.2.2.1
            (i.1.1 - Tao.taoSection5M0 B) i.2.1.1))) /
      ((ndA5OddBand B branch j).card : ℝ)
  else 0

/-- The strict-support harmonic nominal term, normalized by the physical
band's exact logarithmic mass. -/
noncomputable def ndA5HarmonicTerminalAtomNominalIdealMass
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (i : NDA5TerminalAtomIndex B branch C j E) : ℝ :=
  if ndA5TerminalAtomNominalSupported i then
    ndA5HarmonicTerminalAtomMWeight i /
      Tao.logFinsetMass (ndA5OddBand B branch j)
  else 0

/-- The factorized flat coefficient is exactly one. -/
theorem ndA5NominalFlatFactor_eq_one
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (hB : 1 ≤ B)
    (i : NDA5TerminalAtomIndex B branch C j E) :
    ndA5HarmonicTerminalAtomMWeight i *
        (ndA5BandLower B branch j *
          Real.exp (ndA5NominalAffinePosition
            (ndA5BandLower B branch j) i.2.2.2.1
            (i.1.1 - Tao.taoSection5M0 B) i.2.1.1)) = 1 := by
  let z := ndA5BandLower B branch j
  let q := i.1.1 - Tao.taoSection5M0 B
  let L := i.2.1.1
  let M := i.2.2.2.1
  have hBpos : (0 : ℝ) < B := by
    exact_mod_cast hB
  have hz : 0 < z := by
    have hYpos : 0 < Tao.taoSection5SourceY B branch := by
      rw [Tao.taoSection5SourceY_eq_branch_rpow]
      exact Real.rpow_pos_of_pos hBpos _
    dsimp only [z]
    unfold ndA5BandLower
    exact mul_pos hYpos (Real.exp_pos _)
  have hMposNat : 0 < M := Odd.pos
    (Tao.mem_taoSection5EPrime_iff.mp
      (ndA5TerminalAtom_endpoint_mem i)).2.2.1
  have hMpos : (0 : ℝ) < M := by exact_mod_cast hMposNat
  have hlogTwo : Real.log (2 : ℝ) ≠ 0 :=
    (Real.log_pos (by norm_num)).ne'
  have hlogPhase :
      Real.log (z / (M : ℝ)) = Real.log z - Real.log (M : ℝ) := by
    rw [Real.log_div hz.ne' hMpos.ne']
  have hexp :
      Real.exp (ndA5NominalAffinePosition z M q L) =
        (2 : ℝ) ^ L * (M : ℝ) / (z * (3 : ℝ) ^ q) := by
    unfold ndA5NominalAffinePosition ndA5PhysicalPhase logTwoThree
    rw [hlogPhase]
    rw [show
      (((L : ℝ) -
          ((Real.log z - Real.log (M : ℝ)) / Real.log 2 +
            (q : ℝ) * (Real.log 3 / Real.log 2))) * Real.log 2) =
        Real.log ((2 : ℝ) ^ L * (M : ℝ) / (z * (3 : ℝ) ^ q)) by
      rw [Real.log_div
        (mul_ne_zero (pow_ne_zero _ (by norm_num)) hMpos.ne')
        (mul_ne_zero hz.ne' (pow_ne_zero _ (by norm_num))),
        Real.log_mul (pow_ne_zero _ (by norm_num)) hMpos.ne',
        Real.log_mul hz.ne' (pow_ne_zero _ (by norm_num)),
        Real.log_pow, Real.log_pow]
      field_simp [hlogTwo]
      ring]
    rw [Real.exp_log]
    positivity
  change
    (((3 : ℝ) ^ q *
        Tao.geom2PNatListMass (ndA5TerminalAtomValuations i)) /
      (M : ℝ)) *
        (z * Real.exp (ndA5NominalAffinePosition z M q L)) = 1
  rw [Tao.geom2PNatListMass_eq_inv_pow,
    ndA5TerminalAtomValuations_weight]
  change
    (((3 : ℝ) ^ q * (1 / ((2 : ℝ) ^ L))) / (M : ℝ)) *
      (z * Real.exp (ndA5NominalAffinePosition z M q L)) = 1
  rw [hexp]
  field_simp [hz.ne', hMpos.ne', pow_ne_zero]

private theorem ndA5Candidate_mem_oddHalfOpenRealWindow_of_position
    {z a b : ℝ} {N : ℕ}
    (hz : 0 < z) (hodd : Odd N)
    (hlower : a ≤ ndA5ExactAffinePosition z N)
    (hupper : ndA5ExactAffinePosition z N < b) :
    N ∈ oddHalfOpenRealWindow (z * Real.exp a) (z * Real.exp b) := by
  have hNposNat : 0 < N := Odd.pos hodd
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hNposNat
  have hdiv : 0 < (N : ℝ) / z := div_pos hNpos hz
  have hexp : Real.exp (ndA5ExactAffinePosition z N) = (N : ℝ) / z := by
    unfold ndA5ExactAffinePosition
    exact Real.exp_log hdiv
  rw [mem_oddHalfOpenRealWindow]
  refine ⟨?_, ?_, Nat.odd_iff.mp hodd⟩
  · have h := Real.exp_le_exp.mpr hlower
    rw [hexp] at h
    exact (by
      have := (le_div_iff₀ hz).mp h
      simpa only [mul_comm] using this)
  · have h := Real.exp_lt_exp.mpr hupper
    rw [hexp] at h
    exact (by
      have := (div_lt_iff₀ hz).mp h
      simpa only [mul_comm] using this)

/-- A nominal-only compatible candidate lies in the lower boundary shell. -/
theorem ndA5TerminalAtomCandidate_mem_lowerShell_of_nominal_not_actual
    {B : ℕ} (facts : Tao.TaoSection5AffineSourceScaleFacts B)
    {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (hlogB : (300000 : ℝ) ≤ Real.log B)
    (i : NDA5TerminalAtomIndex B branch C j E)
    (ht2 : NDA5T2ScaleFacts B i.1.1 C)
    (hnom : ndA5TerminalAtomNominalSupported i)
    (hnotActual : ¬ ndA5TerminalAtomSupported i) :
    ndA5TerminalAtomCandidate i ∈
      ndA5LowerTerminalBoundaryShell B branch j := by
  let z := ndA5BandLower B branch j
  let eps := ndA5TerminalBoundaryEpsilon B
  have hpacket := ndA5TerminalAtomCandidate_odd_and_affine
    facts i ht2 hnom.1
  let N : Tao.TaoOddNat := ⟨ndA5TerminalAtomCandidate i, hpacket.1⟩
  have hAffN :
      Tao.taoAffList (ndA5TerminalAtomValuations i) (N.1 : ℚ) =
        (i.2.2.2.1 : ℚ) := by
    simpa only [N] using hpacket.2
  have hnotBand : ndA5TerminalAtomCandidate i ∉ ndA5OddBand B branch j := by
    intro hband
    exact hnotActual ⟨hnom.1, hband⟩
  have hnomPos : ndA5StrictPosition (ndA5BandBeta B branch)
      (ndA5NominalAffinePosition z i.2.2.2.1
        (i.1.1 - Tao.taoSection5M0 B) i.2.1.1) :=
    (ndA5NominalStrictBandLevel_iff_nominalPosition _ _ _ _ _).1 hnom.2
  have hnomPos' : ndA5StrictPosition (ndA5BandBeta B branch)
      (ndA5NominalAffinePosition (ndA5BandLower B branch j) i.2.2.2.1
        (i.1.1 - Tao.taoSection5M0 B)
        (Tao.taoTupleWeight (ndA5TerminalAtomValuations i))) := by
    simpa only [z, ndA5TerminalAtomValuations_weight] using hnomPos
  have hstrip := ndA5_affineBandMismatch_mem_strips_ePrime
    (branch := branch) (j := j) (N := N)
      facts hlogB (ndA5TerminalAtom_endpoint_mem i) ht2
      (ndA5TerminalAtomValuations_length i) hAffN
  have hlowerStrip := hstrip.2.2.1 ⟨hnomPos', hnotBand⟩
  have hBpos : (0 : ℝ) < B := by
    exact_mod_cast facts.schedule.one_le_B
  have hz : 0 < z := by
    exact hBpos.trans_le (by
      simpa only [z] using
        cast_le_ndA5BandLower facts.schedule.one_le_B branch j)
  have heq := ndA5_exactAffinePosition_eq_nominal_sub_correction
    hz (ndA5TerminalAtomValuations_length i) hAffN
  have heq' :
      ndA5ExactAffinePosition z N.1 =
        ndA5NominalAffinePosition z i.2.2.2.1
            (i.1.1 - Tao.taoSection5M0 B) i.2.1.1 -
          ndA5AffinePositionCorrection
            (ndA5TerminalAtomValuations i) i.2.2.2.1 := by
    simpa only [ndA5TerminalAtomValuations_weight] using heq
  have hlowerStrip' :
      ndA5NominalAffinePosition z i.2.2.2.1
          (i.1.1 - Tao.taoSection5M0 B) i.2.1.1 ∈
        Set.Ioo 0 (ndA5AffinePositionCorrection
          (ndA5TerminalAtomValuations i) i.2.2.2.1) := by
    simpa only [z, ndA5TerminalAtomValuations_weight] using hlowerStrip
  have hdeltaLe :
      ndA5AffinePositionCorrection
          (ndA5TerminalAtomValuations i) i.2.2.2.1 ≤ eps := by
    simpa only [eps, ndA5TerminalBoundaryEpsilon] using hstrip.2.1
  have hlower : -eps ≤ ndA5ExactAffinePosition z N.1 := by
    linarith [hlowerStrip'.1]
  have hupper : ndA5ExactAffinePosition z N.1 < 0 := by
    linarith [hlowerStrip'.2]
  have hmem := ndA5Candidate_mem_oddHalfOpenRealWindow_of_position
    hz hpacket.1 hlower hupper
  simpa [ndA5LowerTerminalBoundaryShell, z, eps] using hmem

/-- A physical-only compatible candidate lies in the upper boundary shell. -/
theorem ndA5TerminalAtomCandidate_mem_upperShell_of_actual_not_nominal
    {B : ℕ} (facts : Tao.TaoSection5AffineSourceScaleFacts B)
    {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (hlogB : (300000 : ℝ) ≤ Real.log B)
    (i : NDA5TerminalAtomIndex B branch C j E)
    (ht2 : NDA5T2ScaleFacts B i.1.1 C)
    (hactual : ndA5TerminalAtomSupported i)
    (hnotNominal : ¬ ndA5TerminalAtomNominalSupported i) :
    ndA5TerminalAtomCandidate i ∈
      ndA5UpperTerminalBoundaryShell B branch j := by
  let z := ndA5BandLower B branch j
  let beta := ndA5BandBeta B branch
  let eps := ndA5TerminalBoundaryEpsilon B
  have hpacket := ndA5TerminalAtomCandidate_odd_and_affine
    facts i ht2 hactual.1
  let N : Tao.TaoOddNat := ⟨ndA5TerminalAtomCandidate i, hpacket.1⟩
  have hAffN :
      Tao.taoAffList (ndA5TerminalAtomValuations i) (N.1 : ℚ) =
        (i.2.2.2.1 : ℚ) := by
    simpa only [N] using hpacket.2
  have hnotStrict : ¬ ndA5StrictPosition beta
      (ndA5NominalAffinePosition z i.2.2.2.1
        (i.1.1 - Tao.taoSection5M0 B) i.2.1.1) := by
    intro hstrict
    apply hnotNominal
    refine ⟨hactual.1, ?_⟩
    exact (ndA5NominalStrictBandLevel_iff_nominalPosition _ _ _ _ _).2 hstrict
  have hnotStrict' : ¬ ndA5StrictPosition (ndA5BandBeta B branch)
      (ndA5NominalAffinePosition (ndA5BandLower B branch j) i.2.2.2.1
        (i.1.1 - Tao.taoSection5M0 B)
        (Tao.taoTupleWeight (ndA5TerminalAtomValuations i))) := by
    simpa only [beta, z, ndA5TerminalAtomValuations_weight] using hnotStrict
  have hstrip := ndA5_affineBandMismatch_mem_strips_ePrime
    (branch := branch) (j := j) (N := N)
      facts hlogB (ndA5TerminalAtom_endpoint_mem i) ht2
      (ndA5TerminalAtomValuations_length i) hAffN
  have hupperStrip := hstrip.2.2.2 ⟨hactual.2, hnotStrict'⟩
  have hBpos : (0 : ℝ) < B := by
    exact_mod_cast facts.schedule.one_le_B
  have hz : 0 < z := by
    exact hBpos.trans_le (by
      simpa only [z] using
        cast_le_ndA5BandLower facts.schedule.one_le_B branch j)
  have heq := ndA5_exactAffinePosition_eq_nominal_sub_correction
    hz (ndA5TerminalAtomValuations_length i) hAffN
  have heq' :
      ndA5ExactAffinePosition z N.1 =
        ndA5NominalAffinePosition z i.2.2.2.1
            (i.1.1 - Tao.taoSection5M0 B) i.2.1.1 -
          ndA5AffinePositionCorrection
            (ndA5TerminalAtomValuations i) i.2.2.2.1 := by
    simpa only [ndA5TerminalAtomValuations_weight] using heq
  have hupperStrip' :
      ndA5NominalAffinePosition z i.2.2.2.1
          (i.1.1 - Tao.taoSection5M0 B) i.2.1.1 ∈
        Set.Ico beta (beta + ndA5AffinePositionCorrection
          (ndA5TerminalAtomValuations i) i.2.2.2.1) := by
    simpa only [z, beta, ndA5TerminalAtomValuations_weight] using hupperStrip
  have hdeltaLe :
      ndA5AffinePositionCorrection
          (ndA5TerminalAtomValuations i) i.2.2.2.1 ≤ eps := by
    simpa only [eps, ndA5TerminalBoundaryEpsilon] using hstrip.2.1
  have hhalf := (mem_ndA5OddBand_iff_halfOpen_exactPosition
    facts.schedule.one_le_B (Nat.odd_iff.mp hpacket.1)).1 hactual.2
  have hlower : beta - eps ≤ ndA5ExactAffinePosition z N.1 := by
    linarith [hupperStrip'.1]
  have hupper : ndA5ExactAffinePosition z N.1 < beta := by
    simpa only [N, beta, z] using hhalf.2
  have hmem := ndA5Candidate_mem_oddHalfOpenRealWindow_of_position
    hz hpacket.1 hlower hupper
  have hlowerEq :
      z * Real.exp (beta - eps) =
        ndA5BandLower B branch (j + 1) * Real.exp (-eps) := by
    rw [ndA5BandLower_succ, Real.exp_sub, Real.exp_neg]
    ring
  have hupperEq :
      z * Real.exp beta = ndA5BandLower B branch (j + 1) := by
    simpa only [z, beta] using (ndA5BandLower_succ B branch j).symm
  simpa only [ndA5UpperTerminalBoundaryShell, hlowerEq, hupperEq] using hmem

/-- The harmonic `K/M` weight is nonnegative and bounded by the reciprocal
of its compatible odd source candidate. -/
theorem ndA5HarmonicTerminalAtomMWeight_nonneg_le_one_div_candidate
    {B : ℕ} (facts : Tao.TaoSection5AffineSourceScaleFacts B)
    {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (i : NDA5TerminalAtomIndex B branch C j E)
    (ht2 : NDA5T2ScaleFacts B i.1.1 C)
    (hcompat : ndA5TerminalAtomCompatible i) :
    0 ≤ ndA5HarmonicTerminalAtomMWeight i ∧
      ndA5HarmonicTerminalAtomMWeight i ≤
        1 / (ndA5TerminalAtomCandidate i : ℝ) := by
  have hpacket := ndA5TerminalAtomCandidate_odd_and_affine
    facts i ht2 hcompat
  let N : Tao.TaoOddNat := ⟨ndA5TerminalAtomCandidate i, hpacket.1⟩
  have hAffN :
      Tao.taoAffList (ndA5TerminalAtomValuations i) (N.1 : ℚ) =
        (i.2.2.2.1 : ℚ) := by
    simpa only [N] using hpacket.2
  have hrecip := Tao.taoAffList_reciprocal
    (N := N) (ndA5TerminalAtomValuations_length i) hAffN
  have hdenPos := Tao.taoAffList_denominator_pos
    (N := N) (ndA5TerminalAtomValuations_length i) hAffN
  have hMposNat : 0 < i.2.2.2.1 := Odd.pos
    (Tao.mem_taoSection5EPrime_iff.mp
      (ndA5TerminalAtom_endpoint_mem i)).2.2.1
  have hMpos : (0 : ℝ) < i.2.2.2.1 := by exact_mod_cast hMposNat
  have hKnonneg :
      0 ≤ (3 : ℝ) ^ (i.1.1 - Tao.taoSection5M0 B) *
        Tao.geom2PNatListMass (ndA5TerminalAtomValuations i) := by
    rw [Tao.geom2PNatListMass_eq_inv_pow]
    positivity
  constructor
  · unfold ndA5HarmonicTerminalAtomMWeight
    positivity
  · rw [show (1 : ℝ) / (ndA5TerminalAtomCandidate i : ℝ) =
        ((3 : ℝ) ^ (i.1.1 - Tao.taoSection5M0 B) *
            Tao.geom2PNatListMass (ndA5TerminalAtomValuations i)) /
          ((i.2.2.2.1 : ℝ) -
            (Tao.taoOffsetList (ndA5TerminalAtomValuations i) : ℝ)) by
      simpa only [N] using hrecip]
    unfold ndA5HarmonicTerminalAtomMWeight
    apply (div_le_div_iff₀ hMpos hdenPos).2
    have hoffset :
        0 ≤ (Tao.taoOffsetList (ndA5TerminalAtomValuations i) : ℝ) :=
      Rat.cast_nonneg.mpr
        (Tao.taoOffsetList_nonneg (ndA5TerminalAtomValuations i))
    nlinarith

private noncomputable def ndA5TerminalAtomSupportMismatch
    (B : ℕ) (branch : Tao.TaoSection5SourceBranch)
    (C : ℝ) (j : ℕ) (E : Set ℕ) :
    Finset (NDA5TerminalAtomIndex B branch C j E) :=
  Finset.univ.filter fun i =>
    (ndA5TerminalAtomSupported i ∧
        ¬ ndA5TerminalAtomNominalSupported i) ∨
      (ndA5TerminalAtomNominalSupported i ∧
        ¬ ndA5TerminalAtomSupported i)

private theorem ndA5TerminalAtomCompatible_of_mem_supportMismatch
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    {i : NDA5TerminalAtomIndex B branch C j E}
    (hi : i ∈ ndA5TerminalAtomSupportMismatch B branch C j E) :
    ndA5TerminalAtomCompatible i := by
  simp only [ndA5TerminalAtomSupportMismatch, Finset.mem_filter,
    Finset.mem_univ, true_and] at hi
  rcases hi with hi | hi
  · exact hi.1.1
  · exact hi.1.1

private theorem ndA5TerminalAtomCandidate_maps_supportMismatch_to_shells
    {B : ℕ} (facts : Tao.TaoSection5AffineSourceScaleFacts B)
    {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (hlogB : (300000 : ℝ) ≤ Real.log B)
    (ht2 : ∀ i : NDA5TerminalAtomIndex B branch C j E,
      NDA5T2ScaleFacts B i.1.1 C) :
    Set.MapsTo
      (fun i : NDA5TerminalAtomIndex B branch C j E =>
        ndA5TerminalAtomCandidate i)
      (ndA5TerminalAtomSupportMismatch B branch C j E :
        Set (NDA5TerminalAtomIndex B branch C j E))
      ((ndA5LowerTerminalBoundaryShell B branch j ∪
        ndA5UpperTerminalBoundaryShell B branch j : Finset ℕ) : Set ℕ) := by
  intro i hi
  rw [Finset.mem_coe] at hi
  simp only [ndA5TerminalAtomSupportMismatch, Finset.mem_filter,
    Finset.mem_univ, true_and] at hi
  rcases hi with hi | hi
  · exact Finset.mem_union_right _
      (ndA5TerminalAtomCandidate_mem_upperShell_of_actual_not_nominal
        facts hlogB i (ht2 i) hi.1 hi.2)
  · exact Finset.mem_union_left _
      (ndA5TerminalAtomCandidate_mem_lowerShell_of_nominal_not_actual
        facts hlogB i (ht2 i) hi.1 hi.2)

private theorem card_ndA5TerminalAtomSupportMismatch_le_boundaryShellUnion
    {B : ℕ} (facts : Tao.TaoSection5AffineSourceScaleFacts B)
    {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (hlogB : (300000 : ℝ) ≤ Real.log B)
    (ht2 : ∀ i : NDA5TerminalAtomIndex B branch C j E,
      NDA5T2ScaleFacts B i.1.1 C)
    (htime : ∀ n ∈ ndA5PaddedBandWindow B branch C j,
      Tao.taoSection5M0 B < n)
    (hdiam : ∀ n ∈ ndA5PaddedBandWindow B branch C j,
      ∀ n' ∈ ndA5PaddedBandWindow B branch C j,
        n ≤ n' → n' - n ≤ Tao.taoSection5M0 B) :
    (ndA5TerminalAtomSupportMismatch B branch C j E).card ≤
      (ndA5LowerTerminalBoundaryShell B branch j ∪
        ndA5UpperTerminalBoundaryShell B branch j).card := by
  apply Finset.card_le_card_of_injOn
    (fun i : NDA5TerminalAtomIndex B branch C j E =>
      ndA5TerminalAtomCandidate i)
    (ndA5TerminalAtomCandidate_maps_supportMismatch_to_shells
      facts hlogB ht2)
  intro i hi i' hi' hcand
  exact ndA5TerminalAtomCandidate_injOn_compatible
    facts htime hdiam ht2
      (ndA5TerminalAtomCompatible_of_mem_supportMismatch hi)
      (ndA5TerminalAtomCompatible_of_mem_supportMismatch hi') hcand

private theorem abs_sum_indicator_sub_indicator_le_mismatch_sum
    {I : Type*} [Fintype I]
    (p q : I → Prop) [DecidablePred p] [DecidablePred q]
    (w : I → ℝ) (hw : ∀ i, 0 ≤ w i) :
    |(∑ i, if p i then w i else 0) -
        ∑ i, if q i then w i else 0| ≤
      ∑ i ∈ Finset.univ.filter (fun i =>
        (p i ∧ ¬ q i) ∨ (q i ∧ ¬ p i)), w i := by
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ i, ((if p i then w i else 0) -
        (if q i then w i else 0))| ≤
        ∑ i, |(if p i then w i else 0) -
          (if q i then w i else 0)| := by
      simpa using Finset.abs_sum_le_sum_abs
        (fun i => (if p i then w i else 0) -
          (if q i then w i else 0)) Finset.univ
    _ = ∑ i ∈ Finset.univ.filter (fun i =>
        (p i ∧ ¬ q i) ∨ (q i ∧ ¬ p i)), w i := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro i _hi
      by_cases hp : p i <;> by_cases hq : q i <;>
        simp [hp, hq, hw i]

/-- The factorized flat nominal term has the inverse-card shell-charging
form, while retaining its public weighted definition for regrouping. -/
theorem ndA5FlatTerminalAtomNominalIdealMass_eq_ite
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (hB : 1 ≤ B)
    (i : NDA5TerminalAtomIndex B branch C j E) :
    ndA5FlatTerminalAtomNominalIdealMass i =
      if ndA5TerminalAtomNominalSupported i then
        1 / ((ndA5OddBand B branch j).card : ℝ)
      else 0 := by
  unfold ndA5FlatTerminalAtomNominalIdealMass
  by_cases hnom : ndA5TerminalAtomNominalSupported i
  · rw [if_pos hnom, if_pos hnom, ndA5NominalFlatFactor_eq_one hB i]
  · rw [if_neg hnom, if_neg hnom]

/-- One actual flat terminal atom is exactly one inverse band-cardinality on
its proof-free support and zero otherwise. -/
theorem ndA5FlatBandPMF_terminalAtomMass_eq_ite_supported
    {B : ℕ} (facts : Tao.TaoSection5AffineSourceScaleFacts B)
    {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (hcount : 0 < ndA5BandCount B branch)
    (i : NDA5TerminalAtomIndex B branch C j E)
    (ht2 : NDA5T2ScaleFacts B i.1.1 C) :
    ((ndA5FlatBandPMF B branch j facts.schedule.one_le_B hcount).toOuterMeasure
        (ndA5TerminalAtom i)).toReal =
      if ndA5TerminalAtomSupported i then
        1 / ((ndA5OddBand B branch j).card : ℝ)
      else 0 := by
  rw [ndA5FlatBandPMF_terminalAtomMass_eq_card_div,
    ndA5TerminalAtomSourceFinset_eq_ite_supported facts i ht2]
  by_cases hsupp : ndA5TerminalAtomSupported i <;> simp [hsupp]

/-- Raw flat support mismatch, with no index-count loss. -/
theorem abs_sum_ndA5FlatTerminalAtomActualIdeal_sub_nominalIdeal_le_shellRatio
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
    |(∑ i : NDA5TerminalAtomIndex B branch C j E,
        if ndA5TerminalAtomSupported i then
          1 / ((ndA5OddBand B branch j).card : ℝ) else 0) -
      ∑ i : NDA5TerminalAtomIndex B branch C j E,
        ndA5FlatTerminalAtomNominalIdealMass i| ≤
      ((ndA5LowerTerminalBoundaryShell B branch j ∪
          ndA5UpperTerminalBoundaryShell B branch j).card : ℝ) /
        ((ndA5OddBand B branch j).card : ℝ) := by
  classical
  rw [show (∑ i : NDA5TerminalAtomIndex B branch C j E,
      ndA5FlatTerminalAtomNominalIdealMass i) =
      ∑ i : NDA5TerminalAtomIndex B branch C j E,
        if ndA5TerminalAtomNominalSupported i then
          1 / ((ndA5OddBand B branch j).card : ℝ) else 0 by
    apply Finset.sum_congr rfl
    intro i _hi
    exact ndA5FlatTerminalAtomNominalIdealMass_eq_ite
      facts.schedule.one_le_B i]
  have hdenPos : (0 : ℝ) < (ndA5OddBand B branch j).card := by
    exact_mod_cast ndA5OddBand_card_pos facts.schedule.one_le_B j hcount
  have hraw := abs_sum_indicator_sub_indicator_le_mismatch_sum
    (fun i : NDA5TerminalAtomIndex B branch C j E =>
      ndA5TerminalAtomSupported i)
    (fun i => ndA5TerminalAtomNominalSupported i)
    (fun _i => 1 / ((ndA5OddBand B branch j).card : ℝ))
    (fun _i => by positivity)
  have hcard := card_ndA5TerminalAtomSupportMismatch_le_boundaryShellUnion
    facts hlogB ht2 htime hdiam
  calc
    _ ≤ ∑ i ∈ ndA5TerminalAtomSupportMismatch B branch C j E,
        1 / ((ndA5OddBand B branch j).card : ℝ) := by
      simpa only [ndA5TerminalAtomSupportMismatch] using hraw
    _ = ((ndA5TerminalAtomSupportMismatch B branch C j E).card : ℝ) /
        ((ndA5OddBand B branch j).card : ℝ) := by
      simp [div_eq_mul_inv]
    _ ≤ ((ndA5LowerTerminalBoundaryShell B branch j ∪
          ndA5UpperTerminalBoundaryShell B branch j).card : ℝ) /
        ((ndA5OddBand B branch j).card : ℝ) := by
      apply div_le_div_of_nonneg_right _ hdenPos.le
      exact_mod_cast hcard

/-- Endpoint-shaped flat weighted nominalization for one physical band. -/
theorem abs_ndA5FlatTerminalAtomUnionMass_sub_nominalIdealSum_lt
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
    let μ := ndA5FlatBandPMF B branch j
      facts.schedule.one_le_B hcount
    let U := (μ.toOuterMeasure
      (ndA5TerminalAtomUnion B branch C j E)).toReal
    |U - ∑ i : NDA5TerminalAtomIndex B branch C j E,
        ndA5FlatTerminalAtomNominalIdealMass i| <
      11 * (B : ℝ) ^ (-(9 / 10 : ℝ)) := by
  classical
  dsimp only
  let μ := ndA5FlatBandPMF B branch j
    facts.schedule.one_le_B hcount
  have hpair := ndA5TerminalAtoms_pairwiseDisjoint (E := E) htime hdiam
  rw [ndA5TerminalAtomUnion_outerMass_eq_sum μ hpair]
  have hactual :
      (∑ i : NDA5TerminalAtomIndex B branch C j E,
          (μ.toOuterMeasure (ndA5TerminalAtom i)).toReal) =
        ∑ i : NDA5TerminalAtomIndex B branch C j E,
          if ndA5TerminalAtomSupported i then
            1 / ((ndA5OddBand B branch j).card : ℝ) else 0 := by
    apply Finset.sum_congr rfl
    intro i _hi
    exact ndA5FlatBandPMF_terminalAtomMass_eq_ite_supported
      facts hcount i (ht2 i)
  rw [hactual]
  exact (abs_sum_ndA5FlatTerminalAtomActualIdeal_sub_nominalIdeal_le_shellRatio
    facts hlogB hcount ht2 htime hdiam).trans_lt
      (ndA5FlatBoundaryShellRatio_lt_eleven_rpow_neg_nine_tenths
        facts.schedule.one_le_B j hcount)

/-- Harmonic candidate weight in the shell's native logarithmic units. -/
theorem ndA5HarmonicTerminalAtomMWeight_nonneg_le_logNatWeight_candidate
    {B : ℕ} (facts : Tao.TaoSection5AffineSourceScaleFacts B)
    {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (i : NDA5TerminalAtomIndex B branch C j E)
    (ht2 : NDA5T2ScaleFacts B i.1.1 C)
    (hcompat : ndA5TerminalAtomCompatible i) :
    0 ≤ ndA5HarmonicTerminalAtomMWeight i ∧
      ndA5HarmonicTerminalAtomMWeight i ≤
        Tao.logNatWeight (ndA5TerminalAtomCandidate i) := by
  have hpacket := ndA5TerminalAtomCandidate_odd_and_affine
    facts i ht2 hcompat
  have hbound :=
    ndA5HarmonicTerminalAtomMWeight_nonneg_le_one_div_candidate
      facts i ht2 hcompat
  rw [Tao.logNatWeight_eq_one_div_of_pos (Odd.pos hpacket.1)]
  exact hbound

private theorem logFinsetMass_union_le_add
    (S T : Finset ℕ) :
    Tao.logFinsetMass (S ∪ T) ≤
      Tao.logFinsetMass S + Tao.logFinsetMass T := by
  unfold Tao.logFinsetMass
  rw [← Finset.union_sdiff_self_eq_union]
  rw [Finset.sum_union Finset.disjoint_sdiff]
  exact add_le_add le_rfl
    (Finset.sum_le_sum_of_subset_of_nonneg Finset.sdiff_subset
      (fun n _hn _hnot => Tao.logNatWeight_nonneg n))

/-- Raw harmonic support mismatch is charged once to the two boundary shells. -/
theorem abs_sum_ndA5HarmonicTerminalAtomMWeight_phys_sub_nominal_le_shellMass
    {B : ℕ} (facts : Tao.TaoSection5AffineSourceScaleFacts B)
    {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (hlogB : (300000 : ℝ) ≤ Real.log B)
    (ht2 : ∀ i : NDA5TerminalAtomIndex B branch C j E,
      NDA5T2ScaleFacts B i.1.1 C)
    (htime : ∀ n ∈ ndA5PaddedBandWindow B branch C j,
      Tao.taoSection5M0 B < n)
    (hdiam : ∀ n ∈ ndA5PaddedBandWindow B branch C j,
      ∀ n' ∈ ndA5PaddedBandWindow B branch C j,
        n ≤ n' → n' - n ≤ Tao.taoSection5M0 B) :
    |(∑ i : NDA5TerminalAtomIndex B branch C j E,
        if ndA5TerminalAtomSupported i then
          ndA5HarmonicTerminalAtomMWeight i else 0) -
      ∑ i : NDA5TerminalAtomIndex B branch C j E,
        if ndA5TerminalAtomNominalSupported i then
          ndA5HarmonicTerminalAtomMWeight i else 0| ≤
      Tao.logFinsetMass (ndA5LowerTerminalBoundaryShell B branch j) +
        Tao.logFinsetMass (ndA5UpperTerminalBoundaryShell B branch j) := by
  classical
  let D := ndA5TerminalAtomSupportMismatch B branch C j E
  let candidate : NDA5TerminalAtomIndex B branch C j E → ℕ :=
    fun i => ndA5TerminalAtomCandidate i
  let shells := ndA5LowerTerminalBoundaryShell B branch j ∪
    ndA5UpperTerminalBoundaryShell B branch j
  have hraw := abs_sum_indicator_sub_indicator_le_mismatch_sum
    (fun i : NDA5TerminalAtomIndex B branch C j E =>
      ndA5TerminalAtomSupported i)
    (fun i => ndA5TerminalAtomNominalSupported i)
    (fun i => ndA5HarmonicTerminalAtomMWeight i)
    (fun i => by
      by_cases hc : ndA5TerminalAtomCompatible i
      · exact (ndA5HarmonicTerminalAtomMWeight_nonneg_le_logNatWeight_candidate
          facts i (ht2 i) hc).1
      · unfold ndA5HarmonicTerminalAtomMWeight
        change 0 ≤
          ((3 : ℝ) ^ (i.1.1 - Tao.taoSection5M0 B) *
              Tao.geom2PNatListMass (ndA5TerminalAtomValuations i)) /
            (i.2.2.2.1 : ℝ)
        rw [Tao.geom2PNatListMass_eq_inv_pow]
        positivity)
  have hinj := ndA5TerminalAtomCandidate_injOn_compatible
    facts htime hdiam ht2
  have hmaps := ndA5TerminalAtomCandidate_maps_supportMismatch_to_shells
    facts hlogB ht2
  have himage : D.image candidate ⊆ shells := by
    intro N hN
    rcases Finset.mem_image.mp hN with ⟨i, hi, rfl⟩
    exact hmaps hi
  have hsourceToImage :
      (∑ i ∈ D, Tao.logNatWeight (candidate i)) =
        ∑ N ∈ D.image candidate, Tao.logNatWeight N := by
    dsimp only [candidate]
    rw [Finset.sum_image]
    intro i hi i' hi' hcand
    exact hinj
      (ndA5TerminalAtomCompatible_of_mem_supportMismatch hi)
      (ndA5TerminalAtomCompatible_of_mem_supportMismatch hi') hcand
  calc
    _ ≤ ∑ i ∈ D, ndA5HarmonicTerminalAtomMWeight i := by
      simpa only [D, ndA5TerminalAtomSupportMismatch] using hraw
    _ ≤ ∑ i ∈ D, Tao.logNatWeight (candidate i) := by
      apply Finset.sum_le_sum
      intro i hi
      exact (ndA5HarmonicTerminalAtomMWeight_nonneg_le_logNatWeight_candidate
        facts i (ht2 i)
          (ndA5TerminalAtomCompatible_of_mem_supportMismatch hi)).2
    _ = ∑ N ∈ D.image candidate, Tao.logNatWeight N := hsourceToImage
    _ = Tao.logFinsetMass (D.image candidate) := rfl
    _ ≤ Tao.logFinsetMass shells := Tao.logFinsetMass_mono himage
    _ ≤ Tao.logFinsetMass (ndA5LowerTerminalBoundaryShell B branch j) +
        Tao.logFinsetMass (ndA5UpperTerminalBoundaryShell B branch j) :=
      logFinsetMass_union_le_add _ _

/-- The existing actual-support harmonic ideal is the normalized `K/M`
indicator used by the nominalization comparison. -/
theorem ndA5HarmonicTerminalAtomIdealMass_eq_ite_MWeight
    {B : ℕ} {branch : Tao.TaoSection5SourceBranch}
    {C : ℝ} {j : ℕ} {E : Set ℕ}
    (i : NDA5TerminalAtomIndex B branch C j E) :
    ndA5HarmonicTerminalAtomIdealMass i =
      if ndA5TerminalAtomSupported i then
        ndA5HarmonicTerminalAtomMWeight i /
          Tao.logFinsetMass (ndA5OddBand B branch j)
      else 0 := by
  rfl

/-- Normalized harmonic nominalization error before the scalar shell rate. -/
theorem abs_sum_ndA5HarmonicTerminalAtomIdealMass_sub_nominal_le_shellRatio
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
    |(∑ i : NDA5TerminalAtomIndex B branch C j E,
        ndA5HarmonicTerminalAtomIdealMass i) -
      ∑ i : NDA5TerminalAtomIndex B branch C j E,
        ndA5HarmonicTerminalAtomNominalIdealMass i| ≤
      (Tao.logFinsetMass (ndA5LowerTerminalBoundaryShell B branch j) +
        Tao.logFinsetMass (ndA5UpperTerminalBoundaryShell B branch j)) /
          Tao.logFinsetMass (ndA5OddBand B branch j) := by
  classical
  let H := Tao.logFinsetMass (ndA5OddBand B branch j)
  let P : NDA5TerminalAtomIndex B branch C j E → Prop :=
    fun i => ndA5TerminalAtomSupported i
  let Q : NDA5TerminalAtomIndex B branch C j E → Prop :=
    fun i => ndA5TerminalAtomNominalSupported i
  let w : NDA5TerminalAtomIndex B branch C j E → ℝ :=
    fun i => ndA5HarmonicTerminalAtomMWeight i
  have hHpos : 0 < H := by
    simpa only [H] using logFinsetMass_ndA5OddBand_pos
      facts.schedule.one_le_B j hcount
  have hphys :
      (∑ i : NDA5TerminalAtomIndex B branch C j E,
        ndA5HarmonicTerminalAtomIdealMass i) =
        (∑ i, if P i then w i else 0) / H := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _hi
    rw [ndA5HarmonicTerminalAtomIdealMass_eq_ite_MWeight]
    by_cases hp : P i <;> simp [P, w, H, hp]
  have hnom :
      (∑ i : NDA5TerminalAtomIndex B branch C j E,
        ndA5HarmonicTerminalAtomNominalIdealMass i) =
        (∑ i, if Q i then w i else 0) / H := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro i _hi
    unfold ndA5HarmonicTerminalAtomNominalIdealMass
    by_cases hq : Q i <;> simp [Q, w, H, hq]
  rw [hphys, hnom, ← sub_div, abs_div, abs_of_pos hHpos]
  apply div_le_div_of_nonneg_right _ hHpos.le
  simpa only [P, Q, w, H] using
    abs_sum_ndA5HarmonicTerminalAtomMWeight_phys_sub_nominal_le_shellMass
      facts hlogB ht2 htime hdiam

/-- Scalar fixed-band harmonic nominalization error. -/
theorem abs_sum_ndA5HarmonicTerminalAtomIdealMass_sub_nominal_le_five_rpow
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
    |(∑ i : NDA5TerminalAtomIndex B branch C j E,
        ndA5HarmonicTerminalAtomIdealMass i) -
      ∑ i : NDA5TerminalAtomIndex B branch C j E,
        ndA5HarmonicTerminalAtomNominalIdealMass i| ≤
      5 * (B : ℝ) ^ (-(9 / 10 : ℝ)) :=
  (abs_sum_ndA5HarmonicTerminalAtomIdealMass_sub_nominal_le_shellRatio
    facts hlogB hcount ht2 htime hdiam).trans
      (ndA5HarmonicBoundaryShellRatio_le_five_rpow_neg_nine_tenths
        facts.schedule.one_le_B hlogB j hcount)

/-- Endpoint-shaped harmonic terminal nominalization, combining the checked
denominator defect with the once-only boundary-shell charge. -/
theorem ndA5HarmonicTerminalAtomUnionMass_sub_nominalIdealSum_abs_le
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
    let μ := ndA5HarmonicBandPMF B branch j
      facts.schedule.one_le_B hcount
    let U := (μ.toOuterMeasure
      (ndA5TerminalAtomUnion B branch C j E)).toReal
    |U - ∑ i : NDA5TerminalAtomIndex B branch C j E,
        ndA5HarmonicTerminalAtomNominalIdealMass i| ≤
      (B : ℝ) ^ (-(19749 / 20000 : ℝ)) * U +
        5 * (B : ℝ) ^ (-(9 / 10 : ℝ)) := by
  classical
  dsimp only
  let μ := ndA5HarmonicBandPMF B branch j
    facts.schedule.one_le_B hcount
  let U := (μ.toOuterMeasure
    (ndA5TerminalAtomUnion B branch C j E)).toReal
  let Iphys := ∑ i : NDA5TerminalAtomIndex B branch C j E,
    ndA5HarmonicTerminalAtomIdealMass i
  let Inom := ∑ i : NDA5TerminalAtomIndex B branch C j E,
    ndA5HarmonicTerminalAtomNominalIdealMass i
  have hpair := ndA5TerminalAtoms_pairwiseDisjoint (E := E) htime hdiam
  have hden := ndA5HarmonicTerminalAtomUnionMass_sub_idealSum_nonneg_le
    facts hlogB hcount ht2 hpair
  have hnom :=
    abs_sum_ndA5HarmonicTerminalAtomIdealMass_sub_nominal_le_five_rpow
      facts hlogB hcount ht2 htime hdiam
  change |U - Inom| ≤ _
  change 0 ≤ U - Iphys ∧
      U - Iphys ≤ (B : ℝ) ^ (-(19749 / 20000 : ℝ)) * U at hden
  change |Iphys - Inom| ≤ 5 * (B : ℝ) ^ (-(9 / 10 : ℝ)) at hnom
  rw [show U - Inom = (U - Iphys) + (Iphys - Inom) by ring]
  calc
    |(U - Iphys) + (Iphys - Inom)| ≤
        |U - Iphys| + |Iphys - Inom| := abs_add_le _ _
    _ = (U - Iphys) + |Iphys - Inom| := by
      rw [abs_of_nonneg hden.1]
    _ ≤ (B : ℝ) ^ (-(19749 / 20000 : ℝ)) * U +
        5 * (B : ℝ) ^ (-(9 / 10 : ℝ)) :=
      add_le_add hden.2 hnom

end

end ND
end Erdos1135
