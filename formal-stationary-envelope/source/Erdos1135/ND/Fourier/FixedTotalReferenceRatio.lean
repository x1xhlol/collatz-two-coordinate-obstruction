/-
Compatibility modification, 8 October 2026: proof elaboration and unused bound-variable names only.
See provenance/envelope-linter-patches.json for exact source hashes and patches.
-/
import Erdos1135.ND.Fourier.FixedTotalSourceLaw
import Erdos1135.ND.Fourier.FixedTotalDisintegration

/-!
# Fixed-Total Head Law Versus The Endpoint Reference

This leaf starts the post-D6 likelihood-ratio pilot.  It exposes the
conditioned prefix-total law on `Nat` and proves its exact atom factorization
against the unconditioned Geom(2) endpoint law.  The statement includes every
`u`, so impossible low and high totals vanish without a support facade.

The later central likelihood-ratio estimate will compare this law with
`ndGeom2EndpointPMF j`.  No full-L1 replacement is made here.
-/

namespace Erdos1135
namespace ND

open scoped BigOperators

open Tao

noncomputable section

/-- The prefix total at length `j` under the fixed-total length-`n`, total-`L`
law.  The dependent split carrier retains the matching suffix total. -/
noncomputable def ndFixedTotalHeadTotalPMF
    (j n L : ℕ) (hj : 0 < j) (hjn : j < n) (hnL : n ≤ L) : PMF ℕ :=
  (ndFixedTotalSplitIndexPMF j (n - j) L hj (by omega)).map
    (fun s => s.headTotal)

/-- Every prefix-total atom is the product of its prefix and suffix endpoint
masses divided by the parent endpoint mass.  This includes all impossible
`u`: one of the two numerator endpoint masses then vanishes. -/
theorem ndFixedTotalHeadTotalPMF_apply_toReal
    {j n L : ℕ} (hj : 0 < j) (hjn : j < n) (hnL : n ≤ L)
    (u : ℕ) :
    (ndFixedTotalHeadTotalPMF j n L hj hjn hnL u).toReal =
      ndGeom2EndpointMass j u *
        ndGeom2EndpointMass (n - j) (L - u) /
          ndGeom2EndpointMass n L := by
  let hsplit : j + (n - j) ≤ L := by omega
  have hzero_of_no_preimage
      (hno : ∀ s : NDFixedTotalSplitIndex j (n - j) L,
        s.headTotal ≠ u) :
      ndFixedTotalHeadTotalPMF j n L hj hjn hnL u = 0 := by
    unfold ndFixedTotalHeadTotalPMF
    rw [PMF.map_apply, ENNReal.tsum_eq_zero]
    intro s
    have hu : u ≠ s.headTotal := (hno s).symm
    simp [hu]
  by_cases hju : j ≤ u
  · by_cases huL : u ≤ L
    · by_cases htail : n - j ≤ L - u
      · let s : NDFixedTotalSplitIndex j (n - j) L := {
          headTotal := u
          tailTotal := L - u
          headLength_le := hju
          tailLength_le := htail
          total_eq := by omega
        }
        have hs_unique
            (s' : NDFixedTotalSplitIndex j (n - j) L)
            (hu' : u = s'.headTotal) :
            s' = s := by
          apply NDFixedTotalSplitIndex.ext
          · exact hu'.symm
          · have htotal := s'.total_eq
            dsimp [s]
            omega
        have hmap :
            ndFixedTotalHeadTotalPMF j n L hj hjn hnL u =
              ndFixedTotalSplitIndexPMF j (n - j) L hj hsplit s := by
          unfold ndFixedTotalHeadTotalPMF
          rw [PMF.map_apply, tsum_eq_single s]
          · simp [s]
          · intro s' hne
            have hhead : u ≠ s'.headTotal := by
              intro hu'
              exact hne (hs_unique s' hu')
            simp [hhead]
        rw [hmap,
          ndFixedTotalSplitIndexPMF_apply_toReal]
        simp [s, Nat.add_sub_of_le (Nat.le_of_lt hjn)]
      · have hlt : L - u < n - j := by omega
        have hmapZero :
            ndFixedTotalHeadTotalPMF j n L hj hjn hnL u = 0 := by
          apply hzero_of_no_preimage
          intro s hs
          have htotal := s.total_eq
          have htailLe := s.tailLength_le
          omega
        rw [hmapZero, ndGeom2EndpointMass_eq_zero_of_lt hlt]
        simp
    · have hlt : L - u < n - j := by omega
      have hmapZero :
          ndFixedTotalHeadTotalPMF j n L hj hjn hnL u = 0 := by
        apply hzero_of_no_preimage
        intro s hs
        have htotal := s.total_eq
        omega
      rw [hmapZero, ndGeom2EndpointMass_eq_zero_of_lt hlt]
      simp
  · have hlt : u < j := by omega
    have hmapZero :
        ndFixedTotalHeadTotalPMF j n L hj hjn hnL u = 0 := by
      apply hzero_of_no_preimage
      intro s hs
      have hheadLe := s.headLength_le
      omega
    rw [hmapZero, ndGeom2EndpointMass_eq_zero_of_lt hlt]
    simp

/-- A bounded nonnegative test integrated against a countable PMF. -/
noncomputable def ndPMFWeightedExpectation
    {alpha : Type*} (p : PMF alpha) (phi : alpha → ℝ) : ℝ :=
  ∑' u, (p u).toReal * phi u

/-- Real PMF mass outside a predicate, kept as a native countable sum for the
central-plus-tail likelihood-ratio argument. -/
noncomputable def ndPMFOutsideMass
    {alpha : Type*} (p : PMF alpha) (Good : alpha → Prop) : ℝ := by
  classical
  exact ∑' u, if Good u then 0 else (p u).toReal

private theorem ndPMFWeightedExpectation_summable_of_nonneg_le
    {alpha : Type*} (p : PMF alpha) (phi : alpha → ℝ) (H : ℝ)
    (hphi0 : ∀ u, 0 ≤ phi u) (hphiH : ∀ u, phi u ≤ H) :
    Summable fun u => (p u).toReal * phi u := by
  have hp : Summable fun u : alpha => H * (p u).toReal :=
    (Tao.taoPMF_summable_toReal p).mul_left H
  exact Summable.of_nonneg_of_le
    (fun u => mul_nonneg ENNReal.toReal_nonneg (hphi0 u))
    (fun u => by
      have h := mul_le_mul_of_nonneg_left (hphiH u)
        (show 0 ≤ (p u).toReal from ENNReal.toReal_nonneg)
      simpa [mul_comm] using h)
    hp

private theorem ndPMFOutsideMass_summable
    {alpha : Type*} (p : PMF alpha) (Good : alpha → Prop)
    [DecidablePred Good] :
    Summable fun u => if Good u then 0 else (p u).toReal := by
  classical
  exact Summable.of_nonneg_of_le
    (fun u => by
      by_cases hu : Good u <;> simp [hu, ENNReal.toReal_nonneg])
    (fun u => by
      by_cases hu : Good u <;> simp [hu, ENNReal.toReal_nonneg])
    (Tao.taoPMF_summable_toReal p)

/-- Neutral signed central-plus-tail algebra for the direct likelihood-ratio
route.  A relative comparison on the central set is charged against the full
reference expectation, while only the two outside masses pay the absolute
test bound. -/
theorem abs_ndPMFWeightedDifference_le_reference_add_outside
    {alpha : Type*} (p q : PMF alpha) (Good : alpha → Prop)
    (phi : alpha → ℝ) (H centralCoeff deltaP deltaQ : ℝ)
    (hH : 0 ≤ H) (hcentralCoeff : 0 ≤ centralCoeff)
    (hphi0 : ∀ u, 0 ≤ phi u) (hphiH : ∀ u, phi u ≤ H)
    (hcentral : ∀ u, Good u →
      |(p u).toReal - (q u).toReal| ≤ centralCoeff * (q u).toReal)
    (hpOutside : ndPMFOutsideMass p Good ≤ deltaP)
    (hqOutside : ndPMFOutsideMass q Good ≤ deltaQ) :
    |∑' u, ((p u).toReal - (q u).toReal) * phi u| ≤
      centralCoeff * ndPMFWeightedExpectation q phi +
        H * (deltaP + deltaQ) := by
  classical
  let f : alpha → ℝ := fun u =>
    ((p u).toReal - (q u).toReal) * phi u
  let tailP : alpha → ℝ := fun u =>
    if Good u then 0 else (p u).toReal
  let tailQ : alpha → ℝ := fun u =>
    if Good u then 0 else (q u).toReal
  let g : alpha → ℝ := fun u =>
    centralCoeff * ((q u).toReal * phi u) +
      H * (tailP u + tailQ u)
  have hpPhi :=
    ndPMFWeightedExpectation_summable_of_nonneg_le p phi H hphi0 hphiH
  have hqPhi :=
    ndPMFWeightedExpectation_summable_of_nonneg_le q phi H hphi0 hphiH
  have hf : Summable f := by
    have h := hpPhi.sub hqPhi
    exact h.congr fun u => by
      dsimp [f]
      ring
  have htailP : Summable tailP := by
    simpa [tailP] using ndPMFOutsideMass_summable p Good
  have htailQ : Summable tailQ := by
    simpa [tailQ] using ndPMFOutsideMass_summable q Good
  have hg : Summable g := by
    have hRef : Summable fun u =>
        centralCoeff * ((q u).toReal * phi u) :=
      hqPhi.mul_left centralCoeff
    have hTail : Summable fun u =>
        H * (tailP u + tailQ u) :=
      (htailP.add htailQ).mul_left H
    exact hRef.add hTail
  have hpoint : ∀ u, |f u| ≤ g u := by
    intro u
    by_cases hu : Good u
    · have hphiAbs : |phi u| = phi u := abs_of_nonneg (hphi0 u)
      calc
        |f u| = |(p u).toReal - (q u).toReal| * phi u := by
          simp [f, abs_mul, hphiAbs]
        _ ≤ (centralCoeff * (q u).toReal) * phi u :=
          mul_le_mul_of_nonneg_right (hcentral u hu) (hphi0 u)
        _ ≤ g u := by
          dsimp [g, tailP, tailQ]
          rw [if_pos hu, if_pos hu]
          simp [mul_assoc]
    · have hp0 : 0 ≤ (p u).toReal := ENNReal.toReal_nonneg
      have hq0 : 0 ≤ (q u).toReal := ENNReal.toReal_nonneg
      have habs : |(p u).toReal - (q u).toReal| ≤
          (p u).toReal + (q u).toReal := by
        calc
          |(p u).toReal - (q u).toReal| ≤
              |(p u).toReal| + |(q u).toReal| := abs_sub _ _
          _ = (p u).toReal + (q u).toReal := by
            rw [abs_of_nonneg hp0, abs_of_nonneg hq0]
      have htail : |f u| ≤
          H * ((p u).toReal + (q u).toReal) := by
        calc
          |f u| = |(p u).toReal - (q u).toReal| * phi u := by
            simp [f, abs_mul, abs_of_nonneg (hphi0 u)]
          _ ≤ ((p u).toReal + (q u).toReal) * phi u :=
            mul_le_mul_of_nonneg_right habs (hphi0 u)
          _ ≤ ((p u).toReal + (q u).toReal) * H :=
            mul_le_mul_of_nonneg_left (hphiH u) (add_nonneg hp0 hq0)
          _ = H * ((p u).toReal + (q u).toReal) := by ring
      calc
        |f u| ≤ H * ((p u).toReal + (q u).toReal) := htail
        _ ≤ g u := by
          dsimp [g, tailP, tailQ]
          rw [if_neg hu, if_neg hu]
          have href : 0 ≤ centralCoeff * ((q u).toReal * phi u) :=
            mul_nonneg hcentralCoeff (mul_nonneg hq0 (hphi0 u))
          linarith
  have habsTsum : |∑' u, f u| ≤ ∑' u, |f u| := by
    simpa only [Real.norm_eq_abs] using
      norm_tsum_le_tsum_norm hf.norm
  have hfg : (∑' u, |f u|) ≤ ∑' u, g u :=
    hf.abs.tsum_le_tsum hpoint hg
  have hg_eval :
      (∑' u, g u) =
        centralCoeff * ndPMFWeightedExpectation q phi +
          H * (ndPMFOutsideMass p Good + ndPMFOutsideMass q Good) := by
    have hRef : Summable fun u =>
        centralCoeff * ((q u).toReal * phi u) :=
      hqPhi.mul_left centralCoeff
    have hTail : Summable fun u =>
        H * (tailP u + tailQ u) :=
      (htailP.add htailQ).mul_left H
    rw [show (∑' u, g u) =
        (∑' u, centralCoeff * ((q u).toReal * phi u)) +
          ∑' u, H * (tailP u + tailQ u) by
      simpa [g] using hRef.tsum_add hTail]
    rw [tsum_mul_left, tsum_mul_left, (htailP.tsum_add htailQ)]
    rfl
  calc
    |∑' u, ((p u).toReal - (q u).toReal) * phi u| =
        |∑' u, f u| := by rfl
    _ ≤ ∑' u, |f u| := habsTsum
    _ ≤ ∑' u, g u := hfg
    _ = centralCoeff * ndPMFWeightedExpectation q phi +
          H * (ndPMFOutsideMass p Good + ndPMFOutsideMass q Good) := hg_eval
    _ ≤ centralCoeff * ndPMFWeightedExpectation q phi +
          H * (deltaP + deltaQ) := by
      gcongr


end

end ND
end Erdos1135
