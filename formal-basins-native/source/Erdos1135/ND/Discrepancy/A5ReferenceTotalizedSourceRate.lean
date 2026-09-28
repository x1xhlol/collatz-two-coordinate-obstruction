import Erdos1135.ND.Discrepancy.A5ReferenceGenuineSourceRate
import Erdos1135.ND.Probability.PassTotalizer
import Erdos1135.Tao.Probability.FullL1

/-!
# A5 common-target totalized source rates

This leaf applies the neutral complement totalizer and one finite Hahn step to
the checked genuine whole-source comparisons.  Both source branches use the
same passage target `B` and therefore the same finite output carrier.
-/

namespace Erdos1135
namespace ND

open Filter
open scoped Topology

noncomputable section

private def ndNatCastPassCarrierEquiv (B : ℕ) :
    {M : ℕ // M ≤ B} ≃ {M : ℕ // M ≤ Nat.floor (B : ℝ)} where
  toFun M := ⟨M.1, by simpa using M.2⟩
  invFun M := ⟨M.1, by simpa using M.2⟩
  left_inv M := by apply Subtype.ext; rfl
  right_inv M := by apply Subtype.ext; rfl

private theorem val_syracusePassLocationAtMostOrOne_eq_of_eq
    {B B' N : ℕ} (hBB' : B = B')
    (hB : 1 ≤ B) (hB' : 1 ≤ B') :
    (Tao.syracusePassLocationAtMostOrOne B N hB).1 =
      (Tao.syracusePassLocationAtMostOrOne B' N hB').1 := by
  subst B'
  rfl

private theorem taoTV_map_equiv
    {α β : Type*} [Fintype α] [Fintype β]
    (p q : PMF α) (e : α ≃ β) :
    Tao.taoTV (p.map e) (q.map e) = Tao.taoTV p q := by
  apply le_antisymm
  · exact Tao.taoTV_map_le p q e
  · have h := Tao.taoTV_map_le (p.map e) (q.map e) e.symm
    have he : e.symm ∘ e = id := by
      funext x
      exact e.symm_apply_apply x
    rw [PMF.map_comp, PMF.map_comp, he, PMF.map_id, PMF.map_id] at h
    exact h

/-- The totalized flat and harmonic passage laws on either source branch are
within thirty-two reference-rate copies in project full L1. -/
theorem eventually_ndA5FlatHarmonicTotalizedPassTV_le_thirty_two
    {c kappa d : ℝ}
    (hPhase : PhaseGap c kappa)
    (hd : 0 < d) (hd20 : d < 1 / 20)
    (hdk : d < 1 / (2 * kappa)) :
    ∀ᶠ B : ℕ in atTop,
      ∀ (branch : Tao.TaoSection5SourceBranch)
        (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch),
        Tao.taoTV
            (ndTotalizedPassLaw B hB
              (ndA5FlatSourcePMF B branch hB hcount))
            (ndTotalizedPassLaw B hB
              (ndA5HarmonicSourcePMF B branch hB hcount)) ≤
          32 * ndA5ReferenceInteriorScalarRate B d := by
  filter_upwards
      [eventually_abs_ndA5HarmonicSourcePassMass_sub_flat_le_sixteen
        hPhase hd hd20 hdk]
      with B hsource
  intro branch hB hcount
  have hgen : ∀ E : Set ℕ,
      |((ndA5FlatSourcePMF B branch hB hcount).toOuterMeasure
            (Tao.taoSection5PassEvent B E)).toReal -
        ((ndA5HarmonicSourcePMF B branch hB hcount).toOuterMeasure
            (Tao.taoSection5PassEvent B E)).toReal| ≤
          16 * ndA5ReferenceInteriorScalarRate B d := by
    intro E
    simpa only [abs_sub_comm] using hsource branch E hB hcount
  have hTV := taoTV_ndTotalizedPassLaw_le_two_mul_of_genuine
    hB (ndA5FlatSourcePMF B branch hB hcount)
      (ndA5HarmonicSourcePMF B branch hB hcount) hgen
  calc
    Tao.taoTV
        (ndTotalizedPassLaw B hB
          (ndA5FlatSourcePMF B branch hB hcount))
        (ndTotalizedPassLaw B hB
          (ndA5HarmonicSourcePMF B branch hB hcount)) ≤
      2 * (16 * ndA5ReferenceInteriorScalarRate B d) := hTV
    _ = 32 * ndA5ReferenceInteriorScalarRate B d := by ring

/-- The two harmonic source branches have totalized passage laws within
thirty-two reference-rate copies, the LOG-BLOCK sibling endpoint. -/
theorem eventually_ndA5HarmonicBranchesTotalizedPassTV_le_thirty_two
    {c kappa d : ℝ}
    (hPhase : PhaseGap c kappa)
    (hd : 0 < d) (hd20 : d < 1 / 20)
    (hdk : d < 1 / (2 * kappa)) :
    ∀ᶠ B : ℕ in atTop,
      ∀ (branch₁ branch₂ : Tao.TaoSection5SourceBranch)
        (hB : 1 ≤ B)
        (hcount₁ : 0 < ndA5BandCount B branch₁)
        (hcount₂ : 0 < ndA5BandCount B branch₂),
        Tao.taoTV
            (ndTotalizedPassLaw B hB
              (ndA5HarmonicSourcePMF B branch₁ hB hcount₁))
            (ndTotalizedPassLaw B hB
              (ndA5HarmonicSourcePMF B branch₂ hB hcount₂)) ≤
          32 * ndA5ReferenceInteriorScalarRate B d := by
  filter_upwards
      [eventually_abs_ndA5HarmonicSourcePassMass_sub_harmonic_le_sixteen
        hPhase hd hd20 hdk]
      with B hsource
  intro branch₁ branch₂ hB hcount₁ hcount₂
  have hgen : ∀ E : Set ℕ,
      |((ndA5HarmonicSourcePMF B branch₁ hB hcount₁).toOuterMeasure
            (Tao.taoSection5PassEvent B E)).toReal -
        ((ndA5HarmonicSourcePMF B branch₂ hB hcount₂).toOuterMeasure
            (Tao.taoSection5PassEvent B E)).toReal| ≤
          16 * ndA5ReferenceInteriorScalarRate B d := by
    intro E
    exact hsource branch₁ branch₂ E hB hcount₁ hcount₂
  have hTV := taoTV_ndTotalizedPassLaw_le_two_mul_of_genuine
    hB (ndA5HarmonicSourcePMF B branch₁ hB hcount₁)
      (ndA5HarmonicSourcePMF B branch₂ hB hcount₂) hgen
  calc
    Tao.taoTV
        (ndTotalizedPassLaw B hB
          (ndA5HarmonicSourcePMF B branch₁ hB hcount₁))
        (ndTotalizedPassLaw B hB
          (ndA5HarmonicSourcePMF B branch₂ hB hcount₂)) ≤
      2 * (16 * ndA5ReferenceInteriorScalarRate B d) := hTV
    _ = 32 * ndA5ReferenceInteriorScalarRate B d := by ring

/-- At a natural passage target, the ND public full-L1 convention is exactly
the common-target totalized A5 flat/harmonic distance. -/
theorem passFullL1_natCast_taoSection5SourceY_eq_ndA5TotalizedPassTV
    {B : ℕ} (hB : 1 ≤ B) (branch : Tao.TaoSection5SourceBranch)
    (hcount : 0 < ndA5BandCount B branch) :
    passFullL1 (B : ℝ) (Tao.taoSection5SourceY B branch)
        (show (1 : ℝ) ≤ B by exact_mod_cast hB)
        (ndA5OddBlock_sourceY_nonempty hB branch hcount)
        (logFinsetMass_ndA5OddBlock_sourceY_pos hB branch hcount) =
      Tao.taoTV
        (ndTotalizedPassLaw B hB
          (ndA5FlatSourcePMF B branch hB hcount))
        (ndTotalizedPassLaw B hB
          (ndA5HarmonicSourcePMF B branch hB hcount)) := by
  let e := ndNatCastPassCarrierEquiv B
  let p := ndTotalizedPassLaw B hB
    (ndA5FlatSourcePMF B branch hB hcount)
  let q := ndTotalizedPassLaw B hB
    (ndA5HarmonicSourcePMF B branch hB hcount)
  have hflat :
      uniformPassLaw (B : ℝ) (Tao.taoSection5SourceY B branch)
          (show (1 : ℝ) ≤ B by exact_mod_cast hB)
          (ndA5OddBlock_sourceY_nonempty hB branch hcount) =
        p.map e := by
    dsimp only [p, e]
    unfold uniformPassLaw ndA5FlatSourcePMF ndTotalizedPassLaw
    rw [PMF.map_comp, PMF.map_comp]
    congr 1
    funext N
    apply Subtype.ext
    change
      (Tao.syracusePassLocationAtMostOrOne (Nat.floor (B : ℝ)) N.1 _).1 =
        (Tao.syracusePassLocationAtMostOrOne B N.1 hB).1
    exact val_syracusePassLocationAtMostOrOne_eq_of_eq
      (Nat.floor_natCast B) _ _
  have hharmonic :
      logPassLaw (B : ℝ) (Tao.taoSection5SourceY B branch)
          (show (1 : ℝ) ≤ B by exact_mod_cast hB)
          (logFinsetMass_ndA5OddBlock_sourceY_pos hB branch hcount) =
        q.map e := by
    dsimp only [q, e]
    unfold logPassLaw ndA5HarmonicSourcePMF ndTotalizedPassLaw
    rw [PMF.map_comp, PMF.map_comp]
    congr 1
    funext N
    apply Subtype.ext
    change
      (Tao.syracusePassLocationAtMostOrOne (Nat.floor (B : ℝ)) N.1 _).1 =
        (Tao.syracusePassLocationAtMostOrOne B N.1 hB).1
    exact val_syracusePassLocationAtMostOrOne_eq_of_eq
      (Nat.floor_natCast B) _ _
  unfold passFullL1
  rw [hflat, hharmonic]
  exact taoTV_map_equiv p q e

/-- Consumer-shaped natural-target specialization of the ND public
`passFullL1` convention. -/
theorem eventually_passFullL1_natCast_taoSection5SourceY_le_thirty_two
    {c kappa d : ℝ}
    (hPhase : PhaseGap c kappa)
    (hd : 0 < d) (hd20 : d < 1 / 20)
    (hdk : d < 1 / (2 * kappa)) :
    ∀ᶠ B : ℕ in atTop,
      ∀ (branch : Tao.TaoSection5SourceBranch)
        (hB : 1 ≤ B) (hcount : 0 < ndA5BandCount B branch),
        passFullL1 (B : ℝ) (Tao.taoSection5SourceY B branch)
            (show (1 : ℝ) ≤ B by exact_mod_cast hB)
            (ndA5OddBlock_sourceY_nonempty hB branch hcount)
            (logFinsetMass_ndA5OddBlock_sourceY_pos hB branch hcount) ≤
          32 * ndA5ReferenceInteriorScalarRate B d := by
  filter_upwards
      [eventually_ndA5FlatHarmonicTotalizedPassTV_le_thirty_two
        hPhase hd hd20 hdk]
      with B hTV
  intro branch hB hcount
  rw [passFullL1_natCast_taoSection5SourceY_eq_ndA5TotalizedPassTV
    hB branch hcount]
  exact hTV branch hB hcount

end
end ND
end Erdos1135
