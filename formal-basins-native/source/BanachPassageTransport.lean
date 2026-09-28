import BanachFiniteProbability
import NativeWeightedPassageComparison

open Filter
open scoped Topology

namespace CollatzCanonical.LabelLaw
open CollatzCylinderPacking.Arithmetic CollatzCanonical.NativeTao Erdos1135.Tao

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

noncomputable def pmfMeanV {ι : Type*} [Fintype ι] (p : PMF ι) (f : ι → V) : V :=
  finiteMeanV (fun i => (p i).toReal) f

def EventuallyPassageInvariant (F : ℕ → V) : Prop :=
  ∀ᶠ x : ℝ in atTop, ∀ (q : ℕ), Odd q → ∀ (τ : ℕ),
    syracuseFirstHitAtMostReal x q τ → F q = F ((syracuse^[τ]) q)

/-- A successful actual passage preserves the observable. The no-hit
event pays at most twice its probability for a unit-ball Banach observable. -/
theorem native_real_windows_vector_comparison (F : ℕ → V)
    (hF : ∀ q, ‖F q‖ ≤ 1) (x : ℝ) (hx : 1 ≤ x)
    (hpass : ∀ (q : ℕ), Odd q → ∀ τ,
      syracuseFirstHitAtMostReal x q τ → F q = F ((syracuse^[τ]) q))
    (lo₁ hi₁ lo₂ hi₂ : ℕ)
    (hmass₁ : 0 < logFinsetMass (oddLogWindow lo₁ hi₁))
    (hmass₂ : 0 < logFinsetMass (oddLogWindow lo₂ hi₂)) :
    ‖pmfMeanV (oddLogWindowPMF lo₁ hi₁ hmass₁) (fun q => F q.1) -
      pmfMeanV (oddLogWindowPMF lo₂ hi₂ hmass₂) (fun q => F q.1)‖ ≤
      2 * syracuseNoHitRealWindowProb x lo₁ hi₁ hmass₁ +
        2 * syracuseNoHitRealWindowProb x lo₂ hi₂ hmass₂ +
          syracusePassRealFloorWindowTV x lo₁ hi₁ lo₂ hi₂ hx hmass₁ hmass₂ := by
  classical
  have hgood {lo hi : ℕ} (q : {n // n ∈ oddLogWindow lo hi})
      (hq : ¬¬syracuseHitsAtMostReal q.1 x) :
      F q.1 = F (syracusePassLocationRealFloorOrOne x q.1 hx).1 := by
    have hx0 : 0 ≤ x := by linarith
    have hh := (syracuseHitsAtMostReal_iff_floor hx0).mp (not_not.mp hq)
    have hn := syracuseFirstHitAtMost_of_hitsAtMost q.1 ⌊x⌋₊ hh
    have hreal := (syracuseFirstHitAtMostReal_iff_floor hx0).mpr hn
    rw [native_real_passLocation_eq_of_first hx hreal]
    exact hpass q.1 (oddLogWindowValueToOddNat q).2 _ hreal
  have he := finiteMeanV_two_passage_bound
    (fun q => ((oddLogWindowPMF lo₁ hi₁ hmass₁) q).toReal)
    (fun q => ((oddLogWindowPMF lo₂ hi₂ hmass₂) q).toReal)
    (fun q => F q.1) (fun q => F q.1)
    (fun q => syracusePassLocationRealFloorOrOne x q.1 hx)
    (fun q => syracusePassLocationRealFloorOrOne x q.1 hx)
    (fun q => F q.1)
    (fun q => ¬syracuseHitsAtMostReal q.1 x)
    (fun q => ¬syracuseHitsAtMostReal q.1 x)
    (fun _ => ENNReal.toReal_nonneg) (fun _ => ENNReal.toReal_nonneg)
    (fun q => hF q.1) (fun q => hF q.1) (fun q => hF q.1) hgood hgood
  rw [finiteBadMass_eq_native_probability, finiteBadMass_eq_native_probability,
    finite_landing_fullL1_eq_native_TV] at he
  exact he

end CollatzCanonical.LabelLaw

#print axioms CollatzCanonical.LabelLaw.native_real_windows_vector_comparison
