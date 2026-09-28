import Erdos1135.ND.Fourier.FixedSplitCollision
import Erdos1135.Tao.Section6.FixedAmbientSlice

/-!
# Raw Fixed-Total Ambient Slices

This leaf intersects Tao's exact fixed-ambient head slice with one full
valuation total before mapping to residues.  At an additive ambient level,
every inhabited slice is exactly the existing fixed-split source submass with
factor one.  The zero branch retains no fictitious structural split, while the
inhabited branch records both a complete source-gate witness and an inhabited
dependent split fiber.

No endpoint mass, normalized split weight, or denominator occurs here.
-/

namespace Erdos1135
namespace ND

open Tao

noncomputable section

/-- Tao's fixed-ambient head gate intersected with the exact full valuation
total.  The intersection occurs on the iid source before the residue map. -/
noncomputable def ndSection6FixedTotalAmbientGate
    (CA : ℝ) (n k l L : ℕ) (full : List ℕ+) : Prop :=
  Tao.taoSection6FixedAmbientGate CA n k l full ∧
    Tao.taoTupleWeight full = L

/-- Raw accepted residue mass for one fixed ambient head slice and one full
valuation total.  This is a defective submass, not a conditioned law. -/
noncomputable def ndSection6FixedTotalAmbientSubmass
    (CA : ℝ) (n k l L : ℕ) (x : ZMod (3 ^ n)) : ℝ :=
  Tao.taoGatedSubmass
    (Tao.geom2PNatListPMF n)
    (ndSection6FixedTotalAmbientGate CA n k l L)
    (Tao.taoSection7OffsetZMod n) x

/-- At an additive ambient level, selecting the head total stored in a split
index gives exactly the existing fixed-split source submass.  The two source
predicates agree on the exact-length support; all off-length Geom(2) atoms
vanish.  The equality has factor one, including empty split fibers. -/
theorem ndSection6FixedTotalAmbientSubmass_add_eq_fixedSplit
    (CA : ℝ) (T k L : ℕ)
    (s : NDFixedTotalSplitIndex (k + 1) T L) :
    ndSection6FixedTotalAmbientSubmass
        CA (T + (k + 1)) k s.headTotal L =
      ndSection6FixedSplitSourceSubmass CA T k L s := by
  funext x
  unfold ndSection6FixedTotalAmbientSubmass Tao.taoGatedSubmass
  unfold ndSection6FixedSplitSourceSubmass ndSection6FixedSplitSourcePMF
  unfold Tao.taoGatedOptionPMF
  apply congrArg ENNReal.toReal
  rw [PMF.map_apply, PMF.map_apply]
  apply tsum_congr
  intro full
  by_cases hlength : full.length = T + (k + 1)
  · have hgate :
        ndSection6FixedTotalAmbientGate
              CA (T + (k + 1)) k s.headTotal L full ↔
          ndSection6FixedSplitSourceGate CA T k L s full := by
      rw [ndSection6FixedSplitSourceGate_iff_headGate_and_weight]
      simp [ndSection6FixedTotalAmbientGate,
        Tao.taoSection6FixedAmbientGate, hlength]
    have hkey :
        Tao.taoGatedOptionKey
            (ndSection6FixedTotalAmbientGate
              CA (T + (k + 1)) k s.headTotal L)
            (Tao.taoSection7OffsetZMod (T + (k + 1))) full =
          Tao.taoGatedOptionKey
            (ndSection6FixedSplitSourceGate CA T k L s)
            (Tao.taoSection7OffsetZMod (T + (k + 1))) full := by
      unfold Tao.taoGatedOptionKey
      by_cases hleft :
          ndSection6FixedTotalAmbientGate
            CA (T + (k + 1)) k s.headTotal L full
      · rw [if_pos hleft, if_pos (hgate.mp hleft)]
      · rw [if_neg hleft,
          if_neg (fun hright => hleft (hgate.mpr hright))]
    rw [hkey]
  · have hzero :
        Tao.geom2PNatListPMF (T + (k + 1)) full = 0 :=
      Tao.geom2PNatListPMF_apply_eq_zero_of_length_ne _ _ hlength
    simp [hzero]

/-- Every arbitrary fixed-total ambient slice is either the zero vector or
comes from a complete accepted source and an actually inhabited dependent
split fiber.  Retaining both witnesses prevents a structural zero-tail index
from being mistaken for a feasible slice. -/
theorem
    ndSection6FixedTotalAmbientSubmass_add_eq_zero_or_exists_gate_fixedSplit
    (CA : ℝ) (T k l L : ℕ) :
    ndSection6FixedTotalAmbientSubmass
        CA (T + (k + 1)) k l L = (fun _ => 0) ∨
      ∃ full : List ℕ+,
        ndSection6FixedTotalAmbientGate
            CA (T + (k + 1)) k l L full ∧
          ∃ s : NDFixedTotalSplitIndex (k + 1) T L,
            s.headTotal = l ∧
              Nonempty (NDFixedTotalSplitFiber s) ∧
                ndSection6FixedTotalAmbientSubmass
                    CA (T + (k + 1)) k l L =
                  ndSection6FixedSplitSourceSubmass CA T k L s := by
  classical
  by_cases hfull : ∃ full : List ℕ+,
      ndSection6FixedTotalAmbientGate
        CA (T + (k + 1)) k l L full
  · right
    obtain ⟨full, hgate⟩ := hfull
    have hlength : full.length = T + (k + 1) := hgate.1.1
    let a : NDFixedTotalValuations ((k + 1) + T) L :=
      ⟨full, ⟨by omega, hgate.2⟩⟩
    let z : NDFixedTotalSplit (k + 1) T L :=
      (ndFixedTotalValuationsEquivSplit (k + 1) T L) a
    let s : NDFixedTotalSplitIndex (k + 1) T L := z.1
    have hs : s.headTotal = l := by
      dsimp only [s, z]
      rw [ndFixedTotalValuationsEquivSplit_headTotal]
      exact Tao.taoSection6HeadGate_weight hgate.1.2
    refine ⟨full, hgate, s, hs, ⟨z.2⟩, ?_⟩
    rw [← hs]
    exact ndSection6FixedTotalAmbientSubmass_add_eq_fixedSplit CA T k L s
  · left
    funext x
    unfold ndSection6FixedTotalAmbientSubmass
    exact Tao.taoGatedSubmass_eq_zero_of_not_exists_gate
      (Tao.geom2PNatListPMF (T + (k + 1)))
      (ndSection6FixedTotalAmbientGate
        CA (T + (k + 1)) k l L)
      (Tao.taoSection7OffsetZMod (T + (k + 1))) hfull x

/-- Consumer-facing weakening of the witness-retaining dichotomy.  It keeps a
whole-function equality suitable for rewriting oscillation, while the
stronger theorem above remains available when the head-gate and inhabited
fiber witnesses are needed. -/
theorem ndSection6FixedTotalAmbientSubmass_add_eq_zero_or_exists_fixedSplit
    (CA : ℝ) (T k l L : ℕ) :
    ndSection6FixedTotalAmbientSubmass
        CA (T + (k + 1)) k l L = (fun _ => 0) ∨
      ∃ s : NDFixedTotalSplitIndex (k + 1) T L,
        s.headTotal = l ∧
          ndSection6FixedTotalAmbientSubmass
              CA (T + (k + 1)) k l L =
            ndSection6FixedSplitSourceSubmass CA T k L s := by
  rcases
      ndSection6FixedTotalAmbientSubmass_add_eq_zero_or_exists_gate_fixedSplit
        CA T k l L with
    hzero | ⟨full, hgate, s, hs, hfiber, heq⟩
  · exact Or.inl hzero
  · exact Or.inr ⟨s, hs, heq⟩

end

end ND
end Erdos1135
