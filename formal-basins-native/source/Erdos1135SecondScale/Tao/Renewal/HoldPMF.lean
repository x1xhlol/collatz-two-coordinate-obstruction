/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Probability.PascalPrimeList
import Erdos1135SecondScale.Tao.Renewal.HoldPoint

/-!
# Section 7 Hold PMF

This module defines the stochastic `Hold` law from Tao Section 7.3 as a
Geom(4) first-hit index together with an iid Pascal-prime source prefix.  It is
kept free of Fourier, Q-finite, and source-list bridge imports.
-/

namespace Erdos1135SecondScale
namespace Tao

/-- Prefix sum together with the terminal Pascal-prime value `3`. -/
def taoSection7HoldTerminalSum (pre : List ℕ) : ℕ :=
  pre.sum + 3

/-- Renewal point produced by a no-three Pascal-prime prefix before the terminal `3`. -/
def taoSection7HoldPointOfPrefix (m : ℕ) (pre : List ℕ) :
    TaoSection7RenewalPoint :=
  { j := ⟨m + 1, Nat.succ_pos m⟩
    l := Int.ofNat (taoSection7HoldTerminalSum pre) }

@[simp] theorem taoSection7HoldPointOfPrefix_j (m : ℕ) (pre : List ℕ) :
    (taoSection7HoldPointOfPrefix m pre).j =
      ⟨m + 1, Nat.succ_pos m⟩ :=
  rfl

@[simp] theorem taoSection7HoldPointOfPrefix_l (m : ℕ) (pre : List ℕ) :
    (taoSection7HoldPointOfPrefix m pre).l =
      Int.ofNat (taoSection7HoldTerminalSum pre) :=
  rfl

theorem taoSection7HoldPointOfPrefix_zero_nil :
    taoSection7HoldPointOfPrefix 0 [] =
      ({ j := (1 : ℕ+), l := (3 : ℤ) } : TaoSection7RenewalPoint) := by
  ext <;> simp [taoSection7HoldPointOfPrefix, taoSection7HoldTerminalSum]

/-- The Section 7 `Hold` PMF: miss count from `Geom(4)` and source prefix of that length. -/
noncomputable def taoSection7HoldPMF : PMF TaoSection7RenewalPoint :=
  geom4Nat.bind fun m =>
    (taoSection7PascalPrimeSourceListPMF m).map
      fun pre => taoSection7HoldPointOfPrefix m pre

/--
Source-prefix law before pushing forward to renewal points.  Keeping the miss
count `m` and prefix `pre` together avoids any injectivity assumption about
`taoSection7HoldPointOfPrefix`.
-/
noncomputable def taoSection7HoldSourcePrefixPMF : PMF (ℕ × List ℕ) :=
  geom4Nat.bind fun m =>
    (taoSection7PascalPrimeSourceListPMF m).map fun pre => (m, pre)

theorem taoSection7HoldPMF_eq_sourcePrefixPMF_map :
    taoSection7HoldPMF =
      taoSection7HoldSourcePrefixPMF.map
        (fun x => taoSection7HoldPointOfPrefix x.1 x.2) := by
  unfold taoSection7HoldPMF taoSection7HoldSourcePrefixPMF
  rw [PMF.map_bind]
  congr
  funext m
  rw [PMF.map_comp]
  rfl

theorem taoSection7HoldSourcePrefixPMF_apply
    (m : ℕ) (pre : List ℕ) :
    taoSection7HoldSourcePrefixPMF (m, pre) =
      geom4Nat m * taoSection7PascalPrimeSourceListPMF m pre := by
  rw [taoSection7HoldSourcePrefixPMF, PMF.bind_apply]
  rw [tsum_eq_single m]
  · congr 1
    rw [PMF.map_apply]
    rw [tsum_eq_single pre]
    · simp
    · intro pre' hpre'
      have hpair : ¬ (m, pre) = (m, pre') := by
        intro h
        exact hpre' (Prod.ext_iff.mp h).2.symm
      simp [hpair]
  · intro m' hm'
    have hmap_zero :
        ((taoSection7PascalPrimeSourceListPMF m').map fun pre' => (m', pre'))
          (m, pre) = 0 := by
      rw [PMF.map_apply, ENNReal.tsum_eq_zero]
      intro pre'
      have hpair : ¬ (m, pre) = (m', pre') := by
        intro h
        exact hm' (Prod.ext_iff.mp h).1.symm
      simp [hpair]
    rw [hmap_zero, mul_zero]

theorem taoSection7HoldSourcePrefixPMF_apply_toReal
    (m : ℕ) (pre : List ℕ) :
    (taoSection7HoldSourcePrefixPMF (m, pre)).toReal =
      taoSection7Geom4MissMass m *
        (taoSection7PascalPrimeSourceListPMF m pre).toReal := by
  rw [taoSection7HoldSourcePrefixPMF_apply]
  rw [ENNReal.toReal_mul]
  rw [geom4Nat_apply_toReal]
  rfl

/-- The `Hold` law gives zero mass to negative vertical increments. -/
theorem taoSection7HoldPMF_apply_eq_zero_of_l_neg
    {h : TaoSection7RenewalPoint} (hl : h.l < 0) :
    taoSection7HoldPMF h = 0 := by
  rw [taoSection7HoldPMF, PMF.bind_apply, ENNReal.tsum_eq_zero]
  intro m
  have hmap_zero :
      ((taoSection7PascalPrimeSourceListPMF m).map
        fun pre => taoSection7HoldPointOfPrefix m pre) h = 0 := by
    rw [PMF.map_apply, ENNReal.tsum_eq_zero]
    intro pre
    have hnot : h ≠ taoSection7HoldPointOfPrefix m pre := by
      intro heq
      have hnonneg : (0 : ℤ) ≤ (taoSection7HoldPointOfPrefix m pre).l := by
        rw [taoSection7HoldPointOfPrefix_l]
        exact Int.natCast_nonneg _
      rw [← heq] at hnonneg
      exact (not_lt_of_ge hnonneg) hl
    simp [hnot]
  simp [hmap_zero]

/-- Real-valued zero-mass form of `taoSection7HoldPMF_apply_eq_zero_of_l_neg`. -/
theorem taoSection7HoldPMF_toReal_eq_zero_of_l_neg
    {h : TaoSection7RenewalPoint} (hl : h.l < 0) :
    (taoSection7HoldPMF h).toReal = 0 := by
  rw [taoSection7HoldPMF_apply_eq_zero_of_l_neg hl]
  rfl

/-- Statement surface for the first-coordinate law of `Hold`. -/
def taoSection7HoldPMF_map_j_eq_geom4PNat : Prop :=
  taoSection7HoldPMF.map (fun p => p.j) = geom4PNat

/-- Checked first-coordinate law of the Section 7 `Hold` PMF. -/
theorem taoSection7HoldPMF_map_j_eq_geom4PNat_checked :
    taoSection7HoldPMF_map_j_eq_geom4PNat := by
  unfold taoSection7HoldPMF_map_j_eq_geom4PNat taoSection7HoldPMF geom4PNat
  rw [PMF.map_bind]
  congr
  funext m
  rw [PMF.map_comp]
  convert PMF.map_const (taoSection7PascalPrimeSourceListPMF m)
    (⟨m + 1, Nat.succ_pos m⟩ : ℕ+) using 1

/-- Alias using the source note's shorter wording for the first-index law. -/
def taoSection7Hold_firstIndex_law_eq_geom4PNat : Prop :=
  taoSection7HoldPMF_map_j_eq_geom4PNat

/-- Checked alias for the source-facing first-index law. -/
theorem taoSection7Hold_firstIndex_law_eq_geom4PNat_checked :
    taoSection7Hold_firstIndex_law_eq_geom4PNat :=
  taoSection7HoldPMF_map_j_eq_geom4PNat_checked

/-- Fiber-sum real mass surface for point probabilities of the `Hold` PMF. -/
noncomputable def taoSection7HoldPMF_pointMass_fiber_sum
    (p : TaoSection7RenewalPoint) : ℝ :=
  ∑' pre : List ℕ,
    if taoSection7HoldPointOfPrefix pre.length pre = p then
      taoSection7Geom4MissMass pre.length *
        taoSection7PascalPrimeSourcePathMass pre
    else
      0

/-- Statement surface connecting `Hold` point masses to the prefix fiber sum. -/
def taoSection7HoldPMF_apply_toReal_eq_fiber_sum
    (p : TaoSection7RenewalPoint) : Prop :=
  (taoSection7HoldPMF p).toReal =
    taoSection7HoldPMF_pointMass_fiber_sum p

/-- Base-atom statement surface for `Hold`; this is not the full recursive law of Lemma 7.6. -/
def taoSection7HoldPMF_base_atom_toReal : Prop :=
  (taoSection7HoldPMF
      ({ j := (1 : ℕ+), l := (3 : ℤ) } : TaoSection7RenewalPoint)).toReal =
    (1 / 4 : ℝ)

/-- Checked base atom of the Section 7 `Hold` PMF. -/
theorem taoSection7HoldPMF_base_atom_toReal_checked :
    taoSection7HoldPMF_base_atom_toReal := by
  unfold taoSection7HoldPMF_base_atom_toReal taoSection7HoldPMF
  rw [PMF.bind_apply]
  rw [tsum_eq_single 0]
  · have hmap_one :
        (PMF.map (fun pre => taoSection7HoldPointOfPrefix 0 pre)
          (taoSection7PascalPrimeSourceListPMF 0))
          ({ j := (1 : ℕ+), l := (3 : ℤ) } : TaoSection7RenewalPoint) = 1 := by
      rw [PMF.map_apply]
      rw [tsum_eq_single []]
      · simp [taoSection7PascalPrimeSourceListPMF,
          taoSection7HoldPointOfPrefix_zero_nil]
      · intro pre hpre
        cases pre with
        | nil => exact (hpre rfl).elim
        | cons b bs => simp [taoSection7PascalPrimeSourceListPMF]
    rw [hmap_one, mul_one, geom4Nat_apply_toReal]
    norm_num
  · intro m hm
    have hmap_zero :
        (PMF.map (fun pre => taoSection7HoldPointOfPrefix m pre)
          (taoSection7PascalPrimeSourceListPMF m))
          ({ j := (1 : ℕ+), l := (3 : ℤ) } : TaoSection7RenewalPoint) = 0 := by
      rw [PMF.map_apply, ENNReal.tsum_eq_zero]
      intro pre
      have hnot :
          ¬ ({ j := (1 : ℕ+), l := (3 : ℤ) } : TaoSection7RenewalPoint) =
            taoSection7HoldPointOfPrefix m pre := by
        intro h
        have hj := congrArg TaoSection7RenewalPoint.j h
        have hnat : (1 : ℕ) = m + 1 := congrArg Subtype.val hj
        omega
      simp [hnot]
    rw [hmap_zero, mul_zero]

end Tao
end Erdos1135SecondScale
