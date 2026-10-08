/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Probability.PascalPrimeList
import Erdos1135Predecessor.Tao.Renewal.HoldPoint

namespace Erdos1135Predecessor

namespace Tao

def taoSection7HoldTerminalSum (pre : List ℕ) : ℕ :=
  pre.sum + 3

def taoSection7HoldPointOfPrefix (m : ℕ) (pre : List ℕ) :
    TaoSection7RenewalPoint :=
  { j := ⟨m + 1, Nat.succ_pos m⟩
    l := Int.ofNat (taoSection7HoldTerminalSum pre) }

@[simp] theorem taoSection7HoldPointOfPrefix_l (m : ℕ) (pre : List ℕ) :
    (taoSection7HoldPointOfPrefix m pre).l =
      Int.ofNat (taoSection7HoldTerminalSum pre) :=
  rfl

noncomputable def taoSection7HoldPMF : PMF TaoSection7RenewalPoint :=
  geom4Nat.bind fun m =>
    (taoSection7PascalPrimeSourceListPMF m).map
      fun pre => taoSection7HoldPointOfPrefix m pre

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

def taoSection7HoldPMF_map_j_eq_geom4PNat : Prop :=
  taoSection7HoldPMF.map (fun p => p.j) = geom4PNat

theorem taoSection7HoldPMF_map_j_eq_geom4PNat_checked :
    taoSection7HoldPMF_map_j_eq_geom4PNat := by
  unfold taoSection7HoldPMF_map_j_eq_geom4PNat taoSection7HoldPMF geom4PNat
  rw [PMF.map_bind]
  congr
  funext m
  rw [PMF.map_comp]
  convert PMF.map_const (taoSection7PascalPrimeSourceListPMF m)
    (⟨m + 1, Nat.succ_pos m⟩ : ℕ+) using 1

end Tao

end Erdos1135Predecessor
