/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Probability.GatedSubmassPartition
import Erdos1135Predecessor.Tao.Section6.FirstCrossingPartition
import Erdos1135Predecessor.Tao.Section6.FixedAmbientSlice

open scoped BigOperators

namespace Erdos1135Predecessor

namespace Tao

noncomputable section

abbrev taoSection6LocalGateIndex (n : ℕ) := Fin n × Fin (2 * n)

noncomputable def taoSection6LocalGate
    (CA : ℝ) (n : ℕ) (i : taoSection6LocalGateIndex n)
    (full : List ℕ+) : Prop :=
  taoSection6FixedAmbientGate CA n i.1 i.2 full

noncomputable def taoSection6LocalUnionGate
    (CA : ℝ) (n : ℕ) (full : List ℕ+) : Prop :=
  ∃ i : taoSection6LocalGateIndex n, taoSection6LocalGate CA n i full

noncomputable def taoSection6LocalUnionSubmass
    (CA : ℝ) (n : ℕ) (y : ZMod (3 ^ n)) : ℝ :=
  taoGatedSubmass
    (geom2PNatListPMF n)
    (taoSection6LocalUnionGate CA n)
    (taoSection7OffsetZMod n)
    y

theorem taoSection6FixedAmbientGate_prefixCrossing
    {CA : ℝ} {n k l : ℕ} {full : List ℕ+}
    (hgate : taoSection6FixedAmbientGate CA n k l full) :
    taoSection6PrefixCrossing (taoCor63StarQ CA n) full k := by
  have hlength : full.length = n := hgate.1
  have hhead := hgate.2
  have hheadLength := taoSection6HeadGate_length hhead
  have hk : k < full.length := by
    rw [List.length_take] at hheadLength
    omega
  have hcross := taoSection6HeadGate_crossing hhead
  refine ⟨hk, ?_, ?_⟩
  · simpa [List.take_take, Nat.min_eq_left (Nat.le_succ k)] using hcross.1
  · exact hcross.2

theorem taoSection6LocalGate_index_eq
    {CA : ℝ} {n : ℕ} {i j : taoSection6LocalGateIndex n}
    {full : List ℕ+}
    (hi : taoSection6LocalGate CA n i full)
    (hj : taoSection6LocalGate CA n j full) :
    i = j := by
  have hki := taoSection6FixedAmbientGate_prefixCrossing hi
  have hkj := taoSection6FixedAmbientGate_prefixCrossing hj
  have hk : (i.1 : ℕ) = (j.1 : ℕ) := taoSection6PrefixCrossing.eq hki hkj
  have hwi := taoSection6HeadGate_weight hi.2
  have hwj := taoSection6HeadGate_weight hj.2
  have hl : (i.2 : ℕ) = (j.2 : ℕ) := by
    rw [← hwi, ← hwj, hk]
  exact Prod.ext (Fin.ext hk) (Fin.ext hl)

theorem taoSection6LocalGate_disjoint
    {CA : ℝ} {n : ℕ} {i j : taoSection6LocalGateIndex n}
    (hij : i ≠ j) (full : List ℕ+) :
    ¬ (taoSection6LocalGate CA n i full ∧
      taoSection6LocalGate CA n j full) := by
  rintro ⟨hi, hj⟩
  exact hij (taoSection6LocalGate_index_eq hi hj)

theorem taoSection6FixedAmbientSubmass_eq_gatedSubmass
    (CA : ℝ) (n k l : ℕ) (y : ZMod (3 ^ n)) :
    taoSection6FixedAmbientSubmass CA n k l y =
      taoGatedSubmass
        (geom2PNatListPMF n)
        (taoSection6FixedAmbientGate CA n k l)
        (taoSection7OffsetZMod n) y :=
  rfl

theorem taoSection6LocalUnionSubmass_eq_sum
    (CA : ℝ) (n : ℕ) (y : ZMod (3 ^ n)) :
    taoSection6LocalUnionSubmass CA n y =
      ∑ i : taoSection6LocalGateIndex n,
        taoSection6FixedAmbientSubmass CA n i.1 i.2 y := by
  have hunion :
      taoSection6LocalUnionGate CA n =
        fun full => ∃ i ∈ (Finset.univ : Finset (taoSection6LocalGateIndex n)),
          taoSection6LocalGate CA n i full := by
    funext full
    apply propext
    simp [taoSection6LocalUnionGate]
  unfold taoSection6LocalUnionSubmass
  rw [hunion]
  calc
    taoGatedSubmass
        (geom2PNatListPMF n)
        (fun full => ∃ i ∈ (Finset.univ : Finset (taoSection6LocalGateIndex n)),
          taoSection6LocalGate CA n i full)
        (taoSection7OffsetZMod n) y =
      ∑ i ∈ (Finset.univ : Finset (taoSection6LocalGateIndex n)),
        taoGatedSubmass (geom2PNatListPMF n)
          (taoSection6LocalGate CA n i) (taoSection7OffsetZMod n) y := by
      apply taoGatedSubmass_finset_union_eq_sum
      intro i hi j hj hij full hifull hjfull
      exact (taoSection6LocalGate_disjoint hij full) ⟨hifull, hjfull⟩
    _ = ∑ i : taoSection6LocalGateIndex n,
        taoSection6FixedAmbientSubmass CA n i.1 i.2 y := by
      apply Finset.sum_congr rfl
      intro i hi
      exact (taoSection6FixedAmbientSubmass_eq_gatedSubmass
        CA n i.1 i.2 y).symm

end

end Tao

end Erdos1135Predecessor
