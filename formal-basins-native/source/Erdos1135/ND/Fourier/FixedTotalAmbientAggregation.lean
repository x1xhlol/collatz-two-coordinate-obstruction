import Erdos1135.ND.Fourier.FixedTotalAmbientPolynomial
import Erdos1135.Tao.Fourier.OscillationAlgebra
import Erdos1135.Tao.Section6.GatePartition
import Erdos1135.Tao.Section6.HighRegimeMixing

/-!
# Raw Fixed-Total Ambient Aggregation

This leaf transports the additive raw-slice estimate to one fixed ambient
group, intersects Tao's enlarged local union with a fixed full valuation
total, and sums the resulting disjoint source slices.  The exact local box
costs two powers of the ambient level.

The output is still an unnormalized defective submass.  It neither replaces
the full fixed-total vector nor charges an exceptional event or divides by an
endpoint mass.
-/

open scoped BigOperators

namespace Erdos1135
namespace ND

open Tao

noncomputable section

/-- The additive raw fixed-total slice rate transported to one fixed ambient
group.  Terminal tail length zero is included. -/
theorem exists_ndSection6FixedTotalAmbientOscillation_le_fixed_n
    (CA : ℝ) (hCA : 17 ≤ CA) (Q : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ N0 : ℕ, ∀ n k l L m : ℕ,
      N0 ≤ n →
      k + 1 ≤ n →
      m ≤ n →
      9 * n ≤ 10 * m →
      Tao.taoZModPowOscillation m n
          (ndSection6FixedTotalAmbientSubmass CA n k l L) ≤
        D / (n : ℝ) ^ (Q + 3) := by
  obtain ⟨D, hD, N0, hslice⟩ :=
    exists_ndSection6FixedTotalAmbientOscillation_le CA hCA Q
  refine ⟨D, hD, N0, ?_⟩
  intro n k l L m hn hk hmn hhigh
  let T := n - (k + 1)
  have hambient : T + (k + 1) = n := by
    dsimp [T]
    exact Nat.sub_add_cancel hk
  have hbound := hslice T k l L m
    (by simpa only [hambient] using hn)
    (by simpa only [hambient] using hmn)
    (by simpa only [hambient] using hhigh)
  rw [hambient] at hbound
  exact hbound

/-- Tao's enlarged local source gate intersected with one full valuation
total.  The total selector is inside the source gate and is not normalized. -/
noncomputable def ndSection6FixedTotalLocalUnionGate
    (CA : ℝ) (n L : ℕ) (full : List ℕ+) : Prop :=
  Tao.taoSection6LocalUnionGate CA n full ∧
    Tao.taoTupleWeight full = L

/-- Raw accepted residue mass of the fixed-total enlarged local union. -/
noncomputable def ndSection6FixedTotalLocalUnionSubmass
    (CA : ℝ) (n L : ℕ) (y : ZMod (3 ^ n)) : ℝ :=
  Tao.taoGatedSubmass
    (Tao.geom2PNatListPMF n)
    (ndSection6FixedTotalLocalUnionGate CA n L)
    (Tao.taoSection7OffsetZMod n) y

/-- The common total selector distributes through the exact disjoint local
gate partition.  This identity is valid also for the empty box at `n = 0`. -/
theorem ndSection6FixedTotalLocalUnionSubmass_eq_sum_sum
    (CA : ℝ) (n L : ℕ) (y : ZMod (3 ^ n)) :
    ndSection6FixedTotalLocalUnionSubmass CA n L y =
      ∑ k : Fin n, ∑ l : Fin (2 * n),
        ndSection6FixedTotalAmbientSubmass CA n k l L y := by
  classical
  have hunion :
      ndSection6FixedTotalLocalUnionGate CA n L =
        fun full => ∃ i ∈
            (Finset.univ : Finset (Tao.taoSection6LocalGateIndex n)),
          Tao.taoSection6LocalGate CA n i full ∧
            Tao.taoTupleWeight full = L := by
    funext full
    apply propext
    change
      ((∃ i : Tao.taoSection6LocalGateIndex n,
          Tao.taoSection6LocalGate CA n i full) ∧
          Tao.taoTupleWeight full = L) ↔
        ∃ i ∈ (Finset.univ : Finset (Tao.taoSection6LocalGateIndex n)),
          Tao.taoSection6LocalGate CA n i full ∧
            Tao.taoTupleWeight full = L
    constructor
    · rintro ⟨⟨i, hi⟩, hweight⟩
      exact ⟨i, Finset.mem_univ i, hi, hweight⟩
    · rintro ⟨i, _hi, hgate, hweight⟩
      exact ⟨⟨i, hgate⟩, hweight⟩
  unfold ndSection6FixedTotalLocalUnionSubmass
  rw [hunion]
  calc
    Tao.taoGatedSubmass
        (Tao.geom2PNatListPMF n)
        (fun full => ∃ i ∈
            (Finset.univ : Finset (Tao.taoSection6LocalGateIndex n)),
          Tao.taoSection6LocalGate CA n i full ∧
            Tao.taoTupleWeight full = L)
        (Tao.taoSection7OffsetZMod n) y =
      ∑ i ∈ (Finset.univ : Finset (Tao.taoSection6LocalGateIndex n)),
        Tao.taoGatedSubmass (Tao.geom2PNatListPMF n)
          (fun full => Tao.taoSection6LocalGate CA n i full ∧
            Tao.taoTupleWeight full = L)
          (Tao.taoSection7OffsetZMod n) y := by
      apply Tao.taoGatedSubmass_finset_union_eq_sum
      intro i _hi j _hj hij full hifull hjfull
      exact (Tao.taoSection6LocalGate_disjoint hij full)
        ⟨hifull.1, hjfull.1⟩
    _ = ∑ i : Tao.taoSection6LocalGateIndex n,
        ndSection6FixedTotalAmbientSubmass CA n i.1 i.2 L y := by
      apply Finset.sum_congr rfl
      intro i _hi
      rfl
    _ = ∑ k : Fin n, ∑ l : Fin (2 * n),
        ndSection6FixedTotalAmbientSubmass CA n k l L y :=
      Fintype.sum_prod_type _

/-- The raw fixed-total enlarged local union has the exact two-parameter-box
polynomial rate.  The full box spends precisely two powers of `n`. -/
theorem exists_ndSection6FixedTotalLocalUnionOscillation_le
    (CA : ℝ) (hCA : 17 ≤ CA) (Q : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∃ N0 : ℕ, 1 ≤ N0 ∧
      ∀ n L m : ℕ,
        N0 ≤ n →
        m ≤ n →
        9 * n ≤ 10 * m →
        Tao.taoZModPowOscillation m n
            (ndSection6FixedTotalLocalUnionSubmass CA n L) ≤
          (2 * D) / (n : ℝ) ^ (Q + 1) := by
  obtain ⟨D, hD, Nslice, hslice⟩ :=
    exists_ndSection6FixedTotalAmbientOscillation_le_fixed_n CA hCA Q
  refine ⟨D, hD, max Nslice 1, le_max_right _ _, ?_⟩
  intro n L m hn hmn hhigh
  have hnSlice : Nslice ≤ n := (le_max_left _ _).trans hn
  have hnOne : 1 ≤ n := (le_max_right _ _).trans hn
  let B : ℝ := D / (n : ℝ) ^ (Q + 3)
  calc
    Tao.taoZModPowOscillation m n
        (ndSection6FixedTotalLocalUnionSubmass CA n L) =
      Tao.taoZModPowOscillation m n
        (fun y => ∑ k : Fin n, ∑ l : Fin (2 * n),
          ndSection6FixedTotalAmbientSubmass CA n k l L y) := by
      congr 1
      funext y
      exact ndSection6FixedTotalLocalUnionSubmass_eq_sum_sum CA n L y
    _ ≤ ∑ k : Fin n,
        Tao.taoZModPowOscillation m n
          (fun y => ∑ l : Fin (2 * n),
            ndSection6FixedTotalAmbientSubmass CA n k l L y) :=
      Tao.taoZModPowOscillation_sum_le_sum m n
        (fun k : Fin n => fun y => ∑ l : Fin (2 * n),
          ndSection6FixedTotalAmbientSubmass CA n k l L y)
    _ ≤ ∑ k : Fin n, ∑ l : Fin (2 * n),
        Tao.taoZModPowOscillation m n
          (ndSection6FixedTotalAmbientSubmass CA n k l L) := by
      apply Finset.sum_le_sum
      intro k _hk
      exact Tao.taoZModPowOscillation_sum_le_sum m n
        (fun l : Fin (2 * n) =>
          ndSection6FixedTotalAmbientSubmass CA n k l L)
    _ ≤ ∑ _k : Fin n, ∑ _l : Fin (2 * n), B := by
      apply Finset.sum_le_sum
      intro k _hk
      apply Finset.sum_le_sum
      intro l _hl
      exact hslice n k l L m hnSlice
        (Nat.succ_le_of_lt k.isLt) hmn hhigh
    _ = (((n * (2 * n) : ℕ) : ℝ) * B) := by
      simp [Nat.cast_mul]
      ring
    _ = (2 * D) / (n : ℝ) ^ (Q + 1) := by
      exact Tao.taoSection6_box_mul_div_pow_eq Q n D hnOne

end

end ND
end Erdos1135
