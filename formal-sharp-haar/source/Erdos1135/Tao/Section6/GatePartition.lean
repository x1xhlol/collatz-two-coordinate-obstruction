import Erdos1135.Tao.Probability.GatedSubmassPartition
import Erdos1135.Tao.Section6.FirstCrossingPartition
import Erdos1135.Tao.Section6.FixedAmbientSlice

/-!
# Section 6 Finite Local-Gate Partition

This leaf forms the enlarged local event `G` over `k<n`, `l<2n`, proves its
gates pairwise disjoint, includes the repaired global event in `G` eventually,
and identifies its accepted source vector with the exact finite sum of the
fixed-ambient slices.  It does not identify `G` with the global event.
-/

open scoped BigOperators

namespace Erdos1135
namespace Tao

noncomputable section

/-- Finite Section 6 slice box. -/
abbrev taoSection6LocalGateIndex (n : ℕ) := Fin n × Fin (2 * n)

/-- One local exact-length gate indexed inside the finite box. -/
noncomputable def taoSection6LocalGate
    (CA : ℝ) (n : ℕ) (i : taoSection6LocalGateIndex n)
    (full : List ℕ+) : Prop :=
  taoSection6FixedAmbientGate CA n i.1 i.2 full

/-- Enlarged local union `G`; its head typicality deliberately ignores the
tail after the first crossing. -/
noncomputable def taoSection6LocalUnionGate
    (CA : ℝ) (n : ℕ) (full : List ℕ+) : Prop :=
  ∃ i : taoSection6LocalGateIndex n, taoSection6LocalGate CA n i full

/-- Accepted source vector of the enlarged local union. -/
noncomputable def taoSection6LocalUnionSubmass
    (CA : ℝ) (n : ℕ) (y : ZMod (3 ^ n)) : ℝ :=
  taoGatedSubmass
    (geom2PNatListPMF n)
    (taoSection6LocalUnionGate CA n)
    (taoSection7OffsetZMod n)
    y

/-- A fixed-ambient local gate induces the corresponding crossing on the full
source list. -/
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

/-- Local gates on the same full source determine the same finite-box index. -/
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

/-- Distinct finite-box indices give disjoint source gates. -/
theorem taoSection6LocalGate_disjoint
    {CA : ℝ} {n : ℕ} {i j : taoSection6LocalGateIndex n}
    (hij : i ≠ j) (full : List ℕ+) :
    ¬ (taoSection6LocalGate CA n i full ∧
      taoSection6LocalGate CA n j full) := by
  rintro ⟨hi, hj⟩
  exact hij (taoSection6LocalGate_index_eq hi hj)

/-- The repaired global event is eventually contained in the enlarged local
union.  No converse is asserted. -/
theorem exists_taoSection6GlobalTypical_subset_localUnionGate
    (CA : ℝ) (hCA : 17 ≤ CA) :
    ∃ N0 : ℕ, ∀ n : ℕ, N0 ≤ n →
      ∀ full : List ℕ+, taoSection6GlobalTypical CA n full →
        taoSection6LocalUnionGate CA n full := by
  obtain ⟨N0, hpair⟩ :=
    exists_taoSection6GlobalTypical_unique_bounded_headGate CA hCA
  refine ⟨N0, ?_⟩
  intro n hn full hglobal
  obtain ⟨⟨k, l⟩, hkl, _hunique⟩ := hpair n hn full hglobal
  let i : taoSection6LocalGateIndex n :=
    (⟨k, hkl.1⟩, ⟨l, hkl.2.1⟩)
  refine ⟨i, ?_⟩
  exact ⟨taoSection6GlobalTypical_length hglobal, hkl.2.2⟩

/-- The direct fixed-ambient vector is the generic gated submass for its local
source predicate. -/
theorem taoSection6FixedAmbientSubmass_eq_gatedSubmass
    (CA : ℝ) (n k l : ℕ) (y : ZMod (3 ^ n)) :
    taoSection6FixedAmbientSubmass CA n k l y =
      taoGatedSubmass
        (geom2PNatListPMF n)
        (taoSection6FixedAmbientGate CA n k l)
        (taoSection7OffsetZMod n) y :=
  rfl

/-- Exact pointwise local-union vector identity over the product index type. -/
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

/-- Nested source-shaped form of the exact pointwise slice sum. -/
theorem taoSection6LocalUnionSubmass_eq_sum_sum
    (CA : ℝ) (n : ℕ) (y : ZMod (3 ^ n)) :
    taoSection6LocalUnionSubmass CA n y =
      ∑ k : Fin n, ∑ l : Fin (2 * n),
        taoSection6FixedAmbientSubmass CA n k l y := by
  rw [taoSection6LocalUnionSubmass_eq_sum]
  exact Fintype.sum_prod_type _

/-- Empty-box canary at `n=0`. -/
theorem taoSection6LocalUnionSubmass_zero
    (CA : ℝ) (y : ZMod (3 ^ 0)) :
    taoSection6LocalUnionSubmass CA 0 y = 0 := by
  rw [taoSection6LocalUnionSubmass_eq_sum]
  simp

end

end Tao
end Erdos1135
