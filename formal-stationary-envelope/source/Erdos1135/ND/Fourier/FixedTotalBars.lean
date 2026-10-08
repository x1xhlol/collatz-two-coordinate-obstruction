/-
Compatibility modification, 8 October 2026: proof elaboration and unused bound-variable names only.
See provenance/envelope-linter-patches.json for exact source hashes and patches.
-/
import Erdos1135.ND.Fourier.FiberConditioning
import Mathlib.Combinatorics.Enumerative.Composition
import Mathlib.Data.Fintype.Fin
import Mathlib.Data.Set.PowersetCard

/-!
# Fixed-Total Valuations as Uniform Bars

This leaf identifies the finite fixed-total valuation carrier with the
classical bars representation of a positive composition.  Mathlib stores an
interior physical boundary `sigma` as `sigma - 1 : Fin (L - 1)`; the shift is
kept visible for the later prefix/order-statistic interface.

The positive-length and feasibility hypotheses on the equivalence are
essential.  For example, when `n = 0 < L`, the fixed-total valuation fiber is
empty while the `0`-bar carrier contains the empty finset.
-/

namespace Erdos1135
namespace ND

open Tao

/-- Positive compositions of `L` having exactly `n` blocks. -/
abbrev NDFixedLengthComposition (n L : ℕ) :=
  {c : Composition L // c.length = n}

/-- The `n - 1` zero-based interior bars of a positive `n`-part composition
of `L`.  A stored value `b` represents the physical boundary `b + 1`. -/
abbrev NDFixedTotalBars (n L : ℕ) :=
  Set.powersetCard (Fin (L - 1)) (n - 1)

private theorem nd_taoTupleWeight_eq_map_sum (as : List ℕ+) :
    Tao.taoTupleWeight as =
      (as.map fun a : ℕ+ => (a : ℕ)).sum := by
  unfold Tao.taoTupleWeight
  rw [List.bind_eq_flatMap]
  rw [show List.map (fun a : ℕ => a)
        (List.flatMap (fun a : ℕ+ => pure (a : ℕ)) as) =
      List.flatMap (fun a : ℕ+ => pure (a : ℕ)) as by
    exact List.map_id _]
  rw [show List.flatMap (fun a : ℕ+ => pure (a : ℕ)) as =
      List.map (fun a : ℕ+ => (a : ℕ)) as by
    simpa [Function.comp_def] using
      List.flatMap_pure_eq_map (fun a : ℕ+ => (a : ℕ)) as]

/-- Ordered positive valuation lists are exactly fixed-length Mathlib
compositions. -/
noncomputable def ndFixedTotalValuationsEquivComposition (n L : ℕ) :
    NDFixedTotalValuations n L ≃ NDFixedLengthComposition n L where
  toFun as := ⟨{
    blocks := as.1.map fun a : ℕ+ => (a : ℕ)
    blocks_pos := by
      intro i hi
      rcases List.mem_map.1 hi with ⟨a, _ha, rfl⟩
      exact a.2
    blocks_sum := by
      rw [← nd_taoTupleWeight_eq_map_sum]
      exact as.2.2
    }, by
      change (as.1.map fun a : ℕ+ => (a : ℕ)).length = n
      simpa using as.2.1⟩
  invFun c :=
    let as : List ℕ+ := c.1.blocks.pmap
      (fun a ha => ⟨a, ha⟩) (fun a ha => c.1.blocks_pos ha)
    ⟨as, by
      constructor
      · simpa [as] using c.2
      · rw [nd_taoTupleWeight_eq_map_sum]
        simp only [as]
        rw [List.map_pmap]
        change (List.pmap (fun a (_ : 0 < a) => a)
          c.1.blocks _).sum = L
        rw [List.pmap_eq_map]
        simp⟩
  left_inv as := by
    apply Subtype.ext
    simp only
    rw [List.pmap_map]
    calc
      List.pmap
          (fun (a : ℕ+) h => (⟨(a : ℕ), h⟩ : ℕ+)) as.1 _ =
          List.pmap (fun (a : ℕ+) (_ : 0 < (a : ℕ)) => a) as.1
            (fun a _ha => a.2) := by
        apply List.pmap_congr_left
        intro a _ha _h₁ _h₂
        exact Subtype.ext rfl
      _ = as.1.map id := List.pmap_eq_map _
      _ = as.1 := by simp
  right_inv c := by
    apply Subtype.ext
    apply Composition.ext
    simp only
    rw [List.map_pmap]
    change List.pmap (fun a (_ : 0 < a) => a)
      c.1.blocks _ = c.1.blocks
    rw [List.pmap_eq_map]
    simp

/-- Mathlib's composition equivalence, presented as its zero-based interior
bar finset. -/
def ndCompositionBarsEquiv (L : ℕ) :
    Composition L ≃ Finset (Fin (L - 1)) :=
  (compositionEquiv L).trans (compositionAsSetEquiv L)

/-- A positive composition has one fewer interior bar than blocks. -/
theorem card_ndCompositionBars {L : ℕ} (hL : 0 < L)
    (c : Composition L) :
    (ndCompositionBarsEquiv L c).card = c.length - 1 := by
  let s := ndCompositionBarsEquiv L c
  let shift : Fin (L - 1) ↪ Fin (L + 1) :=
    ⟨fun i => ⟨1 + i.1, by omega⟩,
      fun i k h => Fin.ext (by
        have hv := congrArg Fin.val h
        change 1 + i.1 = 1 + k.1 at hv
        omega)⟩
  have hmap :
      s.map shift = (c.boundaries.erase 0).erase (Fin.last L) := by
    ext x
    simp only [Finset.mem_map, Finset.mem_erase]
    constructor
    · rintro ⟨i, hi, rfl⟩
      refine ⟨?_, ?_, ?_⟩
      · intro h
        have hv := congrArg Fin.val h
        change 1 + i.1 = L at hv
        omega
      · intro h
        have hv := congrArg Fin.val h
        change 1 + i.1 = 0 at hv
        omega
      · simpa [s, ndCompositionBarsEquiv, compositionEquiv,
          compositionAsSetEquiv, shift] using hi
    · rintro ⟨hxLast, hxZero, hxBoundary⟩
      have hx0 : 0 < x.1 := by
        by_contra h
        apply hxZero
        exact Fin.ext (Nat.eq_zero_of_not_pos h)
      have hxle : x.1 ≤ L := Nat.le_of_lt_succ x.2
      have hxL : x.1 < L := by
        by_contra h
        apply hxLast
        apply Fin.ext
        simpa using (Nat.le_antisymm hxle (Nat.le_of_not_gt h))
      let i : Fin (L - 1) := ⟨x.1 - 1, by omega⟩
      have hix : shift i = x := by
        apply Fin.ext
        simp [i, shift]
        omega
      refine ⟨i, ?_, hix⟩
      have hshiftBoundary : shift i ∈ c.boundaries := by
        rw [hix]
        exact hxBoundary
      simpa [s, ndCompositionBarsEquiv, compositionEquiv,
        compositionAsSetEquiv, i, shift] using hshiftBoundary
  have hzero : (0 : Fin (L + 1)) ∈ c.boundaries := by
    rw [Composition.boundaries]
    exact Finset.mem_map.2
      ⟨0, Finset.mem_univ _, c.boundary_zero⟩
  have hlast : Fin.last L ∈ c.boundaries := by
    rw [Composition.boundaries]
    exact Finset.mem_map.2
      ⟨Fin.last c.length, Finset.mem_univ _, c.boundary_last⟩
  have hlast_ne_zero : (Fin.last L : Fin (L + 1)) ≠ 0 := by
    intro h
    have hv := congrArg Fin.val h
    simp at hv
    omega
  have hlastErase : Fin.last L ∈ c.boundaries.erase 0 :=
    Finset.mem_erase.mpr ⟨hlast_ne_zero, hlast⟩
  have h1 := Finset.card_erase_add_one hlastErase
  have h2 := Finset.card_erase_add_one hzero
  have hmapCard : (s.map shift).card = s.card := Finset.card_map ..
  rw [hmap] at hmapCard
  have hbound := c.card_boundaries_eq_succ_length
  have hlenPos := c.length_pos_of_pos hL
  change s.card = c.length - 1
  omega

private theorem ndCompositionBarsEquiv_length_iff
    {n L : ℕ} (hn : 0 < n) (hL : n ≤ L)
    (c : Composition L) :
    c.length = n ↔
      (ndCompositionBarsEquiv L c).card = n - 1 := by
  rw [card_ndCompositionBars (hn.trans_le hL) c]
  have hc : 0 < c.length := c.length_pos_of_pos (hn.trans_le hL)
  omega

/-- Restricting Mathlib's bar equivalence by the number of blocks gives the
source's fixed-cardinality bar carrier. -/
noncomputable def ndFixedLengthCompositionEquivBars
    {n L : ℕ} (hn : 0 < n) (hL : n ≤ L) :
    NDFixedLengthComposition n L ≃ NDFixedTotalBars n L :=
  Equiv.subtypeEquiv (ndCompositionBarsEquiv L)
    (fun c => ndCompositionBarsEquiv_length_iff hn hL c)

/-- Fixed-total valuation lists are exactly fixed-cardinality bar sets. -/
noncomputable def ndFixedTotalValuationsEquivBars
    {n L : ℕ} (hn : 0 < n) (hL : n ≤ L) :
    NDFixedTotalValuations n L ≃ NDFixedTotalBars n L :=
  (ndFixedTotalValuationsEquivComposition n L).trans
    (ndFixedLengthCompositionEquivBars hn hL)

/-- The already checked weak-extras carrier, relabeled as bars. -/
noncomputable def ndFiberExtrasEquivBars
    (n L : ℕ) (hn : 0 < n) (hL : n ≤ L) :
    Sym (Fin n) (L - n) ≃ NDFixedTotalBars n L :=
  (ndFiberExtrasEquivFixedTotal n L hL).trans
    (ndFixedTotalValuationsEquivBars hn hL)

/-- The `i`th stored bar in increasing order. -/
noncomputable def ndFixedTotalBarAt
    {n L : ℕ} (B : NDFixedTotalBars n L)
    (i : Fin (n - 1)) : Fin (L - 1) :=
  B.1.orderEmbOfFin B.2 i

private noncomputable def ndCompositionBarOrderEmbedding
    {L : ℕ} (hL : 0 < L) (c : Composition L) :
    Fin (c.length - 1) ↪o Fin (L - 1) :=
  OrderEmbedding.ofStrictMono
    (fun i => ⟨c.sizeUpTo (i.1 + 1) - 1, by
      let k : Fin (c.length + 1) := ⟨i.1 + 1, by omega⟩
      have hk0 : (0 : Fin (c.length + 1)) < k := by
        apply Fin.mk_lt_mk.2
        change 0 < i.1 + 1
        omega
      have hkLast : k < Fin.last c.length := by
        apply Fin.mk_lt_mk.2
        change i.1 + 1 < c.length
        omega
      have hpos := c.boundary.strictMono hk0
      have hlt := c.boundary.strictMono hkLast
      rw [c.boundary_zero] at hpos
      rw [c.boundary_last] at hlt
      change 0 < c.sizeUpTo (i.1 + 1) at hpos
      change c.sizeUpTo (i.1 + 1) < L at hlt
      omega⟩)
    (by
      intro i j hij
      apply Fin.mk_lt_mk.2
      let ki : Fin (c.length + 1) := ⟨i.1 + 1, by omega⟩
      let kj : Fin (c.length + 1) := ⟨j.1 + 1, by omega⟩
      have hkij : ki < kj := by
        apply Fin.mk_lt_mk.2
        change i.1 + 1 < j.1 + 1
        omega
      have hlt := c.boundary.strictMono hkij
      change c.sizeUpTo (i.1 + 1) <
        c.sizeUpTo (j.1 + 1) at hlt
      have hposi : 0 < c.sizeUpTo (i.1 + 1) := by
        have hk0 : (0 : Fin (c.length + 1)) < ki := by
          apply Fin.mk_lt_mk.2
          change 0 < i.1 + 1
          omega
        have h := c.boundary.strictMono hk0
        rw [c.boundary_zero] at h
        exact h
      omega)

private theorem ndCompositionBarOrderEmbedding_mem
    {L : ℕ} (hL : 0 < L) (c : Composition L)
    (i : Fin (c.length - 1)) :
    ndCompositionBarOrderEmbedding hL c i ∈
      ndCompositionBarsEquiv L c := by
  simp only [ndCompositionBarOrderEmbedding]
  have hpos : 0 < c.sizeUpTo (i.1 + 1) := by
    let k : Fin (c.length + 1) := ⟨i.1 + 1, by omega⟩
    have hk0 : (0 : Fin (c.length + 1)) < k := by
      apply Fin.mk_lt_mk.2
      change 0 < i.1 + 1
      omega
    have h := c.boundary.strictMono hk0
    rw [c.boundary_zero] at h
    exact h
  have hprefixLt : c.sizeUpTo (i.1 + 1) < L := by
    let k : Fin (c.length + 1) := ⟨i.1 + 1, by omega⟩
    have hkLast : k < Fin.last c.length := by
      apply Fin.mk_lt_mk.2
      change i.1 + 1 < c.length
      omega
    have h := c.boundary.strictMono hkLast
    rw [c.boundary_last] at h
    exact h
  simp only [ndCompositionBarsEquiv, Equiv.trans_apply]
  change (⟨c.sizeUpTo (i.1 + 1) - 1, by omega⟩ :
      Fin (L - 1)) ∈
    (compositionAsSetEquiv L) c.toCompositionAsSet
  have hb :
      (⟨c.sizeUpTo (i.1 + 1), by omega⟩ : Fin (L + 1)) ∈
        c.boundaries := by
    rw [Composition.boundaries]
    apply Finset.mem_map.2
    let k : Fin (c.length + 1) := ⟨i.1 + 1, by omega⟩
    exact ⟨k, Finset.mem_univ _, by rfl⟩
  have heq : 1 + (c.sizeUpTo (i.1 + 1) - 1) =
      c.sizeUpTo (i.1 + 1) := by
    omega
  simpa [compositionAsSetEquiv, heq] using hb

private theorem ndCompositionBarOrderEmbedding_eq
    {L : ℕ} (hL : 0 < L) (c : Composition L) :
    ndCompositionBarOrderEmbedding hL c =
      (ndCompositionBarsEquiv L c).orderEmbOfFin
        (card_ndCompositionBars hL c) := by
  exact Finset.orderEmbOfFin_unique'
    (card_ndCompositionBars hL c)
    (ndCompositionBarOrderEmbedding_mem hL c)

/-- The prefix sums of the composition bridge are the original tuple
weights, with no reversal. -/
theorem ndFixedTotalValuationsEquivComposition_sizeUpTo
    {n L : ℕ} (a : NDFixedTotalValuations n L) (j : ℕ) :
    ((ndFixedTotalValuationsEquivComposition n L a).1).sizeUpTo j =
      Tao.taoTupleWeight (a.1.take j) := by
  change ((a.1.map fun x : ℕ+ => (x : ℕ)).take j).sum =
    Tao.taoTupleWeight (a.1.take j)
  rw [← List.map_take, ← nd_taoTupleWeight_eq_map_sum]

/-- The Mathlib zero-based bar at index `i` is exactly one less than the
physical prefix total through part `i + 1`. -/
theorem ndFixedTotalBarAt_equiv_add_one
    {n L : ℕ} (hn : 0 < n) (hL : n ≤ L)
    (a : NDFixedTotalValuations n L) (i : Fin (n - 1)) :
    (ndFixedTotalBarAt
        (ndFixedTotalValuationsEquivBars hn hL a) i : ℕ) + 1 =
      Tao.taoTupleWeight (a.1.take (i.1 + 1)) := by
  let c : Composition L :=
    (ndFixedTotalValuationsEquivComposition n L a).1
  have hc : c.length = n :=
    (ndFixedTotalValuationsEquivComposition n L a).2
  let castIndex : Fin (n - 1) ≃o Fin (c.length - 1) :=
    Fin.castOrderIso (congrArg (fun m : ℕ => m - 1) hc.symm)
  let f : Fin (n - 1) ↪o Fin (L - 1) :=
    castIndex.toOrderEmbedding.trans
      (ndCompositionBarOrderEmbedding (hn.trans_le hL) c)
  let B : NDFixedTotalBars n L :=
    ndFixedTotalValuationsEquivBars hn hL a
  have hB : B.1 = ndCompositionBarsEquiv L c := rfl
  have hfmem : ∀ k, f k ∈ B.1 := by
    intro k
    rw [hB]
    exact ndCompositionBarOrderEmbedding_mem
      (hn.trans_le hL) c (castIndex k)
  have hf : f = B.1.orderEmbOfFin B.2 :=
    Finset.orderEmbOfFin_unique' B.2 hfmem
  have hbar : ndFixedTotalBarAt B i = f i := by
    rw [ndFixedTotalBarAt, ← hf]
  rw [show ndFixedTotalValuationsEquivBars hn hL a = B from rfl,
    hbar]
  change (c.sizeUpTo (i.1 + 1) - 1) + 1 =
    Tao.taoTupleWeight (a.1.take (i.1 + 1))
  have hpos : 0 < c.sizeUpTo (i.1 + 1) := by
    let k : Fin (c.length + 1) := ⟨i.1 + 1, by omega⟩
    have hk0 : (0 : Fin (c.length + 1)) < k := by
      apply Fin.mk_lt_mk.2
      change 0 < i.1 + 1
      omega
    have h := c.boundary.strictMono hk0
    rw [c.boundary_zero] at h
    exact h
  rw [show c.sizeUpTo (i.1 + 1) - 1 + 1 =
      c.sizeUpTo (i.1 + 1) by omega]
  exact ndFixedTotalValuationsEquivComposition_sizeUpTo a (i.1 + 1)

/-- Cardinality of the fixed-cardinality bars carrier. -/
theorem natCard_ndFixedTotalBars (n L : ℕ) :
    Nat.card (NDFixedTotalBars n L) =
      Nat.choose (L - 1) (n - 1) := by
  simpa [NDFixedTotalBars] using
    (Set.powersetCard.card (Fin (L - 1)) (n - 1))

/-- The uniform fixed-total valuation law, before applying the Section 7
offset map. -/
noncomputable def ndFixedTotalValuationsPMF
    (n L : ℕ) (hn : 0 < n) (hL : n ≤ L) :
    PMF (NDFixedTotalValuations n L) :=
  (ndFiberExtrasUniformPMF n L hn).map
    (ndFiberExtrasEquivFixedTotal n L hL)

/-- The uniform bars law, defined as the image of the already checked uniform
extras carrier. -/
noncomputable def ndFixedTotalBarsPMF
    (n L : ℕ) (hn : 0 < n) (hL : n ≤ L) :
    PMF (NDFixedTotalBars n L) :=
  (ndFiberExtrasUniformPMF n L hn).map
    (ndFiberExtrasEquivBars n L hn hL)

/-- The canonical uniform law on the bars carrier.  Feasibility supplies a
local inhabitant without installing an invalid global `Nonempty` instance. -/
noncomputable def ndFixedTotalBarsUniformPMF
    (n L : ℕ) (hn : 0 < n) (hL : n ≤ L) :
    PMF (NDFixedTotalBars n L) := by
  let u : Sym (Fin n) (L - n) :=
    Sym.replicate (L - n) (⟨0, hn⟩ : Fin n)
  letI : Nonempty (NDFixedTotalBars n L) :=
    ⟨ndFiberExtrasEquivBars n L hn hL u⟩
  exact PMF.uniformOfFintype _

private theorem nd_uniformOfFintype_map_equiv
    {α β : Type*} [Fintype α] [Fintype β]
    [Nonempty α] [Nonempty β] (e : α ≃ β) :
    (PMF.uniformOfFintype α).map e =
      PMF.uniformOfFintype β := by
  classical
  apply PMF.ext
  intro b
  rw [PMF.map_apply, tsum_eq_single (e.symm b)]
  · simp [PMF.uniformOfFintype_apply, Fintype.card_congr e]
  · intro a hne
    have hmiss : b ≠ e a := by
      intro h
      apply hne
      exact e.injective (by simpa using h.symm)
    simp [hmiss]

/-- The image presentation of the bars law is the canonical uniform law. -/
theorem ndFixedTotalBarsPMF_eq_uniform
    (n L : ℕ) (hn : 0 < n) (hL : n ≤ L) :
    ndFixedTotalBarsPMF n L hn hL =
      ndFixedTotalBarsUniformPMF n L hn hL := by
  let u : Sym (Fin n) (L - n) :=
    Sym.replicate (L - n) (⟨0, hn⟩ : Fin n)
  letI : Nonempty (Sym (Fin n) (L - n)) := ⟨u⟩
  letI : Nonempty (NDFixedTotalBars n L) :=
    ⟨ndFiberExtrasEquivBars n L hn hL u⟩
  simpa [ndFixedTotalBarsPMF, ndFixedTotalBarsUniformPMF,
    ndFiberExtrasUniformPMF] using
      (nd_uniformOfFintype_map_equiv
        (ndFiberExtrasEquivBars n L hn hL))

/-- Mapping the uniform fixed-total valuation law to bars produces the
canonical uniform fixed-cardinality subset law. -/
theorem ndFixedTotalValuationsPMF_map_bars_eq_uniform
    (n L : ℕ) (hn : 0 < n) (hL : n ≤ L) :
    (ndFixedTotalValuationsPMF n L hn hL).map
        (ndFixedTotalValuationsEquivBars hn hL) =
      ndFixedTotalBarsUniformPMF n L hn hL := by
  calc
    (ndFixedTotalValuationsPMF n L hn hL).map
          (ndFixedTotalValuationsEquivBars hn hL) =
        ndFixedTotalBarsPMF n L hn hL := by
      unfold ndFixedTotalValuationsPMF ndFixedTotalBarsPMF
      rw [PMF.map_comp]
      apply congrArg
        (fun f => (ndFiberExtrasUniformPMF n L hn).map f)
      funext u
      rfl
    _ = ndFixedTotalBarsUniformPMF n L hn hL :=
      ndFixedTotalBarsPMF_eq_uniform n L hn hL

/-- Every feasible bars carrier atom has the expected reciprocal binomial
mass. -/
theorem ndFixedTotalBarsPMF_apply_toReal
    (n L : ℕ) (hn : 0 < n) (hL : n ≤ L)
    (B : NDFixedTotalBars n L) :
    (ndFixedTotalBarsPMF n L hn hL B).toReal =
      1 / (Nat.choose (L - 1) (n - 1) : ℝ) := by
  rw [ndFixedTotalBarsPMF_eq_uniform]
  let u : Sym (Fin n) (L - n) :=
    Sym.replicate (L - n) (⟨0, hn⟩ : Fin n)
  letI : Nonempty (NDFixedTotalBars n L) :=
    ⟨ndFiberExtrasEquivBars n L hn hL u⟩
  simp [ndFixedTotalBarsUniformPMF, one_div,
    ← Nat.card_eq_fintype_card]
  simpa only [← Nat.card_coe_set_eq] using
    natCard_ndFixedTotalBars n L

/-- The feasible uniform bars law has full support. -/
theorem support_ndFixedTotalBarsPMF
    (n L : ℕ) (hn : 0 < n) (hL : n ≤ L) :
    (ndFixedTotalBarsPMF n L hn hL).support = Set.univ := by
  rw [ndFixedTotalBarsPMF_eq_uniform]
  let u : Sym (Fin n) (L - n) :=
    Sym.replicate (L - n) (⟨0, hn⟩ : Fin n)
  letI : Nonempty (NDFixedTotalBars n L) :=
    ⟨ndFiberExtrasEquivBars n L hn hL u⟩
  simp [ndFixedTotalBarsUniformPMF]

/-- The checked conditioned Section 7 law is the image of the uniform bars
law.  Mapping preserves residue collisions and their multiplicities. -/
theorem ndSection7FiberPMF_eq_fixedTotalBars_map
    (n L : ℕ) (hn : 0 < n) (hL : n ≤ L) :
    ndSection7FiberPMF n L hn hL =
      (ndFixedTotalBarsPMF n L hn hL).map
        (fun B =>
          Tao.taoSection7OffsetZMod n
            (((ndFixedTotalValuationsEquivBars hn hL).symm B).1)) := by
  unfold ndSection7FiberPMF ndFixedTotalBarsPMF
  rw [PMF.map_comp]
  apply congrArg
    (fun f => (ndFiberExtrasUniformPMF n L hn).map f)
  funext u
  simp [Function.comp_def, ndFiberExtrasEquivBars]

/-- Number of stored bars whose physical one-based positions are at most
`q`.  Because a stored bar is `sigma - 1`, the comparison is strict. -/
def ndBarsPrefixCount {L : ℕ}
    (S : Finset (Fin (L - 1))) (q : ℕ) : ℕ :=
  (S.filter fun b : Fin (L - 1) => (b : ℕ) < q).card

/-- Complementing the interior bars exchanges an `n`-block composition with
an `(L - n + 1)`-block composition of the same total. -/
noncomputable def ndFixedTotalBarsComplEquiv
    (n L : ℕ) (hn : 0 < n) (hL : n ≤ L) :
    NDFixedTotalBars n L ≃ NDFixedTotalBars (L - n + 1) L := by
  simpa only [NDFixedTotalBars, Nat.add_sub_cancel] using
    (Set.powersetCard.compl
      (α := Fin (L - 1)) (n := n - 1) (m := L - n)
      (by simp only [Fintype.card_fin]; omega))

@[simp] theorem ndFixedTotalBarsComplEquiv_coe
    (n L : ℕ) (hn : 0 < n) (hL : n ≤ L)
    (B : NDFixedTotalBars n L) :
    (ndFixedTotalBarsComplEquiv n L hn hL B).1 = B.1ᶜ := rfl

/-- A prefix and its complement partition every available bar position below
`q`.  The `min` form remains valid without restricting `q`. -/
theorem ndBarsPrefixCount_add_compl
    (n L q : ℕ) (hn : 0 < n) (hL : n ≤ L)
    (B : NDFixedTotalBars n L) :
    ndBarsPrefixCount B.1 q +
        ndBarsPrefixCount
          (ndFixedTotalBarsComplEquiv n L hn hL B).1 q =
      min (L - 1) q := by
  unfold ndBarsPrefixCount
  rw [ndFixedTotalBarsComplEquiv_coe]
  have hdisj :
      Disjoint
        (B.1.filter fun b : Fin (L - 1) => (b : ℕ) < q)
        (B.1ᶜ.filter fun b : Fin (L - 1) => (b : ℕ) < q) :=
    Finset.disjoint_filter_filter disjoint_compl_right
  rw [← Finset.card_union_of_disjoint hdisj]
  rw [← Finset.filter_union, Finset.union_compl]
  simpa using Fin.card_filter_val_lt (n := L - 1) (m := q)

/-- The fixed-bars law is invariant under the complement equivalence, with
the block count changed from `n` to `L - n + 1`. -/
theorem ndFixedTotalBarsPMF_map_compl
    (n L : ℕ) (hn : 0 < n) (hL : n ≤ L) :
    (ndFixedTotalBarsPMF n L hn hL).map
        (ndFixedTotalBarsComplEquiv n L hn hL) =
      ndFixedTotalBarsPMF (L - n + 1) L (by omega) (by omega) := by
  let nc : ℕ := L - n + 1
  have hnc : 0 < nc := by omega
  have hLc : nc ≤ L := by omega
  let e : NDFixedTotalBars n L ≃ NDFixedTotalBars nc L :=
    ndFixedTotalBarsComplEquiv n L hn hL
  let u : Sym (Fin n) (L - n) :=
    Sym.replicate (L - n) (⟨0, hn⟩ : Fin n)
  let B : NDFixedTotalBars n L := ndFiberExtrasEquivBars n L hn hL u
  letI : Nonempty (NDFixedTotalBars n L) := ⟨B⟩
  letI : Nonempty (NDFixedTotalBars nc L) := ⟨e B⟩
  change (ndFixedTotalBarsPMF n L hn hL).map e =
    ndFixedTotalBarsPMF nc L hnc hLc
  calc
    (ndFixedTotalBarsPMF n L hn hL).map e =
        (ndFixedTotalBarsUniformPMF n L hn hL).map e := by
      rw [ndFixedTotalBarsPMF_eq_uniform]
    _ = ndFixedTotalBarsUniformPMF nc L hnc hLc := by
      simpa [ndFixedTotalBarsUniformPMF] using
        nd_uniformOfFintype_map_equiv e
    _ = ndFixedTotalBarsPMF nc L hnc hLc :=
      (ndFixedTotalBarsPMF_eq_uniform nc L hnc hLc).symm

/-- The prefix count may be computed on the canonical increasing enumeration
of the bar set. -/
theorem ndBarsPrefixCount_eq_card_filter_barAt
    {n L : ℕ} (B : NDFixedTotalBars n L) (q : ℕ) :
    ndBarsPrefixCount B.1 q =
      (Finset.univ.filter fun i : Fin (n - 1) =>
        (ndFixedTotalBarAt B i : ℕ) < q).card := by
  unfold ndBarsPrefixCount ndFixedTotalBarAt
  have hmap := Finset.map_orderEmbOfFin_univ B.1 B.2
  calc
    (B.1.filter fun b : Fin (L - 1) => (b : ℕ) < q).card =
        ((Finset.univ.map
          (B.1.orderEmbOfFin B.2).toEmbedding).filter
            fun b : Fin (L - 1) => (b : ℕ) < q).card :=
      congrArg
        (fun S : Finset (Fin (L - 1)) =>
          (S.filter fun b : Fin (L - 1) => (b : ℕ) < q).card)
        hmap.symm
    _ = (Finset.univ.filter fun i : Fin (n - 1) =>
        ((B.1.orderEmbOfFin B.2 i : Fin (L - 1)) : ℕ) < q).card := by
      rw [Finset.filter_map, Finset.card_map]
      simp [Function.comp_def]

/-- Exact source prefix event in the bars model.  For `j < n`, the physical
prefix total through `j` parts is at most `q` exactly when at least `j` stored
bars have value strictly below `q`. -/
theorem ndFixedTotal_prefixWeight_le_iff_le_barsPrefixCount
    {n L : ℕ} (hn : 0 < n) (hL : n ≤ L)
    (a : NDFixedTotalValuations n L) {j q : ℕ} (hj : j < n) :
    Tao.taoTupleWeight (a.1.take j) ≤ q ↔
      j ≤ ndBarsPrefixCount
        (ndFixedTotalValuationsEquivBars hn hL a).1 q := by
  by_cases hj0 : j = 0
  · subst j
    simp [Tao.taoTupleWeight]
  have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
  let i : Fin (n - 1) := ⟨j - 1, by omega⟩
  let B : NDFixedTotalBars n L :=
    ndFixedTotalValuationsEquivBars hn hL a
  have hbar := ndFixedTotalBarAt_equiv_add_one hn hL a i
  have hij : i.1 + 1 = j := by
    dsimp [i]
    omega
  rw [hij] at hbar
  change (ndFixedTotalBarAt B i : ℕ) + 1 =
    Tao.taoTupleWeight (a.1.take j) at hbar
  let p : Fin (n - 1) → Prop := fun k =>
    (ndFixedTotalBarAt B k : ℕ) < q
  have hcount : ndBarsPrefixCount B.1 q =
      (Finset.univ.filter p).card := by
    simpa [p] using ndBarsPrefixCount_eq_card_filter_barAt B q
  have hp : ∀ x y, y ≤ x → p x → p y := by
    intro x y hyx hx
    have hmono := (B.1.orderEmbOfFin B.2).monotone hyx
    change (ndFixedTotalBarAt B y : ℕ) ≤
      (ndFixedTotalBarAt B x : ℕ) at hmono
    exact lt_of_le_of_lt hmono hx
  have hthreshold :
      i.1 < (Finset.univ.filter p).card ↔ p i :=
    Fin.lt_card_filter_univ_iff_apply_of_imp p hp
  change Tao.taoTupleWeight (a.1.take j) ≤ q ↔
    j ≤ ndBarsPrefixCount B.1 q
  rw [hcount]
  constructor
  · intro hw
    have hpi : p i := by
      dsimp [p]
      omega
    have hicount := hthreshold.mpr hpi
    dsimp [i] at hicount
    omega
  · intro hjcount
    have hicount : i.1 < (Finset.univ.filter p).card := by
      dsimp [i]
      omega
    have hpi := hthreshold.mp hicount
    dsimp [p] at hpi
    omega

end ND
end Erdos1135
