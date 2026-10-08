import Erdos1135.ND.Fourier.FixedTotalBars
import Erdos1135.ND.Fourier.FixedTotalSplit
import Erdos1135.Tao.Section6.ModulusProjection

/-!
# Normalized Fixed-Total Disintegration

This leaf provides the normalized T2 interface.  It places the uniform
fixed-total valuation law on the dependent head/tail split index, proves the
exact atom normalization, and closes the List-valued take disintegration and
Section-7 projection-bind identities.  Zero tail length is retained:
structurally possible indices with a positive tail total simply have zero
mass.
-/

open scoped BigOperators

namespace Erdos1135
namespace ND

open Tao

noncomputable section

/-- Every fixed-total valuation carrier is finite, including the empty
zero-length fibers. -/
@[reducible]
noncomputable def ndFixedTotalValuationsFintypeOfLe
    (n U : ℕ) (hU : n ≤ U) :
    Fintype (NDFixedTotalValuations n U) :=
  Fintype.ofEquiv (Sym (Fin n) (U - n))
    (ndFiberExtrasEquivFixedTotal n U hU)

/-- A split index is equivalently its dropped-tail total in the exact
feasible interval. -/
def ndFixedTotalSplitIndexEquivTailIcc
    (h t L : ℕ) (hL : h ≤ L) :
    NDFixedTotalSplitIndex h t L ≃
      {u : ℕ // u ∈ Finset.Icc t (L - h)} where
  toFun s := ⟨s.tailTotal, by
    simp only [Finset.mem_Icc]
    constructor
    · exact s.tailLength_le
    · have hhead := s.headLength_le
      have htotal := s.total_eq
      omega⟩
  invFun u := {
    headTotal := L - u.1
    tailTotal := u.1
    headLength_le := by
      have hu := (Finset.mem_Icc.mp u.2).2
      omega
    tailLength_le := (Finset.mem_Icc.mp u.2).1
    total_eq := by
      have hu := (Finset.mem_Icc.mp u.2).2
      omega
  }
  left_inv s := by
    apply NDFixedTotalSplitIndex.ext
    · simp only
      have htotal := s.total_eq
      omega
    · rfl
  right_inv u := by
    apply Subtype.ext
    rfl

/-- The dependent split-index carrier is finite whenever the head length is
at most the total. -/
@[reducible]
noncomputable def ndFixedTotalSplitIndexFintypeOfLe
    (h t L : ℕ) (hL : h ≤ L) :
    Fintype (NDFixedTotalSplitIndex h t L) :=
  Fintype.ofEquiv {u : ℕ // u ∈ Finset.Icc t (L - h)}
    (ndFixedTotalSplitIndexEquivTailIcc h t L hL).symm

/-- Endpoint mass is the number of fixed-total paths times their common iid
Geom(2) atom weight.  This statement includes all zero-length cases. -/
theorem ndGeom2EndpointMass_eq_natCard_fixedTotal_mul_pow
    (n U : ℕ) (hU : n ≤ U) :
    ndGeom2EndpointMass n U =
      (Nat.card (NDFixedTotalValuations n U) : ℝ) *
        (1 / 2 : ℝ) ^ U := by
  letI : Fintype (NDFixedTotalValuations n U) :=
    ndFixedTotalValuationsFintypeOfLe n U hU
  rw [ndGeom2EndpointMass_eq_tsum_fixedTotal, tsum_fintype]
  calc
    (∑ a : NDFixedTotalValuations n U,
        (Tao.geom2PNatListPMF n a.1).toReal) =
        ∑ _a : NDFixedTotalValuations n U,
          (1 / 2 : ℝ) ^ U := by
      apply Finset.sum_congr rfl
      intro a _ha
      have hmass :=
        Tao.geom2PNatListPMF_apply_length_toReal_eq_weight a.1
      rw [a.2.1] at hmass
      rw [hmass, a.2.2]
    _ = (Fintype.card (NDFixedTotalValuations n U) : ℝ) *
          (1 / 2 : ℝ) ^ U := by simp
    _ = (Nat.card (NDFixedTotalValuations n U) : ℝ) *
          (1 / 2 : ℝ) ^ U := by
      rw [Nat.card_eq_fintype_card]

private theorem nd_uniformOfFintype_map_equiv'
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

private def ndFixedTotalSplitIndexPreimageEquiv
    (h t L : ℕ) (s : NDFixedTotalSplitIndex h t L) :
    {a : NDFixedTotalValuations (h + t) L //
      ((ndFixedTotalValuationsEquivSplit h t L a).1 = s)} ≃
      NDFixedTotalSplitFiber s :=
  (ndFixedTotalValuationsEquivSplit h t L).subtypeEquivOfSubtype.trans
    (Equiv.sigmaSubtype s)

/-- The normalized dependent split-index marginal.  It is defined as the
literal image of the checked uniform full-fiber law, so multiplicities are
retained. -/
noncomputable def ndFixedTotalSplitIndexPMF
    (h t L : ℕ) (hh : 0 < h) (hL : h + t ≤ L) :
    PMF (NDFixedTotalSplitIndex h t L) :=
  (ndFixedTotalValuationsPMF (h + t) L
      (Nat.add_pos_left hh t) hL).map
    (fun a => ((ndFixedTotalValuationsEquivSplit h t L) a).1)

/-- The normalized split head total is the physical `h`th boundary of the
same uniform fixed-total composition.  The stored bar is zero-based, hence
the visible `+ 1`; positive tail length makes that boundary interior. -/
theorem ndFixedTotalSplitIndexPMF_map_headTotal_eq_barsBoundary
    (h t L : ℕ) (hh : 0 < h) (ht : 0 < t)
    (hL : h + t ≤ L) :
    (ndFixedTotalSplitIndexPMF h t L hh hL).map
        (fun s : NDFixedTotalSplitIndex h t L => s.headTotal) =
      (ndFixedTotalBarsPMF (h + t) L
          (Nat.add_pos_left hh t) hL).map
        (fun B =>
          (ndFixedTotalBarAt B
              (⟨h - 1, by omega⟩ : Fin (h + t - 1)) : ℕ) + 1) := by
  let hn : 0 < h + t := Nat.add_pos_left hh t
  let i : Fin (h + t - 1) := ⟨h - 1, by omega⟩
  have hbars :
      (ndFixedTotalValuationsPMF (h + t) L hn hL).map
          (ndFixedTotalValuationsEquivBars hn hL) =
        ndFixedTotalBarsPMF (h + t) L hn hL := by
    unfold ndFixedTotalValuationsPMF ndFixedTotalBarsPMF
    rw [PMF.map_comp]
    apply congrArg
      (fun f => (ndFiberExtrasUniformPMF (h + t) L hn).map f)
    funext u
    rfl
  change
    (ndFixedTotalSplitIndexPMF h t L hh hL).map
        (fun s : NDFixedTotalSplitIndex h t L => s.headTotal) =
      (ndFixedTotalBarsPMF (h + t) L hn hL).map
        (fun B => (ndFixedTotalBarAt B i : ℕ) + 1)
  rw [← hbars]
  unfold ndFixedTotalSplitIndexPMF
  rw [PMF.map_comp, PMF.map_comp]
  apply congrArg
    (fun f => (ndFixedTotalValuationsPMF (h + t) L hn hL).map f)
  funext a
  change
    ((ndFixedTotalValuationsEquivSplit h t L a).1).headTotal =
      (ndFixedTotalBarAt
        (ndFixedTotalValuationsEquivBars hn hL a) i : ℕ) + 1
  rw [ndFixedTotalValuationsEquivSplit_headTotal]
  symm
  have hbar := ndFixedTotalBarAt_equiv_add_one hn hL a i
  have hi : i.1 + 1 = h := by
    dsimp [i]
    omega
  rw [hi] at hbar
  exact hbar

/-- A physical fixed-bars boundary is at most `q` exactly when its prefix
contains the corresponding number of bars. -/
private theorem ndFixedTotalBars_boundary_le_iff_le_prefixCount
    (h t L q : ℕ) (hh : 0 < h) (ht : 0 < t)
    (hL : h + t ≤ L) (B : NDFixedTotalBars (h + t) L) :
    (ndFixedTotalBarAt B
        (⟨h - 1, by omega⟩ : Fin (h + t - 1)) : ℕ) + 1 ≤ q ↔
      h ≤ ndBarsPrefixCount B.1 q := by
  let hn : 0 < h + t := Nat.add_pos_left hh t
  let i : Fin (h + t - 1) := ⟨h - 1, by omega⟩
  let a : NDFixedTotalValuations (h + t) L :=
    (ndFixedTotalValuationsEquivBars hn hL).symm B
  have haB : ndFixedTotalValuationsEquivBars hn hL a = B :=
    (ndFixedTotalValuationsEquivBars hn hL).apply_symm_apply B
  have hi : i.1 + 1 = h := by
    dsimp [i]
    omega
  have hbar := ndFixedTotalBarAt_equiv_add_one hn hL a i
  rw [hi, haB] at hbar
  have hp := ndFixedTotal_prefixWeight_le_iff_le_barsPrefixCount
    hn hL a (j := h) (q := q) (by omega)
  rw [haB] at hp
  change (ndFixedTotalBarAt B i : ℕ) + 1 ≤ q ↔
    h ≤ ndBarsPrefixCount B.1 q
  rw [hbar]
  exact hp

/-- The split-head lower-tail event is the matching prefix-count event in the
uniform bars model.  Evaluating the Bool image at `false` gives the matching
strict upper-tail event as well. -/
theorem ndFixedTotalSplitIndexPMF_map_headTotal_le_eq_barsPrefixCount
    (h t L q : ℕ) (hh : 0 < h) (ht : 0 < t)
    (hL : h + t ≤ L) :
    (ndFixedTotalSplitIndexPMF h t L hh hL).map
        (fun s : NDFixedTotalSplitIndex h t L =>
          decide (s.headTotal ≤ q)) =
      (ndFixedTotalBarsPMF (h + t) L
          (Nat.add_pos_left hh t) hL).map
        (fun B => decide (h ≤ ndBarsPrefixCount B.1 q)) := by
  let i : Fin (h + t - 1) := ⟨h - 1, by omega⟩
  have hpush :=
    ndFixedTotalSplitIndexPMF_map_headTotal_eq_barsBoundary
      h t L hh ht hL
  change
    (ndFixedTotalSplitIndexPMF h t L hh hL).map
        (fun s => s.headTotal) =
      (ndFixedTotalBarsPMF (h + t) L
          (Nat.add_pos_left hh t) hL).map
        (fun B => (ndFixedTotalBarAt B i : ℕ) + 1) at hpush
  have hpushBool := congrArg
    (fun p : PMF ℕ => p.map (fun z => decide (z ≤ q))) hpush
  dsimp only at hpushBool
  rw [PMF.map_comp, PMF.map_comp] at hpushBool
  calc
    (ndFixedTotalSplitIndexPMF h t L hh hL).map
        (fun s => decide (s.headTotal ≤ q)) =
      (ndFixedTotalBarsPMF (h + t) L
          (Nat.add_pos_left hh t) hL).map
        (fun B => decide ((ndFixedTotalBarAt B i : ℕ) + 1 ≤ q)) := by
          simpa only [Function.comp_apply] using hpushBool
    _ = (ndFixedTotalBarsPMF (h + t) L
          (Nat.add_pos_left hh t) hL).map
        (fun B => decide (h ≤ ndBarsPrefixCount B.1 q)) := by
      apply congrArg
        (fun f => (ndFixedTotalBarsPMF (h + t) L
          (Nat.add_pos_left hh t) hL).map f)
      funext B
      exact decide_eq_decide.mpr
        (ndFixedTotalBars_boundary_le_iff_le_prefixCount
          h t L q hh ht hL B)

/-- A split atom is exactly the cardinality of its dependent head/tail fiber
divided by the cardinality of the full fixed-total fiber. -/
theorem ndFixedTotalSplitIndexPMF_apply_toReal_eq_card_ratio
    (h t L : ℕ) (hh : 0 < h) (hL : h + t ≤ L)
    (s : NDFixedTotalSplitIndex h t L) :
    (ndFixedTotalSplitIndexPMF h t L hh hL s).toReal =
      (Nat.card (NDFixedTotalSplitFiber s) : ℝ) /
        (Nat.card (NDFixedTotalValuations (h + t) L) : ℝ) := by
  classical
  let u : Sym (Fin (h + t)) (L - (h + t)) :=
    Sym.replicate (L - (h + t))
      (⟨0, Nat.add_pos_left hh t⟩ : Fin (h + t))
  letI : Nonempty (Sym (Fin (h + t)) (L - (h + t))) := ⟨u⟩
  letI : Fintype (NDFixedTotalValuations (h + t) L) :=
    ndFixedTotalValuationsFintypeOfLe (h + t) L hL
  letI : Nonempty (NDFixedTotalValuations (h + t) L) :=
    ⟨ndFiberExtrasEquivFixedTotal (h + t) L hL u⟩
  letI _ (s' : NDFixedTotalSplitIndex h t L) :
      Fintype (NDFixedTotalValuations h s'.headTotal) :=
    ndFixedTotalValuationsFintypeOfLe
      h s'.headTotal s'.headLength_le
  letI _ (s' : NDFixedTotalSplitIndex h t L) :
      Fintype (NDFixedTotalValuations t s'.tailTotal) :=
    ndFixedTotalValuationsFintypeOfLe
      t s'.tailTotal s'.tailLength_le
  have hp_uniform :
      ndFixedTotalValuationsPMF (h + t) L
          (Nat.add_pos_left hh t) hL =
        PMF.uniformOfFintype
          (NDFixedTotalValuations (h + t) L) := by
    simpa [ndFixedTotalValuationsPMF, ndFiberExtrasUniformPMF] using
      (nd_uniformOfFintype_map_equiv'
        (ndFiberExtrasEquivFixedTotal (h + t) L hL))
  let f : NDFixedTotalValuations (h + t) L →
      NDFixedTotalSplitIndex h t L :=
    fun a => ((ndFixedTotalValuationsEquivSplit h t L) a).1
  calc
    (ndFixedTotalSplitIndexPMF h t L hh hL s).toReal =
        Tao.pmfProb
          (ndFixedTotalValuationsPMF (h + t) L
            (Nat.add_pos_left hh t) hL)
          {a | f a = s} := by
      exact (Tao.pmfProb_singleton_eq_map_apply_toReal
        (ndFixedTotalValuationsPMF (h + t) L
          (Nat.add_pos_left hh t) hL) f s).symm
    _ = Tao.pmfProb
          (PMF.uniformOfFintype
            (NDFixedTotalValuations (h + t) L))
          {a | f a = s} := by rw [hp_uniform]
    _ = (Fintype.card {a : NDFixedTotalValuations (h + t) L //
            f a = s} : ℝ) /
          (Fintype.card (NDFixedTotalValuations (h + t) L) : ℝ) :=
      Tao.pmfProb_uniformOfFintype _
    _ = (Fintype.card (NDFixedTotalSplitFiber s) : ℝ) /
          (Fintype.card (NDFixedTotalValuations (h + t) L) : ℝ) := by
      rw [Fintype.card_congr
        (ndFixedTotalSplitIndexPreimageEquiv h t L s)]
    _ = (Nat.card (NDFixedTotalSplitFiber s) : ℝ) /
          (Nat.card (NDFixedTotalValuations (h + t) L) : ℝ) := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]

/-- The exact normalized endpoint-mass ratio.  It remains valid at zero tail
length; empty zero-length tail fibers give structural zero atoms. -/
theorem ndFixedTotalSplitIndexPMF_apply_toReal
    (h t L : ℕ) (hh : 0 < h) (hL : h + t ≤ L)
    (s : NDFixedTotalSplitIndex h t L) :
    (ndFixedTotalSplitIndexPMF h t L hh hL s).toReal =
      ndGeom2EndpointMass h s.headTotal *
          ndGeom2EndpointMass t s.tailTotal /
        ndGeom2EndpointMass (h + t) L := by
  classical
  have hfullMass : ndGeom2EndpointMass (h + t) L ≠ 0 :=
    ndGeom2EndpointMass_ne_zero (Nat.add_pos_left hh t) hL
  apply (eq_div_iff hfullMass).2
  rw [ndFixedTotalSplitIndexPMF_apply_toReal_eq_card_ratio]
  rw [ndGeom2EndpointMass_eq_natCard_fixedTotal_mul_pow
      (h + t) L hL,
    ndGeom2EndpointMass_eq_natCard_fixedTotal_mul_pow
      h s.headTotal s.headLength_le,
    ndGeom2EndpointMass_eq_natCard_fixedTotal_mul_pow
      t s.tailTotal s.tailLength_le]
  rw [Nat.card_prod]
  change
    ((Nat.card (NDFixedTotalValuations h s.headTotal) *
        Nat.card (NDFixedTotalValuations t s.tailTotal) : ℕ) : ℝ) /
          (Nat.card (NDFixedTotalValuations (h + t) L) : ℝ) *
        ((Nat.card (NDFixedTotalValuations (h + t) L) : ℝ) *
          (1 / 2 : ℝ) ^ L) =
      ((Nat.card (NDFixedTotalValuations h s.headTotal) : ℝ) *
          (1 / 2 : ℝ) ^ s.headTotal) *
        ((Nat.card (NDFixedTotalValuations t s.tailTotal) : ℝ) *
          (1 / 2 : ℝ) ^ s.tailTotal)
  have hfullCard :
      (Nat.card (NDFixedTotalValuations (h + t) L) : ℝ) ≠ 0 := by
    intro hcard
    apply hfullMass
    rw [ndGeom2EndpointMass_eq_natCard_fixedTotal_mul_pow
      (h + t) L hL, hcard]
    simp
  have hpow :
      (1 / 2 : ℝ) ^ s.headTotal *
          (1 / 2 : ℝ) ^ s.tailTotal =
        (1 / 2 : ℝ) ^ L := by
    rw [← pow_add, s.total_eq]
  field_simp [hfullCard]
  rw [← hpow]
  push_cast
  ring

/-- In the positive-tail regime the normalized atom is the usual
hypergeometric ratio of positive-composition counts. -/
theorem ndFixedTotalSplitIndexPMF_apply_toReal_eq_choose_ratio
    (h t L : ℕ) (hh : 0 < h) (ht : 0 < t)
    (hL : h + t ≤ L)
    (s : NDFixedTotalSplitIndex h t L) :
    (ndFixedTotalSplitIndexPMF h t L hh hL s).toReal =
      (Nat.choose (s.headTotal - 1) (h - 1) : ℝ) *
          (Nat.choose (s.tailTotal - 1) (t - 1) : ℝ) /
        (Nat.choose (L - 1) (h + t - 1) : ℝ) := by
  rw [ndFixedTotalSplitIndexPMF_apply_toReal_eq_card_ratio]
  change
    (Nat.card
        (NDFixedTotalValuations h s.headTotal ×
          NDFixedTotalValuations t s.tailTotal) : ℝ) /
      (Nat.card (NDFixedTotalValuations (h + t) L) : ℝ) = _
  rw [Nat.card_prod,
    natCard_fixedTotalValuations hh s.headLength_le,
    natCard_fixedTotalValuations ht s.tailLength_le,
    natCard_fixedTotalValuations (Nat.add_pos_left hh t) hL]
  push_cast
  rfl

private theorem ndFixedTotalValuationsPMF_apply_toReal_eq_inv_natCard
    (n U : ℕ) (hn : 0 < n) (hU : n ≤ U)
    (a : NDFixedTotalValuations n U) :
    (ndFixedTotalValuationsPMF n U hn hU a).toReal =
      1 / (Nat.card (NDFixedTotalValuations n U) : ℝ) := by
  classical
  let u : Sym (Fin n) (U - n) :=
    Sym.replicate (U - n) (⟨0, hn⟩ : Fin n)
  letI : Fintype (NDFixedTotalValuations n U) :=
    ndFixedTotalValuationsFintypeOfLe n U hU
  letI : Nonempty (Sym (Fin n) (U - n)) := ⟨u⟩
  letI : Nonempty (NDFixedTotalValuations n U) :=
    ⟨ndFiberExtrasEquivFixedTotal n U hU u⟩
  have hp_uniform :
      ndFixedTotalValuationsPMF n U hn hU =
        PMF.uniformOfFintype
          (NDFixedTotalValuations n U) := by
    simpa [ndFixedTotalValuationsPMF, ndFiberExtrasUniformPMF] using
      (nd_uniformOfFintype_map_equiv'
        (ndFiberExtrasEquivFixedTotal n U hU))
  rw [hp_uniform]
  simp [one_div]

private theorem
    ndFixedTotalValuationsPMF_map_apply_toReal_eq_card_ratio
    {β : Type*} (n U : ℕ) (hn : 0 < n) (hU : n ≤ U)
    (f : NDFixedTotalValuations n U → β) (b : β) :
    (((ndFixedTotalValuationsPMF n U hn hU).map f) b).toReal =
      (Nat.card {a : NDFixedTotalValuations n U // f a = b} : ℝ) /
        (Nat.card (NDFixedTotalValuations n U) : ℝ) := by
  classical
  let u : Sym (Fin n) (U - n) :=
    Sym.replicate (U - n) (⟨0, hn⟩ : Fin n)
  letI : Fintype (NDFixedTotalValuations n U) :=
    ndFixedTotalValuationsFintypeOfLe n U hU
  letI : Nonempty (Sym (Fin n) (U - n)) := ⟨u⟩
  letI : Nonempty (NDFixedTotalValuations n U) :=
    ⟨ndFiberExtrasEquivFixedTotal n U hU u⟩
  have hp_uniform :
      ndFixedTotalValuationsPMF n U hn hU =
        PMF.uniformOfFintype
          (NDFixedTotalValuations n U) := by
    simpa [ndFixedTotalValuationsPMF, ndFiberExtrasUniformPMF] using
      (nd_uniformOfFintype_map_equiv'
        (ndFiberExtrasEquivFixedTotal n U hU))
  calc
    (((ndFixedTotalValuationsPMF n U hn hU).map f) b).toReal =
        Tao.pmfProb (ndFixedTotalValuationsPMF n U hn hU)
          {a | f a = b} := by
      exact (Tao.pmfProb_singleton_eq_map_apply_toReal
        (ndFixedTotalValuationsPMF n U hn hU) f b).symm
    _ = Tao.pmfProb
          (PMF.uniformOfFintype (NDFixedTotalValuations n U))
          {a | f a = b} := by
      rw [hp_uniform]
    _ = (Fintype.card
            {a : NDFixedTotalValuations n U // f a = b} : ℝ) /
          (Fintype.card (NDFixedTotalValuations n U) : ℝ) :=
      Tao.pmfProb_uniformOfFintype _
    _ = (Nat.card
            {a : NDFixedTotalValuations n U // f a = b} : ℝ) /
          (Nat.card (NDFixedTotalValuations n U) : ℝ) := by
      rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]

/-- A split together with its retained head, before the tail is forgotten. -/
private abbrev NDFixedTotalSplitHead (h t L : ℕ) :=
  Σ s : NDFixedTotalSplitIndex h t L,
    NDFixedTotalValuations h s.headTotal

private def ndFixedTotalSplitEquivSplitHeadTail (h t L : ℕ) :
    NDFixedTotalSplit h t L ≃
      Σ z : NDFixedTotalSplitHead h t L,
        NDFixedTotalValuations t z.1.tailTotal where
  toFun z := ⟨⟨z.1, z.2.1⟩, z.2.2⟩
  invFun z := ⟨z.1.1, ⟨z.1.2, z.2⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def ndFixedTotalValuationsEquivSplitHeadTail (h t L : ℕ) :
    NDFixedTotalValuations (h + t) L ≃
      Σ z : NDFixedTotalSplitHead h t L,
        NDFixedTotalValuations t z.1.tailTotal :=
  (ndFixedTotalValuationsEquivSplit h t L).trans
    (ndFixedTotalSplitEquivSplitHeadTail h t L)

private def ndFixedTotalValuationsSplitHead
    (h t L : ℕ) (a : NDFixedTotalValuations (h + t) L) :
    NDFixedTotalSplitHead h t L :=
  (ndFixedTotalValuationsEquivSplitHeadTail h t L a).1

@[simp]
private theorem ndFixedTotalValuationsSplitHead_val
    (h t L : ℕ) (a : NDFixedTotalValuations (h + t) L) :
    (ndFixedTotalValuationsSplitHead h t L a).2.1 = a.1.take h := rfl

private def ndFixedTotalSplitHeadPreimageEquivTail
    (h t L : ℕ) (z : NDFixedTotalSplitHead h t L) :
    {a : NDFixedTotalValuations (h + t) L //
      ndFixedTotalValuationsSplitHead h t L a = z} ≃
      NDFixedTotalValuations t z.1.tailTotal :=
  (ndFixedTotalValuationsEquivSplitHeadTail h t L).subtypeEquivOfSubtype.trans
    (Equiv.sigmaSubtype z)

private theorem
    ndFixedTotalValuationsPMF_map_splitHead_apply_toReal
    (h t L : ℕ) (hh : 0 < h) (hL : h + t ≤ L)
    (z : NDFixedTotalSplitHead h t L) :
    (((ndFixedTotalValuationsPMF (h + t) L
        (Nat.add_pos_left hh t) hL).map
      (ndFixedTotalValuationsSplitHead h t L)) z).toReal =
        (Nat.card (NDFixedTotalValuations t z.1.tailTotal) : ℝ) /
          (Nat.card (NDFixedTotalValuations (h + t) L) : ℝ) := by
  rw [ndFixedTotalValuationsPMF_map_apply_toReal_eq_card_ratio]
  rw [Nat.card_congr
    (ndFixedTotalSplitHeadPreimageEquivTail h t L z)]

private theorem nd_pmf_map_apply_of_injective
    {α β : Type*} (p : PMF α) (f : α → β)
    (hf : Function.Injective f) (a : α) :
    (p.map f) (f a) = p a := by
  classical
  rw [PMF.map_apply, tsum_eq_single a]
  · simp
  · intro b hba
    have hne : f a ≠ f b := by
      intro hab
      exact hba (hf hab).symm
    simp [hne]

private theorem ndFixedTotalValuationsPMF_map_splitHead_eq_bind
    (h t L : ℕ) (hh : 0 < h) (hL : h + t ≤ L) :
    (ndFixedTotalValuationsPMF (h + t) L
        (Nat.add_pos_left hh t) hL).map
        (ndFixedTotalValuationsSplitHead h t L) =
      (ndFixedTotalSplitIndexPMF h t L hh hL).bind
        (fun s =>
          (ndFixedTotalValuationsPMF
              h s.headTotal hh s.headLength_le).map
            (fun head =>
              (⟨s, head⟩ : NDFixedTotalSplitHead h t L))) := by
  classical
  letI : Fintype (NDFixedTotalValuations (h + t) L) :=
    ndFixedTotalValuationsFintypeOfLe (h + t) L hL
  letI : Fintype (NDFixedTotalSplitIndex h t L) :=
    ndFixedTotalSplitIndexFintypeOfLe h t L (by omega)
  letI _ (s : NDFixedTotalSplitIndex h t L) :
      Fintype (NDFixedTotalValuations h s.headTotal) :=
    ndFixedTotalValuationsFintypeOfLe
      h s.headTotal s.headLength_le
  letI _ (s : NDFixedTotalSplitIndex h t L) :
      Fintype (NDFixedTotalValuations t s.tailTotal) :=
    ndFixedTotalValuationsFintypeOfLe
      t s.tailTotal s.tailLength_le
  apply PMF.ext
  rintro ⟨s, head⟩
  apply (ENNReal.toReal_eq_toReal_iff'
    (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
  rw [PMF.bind_apply, tsum_eq_single s]
  · have hmap :
        ((ndFixedTotalValuationsPMF
            h s.headTotal hh s.headLength_le).map
          (fun head' =>
            (⟨s, head'⟩ : NDFixedTotalSplitHead h t L)))
            (⟨s, head⟩ : NDFixedTotalSplitHead h t L) =
          ndFixedTotalValuationsPMF
            h s.headTotal hh s.headLength_le head := by
      exact nd_pmf_map_apply_of_injective
        (ndFixedTotalValuationsPMF
          h s.headTotal hh s.headLength_le)
        (fun head' =>
          (⟨s, head'⟩ : NDFixedTotalSplitHead h t L))
        (by
          intro a b hab
          exact eq_of_heq (Sigma.mk.inj_iff.mp hab).2)
        head
    rw [hmap]
    rw [ENNReal.toReal_mul]
    rw [ndFixedTotalValuationsPMF_map_splitHead_apply_toReal
        h t L hh hL ⟨s, head⟩,
      ndFixedTotalSplitIndexPMF_apply_toReal_eq_card_ratio
        h t L hh hL s,
      ndFixedTotalValuationsPMF_apply_toReal_eq_inv_natCard
        h s.headTotal hh s.headLength_le head,
      Nat.card_prod]
    letI : Nonempty (NDFixedTotalValuations h s.headTotal) := ⟨head⟩
    have hheadCardNat :
        Nat.card (NDFixedTotalValuations h s.headTotal) ≠ 0 :=
      Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩
    have hheadCard :
        (Nat.card (NDFixedTotalValuations h s.headTotal) : ℝ) ≠ 0 := by
      exact_mod_cast hheadCardNat
    field_simp [hheadCard]
    push_cast
    ring
  · intro s' hs'
    have hzero :
        ((ndFixedTotalValuationsPMF
            h s'.headTotal hh s'.headLength_le).map
          (fun head' =>
            (⟨s', head'⟩ : NDFixedTotalSplitHead h t L)))
            (⟨s, head⟩ : NDFixedTotalSplitHead h t L) = 0 := by
      rw [PMF.map_apply, ENNReal.tsum_eq_zero]
      intro head'
      have hne :
          (⟨s, head⟩ : NDFixedTotalSplitHead h t L) ≠
            (⟨s', head'⟩ : NDFixedTotalSplitHead h t L) := by
        intro heq
        exact hs' (congrArg Sigma.fst heq).symm
      simp [hne]
    rw [hzero, mul_zero]

/-- The first `h` valuations of a uniform fixed-total length-`h+t` fiber are
the exact dependent mixture of the feasible uniform head fibers.  The theorem
includes `t = 0`; impossible zero-length tail branches have zero marginal
mass and require no tail PMF. -/
theorem ndFixedTotalValuationsPMF_map_take_eq_splitBind
    (h t L : ℕ) (hh : 0 < h) (hL : h + t ≤ L) :
    (ndFixedTotalValuationsPMF (h + t) L
        (Nat.add_pos_left hh t) hL).map
        (fun a => a.1.take h) =
      (ndFixedTotalSplitIndexPMF h t L hh hL).bind
        (fun s =>
          (ndFixedTotalValuationsPMF
              h s.headTotal hh s.headLength_le).map
            Subtype.val) := by
  have hsplit :=
    ndFixedTotalValuationsPMF_map_splitHead_eq_bind h t L hh hL
  have hmap := congrArg
    (PMF.map
      (fun z : NDFixedTotalSplitHead h t L => z.2.1)) hsplit
  simpa only [PMF.map_comp, PMF.map_bind, Function.comp_apply,
    ndFixedTotalValuationsSplitHead_val] using hmap

/-- The conditioned Section-7 law is the image of the uniform list-shaped
fixed-total fiber. -/
theorem ndSection7FiberPMF_eq_fixedTotalValuations_map
    (n U : ℕ) (hn : 0 < n) (hU : n ≤ U) :
    ndSection7FiberPMF n U hn hU =
      (ndFixedTotalValuationsPMF n U hn hU).map
        (fun a => Tao.taoSection7OffsetZMod n a.1) := by
  unfold ndSection7FiberPMF ndFixedTotalValuationsPMF
  rw [PMF.map_comp]
  apply congrArg
    (fun f => (ndFiberExtrasUniformPMF n U hn).map f)
  funext u
  rfl

/-- Projecting a conditioned length-`h+t` Section-7 fiber to level `h` is
exactly the dependent split-index mixture of the conditioned head fibers. -/
theorem ndSection7FiberPMF_map_projection_eq_splitBind
    (h t L : ℕ) (hh : 0 < h) (hL : h + t ≤ L) :
    (ndSection7FiberPMF (h + t) L
        (Nat.add_pos_left hh t) hL).map
        (Tao.taoZModThreeProjection
          (Nat.le_add_right h t)) =
      (ndFixedTotalSplitIndexPMF h t L hh hL).bind
        (fun s =>
          ndSection7FiberPMF
            h s.headTotal hh s.headLength_le) := by
  calc
    (ndSection7FiberPMF (h + t) L
          (Nat.add_pos_left hh t) hL).map
          (Tao.taoZModThreeProjection
            (Nat.le_add_right h t)) =
        ((ndFixedTotalValuationsPMF (h + t) L
            (Nat.add_pos_left hh t) hL).map
            (fun a => a.1.take h)).map
          (fun as => Tao.taoSection7OffsetZMod h as) := by
      rw [ndSection7FiberPMF_eq_fixedTotalValuations_map]
      rw [PMF.map_comp, PMF.map_comp]
      apply congrArg
        (fun f =>
          (ndFixedTotalValuationsPMF (h + t) L
            (Nat.add_pos_left hh t) hL).map f)
      funext a
      exact Tao.taoSection7OffsetZMod_projection_eq_take_of_le
        (Nat.le_add_right h t) a.1
    _ = ((ndFixedTotalSplitIndexPMF h t L hh hL).bind
          (fun s =>
            (ndFixedTotalValuationsPMF
                h s.headTotal hh s.headLength_le).map
              Subtype.val)).map
          (fun as => Tao.taoSection7OffsetZMod h as) := by
      rw [ndFixedTotalValuationsPMF_map_take_eq_splitBind]
    _ = (ndFixedTotalSplitIndexPMF h t L hh hL).bind
          (fun s =>
            (ndFixedTotalValuationsPMF
                h s.headTotal hh s.headLength_le).map
              (fun a => Tao.taoSection7OffsetZMod h a.1)) := by
      rw [PMF.map_bind]
      apply congrArg
        (fun K => (ndFixedTotalSplitIndexPMF h t L hh hL).bind K)
      funext s
      rw [PMF.map_comp]
      rfl
    _ = (ndFixedTotalSplitIndexPMF h t L hh hL).bind
          (fun s =>
            ndSection7FiberPMF
              h s.headTotal hh s.headLength_le) := by
      apply congrArg
        (fun K => (ndFixedTotalSplitIndexPMF h t L hh hL).bind K)
      funext s
      exact (ndSection7FiberPMF_eq_fixedTotalValuations_map
        h s.headTotal hh s.headLength_le).symm

end

end ND
end Erdos1135
