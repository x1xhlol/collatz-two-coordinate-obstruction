/-
Compatibility modification, 8 October 2026: proof elaboration and unused bound-variable names only.
See provenance/envelope-linter-patches.json for exact source hashes and patches.
-/
import Erdos1135.ND.Fourier.FiberHoldTransport
import Erdos1135.Tao.Probability.FullL1
import Mathlib.Data.Sym.Card
import Mathlib.SetTheory.Cardinal.Finite

/-!
# Fixed-Fiber Section 7 Conditioning

This leaf supplies the finite carrier and exact endpoint mass needed to
normalize the fixed-total numerator.  The public mass event deliberately
matches the weight selector in `ndSection7FiberNumerator`; the Geom(2) list
law's checked length support then restricts it to a finite positive-composition
fiber.
-/

open scoped BigOperators

namespace Erdos1135
namespace ND

open Tao

/-- The total-weight event used to condition the length-`n` Geom(2) list law. -/
def ndSection7WeightEvent (L : ℕ) : Set (List ℕ+) :=
  {as | Tao.taoTupleWeight as = L}

/-- Positive valuation lists of length `n` and total weight `L`. -/
abbrev NDFixedTotalValuations (n L : ℕ) :=
  {as : List ℕ+ // as.length = n ∧ Tao.taoTupleWeight as = L}

/-- Function-shaped positive compositions, used only as the finite counting
carrier between fixed-length lists and Mathlib's symmetric powers. -/
def NDPositiveValuationTuple (n L : ℕ) :=
  {a : Fin n → ℕ+ // ∑ i, (a i : ℕ) = L}

/-- Real mass of the total-weight `L` event under the length-`n` Geom(2)
valuation law. -/
noncomputable def ndGeom2EndpointMass (n L : ℕ) : ℝ :=
  ((Tao.geom2PNatListPMF n).toOuterMeasure
    (ndSection7WeightEvent L)).toReal

private theorem nd_taoTupleWeight_ofFn {n : ℕ} (a : Fin n → ℕ+) :
    Tao.taoTupleWeight (List.ofFn a) = ∑ i, (a i : ℕ) := by
  unfold Tao.taoTupleWeight
  rw [List.bind_eq_flatMap]
  rw [show List.map (fun a : ℕ => a)
        (List.flatMap (fun a : ℕ+ => pure (a : ℕ)) (List.ofFn a)) =
      List.flatMap (fun a : ℕ+ => pure (a : ℕ)) (List.ofFn a) by
    exact List.map_id _]
  rw [show List.flatMap (fun a : ℕ+ => pure (a : ℕ)) (List.ofFn a) =
      List.map (fun a : ℕ+ => (a : ℕ)) (List.ofFn a) by
    simpa [Function.comp_def] using
      List.flatMap_pure_eq_map (fun a : ℕ+ => (a : ℕ)) (List.ofFn a)]
  rw [List.map_ofFn]
  change (List.ofFn (fun i : Fin n => (a i : ℕ))).sum =
    Finset.univ.sum fun i => (a i : ℕ)
  rw [List.sum_ofFn]

private noncomputable def ndFiberGetLength {n : ℕ} (as : List ℕ+)
    (hlen : as.length = n) : Fin n → ℕ+ :=
  fun i => as.get (Fin.cast hlen.symm i)

private theorem ndFiber_ofFn_getLength {n : ℕ} (as : List ℕ+)
    (hlen : as.length = n) :
    List.ofFn (ndFiberGetLength as hlen) = as := by
  subst n
  unfold ndFiberGetLength
  convert List.ofFn_get as using 1

/-- Fixed-length lists are exactly function-shaped positive compositions. -/
noncomputable def ndFixedTotalValuationsEquivPositiveTuple (n L : ℕ) :
    NDFixedTotalValuations n L ≃ NDPositiveValuationTuple n L where
  toFun as := ⟨ndFiberGetLength as.1 as.2.1, by
    rw [← nd_taoTupleWeight_ofFn, ndFiber_ofFn_getLength]
    exact as.2.2⟩
  invFun a := ⟨List.ofFn a.1, by
    exact ⟨List.length_ofFn, by
      rw [nd_taoTupleWeight_ofFn]
      exact a.2⟩⟩
  left_inv as := by
    apply Subtype.ext
    exact ndFiber_ofFn_getLength as.1 as.2.1
  right_inv a := by
    apply Subtype.ext
    funext i
    simp [ndFiberGetLength]

/-- Subtracting one from every positive coordinate identifies a total-`L`
positive tuple with a weak composition of `L - n`. -/
noncomputable def ndPositiveValuationTupleEquivSym
    {n L : ℕ} (hL : n ≤ L) :
    NDPositiveValuationTuple n L ≃ Sym (Fin n) (L - n) := by
  let e : (Fin n → ℕ+) ≃ (Fin n → ℕ) :=
    Equiv.piCongrRight (fun _ => Equiv.pnatEquivNat)
  refine (Equiv.subtypeEquiv e ?_).trans
    (Sym.equivNatSumOfFintype (Fin n) (L - n)).symm
  intro a
  change (∑ i, (a i : ℕ)) = L ↔ ∑ i, (e a) i = L - n
  have hshift : (∑ i, (a i : ℕ)) = (∑ i, (e a) i) + n := by
    calc
      (∑ i, (a i : ℕ)) = ∑ i, ((e a) i + 1) := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact (PNat.natPred_add_one (a i)).symm
      _ = (∑ i, (e a) i) + n := by
        rw [Finset.sum_add_distrib]
        simp
  omega

/-- Weak extras of total `L - n`, decoded as a fixed-total positive valuation
list.  This is the carrier used by the conditioned finite PMF. -/
noncomputable def ndFiberExtrasEquivFixedTotal
    (n L : ℕ) (hL : n ≤ L) :
    Sym (Fin n) (L - n) ≃ NDFixedTotalValuations n L :=
  ((ndFixedTotalValuationsEquivPositiveTuple n L).trans
    (ndPositiveValuationTupleEquivSym hL)).symm

/-- Stars and bars in the exact endpoint form used by the v10 source. -/
theorem card_ndFiberExtras (n L : ℕ) (hn : 0 < n) (hL : n ≤ L) :
    Fintype.card (Sym (Fin n) (L - n)) =
      Nat.choose (L - 1) (n - 1) := by
  calc
    Fintype.card (Sym (Fin n) (L - n)) =
        Nat.choose (L - 1) (L - n) := by
      rw [Sym.card_sym_eq_choose, Fintype.card_fin,
        Nat.add_sub_of_le hL]
    _ = Nat.choose (L - 1) (n - 1) :=
      Nat.choose_symm_of_eq_add (by omega)

/-- Cardinality of the list-shaped fixed-total fiber. -/
theorem natCard_fixedTotalValuations
    {n L : ℕ} (hn : 0 < n) (hL : n ≤ L) :
    Nat.card (NDFixedTotalValuations n L) =
      Nat.choose (L - 1) (n - 1) := by
  calc
    Nat.card (NDFixedTotalValuations n L) =
        Nat.card (Sym (Fin n) (L - n)) :=
      Nat.card_congr (ndFiberExtrasEquivFixedTotal n L hL).symm
    _ = Fintype.card (Sym (Fin n) (L - n)) :=
      Nat.card_eq_fintype_card
    _ = Nat.choose (L - 1) (n - 1) :=
      card_ndFiberExtras n L hn hL

/-- The endpoint mass is literally the real weight-selector series used by
the fixed-fiber numerator. -/
theorem ndGeom2EndpointMass_eq_weightSelector (n L : ℕ) :
    ndGeom2EndpointMass n L =
      ∑' as : List ℕ+,
        if Tao.taoTupleWeight as = L then
          (Tao.geom2PNatListPMF n as).toReal
        else 0 := by
  classical
  rw [ndGeom2EndpointMass, Tao.pmfOuterMass_toReal_eq_tsum_indicator]
  apply tsum_congr
  intro as
  by_cases hweight : Tao.taoTupleWeight as = L <;>
    simp [ndSection7WeightEvent, Set.indicator, hweight]

/-- The weight-selector mass may be restricted to the finite exact-length
fiber because all off-length Geom(2) atoms vanish. -/
theorem ndGeom2EndpointMass_eq_tsum_fixedTotal (n L : ℕ) :
    ndGeom2EndpointMass n L =
      ∑' as : NDFixedTotalValuations n L,
        (Tao.geom2PNatListPMF n as.1).toReal := by
  classical
  rw [ndGeom2EndpointMass, Tao.pmfOuterMass_toReal_eq_tsum_indicator]
  simp only [ndSection7WeightEvent, Set.indicator, Set.mem_setOf_eq]
  let f : List ℕ+ → ℝ := fun as =>
    if Tao.taoTupleWeight as = L then
      (Tao.geom2PNatListPMF n as).toReal
    else 0
  change (∑' as : List ℕ+, f as) = _
  have hsupp : Function.support f ⊆
      {as : List ℕ+ |
        as.length = n ∧ Tao.taoTupleWeight as = L} := by
    intro as has
    by_cases hweight : Tao.taoTupleWeight as = L
    · refine ⟨?_, hweight⟩
      by_contra hlength
      simp [f, hweight,
        Tao.geom2PNatListPMF_apply_eq_zero_of_length_ne n as hlength] at has
    · simp [f, hweight] at has
  calc
    (∑' as : List ℕ+, f as) =
        ∑' as : NDFixedTotalValuations n L, f as.1 :=
      (tsum_subtype_eq_of_support_subset (f := f)
        (s := {as : List ℕ+ |
          as.length = n ∧ Tao.taoTupleWeight as = L}) hsupp).symm
    _ = ∑' as : NDFixedTotalValuations n L,
        (Tao.geom2PNatListPMF n as.1).toReal := by
      apply tsum_congr
      intro as
      simp [f, as.2.2]

/-- Exact negative-binomial endpoint mass in the guarded v10 source regime. -/
theorem ndGeom2EndpointMass_eq_choose_mul_pow
    {n L : ℕ} (hn : 0 < n) (hL : n ≤ L) :
    ndGeom2EndpointMass n L =
      (Nat.choose (L - 1) (n - 1) : ℝ) * (1 / 2 : ℝ) ^ L := by
  rw [ndGeom2EndpointMass_eq_tsum_fixedTotal]
  letI : Fintype (NDFixedTotalValuations n L) :=
    Fintype.ofEquiv (Sym (Fin n) (L - n))
      (ndFiberExtrasEquivFixedTotal n L hL)
  calc
    (∑' as : NDFixedTotalValuations n L,
        (Tao.geom2PNatListPMF n as.1).toReal) =
        ∑' _as : NDFixedTotalValuations n L, (1 / 2 : ℝ) ^ L := by
      apply tsum_congr
      intro as
      have hmass :=
        Tao.geom2PNatListPMF_apply_length_toReal_eq_weight as.1
      rw [as.2.1] at hmass
      rw [hmass, as.2.2]
    _ = (Fintype.card (NDFixedTotalValuations n L) : ℝ) *
        (1 / 2 : ℝ) ^ L := by
      rw [tsum_fintype]
      simp
    _ = (Nat.choose (L - 1) (n - 1) : ℝ) *
        (1 / 2 : ℝ) ^ L := by
      rw [← Nat.card_eq_fintype_card,
        natCard_fixedTotalValuations hn hL]

/-- The endpoint denominator is strictly positive throughout the source
regime `0 < n ≤ L`. -/
theorem ndGeom2EndpointMass_pos
    {n L : ℕ} (hn : 0 < n) (hL : n ≤ L) :
    0 < ndGeom2EndpointMass n L := by
  rw [ndGeom2EndpointMass_eq_choose_mul_pow hn hL]
  exact mul_pos
    (Nat.cast_pos.2 (Nat.choose_pos (by omega)))
    (pow_pos (by norm_num) L)

theorem ndGeom2EndpointMass_ne_zero
    {n L : ℕ} (hn : 0 < n) (hL : n ≤ L) :
    ndGeom2EndpointMass n L ≠ 0 :=
  (ndGeom2EndpointMass_pos hn hL).ne'

theorem ndGeom2EndpointMass_complex_ne_zero
    {n L : ℕ} (hn : 0 < n) (hL : n ≤ L) :
    ((ndGeom2EndpointMass n L : ℝ) : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (ndGeom2EndpointMass_ne_zero hn hL)

/-- Positive endpoint mass supplies the exact event/support witness required
by `PMF.filter`; no ad hoc canonical list is baked into later consumers. -/
theorem ndSection7WeightEvent_exists_mem_support
    {n L : ℕ} (hn : 0 < n) (hL : n ≤ L) :
    ∃ as ∈ ndSection7WeightEvent L,
      as ∈ (Tao.geom2PNatListPMF n).support := by
  have hpos := ndGeom2EndpointMass_pos hn hL
  have hmass :
      (Tao.geom2PNatListPMF n).toOuterMeasure
          (ndSection7WeightEvent L) ≠ 0 := by
    intro hzero
    have : ndGeom2EndpointMass n L = 0 := by
      simp [ndGeom2EndpointMass, hzero]
    exact hpos.ne' this
  have hnotDisjoint :
      ¬ Disjoint (Tao.geom2PNatListPMF n).support
        (ndSection7WeightEvent L) := by
    intro hd
    exact hmass
      ((PMF.toOuterMeasure_apply_eq_zero_iff
        (Tao.geom2PNatListPMF n) (ndSection7WeightEvent L)).2 hd)
  rcases Set.not_disjoint_iff.mp hnotDisjoint with
    ⟨as, hasSupport, hasEvent⟩
  exact ⟨as, hasEvent, hasSupport⟩

/-- Uniform weak-composition law on the finite extras carrier.  The explicit
positive-length hypothesis supplies a local inhabitant without installing a
global `Nonempty` instance for symmetric powers of `Fin n`. -/
noncomputable def ndFiberExtrasUniformPMF
    (n L : ℕ) (hn : 0 < n) : PMF (Sym (Fin n) (L - n)) := by
  letI : Nonempty (Sym (Fin n) (L - n)) :=
    ⟨Sym.replicate (L - n) (⟨0, hn⟩ : Fin n)⟩
  exact PMF.uniformOfFintype _

theorem ndFiberExtrasUniformPMF_apply_toReal
    (n L : ℕ) (hn : 0 < n) (u : Sym (Fin n) (L - n)) :
    (ndFiberExtrasUniformPMF n L hn u).toReal =
      1 / (Fintype.card (Sym (Fin n) (L - n)) : ℝ) := by
  simp [ndFiberExtrasUniformPMF, one_div]

/-- Conditioned Section 7 offset law, presented as the direct image of the
uniform extras carrier.  Mapping retains collisions and hence their correct
multiplicities. -/
noncomputable def ndSection7FiberPMF
    (n L : ℕ) (hn : 0 < n) (hL : n ≤ L) : PMF (ZMod (3 ^ n)) :=
  (ndFiberExtrasUniformPMF n L hn).map fun u =>
    Tao.taoSection7OffsetZMod n
      ((ndFiberExtrasEquivFixedTotal n L hL u).1)

/-- Unweighted character sum over the fixed-total extras carrier. -/
noncomputable def ndSection7FiberCharacterSum
    (n L : ℕ) (hL : n ≤ L) (xi : ZMod (3 ^ n)) : ℂ :=
  ∑' u : Sym (Fin n) (L - n),
    Tao.taoSection7CharacterTerm n xi
      ((ndFiberExtrasEquivFixedTotal n L hL u).1)

/-- On a fixed-total fiber every Geom(2) atom has the same weight
`(1/2)^L`, so the unnormalized numerator is that weight times the raw finite
character sum. -/
theorem ndSection7FiberNumerator_eq_pow_mul_characterSum
    (n L : ℕ) (hL : n ≤ L) (xi : ZMod (3 ^ n)) :
    ndSection7FiberNumerator n L xi =
      (((1 / 2 : ℝ) ^ L : ℝ) : ℂ) *
        ndSection7FiberCharacterSum n L hL xi := by
  rw [ndSection7FiberNumerator_eq_restrictedCharacterSum]
  let f : List ℕ+ → ℂ := fun as =>
    if Tao.taoTupleWeight as = L then
      ((Tao.geom2PNatListPMF n as).toReal : ℂ) *
        Tao.taoSection7CharacterTerm n xi as
    else 0
  change (∑' as : List ℕ+, f as) = _
  have hsupp : Function.support f ⊆
      {as : List ℕ+ |
        as.length = n ∧ Tao.taoTupleWeight as = L} := by
    intro as has
    by_cases hweight : Tao.taoTupleWeight as = L
    · refine ⟨?_, hweight⟩
      by_contra hlength
      simp [f, hweight,
        Tao.geom2PNatListPMF_apply_eq_zero_of_length_ne n as hlength] at has
    · simp [f, hweight] at has
  calc
    (∑' as : List ℕ+, f as) =
        ∑' as : NDFixedTotalValuations n L, f as.1 :=
      (tsum_subtype_eq_of_support_subset (f := f)
        (s := {as : List ℕ+ |
          as.length = n ∧ Tao.taoTupleWeight as = L}) hsupp).symm
    _ = ∑' as : NDFixedTotalValuations n L,
        (((1 / 2 : ℝ) ^ L : ℝ) : ℂ) *
          Tao.taoSection7CharacterTerm n xi as.1 := by
      apply tsum_congr
      intro as
      have hmass :=
        Tao.geom2PNatListPMF_apply_length_toReal_eq_weight as.1
      rw [as.2.1] at hmass
      simp [f, as.2.2, hmass]
    _ = ∑' u : Sym (Fin n) (L - n),
        (((1 / 2 : ℝ) ^ L : ℝ) : ℂ) *
          Tao.taoSection7CharacterTerm n xi
            ((ndFiberExtrasEquivFixedTotal n L hL u).1) := by
      exact ((ndFiberExtrasEquivFixedTotal n L hL).tsum_eq
        (fun as : NDFixedTotalValuations n L =>
          (((1 / 2 : ℝ) ^ L : ℝ) : ℂ) *
            Tao.taoSection7CharacterTerm n xi as.1)).symm
    _ = (((1 / 2 : ℝ) ^ L : ℝ) : ℂ) *
        ndSection7FiberCharacterSum n L hL xi := by
      rw [ndSection7FiberCharacterSum, tsum_mul_left]

/-- Multiplying the conditioned DFT by the carrier cardinality removes its
uniform normalization and recovers the raw fixed-fiber character sum. -/
theorem card_mul_dft_ndSection7FiberPMF_eq_characterSum
    (n L : ℕ) (hn : 0 < n) (hL : n ≤ L)
    (xi : ZMod (3 ^ n)) :
    ((Fintype.card (Sym (Fin n) (L - n)) : ℝ) : ℂ) *
        ZMod.dft (Tao.pmfComplexMass
          (ndSection7FiberPMF n L hn hL)) xi =
      ndSection7FiberCharacterSum n L hL xi := by
  letI : Nonempty (Sym (Fin n) (L - n)) :=
    ⟨Sym.replicate (L - n) (⟨0, hn⟩ : Fin n)⟩
  rw [ndSection7FiberPMF,
    Tao.tao_dft_pmfComplexMass_map_apply]
  unfold ndSection7FiberCharacterSum
  rw [tsum_fintype, tsum_fintype, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _hu
  rw [ndFiberExtrasUniformPMF_apply_toReal]
  rw [Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_natCast]
  have hcard :
      (Fintype.card (Sym (Fin n) (L - n)) : ℂ) ≠ 0 := by
    exact_mod_cast (Fintype.card_ne_zero :
      Fintype.card (Sym (Fin n) (L - n)) ≠ 0)
  field_simp [hcard]
  rfl

/-- Division-free conditioning identity: endpoint mass times the conditioned
DFT is exactly the checked unnormalized fixed-fiber numerator. -/
theorem ndGeom2EndpointMass_mul_fiberDFT
    (n L : ℕ) (hn : 0 < n) (hL : n ≤ L)
    (xi : ZMod (3 ^ n)) :
    (ndGeom2EndpointMass n L : ℂ) *
        ZMod.dft (Tao.pmfComplexMass
          (ndSection7FiberPMF n L hn hL)) xi =
      ndSection7FiberNumerator n L xi := by
  calc
    (ndGeom2EndpointMass n L : ℂ) *
          ZMod.dft (Tao.pmfComplexMass
            (ndSection7FiberPMF n L hn hL)) xi =
        (((1 / 2 : ℝ) ^ L : ℝ) : ℂ) *
          (((Fintype.card (Sym (Fin n) (L - n)) : ℝ) : ℂ) *
            ZMod.dft (Tao.pmfComplexMass
              (ndSection7FiberPMF n L hn hL)) xi) := by
      rw [ndGeom2EndpointMass_eq_choose_mul_pow hn hL,
        card_ndFiberExtras n L hn hL]
      push_cast
      ring
    _ = (((1 / 2 : ℝ) ^ L : ℝ) : ℂ) *
        ndSection7FiberCharacterSum n L hL xi := by
      rw [card_mul_dft_ndSection7FiberPMF_eq_characterSum]
    _ = ndSection7FiberNumerator n L xi :=
      (ndSection7FiberNumerator_eq_pow_mul_characterSum
        n L hL xi).symm

/-- Quotient form of the conditioning identity, justified by the explicit
positive endpoint denominator. -/
theorem dft_ndSection7FiberPMF_eq_fiberNumerator_div_endpointMass
    (n L : ℕ) (hn : 0 < n) (hL : n ≤ L)
    (xi : ZMod (3 ^ n)) :
    ZMod.dft (Tao.pmfComplexMass
        (ndSection7FiberPMF n L hn hL)) xi =
      ndSection7FiberNumerator n L xi /
        (ndGeom2EndpointMass n L : ℂ) := by
  apply (eq_div_iff
    (ndGeom2EndpointMass_complex_ne_zero hn hL)).2
  rw [mul_comm]
  exact ndGeom2EndpointMass_mul_fiberDFT n L hn hL xi

/-- The committed actual-`Q` numerator estimate in its conditioned,
mass-weighted form.  Positivity is visible, while division is intentionally
deferred to the later endpoint-floor step. -/
theorem ndGeom2EndpointMass_mul_norm_fiberDFT_le_holdExpectation_sourceActualQ
    (n L : ℕ) (hn : 0 < n) (hL : n ≤ L)
    (xi : ZMod (3 ^ n)) {epsilon : ℝ}
    (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1) :
    ndGeom2EndpointMass n L *
        ‖ZMod.dft (Tao.pmfComplexMass
          (ndSection7FiberPMF n L hn hL)) xi‖ ≤
      Tao.taoSection7HoldExpectationFull
        (Tao.taoSection7SourceActualQ n xi epsilon) := by
  have hnum :=
    norm_ndSection7FiberNumerator_le_holdExpectation_sourceActualQ
      n L xi hepsilon0 hepsilon1
  rw [← ndGeom2EndpointMass_mul_fiberDFT n L hn hL xi,
    norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (ndGeom2EndpointMass_pos hn hL).le] at hnum
  exact hnum

/-- Normalized fixed-fiber DFT estimate before the endpoint floor is inserted. -/
theorem norm_dft_ndSection7FiberPMF_le_holdExpectation_div_endpointMass
    (n L : ℕ) (hn : 0 < n) (hL : n ≤ L)
    (xi : ZMod (3 ^ n)) {epsilon : ℝ}
    (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1) :
    ‖ZMod.dft (Tao.pmfComplexMass
        (ndSection7FiberPMF n L hn hL)) xi‖ ≤
      Tao.taoSection7HoldExpectationFull
          (Tao.taoSection7SourceActualQ n xi epsilon) /
        ndGeom2EndpointMass n L := by
  exact (le_div_iff₀ (ndGeom2EndpointMass_pos hn hL)).2
    (by simpa [mul_comm] using
      (ndGeom2EndpointMass_mul_norm_fiberDFT_le_holdExpectation_sourceActualQ
        n L hn hL xi hepsilon0 hepsilon1))

end ND
end Erdos1135
