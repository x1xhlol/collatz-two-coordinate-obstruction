import Erdos1135.ND.Fourier.FixedSplitTailDFT

/-!
# Fixed-Total Conductor Descent

This leaf keeps the exact conductor loss visible on a fixed-total Section-7
fiber.  Dropping the final `j` valuations leaves a mixture over their iid
Geom(2) total; the retained factor is still the unnormalized numerator at
the projected cofactor.

There is no normalized projectivity statement here.  In particular, the
mixture carries one explicit endpoint mass and no hypergeometric weight.
-/

open scoped BigOperators

namespace Erdos1135
namespace ND

open Tao

noncomputable section

@[reducible] private noncomputable def ndFixedTotalValuationsFintypeOfLe
    (n L : ℕ) (hL : n ≤ L) :
    Fintype (NDFixedTotalValuations n L) :=
  Fintype.ofEquiv (Sym (Fin n) (L - n))
    (ndFiberExtrasEquivFixedTotal n L hL)

/-- Multiplying the high-level frequency by `3^j` makes its character depend
only on the first `r` valuations, at the projection of the cofactor.  The
cofactor is projected before multiplication; no primitivity is required. -/
theorem taoSection7CharacterTerm_three_pow_mul_eq_take
    (r j : ℕ) (eta : ZMod (3 ^ (r + j))) (as : List ℕ+) :
    Tao.taoSection7CharacterTerm (r + j)
        ((3 : ZMod (3 ^ (r + j))) ^ j * eta) as =
      Tao.taoSection7CharacterTerm r
        (Tao.taoZModThreeProjection
          (Nat.le_add_right r j) eta) (as.take r) := by
  unfold Tao.taoSection7CharacterTerm
  rw [Tao.taoForwardDFTKernel_three_pow_mul_eq_projection]
  rw [Tao.taoSection7OffsetZMod_projection_eq_take_of_le]

private def ndFixedTotalSplitIndexEquivTailIcc
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

private theorem ndSection7FiberNumerator_eq_pow_mul_fixedTotalTsum
    (n L : ℕ) (hL : n ≤ L) (xi : ZMod (3 ^ n)) :
    ndSection7FiberNumerator n L xi =
      (((1 / 2 : ℝ) ^ L : ℝ) : ℂ) *
        ∑' as : NDFixedTotalValuations n L,
          Tao.taoSection7CharacterTerm n xi as.1 := by
  rw [ndSection7FiberNumerator_eq_pow_mul_characterSum n L hL xi]
  unfold ndSection7FiberCharacterSum
  congr 1
  exact (ndFiberExtrasEquivFixedTotal n L hL).tsum_eq
    (fun as : NDFixedTotalValuations n L =>
      Tao.taoSection7CharacterTerm n xi as.1)

private theorem ndFixedTotalSplitFiber_weightedCharacterSum
    (r j R : ℕ) (s : NDFixedTotalSplitIndex r j R)
    (xi : ZMod (3 ^ r))
    [Fintype (NDFixedTotalValuations r s.headTotal)]
    [Fintype (NDFixedTotalValuations j s.tailTotal)] :
    (((1 / 2 : ℝ) ^ R : ℝ) : ℂ) *
        ∑ p : NDFixedTotalSplitFiber s,
          Tao.taoSection7CharacterTerm r xi p.1.1 =
      (ndGeom2EndpointMass j s.tailTotal : ℂ) *
        ndSection7FiberNumerator r s.headTotal xi := by
  have htailMass :
      ndGeom2EndpointMass j s.tailTotal =
        (Fintype.card
            (NDFixedTotalValuations j s.tailTotal) : ℝ) *
          (1 / 2 : ℝ) ^ s.tailTotal := by
    rw [ndGeom2EndpointMass_eq_tsum_fixedTotal, tsum_fintype]
    calc
      (∑ a : NDFixedTotalValuations j s.tailTotal,
          (Tao.geom2PNatListPMF j a.1).toReal) =
          ∑ _a : NDFixedTotalValuations j s.tailTotal,
            (1 / 2 : ℝ) ^ s.tailTotal := by
        apply Finset.sum_congr rfl
        intro a _ha
        have hmass :=
          Tao.geom2PNatListPMF_apply_length_toReal_eq_weight a.1
        rw [a.2.1] at hmass
        rw [hmass, a.2.2]
      _ = (Fintype.card
            (NDFixedTotalValuations j s.tailTotal) : ℝ) *
          (1 / 2 : ℝ) ^ s.tailTotal := by
        simp
  have hheadNumerator :=
    ndSection7FiberNumerator_eq_pow_mul_fixedTotalTsum
      r s.headTotal s.headLength_le xi
  rw [tsum_fintype] at hheadNumerator
  rw [htailMass, hheadNumerator]
  push_cast
  rw [Fintype.sum_prod_type]
  simp only [Finset.sum_const, nsmul_eq_mul]
  have hpow :
      (1 / 2 : ℂ) ^ R =
        (1 / 2 : ℂ) ^ s.headTotal *
          (1 / 2 : ℂ) ^ s.tailTotal := by
    rw [← pow_add]
    exact congrArg (fun m : ℕ => (1 / 2 : ℂ) ^ m) s.total_eq.symm
  rw [hpow]
  simp only [Fintype.card]
  rw [← Finset.mul_sum]
  ring

/-- Exact raw conductor descent on a fixed-total fiber.  The index `t` is the
total of the dropped suffix, so the retained numerator has total `R - t`.
The single visible coefficient is its iid Geom(2) endpoint mass. -/
theorem ndSection7FiberNumerator_three_pow_mul_eq_droppedTotalSum
    (r j R : ℕ) (hR : r + j ≤ R)
    (eta : ZMod (3 ^ (r + j))) :
    ndSection7FiberNumerator (r + j) R
        ((3 : ZMod (3 ^ (r + j))) ^ j * eta) =
      ∑ t ∈ Finset.Icc j (R - r),
        (ndGeom2EndpointMass j t : ℂ) *
          ndSection7FiberNumerator r (R - t)
            (Tao.taoZModThreeProjection
              (Nat.le_add_right r j) eta) := by
  classical
  let xi : ZMod (3 ^ r) :=
    Tao.taoZModThreeProjection (Nat.le_add_right r j) eta
  letI : Fintype (NDFixedTotalValuations (r + j) R) :=
    ndFixedTotalValuationsFintypeOfLe (r + j) R hR
  have hrR : r ≤ R := by omega
  letI : Fintype (NDFixedTotalSplitIndex r j R) :=
    Fintype.ofEquiv {u : ℕ // u ∈ Finset.Icc j (R - r)}
      (ndFixedTotalSplitIndexEquivTailIcc r j R hrR).symm
  letI _ (s : NDFixedTotalSplitIndex r j R) :
      Fintype (NDFixedTotalValuations r s.headTotal) :=
    ndFixedTotalValuationsFintypeOfLe r s.headTotal s.headLength_le
  letI _ (s : NDFixedTotalSplitIndex r j R) :
      Fintype (NDFixedTotalValuations j s.tailTotal) :=
    ndFixedTotalValuationsFintypeOfLe j s.tailTotal s.tailLength_le
  rw [ndSection7FiberNumerator_eq_pow_mul_fixedTotalTsum
    (r + j) R hR, tsum_fintype]
  change (((1 / 2 : ℝ) ^ R : ℝ) : ℂ) *
      ∑ as : NDFixedTotalValuations (r + j) R,
        Tao.taoSection7CharacterTerm (r + j)
          ((3 : ZMod (3 ^ (r + j))) ^ j * eta) as.1 = _
  calc
    (((1 / 2 : ℝ) ^ R : ℝ) : ℂ) *
          ∑ as : NDFixedTotalValuations (r + j) R,
            Tao.taoSection7CharacterTerm (r + j)
              ((3 : ZMod (3 ^ (r + j))) ^ j * eta) as.1 =
        (((1 / 2 : ℝ) ^ R : ℝ) : ℂ) *
          ∑ z : NDFixedTotalSplit r j R,
            Tao.taoSection7CharacterTerm (r + j)
              ((3 : ZMod (3 ^ (r + j))) ^ j * eta)
              ((ndFixedTotalValuationsEquivSplit r j R).symm z).1 := by
      congr 1
      exact ((ndFixedTotalValuationsEquivSplit r j R).symm.sum_comp
        (fun as : NDFixedTotalValuations (r + j) R =>
          Tao.taoSection7CharacterTerm (r + j)
            ((3 : ZMod (3 ^ (r + j))) ^ j * eta) as.1)).symm
    _ = (((1 / 2 : ℝ) ^ R : ℝ) : ℂ) *
          ∑ z : NDFixedTotalSplit r j R,
            Tao.taoSection7CharacterTerm r xi z.2.1.1 := by
      congr 1
      apply Finset.sum_congr rfl
      intro z _hz
      rw [ndFixedTotalValuationsEquivSplit_symm_apply_val]
      rw [taoSection7CharacterTerm_three_pow_mul_eq_take]
      change Tao.taoSection7CharacterTerm r xi
          ((z.2.1.1 ++ z.2.2.1).take r) = _
      apply congrArg (Tao.taoSection7CharacterTerm r xi)
      have htake :
          (z.2.1.1 ++ z.2.2.1).take z.2.1.1.length = z.2.1.1 :=
        List.take_append_length
      simpa only [z.2.1.2.1] using htake
    _ = ∑ s : NDFixedTotalSplitIndex r j R,
          (((1 / 2 : ℝ) ^ R : ℝ) : ℂ) *
            ∑ p : NDFixedTotalSplitFiber s,
              Tao.taoSection7CharacterTerm r xi p.1.1 := by
      rw [Fintype.sum_sigma, Finset.mul_sum]
    _ = ∑ s : NDFixedTotalSplitIndex r j R,
          (ndGeom2EndpointMass j s.tailTotal : ℂ) *
            ndSection7FiberNumerator r s.headTotal xi := by
      apply Finset.sum_congr rfl
      intro s _hs
      exact ndFixedTotalSplitFiber_weightedCharacterSum r j R s xi
    _ = ∑ t : {u : ℕ // u ∈ Finset.Icc j (R - r)},
          (ndGeom2EndpointMass j t.1 : ℂ) *
            ndSection7FiberNumerator r (R - t.1) xi := by
      apply Fintype.sum_equiv
        (ndFixedTotalSplitIndexEquivTailIcc r j R hrR)
      intro s
      have hhead : R - s.tailTotal = s.headTotal := by
        have htotal := s.total_eq
        omega
      change (ndGeom2EndpointMass j s.tailTotal : ℂ) *
          ndSection7FiberNumerator r s.headTotal xi =
        (ndGeom2EndpointMass j s.tailTotal : ℂ) *
          ndSection7FiberNumerator r (R - s.tailTotal) xi
      rw [hhead]
    _ = ∑ t ∈ Finset.Icc j (R - r),
          (ndGeom2EndpointMass j t : ℂ) *
            ndSection7FiberNumerator r (R - t) xi := by
      rw [← Finset.attach_eq_univ]
      exact Finset.sum_attach (Finset.Icc j (R - r))
        (fun t => (ndGeom2EndpointMass j t : ℂ) *
          ndSection7FiberNumerator r (R - t) xi)

/-- At zero frequency the unnormalized fixed-fiber character sum is exactly
the real endpoint mass, viewed in `ℂ`. -/
theorem ndSection7FiberNumerator_zero (n L : ℕ) :
    ndSection7FiberNumerator n L 0 =
      (ndGeom2EndpointMass n L : ℂ) := by
  rw [ndSection7FiberNumerator_eq_restrictedCharacterSum]
  rw [ndGeom2EndpointMass_eq_weightSelector, Complex.ofReal_tsum]
  apply tsum_congr
  intro as
  by_cases hweight : Tao.taoTupleWeight as = L
  · simp [hweight, Tao.taoSection7CharacterTerm,
      Tao.taoForwardDFTKernel]
  · simp [hweight]

/-- The length-zero iid list has total zero and no other endpoint. -/
@[simp]
theorem ndGeom2EndpointMass_zero (L : ℕ) :
    ndGeom2EndpointMass 0 L = if L = 0 then 1 else 0 := by
  classical
  rw [ndGeom2EndpointMass_eq_weightSelector]
  by_cases hL : L = 0
  · subst L
    rw [tsum_eq_single ([] : List ℕ+)]
    · simp [Tao.taoTupleWeight,
        Tao.geom2PNatListPMF_zero_apply_nil]
    · intro as has
      cases as with
      | nil => exact False.elim (has rfl)
      | cons a as =>
          simp
  · rw [if_neg hL]
    calc
      (∑' as : List ℕ+,
          if Tao.taoTupleWeight as = L then
            (Tao.geom2PNatListPMF 0 as).toReal
          else 0) =
          ∑' _as : List ℕ+, (0 : ℝ) := by
        apply tsum_congr
        intro as
        cases as with
        | nil =>
            have hL' : 0 ≠ L := fun h => hL h.symm
            simp [Tao.taoTupleWeight, hL']
        | cons a as =>
            rw [Tao.geom2PNatListPMF_zero_apply_cons]
            simp
      _ = 0 := by simp

/-- Zero frequency specializes conductor descent to the exact iid endpoint
convolution.  This is also a regression for the orientation `R - t`. -/
theorem ndGeom2EndpointMass_add_eq_droppedTotalSum
    (r j R : ℕ) (hR : r + j ≤ R) :
    ndGeom2EndpointMass (r + j) R =
      ∑ t ∈ Finset.Icc j (R - r),
        ndGeom2EndpointMass j t *
          ndGeom2EndpointMass r (R - t) := by
  have h :=
    ndSection7FiberNumerator_three_pow_mul_eq_droppedTotalSum
      r j R hR (0 : ZMod (3 ^ (r + j)))
  simp only [mul_zero, ndSection7FiberNumerator_zero,
    map_zero] at h
  exact_mod_cast congrArg Complex.re h

/-- The checked accepted-tail DFT consumes the raw conductor mixture without
renormalizing the defective tail law. -/
theorem dft_ndSection6FixedSplitTailSubmass_eq_droppedTotalSum
    (q r j l R : ℕ) (hR : r + j ≤ R)
    (xi : ZMod (3 ^ ((r + j) + q)))
    (eta : ZMod (3 ^ (r + j)))
    (hxi : Tao.taoSection6TailScaledFrequency
        (Nat.le_add_right (r + j) q) l xi =
      (3 : ZMod (3 ^ (r + j))) ^ j * eta) :
    ZMod.dft (fun z =>
      ((ndSection6FixedSplitTailSubmass q (r + j) l R z : ℝ) : ℂ)) xi =
      ∑ t ∈ Finset.Icc j (R - r),
        (ndGeom2EndpointMass j t : ℂ) *
          ndSection7FiberNumerator r (R - t)
            (Tao.taoZModThreeProjection
              (Nat.le_add_right r j) eta) := by
  rw [dft_ndSection6FixedSplitTailSubmass, hxi]
  exact ndSection7FiberNumerator_three_pow_mul_eq_droppedTotalSum
    r j R hR eta

end

end ND
end Erdos1135
