import Erdos1135.ND.Fourier.FixedTotalRatioNormalization

/-!
# Fixed-Total Weighted Reconstruction

This leaf reconstructs one endpoint-weighted conditioned-fiber expectation
as the raw multiplicity-preserving fixed-total tuple sum.  The tuple side is
in affine orientation; the conditioned PMF side is the checked chronological
Section-7 law, connected only through the distributional reversal seam.
-/

namespace Erdos1135
namespace ND

open Tao

noncomputable section

private theorem nd_pmf_map_realWeightedSum_eq_tsum
    {α β : Type*} [Fintype β]
    (p : PMF α) (f : α → β) (w : β → ℝ) :
    (∑ b : β, ((p.map f) b).toReal * w b) =
      ∑' a : α, (p a).toReal * w (f a) := by
  classical
  have hsummable : ∀ b : β, Summable fun a : α =>
      (if b = f a then (p a).toReal else 0) * w b := by
    intro b
    have hindicator : Summable fun a : α =>
        if b = f a then (p a).toReal else 0 :=
      Summable.of_nonneg_of_le
        (fun a => by
          by_cases h : b = f a <;> simp [h, ENNReal.toReal_nonneg])
        (fun a => by
          by_cases h : b = f a <;> simp [h, ENNReal.toReal_nonneg])
        (Tao.taoPMF_summable_toReal p)
    exact hindicator.mul_right (w b)
  calc
    (∑ b : β, ((p.map f) b).toReal * w b) =
        ∑ b : β,
          (∑' a : α, if b = f a then (p a).toReal else 0) * w b := by
      apply Finset.sum_congr rfl
      intro b _hb
      rw [Tao.taoPMF_map_apply_toReal_tsum]
    _ = ∑ b : β, ∑' a : α,
          (if b = f a then (p a).toReal else 0) * w b := by
      apply Finset.sum_congr rfl
      intro b _hb
      rw [tsum_mul_right]
    _ = ∑' a : α, ∑ b : β,
          (if b = f a then (p a).toReal else 0) * w b := by
      simpa using
        (Summable.tsum_finsetSum (s := (Finset.univ : Finset β))
          (f := fun b a =>
            (if b = f a then (p a).toReal else 0) * w b)
          (fun b _hb => hsummable b)).symm
    _ = ∑' a : α, (p a).toReal * w (f a) := by
      apply tsum_congr
      intro a
      rw [Finset.sum_eq_single_of_mem (f a) (Finset.mem_univ (f a))]
      · simp
      · intro b _hb hne
        simp [hne]

private theorem sum_gatedSubmass_mul_eq_tsum
    {α β : Type*} [Fintype β] (p : PMF α)
    (G : α → Prop) [DecidablePred G]
    (f : α → β) (w : β → ℝ) :
    (∑ b : β, Tao.taoGatedSubmass p G f b * w b) =
      ∑' a : α, if G a then (p a).toReal * w (f a) else 0 := by
  classical
  let key : α → Option β := Tao.taoGatedOptionKey G f
  let wOption : Option β → ℝ
    | none => 0
    | some b => w b
  have h := nd_pmf_map_realWeightedSum_eq_tsum p key wOption
  change (∑ b : β, ((p.map key) (some b)).toReal * w b) = _
  calc
    (∑ b : β, ((p.map key) (some b)).toReal * w b) =
        ∑' a : α, (p a).toReal * wOption (key a) := by
      simpa only [Fintype.sum_option, wOption, mul_zero, zero_add] using h
    _ = ∑' a : α, if G a then (p a).toReal * w (f a) else 0 := by
      apply tsum_congr
      intro a
      by_cases hG : G a <;>
        simp [key, wOption, Tao.taoGatedOptionKey, hG]

/-- One fixed-total affine tuple sum is exactly one parent endpoint mass
times the corresponding conditioned Section-7 fiber expectation.  Tuple
multiplicity is retained, and the endpoint factor occurs exactly once. -/
theorem ndFixedTotalAffineExpectation_eq_endpoint_mul_fiberExpectation
    {n L : ℕ} (hn : 0 < n) (hL : n ≤ L)
    (c : ZMod (3 ^ n) → ℝ) :
    (∑' a : NDFixedTotalValuations n L,
        Tao.geom2PNatListMass a.1 *
          c (Tao.taoAffineOffsetZMod n a.1)) =
      ndGeom2EndpointMass n L *
        Tao.pmfExpectation (ndSection7FiberPMF n L hn hL) c := by
  classical
  let p : PMF (List ℕ+) := Tao.geom2PNatListPMF n
  let gate : List ℕ+ → Prop := fun as => Tao.taoTupleWeight as = L
  let affine : List ℕ+ → ZMod (3 ^ n) :=
    Tao.taoAffineOffsetZMod n
  let f : List ℕ+ → ℝ := fun as =>
    if gate as then (p as).toReal * c (affine as) else 0
  have hgate :
      (∑ y : ZMod (3 ^ n),
          Tao.taoGatedSubmass p gate affine y * c y) =
        ∑' as : List ℕ+, f as := by
    simpa only [f] using
      sum_gatedSubmass_mul_eq_tsum p gate affine c
  have hsupp : Function.support f ⊆
      {as : List ℕ+ |
        as.length = n ∧ Tao.taoTupleWeight as = L} := by
    intro as has
    by_cases hweight : Tao.taoTupleWeight as = L
    · refine ⟨?_, hweight⟩
      by_contra hlength
      simp [f, gate, p, hweight,
        Tao.geom2PNatListPMF_apply_eq_zero_of_length_ne n as hlength]
        at has
    · simp [f, gate, hweight] at has
  have hrestrict :
      (∑' as : List ℕ+, f as) =
        ∑' a : NDFixedTotalValuations n L,
          Tao.geom2PNatListMass a.1 *
            c (Tao.taoAffineOffsetZMod n a.1) := by
    calc
      (∑' as : List ℕ+, f as) =
          ∑' a : NDFixedTotalValuations n L, f a.1 :=
        (tsum_subtype_eq_of_support_subset (f := f)
          (s := {as : List ℕ+ |
            as.length = n ∧ Tao.taoTupleWeight as = L}) hsupp).symm
      _ = ∑' a : NDFixedTotalValuations n L,
          Tao.geom2PNatListMass a.1 *
            c (Tao.taoAffineOffsetZMod n a.1) := by
        apply tsum_congr
        intro a
        have hmass := Tao.geom2PNatListPMF_apply_length_toReal a.1
        rw [a.2.1] at hmass
        simp [f, gate, p, affine, a.2.2, hmass]
  rw [← hrestrict, ← hgate]
  unfold Tao.pmfExpectation
  calc
    (∑ y : ZMod (3 ^ n),
        Tao.taoGatedSubmass p gate affine y * c y) =
        ∑ y : ZMod (3 ^ n),
          (ndGeom2EndpointMass n L *
            (ndSection7FiberPMF n L hn hL y).toReal) * c y := by
      apply Finset.sum_congr rfl
      intro y _hy
      rw [← ndAffineFixedTotalSubmass_eq_endpointMass_mul_fiberPMF
        hn hL y]
    _ = ndGeom2EndpointMass n L *
        ∑ y : ZMod (3 ^ n),
          (ndSection7FiberPMF n L hn hL y).toReal * c y := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro y _hy
      ring

/-- The same reconstruction in the countable weighted-expectation notation
used by the likelihood-ratio leaf. -/
theorem ndFixedTotalAffineExpectation_eq_endpoint_mul_weightedExpectation
    {n L : ℕ} (hn : 0 < n) (hL : n ≤ L)
    (c : ZMod (3 ^ n) → ℝ) :
    (∑' a : NDFixedTotalValuations n L,
        Tao.geom2PNatListMass a.1 *
          c (Tao.taoAffineOffsetZMod n a.1)) =
      ndGeom2EndpointMass n L *
        ndPMFWeightedExpectation (ndSection7FiberPMF n L hn hL) c := by
  rw [ndFixedTotalAffineExpectation_eq_endpoint_mul_fiberExpectation
    hn hL c]
  unfold Tao.pmfExpectation ndPMFWeightedExpectation
  rw [tsum_fintype]

/-! The following private checks pin the two normalization hazards at the
smallest useful parameters: a missing or repeated endpoint factor, and loss
of tuple multiplicity under a residue collision. -/

private theorem nd_fixedTotal_2_3_const_canary (k : ℝ) :
    (∑' a : NDFixedTotalValuations 2 3,
        Tao.geom2PNatListMass a.1 * k) = (1 / 4 : ℝ) * k := by
  calc
    _ = ndGeom2EndpointMass 2 3 *
        Tao.pmfExpectation
          (ndSection7FiberPMF 2 3 (by omega) (by omega))
          (fun _ : ZMod (3 ^ 2) => k) :=
      ndFixedTotalAffineExpectation_eq_endpoint_mul_fiberExpectation
        (n := 2) (L := 3) (by omega) (by omega) _
    _ = (1 / 4 : ℝ) * k := by
      rw [ndGeom2EndpointMass_eq_choose_mul_pow
        (n := 2) (L := 3) (by omega) (by omega)]
      unfold Tao.pmfExpectation
      rw [← Finset.sum_mul, Tao.pmf_sum_toReal]
      norm_num

private example :
    (∑' a : NDFixedTotalValuations 2 3,
        Tao.geom2PNatListMass a.1 * (1 : ℝ)) = 1 / 4 := by
  simpa using nd_fixedTotal_2_3_const_canary (1 : ℝ)

private example :
    (∑' a : NDFixedTotalValuations 2 3,
        Tao.geom2PNatListMass a.1 * (9 : ℝ)) = 9 / 4 := by
  rw [nd_fixedTotal_2_3_const_canary]
  norm_num

private def ndFixedTotalCollisionA : NDFixedTotalValuations 3 7 :=
  ⟨[(1 : ℕ+), (3 : ℕ+), (3 : ℕ+)], by
    norm_num [Tao.taoTupleWeight]⟩

private def ndFixedTotalCollisionB : NDFixedTotalValuations 3 7 :=
  ⟨[(2 : ℕ+), (4 : ℕ+), (1 : ℕ+)], by
    norm_num [Tao.taoTupleWeight]⟩

private theorem ndFixedTotalCollisionA_ne_B :
    ndFixedTotalCollisionA ≠ ndFixedTotalCollisionB := by
  intro h
  have hv := congrArg
    (fun a : NDFixedTotalValuations 3 7 => a.1) h
  norm_num [ndFixedTotalCollisionA, ndFixedTotalCollisionB] at hv

private theorem ndFixedTotalCollisionA_offset :
    Tao.taoAffineOffsetZMod 3 ndFixedTotalCollisionA.1 =
      (11 : ZMod (3 ^ 3)) := by
  symm
  apply (Tao.taoAffineOffsetZMod_eq_iff_cleared
    3 ndFixedTotalCollisionA.1 11).2
  change (1408 : ZMod 27) = 31
  decide

private theorem ndFixedTotalCollisionB_offset :
    Tao.taoAffineOffsetZMod 3 ndFixedTotalCollisionB.1 =
      (11 : ZMod (3 ^ 3)) := by
  symm
  apply (Tao.taoAffineOffsetZMod_eq_iff_cleared
    3 ndFixedTotalCollisionB.1 11).2
  change (1408 : ZMod 27) = 85
  decide

private theorem nd_fixedTotal_3_7_collision_canary :
    ndFixedTotalCollisionA ≠ ndFixedTotalCollisionB ∧
      Tao.taoAffineOffsetZMod 3 ndFixedTotalCollisionA.1 =
        Tao.taoAffineOffsetZMod 3 ndFixedTotalCollisionB.1 := by
  constructor
  · exact ndFixedTotalCollisionA_ne_B
  · rw [ndFixedTotalCollisionA_offset, ndFixedTotalCollisionB_offset]

private theorem nd_fixedTotal_3_7_residue_eleven_iff
    (a : NDFixedTotalValuations 3 7) :
    ((11 : ℕ) : ZMod (3 ^ 3)) =
        Tao.taoAffineOffsetZMod 3 a.1 ↔
      a = ndFixedTotalCollisionA ∨ a = ndFixedTotalCollisionB := by
  rcases a with ⟨as, hlen, hweight⟩
  obtain ⟨aa, bb, cc, rfl⟩ := List.length_eq_three.mp hlen
  rcases aa with ⟨aa, haa⟩
  rcases bb with ⟨bb, hbb⟩
  rcases cc with ⟨cc, hcc⟩
  simp [Tao.taoTupleWeight] at hweight
  have haa_le : aa ≤ 5 := by omega
  have hbb_le : bb ≤ 5 := by omega
  have hcc_le : cc ≤ 5 := by omega
  rw [Tao.taoAffineOffsetZMod_eq_iff_cleared]
  change ((2 ^ (aa + (bb + cc)) * 11 : ℕ) : ZMod 27) =
      (Tao.taoOffsetNum
        [⟨aa, haa⟩, ⟨bb, hbb⟩, ⟨cc, hcc⟩] : ℕ) ↔ _
  rw [hweight]
  interval_cases aa <;> interval_cases bb <;> interval_cases cc <;>
    norm_num [Tao.taoOffsetNum, ndFixedTotalCollisionA,
      ndFixedTotalCollisionB, Subtype.ext_iff] at * <;> decide

private theorem nd_fixedTotal_3_7_residue_eleven_mass_canary :
    (∑' a : NDFixedTotalValuations 3 7,
        Tao.geom2PNatListMass a.1 *
          (if ((11 : ℕ) : ZMod (3 ^ 3)) =
              Tao.taoAffineOffsetZMod 3 a.1 then (1 : ℝ) else 0)) =
      (1 / 64 : ℝ) := by
  letI : Fintype (NDFixedTotalValuations 3 7) :=
    ndFixedTotalValuationsFintypeOfLe 3 7 (by omega)
  rw [tsum_fintype]
  calc
    _ = ∑ a : NDFixedTotalValuations 3 7,
        ((if a = ndFixedTotalCollisionA then (1 / 128 : ℝ) else 0) +
          if a = ndFixedTotalCollisionB then (1 / 128 : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro a _ha
      have hmass :
          Tao.geom2PNatListMass a.1 = (1 / 128 : ℝ) := by
        rw [Tao.geom2PNatListMass_eq_pow, a.2.2]
        norm_num
      rw [hmass]
      by_cases hc : ((11 : ℕ) : ZMod (3 ^ 3)) =
          Tao.taoAffineOffsetZMod 3 a.1
      · rw [if_pos hc]
        rcases (nd_fixedTotal_3_7_residue_eleven_iff a).1 hc with
          rfl | rfl
        · simp [ndFixedTotalCollisionA_ne_B]
        · have hBA :
              ndFixedTotalCollisionB ≠ ndFixedTotalCollisionA :=
            Ne.symm ndFixedTotalCollisionA_ne_B
          simp [hBA]
      · rw [if_neg hc]
        have hneA : a ≠ ndFixedTotalCollisionA := by
          intro h
          apply hc
          exact (nd_fixedTotal_3_7_residue_eleven_iff a).2 (Or.inl h)
        have hneB : a ≠ ndFixedTotalCollisionB := by
          intro h
          apply hc
          exact (nd_fixedTotal_3_7_residue_eleven_iff a).2 (Or.inr h)
        simp [hneA, hneB]
    _ = 1 / 64 := by
      rw [Finset.sum_add_distrib]
      simp
      norm_num

end

end ND
end Erdos1135
