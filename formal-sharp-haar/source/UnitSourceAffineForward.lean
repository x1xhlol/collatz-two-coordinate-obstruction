import UnitSourceNativeLawComparison

/-!
# Literal affine law and forward recursion

The fixed-seed finite law from the frozen mixing packet commutes with
modulus projection and obeys the native affine Syracuse transition. At
conductor j+1 after j steps, its seed depends only on its residue modulo
three. All statements retain the actual geometric-list PMF.
-/

set_option autoImplicit false

namespace Erdos1135.Tao

/-- Fixed step count and seed commute with every modulus projection. -/
theorem unitSourceAffinePMF_project
    {r N : ℕ} (hrN : r ≤ N) (k : ℕ) (z : ZMod (3 ^ N)) :
    (unitSourceAffinePMF N k z).map (taoZModThreeProjection hrN) =
      unitSourceAffinePMF r k (taoZModThreeProjection hrN z) := by
  unfold unitSourceAffinePMF
  rw [PMF.map_comp]
  apply congrArg (fun f => (geom2PNatListPMF k).map f)
  funext as
  exact unitSourceAffineOffset_projection hrN k z as

theorem unitSourceAffineOffset_cons
    (N k : ℕ) (z : ZMod (3 ^ N)) (a : ℕ+) (as : List ℕ+) :
    unitSourceAffineOffset N (k + 1) z (a :: as) =
      (((2 : ZMod (3 ^ N)) ^ (a : ℕ))⁻¹) *
        (1 + 3 * unitSourceAffineOffset N k z as) := by
  have h := unitSourceAffineOffset_append N 1 k z [a] as rfl
  have hp : taoSection7OffsetPrefix N 1 [a] =
      (((2 : ZMod (3 ^ N)) ^ (a : ℕ))⁻¹) := by
    simp [taoSection7OffsetPrefix, taoSection7OffsetSummand, taoTupleWeight]
  have hw : taoTupleWeight [a] = (a : ℕ) := by rfl
  simp only [List.singleton_append, Nat.add_comm 1 k, hp, hw, pow_one] at h
  exact h.trans (by ring)

theorem unitSourceAffineOneStep_eq_syracStep
    (N : ℕ) (a : ℕ+) (y : ZMod (3 ^ (N + 1))) :
    (((2 : ZMod (3 ^ (N + 1))) ^ (a : ℕ))⁻¹) * (1 + 3 * y) =
      syracStep N (taoZModThreeProjection (Nat.le_succ N) y) a := by
  have h := taoSection6_three_pow_mul_val_eq_three_pow_mul_of_projection_eq
    N 1 y (taoZModThreeProjection (Nat.le_succ N) y) rfl
  simp only [pow_one] at h
  unfold syracStep
  rw [h]
  ring

/-- The literal prefix-ordered affine law obeys the forward native Markov
recursion. Independent geometric head and tail variables are commuted. -/
theorem unitSourceAffinePMF_succ
    (N k : ℕ) (z : ZMod (3 ^ (N + 1))) :
    unitSourceAffinePMF (N + 1) (k + 1) z =
      (unitSourceAffinePMF N k (taoZModThreeProjection (Nat.le_succ N) z)).bind
        (fun y => geom2PNat.map (fun a => syracStep N y a)) := by
  have houter : unitSourceAffinePMF (N + 1) (k + 1) z =
      geom2PNat.bind (fun a =>
        (unitSourceAffinePMF N k (taoZModThreeProjection (Nat.le_succ N) z)).map
          (fun y => syracStep N y a)) := by
    unfold unitSourceAffinePMF
    change (geom2PNat.bind (fun a => (geom2PNatListPMF k).map (fun as => a :: as))).map
      (unitSourceAffineOffset (N + 1) (k + 1) z) = _
    rw [PMF.map_bind]
    apply congrArg (PMF.bind geom2PNat)
    funext a
    rw [PMF.map_comp, PMF.map_comp]
    apply congrArg (fun f => (geom2PNatListPMF k).map f)
    funext as
    simp only [Function.comp_apply]
    rw [unitSourceAffineOffset_cons, unitSourceAffineOneStep_eq_syracStep,
      unitSourceAffineOffset_projection]
  rw [houter]
  simp only [PMF.map]
  exact PMF.bind_comm _ _ _

theorem unitSourceAffinePMF_zero (N : ℕ) (z : ZMod (3 ^ N)) :
    unitSourceAffinePMF N 0 z = PMF.pure z := by
  unfold unitSourceAffinePMF
  change (PMF.pure []).map _ = _
  rw [PMF.pure_map]
  simp [unitSourceAffineOffset,
    taoSection7OffsetPrefix, taoTupleWeight, taoSection7TwoZPow]

/-- At conductor j+1 after j steps, the output depends only on the seed's
first ternary digit. This is a deterministic identity before taking laws. -/
theorem unitSourceAffineOffset_seed_projection
    (j : ℕ) (z : ZMod (3 ^ (j + 1))) (as : List ℕ+) :
    unitSourceAffineOffset (j + 1) j z as =
      unitSourceAffineOffset (j + 1) j
        ((taoZModThreeProjection (by omega : 1 ≤ j + 1) z).val :
          ZMod (3 ^ (j + 1))) as := by
  have h : (3 : ZMod (3 ^ (j + 1))) ^ j *
      ((taoZModThreeProjection (by omega : 1 ≤ j + 1) z).val : ZMod (3 ^ (j + 1))) =
      (3 : ZMod (3 ^ (j + 1))) ^ j * z := by
    let r := taoZModThreeProjection (by omega : 1 ≤ j + 1) z
    have hmod : z.val ≡ r.val [MOD 3] := by
      rw [← ZMod.natCast_eq_natCast_iff]
      have hr : (z.val : ZMod 3) = r :=
        (taoZModThreeProjection_eq_natCast_val (by omega : 1 ≤ j + 1) z).symm
      rw [hr, ZMod.natCast_zmod_val]
    have hscaled : 3 ^ j * z.val ≡ 3 ^ j * r.val [MOD 3 ^ (j + 1)] := by
      simpa [pow_succ] using Nat.ModEq.mul_left' (3 ^ j) hmod
    rw [← ZMod.natCast_zmod_val z]
    simpa [Nat.cast_mul] using
      (ZMod.natCast_eq_natCast_iff (3 ^ j * r.val) (3 ^ j * z.val)
        (3 ^ (j + 1))).mpr hscaled.symm
  unfold unitSourceAffineOffset
  congr 1
  calc
    _ = taoSection7TwoZPow (j + 1) (-(taoTupleWeight as : ℤ)) *
        ((3 : ZMod (3 ^ (j + 1))) ^ j * z) := by ring
    _ = _ := by rw [← h]; ring

theorem unitSourceAffinePMF_seed_projection
    (j : ℕ) (z : ZMod (3 ^ (j + 1))) :
    unitSourceAffinePMF (j + 1) j z =
      unitSourceAffinePMF (j + 1) j
        ((taoZModThreeProjection (by omega : 1 ≤ j + 1) z).val :
          ZMod (3 ^ (j + 1))) := by
  unfold unitSourceAffinePMF
  apply congrArg (fun f => (geom2PNatListPMF j).map f)
  funext as
  exact unitSourceAffineOffset_seed_projection j z as

#print axioms unitSourceAffinePMF_succ
#print axioms unitSourceAffinePMF_seed_projection

end Erdos1135.Tao
