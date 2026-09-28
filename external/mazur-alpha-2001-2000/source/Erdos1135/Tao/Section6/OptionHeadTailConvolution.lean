import Erdos1135.Tao.Probability.GatedSubmass
import Erdos1135.Tao.Section6.FiniteFourierConvolution

/-!
# Section 6 Option Head-Tail Convolution

This generic finite-cyclic leaf convolves an Option-valued head law with a
normalized tail law.  Rejected head mass remains at `none`; accepted mass is
translated by the independent tail without conditioning or renormalization.
-/

open scoped BigOperators

namespace Erdos1135
namespace Tao

noncomputable section

/-- After a rejected head the output stays rejected.  After an accepted head
at `y`, add an independent normalized tail residue. -/
noncomputable def taoOptionHeadTailKernel
    {N : ℕ} [NeZero N] (tau : PMF (ZMod N)) :
    Option (ZMod N) → PMF (Option (ZMod N))
  | none => PMF.pure none
  | some y => tau.map (fun z => some (y + z))

/-- Full Option-valued head-tail law, retaining all rejected mass at `none`. -/
noncomputable def taoOptionHeadTailPMF
    {N : ℕ} [NeZero N]
    (h : PMF (Option (ZMod N))) (tau : PMF (ZMod N)) :
    PMF (Option (ZMod N)) :=
  h.bind (taoOptionHeadTailKernel tau)

/-- Translating a cyclic PMF by `y` gives atom `x-y` at target `x`. -/
theorem taoOptionHeadTailKernel_apply_some
    {N : ℕ} [NeZero N] (tau : PMF (ZMod N)) (x y : ZMod N) :
    taoOptionHeadTailKernel tau (some y) (some x) = tau (x - y) := by
  unfold taoOptionHeadTailKernel
  rw [PMF.map_apply]
  rw [tsum_eq_single (x - y)]
  · simp
  · intro z hz
    have hne : some x ≠ some (y + z) := by
      intro h
      apply hz
      simpa [eq_sub_iff_add_eq, add_comm] using (Option.some.inj h).symm
    simp [hne]

/-- The accepted ENNReal atom is the raw cyclic convolution of accepted head
atoms with the normalized tail.  The literal orientation is `tau (x-y)`. -/
theorem taoOptionHeadTailPMF_apply_some
    {N : ℕ} [NeZero N]
    (h : PMF (Option (ZMod N))) (tau : PMF (ZMod N)) (x : ZMod N) :
    taoOptionHeadTailPMF h tau (some x) =
      ∑ y : ZMod N, h (some y) * tau (x - y) := by
  unfold taoOptionHeadTailPMF
  rw [PMF.bind_apply, tsum_fintype, Fintype.sum_option]
  have hnone :
      (PMF.pure none : PMF (Option (ZMod N))) (some x) = 0 := by
    simp
  rw [show taoOptionHeadTailKernel tau none = PMF.pure none by rfl]
  rw [hnone, mul_zero, zero_add]
  apply Finset.sum_congr rfl
  intro y _hy
  rw [taoOptionHeadTailKernel_apply_some]

/-- Tail evolution never changes the rejected atom. -/
theorem taoOptionHeadTailPMF_apply_none
    {N : ℕ} [NeZero N]
    (h : PMF (Option (ZMod N))) (tau : PMF (ZMod N)) :
    taoOptionHeadTailPMF h tau none = h none := by
  unfold taoOptionHeadTailPMF
  rw [PMF.bind_apply, tsum_fintype, Fintype.sum_option]
  simp [taoOptionHeadTailKernel, PMF.map_apply]

/-- Real accepted atoms are the finite sum of the real head and tail atoms. -/
theorem taoOptionHeadTailPMF_apply_some_toReal
    {N : ℕ} [NeZero N]
    (h : PMF (Option (ZMod N))) (tau : PMF (ZMod N)) (x : ZMod N) :
    (taoOptionHeadTailPMF h tau (some x)).toReal =
      ∑ y : ZMod N, (h (some y)).toReal * (tau (x - y)).toReal := by
  rw [taoOptionHeadTailPMF_apply_some]
  rw [ENNReal.toReal_sum]
  · simp only [ENNReal.toReal_mul]
  · intro y _hy
    exact ENNReal.mul_ne_top (h.apply_ne_top (some y))
      (tau.apply_ne_top (x - y))

/-- The accepted real atom is exactly the existing raw cyclic convolution. -/
theorem taoOptionHeadTailPMF_apply_some_toReal_eq_rawConvolution
    {N : ℕ} [NeZero N]
    (h : PMF (Option (ZMod N))) (tau : PMF (ZMod N)) (x : ZMod N) :
    (taoOptionHeadTailPMF h tau (some x)).toReal =
      taoZModRawConvolution
        (fun y => (h (some y)).toReal)
        (fun z => (tau z).toReal) x := by
  rw [taoOptionHeadTailPMF_apply_some_toReal]
  rfl

/-- Accepted singleton canary fixing the convolution orientation at `x-y`. -/
theorem taoOptionHeadTailPMF_pure_some_apply_some
    {N : ℕ} [NeZero N] (tau : PMF (ZMod N)) (x y : ZMod N) :
    taoOptionHeadTailPMF (PMF.pure (some y)) tau (some x) =
      tau (x - y) := by
  rw [taoOptionHeadTailPMF_apply_some]
  simp

/-- Rejected singleton canary: no tail mass is applied after rejection. -/
theorem taoOptionHeadTailPMF_pure_none
    {N : ℕ} [NeZero N] (tau : PMF (ZMod N)) :
    taoOptionHeadTailPMF (PMF.pure none) tau = PMF.pure none := by
  apply PMF.ext
  intro x
  cases x with
  | none => rw [taoOptionHeadTailPMF_apply_none]
  | some x => rw [taoOptionHeadTailPMF_apply_some]; simp

/-- A point mass at zero is the identity tail law. -/
theorem taoOptionHeadTailPMF_pure_zero
    {N : ℕ} [NeZero N] (h : PMF (Option (ZMod N))) :
    taoOptionHeadTailPMF h (PMF.pure 0) = h := by
  classical
  apply PMF.ext
  intro x
  cases x with
  | none => rw [taoOptionHeadTailPMF_apply_none]
  | some x =>
      rw [taoOptionHeadTailPMF_apply_some]
      rw [Finset.sum_eq_single x]
      · simp
      · intro y _hy hyx
        simp [sub_eq_zero, Ne.symm hyx]
      · simp

end

end Tao
end Erdos1135
