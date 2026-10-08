import TrapCanonicalEntries
import TrapCanonicalTruncation

/-! Few white points on a shortened path select a prefix of the original full trace. -/

set_option autoImplicit false

namespace Erdos1135.Tao
open TaoSection7Case3SourceStoppingRun.Lemma79TailExpectation

theorem exists_native_black_trap_family_of_shortened_canonical_trace
    (n coverJ J M C K H : ℕ) (xi : ZMod (3 ^ n)) (epsilon V D : ℝ)
    (pointAt : ℕ → TaoSection7Point) (family : Set TaoSection7Triangle) (S : ℤ)
    (hxi : zmodThreePrimitive n xi) (hnJ : 2 * J ≤ n) (hJcover : J ≤ coverJ)
    (hMC : M ≤ C) (hV : 0 ≤ V)
    (hcover : TaoSection7TriangleFamilyCoverBlack
      (taoSection7SourceBlackInDomain n xi epsilon coverJ) family)
    (hdomain : ∀ q < M, ((pointAt q).j : ℕ) ≤ J)
    (hcount : trapSourceWhiteCount n xi epsilon pointAt M ≤ K) (hKM : K < M)
    (hmonoJ : Monotone fun q => ((pointAt q).j : ℕ))
    (hstepJ : ∀ q < M, ((pointAt (q + 1)).j : ℕ) ≤ (pointAt q).j + H)
    (hstepL : ∀ q < M, ((pointAt (q + 1)).l : ℝ) ≤ (pointAt q).l + V)
    (htube : ∀ q < M, |((pointAt q).l : ℝ) - 4 * (((pointAt q).j : ℕ) : ℝ)| ≤ D)
    (hS : |(S : ℝ) - 4 * (J : ℝ)| ≤ D)
    (hendpoint : S ≤ (pointAt M).l) :
    ∃ r : ℕ, ∃ f : NativeBlackTrapFamily epsilon n r,
      (trapTraceBefore M (lemma79BoundedInclusiveTraceSteps pointAt family C)).length = r + 1 ∧
      f.xi = xi ∧
      nativeTrapFamilyError f ≤
        2 * ((r : ℝ) + 1) * D + V * ((K : ℝ) + 1) + 2 * V * ((K : ℝ) + r) ∧
      4 * (J : ℝ) - 4 * ((((pointAt 0).j : ℕ) + H * K : ℕ) : ℝ) -
        2 * D - V * ((K : ℝ) + 1) ≤ nativeTrapFamilySpan f := by
  have htrace := trap_bounded_inclusive_trace_before hMC
    (lemma79BoundedInclusiveTraceSteps_spec pointAt family C)
  have hne := trap_bounded_inclusive_nonempty_of_few_white n coverJ M xi epsilon
    pointAt family _ hcover (fun q hq => (hdomain q hq).trans hJcover)
    (hcount.trans_lt hKM) htrace
  cases hsteps : trapTraceBefore M (lemma79BoundedInclusiveTraceSteps pointAt family C) with
  | nil => exact (hne hsteps).elim
  | cons first rest =>
      rw [hsteps] at htrace
      obtain ⟨f, hfxi, herr, hspan⟩ := exists_native_black_trap_family_of_bounded_trace
        n coverJ J M K H xi epsilon V D pointAt family first rest S
        hxi hnJ hJcover hV hcover hdomain hcount htrace
        hmonoJ hstepJ hstepL htube hS hendpoint
      exact ⟨rest.length, f, rfl, hfxi, herr, hspan⟩

end Erdos1135.Tao

#print axioms Erdos1135.Tao.exists_native_black_trap_family_of_shortened_canonical_trace
