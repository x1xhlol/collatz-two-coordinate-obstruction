import FirstPassageExpectationTransport
import OddTargetFirstPassageTransport
import NativeSyracusePrefix
import Erdos1135.Tao.Syracuse.RealFirstPassage

set_option autoImplicit false

namespace CollatzCanonical.NativeTao

open Erdos1135 CollatzCylinderPacking CollatzCylinderPacking.Arithmetic

theorem step_eq_native (q : ℕ) : step q = Terras.accelerated q := by
  simp only [step, Terras.accelerated, Nat.even_iff]

theorem iterate_eq_native (A q : ℕ) : iterate A q = (Terras.accelerated^[A]) q := by
  induction A with
  | zero => rfl
  | succ A ih =>
    rw [iterate, step_eq_native, ih, Function.iterate_succ_apply']

theorem syracuse_shortcut_landing (n q : ℕ) (hq : Odd q) :
    iterate (Tao.taoTupleWeight (Tao.syracuseValuationPNatList n q hq)) q =
      (Tao.syracuse^[n]) q := by
  rw [iterate_eq_native]
  exact Tao.accelerated_iterate_taoTupleWeight_syracuseValuationPNatList n q hq

theorem native_natural_first_passage_is_oddBarrier {B q n : ℕ} (hq : Odd q)
    (hfirst : Tao.syracuseFirstHitAtMost B q n) :
    OddBarrierPassage q (Tao.taoTupleWeight (Tao.syracuseValuationPNatList n q hq)) B := by
  refine ⟨?_, ?_, ?_⟩
  · rw [syracuse_shortcut_landing]
    exact Nat.odd_iff.mp (Tao.syracuse_iterate_odd n q hq)
  · rw [syracuse_shortcut_landing]
    exact_mod_cast hfirst.1
  · intro i hi ho
    rw [iterate_eq_native] at ho ⊢
    exact_mod_cast first_passage_shortcut_odd_sources_above hq hfirst i hi (Nat.odd_iff.mpr ho)

theorem native_real_first_passage_is_oddBarrier {M : ℝ} {q n : ℕ} (hM : 0 ≤ M)
    (hq : Odd q) (hfirst : Tao.syracuseFirstHitAtMostReal M q n) :
    OddBarrierPassage q (Tao.taoTupleWeight (Tao.syracuseValuationPNatList n q hq)) M := by
  have hn := (Tao.syracuseFirstHitAtMostReal_iff_floor hM).mp hfirst
  refine ⟨?_, ?_, ?_⟩
  · rw [syracuse_shortcut_landing]
    exact Nat.odd_iff.mp (Tao.syracuse_iterate_odd n q hq)
  · rw [syracuse_shortcut_landing]
    exact hfirst.1
  · intro i hi ho
    rw [iterate_eq_native] at ho ⊢
    exact (Tao.floor_lt_nat_iff_real_lt hM).mp
      (first_passage_shortcut_odd_sources_above hq hn i hi (Nat.odd_iff.mpr ho))

/-- The actual native real-threshold passage supplies the deterministic
certificate used by the arbitrary-target weighted-observable transport. -/
theorem native_real_first_passage_goodLanding {M : ℝ} {q n N : ℕ} (hM : 0 ≤ M)
    (hq : Odd q) (hfirst : Tao.syracuseFirstHitAtMostReal M q n)
    (hland : N < (Tao.syracuse^[n]) q) :
    GoodOddBarrierLanding q ((Tao.syracuse^[n]) q) N M := by
  refine ⟨Tao.taoTupleWeight (Tao.syracuseValuationPNatList n q hq),
    native_real_first_passage_is_oddBarrier hM hq hfirst,
    syracuse_shortcut_landing n q hq, hland⟩

theorem native_real_first_passage_successfulLanding {M : ℝ} {q n : ℕ} (hM : 0 ≤ M)
    (hq : Odd q) (hfirst : Tao.syracuseFirstHitAtMostReal M q n) :
    SuccessfulOddBarrierLanding q ((Tao.syracuse^[n]) q) M := by
  exact ⟨Tao.taoTupleWeight (Tao.syracuseValuationPNatList n q hq),
    native_real_first_passage_is_oddBarrier hM hq hfirst,
    syracuse_shortcut_landing n q hq⟩

#print axioms iterate_eq_native
#print axioms native_real_first_passage_is_oddBarrier
#print axioms native_real_first_passage_goodLanding

end CollatzCanonical.NativeTao
