import Erdos1135.Tao.Fourier.Section7SourcePairing

/-! Exact prefix splitting for the native iid raw Pascal list law. -/

set_option autoImplicit false

namespace Erdos1135.Tao

theorem trap_pascalList_zero_of_length_ne (u : ℕ) (bs : List ℕ)
    (hne : bs.length ≠ u) : taoSection7PascalSourceListPMF u bs = 0 := by
  induction u generalizing bs with
  | zero =>
      cases bs with
      | nil => exact (hne rfl).elim
      | cons b bs => simp [taoSection7PascalSourceListPMF, PMF.pure_apply]
  | succ u ih =>
      cases bs with
      | nil => exact taoSection7PascalSourceListPMF_succ_apply_nil u
      | cons b bs =>
          rw [taoSection7PascalSourceListPMF_succ_apply_cons, ih bs (by simpa using hne)]
          exact mul_zero _

theorem trap_pascalList_append (u v : ℕ) :
    taoSection7PascalSourceListPMF (u + v) =
      (taoSection7PascalSourceListPMF u).bind fun bs =>
        (taoSection7PascalSourceListPMF v).map fun cs => bs ++ cs := by
  induction u with
  | zero =>
      simp only [Nat.zero_add, taoSection7PascalSourceListPMF, PMF.pure_bind,
        List.nil_append]
      exact (PMF.map_id _).symm
  | succ u ih =>
      rw [show u + 1 + v = (u + v) + 1 by omega]
      change (taoSection7PascalSourcePMF.bind fun b =>
        (taoSection7PascalSourceListPMF (u + v)).map fun bs => b :: bs) =
        ((taoSection7PascalSourcePMF.bind fun b =>
          (taoSection7PascalSourceListPMF u).map fun bs => b :: bs).bind fun bs =>
            (taoSection7PascalSourceListPMF v).map fun cs => bs ++ cs)
      rw [PMF.bind_bind]
      apply congrArg (fun f : ℕ → PMF (List ℕ) => taoSection7PascalSourcePMF.bind f)
      funext b
      rw [ih, PMF.map_bind, PMF.bind_map]
      apply congrArg (fun f : List ℕ → PMF (List ℕ) =>
        (taoSection7PascalSourceListPMF u).bind f)
      funext bs
      rw [PMF.map_comp]
      rfl

end Erdos1135.Tao

#print axioms Erdos1135.Tao.trap_pascalList_append
