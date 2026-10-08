import TrapPrefixTransport
import Erdos1135.Tao.Fourier.Section7SourceFThreeQFinite

/-! Exact deterministic split of the native source-factor product. -/

set_option autoImplicit false

namespace Erdos1135.Tao

theorem trap_sourceFactor_transport (n u : ℕ) (hu : 2 * u ≤ n)
    (xi : ZMod (3 ^ n)) (j s t b : ℕ) (hj : 0 < j) :
    taoSection7SourceFThreeFactor n xi (u + j) (s + t) b =
      taoSection7SourceFThreeFactor (n - 2 * u)
        (trapPrefixFrequency n u (s : ℤ) xi) j t b := by
  by_cases hb : b = 3
  · rw [taoSection7SourceFThreeFactor, dite_eq_left ⟨hb, by omega⟩,
      taoSection7SourceFThreeFactor, dite_eq_left ⟨hb, hj⟩]
    apply congrArg norm
    simpa only [Int.ofNat_eq_natCast, Nat.cast_add, PNat.mk_coe, add_assoc] using
      trap_prefix_FThree_transport n u hu (s : ℤ) ((t + b : ℕ) : ℤ) xi ⟨j, hj⟩
  · rw [taoSection7SourceFThreeFactor, dite_eq_right (by simp [hb]),
      taoSection7SourceFThreeFactor, dite_eq_right (by simp [hb])]

theorem trap_factorProduct_append (F : ℕ → ℕ → ℕ → ℝ)
    (j s : ℕ) (bs cs : List ℕ) :
    taoSection7FactorProductFrom F j s (bs ++ cs) =
      taoSection7FactorProductFrom F j s bs *
        taoSection7FactorProductFrom F (j + bs.length) (s + bs.sum) cs := by
  induction bs generalizing j s with
  | nil => simp [taoSection7FactorProductFrom]
  | cons b bs ih =>
      simp only [List.cons_append, taoSection7FactorProductFrom, ih,
        List.length_cons, List.sum_cons]
      rw [show j + (bs.length + 1) = j + 1 + bs.length by omega,
        show s + (b + bs.sum) = s + b + bs.sum by omega]
      ring

theorem trap_factorProduct_transport (n u : ℕ) (hu : 2 * u ≤ n)
    (xi : ZMod (3 ^ n)) (j s t : ℕ) (hj : 0 < j) (bs : List ℕ) :
    taoSection7FactorProductFrom (taoSection7SourceFThreeFactor n xi)
        (u + j) (s + t) bs =
      taoSection7FactorProductFrom (taoSection7SourceFThreeFactor (n - 2 * u)
        (trapPrefixFrequency n u (s : ℤ) xi)) j t bs := by
  induction bs generalizing j t with
  | nil => rfl
  | cons b bs ih =>
      simp only [taoSection7FactorProductFrom]
      rw [trap_sourceFactor_transport n u hu xi j s t b hj,
        show u + j + 1 = u + (j + 1) by omega,
        show s + t + b = s + (t + b) by omega,
        ih (j + 1) (t + b) (by omega)]

theorem trap_factorProduct_prefix_split (n u : ℕ) (hu : 2 * u ≤ n)
    (xi : ZMod (3 ^ n)) (bs cs : List ℕ) (hlen : bs.length = u) :
    taoSection7FactorProduct (taoSection7SourceFThreeFactor n xi) (bs ++ cs) =
      taoSection7FactorProduct (taoSection7SourceFThreeFactor n xi) bs *
        taoSection7FactorProduct (taoSection7SourceFThreeFactor (n - 2 * u)
          (trapPrefixFrequency n u (bs.sum : ℤ) xi)) cs := by
  unfold taoSection7FactorProduct
  rw [trap_factorProduct_append, hlen, Nat.zero_add,
    show 1 + u = u + 1 by omega]
  exact congrArg (fun x : ℝ =>
    taoSection7FactorProductFrom (taoSection7SourceFThreeFactor n xi) 1 0 bs * x)
    (by simpa only [Nat.add_zero] using
      trap_factorProduct_transport n u hu xi 1 bs.sum 0 (by omega) cs)

end Erdos1135.Tao

#print axioms Erdos1135.Tao.trap_factorProduct_prefix_split
