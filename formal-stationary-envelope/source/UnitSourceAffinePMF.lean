import UnitSourcePairExpectation
import Erdos1135.Tao.Fourier.Section7SourceLaw

/-!
# Literal affine geometric source law

The source is the native list of independent Geom(2) positive exponents.
Its image is the native offset prefix plus the finite-modulus terminal seed.
The even/odd product lemmas adapt the private native `Section7SourceLaw`
proofs to an ambient conductor independent of the list length.
-/

set_option autoImplicit false
open scoped BigOperators

namespace Erdos1135.Tao

private theorem unitSourcePairExpansionFrom_even_eq_product :
    ∀ (m : ℕ) (N : ℕ) (xi : ZMod (3 ^ N))
      (j : ℕ+) (s : ℕ) (as : List ℕ+),
      as.length = 2 * m →
      taoSection7PairExpansionFrom N xi j s as =
        ∏ r ∈ Finset.range m,
          taoSection7PairPhase N xi
            (taoSection7PairX N
              ⟨(j : ℕ) + r, Nat.add_pos_left j.2 r⟩
              (Int.ofNat
                (s + taoTupleWeight (as.take (2 * r + 2)))))
            (as.getD (2 * r + 1) 1) := by
  intro m
  induction m with
  | zero =>
      intro N xi j s as hlen
      cases as with
      | nil => simp [taoSection7PairExpansionFrom]
      | cons a as => simp at hlen
  | succ m ih =>
      intro N xi j s as hlen
      cases as with
      | nil => simp at hlen
      | cons a₁ as =>
          cases as with
          | nil =>
              simp only [List.length_cons, List.length_nil] at hlen
              omega
          | cons a₂ tail =>
              rw [taoSection7PairExpansionFrom, Finset.prod_range_succ']
              conv_lhs => rw [mul_comm]
              apply congrArg₂ (· * ·)
              · have htail : tail.length = 2 * m := by
                  simp only [List.length_cons] at hlen
                  omega
                rw [ih N xi ⟨(j : ℕ) + 1, by omega⟩
                  (s + (a₁ : ℕ) + (a₂ : ℕ)) tail htail]
                apply Finset.prod_congr rfl
                intro r hr
                have hrm : r < m := Finset.mem_range.mp hr
                have hweight :
                    s + (a₁ : ℕ) + (a₂ : ℕ) +
                        taoTupleWeight (tail.take (2 * r + 2)) =
                      s + taoTupleWeight
                        ((a₁ :: a₂ :: tail).take (2 * (r + 1) + 2)) := by
                  rw [show 2 * (r + 1) + 2 = (2 * r + 2) + 2 by omega]
                  simp [taoTupleWeight, List.take, add_assoc]
                have hgetD :
                    tail.getD (2 * r + 1) 1 =
                      (a₁ :: a₂ :: tail).getD (2 * (r + 1) + 1) 1 := by
                  rw [show 2 * (r + 1) + 1 = (2 * r + 1) + 2 by omega]
                  simp [List.getD]
                apply congrArg₂ (taoSection7PairPhase N xi)
                · apply congrArg₂ (taoSection7PairX N)
                  · apply Subtype.ext
                    simp
                    omega
                  · exact congrArg Int.ofNat hweight
                · exact hgetD
              · congr 3; simp [taoTupleWeight, add_assoc]

private theorem unitSourcePairExpansionFrom_odd_eq_product_mul_terminal :
    ∀ (m : ℕ) (N : ℕ) (xi : ZMod (3 ^ N))
      (j : ℕ+) (s : ℕ) (as : List ℕ+),
      as.length = 2 * m + 1 →
      taoSection7PairExpansionFrom N xi j s as =
        (∏ r ∈ Finset.range m,
          taoSection7PairPhase N xi
            (taoSection7PairX N
              ⟨(j : ℕ) + r, Nat.add_pos_left j.2 r⟩
              (Int.ofNat
                (s + taoTupleWeight (as.take (2 * r + 2)))))
            (as.getD (2 * r + 1) 1)) *
          taoForwardDFTKernel
            (taoSection7PairX N
              ⟨(j : ℕ) + m, Nat.add_pos_left j.2 m⟩
              (Int.ofNat (s + taoTupleWeight as))) xi := by
  intro m
  induction m with
  | zero =>
      intro N xi j s as hlen
      cases as with
      | nil => simp at hlen
      | cons a tail =>
          have htail : tail = [] := by
            cases tail with
            | nil => rfl
            | cons b bs => simp at hlen
          subst tail
          have hj : (⟨(j : ℕ) + 0, Nat.add_pos_left j.2 0⟩ : ℕ+) = j := by
            apply Subtype.ext
            rfl
          simp [taoSection7PairExpansionFrom, taoTupleWeight]
          apply congrArg
            (fun x : ZMod (3 ^ N) => taoForwardDFTKernel x xi)
          apply congrArg₂ (taoSection7PairX N)
          · apply Subtype.ext
            rfl
          · rfl
  | succ m ih =>
      intro N xi j s as hlen
      cases as with
      | nil => simp at hlen
      | cons a₁ rest =>
          cases rest with
          | nil => simp at hlen
          | cons a₂ tail =>
              have htail : tail.length = 2 * m + 1 := by
                simp only [List.length_cons] at hlen
                omega
              rw [taoSection7PairExpansionFrom]
              rw [ih N xi ⟨(j : ℕ) + 1, by omega⟩
                (s + (a₁ : ℕ) + (a₂ : ℕ)) tail htail]
              rw [Finset.prod_range_succ']
              have hprod :
                  (∏ r ∈ Finset.range m,
                    taoSection7PairPhase N xi
                      (taoSection7PairX N
                        ⟨((⟨(j : ℕ) + 1, by omega⟩ : ℕ+) : ℕ) + r,
                          by positivity⟩
                        (Int.ofNat
                          (s + (a₁ : ℕ) + (a₂ : ℕ) +
                            taoTupleWeight (tail.take (2 * r + 2)))))
                      (tail.getD (2 * r + 1) 1)) =
                    ∏ r ∈ Finset.range m,
                      taoSection7PairPhase N xi
                        (taoSection7PairX N
                          ⟨(j : ℕ) + (r + 1), by omega⟩
                          (Int.ofNat
                            (s + taoTupleWeight
                              ((a₁ :: a₂ :: tail).take
                                (2 * (r + 1) + 2)))))
                        ((a₁ :: a₂ :: tail).getD
                          (2 * (r + 1) + 1) 1) := by
                apply Finset.prod_congr rfl
                intro r hr
                have hweight :
                    s + (a₁ : ℕ) + (a₂ : ℕ) +
                        taoTupleWeight (tail.take (2 * r + 2)) =
                      s + taoTupleWeight
                        ((a₁ :: a₂ :: tail).take (2 * (r + 1) + 2)) := by
                  rw [show 2 * (r + 1) + 2 = (2 * r + 2) + 2 by omega]
                  simp [taoTupleWeight, List.take, add_assoc]
                have hgetD :
                    tail.getD (2 * r + 1) 1 =
                      (a₁ :: a₂ :: tail).getD (2 * (r + 1) + 1) 1 := by
                  rw [show 2 * (r + 1) + 1 = (2 * r + 1) + 2 by omega]
                  simp [List.getD]
                apply congrArg₂ (taoSection7PairPhase N xi)
                · apply congrArg₂ (taoSection7PairX N)
                  · apply Subtype.ext
                    simp
                    omega
                  · exact congrArg Int.ofNat hweight
                · exact hgetD
              have hterm :
                  taoForwardDFTKernel
                      (taoSection7PairX N
                        ⟨((⟨(j : ℕ) + 1, by omega⟩ : ℕ+) : ℕ) + m,
                          by positivity⟩
                        (Int.ofNat
                          (s + (a₁ : ℕ) + (a₂ : ℕ) +
                            taoTupleWeight tail))) xi =
                    taoForwardDFTKernel
                      (taoSection7PairX N
                        ⟨(j : ℕ) + (m + 1), by omega⟩
                        (Int.ofNat
                          (s + taoTupleWeight (a₁ :: a₂ :: tail)))) xi := by
                apply congrArg
                  (fun x : ZMod (3 ^ N) => taoForwardDFTKernel x xi)
                apply congrArg₂ (taoSection7PairX N)
                · apply Subtype.ext
                  simp
                  omega
                · congr 1
                  simp [taoTupleWeight, add_assoc]
              have hhead :
                  taoSection7PairPhase N xi
                      (taoSection7PairX N j
                        (Int.ofNat (s + (a₁ : ℕ) + (a₂ : ℕ)))) a₂ =
                    taoSection7PairPhase N xi
                      (taoSection7PairX N
                        ⟨(j : ℕ) + 0, Nat.add_pos_left j.2 0⟩
                        (Int.ofNat
                          (s + taoTupleWeight
                            ((a₁ :: a₂ :: tail).take 2))))
                      ((a₁ :: a₂ :: tail).getD 1 1) := by
                congr 3; simp [taoTupleWeight, add_assoc]
              exact
                (congrArg₂ (· * ·) hhead
                  (congrArg₂ (· * ·) hprod hterm)).trans (by ring)

theorem unitSourceOffsetPrefix_kernel_eq_pairExpansion
    (N : ℕ) (xi : ZMod (3 ^ N)) (as : List ℕ+) :
    taoForwardDFTKernel (taoSection7OffsetPrefix N as.length as) xi =
      taoSection7PairExpansionFrom N xi 1 0 as := by
  rcases Nat.even_or_odd' as.length with ⟨m, hlen | hlen⟩
  · rw [hlen, taoSection7OffsetPrefix_even_eq_pairExpansionSum N m as (by omega)]
    unfold taoSection7PairExpansionSum
    rw [taoForwardDFTKernel_sum_eq_prod]
    rw [unitSourcePairExpansionFrom_even_eq_product m N xi 1 0 as hlen]
    apply Finset.prod_congr rfl
    intro r hr
    simp [taoSection7PairExpansionTerm, taoSection7PairPhase,
      taoSection7PairX, Nat.add_comm]
  · have he : taoSection7OffsetPrefix N (2 * m + 1) as =
        taoSection7PairExpansionSum N m as + taoSection7OddTerminalOffset N m as := by
      unfold taoSection7OffsetPrefix
      rw [Finset.sum_range_succ]
      rw [← taoSection7OffsetPrefix, taoSection7OffsetPrefix_even_eq_pairExpansionSum
        N m as (by omega)]
      rw [← taoSection7OddTerminalOffset_eq_summand N m as hlen]
    rw [hlen, he, taoForwardDFTKernel_add]
    unfold taoSection7PairExpansionSum
    rw [taoForwardDFTKernel_sum_eq_prod]
    rw [unitSourcePairExpansionFrom_odd_eq_product_mul_terminal m N xi 1 0 as hlen]
    apply congrArg₂ (· * ·)
    · apply Finset.prod_congr rfl
      intro r hr
      simp [taoSection7PairExpansionTerm, taoSection7PairPhase,
        taoSection7PairX, Nat.add_comm]
    · unfold taoSection7OddTerminalOffset taoSection7PairX
      simp

/-- The literal finite-modulus affine image of a geometric exponent list. -/
noncomputable def unitSourceAffineOffset
    (N k : ℕ) (z : ZMod (3 ^ N)) (as : List ℕ+) : ZMod (3 ^ N) :=
  taoSection7OffsetPrefix N k as +
    (3 : ZMod (3 ^ N)) ^ k *
      taoSection7TwoZPow N (-(taoTupleWeight as : ℤ)) * z

noncomputable def unitSourceAffinePMF
    (N k : ℕ) (z : ZMod (3 ^ N)) : PMF (ZMod (3 ^ N)) :=
  (geom2PNatListPMF k).map (unitSourceAffineOffset N k z)

noncomputable def unitSourceSeedPhase
    (N k : ℕ) (xi z : ZMod (3 ^ N)) : UnitSourceTerminalPhase :=
  ⟨fun s => taoForwardDFTKernel
      ((3 : ZMod (3 ^ N)) ^ k * taoSection7TwoZPow N (-(s : ℤ)) * z) xi,
    fun _ => norm_taoForwardDFTKernel_eq_one _ _⟩

theorem unitSourceAffine_kernel_eq_twistedPairExpansion
    (N k : ℕ) (xi z : ZMod (3 ^ N)) (as : List ℕ+)
    (hlen : as.length = k) :
    taoForwardDFTKernel (unitSourceAffineOffset N k z as) xi =
      unitSourcePairExpansionFrom N xi (unitSourceSeedPhase N k xi z) 1 0 as := by
  rw [unitSourcePairExpansionFrom_eq_original_mul_terminal]
  unfold unitSourceAffineOffset
  rw [taoForwardDFTKernel_add, ← hlen,
    unitSourceOffsetPrefix_kernel_eq_pairExpansion]
  simp [unitSourceSeedPhase]

/-- The Fourier quantity is the actual mapped geometric PMF, not a surrogate
expectation assumed to satisfy the desired estimate. -/
theorem unitSourceAffinePMF_dft_eq_twistedPairExpectation
    (N k : ℕ) (xi z : ZMod (3 ^ N)) :
    ZMod.dft (pmfComplexMass (unitSourceAffinePMF N k z)) xi =
      unitSourcePairExpectation N xi (unitSourceSeedPhase N k xi z) k 1 0 := by
  unfold unitSourceAffinePMF
  rw [tao_dft_pmfComplexMass_map_apply]
  unfold unitSourcePairExpectation
  apply tsum_congr
  intro as
  by_cases hlen : as.length = k
  · rw [unitSourceAffine_kernel_eq_twistedPairExpansion N k xi z as hlen]
    ring
  · rw [geom2PNatListPMF_apply_eq_zero_of_length_ne k as hlen]
    simp

end Erdos1135.Tao
