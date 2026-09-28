import Erdos1135.Tao.Fourier.Section7PairFiber
import Mathlib.Data.List.GetD
import Mathlib.Data.List.TakeDrop

/-!
# Section 7 Deterministic Pair Expansion

This leaf groups adjacent offset summands without changing the ambient modulus.
It proves exact even and odd character products before any expectation or norm
estimate is taken.
-/

open scoped BigOperators

namespace Erdos1135
namespace Tao

/-- One adjacent-pair contribution at zero-based pair index `r`. -/
noncomputable def taoSection7PairExpansionTerm
    (N : ℕ) (as : List ℕ+) (r : ℕ) : ZMod (3 ^ N) :=
  let a₂ := as.getD (2 * r + 1) 1
  (((2 : ZMod (3 ^ N)) ^ (a₂ : ℕ) + 3) *
    taoSection7PairX N ⟨r + 1, by omega⟩
      (Int.ofNat (taoTupleWeight (as.take (2 * r + 2)))))

/-- Sum of the first `m` adjacent-pair contributions. -/
noncomputable def taoSection7PairExpansionSum
    (N m : ℕ) (as : List ℕ+) : ZMod (3 ^ N) :=
  ∑ r ∈ Finset.range m, taoSection7PairExpansionTerm N as r

/-- The unpaired final offset summand of an odd valuation list. -/
noncomputable def taoSection7OddTerminalOffset
    (N m : ℕ) (as : List ℕ+) : ZMod (3 ^ N) :=
  (3 : ZMod (3 ^ N)) ^ (2 * m) *
    taoSection7TwoZPow N (-(taoTupleWeight as : ℤ))

theorem taoSection7TwoZPow_neg_nat_eq_inv_pow
    (N k : ℕ) :
    taoSection7TwoZPow N (-(k : ℤ)) =
      (((2 : ZMod (3 ^ N)) ^ k)⁻¹) := by
  unfold taoSection7TwoZPow
  rw [zpow_neg, zpow_natCast]
  rw [← ZMod.inv_coe_unit]
  simp [taoSection7TwoUnit_coe]

theorem taoSection7TwoZPow_neg_add_mul_pow
    (N s a : ℕ) :
    taoSection7TwoZPow N (-((s + a : ℕ) : ℤ)) *
        (2 : ZMod (3 ^ N)) ^ a =
      taoSection7TwoZPow N (-(s : ℤ)) := by
  unfold taoSection7TwoZPow
  rw [← taoSection7TwoUnit_coe N]
  change
    ((taoSection7TwoUnit N ^ (-((s + a : ℕ) : ℤ)) :
        (ZMod (3 ^ N))ˣ) : ZMod (3 ^ N)) *
      ((taoSection7TwoUnit N ^ a : (ZMod (3 ^ N))ˣ) : ZMod (3 ^ N)) =
        ((taoSection7TwoUnit N ^ (-(s : ℤ)) :
          (ZMod (3 ^ N))ˣ) : ZMod (3 ^ N))
  rw [← Units.val_mul]
  congr 1
  rw [← zpow_natCast]
  rw [← zpow_add]
  congr 1
  omega

theorem taoTupleWeight_take_succ_getD
    (as : List ℕ+) (i : ℕ) (hi : i < as.length) :
    taoTupleWeight (as.take (i + 1)) =
      taoTupleWeight (as.take i) + (as.getD i 1 : ℕ+) := by
  rw [List.getD_eq_getElem as (1 : ℕ+) hi]
  have hsum := List.sum_take_succ
    (as.map fun a : ℕ+ => (a : ℕ)) i (by simp [hi])
  simpa [taoTupleWeight, ← List.map_eq_flatMap, List.map_take] using hsum

private theorem sum_range_two_mul
    {R : Type*} [AddCommMonoid R] (f : ℕ → R) (m : ℕ) :
    (∑ i ∈ Finset.range (2 * m), f i) =
      ∑ r ∈ Finset.range m, (f (2 * r) + f (2 * r + 1)) := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega]
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
      rw [Finset.sum_range_succ]
      simp [add_assoc]

theorem taoSection7OffsetSummand_pair
    (N : ℕ) (as : List ℕ+) (r : ℕ)
    (hr : 2 * r + 2 ≤ as.length) :
    taoSection7OffsetSummand N as (2 * r) +
        taoSection7OffsetSummand N as (2 * r + 1) =
      taoSection7PairExpansionTerm N as r := by
  have hi : 2 * r + 1 < as.length := by omega
  have hweight := taoTupleWeight_take_succ_getD as (2 * r + 1) hi
  let S₁ := taoTupleWeight (as.take (2 * r + 1))
  let S₂ := taoTupleWeight (as.take (2 * r + 2))
  let a₂ : ℕ := (as.getD (2 * r + 1) 1 : ℕ+)
  have hS₂ : S₂ = S₁ + a₂ := by
    simpa [S₁, S₂, a₂] using hweight
  unfold taoSection7OffsetSummand taoSection7PairExpansionTerm
  unfold taoSection7PairX
  dsimp only
  rw [← taoSection7TwoZPow_neg_nat_eq_inv_pow N
      (taoTupleWeight (as.take (2 * r + 1))),
    ← taoSection7TwoZPow_neg_nat_eq_inv_pow N
      (taoTupleWeight (as.take (2 * r + 1 + 1)))]
  change
    (3 : ZMod (3 ^ N)) ^ (2 * r) * taoSection7TwoZPow N (-(S₁ : ℤ)) +
        3 ^ (2 * r + 1) * taoSection7TwoZPow N (-(S₂ : ℤ)) =
      (2 ^ a₂ + 3) *
        (3 ^ (2 * r) * taoSection7TwoZPow N (-(S₂ : ℤ)))
  rw [hS₂]
  have hcancel := taoSection7TwoZPow_neg_add_mul_pow N S₁ a₂
  rw [pow_succ']
  rw [← hcancel]
  ring

theorem taoSection7OffsetPrefix_even_eq_pairExpansionSum
    (N m : ℕ) (as : List ℕ+) (hlen : 2 * m ≤ as.length) :
    taoSection7OffsetPrefix N (2 * m) as =
      taoSection7PairExpansionSum N m as := by
  unfold taoSection7OffsetPrefix taoSection7PairExpansionSum
  rw [sum_range_two_mul]
  apply Finset.sum_congr rfl
  intro r hr
  exact taoSection7OffsetSummand_pair N as r (by
    have hrm := Finset.mem_range.mp hr
    omega)

theorem taoSection7OddTerminalOffset_eq_summand
    (N m : ℕ) (as : List ℕ+) (hlen : as.length = 2 * m + 1) :
    taoSection7OddTerminalOffset N m as =
      taoSection7OffsetSummand N as (2 * m) := by
  unfold taoSection7OddTerminalOffset taoSection7OffsetSummand
  rw [show as.take (2 * m + 1) = as by simp [hlen]]
  rw [taoSection7TwoZPow_neg_nat_eq_inv_pow]

theorem taoSection7OffsetZMod_even_eq_pairExpansionSum
    (m : ℕ) (as : List ℕ+) (hlen : as.length = 2 * m) :
    taoSection7OffsetZMod (2 * m) as =
      taoSection7PairExpansionSum (2 * m) m as := by
  rw [taoSection7OffsetZMod_eq_offsetPrefix]
  exact taoSection7OffsetPrefix_even_eq_pairExpansionSum
    (2 * m) m as (by omega)

theorem taoSection7OffsetZMod_odd_eq_pairExpansionSum_add_terminal
    (m : ℕ) (as : List ℕ+) (hlen : as.length = 2 * m + 1) :
    taoSection7OffsetZMod (2 * m + 1) as =
      taoSection7PairExpansionSum (2 * m + 1) m as +
        taoSection7OddTerminalOffset (2 * m + 1) m as := by
  rw [taoSection7OffsetZMod_eq_offsetPrefix]
  rw [show taoSection7OffsetPrefix (2 * m + 1) (2 * m + 1) as =
      taoSection7OffsetPrefix (2 * m + 1) (2 * m) as +
        taoSection7OffsetSummand (2 * m + 1) as (2 * m) by
    unfold taoSection7OffsetPrefix
    rw [Finset.sum_range_succ]]
  rw [taoSection7OffsetPrefix_even_eq_pairExpansionSum
    (2 * m + 1) m as (by omega)]
  rw [← taoSection7OddTerminalOffset_eq_summand
    (2 * m + 1) m as hlen]

/-- The Section 7 DFT kernel is multiplicative across additive inputs. -/
theorem taoForwardDFTKernel_add
    {N : ℕ} [NeZero N] (xi x y : ZMod N) :
    taoForwardDFTKernel (x + y) xi =
      taoForwardDFTKernel x xi * taoForwardDFTKernel y xi := by
  unfold taoForwardDFTKernel
  rw [show -((x + y) * xi) = -(x * xi) + -(y * xi) by ring]
  exact AddChar.map_add_eq_mul _ _ _

/-- Additive characters turn finite sums into products. -/
theorem taoForwardDFTKernel_sum_eq_prod
    {N : ℕ} [NeZero N] (xi : ZMod N)
    (s : Finset ℕ) (f : ℕ → ZMod N) :
    taoForwardDFTKernel (∑ i ∈ s, f i) xi =
      ∏ i ∈ s, taoForwardDFTKernel (f i) xi := by
  classical
  induction s using Finset.induction with
  | empty => simp [taoForwardDFTKernel]
  | @insert a s ha ih =>
      simp only [Finset.sum_insert ha, Finset.prod_insert ha]
      rw [taoForwardDFTKernel_add]
      rw [ih]

theorem taoSection7CharacterTerm_even_eq_pairPhaseProduct
    (m : ℕ) (xi : ZMod (3 ^ (2 * m)))
    (as : List ℕ+) (hlen : as.length = 2 * m) :
    taoSection7CharacterTerm (2 * m) xi as =
      ∏ r ∈ Finset.range m,
        taoSection7PairPhase (2 * m) xi
          (taoSection7PairX (2 * m) ⟨r + 1, by omega⟩
            (Int.ofNat (taoTupleWeight (as.take (2 * r + 2)))))
          (as.getD (2 * r + 1) 1) := by
  unfold taoSection7CharacterTerm
  rw [taoSection7OffsetZMod_even_eq_pairExpansionSum m as hlen]
  unfold taoSection7PairExpansionSum
  rw [taoForwardDFTKernel_sum_eq_prod]
  apply Finset.prod_congr rfl
  intro r _hr
  rfl

theorem taoSection7CharacterTerm_odd_eq_pairPhaseProduct_mul_terminal
    (m : ℕ) (xi : ZMod (3 ^ (2 * m + 1)))
    (as : List ℕ+) (hlen : as.length = 2 * m + 1) :
    taoSection7CharacterTerm (2 * m + 1) xi as =
      (∏ r ∈ Finset.range m,
        taoSection7PairPhase (2 * m + 1) xi
          (taoSection7PairX (2 * m + 1) ⟨r + 1, by omega⟩
            (Int.ofNat (taoTupleWeight (as.take (2 * r + 2)))))
          (as.getD (2 * r + 1) 1)) *
        taoForwardDFTKernel
          (taoSection7OddTerminalOffset (2 * m + 1) m as) xi := by
  unfold taoSection7CharacterTerm
  rw [taoSection7OffsetZMod_odd_eq_pairExpansionSum_add_terminal m as hlen]
  rw [taoForwardDFTKernel_add]
  unfold taoSection7PairExpansionSum
  rw [taoForwardDFTKernel_sum_eq_prod]
  apply congrArg (fun z : ℂ => z *
    taoForwardDFTKernel
      (taoSection7OddTerminalOffset (2 * m + 1) m as) xi)
  apply Finset.prod_congr rfl
  intro r _hr
  rfl

theorem norm_taoSection7OddTerminalKernel_eq_one
    (N m : ℕ) (xi : ZMod (3 ^ N)) (as : List ℕ+) :
    ‖taoForwardDFTKernel (taoSection7OddTerminalOffset N m as) xi‖ = 1 :=
  norm_taoForwardDFTKernel_eq_one _ _

/-- Fixed-modulus adjacent-pair expansion from source state `(j,s)`.  A final
unpaired valuation is retained as its unit-modulus terminal character. -/
noncomputable def taoSection7PairExpansionFrom
    (N : ℕ) (xi : ZMod (3 ^ N)) : ℕ+ → ℕ → List ℕ+ → ℂ
  | _j, _s, [] => 1
  | j, s, [a] =>
      taoForwardDFTKernel
        (taoSection7PairX N j (Int.ofNat (s + (a : ℕ)))) xi
  | j, s, a₁ :: a₂ :: as =>
      taoSection7PairPhase N xi
          (taoSection7PairX N j
            (Int.ofNat (s + (a₁ : ℕ) + (a₂ : ℕ)))) a₂ *
        taoSection7PairExpansionFrom N xi
          ⟨(j : ℕ) + 1, by omega⟩
          (s + (a₁ : ℕ) + (a₂ : ℕ)) as

theorem norm_taoSection7PairExpansionFrom_eq_one
    (N : ℕ) (xi : ZMod (3 ^ N)) :
    ∀ (j : ℕ+) (s : ℕ) (as : List ℕ+),
      ‖taoSection7PairExpansionFrom N xi j s as‖ = 1 := by
  intro j s as
  induction as using List.twoStepInduction generalizing j s with
  | nil => simp [taoSection7PairExpansionFrom]
  | singleton a =>
      simp [taoSection7PairExpansionFrom,
        norm_taoForwardDFTKernel_eq_one]
  | cons_cons a₁ a₂ as ih =>
      rw [taoSection7PairExpansionFrom, norm_mul]
      rw [show ‖taoSection7PairPhase N xi
          (taoSection7PairX N j
            (Int.ofNat (s + (a₁ : ℕ) + (a₂ : ℕ)))) a₂‖ = 1 by
        unfold taoSection7PairPhase
        exact norm_taoForwardDFTKernel_eq_one _ _]
      rw [ih]
      norm_num

private theorem taoSection7PairExpansionFrom_even_eq_product :
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
              · congr 3 <;> simp [taoTupleWeight, add_assoc]

private theorem taoSection7PairExpansionFrom_odd_eq_product_mul_terminal :
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
          simp [taoSection7PairExpansionFrom, taoTupleWeight, hj]
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
                congr 3 <;> simp [taoTupleWeight, add_assoc]
              exact
                (congrArg₂ (· * ·) hhead
                  (congrArg₂ (· * ·) hprod hterm)).trans (by ring)

theorem taoSection7CharacterTerm_eq_pairExpansionFrom
    (N : ℕ) (xi : ZMod (3 ^ N)) (as : List ℕ+)
    (hlen : as.length = N) :
    taoSection7CharacterTerm N xi as =
      taoSection7PairExpansionFrom N xi 1 0 as := by
  rcases Nat.even_or_odd' N with ⟨m, rfl | rfl⟩
  · rw [taoSection7CharacterTerm_even_eq_pairPhaseProduct m xi as hlen]
    rw [taoSection7PairExpansionFrom_even_eq_product
      m (2 * m) xi 1 0 as hlen]
    apply Finset.prod_congr rfl
    intro r _hr
    congr 2
    · apply Subtype.ext
      simp
      omega
    · congr 1
      simp
  · rw [taoSection7CharacterTerm_odd_eq_pairPhaseProduct_mul_terminal
      m xi as hlen]
    rw [taoSection7PairExpansionFrom_odd_eq_product_mul_terminal
      m (2 * m + 1) xi 1 0 as hlen]
    apply congrArg₂ (· * ·)
    · apply Finset.prod_congr rfl
      intro r _hr
      congr 2
      · apply Subtype.ext
        simp
        omega
      · congr 1
        simp
    · apply congrArg
        (fun x : ZMod (3 ^ (2 * m + 1)) => taoForwardDFTKernel x xi)
      unfold taoSection7OddTerminalOffset taoSection7PairX
      simp

end Tao
end Erdos1135
