import RationalSubspaceBridge
import TrapCoordinateShear
import RationalSubspaceObstruction
import TrapLocalProduct

set_option autoImplicit false
open Module NumberField Filter
open scoped BigOperators Classical Topology

namespace CollatzResearch

noncomputable def trapFormBasis (t : ℕ) (v : AbsoluteValue ℚ ℝ) :
    Basis (Fin (t + 1)) ℚ (Dual ℚ (Fin (t + 1) → ℚ)) :=
  if v = Rat.infinitePlace.1 then
    (Pi.basisFun ℚ (Fin (t + 1))).dualBasis.map (trapCoordinateShear t).dualMap
  else (Pi.basisFun ℚ (Fin (t + 1))).dualBasis

noncomputable def trapSubspaceForms (t : ℕ) (v : AbsoluteValue ℚ ℝ) :
    Fin (t + 1) → Dual ℚ (Fin (t + 1) → ℚ) := trapFormBasis t v

theorem trapSubspaceForms_independent (t : ℕ) (v : AbsoluteValue ℚ ℝ) :
    LinearIndependent ℚ (trapSubspaceForms t v) :=
  (trapFormBasis t v).linearIndependent

theorem trapSubspaceForms_infinite_apply (t : ℕ) (i : Fin (t + 1))
    (x : Fin (t + 1) → ℚ) :
    trapSubspaceForms t Rat.infinitePlace.1 i x = trapCoordinateShear t x i := by
  simp [trapSubspaceForms, trapFormBasis]

theorem trapSubspaceForms_padic_apply (t : ℕ) (p : Nat.Primes)
    (i : Fin (t + 1)) (x : Fin (t + 1) → ℚ) :
    trapSubspaceForms t (Rat.AbsoluteValue.padic (p : ℕ)) i x = x i := by
  simp [trapSubspaceForms, trapFormBasis, (Rat.infinitePlace_val_ne_padic p).symm]

def trapPrimeTwo : Nat.Primes := ⟨2, by decide⟩

def trapPrimeThree : Nat.Primes := ⟨3, by decide⟩

def trapPrimeSet : Finset Nat.Primes := {trapPrimeTwo, trapPrimeThree}

def trapRawRealProduct {t : ℕ} (x : Fin (t + 1) → ℚ) : ℝ :=
  (|((x 0 - ∑ i : Fin t, x i.succ : ℚ) : ℝ)| * ∏ i : Fin t, |(x i.succ : ℝ)|) *
    (∏ i, (padicNorm 2 (x i) : ℝ)) * (∏ i, (padicNorm 3 (x i) : ℝ))

theorem trapSubspaceForms_product_eq (t : ℕ) (x : Fin (t + 1) → ℚ) :
    (∏ i, |(trapSubspaceForms t Rat.infinitePlace.1 i x : ℝ)|) *
      (∏ p ∈ trapPrimeSet, ∏ i,
        (padicNorm (p : ℕ) (trapSubspaceForms t (Rat.AbsoluteValue.padic (p : ℕ)) i x) : ℝ)) =
      trapRawRealProduct x := by
  simp_rw [trapSubspaceForms_infinite_apply, trapSubspaceForms_padic_apply]
  have hp : trapPrimeTwo ≠ trapPrimeThree := by
    intro h
    have hc := congrArg Subtype.val h
    norm_num [trapPrimeTwo, trapPrimeThree] at hc
  rw [trapPrimeSet, Finset.prod_pair hp]
  rw [Fin.prod_univ_succ]
  simp only [trapCoordinateShear_zero, trapCoordinateShear_succ]
  unfold trapRawRealProduct trapPrimeTwo trapPrimeThree
  ring

theorem exists_finite_subspaces_of_small_trap_product (t : ℕ) (ht : 0 < t)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ T : Finset (Submodule ℚ (Fin (t + 1) → ℚ)), (∀ W ∈ T, W ≠ ⊤) ∧
      ∀ x : Fin (t + 1) → ℤ, (fun i => (x i : ℚ)) ≠ 0 →
        trapRawRealProduct (fun i => (x i : ℚ)) ≤
          (⨆ i, |(x i : ℝ)|) ^ (-ε) →
        ∃ W ∈ T, (fun i => (x i : ℚ)) ∈ W := by
  have : Nontrivial (Fin (t + 1)) := Fin.nontrivial_iff_two_le.mpr (by omega)
  obtain ⟨T, hT, hcov⟩ := CollatzSubspaceBridge.rational_integer_subspace_cover
    trapPrimeSet (trapSubspaceForms t) (trapSubspaceForms_independent t _)
    (fun p _ => trapSubspaceForms_independent t _) hε
  refine ⟨T, hT, fun x hx hprod => hcov x hx ?_⟩
  simpa only [trapSubspaceForms_product_eq] using hprod

theorem trapRawRealProduct_eq_cast {t : ℕ} (x : Fin (t + 1) → ℚ) :
    trapRawRealProduct x = (trapLocalProduct (x 0 - ∑ i : Fin t, x i.succ) x : ℝ) := by
  simp [trapRawRealProduct, trapLocalProduct]

theorem trapRawRealProduct_le_carry_bound {t : ℕ} (x : Fin (t + 1) → ℤ)
    (a : ℤ) (D : ℕ) (z : Fin t → ℤ) (p s : Fin t → ℕ)
    (hhead : x 0 = 2 ^ D * a)
    (htail : ∀ i : Fin t, x i.succ = z i * 2 ^ p i * 3 ^ s i) :
    trapRawRealProduct (fun i => (x i : ℚ)) ≤
      (∏ i, |(z i : ℝ)|) * |((x 0 - ∑ i : Fin t, x i.succ : ℤ) : ℝ)| / 2 ^ D := by
  have hxq : (fun i => (x i : ℚ)) =
      Fin.cases ((2 : ℚ) ^ D * a) (fun i => (z i : ℚ) * 2 ^ p i * 3 ^ s i) := by
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [hhead]
    · simp [htail]
  have h := trapLocalProduct_real_le_carry_product a
    ((x 0 : ℚ) - ∑ i : Fin t, (x i.succ : ℚ)) D z p s
  rw [← hxq] at h
  rw [trapRawRealProduct_eq_cast]
  simpa using h

theorem not_eventually_small_trap_product_of_trap_ratios {t : ℕ} (ht : 0 < t)
    {ε : ℝ} (hε : 0 < ε) (x : ℕ → Fin (t + 1) → ℤ)
    (hb : ∀ᶠ n in atTop, x n 0 - ∑ i : Fin t, x n i.succ ≠ 0)
    (hx : ∀ i : Fin t, ∀ᶠ n in atTop, x n i.succ ≠ 0)
    (hbsmall : ∀ i : Fin t,
      Tendsto (fun n => ((x n 0 - ∑ j : Fin t, x n j.succ : ℤ) : ℝ) /
        (x n i.succ : ℝ)) atTop (𝓝 0))
    (hsep : ∀ i j : Fin t, i < j →
      Tendsto (fun n => (x n i.succ : ℝ) / (x n j.succ : ℝ)) atTop (𝓝 0)) :
    ¬ (∀ᶠ n in atTop, trapRawRealProduct (fun i => (x n i : ℚ)) ≤
      (⨆ i, |(x n i : ℝ)|) ^ (-ε)) := by
  have h := CollatzSubspaceBridge.not_eventually_small_localProduct_of_trap_ratios
    ht trapPrimeSet (trapSubspaceForms t) (trapSubspaceForms_independent t _)
    (fun p _ => trapSubspaceForms_independent t _) hε x hb hx hbsmall hsep
  simpa only [CollatzSubspaceBridge.rationalLocalProduct, trapSubspaceForms_product_eq] using h

theorem not_eventually_small_carry_bound_of_trap_ratios {t : ℕ} (ht : 0 < t)
    {ε : ℝ} (hε : 0 < ε) (x : ℕ → Fin (t + 1) → ℤ)
    (a : ℕ → ℤ) (D : ℕ → ℕ) (z : ℕ → Fin t → ℤ) (p s : ℕ → Fin t → ℕ)
    (hhead : ∀ n, x n 0 = 2 ^ D n * a n)
    (htail : ∀ n (i : Fin t), x n i.succ = z n i * 2 ^ p n i * 3 ^ s n i)
    (hb : ∀ᶠ n in atTop, x n 0 - ∑ i : Fin t, x n i.succ ≠ 0)
    (hx : ∀ i : Fin t, ∀ᶠ n in atTop, x n i.succ ≠ 0)
    (hbsmall : ∀ i : Fin t,
      Tendsto (fun n => ((x n 0 - ∑ j : Fin t, x n j.succ : ℤ) : ℝ) /
        (x n i.succ : ℝ)) atTop (𝓝 0))
    (hsep : ∀ i j : Fin t, i < j →
      Tendsto (fun n => (x n i.succ : ℝ) / (x n j.succ : ℝ)) atTop (𝓝 0)) :
    ¬ (∀ᶠ n in atTop,
      (∏ i, |(z n i : ℝ)|) * |((x n 0 - ∑ i : Fin t, x n i.succ : ℤ) : ℝ)| / 2 ^ D n ≤
        (⨆ i, |(x n i : ℝ)|) ^ (-ε)) := by
  intro hsmall
  apply not_eventually_small_trap_product_of_trap_ratios ht hε x hb hx hbsmall hsep
  filter_upwards [hsmall] with n hn
  exact (trapRawRealProduct_le_carry_bound (x n) (a n) (D n) (z n) (p n) (s n)
    (hhead n) (htail n)).trans hn

end CollatzResearch

#print axioms CollatzResearch.exists_finite_subspaces_of_small_trap_product
#print axioms CollatzResearch.not_eventually_small_carry_bound_of_trap_ratios
