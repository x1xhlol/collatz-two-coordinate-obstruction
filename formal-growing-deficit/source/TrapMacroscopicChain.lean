import TrapCarryIdentities
import TrapCarryGrowth
import TrapCoordinateHeight
import TrapFiniteErrors
import TrapVariableSupportObstruction

set_option autoImplicit false
open Filter
open scoped BigOperators Topology

namespace CollatzResearch

def trapChainSum {A : Type*} [AddCommMonoid A] (f : ℕ → A) (l t : ℕ) : A :=
  ∑ j ∈ Finset.range t, f (l + j)

theorem trapChain_modulus_segment (q : ℕ → ℤ) (m u : ℕ → ℕ) (r l t : ℕ)
    (hlt : l + t ≤ r)
    (hmod : ∀ i < r, q i = 9 ^ (m i + u i) * q (i + 1)) :
    q l = 9 ^ (trapChainSum m l t + trapChainSum u l t) * q (l + t) := by
  have h := trap_modulus_prefix_unroll (fun j => q (l + j))
    (fun j => m (l + j)) (fun j => u (l + j)) t (by
      intro j hj
      simpa only [Nat.add_assoc] using hmod (l + j) (by omega))
  simpa only [Nat.add_zero, trapPrefixExponent, trapChainSum] using h

theorem trapChain_prefix_slope (h D m : ℕ → ℕ) (e g : ℕ → ℤ) (r i : ℕ)
    (hi : i ≤ r)
    (hh : ∀ j ≤ r, (h j : ℤ) = 4 * (m j : ℤ) + e j)
    (hD : ∀ j < r, (D j : ℤ) = (h (j + 1) : ℤ) + g j) :
    ((h 0 + trapPrefixExponent D i : ℕ) : ℤ) =
      4 * ((trapChainSum m 0 (i + 1) : ℕ) : ℤ) +
        (trapChainSum e 0 (i + 1) + trapChainSum g 0 i) := by
  have hsum : (trapPrefixExponent D i : ℤ) =
      ∑ j ∈ Finset.range i, ((h (j + 1) : ℤ) + g j) := by
    simp only [trapPrefixExponent, Nat.cast_sum]
    apply Finset.sum_congr rfl
    intro j hj
    exact hD j (by have := Finset.mem_range.mp hj; omega)
  have hheq : ∑ j ∈ Finset.range (i + 1), (h j : ℤ) =
      ∑ j ∈ Finset.range (i + 1), (4 * (m j : ℤ) + e j) := by
    apply Finset.sum_congr rfl
    intro j hj
    exact hh j (by have := Finset.mem_range.mp hj; omega)
  simp only [trapChainSum, Nat.zero_add, Nat.cast_add, Nat.cast_sum]
  rw [hsum, Finset.sum_add_distrib]
  rw [Finset.sum_range_succ'] at hheq
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hheq
  linarith

theorem trapChain_segment_slope (h D m : ℕ → ℕ) (e g : ℕ → ℤ) (r l t : ℕ)
    (hlt : l + t ≤ r)
    (hh : ∀ j ≤ r, (h j : ℤ) = 4 * (m j : ℤ) + e j)
    (hD : ∀ j < r, (D j : ℤ) = (h (j + 1) : ℤ) + g j) :
    ((trapChainSum D l t : ℕ) : ℤ) =
      4 * ((trapChainSum m (l + 1) t : ℕ) : ℤ) +
        (trapChainSum e (l + 1) t + trapChainSum g l t) := by
  simp only [trapChainSum, Nat.cast_sum]
  have hpoint : ∀ j ∈ Finset.range t, (D (l + j) : ℤ) =
      4 * (m (l + 1 + j) : ℤ) + e (l + 1 + j) + g (l + j) := by
    intro j hj
    rw [hD (l + j) (by have := Finset.mem_range.mp hj; omega),
      hh (l + j + 1) (by have := Finset.mem_range.mp hj; omega)]
    rw [show l + j + 1 = l + 1 + j by omega]
  rw [Finset.sum_congr rfl hpoint]
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum]
  ring

theorem trapChainSum_first_le (m : ℕ → ℕ) (l t : ℕ) (ht : 0 < t) :
    m l ≤ trapChainSum m l t := by
  have h := Finset.single_le_sum (s := Finset.range t)
    (f := fun j => m (l + j)) (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr ht)
  simpa only [trapChainSum, Nat.add_zero] using h

theorem eventually_trapChainSum_sublinear (e : ℕ → ℕ → ℤ) (N : ℕ → ℝ)
    (l t : ℕ) (hN : ∀ᶠ k in atTop, 0 ≤ N k)
    (he : ∀ j < t, ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ k in atTop, |(e k (l + j) : ℝ)| ≤ gamma * N k) :
    ∀ gamma : ℝ, 0 < gamma → ∀ᶠ k in atTop,
      |((trapChainSum (e k) l t : ℤ) : ℝ)| ≤ gamma * N k := by
  have hsum := eventually_trap_finset_abs_sublinear (Finset.range t)
    (fun k j => (e k (l + j) : ℝ)) N hN
    (fun j hj => he j (Finset.mem_range.mp hj))
  intro gamma hgamma
  filter_upwards [hsum gamma hgamma] with k hk
  have h := Finset.abs_sum_le_sum_abs (fun j => (e k (l + j) : ℝ)) (Finset.range t)
  simpa only [trapChainSum, Int.cast_sum] using h.trans hk

theorem eventually_trapChainSum_nat_sublinear (u : ℕ → ℕ → ℕ) (N : ℕ → ℝ)
    (l t : ℕ) (hN : ∀ᶠ k in atTop, 0 ≤ N k)
    (hu : ∀ j < t, ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ k in atTop, (u k (l + j) : ℝ) ≤ gamma * N k) :
    ∀ gamma : ℝ, 0 < gamma → ∀ᶠ k in atTop,
      ((trapChainSum (u k) l t : ℕ) : ℝ) ≤ gamma * N k := by
  have hsum := eventually_trap_finset_abs_sublinear (Finset.range t)
    (fun k j => (u k (l + j) : ℝ)) N hN (by
      intro j hj gamma hgamma
      simpa only [Nat.abs_cast] using hu j (Finset.mem_range.mp hj) gamma hgamma)
  simpa only [Nat.abs_cast, trapChainSum, Nat.cast_sum] using hsum

theorem eventually_trapChain_error_sum (e g : ℕ → ℕ → ℤ) (N : ℕ → ℝ)
    (le te lg tg : ℕ) (hN : ∀ᶠ k in atTop, 0 ≤ N k)
    (he : ∀ j < te, ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ k in atTop, |(e k (le + j) : ℝ)| ≤ gamma * N k)
    (hg : ∀ j < tg, ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ k in atTop, |(g k (lg + j) : ℝ)| ≤ gamma * N k) :
    ∀ gamma : ℝ, 0 < gamma → ∀ᶠ k in atTop,
      |((trapChainSum (e k) le te + trapChainSum (g k) lg tg : ℤ) : ℝ)| ≤
        gamma * N k := by
  have he' := eventually_trapChainSum_sublinear e N le te hN he
  have hg' := eventually_trapChainSum_sublinear g N lg tg hN hg
  have h := eventually_linear_error_bound
    (fun k => ((trapChainSum (e k) le te : ℤ) : ℝ))
    (fun k => ((trapChainSum (g k) lg tg : ℤ) : ℝ)) N 1 1 hN he' hg'
  simpa only [one_mul, Int.cast_add] using h

theorem div_abs_int_le_one {epsilon : ℝ} (hepsilon : epsilon ≤ 1) (z : ℤ) :
    epsilon / |(z : ℝ)| ≤ 1 := by
  by_cases hz : z = 0
  · simp [hz]
  have hzpos : (0 : ℤ) < |z| := abs_pos.mpr hz
  have hz1 : (1 : ℝ) ≤ |(z : ℝ)| := by
    exact_mod_cast (show (1 : ℤ) ≤ |z| by omega)
  exact (div_le_one (by linarith)).mpr (hepsilon.trans hz1)

theorem abs_div_abs_int_le (a z : ℤ) :
    |(a : ℝ)| / |(z : ℝ)| ≤ |(a : ℝ)| := by
  by_cases hz : z = 0
  · simp [hz]
  have hzpos : (0 : ℤ) < |z| := abs_pos.mpr hz
  have hz1 : (1 : ℝ) ≤ |(z : ℝ)| := by
    exact_mod_cast (show (1 : ℤ) ≤ |z| by omega)
  exact div_le_self (abs_nonneg _) hz1

theorem eventually_trap_chain_residual_ratio (r i : ℕ) (hi : i < r)
    (a : ℕ → ℤ) (q z e g : ℕ → ℕ → ℤ) (h D m u : ℕ → ℕ → ℕ)
    (N : ℕ → ℝ) {epsilon delta : ℝ} (hepsilon : epsilon ≤ 1) (hdelta : 0 < delta)
    (hN : ∀ᶠ k in atTop, 0 ≤ N k)
    (hq : ∀ k j, j ≤ r → 0 < q k j)
    (hmod : ∀ k j, j < r → q k j = 9 ^ (m k j + u k j) * q k (j + 1))
    (hh : ∀ k j, j ≤ r → (h k j : ℤ) = 4 * (m k j : ℤ) + e k j)
    (hD : ∀ k j, j < r → (D k j : ℤ) = (h k (j + 1) : ℤ) + g k j)
    (ha : ∀ k, |(a k : ℝ)| ≤ epsilon * (q k 0 : ℝ) / (2 : ℝ) ^ h k 0)
    (hmacro : ∀ᶠ k in atTop, delta * N k ≤ (m k 0 : ℝ))
    (hu : ∀ j < r, ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ k in atTop, (u k j : ℝ) ≤ gamma * N k)
    (he : ∀ j ≤ r, ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ k in atTop, |(e k j : ℝ)| ≤ gamma * N k)
    (hg : ∀ j < r, ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ k in atTop, |(g k j : ℝ)| ≤ gamma * N k) :
    ∀ᶠ k in atTop, z k i ≠ 0 →
      |(a k : ℝ) / (trapCarryCoordinate (D k) (z k) (q k) i : ℝ)| ≤
        Real.exp (-(Real.log (16 / 9) * delta / 2) * N k) := by
  let M k := trapChainSum (m k) 0 (i + 1)
  let U k := trapChainSum (u k) 0 (i + 1)
  let G k := trapChainSum (e k) 0 (i + 1) + trapChainSum (g k) 0 i
  have hM : ∀ᶠ k in atTop, delta * N k ≤ (M k : ℝ) := by
    filter_upwards [hmacro] with k hk
    have hm : (m k 0 : ℝ) ≤ M k := by
      exact_mod_cast trapChainSum_first_le (m k) 0 (i + 1) (by omega)
    exact hk.trans hm
  have hU := eventually_trapChainSum_nat_sublinear u N 0 (i + 1) hN
    (by intro j hj; simpa only [Nat.zero_add] using hu j (by omega))
  have hG := eventually_trapChain_error_sum e g N 0 (i + 1) 0 i hN
    (by intro j hj; simpa only [Nat.zero_add] using he j (by omega))
    (by intro j hj; simpa only [Nat.zero_add] using hg j (by omega))
  have hC : ∀ gamma : ℝ, 0 < gamma → ∀ᶠ k in atTop,
      epsilon / |(z k i : ℝ)| ≤ Real.exp (gamma * N k) := by
    intro gamma hgamma
    filter_upwards [hN] with k hk
    exact (div_abs_int_le_one hepsilon (z k i)).trans
      (Real.one_le_exp (mul_nonneg hgamma.le hk))
  have hsl := eventually_trap_slope_separation
    (fun k => epsilon / |(z k i : ℝ)|) N M U G hdelta hN hM hC hU hG
  filter_upwards [hsl] with k hk hzi
  have hqmod : q k 0 = 9 ^ (M k + U k) * q k (i + 1) := by
    simpa only [Nat.zero_add, M, U] using
      trapChain_modulus_segment (q k) (m k) (u k) r 0 (i + 1) (by omega) (hmod k)
  have hexp : ((h k 0 + trapPrefixExponent (D k) i : ℕ) : ℤ) =
      4 * (M k : ℤ) + G k :=
    trapChain_prefix_slope (h k) (D k) (m k) (e k) (g k) r i (by omega) (hh k) (hD k)
  have hbnd := trap_residual_to_carry_ratio_le_slope
    (b := a k) (z := z k i) (q0 := q k 0) (q := q k (i + 1))
    (h k 0) (trapPrefixExponent (D k) i) (M k) (U k) (G k) epsilon
    hzi (hq k (i + 1) (by omega)) hqmod hexp (ha k)
  have hbnd' : |(a k : ℝ) / (trapCarryCoordinate (D k) (z k) (q k) i : ℝ)| ≤
      (epsilon / |(z k i : ℝ)|) *
        ((9 : ℝ) ^ U k * (2 : ℝ) ^ (-G k) * (9 / 16 : ℝ) ^ M k) := by
    simpa only [trapCarryCoordinate, abs_div] using hbnd
  exact hbnd'.trans hk

theorem eventually_trap_chain_carry_ratio (r i j : ℕ) (hij : i < j) (hj : j < r)
    (q z e g : ℕ → ℕ → ℤ) (h D m u : ℕ → ℕ → ℕ)
    (N : ℕ → ℝ) {delta : ℝ} (hdelta : 0 < delta)
    (hN : ∀ᶠ k in atTop, 0 ≤ N k)
    (hq : ∀ k l, l ≤ r → 0 < q k l)
    (hmod : ∀ k l, l < r → q k l = 9 ^ (m k l + u k l) * q k (l + 1))
    (hh : ∀ k l, l ≤ r → (h k l : ℤ) = 4 * (m k l : ℤ) + e k l)
    (hD : ∀ k l, l < r → (D k l : ℤ) = (h k (l + 1) : ℤ) + g k l)
    (hmacro : ∀ᶠ k in atTop, delta * N k ≤ (m k (i + 1) : ℝ))
    (hz : ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ k in atTop, |(z k i : ℝ)| ≤ Real.exp (gamma * N k))
    (hu : ∀ l < r, ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ k in atTop, (u k l : ℝ) ≤ gamma * N k)
    (he : ∀ l ≤ r, ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ k in atTop, |(e k l : ℝ)| ≤ gamma * N k)
    (hg : ∀ l < r, ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ k in atTop, |(g k l : ℝ)| ≤ gamma * N k) :
    ∀ᶠ k in atTop, z k j ≠ 0 →
      |(trapCarryCoordinate (D k) (z k) (q k) i : ℝ) /
          (trapCarryCoordinate (D k) (z k) (q k) j : ℝ)| ≤
        Real.exp (-(Real.log (16 / 9) * delta / 2) * N k) := by
  let M k := trapChainSum (m k) (i + 1) (j - i)
  let U k := trapChainSum (u k) (i + 1) (j - i)
  let G k := trapChainSum (e k) (i + 1) (j - i) + trapChainSum (g k) i (j - i)
  let E k := trapChainSum (D k) i (j - i)
  have hM : ∀ᶠ k in atTop, delta * N k ≤ (M k : ℝ) := by
    filter_upwards [hmacro] with k hk
    have hm : (m k (i + 1) : ℝ) ≤ M k := by
      exact_mod_cast trapChainSum_first_le (m k) (i + 1) (j - i) (by omega)
    exact hk.trans hm
  have hU := eventually_trapChainSum_nat_sublinear u N (i + 1) (j - i) hN
    (by intro l hl; exact hu (i + 1 + l) (by omega))
  have hG := eventually_trapChain_error_sum e g N (i + 1) (j - i) i (j - i) hN
    (by intro l hl; exact he (i + 1 + l) (by omega))
    (by intro l hl; exact hg (i + l) (by omega))
  have hC : ∀ gamma : ℝ, 0 < gamma → ∀ᶠ k in atTop,
      |(z k i : ℝ)| / |(z k j : ℝ)| ≤ Real.exp (gamma * N k) := by
    intro gamma hgamma
    filter_upwards [hz gamma hgamma] with k hk
    exact (abs_div_abs_int_le (z k i) (z k j)).trans hk
  have hsl := eventually_trap_slope_separation
    (fun k => |(z k i : ℝ)| / |(z k j : ℝ)|) N M U G hdelta hN hM hC hU hG
  filter_upwards [hsl] with k hk hzj
  have hqmod : q k (i + 1) = 9 ^ (M k + U k) * q k (j + 1) := by
    have hid : i + 1 + (j - i) = j + 1 := by omega
    simpa only [hid, M, U] using
      trapChain_modulus_segment (q k) (m k) (u k) r (i + 1) (j - i) (by omega) (hmod k)
  have hp : trapPrefixExponent (D k) j = trapPrefixExponent (D k) i + E k := by
    exact trap_prefix_exponent_split (D k) (by omega)
  have hexp : (E k : ℤ) = 4 * (M k : ℤ) + G k :=
    trapChain_segment_slope (h k) (D k) (m k) (e k) (g k) r i (j - i)
      (by omega) (hh k) (hD k)
  have heq := trap_carry_ratio_eq_slope
    (zi := z k i) (zk := z k j) (qi := q k (i + 1)) (qk := q k (j + 1))
    (trapPrefixExponent (D k) i) (trapPrefixExponent (D k) j) (E k) (M k) (U k) (G k)
    hzj (hq k (j + 1) (by omega)) hqmod hp hexp
  have heq' : |(trapCarryCoordinate (D k) (z k) (q k) i : ℝ) /
      (trapCarryCoordinate (D k) (z k) (q k) j : ℝ)| =
      (|(z k i : ℝ)| / |(z k j : ℝ)|) *
        ((9 : ℝ) ^ U k * (2 : ℝ) ^ (-G k) * (9 / 16 : ℝ) ^ M k) := by
    simpa only [trapCarryCoordinate, abs_div] using heq
  exact heq'.le.trans hk

/-- A fixed finite chain whose blocks all occupy a positive fraction of the
depth cannot have sublinear omissions and slope errors together with a strict
entropy saving. Carries may vanish at arbitrary sequence indices. -/
theorem false_of_macroscopic_trap_chain {r : ℕ}
    (N : ℕ → ℕ) (a z e g : ℕ → ℕ → ℤ) (h D m u s : ℕ → ℕ → ℕ)
    {epsilon eta delta : ℝ} (hepsilon0 : 0 ≤ epsilon) (hepsilon1 : epsilon ≤ 1)
    (heta : 0 < eta) (hdelta : 0 < delta)
    (hN : Tendsto (fun k => (N k : ℝ)) atTop atTop)
    (ha0 : ∀ k i, i ≤ r → a k i ≠ 0)
    (hs : ∀ k i, i ≤ r → s k i ≤ N k)
    (htotal : ∀ k, ∑ i ∈ Finset.range (r + 1), m k i ≤ N k)
    (hrec : ∀ k i, i < r → a k i = 2 ^ D k i * a k (i + 1) - z k i * 3 ^ s k (i + 1))
    (hmod : ∀ k i, i < r → (3 : ℤ) ^ s k i =
      9 ^ (m k i + u k i) * 3 ^ s k (i + 1))
    (hD : ∀ k i, i < r → (D k i : ℤ) = (h k (i + 1) : ℤ) + g k i)
    (hh : ∀ k i, i ≤ r → (h k i : ℤ) = 4 * (m k i : ℤ) + e k i)
    (hblack : ∀ k i, i ≤ r → |(a k i : ℝ)| ≤
      epsilon * (3 : ℝ) ^ s k i / (2 : ℝ) ^ h k i)
    (hmacro : ∀ i ≤ r, ∀ᶠ k in atTop, delta * (N k : ℝ) ≤ (m k i : ℝ))
    (hgap : ∀ᶠ k in atTop,
      (N k : ℝ) * Real.log 3 + eta * (N k : ℝ) ≤
        ((h k 0 + trapPrefixExponent (D k) r : ℕ) : ℝ) * Real.log 2)
    (hu : ∀ i < r, ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ k in atTop, (u k i : ℝ) ≤ gamma * (N k : ℝ))
    (hg : ∀ i < r, ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ k in atTop, |(g k i : ℝ)| ≤ gamma * (N k : ℝ))
    (he : ∀ i ≤ r, ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ k in atTop, |(e k i : ℝ)| ≤ gamma * (N k : ℝ)) :
    False := by
  let q (k i : ℕ) : ℤ := 3 ^ s k i
  let x (k : ℕ) : Fin (r + 1) → ℤ :=
    Fin.cases (2 ^ trapPrefixExponent (D k) r * a k r)
      (fun i => trapCarryCoordinate (D k) (z k) (q k) i)
  have hN0 : ∀ᶠ k in atTop, (0 : ℝ) ≤ N k :=
    Eventually.of_forall fun _ => Nat.cast_nonneg _
  have hq : ∀ k i, i ≤ r → 0 < q k i := by intro k i _; dsimp [q]; positivity
  have hqmod : ∀ k i, i < r → q k i = 9 ^ (m k i + u k i) * q k (i + 1) := hmod
  have hres (k : ℕ) : x k 0 - ∑ i : Fin r, x k i.succ = a k 0 := by
    have hunroll := trap_carry_unroll (a k) (q k) (z k) (D k) r (hrec k)
    simpa only [x, Fin.cases_zero, Fin.cases_succ, Fin.sum_univ_eq_sum_range] using hunroll.symm
  have hzsub : ∀ i < r, ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ k in atTop, |(z k i : ℝ)| ≤ Real.exp (gamma * (N k : ℝ)) := by
    intro i hi
    apply eventually_trap_carry_subexponential_of_recurrences
      (fun k => a k i) (fun k => a k (i + 1)) (fun k => z k i)
      (fun k => q k i) (fun k => q k (i + 1)) (fun k => g k i) (fun k => e k i)
      (fun k => D k i) (fun k => h k i) (fun k => h k (i + 1))
      (fun k => m k i) (fun k => u k i) (fun k => (N k : ℝ)) hepsilon0 hN
      (Eventually.of_forall fun k => hq k (i + 1) (by omega))
      (Eventually.of_forall fun k => hqmod k i hi)
      (Eventually.of_forall fun k => hrec k i hi)
      (Eventually.of_forall fun k => hD k i hi)
      (Eventually.of_forall fun k => hh k i (by omega))
      ?_ ?_ (hu i hi) (hg i hi) (he i (by omega))
    · exact Eventually.of_forall fun k => by simpa [q] using hblack k i (by omega)
    · exact Eventually.of_forall fun k => by simpa [q] using hblack k (i + 1) (by omega)
  have hsaving : ∀ᶠ k in atTop,
      |(a k 0 : ℝ)| / (2 : ℝ) ^ trapPrefixExponent (D k) r ≤
        Real.exp (-eta * (N k : ℝ)) := by
    filter_upwards [hgap] with k hk
    have hqbound : (3 : ℝ) ^ s k 0 ≤ 3 ^ N k :=
      pow_le_pow_right₀ (by norm_num) (hs k 0 (by omega))
    have hbnd : |(a k 0 : ℝ)| ≤ epsilon * (3 : ℝ) ^ N k / (2 : ℝ) ^ h k 0 :=
      (hblack k 0 (by omega)).trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hqbound hepsilon0) (by positivity))
    exact (trap_residual_div_pow_bound (h k 0) (trapPrefixExponent (D k) r)
      (ha0 k 0 (by omega)) hbnd).2.trans
      (trap_entropy_saving_bound (N k) (h k 0 + trapPrefixExponent (D k) r) hepsilon1 hk)
  have hbexp : ∀ i : Fin r, ∀ᶠ k in atTop, z k i ≠ 0 →
      |(a k 0 : ℝ) / (trapCarryCoordinate (D k) (z k) (q k) i : ℝ)| ≤
        Real.exp (-(Real.log (16 / 9) * delta / 2) * (N k : ℝ)) := by
    intro i
    exact eventually_trap_chain_residual_ratio r i i.isLt (fun k => a k 0) q z e g h D m u
      (fun k => (N k : ℝ)) hepsilon1 hdelta hN0 hq hqmod hh hD
      (fun k => by simpa [q] using hblack k 0 (by omega))
      (hmacro 0 (by omega)) hu he hg
  have hsepexp : ∀ i j : Fin r, i < j → ∀ᶠ k in atTop, z k j ≠ 0 →
      |(trapCarryCoordinate (D k) (z k) (q k) i : ℝ) /
          (trapCarryCoordinate (D k) (z k) (q k) j : ℝ)| ≤
        Real.exp (-(Real.log (16 / 9) * delta / 2) * (N k : ℝ)) := by
    intro i j hij
    exact eventually_trap_chain_carry_ratio r i j hij j.isLt q z e g h D m u
      (fun k => (N k : ℝ)) hdelta hN0 hq hqmod hh hD
      (hmacro (i + 1) (by omega)) (hzsub i i.isLt) hu he hg
  have heAgg := eventually_trap_finset_abs_sublinear (Finset.range (r + 1))
    (fun k i => (e k i : ℝ)) (fun k => (N k : ℝ)) hN0
    (by intro i hi; exact he i (by have := Finset.mem_range.mp hi; omega))
  have hgAgg := eventually_trap_finset_abs_sublinear (Finset.range r)
    (fun k i => (g k i : ℝ)) (fun k => (N k : ℝ)) hN0
    (by intro i hi; exact hg i (Finset.mem_range.mp hi))
  have hprefix : ∀ᶠ k in atTop, ∀ j ≤ r,
      (trapPrefixExponent (D k) j : ℝ) ≤ 6 * (N k : ℝ) := by
    filter_upwards [heAgg 1 (by norm_num), hgAgg 1 (by norm_num)] with k hek hgk
    have heN : ∑ i ∈ Finset.range (r + 1), (e k i).natAbs ≤ N k := by
      have hc : ((∑ i ∈ Finset.range (r + 1), (e k i).natAbs : ℕ) : ℝ) ≤ N k := by
        simpa only [one_mul, Nat.cast_sum, Nat.cast_natAbs, Int.cast_abs] using hek
      exact_mod_cast hc
    have hgN : ∑ i ∈ Finset.range r, (g k i).natAbs ≤ N k := by
      have hc : ((∑ i ∈ Finset.range r, (g k i).natAbs : ℕ) : ℝ) ≤ N k := by
        simpa only [one_mul, Nat.cast_sum, Nat.cast_natAbs, Int.cast_abs] using hgk
      exact_mod_cast hc
    intro j hj
    exact_mod_cast trap_prefix_exponent_le_six r (N k) (D k) (h k) (m k) (e k) (g k)
      (fun i hi => hh k i (by omega)) (hD k) (htotal k) heN hgN hj
  have hzOne : ∀ᶠ k in atTop, ∀ i : Fin r, |(z k i : ℝ)| ≤ Real.exp (N k : ℝ) := by
    apply (eventually_all).mpr
    intro i
    simpa only [one_mul] using hzsub i i.isLt 1 (by norm_num)
  have hheight : ∀ᶠ k in atTop,
      (⨆ i : Fin (r + 1), |(x k i : ℝ)|) ≤
        Real.exp ((6 * Real.log 2 + Real.log 3 + 1) * (N k : ℝ)) := by
    filter_upwards [hprefix, hzOne] with k hpk hzk
    have har : |(a k r : ℝ)| ≤ Real.exp (Real.log 3 * (N k : ℝ)) :=
      abs_integer_le_exp_log_three_of_phase_bound (s k r) (h k r) hepsilon0 hepsilon1
        (by positivity) le_rfl (by exact_mod_cast hs k r le_rfl) (hblack k r le_rfl)
    apply trap_coordinate_height_bound (x k) (a k r) (trapPrefixExponent (D k) r)
      (fun i : Fin r => z k i) (fun i => trapPrefixExponent (D k) i)
      (fun i => s k (i + 1)) (Nat.cast_nonneg _) rfl ?_ har (hpk r le_rfl) hzk ?_ ?_
    · intro i
      simp only [x, Fin.cases_succ, trapCarryCoordinate, trapScaledCarry, q]
      ring
    · intro i
      exact hpk i (Nat.le_of_lt i.isLt)
    · intro i
      exact_mod_cast hs k (i + 1) (by omega)
  have hrate : 0 < Real.log (16 / 9 : ℝ) * delta / 2 := by
    have : 0 < Real.log (16 / 9 : ℝ) := Real.log_pos (by norm_num)
    positivity
  have hK : 0 < 6 * Real.log 2 + Real.log 3 + 1 := by
    have : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    have : 0 < Real.log (3 : ℝ) := Real.log_pos (by norm_num)
    positivity
  apply false_of_trap_exponential_bounds_variable_support x (fun k => a k r)
    (fun k => trapPrefixExponent (D k) r) (fun k i => z k i)
    (fun k i => trapPrefixExponent (D k) i) (fun k i => s k (i + 1))
    (fun k => (N k : ℝ)) (fun _ => rfl) ?_ ?_ heta hK hrate hN ?_ ?_ ?_ ?_ hheight
  · intro k i
    simp only [x, Fin.cases_succ, trapCarryCoordinate, trapScaledCarry, q]
    ring
  · exact Eventually.of_forall fun k => by rw [hres]; exact ha0 k 0 (by omega)
  · intro i
    filter_upwards [hbexp i] with k hk hzi
    rw [hres]
    exact hk hzi
  · intro i j hij
    filter_upwards [hsepexp i j hij] with k hk _ hzj
    exact hk hzj
  · intro i gamma hgamma
    exact hzsub i i.isLt gamma hgamma
  · filter_upwards [hsaving] with k hk
    rw [hres]
    exact hk

end CollatzResearch

#print axioms CollatzResearch.trapChain_prefix_slope
#print axioms CollatzResearch.trapChain_segment_slope
#print axioms CollatzResearch.false_of_macroscopic_trap_chain
