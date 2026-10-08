import TrapTriangleArithmetic
import TrapMacroscopicChain

set_option autoImplicit false
open Filter
open scoped BigOperators Topology

namespace Erdos1135.Tao

theorem trap_top_increment_prefix (T : ℕ → ℤ) (r : ℕ)
    (hforward : ∀ i < r, T i ≤ T (i + 1)) :
    (CollatzResearch.trapPrefixExponent (fun i => (T (i + 1) - T i).toNat) r : ℤ) =
      T r - T 0 := by
  simp only [CollatzResearch.trapPrefixExponent, Nat.cast_sum]
  calc
    (∑ i ∈ Finset.range r, ((T (i + 1) - T i).toNat : ℤ)) =
        ∑ i ∈ Finset.range r, (T (i + 1) - T i) := by
          apply Finset.sum_congr rfl
          intro i hi
          exact Int.toNat_of_nonneg (sub_nonneg.mpr (hforward i (Finset.mem_range.mp hi)))
    _ = T r - T 0 := Finset.sum_range_sub T r

/-- A fixed finite sequence of literal native black triangles cannot have
macroscopic block lengths, sublinear scheduling errors, and a strict entropy
excess in its first-height-to-last-top span. -/
theorem false_of_macroscopic_native_black_traps {r : ℕ}
    (n : ℕ → ℕ) (h m u : ℕ → ℕ → ℕ) (e g : ℕ → ℕ → ℤ)
    (xi : ∀ k, ZMod (3 ^ n k)) (p : ℕ → ℕ → TaoSection7Point)
    {epsilon eta delta : ℝ} (hepsilon0 : 0 ≤ epsilon) (hepsilon : epsilon < 1 / 4)
    (heta : 0 < eta) (hdelta : 0 < delta)
    (hn : Tendsto (fun k => (n k : ℝ)) atTop atTop)
    (hxi : ∀ k, zmodThreePrimitive (n k) (xi k))
    (hstrip : ∀ k, 2 * (((p k r).j : ℕ) - 1) < n k)
    (hspace : ∀ k i, i < r →
      ((p k (i + 1)).j : ℕ) = ((p k i).j : ℕ) + (m k i + u k i))
    (hforward : ∀ k i, i < r → (p k i).l ≤ (p k (i + 1)).l)
    (htop : ∀ k i, i < r →
      (p k (i + 1)).l - (p k i).l = (h k (i + 1) : ℤ) + g k i)
    (hh : ∀ k i, i ≤ r → (h k i : ℤ) = 4 * (m k i : ℤ) + e k i)
    (htotal : ∀ k, ∑ i ∈ Finset.range (r + 1), m k i ≤ n k)
    (hblack : ∀ k i, i ≤ r → (integerHeightTrap (p k i) (h k i)).BlackOn
      (taoSection7SourceBlackPoint (n k) (xi k) epsilon))
    (hmacro : ∀ i ≤ r, ∀ᶠ k in atTop, delta * (n k : ℝ) ≤ (m k i : ℝ))
    (hgap : ∀ᶠ k in atTop,
      (n k : ℝ) * Real.log 3 + eta * (n k : ℝ) ≤
        (((h k 0 : ℤ) + ((p k r).l - (p k 0).l) : ℤ) : ℝ) * Real.log 2)
    (hu : ∀ i < r, ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ k in atTop, (u k i : ℝ) ≤ gamma * (n k : ℝ))
    (hg : ∀ i < r, ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ k in atTop, |(g k i : ℝ)| ≤ gamma * (n k : ℝ))
    (he : ∀ i ≤ r, ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ k in atTop, |(e k i : ℝ)| ≤ gamma * (n k : ℝ)) :
    False := by
  classical
  let a k i := trapReducedNumerator (n k) (xi k) (p k i)
  let s k i := n k - 2 * (((p k i).j : ℕ) - 1)
  let D k i := ((p k (i + 1)).l - (p k i).l).toNat
  have hbefore (k j : ℕ) : j ≤ r → ∀ i ≤ j, ((p k i).j : ℕ) ≤ (p k j).j := by
    induction j with
    | zero =>
        intro _ i hi
        have : i = 0 := by omega
        subst i
        exact le_rfl
    | succ j ih =>
        intro hj i hi
        by_cases hij : i = j + 1
        · subst i
          exact le_rfl
        · have hpj := ih (by omega) i (by omega)
          have hstep := hspace k j (by omega)
          omega
  have hallstrip (k i : ℕ) (hi : i ≤ r) :
      2 * (((p k i).j : ℕ) - 1) < n k := by
    have hb := hbefore k r le_rfl i hi
    have hs := hstrip k
    omega
  have hdata : ∀ k, ∃ z : ℕ → ℤ,
      (∀ i < r, a k i = 2 ^ D k i * a k (i + 1) -
        z i * (trapReducedModulus (n k) (p k (i + 1)) : ℤ)) ∧
      (∀ i ≤ r, a k i ≠ 0 ∧ ¬ (3 : ℤ) ∣ a k i) ∧
      (∀ i ≤ r, 0 < trapReducedModulus (n k) (p k i)) ∧
      (∀ i ≤ r, |(a k i : ℝ)| ≤
        epsilon * (trapReducedModulus (n k) (p k i) : ℝ) / (2 : ℝ) ^ h k i) ∧
      (∀ i < r, trapReducedModulus (n k) (p k i) =
        9 ^ (m k i + u k i) * trapReducedModulus (n k) (p k (i + 1))) := by
    intro k
    exact exists_native_trap_arithmetic (n k) r (xi k) (hxi k) (p k) (h k)
      (fun i => m k i + u k i) hepsilon (hallstrip k) (hspace k) (hforward k) (hblack k)
  choose z hrec ha0 hq hbound hmod using hdata
  have hDcast (k i : ℕ) (hi : i < r) :
      (D k i : ℤ) = (p k (i + 1)).l - (p k i).l :=
    Int.toNat_of_nonneg (sub_nonneg.mpr (hforward k i hi))
  have hspan (k : ℕ) :
      (CollatzResearch.trapPrefixExponent (D k) r : ℤ) = (p k r).l - (p k 0).l :=
    trap_top_increment_prefix (fun i => (p k i).l) r (hforward k)
  apply CollatzResearch.false_of_macroscopic_trap_chain n a z e g h D m u s
    hepsilon0 (by linarith) heta hdelta hn
    (fun k i hi => (ha0 k i hi).1) ?_ htotal ?_ ?_ ?_ hh ?_ hmacro ?_ hu hg he
  · intro k i _
    exact Nat.sub_le _ _
  · intro k i hi
    simpa [s, trapReducedModulus] using hrec k i hi
  · intro k i hi
    have hm := hmod k i hi
    change (3 : ℕ) ^ s k i = 9 ^ (m k i + u k i) * 3 ^ s k (i + 1) at hm
    exact_mod_cast hm
  · intro k i hi
    exact (hDcast k i hi).trans (htop k i hi)
  · intro k i hi
    simpa [s, trapReducedModulus] using hbound k i hi
  · filter_upwards [hgap] with k hk
    have hreal : ((h k 0 + CollatzResearch.trapPrefixExponent (D k) r : ℕ) : ℝ) =
        (((h k 0 : ℤ) + ((p k r).l - (p k 0).l) : ℤ) : ℝ) := by
      have hi : ((h k 0 + CollatzResearch.trapPrefixExponent (D k) r : ℕ) : ℤ) =
          (h k 0 : ℤ) + ((p k r).l - (p k 0).l) := by
        rw [Nat.cast_add, hspan]
      exact_mod_cast hi
    rw [hreal]
    exact hk

theorem false_of_macroscopic_native_black_traps_eventually_forward {r : ℕ}
    (n : ℕ → ℕ) (h m u : ℕ → ℕ → ℕ) (e g : ℕ → ℕ → ℤ)
    (xi : ∀ k, ZMod (3 ^ n k)) (p : ℕ → ℕ → TaoSection7Point)
    {epsilon eta delta : ℝ} (hepsilon0 : 0 ≤ epsilon) (hepsilon : epsilon < 1 / 4)
    (heta : 0 < eta) (hdelta : 0 < delta)
    (hn : Tendsto (fun k => (n k : ℝ)) atTop atTop)
    (hxi : ∀ k, zmodThreePrimitive (n k) (xi k))
    (hstrip : ∀ k, 2 * (((p k r).j : ℕ) - 1) < n k)
    (hspace : ∀ k i, i < r →
      ((p k (i + 1)).j : ℕ) = ((p k i).j : ℕ) + (m k i + u k i))
    (hforward : ∀ i < r, ∀ᶠ k in atTop, (p k i).l ≤ (p k (i + 1)).l)
    (htop : ∀ k i, i < r →
      (p k (i + 1)).l - (p k i).l = (h k (i + 1) : ℤ) + g k i)
    (hh : ∀ k i, i ≤ r → (h k i : ℤ) = 4 * (m k i : ℤ) + e k i)
    (htotal : ∀ k, ∑ i ∈ Finset.range (r + 1), m k i ≤ n k)
    (hblack : ∀ k i, i ≤ r → (integerHeightTrap (p k i) (h k i)).BlackOn
      (taoSection7SourceBlackPoint (n k) (xi k) epsilon))
    (hmacro : ∀ i ≤ r, ∀ᶠ k in atTop, delta * (n k : ℝ) ≤ (m k i : ℝ))
    (hgap : ∀ᶠ k in atTop,
      (n k : ℝ) * Real.log 3 + eta * (n k : ℝ) ≤
        (((h k 0 : ℤ) + ((p k r).l - (p k 0).l) : ℤ) : ℝ) * Real.log 2)
    (hu : ∀ i < r, ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ k in atTop, (u k i : ℝ) ≤ gamma * (n k : ℝ))
    (hg : ∀ i < r, ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ k in atTop, |(g k i : ℝ)| ≤ gamma * (n k : ℝ))
    (he : ∀ i ≤ r, ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ k in atTop, |(e k i : ℝ)| ≤ gamma * (n k : ℝ)) :
    False := by
  have hall : ∀ᶠ k in atTop, ∀ i < r, (p k i).l ≤ (p k (i + 1)).l := by
    simpa only [Finset.mem_range] using
      (eventually_all_finset (Finset.range r)).mpr
        (fun i hi => hforward i (Finset.mem_range.mp hi))
  obtain ⟨K, hK⟩ := eventually_atTop.mp hall
  have hshift : Tendsto (fun k : ℕ => k + K) atTop atTop :=
    (show StrictMono (fun k : ℕ => k + K) from fun _ _ hij => Nat.add_lt_add_right hij K).tendsto_atTop
  exact false_of_macroscopic_native_black_traps
    (fun k => n (k + K)) (fun k => h (k + K)) (fun k => m (k + K))
    (fun k => u (k + K)) (fun k => e (k + K)) (fun k => g (k + K))
    (fun k => xi (k + K)) (fun k => p (k + K))
    hepsilon0 hepsilon heta hdelta (hn.comp hshift)
    (fun k => hxi (k + K)) (fun k => hstrip (k + K)) (fun k => hspace (k + K))
    (fun k i hi => hK (k + K) (by omega) i hi)
    (fun k => htop (k + K)) (fun k => hh (k + K))
    (fun k => htotal (k + K)) (fun k => hblack (k + K))
    (fun i hi => hshift.eventually (hmacro i hi)) (hshift.eventually hgap)
    (fun i hi gamma hgamma => hshift.eventually (hu i hi gamma hgamma))
    (fun i hi gamma hgamma => hshift.eventually (hg i hi gamma hgamma))
    (fun i hi gamma hgamma => hshift.eventually (he i hi gamma hgamma))

end Erdos1135.Tao

#print axioms Erdos1135.Tao.trap_top_increment_prefix
#print axioms Erdos1135.Tao.false_of_macroscopic_native_black_traps
#print axioms Erdos1135.Tao.false_of_macroscopic_native_black_traps_eventually_forward
