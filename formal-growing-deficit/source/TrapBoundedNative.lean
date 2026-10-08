import TrapBoundedSpan
import TrapBlockSubsequence
import TrapBoundedCompression
import TrapMacroscopicNative

set_option autoImplicit false
open Filter
open scoped BigOperators Topology

namespace CollatzResearch

def trapCompressedOmission (m u : ℕ → ℕ) (a b : ℕ) : ℕ :=
  trapChainSum u a (b - a) + trapChainSum m (a + 1) (b - a - 1)

def trapCompressedGap (h : ℕ → ℕ) (g : ℕ → ℤ) (a b : ℕ) : ℤ :=
  trapChainSum g a (b - a) +
    trapChainSum (fun i => (h i : ℤ)) (a + 1) (b - a - 1)

theorem trap_compressed_horizontal_schedule (j m u : ℕ → ℕ) (r a b : ℕ)
    (hab : a < b) (hbr : b ≤ r)
    (hstep : ∀ i < r, j (i + 1) = j i + (m i + u i)) :
    j b = j a + (m a + trapCompressedOmission m u a b) := by
  have hs := trap_deleted_horizontal_schedule j m u a (b - a - 1)
    (fun i hi => by simpa only [add_assoc] using hstep (a + i) (by omega))
  rw [show a + (b - a - 1) + 1 = b by omega,
    show b - a - 1 + 1 = b - a by omega] at hs
  simpa only [trapCompressedOmission, trapChainSum, add_assoc, add_left_comm, add_comm] using hs

theorem trap_compressed_vertical_schedule (T g : ℕ → ℤ) (h : ℕ → ℕ) (r a b : ℕ)
    (hab : a < b) (hbr : b ≤ r)
    (hstep : ∀ i < r, T (i + 1) - T i = (h (i + 1) : ℤ) + g i) :
    T b - T a = (h b : ℤ) + trapCompressedGap h g a b := by
  have hs := trap_deleted_vertical_schedule T (fun i => (h i : ℤ)) g a (b - a - 1)
    (by intro i hi; have := hstep (a + i) (by omega); linarith)
  rw [show a + (b - a - 1) + 1 = b by omega,
    show b - a - 1 + 1 = b - a by omega] at hs
  have hs' : T b = T a + (h b : ℤ) + trapCompressedGap h g a b := by
    simpa only [trapCompressedGap, trapChainSum, Nat.add_assoc, Nat.add_left_comm,
      Nat.add_comm] using hs
  linarith

theorem eventually_trap_compressed_omission_sublinear
    (m u : ℕ → ℕ → ℕ) (N : ℕ → ℝ) (a b : ℕ)
    (hN : ∀ᶠ k in atTop, 0 ≤ N k)
    (hu : ∀ i < b - a, ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ k in atTop, (u k (a + i) : ℝ) ≤ gamma * N k)
    (hm : ∀ i < b - a - 1, ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ k in atTop, (m k (a + 1 + i) : ℝ) ≤ gamma * N k) :
    ∀ gamma : ℝ, 0 < gamma → ∀ᶠ k in atTop,
      (trapCompressedOmission (m k) (u k) a b : ℝ) ≤ gamma * N k := by
  have hu' := eventually_trapChainSum_nat_sublinear u N a (b - a) hN hu
  have hm' := eventually_trapChainSum_nat_sublinear m N (a + 1) (b - a - 1) hN hm
  intro gamma hgamma
  filter_upwards [hu' (gamma / 2) (by positivity), hm' (gamma / 2) (by positivity)]
    with k huk hmk
  simp only [trapCompressedOmission, Nat.cast_add]
  linarith

theorem eventually_trap_compressed_gap_sublinear
    (h : ℕ → ℕ → ℕ) (g : ℕ → ℕ → ℤ) (N : ℕ → ℝ) (a b : ℕ)
    (hN : ∀ᶠ k in atTop, 0 ≤ N k)
    (hg : ∀ i < b - a, ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ k in atTop, |(g k (a + i) : ℝ)| ≤ gamma * N k)
    (hh : ∀ i < b - a - 1, ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ k in atTop, (h k (a + 1 + i) : ℝ) ≤ gamma * N k) :
    ∀ gamma : ℝ, 0 < gamma → ∀ᶠ k in atTop,
      |(trapCompressedGap (h k) (g k) a b : ℝ)| ≤ gamma * N k := by
  exact eventually_trapChain_error_sum g (fun k i => (h k i : ℤ)) N
    a (b - a) (a + 1) (b - a - 1) hN hg (by
      intro i hi gamma hgamma
      simpa only [Int.cast_natCast, Nat.abs_cast] using hh i hi gamma hgamma)

end CollatzResearch

namespace Erdos1135.Tao

open CollatzResearch

theorem false_of_native_black_traps_selected_support {r : ℕ}
    (n : ℕ → ℕ) (h m u : ℕ → ℕ → ℕ) (e g : ℕ → ℕ → ℤ)
    (xi : ∀ k, ZMod (3 ^ n k)) (p : ℕ → ℕ → TaoSection7Point)
    {epsilon eta delta : ℝ} (hepsilon0 : 0 ≤ epsilon) (hepsilon : epsilon < 1 / 4)
    (heta : 0 < eta) (hdelta : 0 < delta)
    (hn : Tendsto (fun k => (n k : ℝ)) atTop atTop)
    (hxi : ∀ k, zmodThreePrimitive (n k) (xi k))
    (hstrip : ∀ k i, i ≤ r → 2 * (((p k i).j : ℕ) - 1) < n k)
    (hspace : ∀ k i, i < r →
      ((p k (i + 1)).j : ℕ) = ((p k i).j : ℕ) + (m k i + u k i))
    (htop : ∀ k i, i < r →
      (p k (i + 1)).l - (p k i).l = (h k (i + 1) : ℤ) + g k i)
    (hh : ∀ k i, i ≤ r → (h k i : ℤ) = 4 * (m k i : ℤ) + e k i)
    (htotal : ∀ k, ∑ i ∈ Finset.range (r + 1), m k i ≤ n k)
    (hblack : ∀ k i, i ≤ r → (integerHeightTrap (p k i) (h k i)).BlackOn
      (taoSection7SourceBlackPoint (n k) (xi k) epsilon))
    (hgap : ∀ᶠ k in atTop,
      (n k : ℝ) * Real.log 3 + eta * (n k : ℝ) ≤
        (((h k 0 : ℤ) + ((p k r).l - (p k 0).l) : ℤ) : ℝ) * Real.log 2)
    (hu : ∀ i < r, ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ k in atTop, (u k i : ℝ) ≤ gamma * (n k : ℝ))
    (hg : ∀ i < r, ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ k in atTop, |(g k i : ℝ)| ≤ gamma * (n k : ℝ))
    (he : ∀ i ≤ r, ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ k in atTop, |(e k i : ℝ)| ≤ gamma * (n k : ℝ))
    (S : Finset ℕ) (hS : S.Nonempty) (hSsub : S ⊆ Finset.range (r + 1))
    (hlarge : ∀ i ∈ S, ∀ᶠ k in atTop, delta * (n k : ℝ) ≤ (m k i : ℝ))
    (hsmall : ∀ i ≤ r, i ∉ S → ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ k in atTop, (m k i : ℝ) ≤ gamma * (n k : ℝ)) : False := by
  obtain ⟨t, I, hImem, hImono, hIonto, hIbound⟩ := exists_ordered_nat_support r S hS hSsub
  let unew k i := trapCompressedOmission (m k) (u k) (I i) (I (i + 1))
  let gnew k i := trapCompressedGap (h k) (g k) (I i) (I (i + 1))
  have hN0 : ∀ᶠ k in atTop, (0 : ℝ) ≤ n k := Eventually.of_forall fun _ => by positivity
  have hhsmall : ∀ i ≤ r, i ∉ S → ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ k in atTop, (h k i : ℝ) ≤ gamma * (n k : ℝ) := by
    intro i hi hnot
    exact eventually_trap_height_sublinear (fun k => h k i) (fun k => m k i)
      (fun k => e k i) (fun k => (n k : ℝ)) (fun k => hh k i hi)
      (hsmall i hi hnot) (he i hi)
  have hunew : ∀ i < t, ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ k in atTop, (unew k i : ℝ) ≤ gamma * (n k : ℝ) := by
    intro i hi
    apply eventually_trap_compressed_omission_sublinear m u (fun k => (n k : ℝ))
      (I i) (I (i + 1)) hN0
    · intro j hj
      exact hu (I i + j) (by have := hIbound (i + 1) (by omega); omega)
    · intro j hj
      have hleft : I i < I i + 1 + j := by omega
      have hright : I i + 1 + j < I (i + 1) := by omega
      exact hsmall (I i + 1 + j) (by have := hIbound (i + 1) (by omega); omega)
        (support_gap_not_mem S t I hImono hIonto hi hleft hright)
  have hgnew : ∀ i < t, ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ k in atTop, |(gnew k i : ℝ)| ≤ gamma * (n k : ℝ) := by
    intro i hi
    apply eventually_trap_compressed_gap_sublinear h g (fun k => (n k : ℝ))
      (I i) (I (i + 1)) hN0
    · intro j hj
      exact hg (I i + j) (by have := hIbound (i + 1) (by omega); omega)
    · intro j hj
      have hleft : I i < I i + 1 + j := by omega
      have hright : I i + 1 + j < I (i + 1) := by omega
      exact hhsmall (I i + 1 + j) (by have := hIbound (i + 1) (by omega); omega)
        (support_gap_not_mem S t I hImono hIonto hi hleft hright)
  have htopnew : ∀ k i, i < t →
      (p k (I (i + 1))).l - (p k (I i)).l = (h k (I (i + 1)) : ℤ) + gnew k i := by
    intro k i hi
    exact trap_compressed_vertical_schedule (fun j => (p k j).l) (g k) (h k) r
      (I i) (I (i + 1)) (hImono i (i + 1) (by omega) (by omega))
      (hIbound (i + 1) (by omega)) (htop k)
  have hforward : ∀ i < t, ∀ᶠ k in atTop,
      (p k (I i)).l ≤ (p k (I (i + 1))).l := by
    intro i hi
    filter_upwards [hlarge (I (i + 1)) (hImem (i + 1) (by omega)),
      he (I (i + 1)) (hIbound (i + 1) (by omega)) delta hdelta,
      hgnew i hi delta hdelta] with k hmk hek hgk
    have hheq : (h k (I (i + 1)) : ℝ) =
        4 * (m k (I (i + 1)) : ℝ) + (e k (I (i + 1)) : ℝ) := by
      exact_mod_cast hh k (I (i + 1)) (hIbound (i + 1) (by omega))
    have hn0 : 0 ≤ delta * (n k : ℝ) := mul_nonneg hdelta.le (Nat.cast_nonneg _)
    have hnonneg : (0 : ℝ) ≤ (h k (I (i + 1)) : ℝ) + (gnew k i : ℝ) := by
      linarith [neg_abs_le (e k (I (i + 1)) : ℝ), neg_abs_le (gnew k i : ℝ)]
    have hnonneg' : (0 : ℤ) ≤ (h k (I (i + 1)) : ℤ) + gnew k i := by
      exact_mod_cast hnonneg
    have ht := htopnew k i hi
    omega
  have hstep : ∀ k i, i < r →
      (p k (i + 1)).l = (p k i).l + (h k (i + 1) : ℤ) + g k i := by
    intro k i hi
    have := htop k i hi
    linarith
  have hloss := eventually_trap_deleted_span_sublinear (fun k i => (p k i).l) g h
    (fun k => (n k : ℝ)) r (I 0) (I t)
    (ordered_support_le hImono (Nat.zero_le t) le_rfl) (hIbound t le_rfl) hstep hN0
    (by
      intro i hi
      rcases hi with hi | ⟨hit, hir⟩
      · exact hhsmall i (by have := hIbound 0 (Nat.zero_le t); omega)
          (support_before_first_not_mem S t I hImono hIonto hi)
      · exact hhsmall i hir (support_after_last_not_mem S t I hImono hIonto hit)) hg
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hgapnew : ∀ᶠ k in atTop,
      (n k : ℝ) * Real.log 3 + (eta / 2) * (n k : ℝ) ≤
        (((h k (I 0) : ℤ) + ((p k (I t)).l - (p k (I 0)).l) : ℤ) : ℝ) *
          Real.log 2 := by
    filter_upwards [hgap, hloss (eta / (2 * Real.log 2)) (by positivity)] with k hk hlk
    have hdiff := (le_abs_self _).trans hlk
    have hmul := mul_le_mul_of_nonneg_right hdiff hlog2.le
    have hrate : eta / (2 * Real.log 2) * (n k : ℝ) * Real.log 2 =
        eta / 2 * (n k : ℝ) := by field_simp
    rw [hrate] at hmul
    simp only [Int.cast_sub, Int.cast_add, Int.cast_natCast] at hk hmul ⊢
    nlinarith
  apply false_of_macroscopic_native_black_traps_eventually_forward n
    (fun k i => h k (I i)) (fun k i => m k (I i)) unew
    (fun k i => e k (I i)) gnew xi (fun k i => p k (I i))
    hepsilon0 hepsilon (show 0 < eta / 2 by positivity) hdelta hn hxi
    (fun k => hstrip k (I t) (hIbound t le_rfl)) ?_ hforward htopnew
    (fun k i hi => hh k (I i) (hIbound i hi)) ?_
    (fun k i hi => hblack k (I i) (hIbound i hi))
    (fun i hi => hlarge (I i) (hImem i hi)) hgapnew hunew hgnew
    (fun i hi => he (I i) (hIbound i hi))
  · intro k i hi
    exact trap_compressed_horizontal_schedule (fun j => ((p k j).j : ℕ)) (m k) (u k) r
      (I i) (I (i + 1)) (hImono i (i + 1) (by omega) (by omega))
      (hIbound (i + 1) (by omega)) (hspace k)
  · intro k
    exact (sum_ordered_support_le_range r t I (m k) hIbound hImono).trans (htotal k)

/-- A fixed finite family of literal native black triangles cannot have
sublinear scheduling errors and a fixed positive entropy-span excess.
No macroscopic block length or ordering of the original tops is assumed. -/
theorem false_of_bounded_native_black_traps {r : ℕ}
    (n : ℕ → ℕ) (h m u : ℕ → ℕ → ℕ) (e g : ℕ → ℕ → ℤ)
    (xi : ∀ k, ZMod (3 ^ n k)) (p : ℕ → ℕ → TaoSection7Point)
    {epsilon eta : ℝ} (hepsilon0 : 0 ≤ epsilon) (hepsilon : epsilon < 1 / 4)
    (heta : 0 < eta)
    (hn : Tendsto (fun k => (n k : ℝ)) atTop atTop)
    (hxi : ∀ k, zmodThreePrimitive (n k) (xi k))
    (hstrip : ∀ k i, i ≤ r → 2 * (((p k i).j : ℕ) - 1) < n k)
    (hspace : ∀ k i, i < r →
      ((p k (i + 1)).j : ℕ) = ((p k i).j : ℕ) + (m k i + u k i))
    (htop : ∀ k i, i < r →
      (p k (i + 1)).l - (p k i).l = (h k (i + 1) : ℤ) + g k i)
    (hh : ∀ k i, i ≤ r → (h k i : ℤ) = 4 * (m k i : ℤ) + e k i)
    (htotal : ∀ k, ∑ i ∈ Finset.range (r + 1), m k i ≤ n k)
    (hblack : ∀ k i, i ≤ r → (integerHeightTrap (p k i) (h k i)).BlackOn
      (taoSection7SourceBlackPoint (n k) (xi k) epsilon))
    (hgap : ∀ᶠ k in atTop,
      (n k : ℝ) * Real.log 3 + eta * (n k : ℝ) ≤
        (((h k 0 : ℤ) + ((p k r).l - (p k 0).l) : ℤ) : ℝ) * Real.log 2)
    (hu : ∀ i < r, ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ k in atTop, (u k i : ℝ) ≤ gamma * (n k : ℝ))
    (hg : ∀ i < r, ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ k in atTop, |(g k i : ℝ)| ≤ gamma * (n k : ℝ))
    (he : ∀ i ≤ r, ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ k in atTop, |(e k i : ℝ)| ≤ gamma * (n k : ℝ)) : False := by
  classical
  have hstep : ∀ k i, i < r →
      (p k (i + 1)).l = (p k i).l + (h k (i + 1) : ℤ) + g k i := by
    intro k i hi
    have := htop k i hi
    linarith
  have hgap' : ∀ᶠ k in atTop,
      (n k : ℝ) * Real.log 3 + eta * (n k : ℝ) ≤
        (((h k 0 : ℤ) + (p k r).l - (p k 0).l : ℤ) : ℝ) * Real.log 2 := by
    simpa only [add_sub_assoc] using hgap
  have hmass := eventually_trap_total_mass_from_entropy (fun k i => (p k i).l)
    e g h m n r heta hstep hh hgap' he hg
  have hmi (k : ℕ) (i : Fin (r + 1)) : m k i ≤ n k := by
    exact (Finset.single_le_sum (s := Finset.range (r + 1)) (f := m k)
      (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr i.isLt)).trans (htotal k)
  have hmF : ∀ k (i : Fin (r + 1)),
      (0 : ℝ) ≤ (m k i : ℝ) ∧ (m k i : ℝ) ≤ (n k : ℝ) := by
    intro k i
    exact ⟨Nat.cast_nonneg _, by exact_mod_cast hmi k i⟩
  have hmassF : ∀ᶠ k in atTop, (eta / (8 * Real.log 2)) * (n k : ℝ) ≤
      ∑ i : Fin (r + 1), (m k i : ℝ) := by
    filter_upwards [hmass] with k hk
    rw [Fin.sum_univ_eq_sum_range (fun i => (m k i : ℝ)) (r + 1)]
    exact hk
  have hc : 0 < eta / (8 * Real.log 2) := by
    have : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    positivity
  obtain ⟨sigma, Sfin, delta, hsigma, hSfin, hdelta, hlarge, hsmall⟩ :=
    trap_block_subsequence_nonempty (fun k (i : Fin (r + 1)) => (m k i : ℝ)) n
      hmF hn (eta / (8 * Real.log 2)) hc hmassF
  let S : Finset ℕ := Sfin.image Fin.val
  have hS : S.Nonempty := hSfin.image Fin.val
  have hSsub : S ⊆ Finset.range (r + 1) := by
    intro a ha
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
    exact Finset.mem_range.mpr i.isLt
  apply false_of_native_black_traps_selected_support
    (fun k => n (sigma k)) (fun k => h (sigma k)) (fun k => m (sigma k))
    (fun k => u (sigma k)) (fun k => e (sigma k)) (fun k => g (sigma k))
    (fun k => xi (sigma k)) (fun k => p (sigma k))
    hepsilon0 hepsilon heta hdelta (hn.comp hsigma.tendsto_atTop)
    (fun k => hxi (sigma k)) (fun k => hstrip (sigma k))
    (fun k => hspace (sigma k)) (fun k => htop (sigma k)) (fun k => hh (sigma k))
    (fun k => htotal (sigma k)) (fun k => hblack (sigma k))
    (hsigma.tendsto_atTop.eventually hgap)
    (fun i hi gamma hgamma => hsigma.tendsto_atTop.eventually (hu i hi gamma hgamma))
    (fun i hi gamma hgamma => hsigma.tendsto_atTop.eventually (hg i hi gamma hgamma))
    (fun i hi gamma hgamma => hsigma.tendsto_atTop.eventually (he i hi gamma hgamma))
    S hS hSsub ?_ ?_
  · intro a ha
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp ha
    exact hlarge i hi
  · intro a ha hnot gamma hgamma
    have hnotFin : (⟨a, by omega⟩ : Fin (r + 1)) ∉ Sfin := by
      intro hmem
      exact hnot (Finset.mem_image_of_mem Fin.val hmem)
    exact hsmall ⟨a, by omega⟩ hnotFin gamma hgamma

end Erdos1135.Tao

#print axioms Erdos1135.Tao.false_of_native_black_traps_selected_support
#print axioms Erdos1135.Tao.false_of_bounded_native_black_traps
