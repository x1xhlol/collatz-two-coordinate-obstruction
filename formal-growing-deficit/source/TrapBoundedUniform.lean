import TrapBoundedNative

set_option autoImplicit false
open Filter
open scoped BigOperators Topology

namespace Erdos1135.Tao

/-- A family has `r+1` literal black triangles with exact signed schedules. -/
structure NativeBlackTrapFamily (epsilon : ℝ) (n r : ℕ) where
  h : ℕ → ℕ
  m : ℕ → ℕ
  u : ℕ → ℕ
  e : ℕ → ℤ
  g : ℕ → ℤ
  xi : ZMod (3 ^ n)
  p : ℕ → TaoSection7Point
  primitive : zmodThreePrimitive n xi
  strip : ∀ i ≤ r, 2 * (((p i).j : ℕ) - 1) < n
  space : ∀ i < r, ((p (i + 1)).j : ℕ) = ((p i).j : ℕ) + (m i + u i)
  top : ∀ i < r, (p (i + 1)).l - (p i).l = (h (i + 1) : ℤ) + g i
  height : ∀ i ≤ r, (h i : ℤ) = 4 * (m i : ℤ) + e i
  total : ∑ i ∈ Finset.range (r + 1), m i ≤ n
  black : ∀ i ≤ r, (integerHeightTrap (p i) (h i)).BlackOn
    (taoSection7SourceBlackPoint n xi epsilon)

def nativeTrapFamilyError {epsilon : ℝ} {n r : ℕ}
    (t : NativeBlackTrapFamily epsilon n r) : ℝ :=
  (∑ i ∈ Finset.range (r + 1), |(t.e i : ℝ)|) +
    ∑ i ∈ Finset.range r, ((t.u i : ℝ) + |(t.g i : ℝ)|)

def nativeTrapFamilySpan {epsilon : ℝ} {n r : ℕ}
    (t : NativeBlackTrapFamily epsilon n r) : ℝ :=
  (((t.h 0 : ℤ) + ((t.p r).l - (t.p 0).l) : ℤ) : ℝ)

theorem nativeTrapFamily_error_bounds {epsilon : ℝ} {n r : ℕ}
    (t : NativeBlackTrapFamily epsilon n r) :
    (∀ i < r, (t.u i : ℝ) ≤ nativeTrapFamilyError t ∧
      |(t.g i : ℝ)| ≤ nativeTrapFamilyError t) ∧
    (∀ i ≤ r, |(t.e i : ℝ)| ≤ nativeTrapFamilyError t) := by
  have hE : 0 ≤ ∑ i ∈ Finset.range (r + 1), |(t.e i : ℝ)| :=
    Finset.sum_nonneg (fun _ _ => abs_nonneg _)
  have hG : 0 ≤ ∑ i ∈ Finset.range r, ((t.u i : ℝ) + |(t.g i : ℝ)|) :=
    Finset.sum_nonneg (fun _ _ => by positivity)
  constructor
  · intro i hi
    have hs := Finset.single_le_sum (s := Finset.range r)
      (f := fun j => (t.u j : ℝ) + |(t.g j : ℝ)|)
      (fun _ _ => by positivity) (Finset.mem_range.mpr hi)
    dsimp [nativeTrapFamilyError]
    constructor <;> linarith [abs_nonneg (t.g i : ℝ), Nat.cast_nonneg (α := ℝ) (t.u i)]
  · intro i hi
    have hs := Finset.single_le_sum (s := Finset.range (r + 1))
      (f := fun j => |(t.e j : ℝ)|) (fun _ _ => abs_nonneg _)
      (Finset.mem_range.mpr (by omega : i < r + 1))
    dsimp [nativeTrapFamilyError]
    linarith

theorem eventually_no_native_black_trap_family (r : ℕ)
    {epsilon eta : ℝ} (hepsilon0 : 0 ≤ epsilon) (hepsilon : epsilon < 1 / 4)
    (heta : 0 < eta) (w : ℕ → ℝ)
    (hw : ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ n in atTop, w n ≤ gamma * (n : ℝ)) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ t : NativeBlackTrapFamily epsilon n r,
      nativeTrapFamilyError t ≤ w n →
      nativeTrapFamilySpan t * Real.log 2 < (n : ℝ) * Real.log 3 + eta * (n : ℝ) := by
  classical
  by_contra! hbad
  choose n hn t herror hspan using hbad
  have hnat : Tendsto n atTop atTop := tendsto_atTop_mono hn tendsto_id
  have hnreal : Tendsto (fun k => (n k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hnat
  have herr : ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ k in atTop, nativeTrapFamilyError (t k) ≤ gamma * (n k : ℝ) := by
    intro gamma hgamma
    filter_upwards [hnat.eventually (hw gamma hgamma)] with k hk
    exact (herror k).trans hk
  have hu : ∀ i < r, ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ k in atTop, ((t k).u i : ℝ) ≤ gamma * (n k : ℝ) := by
    intro i hi gamma hgamma
    filter_upwards [herr gamma hgamma] with k hk
    exact ((nativeTrapFamily_error_bounds (t k)).1 i hi).1.trans hk
  have hg : ∀ i < r, ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ k in atTop, |((t k).g i : ℝ)| ≤ gamma * (n k : ℝ) := by
    intro i hi gamma hgamma
    filter_upwards [herr gamma hgamma] with k hk
    exact ((nativeTrapFamily_error_bounds (t k)).1 i hi).2.trans hk
  have he : ∀ i ≤ r, ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ k in atTop, |((t k).e i : ℝ)| ≤ gamma * (n k : ℝ) := by
    intro i hi gamma hgamma
    filter_upwards [herr gamma hgamma] with k hk
    exact ((nativeTrapFamily_error_bounds (t k)).2 i hi).trans hk
  exact false_of_bounded_native_black_traps n
    (fun k => (t k).h) (fun k => (t k).m) (fun k => (t k).u)
    (fun k => (t k).e) (fun k => (t k).g) (fun k => (t k).xi) (fun k => (t k).p)
    hepsilon0 hepsilon heta hnreal (fun k => (t k).primitive)
    (fun k => (t k).strip) (fun k => (t k).space) (fun k => (t k).top)
    (fun k => (t k).height) (fun k => (t k).total) (fun k => (t k).black)
    (Eventually.of_forall hspan) hu hg he

/-- One cutoff applies to every family with at most the fixed number `R` of
triangles, for all primitive frequencies and all allowed triangle locations. -/
theorem eventually_no_bounded_native_black_trap_families (R : ℕ)
    {epsilon eta : ℝ} (hepsilon0 : 0 ≤ epsilon) (hepsilon : epsilon < 1 / 4)
    (heta : 0 < eta) (w : ℕ → ℝ)
    (hw : ∀ gamma : ℝ, 0 < gamma →
      ∀ᶠ n in atTop, w n ≤ gamma * (n : ℝ)) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ r < R, ∀ t : NativeBlackTrapFamily epsilon n r,
      nativeTrapFamilyError t ≤ w n →
      nativeTrapFamilySpan t * Real.log 2 < (n : ℝ) * Real.log 3 + eta * (n : ℝ) := by
  classical
  choose K hK using fun r => eventually_no_native_black_trap_family r hepsilon0 hepsilon heta w hw
  refine ⟨∑ r ∈ Finset.range R, K r, ?_⟩
  intro n hn r hr t ht
  have hKr : K r ≤ ∑ j ∈ Finset.range R, K j :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_range.mpr hr)
  exact hK r n (hKr.trans hn) t ht

end Erdos1135.Tao

#print axioms Erdos1135.Tao.nativeTrapFamily_error_bounds
#print axioms Erdos1135.Tao.eventually_no_native_black_trap_family
#print axioms Erdos1135.Tao.eventually_no_bounded_native_black_trap_families
