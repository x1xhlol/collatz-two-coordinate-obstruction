import Erdos1135.Tao.Syracuse.Defs

/-!
# Deterministic Syracuse First Passage

This module records the deterministic least-hit API for Tao's Syracuse first
passage time.  It includes the deterministic artificial no-hit totalizer, but
keeps probabilistic `Pass_x` random variables, PMF/TV, and window layers out of
this layer.
-/

namespace Erdos1135
namespace Tao

/-- The Syracuse orbit first hits the natural threshold `B` at time `n`. -/
def syracuseFirstHitAtMost (B N n : ℕ) : Prop :=
  (syracuse^[n]) N ≤ B ∧ ∀ k < n, B < (syracuse^[k]) N

/-- Least Syracuse hitting time, defined only from an existing hit witness. -/
def syracuseFirstPassageTime (N B : ℕ) (h : syracuseHitsAtMost N B) : ℕ :=
  Nat.find h

theorem syracuseFirstPassageTime_spec (N B : ℕ)
    (h : syracuseHitsAtMost N B) :
    (syracuse^[syracuseFirstPassageTime N B h]) N ≤ B :=
  Nat.find_spec h

theorem syracuseFirstPassageTime_minimal (N B k : ℕ)
    (h : syracuseHitsAtMost N B)
    (hk : k < syracuseFirstPassageTime N B h) :
    ¬ (syracuse^[k]) N ≤ B :=
  Nat.find_min h hk

theorem syracuseFirstPassageTime_pre_gt (N B k : ℕ)
    (h : syracuseHitsAtMost N B)
    (hk : k < syracuseFirstPassageTime N B h) :
    B < (syracuse^[k]) N :=
  Nat.lt_of_not_ge (syracuseFirstPassageTime_minimal N B k h hk)

theorem syracuseFirstHitAtMost_of_hitsAtMost (N B : ℕ)
    (h : syracuseHitsAtMost N B) :
    syracuseFirstHitAtMost B N (syracuseFirstPassageTime N B h) := by
  constructor
  · exact syracuseFirstPassageTime_spec N B h
  · intro k hk
    exact syracuseFirstPassageTime_pre_gt N B k h hk

/-- The first-passage location relation at natural threshold `B`. -/
def syracusePassLocationAtMost (B N M : ℕ) : Prop :=
  ∃ n, syracuseFirstHitAtMost B N n ∧ M = (syracuse^[n]) N

theorem syracusePassLocationAtMost_of_hitsAtMost (N B : ℕ)
    (h : syracuseHitsAtMost N B) :
    syracusePassLocationAtMost B N
      ((syracuse^[syracuseFirstPassageTime N B h]) N) := by
  exact ⟨syracuseFirstPassageTime N B h,
    syracuseFirstHitAtMost_of_hitsAtMost N B h, rfl⟩

/-- Total first-passage location with Tao's artificial no-hit value `1`. -/
noncomputable def syracusePassLocationAtMostOrOne
    (B N : ℕ) (hB : 1 ≤ B) : {M : ℕ // M ≤ B} := by
  classical
  exact
    if h : syracuseHitsAtMost N B then
      ⟨(syracuse^[syracuseFirstPassageTime N B h]) N,
        syracuseFirstPassageTime_spec N B h⟩
    else
      ⟨1, hB⟩

@[simp] theorem syracusePassLocationAtMostOrOne_of_hitsAtMost
    {B N : ℕ} (hB : 1 ≤ B) (h : syracuseHitsAtMost N B) :
    syracusePassLocationAtMostOrOne B N hB =
      ⟨(syracuse^[syracuseFirstPassageTime N B h]) N,
        syracuseFirstPassageTime_spec N B h⟩ := by
  simp [syracusePassLocationAtMostOrOne, h]

@[simp] theorem syracusePassLocationAtMostOrOne_of_not_hitsAtMost
    {B N : ℕ} (hB : 1 ≤ B) (h : ¬ syracuseHitsAtMost N B) :
    syracusePassLocationAtMostOrOne B N hB = ⟨1, hB⟩ := by
  simp [syracusePassLocationAtMostOrOne, h]

theorem syracuseFirstHitAtMost_unique {B N n m : ℕ}
    (hn : syracuseFirstHitAtMost B N n)
    (hm : syracuseFirstHitAtMost B N m) :
    n = m := by
  apply le_antisymm
  · exact Nat.le_of_not_gt fun hmn =>
      Nat.not_lt_of_ge hm.1 (hn.2 m hmn)
  · exact Nat.le_of_not_gt fun hnm =>
      Nat.not_lt_of_ge hn.1 (hm.2 n hnm)

theorem syracuseFirstHitAtMost_tail {B N n r : ℕ}
    (h : syracuseFirstHitAtMost B N n) (hr : r ≤ n) :
    syracuseFirstHitAtMost B ((syracuse^[r]) N) (n - r) := by
  constructor
  · have hiter :
        (syracuse^[n - r]) ((syracuse^[r]) N) = (syracuse^[n]) N := by
      rw [← Function.iterate_add_apply]
      rw [Nat.sub_add_cancel hr]
    simpa [hiter] using h.1
  · intro k hk
    have hk_total : k + r < n := by omega
    have hiter :
        (syracuse^[k]) ((syracuse^[r]) N) = (syracuse^[k + r]) N := by
      rw [← Function.iterate_add_apply]
    simpa [hiter] using h.2 (k + r) hk_total

theorem syracuseFirstHitAtMost_of_tail {B N r t : ℕ}
    (hpre : ∀ k < r, B < (syracuse^[k]) N)
    (htail : syracuseFirstHitAtMost B ((syracuse^[r]) N) t) :
    syracuseFirstHitAtMost B N (r + t) := by
  constructor
  · have hiter :
        (syracuse^[r + t]) N = (syracuse^[t]) ((syracuse^[r]) N) := by
      rw [Nat.add_comm r t, Function.iterate_add_apply]
    simpa [hiter] using htail.1
  · intro k hk
    by_cases hkr : k < r
    · exact hpre k hkr
    · have hrk : r ≤ k := Nat.le_of_not_gt hkr
      let j := k - r
      have hj : j < t := by
        dsimp [j]
        omega
      have hjr : j + r = k := by
        dsimp [j]
        omega
      have hiter :
          (syracuse^[j]) ((syracuse^[r]) N) = (syracuse^[j + r]) N := by
        rw [← Function.iterate_add_apply]
      simpa [hiter, hjr] using htail.2 j hj

/-- Split a first hit into the strict prefix before a chosen tail and the
first hit inside that tail. -/
theorem syracuseFirstHitAtMost_iff_prefix_tail
    {B N n m : ℕ} (hm : m ≤ n) :
    syracuseFirstHitAtMost B N n ↔
      (∀ k < n - m, B < (syracuse^[k]) N) ∧
        syracuseFirstHitAtMost B ((syracuse^[n - m]) N) m := by
  constructor
  · intro h
    constructor
    · intro k hk
      exact h.2 k (lt_of_lt_of_le hk (Nat.sub_le n m))
    · simpa [Nat.sub_sub_self hm] using
        syracuseFirstHitAtMost_tail h (Nat.sub_le n m)
  · rintro ⟨hpre, htail⟩
    simpa [Nat.sub_add_cancel hm] using
      syracuseFirstHitAtMost_of_tail hpre htail

end Tao
end Erdos1135
