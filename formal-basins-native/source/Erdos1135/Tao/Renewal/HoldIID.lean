import Erdos1135.Tao.Renewal.HoldPMF
import Erdos1135.Tao.Renewal.QFinite

/-!
# Section 7 Finite IID Hold Lists

This module defines finite iid lists from Tao's `Hold` law and finite
expectation-on-a-finset adapters for the deterministic `QFinite` recursion.  It
does not define the infinite renewal process, prove a tail estimate, or prove
Proposition 7.3.
-/

open scoped BigOperators

namespace Erdos1135
namespace Tao

/-- Finite iid lists sampled from Tao's Section 7 `Hold` PMF. -/
noncomputable def taoSection7HoldListPMF : ℕ → PMF (List TaoSection7RenewalPoint)
  | 0 => PMF.pure []
  | n + 1 => taoSection7HoldPMF.bind fun h =>
      (taoSection7HoldListPMF n).map fun hs => h :: hs

/-- Finite iid lists sampled from the source-prefix carrier below the `Hold` law. -/
noncomputable def taoSection7HoldSourcePrefixListPMF :
    ℕ → PMF (List (ℕ × List ℕ))
  | 0 => PMF.pure []
  | n + 1 => taoSection7HoldSourcePrefixPMF.bind fun x =>
      (taoSection7HoldSourcePrefixListPMF n).map fun xs => x :: xs

/--
The finite iid source-prefix carrier pushes forward to the finite iid `Hold`
list law.

This is the list-level lift of `taoSection7HoldPMF_eq_sourcePrefixPMF_map`.
-/
theorem taoSection7HoldSourcePrefixListPMF_map_holdPoint_eq
    (N : ℕ) :
    (taoSection7HoldSourcePrefixListPMF N).map
      (fun xs => xs.map fun x => taoSection7HoldPointOfPrefix x.1 x.2) =
    taoSection7HoldListPMF N := by
  induction N with
  | zero =>
      change PMF.map (fun xs : List (ℕ × List ℕ) =>
          xs.map fun x => taoSection7HoldPointOfPrefix x.1 x.2) (PMF.pure []) =
        PMF.pure ([] : List TaoSection7RenewalPoint)
      rw [← PMF.bind_pure_comp]
      rw [PMF.pure_bind]
      rfl
  | succ N ih =>
      change PMF.map (fun xs : List (ℕ × List ℕ) =>
            xs.map fun x => taoSection7HoldPointOfPrefix x.1 x.2)
          (taoSection7HoldSourcePrefixPMF.bind fun x =>
            (taoSection7HoldSourcePrefixListPMF N).map fun xs => x :: xs) =
        taoSection7HoldPMF.bind fun h =>
          (taoSection7HoldListPMF N).map fun hs => h :: hs
      rw [PMF.map_bind]
      rw [taoSection7HoldPMF_eq_sourcePrefixPMF_map]
      rw [PMF.bind_map]
      congr
      funext x
      calc
        PMF.map (fun xs : List (ℕ × List ℕ) =>
            xs.map fun x => taoSection7HoldPointOfPrefix x.1 x.2)
            (PMF.map (fun xs : List (ℕ × List ℕ) => x :: xs)
              (taoSection7HoldSourcePrefixListPMF N))
            = PMF.map
                ((fun xs : List (ℕ × List ℕ) =>
                  xs.map fun x => taoSection7HoldPointOfPrefix x.1 x.2) ∘
                    (fun xs : List (ℕ × List ℕ) => x :: xs))
                (taoSection7HoldSourcePrefixListPMF N) := by
              rw [PMF.map_comp]
        _ = PMF.map
              (fun xs : List (ℕ × List ℕ) =>
                taoSection7HoldPointOfPrefix x.1 x.2 ::
                  xs.map fun x => taoSection7HoldPointOfPrefix x.1 x.2)
              (taoSection7HoldSourcePrefixListPMF N) := by
              apply congrArg
                (fun f => PMF.map f (taoSection7HoldSourcePrefixListPMF N))
              funext xs
              simp [Function.comp_apply]
        _ = PMF.map
              ((fun hs : List TaoSection7RenewalPoint =>
                  taoSection7HoldPointOfPrefix x.1 x.2 :: hs) ∘
                (fun xs : List (ℕ × List ℕ) =>
                  xs.map fun x => taoSection7HoldPointOfPrefix x.1 x.2))
              (taoSection7HoldSourcePrefixListPMF N) := rfl
        _ = PMF.map
              (fun hs : List TaoSection7RenewalPoint =>
                  taoSection7HoldPointOfPrefix x.1 x.2 :: hs)
              (PMF.map
                (fun xs : List (ℕ × List ℕ) =>
                  xs.map fun x => taoSection7HoldPointOfPrefix x.1 x.2)
                (taoSection7HoldSourcePrefixListPMF N)) := by
              rw [← PMF.map_comp]
        _ = PMF.map
              (fun hs : List TaoSection7RenewalPoint =>
                  taoSection7HoldPointOfPrefix x.1 x.2 :: hs)
              (taoSection7HoldListPMF N) := by
              rw [ih]

theorem taoSection7HoldSourcePrefixListPMF_zero_apply_cons
    (x : ℕ × List ℕ) (xs : List (ℕ × List ℕ)) :
    taoSection7HoldSourcePrefixListPMF 0 (x :: xs) = 0 := by
  simp [taoSection7HoldSourcePrefixListPMF]

theorem taoSection7HoldSourcePrefixListPMF_succ_apply_cons
    (n : ℕ) (x : ℕ × List ℕ) (xs : List (ℕ × List ℕ)) :
    taoSection7HoldSourcePrefixListPMF (n + 1) (x :: xs) =
      taoSection7HoldSourcePrefixPMF x *
        taoSection7HoldSourcePrefixListPMF n xs := by
  classical
  rw [taoSection7HoldSourcePrefixListPMF, PMF.bind_apply]
  have hmap : ∀ x' : ℕ × List ℕ,
      ((taoSection7HoldSourcePrefixListPMF n).map fun ys => x' :: ys) (x :: xs) =
        if x = x' then taoSection7HoldSourcePrefixListPMF n xs else 0 := by
    intro x'
    rw [PMF.map_apply]
    by_cases hx : x = x'
    · subst hx
      rw [tsum_eq_single xs]
      · simp
      · intro ys hys
        have hc : ¬ x :: xs = x :: ys := by
          intro hcons
          exact hys (List.cons.inj hcons).2.symm
        simp [hc]
    · have hnone : ∀ ys : List (ℕ × List ℕ), ¬ x :: xs = x' :: ys := by
        intro ys hcons
        exact hx (List.cons.inj hcons).1
      simp [hx, hnone]
  calc
    (∑' x' : ℕ × List ℕ,
        taoSection7HoldSourcePrefixPMF x' *
          ((taoSection7HoldSourcePrefixListPMF n).map fun ys => x' :: ys) (x :: xs))
        = ∑' x' : ℕ × List ℕ,
            taoSection7HoldSourcePrefixPMF x' *
              (if x = x' then taoSection7HoldSourcePrefixListPMF n xs else 0) := by
          apply tsum_congr
          intro x'
          rw [hmap x']
    _ = taoSection7HoldSourcePrefixPMF x *
          taoSection7HoldSourcePrefixListPMF n xs := by
          rw [tsum_eq_single x]
          · simp
          · intro x' hx'
            simp [hx'.symm]

theorem taoSection7HoldSourcePrefixListPMF_succ_apply_nil (n : ℕ) :
    taoSection7HoldSourcePrefixListPMF (n + 1) [] = 0 := by
  classical
  rw [taoSection7HoldSourcePrefixListPMF, PMF.bind_apply]
  simp [PMF.map_apply]

theorem taoSection7HoldSourcePrefixListPMF_apply_eq_zero_of_length_ne
    (n : ℕ) (xs : List (ℕ × List ℕ)) (h : xs.length ≠ n) :
    taoSection7HoldSourcePrefixListPMF n xs = 0 := by
  induction n generalizing xs with
  | zero =>
      cases xs with
      | nil => exact (h rfl).elim
      | cons x xs => exact taoSection7HoldSourcePrefixListPMF_zero_apply_cons x xs
  | succ n ih =>
      cases xs with
      | nil =>
          exact taoSection7HoldSourcePrefixListPMF_succ_apply_nil n
      | cons x xs =>
          rw [taoSection7HoldSourcePrefixListPMF_succ_apply_cons]
          have htail : xs.length ≠ n := by
            intro hlen
            exact h (by simp [hlen])
          rw [ih xs htail, mul_zero]

theorem taoSection7HoldListPMF_zero_apply_nil :
    taoSection7HoldListPMF 0 [] = 1 := by
  simp [taoSection7HoldListPMF]

theorem taoSection7HoldListPMF_zero_apply_cons
    (h : TaoSection7RenewalPoint) (hs : List TaoSection7RenewalPoint) :
    taoSection7HoldListPMF 0 (h :: hs) = 0 := by
  simp [taoSection7HoldListPMF]

theorem taoSection7HoldListPMF_succ_apply_cons
    (n : ℕ) (h : TaoSection7RenewalPoint) (hs : List TaoSection7RenewalPoint) :
    taoSection7HoldListPMF (n + 1) (h :: hs) =
      taoSection7HoldPMF h * taoSection7HoldListPMF n hs := by
  classical
  rw [taoSection7HoldListPMF, PMF.bind_apply]
  have hmap : ∀ h' : TaoSection7RenewalPoint,
      ((taoSection7HoldListPMF n).map fun ts => h' :: ts) (h :: hs) =
        if h = h' then taoSection7HoldListPMF n hs else 0 := by
    intro h'
    rw [PMF.map_apply]
    by_cases hh : h = h'
    · subst hh
      rw [tsum_eq_single hs]
      · simp
      · intro ts hts
        have hc : ¬ h :: hs = h :: ts := by
          intro hcons
          exact hts (List.cons.inj hcons).2.symm
        simp [hc]
    · have hnone : ∀ ts : List TaoSection7RenewalPoint, ¬ h :: hs = h' :: ts := by
        intro ts hcons
        exact hh (List.cons.inj hcons).1
      simp [hh, hnone]
  calc
    (∑' h' : TaoSection7RenewalPoint,
        taoSection7HoldPMF h' *
          ((taoSection7HoldListPMF n).map fun ts => h' :: ts) (h :: hs))
        = ∑' h' : TaoSection7RenewalPoint,
            taoSection7HoldPMF h' *
              (if h = h' then taoSection7HoldListPMF n hs else 0) := by
          apply tsum_congr
          intro h'
          rw [hmap h']
    _ = taoSection7HoldPMF h * taoSection7HoldListPMF n hs := by
          rw [tsum_eq_single h]
          · simp
          · intro h' hh'
            simp [hh'.symm]

theorem taoSection7HoldListPMF_succ_apply_nil (n : ℕ) :
    taoSection7HoldListPMF (n + 1) [] = 0 := by
  classical
  rw [taoSection7HoldListPMF, PMF.bind_apply]
  simp [PMF.map_apply]

theorem taoSection7HoldListPMF_apply_eq_zero_of_length_ne
    (n : ℕ) (hs : List TaoSection7RenewalPoint) (h : hs.length ≠ n) :
    taoSection7HoldListPMF n hs = 0 := by
  induction n generalizing hs with
  | zero =>
      cases hs with
      | nil => exact (h rfl).elim
      | cons h hs => simp [taoSection7HoldListPMF]
  | succ n ih =>
      cases hs with
      | nil =>
          exact taoSection7HoldListPMF_succ_apply_nil n
      | cons h hs =>
          rw [taoSection7HoldListPMF_succ_apply_cons]
          have htail : hs.length ≠ n := by
            intro hlen
            exact h (by simp [hlen])
          rw [ih hs htail, mul_zero]

/--
Finite iid `Hold` prefix marginal.

Sampling a length `K + L` iid `Hold` list and retaining its first `K`
increments has the same law as sampling a length `K` iid `Hold` list.
-/
theorem taoSection7HoldListPMF_map_take_eq
    (K L : ℕ) :
    (taoSection7HoldListPMF (K + L)).map (fun hs => hs.take K) =
      taoSection7HoldListPMF K := by
  induction K with
  | zero =>
      rw [Nat.zero_add]
      change PMF.map (fun hs : List TaoSection7RenewalPoint => hs.take 0)
          (taoSection7HoldListPMF L) = PMF.pure []
      convert PMF.map_const (taoSection7HoldListPMF L)
        ([] : List TaoSection7RenewalPoint) using 1
  | succ K ih =>
      rw [Nat.succ_add]
      change PMF.map (fun hs : List TaoSection7RenewalPoint => hs.take (K + 1))
          (taoSection7HoldPMF.bind fun h =>
            (taoSection7HoldListPMF (K + L)).map fun hs => h :: hs) =
        taoSection7HoldPMF.bind fun h =>
          (taoSection7HoldListPMF K).map fun hs => h :: hs
      rw [PMF.map_bind]
      congr
      funext h
      calc
        PMF.map (fun hs : List TaoSection7RenewalPoint => hs.take (K + 1))
            (PMF.map (fun hs : List TaoSection7RenewalPoint => h :: hs)
              (taoSection7HoldListPMF (K + L)))
            = PMF.map
                ((fun hs : List TaoSection7RenewalPoint => hs.take (K + 1)) ∘
                  (fun hs : List TaoSection7RenewalPoint => h :: hs))
                (taoSection7HoldListPMF (K + L)) := by
              rw [PMF.map_comp]
        _ = PMF.map (fun hs : List TaoSection7RenewalPoint => h :: hs.take K)
              (taoSection7HoldListPMF (K + L)) := by
              apply congrArg
                (fun f => PMF.map f (taoSection7HoldListPMF (K + L)))
              funext hs
              rw [Function.comp_apply]
              rw [List.take_cons (Nat.succ_pos K)]
              simp
        _ = PMF.map ((fun hs : List TaoSection7RenewalPoint => h :: hs) ∘
                (fun hs : List TaoSection7RenewalPoint => hs.take K))
              (taoSection7HoldListPMF (K + L)) := rfl
        _ = PMF.map (fun hs : List TaoSection7RenewalPoint => h :: hs)
              (PMF.map (fun hs : List TaoSection7RenewalPoint => hs.take K)
                (taoSection7HoldListPMF (K + L))) := by
              rw [← PMF.map_comp]
        _ = PMF.map (fun hs : List TaoSection7RenewalPoint => h :: hs)
              (taoSection7HoldListPMF K) := by
              rw [ih]

/--
Deterministic prefix/future independence for a finite iid `Hold` list.

Splitting a length-`K+N` list after its first `K` increments has the same law
as independently sampling a length-`K` prefix and a length-`N` future block.
-/
theorem taoSection7HoldListPMF_map_take_drop_eq
    (K N : ℕ) :
    (taoSection7HoldListPMF (K + N)).map
        (fun full => (full.take K, full.drop K)) =
      (taoSection7HoldListPMF K).bind fun pre =>
        (taoSection7HoldListPMF N).map fun future => (pre, future) := by
  induction K with
  | zero =>
      rw [Nat.zero_add]
      change
        (taoSection7HoldListPMF N).map
            (fun full => (full.take 0, full.drop 0)) =
          (PMF.pure []).bind fun pre =>
            (taoSection7HoldListPMF N).map fun future => (pre, future)
      rw [PMF.pure_bind]
      apply congrArg (fun f => (taoSection7HoldListPMF N).map f)
      funext full
      simp
  | succ K ih =>
      rw [Nat.succ_add]
      change
        (taoSection7HoldPMF.bind fun h =>
            (taoSection7HoldListPMF (K + N)).map fun hs => h :: hs).map
            (fun full => (full.take (K + 1), full.drop (K + 1))) =
          (taoSection7HoldPMF.bind fun h =>
            (taoSection7HoldListPMF K).map fun hs => h :: hs).bind fun pre =>
              (taoSection7HoldListPMF N).map fun future => (pre, future)
      rw [PMF.map_bind, PMF.bind_bind]
      congr
      funext h
      calc
        ((taoSection7HoldListPMF (K + N)).map fun hs => h :: hs).map
            (fun full => (full.take (K + 1), full.drop (K + 1))) =
            (taoSection7HoldListPMF (K + N)).map
              (fun hs => (h :: hs.take K, hs.drop K)) := by
                rw [PMF.map_comp]
                apply congrArg
                  (fun f => (taoSection7HoldListPMF (K + N)).map f)
                funext hs
                simp [Function.comp_apply]
        _ = ((taoSection7HoldListPMF (K + N)).map
              (fun hs => (hs.take K, hs.drop K))).map
              (fun pair => (h :: pair.1, pair.2)) := by
                rw [PMF.map_comp]
                apply congrArg
                  (fun f => (taoSection7HoldListPMF (K + N)).map f)
                funext hs
                rfl
        _ = ((taoSection7HoldListPMF K).bind fun pre =>
              (taoSection7HoldListPMF N).map fun future =>
                (pre, future)).map
              (fun pair => (h :: pair.1, pair.2)) := by
                rw [ih]
        _ = (taoSection7HoldListPMF K).bind fun pre =>
              (taoSection7HoldListPMF N).map fun future =>
                (h :: pre, future) := by
                rw [PMF.map_bind]
                congr
                funext pre
                rw [PMF.map_comp]
                apply congrArg
                  (fun f => (taoSection7HoldListPMF N).map f)
                funext future
                rfl
        _ = ((taoSection7HoldListPMF K).map fun pre => h :: pre).bind
              (fun pre =>
                (taoSection7HoldListPMF N).map fun future =>
                  (pre, future)) := by
                rw [PMF.bind_map]
                rfl

/-- Finite iid `Hold` prefix marginal with an arbitrary longer horizon. -/
theorem taoSection7HoldListPMF_map_take_eq_of_le
    {K N : ℕ} (hK : K ≤ N) :
    (taoSection7HoldListPMF N).map (fun hs => hs.take K) =
      taoSection7HoldListPMF K := by
  rw [← Nat.add_sub_of_le hK]
  exact taoSection7HoldListPMF_map_take_eq K (N - K)

/-- Pointwise real-valued form of the finite iid `Hold` prefix marginal. -/
theorem taoSection7HoldListPMF_map_take_apply_toReal_eq_of_le
    {K N : ℕ} (hK : K ≤ N)
    (hs : List TaoSection7RenewalPoint) :
    (((taoSection7HoldListPMF N).map
        (fun full : List TaoSection7RenewalPoint => full.take K)) hs).toReal =
      (taoSection7HoldListPMF K hs).toReal := by
  rw [taoSection7HoldListPMF_map_take_eq_of_le hK]

/-- Prefix form of the finite iid source-prefix carrier pushforward law. -/
theorem taoSection7HoldSourcePrefixListPMF_map_take_holdPoint_eq_of_le
    {n N : ℕ} (hn : n ≤ N) :
    (taoSection7HoldSourcePrefixListPMF N).map
      (fun xs =>
        (xs.map fun x => taoSection7HoldPointOfPrefix x.1 x.2).take n) =
    taoSection7HoldListPMF n := by
  change PMF.map
      ((fun hs : List TaoSection7RenewalPoint => hs.take n) ∘
        (fun xs : List (ℕ × List ℕ) =>
          xs.map fun x => taoSection7HoldPointOfPrefix x.1 x.2))
      (taoSection7HoldSourcePrefixListPMF N) = taoSection7HoldListPMF n
  rw [← PMF.map_comp]
  rw [taoSection7HoldSourcePrefixListPMF_map_holdPoint_eq]
  exact taoSection7HoldListPMF_map_take_eq_of_le hn

/-- A finite iid `Hold` list has zero mass if one increment has negative vertical coordinate. -/
theorem taoSection7HoldListPMF_apply_eq_zero_of_exists_l_neg
    {n : ℕ} {hs : List TaoSection7RenewalPoint}
    (hbad : ∃ h, h ∈ hs ∧ h.l < 0) :
    taoSection7HoldListPMF n hs = 0 := by
  induction n generalizing hs with
  | zero =>
      cases hs with
      | nil =>
          rcases hbad with ⟨h, hmem, _hl⟩
          cases hmem
      | cons h hs =>
          exact taoSection7HoldListPMF_zero_apply_cons h hs
  | succ n ih =>
      cases hs with
      | nil =>
          rcases hbad with ⟨h, hmem, _hl⟩
          cases hmem
      | cons h hs =>
          rw [taoSection7HoldListPMF_succ_apply_cons]
          rcases hbad with ⟨hbad, hmem, hneg⟩
          rcases List.mem_cons.mp hmem with rfl | htail
          · rw [taoSection7HoldPMF_apply_eq_zero_of_l_neg hneg, zero_mul]
          · have htail_zero :
                taoSection7HoldListPMF n hs = 0 :=
              ih ⟨hbad, htail, hneg⟩
            rw [htail_zero, mul_zero]

/-- Real-valued zero-mass form for iid `Hold` lists with a negative vertical increment. -/
theorem taoSection7HoldListPMF_toReal_eq_zero_of_exists_l_neg
    {n : ℕ} {hs : List TaoSection7RenewalPoint}
    (hbad : ∃ h, h ∈ hs ∧ h.l < 0) :
    (taoSection7HoldListPMF n hs).toReal = 0 := by
  rw [taoSection7HoldListPMF_apply_eq_zero_of_exists_l_neg hbad]
  rfl

/-- Product of Hold point masses along a finite list. -/
noncomputable def taoSection7HoldListMass
    (hs : List TaoSection7RenewalPoint) : ℝ :=
  (hs.map fun h => (taoSection7HoldPMF h).toReal).prod

theorem taoSection7HoldListPMF_apply_length_toReal
    (hs : List TaoSection7RenewalPoint) :
    (taoSection7HoldListPMF hs.length hs).toReal =
      taoSection7HoldListMass hs := by
  induction hs with
  | nil =>
      simp [taoSection7HoldListPMF, taoSection7HoldListMass]
  | cons h hs ih =>
      rw [List.length_cons, taoSection7HoldListPMF_succ_apply_cons]
      rw [ENNReal.toReal_mul, ih]
      simp [taoSection7HoldListMass]

/-- Nonzero iid `Hold` list mass implies all vertical increments are nonnegative. -/
theorem taoSection7HoldListPMF_ne_zero_all_l_nonneg
    {n : ℕ} {hs : List TaoSection7RenewalPoint}
    (hmass : (taoSection7HoldListPMF n hs).toReal ≠ 0) :
    ∀ h, h ∈ hs → 0 ≤ h.l := by
  intro h hmem
  by_contra hnonneg
  exact hmass
    (taoSection7HoldListPMF_toReal_eq_zero_of_exists_l_neg
      (n := n) (hs := hs) ⟨h, hmem, lt_of_not_ge hnonneg⟩)

/-- Finite expectation over a chosen support set of Hold lists. -/
noncomputable def taoSection7HoldListExpectationOn
    (K : ℕ) (S : Finset (List TaoSection7RenewalPoint))
    (F : List TaoSection7RenewalPoint → ℝ) : ℝ :=
  ∑ hs ∈ S, (taoSection7HoldListPMF K hs).toReal * F hs

/-- Finite expectation surface for `QFinite` over iid Hold lists. -/
noncomputable def taoSection7QFiniteHoldExpectationOn
    (K : ℕ) (S : Finset (List TaoSection7RenewalPoint))
    (epsilon : ℝ) (W : TaoSection7RenewalPoint → Prop)
    (p : TaoSection7RenewalPoint) : ℝ :=
  taoSection7HoldListExpectationOn K S
    (fun hs => taoSection7QFinite epsilon W p hs)

theorem taoSection7HoldListExpectationOn_nonneg
    {K : ℕ} {S : Finset (List TaoSection7RenewalPoint)}
    {F : List TaoSection7RenewalPoint → ℝ}
    (hF : ∀ hs ∈ S, 0 ≤ F hs) :
    0 ≤ taoSection7HoldListExpectationOn K S F := by
  classical
  unfold taoSection7HoldListExpectationOn
  exact Finset.sum_nonneg (by
    intro hs hS
    have hmass : 0 ≤ (taoSection7HoldListPMF K hs).toReal :=
      ENNReal.toReal_nonneg
    exact mul_nonneg hmass (hF hs hS))

theorem taoSection7QFiniteHoldExpectationOn_nonneg
    (K : ℕ) (S : Finset (List TaoSection7RenewalPoint))
    (epsilon : ℝ) (W : TaoSection7RenewalPoint → Prop)
    (p : TaoSection7RenewalPoint) :
    0 ≤ taoSection7QFiniteHoldExpectationOn K S epsilon W p := by
  exact taoSection7HoldListExpectationOn_nonneg (by
    intro hs _hS
    exact taoSection7QFinite_nonneg epsilon W p hs)

theorem taoSection7HoldListExpectationOn_le_mass
    {K : ℕ} {S : Finset (List TaoSection7RenewalPoint)}
    {F : List TaoSection7RenewalPoint → ℝ}
    (hF1 : ∀ hs ∈ S, F hs ≤ 1) :
    taoSection7HoldListExpectationOn K S F ≤
      ∑ hs ∈ S, (taoSection7HoldListPMF K hs).toReal := by
  classical
  unfold taoSection7HoldListExpectationOn
  exact Finset.sum_le_sum (by
    intro hs hS
    calc
      (taoSection7HoldListPMF K hs).toReal * F hs
          ≤ (taoSection7HoldListPMF K hs).toReal * 1 := by
            have hmass : 0 ≤ (taoSection7HoldListPMF K hs).toReal :=
              ENNReal.toReal_nonneg
            exact mul_le_mul_of_nonneg_left (hF1 hs hS) hmass
      _ = (taoSection7HoldListPMF K hs).toReal := by ring)

theorem taoSection7QFiniteHoldExpectationOn_le_mass
    {K : ℕ} {S : Finset (List TaoSection7RenewalPoint)}
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (W : TaoSection7RenewalPoint → Prop) (p : TaoSection7RenewalPoint) :
    taoSection7QFiniteHoldExpectationOn K S epsilon W p ≤
      ∑ hs ∈ S, (taoSection7HoldListPMF K hs).toReal := by
  exact taoSection7HoldListExpectationOn_le_mass
    (by
      intro hs _hS
      exact taoSection7QFinite_le_one hepsilon W p hs)

theorem taoSection7QFiniteHoldExpectationOn_le_one_of_mass_le_one
    {K : ℕ} {S : Finset (List TaoSection7RenewalPoint)}
    {epsilon : ℝ} (hepsilon : 0 ≤ epsilon)
    (W : TaoSection7RenewalPoint → Prop) (p : TaoSection7RenewalPoint)
    (hS : (∑ hs ∈ S, (taoSection7HoldListPMF K hs).toReal) ≤ 1) :
    taoSection7QFiniteHoldExpectationOn K S epsilon W p ≤ 1 :=
  (taoSection7QFiniteHoldExpectationOn_le_mass hepsilon W p).trans hS

end Tao
end Erdos1135
