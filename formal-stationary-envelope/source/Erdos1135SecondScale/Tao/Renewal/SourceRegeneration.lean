/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Fourier.Section7PairFiber
import Erdos1135SecondScale.Tao.Renewal.HoldIID
import Erdos1135SecondScale.Tao.Renewal.SourceListBridge

/-!
# Section 7 Raw Pascal Regeneration

This leaf isolates the probability law that reconstructs a raw Pascal prefix
from iid first-hit source blocks. It deliberately precedes all Q-finite and
Fourier expectation comparisons.
-/

namespace Erdos1135SecondScale
namespace Tao

private theorem taoSection7Geom4MissMass_succ_regeneration (m : ℕ) :
    taoSection7Geom4MissMass (m + 1) =
      (3 / 4 : ℝ) * taoSection7Geom4MissMass m := by
  unfold taoSection7Geom4MissMass
  rw [pow_succ]
  ring

private theorem taoSection7HoldSourcePrefixPMF_apply_eq_zero_of_length_ne
    (m : ℕ) (pre : List ℕ) (h : pre.length ≠ m) :
    taoSection7HoldSourcePrefixPMF (m, pre) = 0 := by
  rw [taoSection7HoldSourcePrefixPMF_apply,
    taoSection7PascalPrimeSourceListPMF_apply_eq_zero_of_length_ne m pre h,
    mul_zero]

private theorem taoSection7HoldSourcePrefixPMF_succ_three
    (m : ℕ) (pre : List ℕ) :
    taoSection7HoldSourcePrefixPMF (m + 1, 3 :: pre) = 0 := by
  rw [taoSection7HoldSourcePrefixPMF_apply,
    taoSection7PascalPrimeSourceListPMF_succ_apply_cons,
    taoSection7PascalPrimeSourcePMF_three,
    zero_mul, mul_zero]

private theorem taoSection7HoldSourcePrefixPMF_succ_cons_toReal
    (m b : ℕ) (pre : List ℕ) (hb : b ≠ 3) :
    (taoSection7HoldSourcePrefixPMF (m + 1, b :: pre)).toReal =
      (taoSection7PascalSourcePMF b).toReal *
        (taoSection7HoldSourcePrefixPMF (m, pre)).toReal := by
  rw [taoSection7HoldSourcePrefixPMF_apply_toReal,
    taoSection7HoldSourcePrefixPMF_apply_toReal,
    taoSection7PascalPrimeSourceListPMF_succ_apply_cons,
    ENNReal.toReal_mul,
    taoSection7Geom4MissMass_succ_regeneration,
    taoSection7PascalPrimeSourcePMF_apply_toReal,
    taoSection7PascalPrimeSourceMass_of_ne_three hb,
    taoSection7PascalSourcePMF_apply_toReal]
  ring

private noncomputable def taoSection7HoldSourcePrefixRegeneratedPMF :
    PMF (ℕ × List ℕ) :=
  taoSection7PascalSourcePMF.bind fun b =>
    if b = 3 then
      PMF.pure (0, [])
    else
      taoSection7HoldSourcePrefixPMF.map fun x =>
        (x.1 + 1, b :: x.2)

private theorem taoSection7HoldSourcePrefixPMF_map_miss_apply
    (c m b : ℕ) (pre : List ℕ) :
    (taoSection7HoldSourcePrefixPMF.map
        (fun x => (x.1 + 1, c :: x.2))) (m + 1, b :: pre) =
      if b = c then taoSection7HoldSourcePrefixPMF (m, pre) else 0 := by
  classical
  rw [PMF.map_apply]
  by_cases hbc : b = c
  · subst c
    rw [tsum_eq_single (m, pre)]
    · simp
    · rintro ⟨k, xs⟩ hne
      have hpair : ¬(m + 1, b :: pre) = (k + 1, b :: xs) := by
        intro h
        have hk : m = k := by
          have := congrArg Prod.fst h
          omega
        have hxs : pre = xs := (List.cons.inj (congrArg Prod.snd h)).2
        exact hne (Prod.ext hk hxs).symm
      simp [hpair]
  · rw [if_neg hbc, ENNReal.tsum_eq_zero]
    rintro ⟨k, xs⟩
    have hpair : ¬(m + 1, b :: pre) = (k + 1, c :: xs) := by
      intro h
      exact hbc (List.cons.inj (congrArg Prod.snd h)).1
    simp [hpair]

private theorem taoSection7HoldSourcePrefixRegeneratedPMF_succ_cons_apply
    (m b : ℕ) (pre : List ℕ) :
    taoSection7HoldSourcePrefixRegeneratedPMF (m + 1, b :: pre) =
      if b = 3 then 0 else
        taoSection7PascalSourcePMF b *
          taoSection7HoldSourcePrefixPMF (m, pre) := by
  classical
  rw [taoSection7HoldSourcePrefixRegeneratedPMF, PMF.bind_apply]
  by_cases hb : b = 3
  · subst b
    rw [if_pos rfl, ENNReal.tsum_eq_zero]
    intro c
    by_cases hc : c = 3
    · subst c
      simp
    · rw [if_neg hc, taoSection7HoldSourcePrefixPMF_map_miss_apply]
      simp [Ne.symm hc]
  · rw [if_neg hb, tsum_eq_single b]
    · rw [if_neg hb, taoSection7HoldSourcePrefixPMF_map_miss_apply]
      simp
    · intro c hcb
      by_cases hc : c = 3
      · subst c
        simp
      · rw [if_neg hc, taoSection7HoldSourcePrefixPMF_map_miss_apply]
        simp [Ne.symm hcb]

private theorem taoSection7HoldSourcePrefixRegeneratedPMF_zero_nil_apply :
    taoSection7HoldSourcePrefixRegeneratedPMF (0, []) =
      taoSection7PascalSourcePMF 3 := by
  classical
  rw [taoSection7HoldSourcePrefixRegeneratedPMF, PMF.bind_apply,
    tsum_eq_single 3]
  · simp
  · intro c hc
    by_cases hc3 : c = 3
    · exact (hc hc3).elim
    · rw [if_neg hc3]
      have hmap :
          (taoSection7HoldSourcePrefixPMF.map fun x =>
            (x.1 + 1, c :: x.2)) (0, []) = 0 := by
        rw [PMF.map_apply, ENNReal.tsum_eq_zero]
        intro x
        have hpair : ¬(0, []) = (x.1 + 1, c :: x.2) := by
          intro h
          have := congrArg Prod.fst h
          omega
        simp [hpair]
      rw [hmap, mul_zero]

private theorem taoSection7HoldSourcePrefixRegeneratedPMF_zero_cons_apply
    (b : ℕ) (pre : List ℕ) :
    taoSection7HoldSourcePrefixRegeneratedPMF (0, b :: pre) = 0 := by
  classical
  rw [taoSection7HoldSourcePrefixRegeneratedPMF, PMF.bind_apply,
    ENNReal.tsum_eq_zero]
  intro c
  by_cases hc3 : c = 3
  · subst c
    simp
  · rw [if_neg hc3]
    have hmap :
        (taoSection7HoldSourcePrefixPMF.map fun x =>
          (x.1 + 1, c :: x.2)) (0, b :: pre) = 0 := by
      rw [PMF.map_apply, ENNReal.tsum_eq_zero]
      intro x
      have hpair : ¬(0, b :: pre) = (x.1 + 1, c :: x.2) := by
        intro h
        have := congrArg Prod.fst h
        omega
      simp [hpair]
    rw [hmap, mul_zero]

private theorem taoSection7HoldSourcePrefixRegeneratedPMF_succ_nil_apply
    (m : ℕ) :
    taoSection7HoldSourcePrefixRegeneratedPMF (m + 1, []) = 0 := by
  classical
  rw [taoSection7HoldSourcePrefixRegeneratedPMF, PMF.bind_apply,
    ENNReal.tsum_eq_zero]
  intro c
  by_cases hc3 : c = 3
  · subst c
    simp
  · rw [if_neg hc3]
    have hmap :
        (taoSection7HoldSourcePrefixPMF.map fun x =>
          (x.1 + 1, c :: x.2)) (m + 1, []) = 0 := by
      rw [PMF.map_apply, ENNReal.tsum_eq_zero]
      intro x
      have hpair : ¬(m + 1, []) = (x.1 + 1, c :: x.2) := by
        intro h
        have hfalse : False := by
          simpa using congrArg (fun y : ℕ × List ℕ => y.2) h
        exact hfalse.elim
      simp [hpair]
    rw [hmap, mul_zero]

/-- Exposing the first raw Pascal symbol of a Hold source block either hits
`3` immediately or refreshes the same block after one miss. -/
theorem taoSection7HoldSourcePrefixPMF_eq_pascalSource_bind :
    taoSection7HoldSourcePrefixPMF =
      taoSection7PascalSourcePMF.bind fun b =>
        if b = 3 then
          PMF.pure (0, [])
        else
          taoSection7HoldSourcePrefixPMF.map fun x =>
            (x.1 + 1, b :: x.2) := by
  classical
  change taoSection7HoldSourcePrefixPMF =
    taoSection7HoldSourcePrefixRegeneratedPMF
  apply PMF.ext
  rintro ⟨m, pre⟩
  cases m with
  | zero =>
      cases pre with
      | nil =>
          rw [taoSection7HoldSourcePrefixRegeneratedPMF_zero_nil_apply]
          apply (ENNReal.toReal_eq_toReal_iff'
            (PMF.apply_ne_top _ _) (PMF.apply_ne_top _ _)).mp
          rw [taoSection7HoldSourcePrefixPMF_apply_toReal,
            taoSection7PascalSourcePMF_three_toReal]
          norm_num [taoSection7Geom4MissMass,
            taoSection7PascalPrimeSourceListPMF]
      | cons b pre =>
          rw [taoSection7HoldSourcePrefixPMF_apply_eq_zero_of_length_ne,
            taoSection7HoldSourcePrefixRegeneratedPMF_zero_cons_apply]
          simp
  | succ m =>
      cases pre with
      | nil =>
          rw [taoSection7HoldSourcePrefixPMF_apply_eq_zero_of_length_ne,
            taoSection7HoldSourcePrefixRegeneratedPMF_succ_nil_apply]
          simp
      | cons b pre =>
          rw [taoSection7HoldSourcePrefixRegeneratedPMF_succ_cons_apply]
          by_cases hb : b = 3
          · subst b
            rw [if_pos rfl, taoSection7HoldSourcePrefixPMF_succ_three]
          · rw [if_neg hb]
            apply (ENNReal.toReal_eq_toReal_iff'
              (PMF.apply_ne_top _ _)
              (ENNReal.mul_ne_top
                (PMF.apply_ne_top _ _)
                (PMF.apply_ne_top _ _))).mp
            rw [ENNReal.toReal_mul]
            exact taoSection7HoldSourcePrefixPMF_succ_cons_toReal m b pre hb

/-- The first `J` raw Pascal symbols exposed by a list of complete Hold source
blocks. A final partial block is retained by `take`. -/
def taoSection7RawPrefixOfHoldBlocks
    (J : ℕ) (xs : List (ℕ × List ℕ)) : List ℕ :=
  (taoSection7SourceBlocks (xs.map Prod.snd)).take J

@[simp] theorem taoSection7RawPrefixOfHoldBlocks_zero
    (xs : List (ℕ × List ℕ)) :
    taoSection7RawPrefixOfHoldBlocks 0 xs = [] := by
  simp [taoSection7RawPrefixOfHoldBlocks]

@[simp] theorem taoSection7RawPrefixOfHoldBlocks_hit
    (J : ℕ) (xs : List (ℕ × List ℕ)) :
    taoSection7RawPrefixOfHoldBlocks (J + 1) ((0, []) :: xs) =
      3 :: taoSection7RawPrefixOfHoldBlocks J xs := by
  simp [taoSection7RawPrefixOfHoldBlocks, taoSection7SourceBlocks]

@[simp] theorem taoSection7RawPrefixOfHoldBlocks_miss
    (J m b : ℕ) (pre : List ℕ) (xs : List (ℕ × List ℕ)) :
    taoSection7RawPrefixOfHoldBlocks (J + 1) ((m + 1, b :: pre) :: xs) =
      b :: taoSection7RawPrefixOfHoldBlocks J ((m, pre) :: xs) := by
  simp [taoSection7RawPrefixOfHoldBlocks, taoSection7SourceBlocks]

private theorem
    taoSection7HoldSourcePrefixListPMF_map_rawPrefix_succ_expose
    (J N : ℕ) :
    (taoSection7HoldSourcePrefixListPMF (N + 1)).map
        (taoSection7RawPrefixOfHoldBlocks (J + 1)) =
      taoSection7PascalSourcePMF.bind fun b =>
        if b = 3 then
          ((taoSection7HoldSourcePrefixListPMF N).map
              (taoSection7RawPrefixOfHoldBlocks J)).map
            (fun bs => b :: bs)
        else
          ((taoSection7HoldSourcePrefixListPMF (N + 1)).map
              (taoSection7RawPrefixOfHoldBlocks J)).map
            (fun bs => b :: bs) := by
  change
    PMF.map (taoSection7RawPrefixOfHoldBlocks (J + 1))
        (taoSection7HoldSourcePrefixPMF.bind fun x =>
          (taoSection7HoldSourcePrefixListPMF N).map fun xs => x :: xs) = _
  rw [PMF.map_bind, taoSection7HoldSourcePrefixPMF_eq_pascalSource_bind,
    PMF.bind_bind]
  apply congrArg
    (fun f : ℕ → PMF (List ℕ) => taoSection7PascalSourcePMF.bind f)
  funext b
  by_cases hb : b = 3
  · subst b
    rw [if_pos rfl, PMF.pure_bind, PMF.map_comp, PMF.map_comp]
    apply congrArg
      (fun f => (taoSection7HoldSourcePrefixListPMF N).map f)
    funext xs
    simp [Function.comp_apply]
  · simp only [if_neg hb]
    rw [PMF.bind_map]
    change
      taoSection7HoldSourcePrefixPMF.bind
          (fun x =>
            PMF.map (taoSection7RawPrefixOfHoldBlocks (J + 1))
              ((taoSection7HoldSourcePrefixListPMF N).map
                (fun xs => (x.1 + 1, b :: x.2) :: xs))) =
        PMF.map (fun bs => b :: bs)
          (PMF.map (taoSection7RawPrefixOfHoldBlocks J)
            (taoSection7HoldSourcePrefixPMF.bind fun x =>
              (taoSection7HoldSourcePrefixListPMF N).map
                (fun xs => x :: xs)))
    rw [PMF.map_comp, PMF.map_bind]
    apply congrArg
      (fun f : (ℕ × List ℕ) → PMF (List ℕ) =>
        taoSection7HoldSourcePrefixPMF.bind f)
    funext x
    rw [PMF.map_comp, PMF.map_comp]
    apply congrArg
      (fun f => (taoSection7HoldSourcePrefixListPMF N).map f)
    funext xs
    simp [Function.comp_apply]

/-- Any `N` complete Hold source blocks expose the exact iid raw Pascal law
on their first `J` symbols when `J ≤ N`. The current block is retained across
a miss, so this includes the positive no-hit mass and prefixes ending inside a
block. -/
theorem taoSection7HoldSourcePrefixListPMF_map_rawPrefix_eq_of_le
    (J N : ℕ) (hJN : J ≤ N) :
    (taoSection7HoldSourcePrefixListPMF N).map
        (taoSection7RawPrefixOfHoldBlocks J) =
      taoSection7PascalSourceListPMF J := by
  induction J generalizing N with
  | zero =>
      change
        (taoSection7HoldSourcePrefixListPMF N).map
            (taoSection7RawPrefixOfHoldBlocks 0) =
          PMF.pure ([] : List ℕ)
      convert PMF.map_const
        (taoSection7HoldSourcePrefixListPMF N) ([] : List ℕ) using 1
  | succ J ih =>
      cases N with
      | zero => omega
      | succ N =>
          rw [taoSection7HoldSourcePrefixListPMF_map_rawPrefix_succ_expose,
            ih N (by omega), ih (N + 1) (by omega)]
          simp [taoSection7PascalSourceListPMF]

/-- Sharp finite specialization: `J` complete Hold source blocks suffice to
expose the first `J` raw Pascal symbols. -/
theorem taoSection7HoldSourcePrefixListPMF_map_rawPrefix_self (J : ℕ) :
    (taoSection7HoldSourcePrefixListPMF J).map
        (taoSection7RawPrefixOfHoldBlocks J) =
      taoSection7PascalSourceListPMF J :=
  taoSection7HoldSourcePrefixListPMF_map_rawPrefix_eq_of_le J J le_rfl

end Tao
end Erdos1135SecondScale
