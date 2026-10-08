/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Probability.PascalPrime

/-!
# Section 7 Pascal-Prime Source Lists

This module packages the source-valued Pascal-prime law and its iid finite-list
PMF.  It is probability-only plumbing for the later HoldPMF construction: no
Fourier, Q-finite, or renewal bridge modules are imported here.
-/

namespace Erdos1135SecondScale
namespace Tao

/-- Pascal-prime PMF pushed from the internal index `n` to the source value `b = n + 2`. -/
noncomputable def taoSection7PascalPrimeSourcePMF : PMF ℕ :=
  taoSection7PascalPrimePMF.map fun n => n + 2

theorem taoSection7PascalPrimeSourcePMF_zero :
    taoSection7PascalPrimeSourcePMF 0 = 0 := by
  rw [taoSection7PascalPrimeSourcePMF, PMF.map_apply]
  simp

theorem taoSection7PascalPrimeSourcePMF_one :
    taoSection7PascalPrimeSourcePMF 1 = 0 := by
  rw [taoSection7PascalPrimeSourcePMF, PMF.map_apply]
  simp

theorem taoSection7PascalPrimeSourcePMF_eq_zero_of_lt_two
    {b : ℕ} (hb : b < 2) :
    taoSection7PascalPrimeSourcePMF b = 0 := by
  rcases b with _ | b
  · exact taoSection7PascalPrimeSourcePMF_zero
  rcases b with _ | b
  · exact taoSection7PascalPrimeSourcePMF_one
  · omega

theorem taoSection7PascalPrimeSourcePMF_add_two (n : ℕ) :
    taoSection7PascalPrimeSourcePMF (n + 2) =
      taoSection7PascalPrimePMF n := by
  rw [taoSection7PascalPrimeSourcePMF, PMF.map_apply]
  rw [tsum_eq_single n]
  · simp
  · intro m hm
    have hmn : n ≠ m := by
      intro h
      exact hm h.symm
    simp [hmn]

theorem taoSection7PascalPrimeSourcePMF_three :
    taoSection7PascalPrimeSourcePMF 3 = 0 := by
  rw [show (3 : ℕ) = 1 + 2 by norm_num,
    taoSection7PascalPrimeSourcePMF_add_two]
  have htoReal : (taoSection7PascalPrimePMF 1).toReal = 0 :=
    taoSection7PascalPrimePMF_one_toReal
  rcases (ENNReal.toReal_eq_zero_iff (taoSection7PascalPrimePMF 1)).mp htoReal with
    hzero | htop
  · exact hzero
  · exact False.elim ((PMF.apply_ne_top taoSection7PascalPrimePMF 1) htop)

theorem taoSection7PascalPrimeSourcePMF_apply_toReal (b : ℕ) :
    (taoSection7PascalPrimeSourcePMF b).toReal =
      taoSection7PascalPrimeSourceMass b := by
  rcases b with _ | b
  · rw [taoSection7PascalPrimeSourcePMF_zero,
      taoSection7PascalPrimeSourceMass_zero]
    norm_num
  rcases b with _ | n
  · rw [taoSection7PascalPrimeSourcePMF_one,
      taoSection7PascalPrimeSourceMass_one]
    norm_num
  · rw [taoSection7PascalPrimeSourcePMF_add_two,
      taoSection7PascalPrimePMF_apply_toReal,
      taoSection7PascalPrimeSourceMass_add_two]

theorem taoSection7PascalPrimeSourcePMF_ne_zero_ge_two
    {b : ℕ} (hb : taoSection7PascalPrimeSourcePMF b ≠ 0) :
    2 ≤ b := by
  by_contra hlt
  exact hb (taoSection7PascalPrimeSourcePMF_eq_zero_of_lt_two (Nat.lt_of_not_ge hlt))

theorem taoSection7PascalPrimeSourcePMF_ne_zero_ne_three
    {b : ℕ} (hb : taoSection7PascalPrimeSourcePMF b ≠ 0) :
    b ≠ 3 := by
  intro hb3
  exact hb (by simpa [hb3] using taoSection7PascalPrimeSourcePMF_three)

/-- Product of source-valued Pascal-prime PMF point masses along a finite list. -/
noncomputable def taoSection7PascalPrimeSourceListMass (bs : List ℕ) : ℝ :=
  (bs.map fun b => (taoSection7PascalPrimeSourcePMF b).toReal).prod

/-- Iid finite-list law for source-valued Pascal-prime variables. -/
noncomputable def taoSection7PascalPrimeSourceListPMF : ℕ → PMF (List ℕ)
  | 0 => PMF.pure []
  | n + 1 => taoSection7PascalPrimeSourcePMF.bind fun b =>
      (taoSection7PascalPrimeSourceListPMF n).map fun bs => b :: bs

theorem taoSection7PascalPrimeSourceListPMF_zero_apply_nil :
    taoSection7PascalPrimeSourceListPMF 0 [] = 1 := by
  simp [taoSection7PascalPrimeSourceListPMF]

theorem taoSection7PascalPrimeSourceListPMF_zero_apply_cons
    (b : ℕ) (bs : List ℕ) :
    taoSection7PascalPrimeSourceListPMF 0 (b :: bs) = 0 := by
  simp [taoSection7PascalPrimeSourceListPMF]

theorem taoSection7PascalPrimeSourceListPMF_succ_apply_cons
    (n b : ℕ) (bs : List ℕ) :
    taoSection7PascalPrimeSourceListPMF (n + 1) (b :: bs) =
      taoSection7PascalPrimeSourcePMF b *
        taoSection7PascalPrimeSourceListPMF n bs := by
  classical
  rw [taoSection7PascalPrimeSourceListPMF, PMF.bind_apply]
  have hmap : ∀ b' : ℕ,
      ((taoSection7PascalPrimeSourceListPMF n).map fun cs => b' :: cs) (b :: bs) =
        if b = b' then taoSection7PascalPrimeSourceListPMF n bs else 0 := by
    intro b'
    rw [PMF.map_apply]
    by_cases h : b = b'
    · subst h
      rw [tsum_eq_single bs]
      · simp
      · intro cs hcs
        have hc : ¬ b :: bs = b :: cs := by
          intro hcons
          exact hcs (List.cons.inj hcons).2.symm
        simp [hc]
    · have hnone : ∀ cs : List ℕ, ¬ b :: bs = b' :: cs := by
        intro cs hcons
        exact h (List.cons.inj hcons).1
      simp [h, hnone]
  calc
    (∑' b' : ℕ,
        taoSection7PascalPrimeSourcePMF b' *
          ((taoSection7PascalPrimeSourceListPMF n).map fun cs => b' :: cs) (b :: bs))
        = ∑' b' : ℕ,
            taoSection7PascalPrimeSourcePMF b' *
              (if b = b' then taoSection7PascalPrimeSourceListPMF n bs else 0) := by
          apply tsum_congr
          intro b'
          rw [hmap b']
    _ = taoSection7PascalPrimeSourcePMF b *
          taoSection7PascalPrimeSourceListPMF n bs := by
          rw [tsum_eq_single b]
          · simp
          · intro b' hb'
            simp [hb'.symm]

theorem taoSection7PascalPrimeSourceListPMF_succ_apply_nil (n : ℕ) :
    taoSection7PascalPrimeSourceListPMF (n + 1) [] = 0 := by
  classical
  rw [taoSection7PascalPrimeSourceListPMF, PMF.bind_apply]
  simp [PMF.map_apply]

theorem taoSection7PascalPrimeSourceListPMF_apply_eq_zero_of_length_ne
    (n : ℕ) (bs : List ℕ) (h : bs.length ≠ n) :
    taoSection7PascalPrimeSourceListPMF n bs = 0 := by
  induction n generalizing bs with
  | zero =>
      cases bs with
      | nil => exact (h rfl).elim
      | cons b bs => simp [taoSection7PascalPrimeSourceListPMF]
  | succ n ih =>
      cases bs with
      | nil =>
          exact taoSection7PascalPrimeSourceListPMF_succ_apply_nil n
      | cons b bs =>
          rw [taoSection7PascalPrimeSourceListPMF_succ_apply_cons]
          have htail : bs.length ≠ n := by
            intro hs
            exact h (by simp [hs])
          rw [ih bs htail, mul_zero]

theorem taoSection7PascalPrimeSourceListPMF_apply_ne_zero_allGeTwo
    {n : ℕ} {bs : List ℕ}
    (h : taoSection7PascalPrimeSourceListPMF n bs ≠ 0) :
    taoSection7AllGeTwo bs := by
  induction n generalizing bs with
  | zero =>
      cases bs with
      | nil =>
          intro b hb
          cases hb
      | cons b bs =>
          exact False.elim (h (taoSection7PascalPrimeSourceListPMF_zero_apply_cons b bs))
  | succ n ih =>
      cases bs with
      | nil =>
          intro b hb
          cases hb
      | cons b bs =>
          have hprod :
              taoSection7PascalPrimeSourcePMF b *
                  taoSection7PascalPrimeSourceListPMF n bs ≠ 0 := by
            simpa [taoSection7PascalPrimeSourceListPMF_succ_apply_cons] using h
          have hb : taoSection7PascalPrimeSourcePMF b ≠ 0 := by
            intro hbzero
            exact hprod (by rw [hbzero, zero_mul])
          have htail : taoSection7PascalPrimeSourceListPMF n bs ≠ 0 := by
            intro hzero
            exact hprod (by rw [hzero, mul_zero])
          intro x hx
          simp at hx
          rcases hx with rfl | hx
          · exact taoSection7PascalPrimeSourcePMF_ne_zero_ge_two hb
          · exact ih htail x hx

theorem taoSection7PascalPrimeSourceListPMF_apply_ne_zero_noThree
    {n : ℕ} {bs : List ℕ}
    (h : taoSection7PascalPrimeSourceListPMF n bs ≠ 0) :
    taoSection7NoThree bs := by
  induction n generalizing bs with
  | zero =>
      cases bs with
      | nil =>
          intro b hb
          cases hb
      | cons b bs =>
          exact False.elim (h (taoSection7PascalPrimeSourceListPMF_zero_apply_cons b bs))
  | succ n ih =>
      cases bs with
      | nil =>
          intro b hb
          cases hb
      | cons b bs =>
          have hprod :
              taoSection7PascalPrimeSourcePMF b *
                  taoSection7PascalPrimeSourceListPMF n bs ≠ 0 := by
            simpa [taoSection7PascalPrimeSourceListPMF_succ_apply_cons] using h
          have hb : taoSection7PascalPrimeSourcePMF b ≠ 0 := by
            intro hbzero
            exact hprod (by rw [hbzero, zero_mul])
          have htail : taoSection7PascalPrimeSourceListPMF n bs ≠ 0 := by
            intro hzero
            exact hprod (by rw [hzero, mul_zero])
          intro x hx
          simp at hx
          rcases hx with rfl | hx
          · exact taoSection7PascalPrimeSourcePMF_ne_zero_ne_three hb
          · exact ih htail x hx

theorem taoSection7PascalPrimeSourceListPMF_apply_eq_zero_of_not_allGeTwo
    {n : ℕ} {bs : List ℕ} (h : ¬ taoSection7AllGeTwo bs) :
    taoSection7PascalPrimeSourceListPMF n bs = 0 := by
  by_contra hne
  exact h (taoSection7PascalPrimeSourceListPMF_apply_ne_zero_allGeTwo hne)

theorem taoSection7PascalPrimeSourceListPMF_apply_eq_zero_of_not_noThree
    {n : ℕ} {bs : List ℕ} (h : ¬ taoSection7NoThree bs) :
    taoSection7PascalPrimeSourceListPMF n bs = 0 := by
  by_contra hne
  exact h (taoSection7PascalPrimeSourceListPMF_apply_ne_zero_noThree hne)

theorem taoSection7PascalPrimeSourceListPMF_apply_eq_zero_of_mem_three
    {n : ℕ} {bs : List ℕ} (h : 3 ∈ bs) :
    taoSection7PascalPrimeSourceListPMF n bs = 0 := by
  exact taoSection7PascalPrimeSourceListPMF_apply_eq_zero_of_not_noThree (by
    intro hno
    exact hno 3 h rfl)

theorem taoSection7PascalPrimeSourceListPMF_apply_length_toReal
    (bs : List ℕ) :
    (taoSection7PascalPrimeSourceListPMF bs.length bs).toReal =
      taoSection7PascalPrimeSourceListMass bs := by
  induction bs with
  | nil =>
      simp [taoSection7PascalPrimeSourceListPMF,
        taoSection7PascalPrimeSourceListMass]
  | cons b bs ih =>
      rw [List.length_cons, taoSection7PascalPrimeSourceListPMF_succ_apply_cons]
      rw [ENNReal.toReal_mul, ih]
      simp [taoSection7PascalPrimeSourceListMass]

theorem taoSection7PascalPrimeSourceListMass_eq_sourcePathMass
    (bs : List ℕ) :
    taoSection7PascalPrimeSourceListMass bs =
      taoSection7PascalPrimeSourcePathMass bs := by
  induction bs with
  | nil =>
      simp [taoSection7PascalPrimeSourceListMass,
        taoSection7PascalPrimeSourcePathMass]
  | cons b bs ih =>
      simp [taoSection7PascalPrimeSourceListMass,
        taoSection7PascalPrimeSourcePathMass,
        taoSection7PascalPrimeSourcePMF_apply_toReal]

theorem taoSection7PascalPrimeSourceListPMF_apply_length_toReal_eq_sourcePathMass
    (bs : List ℕ) :
    (taoSection7PascalPrimeSourceListPMF bs.length bs).toReal =
      taoSection7PascalPrimeSourcePathMass bs := by
  rw [taoSection7PascalPrimeSourceListPMF_apply_length_toReal,
    taoSection7PascalPrimeSourceListMass_eq_sourcePathMass]

end Tao
end Erdos1135SecondScale
