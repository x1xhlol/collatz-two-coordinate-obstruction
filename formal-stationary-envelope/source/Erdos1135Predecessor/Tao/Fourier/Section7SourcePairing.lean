/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file was adapted from Lech Mazur's published predecessor-density source
package. Erdos1135, FormalConjectures, and CollatzConjecture identifiers were
renamed to Erdos1135Predecessor, FormalConjecturesPredecessor, and
CollatzConjecturePredecessor where present, keeping this package's baseline
separate in the joint build. The remaining mathematical source is unchanged.
Original attribution and licenses are retained.
-/

import Erdos1135Predecessor.Tao.Fourier.Section7Character

namespace Erdos1135Predecessor

namespace Tao

noncomputable def taoSection7PascalSourcePMF : PMF ℕ :=
  geom2PNat.bind fun a =>
    geom2PNat.map fun b => (a : ℕ) + (b : ℕ)

noncomputable def taoSection7PascalSourceListPMF : ℕ → PMF (List ℕ)
  | 0 => PMF.pure []
  | m + 1 => taoSection7PascalSourcePMF.bind fun b =>
      (taoSection7PascalSourceListPMF m).map fun bs => b :: bs

theorem taoSection7PascalSourceListPMF_succ_apply_cons
    (m b : ℕ) (bs : List ℕ) :
    taoSection7PascalSourceListPMF (m + 1) (b :: bs) =
      taoSection7PascalSourcePMF b *
        taoSection7PascalSourceListPMF m bs := by
  classical
  rw [taoSection7PascalSourceListPMF, PMF.bind_apply]
  have hmap : ∀ b' : ℕ,
      ((taoSection7PascalSourceListPMF m).map fun cs => b' :: cs)
          (b :: bs) =
        if b = b' then taoSection7PascalSourceListPMF m bs else 0 := by
    intro b'
    rw [PMF.map_apply]
    by_cases h : b = b'
    · subst b'
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
        taoSection7PascalSourcePMF b' *
          ((taoSection7PascalSourceListPMF m).map fun cs => b' :: cs)
            (b :: bs)) =
        ∑' b' : ℕ,
          taoSection7PascalSourcePMF b' *
            (if b = b' then taoSection7PascalSourceListPMF m bs else 0) := by
      apply tsum_congr
      intro b'
      rw [hmap b']
    _ = taoSection7PascalSourcePMF b *
          taoSection7PascalSourceListPMF m bs := by
      rw [tsum_eq_single b]
      · simp
      · intro b' hb'
        simp [hb'.symm]

theorem taoSection7PascalSourceListPMF_succ_apply_nil (m : ℕ) :
    taoSection7PascalSourceListPMF (m + 1) [] = 0 := by
  rw [taoSection7PascalSourceListPMF, PMF.bind_apply]
  rw [ENNReal.tsum_eq_zero]
  intro b
  have hmap :
      ((taoSection7PascalSourceListPMF m).map fun bs => b :: bs) [] = 0 := by
    rw [PMF.map_apply, ENNReal.tsum_eq_zero]
    intro bs
    simp
  rw [hmap, mul_zero]

end Tao

end Erdos1135Predecessor
