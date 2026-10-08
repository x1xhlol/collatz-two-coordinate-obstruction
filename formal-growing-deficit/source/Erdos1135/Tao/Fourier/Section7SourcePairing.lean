import Erdos1135.Tao.Fourier.Section7Character

/-!
# Section 7 Source Pairing

This leaf records the deterministic pairing of an exact Geom(2) valuation
list into the adjacent sums used by Tao's Pascal/Hold reduction.  An odd final
valuation is retained separately rather than discarded.
-/

namespace Erdos1135
namespace Tao

/-- Adjacent sums `a_1+a_2, a_3+a_4, ...` of a valuation list. -/
def taoSection7PairSums : List ℕ+ → List ℕ
  | a :: b :: as => ((a : ℕ) + (b : ℕ)) :: taoSection7PairSums as
  | _ => []

/-- The unpaired final valuation of an odd-length source list, when present. -/
def taoSection7OddTerminal : List ℕ+ → Option ℕ+
  | [] => none
  | [a] => some a
  | _ :: _ :: as => taoSection7OddTerminal as

@[simp] theorem taoSection7PairSums_nil :
    taoSection7PairSums [] = [] := rfl

@[simp] theorem taoSection7PairSums_singleton (a : ℕ+) :
    taoSection7PairSums [a] = [] := rfl

@[simp] theorem taoSection7PairSums_cons_cons
    (a b : ℕ+) (as : List ℕ+) :
    taoSection7PairSums (a :: b :: as) =
      ((a : ℕ) + (b : ℕ)) :: taoSection7PairSums as := rfl

@[simp] theorem taoSection7OddTerminal_nil :
    taoSection7OddTerminal [] = none := rfl

@[simp] theorem taoSection7OddTerminal_singleton (a : ℕ+) :
    taoSection7OddTerminal [a] = some a := rfl

@[simp] theorem taoSection7OddTerminal_cons_cons
    (a b : ℕ+) (as : List ℕ+) :
    taoSection7OddTerminal (a :: b :: as) =
      taoSection7OddTerminal as := rfl

theorem taoSection7PairSums_length :
    ∀ as : List ℕ+,
      (taoSection7PairSums as).length = as.length / 2
  | [] => by simp
  | [a] => by simp
  | a :: b :: as => by
      simp only [taoSection7PairSums_cons_cons, List.length_cons]
      rw [taoSection7PairSums_length as]
      omega

theorem taoSection7OddTerminal_isSome_iff :
    ∀ as : List ℕ+,
      (taoSection7OddTerminal as).isSome ↔ as.length % 2 = 1
  | [] => by simp
  | [a] => by simp
  | a :: b :: as => by
      simp only [taoSection7OddTerminal_cons_cons, List.length_cons]
      rw [taoSection7OddTerminal_isSome_iff as]
      omega

theorem taoSection7PairSums_length_of_length
    {n : ℕ} {as : List ℕ+} (hlen : as.length = n) :
    (taoSection7PairSums as).length = n / 2 := by
  rw [taoSection7PairSums_length, hlen]

theorem taoSection7OddTerminal_isSome_iff_length
    {n : ℕ} {as : List ℕ+} (hlen : as.length = n) :
    (taoSection7OddTerminal as).isSome ↔ n % 2 = 1 := by
  simpa [hlen] using taoSection7OddTerminal_isSome_iff as

/-- The unconditioned source Pascal law, defined as the sum of two independent
positive Geom(2) variables. -/
noncomputable def taoSection7PascalSourcePMF : PMF ℕ :=
  geom2PNat.bind fun a =>
    geom2PNat.map fun b => (a : ℕ) + (b : ℕ)

/-- Exact-length iid lists from the unconditioned source Pascal law. -/
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

/-- Exact odd-length source law after pairing, with the unpaired terminal
Geom(2) valuation retained as a separate coordinate. -/
noncomputable def taoSection7PascalSourceOddPMF : ℕ → PMF (List ℕ × ℕ+)
  | 0 => geom2PNat.map fun a => ([], a)
  | m + 1 => taoSection7PascalSourcePMF.bind fun b =>
      (taoSection7PascalSourceOddPMF m).map fun p => (b :: p.1, p.2)

/-- The retained odd terminal is independent of the paired raw Pascal list. -/
theorem taoSection7PascalSourceOddPMF_eq_bind
    (m : ℕ) :
    taoSection7PascalSourceOddPMF m =
      (taoSection7PascalSourceListPMF m).bind fun bs =>
        geom2PNat.map fun a => (bs, a) := by
  induction m with
  | zero =>
      change geom2PNat.map (fun a => ([], a)) =
        (PMF.pure []).bind fun bs => geom2PNat.map fun a => (bs, a)
      rw [PMF.pure_bind]
  | succ m ih =>
      rw [taoSection7PascalSourceOddPMF,
        taoSection7PascalSourceListPMF]
      rw [PMF.bind_bind]
      apply congrArg
        (fun f : ℕ → PMF (List ℕ × ℕ+) =>
          taoSection7PascalSourcePMF.bind f)
      funext b
      rw [PMF.bind_map]
      rw [ih]
      rw [PMF.map_bind]
      apply congrArg
        (fun f : List ℕ → PMF (List ℕ × ℕ+) =>
          (taoSection7PascalSourceListPMF m).bind f)
      funext bs
      rw [PMF.map_comp]
      rfl

theorem taoSection7PascalSourceListPMF_succ (m : ℕ) :
    taoSection7PascalSourceListPMF (m + 1) =
      geom2PNat.bind fun a =>
        geom2PNat.bind fun b =>
          (taoSection7PascalSourceListPMF m).map fun bs =>
            ((a : ℕ) + (b : ℕ)) :: bs := by
  rw [taoSection7PascalSourceListPMF]
  unfold taoSection7PascalSourcePMF
  rw [PMF.bind_bind]
  apply congrArg (fun f : ℕ+ → PMF (List ℕ) => geom2PNat.bind f)
  funext a
  rw [PMF.bind_map]
  change
    (geom2PNat.map fun b : ℕ+ => (b : ℕ)).bind
        ((fun c => (taoSection7PascalSourceListPMF m).map fun bs => c :: bs) ∘
          fun c => (a : ℕ) + c) =
      geom2PNat.bind fun b =>
        (taoSection7PascalSourceListPMF m).map fun bs =>
          ((a : ℕ) + (b : ℕ)) :: bs
  rw [PMF.bind_map]
  rfl

/-- Pairing an exact even-length iid Geom(2) list gives an iid raw Pascal list. -/
theorem geom2PNatListPMF_map_pairSums_eq_pascalSourceListPMF
    (m : ℕ) :
    (geom2PNatListPMF (2 * m)).map taoSection7PairSums =
      taoSection7PascalSourceListPMF m := by
  induction m with
  | zero =>
      change (PMF.pure ([] : List ℕ+)).map taoSection7PairSums =
        PMF.pure ([] : List ℕ)
      rw [PMF.pure_map]
      rfl
  | succ m ih =>
      rw [taoSection7PascalSourceListPMF_succ]
      rw [show 2 * (m + 1) = 2 * m + 1 + 1 by omega]
      change
        ((geom2PNat.bind fun a =>
            (geom2PNat.bind fun b =>
              (geom2PNatListPMF (2 * m)).map fun as => b :: as).map
                fun as => a :: as).map taoSection7PairSums) =
          geom2PNat.bind fun a =>
            geom2PNat.bind fun b =>
              (taoSection7PascalSourceListPMF m).map fun bs =>
                ((a : ℕ) + (b : ℕ)) :: bs
      rw [PMF.map_bind]
      congr
      funext a
      rw [PMF.map_comp, PMF.map_bind]
      congr
      funext b
      calc
        ((geom2PNatListPMF (2 * m)).map fun as => b :: as).map
              (taoSection7PairSums ∘ fun as => a :: as) =
            (geom2PNatListPMF (2 * m)).map
              ((taoSection7PairSums ∘ fun as => a :: as) ∘
                fun as => b :: as) :=
          PMF.map_comp _ _ _
        _ = (geom2PNatListPMF (2 * m)).map
              ((fun bs => ((a : ℕ) + (b : ℕ)) :: bs) ∘
                taoSection7PairSums) := by
          apply congrArg
            (fun f : List ℕ+ → List ℕ =>
              (geom2PNatListPMF (2 * m)).map f)
          funext as
          rfl
        _ = ((geom2PNatListPMF (2 * m)).map taoSection7PairSums).map
              (fun bs => ((a : ℕ) + (b : ℕ)) :: bs) := by
          rw [PMF.map_comp]
        _ = (taoSection7PascalSourceListPMF m).map
              (fun bs => ((a : ℕ) + (b : ℕ)) :: bs) := by
          rw [ih]

/-- Pairing an exact odd-length iid Geom(2) list gives raw Pascal sums together
with the final independent Geom(2) valuation. -/
theorem geom2PNatListPMF_map_pairSums_oddTerminal_eq_pascalSourceOddPMF
    (m : ℕ) :
    (geom2PNatListPMF (2 * m + 1)).map
        (fun as => (taoSection7PairSums as,
          (taoSection7OddTerminal as).getD 1)) =
      taoSection7PascalSourceOddPMF m := by
  induction m with
  | zero =>
      change
        ((geom2PNat.bind fun a => (PMF.pure []).map fun as => a :: as).map
            (fun as => (taoSection7PairSums as,
              (taoSection7OddTerminal as).getD 1))) =
          geom2PNat.map fun a => ([], a)
      rw [PMF.map_bind]
      apply congrArg (fun f : ℕ+ → PMF (List ℕ × ℕ+) => geom2PNat.bind f)
      funext a
      rw [PMF.map_comp, PMF.pure_map]
      rfl
  | succ m ih =>
      rw [show 2 * (m + 1) + 1 = (2 * m + 1) + 1 + 1 by omega]
      change
        ((geom2PNat.bind fun a =>
            (geom2PNat.bind fun b =>
              (geom2PNatListPMF (2 * m + 1)).map fun as => b :: as).map
                fun as => a :: as).map
                  (fun as => (taoSection7PairSums as,
                    (taoSection7OddTerminal as).getD 1))) =
          taoSection7PascalSourcePMF.bind fun c =>
            (taoSection7PascalSourceOddPMF m).map fun p => (c :: p.1, p.2)
      rw [PMF.map_bind]
      unfold taoSection7PascalSourcePMF
      rw [PMF.bind_bind]
      apply congrArg
        (fun f : ℕ+ → PMF (List ℕ × ℕ+) => geom2PNat.bind f)
      funext a
      rw [PMF.map_comp, PMF.map_bind]
      conv_rhs => rw [PMF.bind_map]
      change _ =
        (PMF.map (fun b : ℕ+ => (b : ℕ)) geom2PNat).bind
          ((fun c => (taoSection7PascalSourceOddPMF m).map
            fun p => (c :: p.1, p.2)) ∘ fun b => (a : ℕ) + b)
      rw [PMF.bind_map]
      apply congrArg
        (fun f : ℕ+ → PMF (List ℕ × ℕ+) => geom2PNat.bind f)
      funext b
      calc
        ((geom2PNatListPMF (2 * m + 1)).map fun as => b :: as).map
              ((fun as => (taoSection7PairSums as,
                (taoSection7OddTerminal as).getD 1)) ∘
                  fun as => a :: as) =
            (geom2PNatListPMF (2 * m + 1)).map
              (((fun as => (taoSection7PairSums as,
                (taoSection7OddTerminal as).getD 1)) ∘
                  fun as => a :: as) ∘ fun as => b :: as) := by
          rw [PMF.map_comp]
        _ =
            (geom2PNatListPMF (2 * m + 1)).map
              ((fun p => (((a : ℕ) + (b : ℕ)) :: p.1, p.2)) ∘
                fun as => (taoSection7PairSums as,
                  (taoSection7OddTerminal as).getD 1)) := by
          apply congrArg
            (fun f : List ℕ+ → List ℕ × ℕ+ =>
              (geom2PNatListPMF (2 * m + 1)).map f)
          funext as
          rfl
        _ = ((geom2PNatListPMF (2 * m + 1)).map
              (fun as => (taoSection7PairSums as,
                (taoSection7OddTerminal as).getD 1))).map
              (fun p => (((a : ℕ) + (b : ℕ)) :: p.1, p.2)) := by
          rw [PMF.map_comp]
        _ = (taoSection7PascalSourceOddPMF m).map
              (fun p => (((a : ℕ) + (b : ℕ)) :: p.1, p.2)) := by
          rw [ih]

end Tao
end Erdos1135
