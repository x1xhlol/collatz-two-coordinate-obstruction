/-
Modification notice: changed by Lucas Valbuena, 28 September 2026.
This file is a namespace-renamed copy of the second-scale adaptation of
Lech Mazur's published formalization. Erdos1135 module, import, and namespace
identifiers were changed to Erdos1135SecondScale for the joint build.
The alpha = 2001/2000 adaptation and its proof changes are recorded in the
retained patch and provenance. Original attribution and licenses are retained.
-/

import Erdos1135SecondScale.Tao.Probability.CountableMarkov
import Erdos1135SecondScale.Tao.Probability.FullL1
import Erdos1135SecondScale.Tao.Probability.Geom2ListProjectivity

/-!
# Terminal Coordinate Of A Positive Geom(2) List

This neutral leaf proves that a positive-length iid Geom(2) list has terminal-coordinate mean
`2`.  The terminal value is zero on the empty list, so the length-zero expectation is exactly zero.
-/

namespace Erdos1135SecondScale
namespace Tao

noncomputable section

/-- Natural value of the last coordinate, extended by zero on the empty list. -/
def geom2PNatListTerminalValue (as : List ℕ+) : ℕ :=
  match as.getLast? with
  | none => 0
  | some a => (a : ℕ)

@[simp]
theorem geom2PNatListTerminalValue_nil :
    geom2PNatListTerminalValue [] = 0 := rfl

@[simp]
theorem geom2PNatListTerminalValue_singleton (a : ℕ+) :
    geom2PNatListTerminalValue [a] = (a : ℕ) := by
  simp [geom2PNatListTerminalValue]

theorem geom2PNatListTerminalValue_eq_getLast
    {as : List ℕ+} (has : as ≠ []) :
    geom2PNatListTerminalValue as = (as.getLast has : ℕ) := by
  simp [geom2PNatListTerminalValue,
    List.getLast?_eq_getLast_of_ne_nil has]

theorem geom2PNatListTerminalValue_drop_eq_of_length
    {m : ℕ} {as : List ℕ+} (hlength : as.length = m + 1) :
    geom2PNatListTerminalValue (as.drop m) =
      geom2PNatListTerminalValue as := by
  have has : as ≠ [] := by
    intro hnil
    simp [hnil] at hlength
  have hdrop : as.drop m = [as.getLast has] := by
    have h := List.drop_length_sub_one has
    simpa [hlength] using h
  rw [hdrop, geom2PNatListTerminalValue_singleton,
    geom2PNatListTerminalValue_eq_getLast has]

private theorem geom2PNatListPMF_one_eq_map_singleton :
    geom2PNatListPMF 1 = geom2PNat.map (fun a => [a]) := by
  change (geom2PNat.bind fun a => (PMF.pure []).map fun as => a :: as) = _
  rw [show (fun a : ℕ+ => (PMF.pure []).map fun as => a :: as) =
      PMF.pure ∘ (fun a : ℕ+ => [a]) by
    funext a
    exact PMF.pure_map (fun as : List ℕ+ => a :: as) []]
  exact PMF.bind_pure_comp _ _

private theorem taoPMFENNExpectation_geom2PNat_natCast :
    taoPMFENNExpectation geom2PNat
      (fun a => (((a : ℕ) : ENNReal))) = 2 := by
  unfold taoPMFENNExpectation
  calc
    (∑' a : ℕ+, geom2PNat a * (((a : ℕ) : ENNReal))) =
        ∑' a : ℕ+, ENNReal.ofReal
          ((geom2PNat a).toReal * (((a : ℕ) : ℝ))) := by
      apply tsum_congr
      intro a
      rw [ENNReal.ofReal_mul ENNReal.toReal_nonneg,
        ENNReal.ofReal_toReal (PMF.apply_ne_top geom2PNat a)]
      norm_num
    _ = ENNReal.ofReal
        (∑' a : ℕ+, (geom2PNat a).toReal * (((a : ℕ) : ℝ))) := by
      symm
      exact ENNReal.ofReal_tsum_of_nonneg
        (fun a => mul_nonneg ENNReal.toReal_nonneg (Nat.cast_nonneg _))
        summable_geom2PNat_mul_natCast
    _ = 2 := by
      rw [tsum_geom2PNat_mul_natCast]
      norm_num

private theorem taoPMFENNExpectation_geom2PNatList_one_terminal :
    taoPMFENNExpectation (geom2PNatListPMF 1)
      (fun as => (geom2PNatListTerminalValue as : ENNReal)) = 2 := by
  rw [geom2PNatListPMF_one_eq_map_singleton,
    taoPMFENNExpectation_map]
  calc
    taoPMFENNExpectation geom2PNat
        ((fun as => (geom2PNatListTerminalValue as : ENNReal)) ∘
          fun a => [a]) =
      taoPMFENNExpectation geom2PNat
        (fun a => (((a : ℕ) : ENNReal))) := by
      unfold taoPMFENNExpectation
      apply tsum_congr
      intro a
      simp [Function.comp_apply]
    _ = 2 := taoPMFENNExpectation_geom2PNat_natCast

private theorem taoPMFENNExpectation_geom2PNatList_terminal_succ
    (m : ℕ) :
    taoPMFENNExpectation (geom2PNatListPMF (m + 1))
      (fun as => (geom2PNatListTerminalValue as : ENNReal)) = 2 := by
  let p := geom2PNatListPMF (m + 1)
  let G : List ℕ+ → ENNReal :=
    fun as => (geom2PNatListTerminalValue as : ENNReal)
  have hmap := taoPMFENNExpectation_map p (fun as => as.drop m) G
  have hp : p = geom2PNatListPMF (m + 1) := rfl
  rw [hp, geom2PNatListPMF_map_drop_low_eq m 1] at hmap
  have hterm :
      taoPMFENNExpectation p G =
        taoPMFENNExpectation p (G ∘ fun as => as.drop m) := by
    unfold taoPMFENNExpectation
    apply tsum_congr
    intro as
    by_cases has : as ∈ p.support
    · have hlength : as.length = m + 1 := by
        apply geom2PNatListPMF_support_length_eq
        simpa only [p] using has
      rw [show G as = G (as.drop m) by
        simp only [G]
        exact congrArg Nat.cast
          (geom2PNatListTerminalValue_drop_eq_of_length hlength).symm]
      rfl
    · have hzero : p as = 0 := by
        simpa [PMF.mem_support_iff] using has
      simp [hzero]
  exact hterm.trans (hmap.symm.trans
    taoPMFENNExpectation_geom2PNatList_one_terminal)

private theorem taoPMFENNExpectation_geom2PNatList_terminal
    (m : ℕ) :
    taoPMFENNExpectation (geom2PNatListPMF m)
      (fun as => (geom2PNatListTerminalValue as : ENNReal)) =
      if m = 0 then 0 else 2 := by
  by_cases hm : m = 0
  · subst m
    rw [if_pos rfl]
    unfold taoPMFENNExpectation
    rw [tsum_eq_single ([] : List ℕ+)]
    · simp [geom2PNatListPMF]
    · intro as has
      have hlength : as.length ≠ 0 := by
        intro hzero
        exact has (List.eq_nil_of_length_eq_zero hzero)
      rw [geom2PNatListPMF_apply_eq_zero_of_length_ne 0 as hlength]
      simp
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
    rw [if_neg (Nat.succ_ne_zero k)]
    exact taoPMFENNExpectation_geom2PNatList_terminal_succ k

/-- The real terminal-moment series of the exact-length iid list law is summable. -/
theorem summable_geom2PNatListPMF_mul_terminalValue (m : ℕ) :
    Summable fun as : List ℕ+ =>
      (geom2PNatListPMF m as).toReal *
        (geom2PNatListTerminalValue as : ℝ) := by
  have hfinite :
      (∑' as : List ℕ+,
        geom2PNatListPMF m as *
          (geom2PNatListTerminalValue as : ENNReal)) ≠ ⊤ := by
    rw [show (∑' as : List ℕ+,
        geom2PNatListPMF m as *
          (geom2PNatListTerminalValue as : ENNReal)) =
        if m = 0 then 0 else 2 by
      exact taoPMFENNExpectation_geom2PNatList_terminal m]
    split <;> norm_num
  refine (ENNReal.summable_toReal hfinite).congr ?_
  intro as
  rw [ENNReal.toReal_mul]
  simp

/-- Real terminal expectation of the exact-length iid list law, including the zero-length case. -/
theorem geom2PNatListPMF_terminalValue_expectation (m : ℕ) :
    (∑' as : List ℕ+,
      (geom2PNatListPMF m as).toReal *
        (geom2PNatListTerminalValue as : ℝ)) =
      if m = 0 then 0 else 2 := by
  by_cases hm : m = 0
  · subst m
    rw [if_pos rfl, tsum_eq_single ([] : List ℕ+)]
    · simp [geom2PNatListPMF]
    · intro as has
      have hlength : as.length ≠ 0 := by
        intro hzero
        exact has (List.eq_nil_of_length_eq_zero hzero)
      rw [geom2PNatListPMF_apply_eq_zero_of_length_ne 0 as hlength]
      simp
  · obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hm
    rw [if_neg (Nat.succ_ne_zero k)]
    have hnative := taoPMFENNExpectation_geom2PNatList_terminal_succ k
    let F : List ℕ+ → ENNReal := fun as =>
      geom2PNatListPMF (k + 1) as *
        (geom2PNatListTerminalValue as : ENNReal)
    calc
      (∑' as : List ℕ+,
          (geom2PNatListPMF (k + 1) as).toReal *
            (geom2PNatListTerminalValue as : ℝ)) =
          ∑' as : List ℕ+, (F as).toReal := by
        apply tsum_congr
        intro as
        simp [F, ENNReal.toReal_mul]
      _ = (∑' as : List ℕ+, F as).toReal := by
        symm
        apply ENNReal.tsum_toReal_eq
        intro as
        exact ENNReal.mul_ne_top (PMF.apply_ne_top _ _) (by simp)
      _ = 2 := by
        rw [show (∑' as : List ℕ+, F as) = 2 by
          simpa [F, taoPMFENNExpectation] using hnative]
        norm_num

/-- Exact-length subtype form used by the repaired Lemma 5.3 tuple summation. -/
theorem tsum_geom2PNatListMass_mul_terminalValue_exactLength (m : ℕ) :
    (∑' as : {as : List ℕ+ // as.length = m},
      geom2PNatListMass as.1 *
        (geom2PNatListTerminalValue as.1 : ℝ)) =
      if m = 0 then 0 else 2 := by
  calc
    (∑' as : {as : List ℕ+ // as.length = m},
        geom2PNatListMass as.1 *
          (geom2PNatListTerminalValue as.1 : ℝ)) =
        ∑' as : List ℕ+,
          (geom2PNatListPMF m as).toReal *
            (geom2PNatListTerminalValue as : ℝ) := by
      let E : Set (List ℕ+) := {as | as.length = m}
      let f : List ℕ+ → ℝ := fun xs => geom2PNatListMass xs *
        (geom2PNatListTerminalValue xs : ℝ)
      change (∑' as : E, f as.1) = _
      calc
        (∑' as : E, f as.1) = ∑' as : List ℕ+, E.indicator f as :=
          tsum_subtype E f
        _ = ∑' as : List ℕ+,
            (geom2PNatListPMF m as).toReal *
              (geom2PNatListTerminalValue as : ℝ) := by
          apply tsum_congr
          intro as
          by_cases hlength : as.length = m
          · rw [Set.indicator_of_mem (by simpa [E] using hlength)]
            have hmass := geom2PNatListPMF_apply_length_toReal as
            rw [hlength] at hmass
            simpa [f] using congrArg
              (fun x : ℝ => x * (geom2PNatListTerminalValue as : ℝ))
              hmass.symm
          · rw [Set.indicator_of_notMem (by simpa [E] using hlength),
              geom2PNatListPMF_apply_eq_zero_of_length_ne m as hlength]
            simp
    _ = if m = 0 then 0 else 2 :=
      geom2PNatListPMF_terminalValue_expectation m

/-- The coefficient-facing exact-length terminal-moment series is summable. -/
theorem summable_geom2PNatListMass_mul_terminalValue_exactLength (m : ℕ) :
    Summable fun as : {as : List ℕ+ // as.length = m} =>
      geom2PNatListMass as.1 *
        (geom2PNatListTerminalValue as.1 : ℝ) := by
  let E : Set (List ℕ+) := {as | as.length = m}
  have hs := (summable_geom2PNatListPMF_mul_terminalValue m).subtype E
  refine hs.congr ?_
  intro as
  have hmass := geom2PNatListPMF_apply_length_toReal as.1
  rw [as.2] at hmass
  simpa [E, hmass]

theorem tsum_geom2PNatListMass_mul_terminalValue_exactLength_of_pos
    {m : ℕ} (hm : 0 < m) :
    (∑' as : {as : List ℕ+ // as.length = m},
      geom2PNatListMass as.1 *
        (geom2PNatListTerminalValue as.1 : ℝ)) = 2 := by
  rw [tsum_geom2PNatListMass_mul_terminalValue_exactLength,
    if_neg hm.ne']

/-- Exact-length Geom(2) list mass is summable on the length subtype. -/
theorem summable_geom2PNatListMass_exactLength (m : ℕ) :
    Summable fun as : {as : List ℕ+ // as.length = m} =>
      geom2PNatListMass as.1 := by
  let E : Set (List ℕ+) := {as | as.length = m}
  have hs := (taoPMF_summable_toReal (geom2PNatListPMF m)).subtype E
  refine hs.congr ?_
  intro as
  have hmass := geom2PNatListPMF_apply_length_toReal as.1
  rw [as.2] at hmass
  simpa [E, hmass]

/-- The iid positive Geom(2) law has total mass one at every exact length. -/
theorem tsum_geom2PNatListMass_exactLength (m : ℕ) :
    (∑' as : {as : List ℕ+ // as.length = m},
      geom2PNatListMass as.1) = 1 := by
  let E : Set (List ℕ+) := {as | as.length = m}
  have hsupport : (geom2PNatListPMF m).support ⊆ E := by
    intro as has
    exact geom2PNatListPMF_support_length_eq has
  have hevent : (geom2PNatListPMF m).toOuterMeasure E = 1 :=
    ((geom2PNatListPMF m).toOuterMeasure_apply_eq_one_iff E).2 hsupport
  have hsum :
      (∑' as : E, (geom2PNatListPMF m as.1).toReal) = 1 := by
    rw [← pmfOuterMass_toReal_eq_tsum_subtype, hevent]
    norm_num
  calc
    (∑' as : {as : List ℕ+ // as.length = m},
        geom2PNatListMass as.1) =
        ∑' as : E, (geom2PNatListPMF m as.1).toReal := by
      apply tsum_congr
      intro as
      have hmass := geom2PNatListPMF_apply_length_toReal as.1
      rw [as.2] at hmass
      exact hmass.symm
    _ = 1 := hsum

/-- Native base term retained from the inclusive reciprocal-progression
majorant. -/
noncomputable def geom2PNatListNativeBase (as : List ℕ+) : ℝ :=
  ((geom2PNatListTerminalValue as : ℝ) + 2) /
    (2 : ℝ) ^ (taoTupleWeight as + 1)

theorem geom2PNatListNativeBase_eq_half_mass
    (as : List ℕ+) :
    geom2PNatListNativeBase as =
      (1 / 2 : ℝ) *
        (geom2PNatListMass as *
            (geom2PNatListTerminalValue as : ℝ) +
          2 * geom2PNatListMass as) := by
  unfold geom2PNatListNativeBase
  rw [geom2PNatListMass_eq_inv_pow, pow_succ]
  field_simp [pow_ne_zero]

/-- The native base series is summable at every exact length. -/
theorem summable_geom2PNatListNativeBase_exactLength (m : ℕ) :
    Summable fun as : {as : List ℕ+ // as.length = m} =>
      geom2PNatListNativeBase as.1 := by
  have hterminal :=
    summable_geom2PNatListMass_mul_terminalValue_exactLength m
  have hmass := summable_geom2PNatListMass_exactLength m
  have hinside := hterminal.add (Summable.mul_left (2 : ℝ) hmass)
  have hhalf := Summable.mul_left (1 / 2 : ℝ) hinside
  refine hhalf.congr ?_
  intro as
  exact (geom2PNatListNativeBase_eq_half_mass as.1).symm

/-- Exact native-base total: one at length zero and two at positive length. -/
theorem tsum_geom2PNatListNativeBase_exactLength (m : ℕ) :
    (∑' as : {as : List ℕ+ // as.length = m},
      geom2PNatListNativeBase as.1) =
      if m = 0 then 1 else 2 := by
  have hterminal :=
    summable_geom2PNatListMass_mul_terminalValue_exactLength m
  have hmass := summable_geom2PNatListMass_exactLength m
  have htwomass := Summable.mul_left (2 : ℝ) hmass
  calc
    (∑' as : {as : List ℕ+ // as.length = m},
        geom2PNatListNativeBase as.1) =
        ∑' as : {as : List ℕ+ // as.length = m},
          (1 / 2 : ℝ) *
            (geom2PNatListMass as.1 *
                (geom2PNatListTerminalValue as.1 : ℝ) +
              2 * geom2PNatListMass as.1) := by
      apply tsum_congr
      intro as
      exact geom2PNatListNativeBase_eq_half_mass as.1
    _ = (1 / 2 : ℝ) *
        ((∑' as : {as : List ℕ+ // as.length = m},
            geom2PNatListMass as.1 *
              (geom2PNatListTerminalValue as.1 : ℝ)) +
          ∑' as : {as : List ℕ+ // as.length = m},
            2 * geom2PNatListMass as.1) := by
      rw [tsum_mul_left, hterminal.tsum_add htwomass]
    _ = (1 / 2 : ℝ) *
        ((if m = 0 then 0 else 2) + 2 * 1) := by
      rw [tsum_geom2PNatListMass_mul_terminalValue_exactLength,
        hmass.tsum_mul_left, tsum_geom2PNatListMass_exactLength]
    _ = if m = 0 then 1 else 2 := by
      split_ifs <;> norm_num

end

end Tao
end Erdos1135SecondScale
