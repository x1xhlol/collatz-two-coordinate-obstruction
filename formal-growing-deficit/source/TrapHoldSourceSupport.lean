import Erdos1135.Tao.Renewal.SourceRegeneration

/-! Exact source-support bridges, adapted from Section7SChiActualQ for arbitrary horizons. -/

set_option autoImplicit false

namespace Erdos1135.Tao

theorem trap_holdPoint_length_eq_sourceHitPoint
    (pre : List ℕ) :
    taoSection7HoldPointOfPrefix pre.length pre =
      taoSection7SourceHitPoint (1 : ℕ+) 0 pre := by
  ext
  · apply Subtype.ext
    simp [taoSection7HoldPointOfPrefix, taoSection7SourceHitPoint,
      taoSection7ShiftIndex]
    omega
  · simp [taoSection7HoldPointOfPrefix, taoSection7HoldTerminalSum,
      taoSection7SourceHitPoint]

theorem trap_holdPoint_length_eq_increment
    (pre : List ℕ) :
    taoSection7HoldPointOfPrefix pre.length pre =
      taoSection7HoldIncrementOfPrefix pre := by
  ext
  · apply Subtype.ext
    simp [taoSection7HoldPointOfPrefix, taoSection7HoldIncrementOfPrefix,
      taoSection7ShiftIndex]
    omega
  · simp [taoSection7HoldPointOfPrefix, taoSection7HoldTerminalSum,
      taoSection7HoldIncrementOfPrefix]

theorem trap_holdSourcePrefix_toReal_ne_zero_support
    {m : ℕ} {pre : List ℕ}
    (h : (taoSection7HoldSourcePrefixPMF (m, pre)).toReal ≠ 0) :
    m = pre.length ∧ taoSection7NoThree pre := by
  have hinner :
      (taoSection7PascalPrimeSourceListPMF m pre).toReal ≠ 0 := by
    intro hzero
    rw [taoSection7HoldSourcePrefixPMF_apply_toReal, hzero, mul_zero] at h
    exact h rfl
  have hpmf : taoSection7PascalPrimeSourceListPMF m pre ≠ 0 := by
    intro hzero
    rw [hzero] at hinner
    exact hinner rfl
  have hlen : m = pre.length := by
    by_contra hne
    exact hpmf (taoSection7PascalPrimeSourceListPMF_apply_eq_zero_of_length_ne
      m pre (fun hlen => hne hlen.symm))
  exact ⟨hlen,
    taoSection7PascalPrimeSourceListPMF_apply_ne_zero_noThree hpmf⟩

theorem trap_holdSourceList_toReal_ne_zero_support
    {N : ℕ} {xs : List (ℕ × List ℕ)}
    (h : (taoSection7HoldSourcePrefixListPMF N xs).toReal ≠ 0) :
    xs.length = N ∧
      ∀ x ∈ xs, x.1 = x.2.length ∧ taoSection7NoThree x.2 := by
  have hlen : xs.length = N := by
    by_contra hne
    have hzero := taoSection7HoldSourcePrefixListPMF_apply_eq_zero_of_length_ne
      N xs hne
    rw [hzero] at h
    exact h rfl
  refine ⟨hlen, ?_⟩
  induction N generalizing xs with
  | zero =>
      have hnil : xs = [] := by simpa using hlen
      subst xs
      simp
  | succ N ih =>
      cases xs with
      | nil => simp at hlen
      | cons x xs =>
          have hprod :
              (taoSection7HoldSourcePrefixPMF x).toReal *
                  (taoSection7HoldSourcePrefixListPMF N xs).toReal ≠ 0 := by
            simpa [taoSection7HoldSourcePrefixListPMF_succ_apply_cons,
              ENNReal.toReal_mul] using h
          have hhead : (taoSection7HoldSourcePrefixPMF x).toReal ≠ 0 := by
            intro hzero
            exact hprod (by rw [hzero, zero_mul])
          have htail :
              (taoSection7HoldSourcePrefixListPMF N xs).toReal ≠ 0 := by
            intro hzero
            exact hprod (by rw [hzero, mul_zero])
          have hlenTail : xs.length = N := by simpa using hlen
          have hsTail := ih htail hlenTail
          intro y hy
          simp only [List.mem_cons] at hy
          rcases hy with rfl | hy
          · exact trap_holdSourcePrefix_toReal_ne_zero_support hhead
          · exact hsTail y hy

theorem trap_holdPoint_map_eq_increments_of_supported
    (xs : List (ℕ × List ℕ))
    (hsupp : ∀ x ∈ xs, x.1 = x.2.length) :
    xs.map (fun x => taoSection7HoldPointOfPrefix x.1 x.2) =
      taoSection7HoldIncrementsOfPrefixes (xs.map Prod.snd) := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
      have hx := hsupp x (by simp)
      have htail : ∀ y ∈ xs, y.1 = y.2.length := by
        intro y hy
        exact hsupp y (by simp [hy])
      rw [List.map_cons, taoSection7HoldIncrementsOfPrefixes]
      simp only [List.map_cons]
      rw [ih htail]
      congr 1
      rcases x with ⟨m, pre⟩
      rw [hx]
      exact trap_holdPoint_length_eq_increment pre

end Erdos1135.Tao
