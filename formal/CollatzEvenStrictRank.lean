import CollatzCore

namespace CollatzResearch

def twoVal (n : ℕ) : ℕ :=
  if n = 0 then 0
  else if n % 2 = 0 then twoVal (n / 2) + 1 else 0
termination_by n
decreasing_by omega

theorem twoVal_even {m : ℕ} (hm : 0 < m) :
    twoVal (2 * m) = twoVal m + 1 := by
  rw [twoVal]
  have hne : 2 * m ≠ 0 := by omega
  simp [hne]

theorem twoVal_mul_three (m : ℕ) : twoVal (3 * m) = twoVal m := by
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hz : m = 0
    · subst m
      rfl
    · by_cases he : m % 2 = 0
      · have hp : 0 < m / 2 := by omega
        have hform : m = 2 * (m / 2) := by omega
        have hi := ih (m / 2) (by omega)
        calc
          twoVal (3 * m) = twoVal (2 * (3 * (m / 2))) := by
            congr 1
            omega
          _ = twoVal (3 * (m / 2)) + 1 := twoVal_even (by omega)
          _ = twoVal (m / 2) + 1 := by rw [hi]
          _ = twoVal m := by conv_rhs => rw [hform, twoVal_even hp]
      · have hne : 3 * m ≠ 0 := by omega
        have he3 : (3 * m) % 2 ≠ 0 := by omega
        conv_lhs => rw [twoVal]
        conv_rhs => rw [twoVal]
        simp [hz, he, hne, he3]

theorem twoVal_odd_shortcut (m : ℕ) :
    twoVal ((3 * m + 2) + 1) < twoVal ((2 * m + 1) + 1) := by
  have hleft : (3 * m + 2) + 1 = 3 * (m + 1) := by omega
  have hright : (2 * m + 1) + 1 = 2 * (m + 1) := by omega
  rw [hleft, hright, twoVal_mul_three, twoVal_even (by omega)]
  omega

theorem collatz_of_even_strict_rank (rank : ℕ → ℕ)
    (heven : ∀ m : ℕ, 0 < m → rank m < rank (2 * m))
    (hodd : ∀ m : ℕ, 0 < m → rank (3 * m + 2) ≤ rank (2 * m + 1)) :
    CollatzConjecture := by
  have hmain : ∀ q t n : ℕ, rank n = q → twoVal (n + 1) = t →
      0 < n → ReachesOne n := by
    intro q
    induction q using Nat.strong_induction_on with
    | h q ihq =>
      intro t
      induction t using Nat.strong_induction_on with
      | h t iht =>
        intro n hq ht hn
        by_cases hbase : n = 1
        · exact ⟨0, hbase⟩
        · by_cases he : n % 2 = 0
          · have hmpos : 0 < n / 2 := by omega
            have hform : n = 2 * (n / 2) := by omega
            have hmrank : rank (n / 2) < q := by
              calc
                rank (n / 2) < rank (2 * (n / 2)) := heven (n / 2) hmpos
                _ = q := by rw [← hform, hq]
            have hm := ihq (rank (n / 2)) hmrank (twoVal (n / 2 + 1))
              (n / 2) rfl rfl hmpos
            apply reaches_one_of_reachable (k := 1) (m := n / 2) _ hm
            simp [step, he]
          · have hmpos : 0 < n / 2 := by omega
            have hform : n = 2 * (n / 2) + 1 := by omega
            have hmrank : rank (3 * (n / 2) + 2) ≤ q := by
              calc
                rank (3 * (n / 2) + 2) ≤ rank (2 * (n / 2) + 1) :=
                  hodd (n / 2) hmpos
                _ = q := by rw [← hform, hq]
            have hmt : twoVal ((3 * (n / 2) + 2) + 1) < t := by
              calc
                twoVal ((3 * (n / 2) + 2) + 1) <
                    twoVal ((2 * (n / 2) + 1) + 1) := twoVal_odd_shortcut (n / 2)
                _ = t := by rw [← hform, ht]
            have hm : ReachesOne (3 * (n / 2) + 2) := by
              rcases lt_or_eq_of_le hmrank with hs | hs
              · exact ihq (rank (3 * (n / 2) + 2)) hs
                  (twoVal ((3 * (n / 2) + 2) + 1)) (3 * (n / 2) + 2) rfl rfl (by omega)
              · exact iht (twoVal ((3 * (n / 2) + 2) + 1)) hmt
                  (3 * (n / 2) + 2) hs rfl (by omega)
            apply reaches_one_of_reachable (k := 2) (m := 3 * (n / 2) + 2) _ hm
            rw [hform, two_steps_odd]
            omega
  intro n hn
  exact hmain (rank n) (twoVal (n + 1)) n rfl rfl hn

#print axioms twoVal_even
#print axioms twoVal_mul_three
#print axioms twoVal_odd_shortcut
#print axioms collatz_of_even_strict_rank

end CollatzResearch
