import CollatzOddBlocks

namespace CollatzResearch.RankGrowth

theorem even_strict_rank_bounds_input (rank : ℕ → ℕ)
    (heven : ∀ m : ℕ, 0 < m → rank m < rank (2 * m))
    (hodd : ∀ m : ℕ, 0 < m → rank (3 * m + 2) ≤ rank (2 * m + 1))
    (n : ℕ) (hn : 0 < n) : n ≤ 2 ^ rank n := by
  have hmain : ∀ q t n : ℕ, rank n = q → twoVal (n + 1) = t →
      0 < n → n ≤ 2 ^ q := by
    intro q
    induction q using Nat.strong_induction_on with
    | h q ihq =>
      intro t
      induction t using Nat.strong_induction_on with
      | h t iht =>
        intro n hq ht hn
        by_cases hbase : n = 1
        · subst n
          exact Nat.one_le_pow q 2 (by omega)
        · by_cases he : n % 2 = 0
          · have hmpos : 0 < n / 2 := by omega
            have hform : n = 2 * (n / 2) := by omega
            have hmrank : rank (n / 2) < q := by
              have hs := heven (n / 2) hmpos
              rwa [← hform, hq] at hs
            have hm := ihq (rank (n / 2)) hmrank (twoVal (n / 2 + 1))
              (n / 2) rfl rfl hmpos
            have hp : 2 ^ (rank (n / 2) + 1) ≤ 2 ^ q :=
              Nat.pow_le_pow_right (by omega) hmrank
            rw [pow_succ] at hp
            omega
          · have hmpos : 0 < n / 2 := by omega
            have hform : n = 2 * (n / 2) + 1 := by omega
            have hmrank : rank (3 * (n / 2) + 2) ≤ q := by
              have hs := hodd (n / 2) hmpos
              rwa [← hform, hq] at hs
            have hmt : twoVal ((3 * (n / 2) + 2) + 1) < t := by
              have hs := twoVal_odd_shortcut (n / 2)
              rwa [← hform, ht] at hs
            have hm : 3 * (n / 2) + 2 ≤ 2 ^ q := by
              rcases lt_or_eq_of_le hmrank with hs | hs
              · have hi := ihq (rank (3 * (n / 2) + 2)) hs
                  (twoVal ((3 * (n / 2) + 2) + 1)) (3 * (n / 2) + 2) rfl rfl (by omega)
                exact le_trans hi (Nat.pow_le_pow_right (by omega) (by omega))
              · exact iht (twoVal ((3 * (n / 2) + 2) + 1)) hmt
                  (3 * (n / 2) + 2) hs rfl (by omega)
            omega
  exact hmain (rank n) (twoVal (n + 1)) n rfl rfl hn

theorem odd_strict_rank_near_powers (rank : ℕ → ℕ)
    (heven : ∀ m : ℕ, 0 < m → rank m ≤ rank (2 * m))
    (hodd : ∀ m : ℕ, 0 < m → rank (3 * m + 2) < rank (2 * m + 1))
    (K c : ℕ) (hc : 0 < c) :
    ∃ L : ℕ, ∀ e t : ℕ, L ≤ e → 0 < t → K ≤ rank (2 ^ e * t - c) := by
  induction K generalizing c with
  | zero => exact ⟨0, by intros; omega⟩
  | succ K ihK =>
    induction c using Nat.strong_induction_on with
    | h c ihc =>
      by_cases he : c % 2 = 0
      · have hhalf : 0 < c / 2 := by omega
        obtain ⟨L, hL⟩ := ihc (c / 2) (by omega) hhalf
        refine ⟨L + c + 3, ?_⟩
        intro e t heL ht
        let p := 2 ^ (e - 1) * t
        have hp : c < p := by
          have hexp := Nat.lt_two_pow_self (n := e - 1)
          have hm := Nat.le_mul_of_pos_right (2 ^ (e - 1)) ht
          dsimp [p]
          omega
        have hpow : 2 ^ e * t = 2 * p := by
          have heq : e = (e - 1) + 1 := by omega
          conv_lhs => rw [heq, pow_succ]
          dsimp [p]
          ring
        have hi := hL (e - 1) t (by omega) ht
        have hs := heven (p - c / 2) (by omega)
        have hform : 2 ^ e * t - c = 2 * (p - c / 2) := by rw [hpow]; omega
        rw [hform]
        exact le_trans hi hs
      · let c' := (3 * c - 1) / 2
        have hc' : 0 < c' := by dsimp [c']; omega
        obtain ⟨L, hL⟩ := ihK c' hc'
        refine ⟨L + c + 3, ?_⟩
        intro e t heL ht
        let p := 2 ^ (e - 1) * t
        have hp : c + 1 < p := by
          have hexp := Nat.lt_two_pow_self (n := e - 1)
          have hm := Nat.le_mul_of_pos_right (2 ^ (e - 1)) ht
          dsimp [p]
          omega
        have hpow : 2 ^ e * t = 2 * p := by
          have heq : e = (e - 1) + 1 := by omega
          conv_lhs => rw [heq, pow_succ]
          dsimp [p]
          ring
        let m := p - (c + 1) / 2
        have hmpos : 0 < m := by dsimp [m]; omega
        have hform : 2 ^ e * t - c = 2 * m + 1 := by rw [hpow]; dsimp [m]; omega
        have hnext : 2 ^ (e - 1) * (3 * t) - c' = 3 * m + 2 := by
          have heq : 2 ^ (e - 1) * (3 * t) = 3 * p := by dsimp [p]; ring
          rw [heq]
          dsimp [m, c']
          omega
        have hi := hL (e - 1) (3 * t) (by omega) (by omega)
        rw [hnext] at hi
        rw [hform]
        exact lt_of_le_of_lt hi (hodd m hmpos)

theorem even_strict_rank_near_powers (rank : ℕ → ℕ)
    (heven : ∀ m : ℕ, 0 < m → rank m < rank (2 * m))
    (hodd : ∀ m : ℕ, 0 < m → rank (3 * m + 2) ≤ rank (2 * m + 1))
    (K c : ℕ) :
    ∃ L : ℕ, ∀ e t : ℕ, L ≤ e → 0 < t → K < rank (2 ^ e * t - c) := by
  refine ⟨c + 2 ^ K + 1, ?_⟩
  intro e t he ht
  have hexp := Nat.lt_two_pow_self (n := e)
  have hm := Nat.le_mul_of_pos_right (2 ^ e) ht
  have hlarge : 2 ^ K < 2 ^ e * t - c := by omega
  have hk : 0 < 2 ^ K := by positivity
  have hb := even_strict_rank_bounds_input rank heven hodd (2 ^ e * t - c) (by omega)
  by_contra hn
  have hp : 2 ^ rank (2 ^ e * t - c) ≤ 2 ^ K :=
    Nat.pow_le_pow_right (by omega) (by omega)
  omega

def wordEval {α : Type*} (a b : α → α) : List Bool → α → α
  | [], x => x
  | bit :: w, x => if bit then b (wordEval a b w x) else a (wordEval a b w x)

def wordLabel : List Bool → ℕ → ℕ
  | [], n => n
  | bit :: w, n => if bit then 2 * wordLabel w n + 1 else 2 * wordLabel w n

theorem wordLabel_affine (w : List Bool) (n : ℕ) :
    wordLabel w n = 2 ^ w.length * n + wordLabel w 0 := by
  induction w with
  | nil => simp [wordLabel]
  | cons bit w ih =>
    cases bit <;> simp only [wordLabel, Bool.false_eq_true, ↓reduceIte, List.length_cons,
      pow_succ, ih] <;> ring

theorem wordLabel_residue_bound (w : List Bool) : wordLabel w 0 < 2 ^ w.length := by
  induction w with
  | nil => simp [wordLabel]
  | cons bit w ih =>
    cases bit <;> simp only [wordLabel, Bool.false_eq_true, ↓reduceIte, List.length_cons,
      pow_succ] <;> omega

theorem wordLabel_pos (w : List Bool) {n : ℕ} (hn : 0 < n) : 0 < wordLabel w n := by
  rw [wordLabel_affine]
  have hp : 0 < 2 ^ w.length * n := by positivity
  omega

theorem binaryInterp_wordLabel {α : Type*} (a b : α → α) (w : List Bool)
    (n : ℕ) (hn : 0 < n) (x : α) :
    ReversedCertificate.binaryInterp a b (wordLabel w n) x =
      wordEval a b w (ReversedCertificate.binaryInterp a b n x) := by
  induction w with
  | nil => rfl
  | cons bit w ih =>
    have hp := wordLabel_pos w hn
    cases bit <;> simp only [wordLabel, wordEval, Bool.false_eq_true, ↓reduceIte,
      ReversedCertificate.binaryInterp_even a b hp, ReversedCertificate.binaryInterp_odd a b hp, ih]

theorem wordLabel_near_power (w : List Bool) (n : ℕ) :
    wordLabel w (2 ^ (n + 1) - 1) =
      2 ^ (w.length + (n + 1)) - (2 ^ w.length - wordLabel w 0) := by
  have hres := wordLabel_residue_bound w
  have hp : 0 < 2 ^ (n + 1) := by positivity
  have hm : 2 ^ w.length * (2 ^ (n + 1) - 1) =
      2 ^ w.length * 2 ^ (n + 1) - 2 ^ w.length := Nat.mul_sub_one _ _
  rw [wordLabel_affine, hm, pow_add 2 w.length (n + 1)]
  have hmpos := Nat.le_mul_of_pos_right (2 ^ w.length) hp
  omega

theorem binaryInterp_all_ones {α : Type*} (a b : α → α) (n : ℕ) (x : α) :
    ReversedCertificate.binaryInterp a b (2 ^ (n + 1) - 1) x = b^[n] x := by
  have h := OddBlocks.reversed_binary_suffix a b n 2 (by omega) x
  simpa only [pow_succ, Nat.reduceSub, ReversedCertificate.binaryInterp_one] using h

theorem reversed_word_b_growth {α : Type*} [Preorder α]
    (c : ReversedCertificate.Data α)
    (hda : ∀ x, c.readout x ≤ c.readout (c.a x))
    (hdb : ∀ x, c.readout (c.g x) ≤ c.readout (c.b x))
    (hs : (∀ x, c.readout x < c.readout (c.a x)) ∨
      (∀ x, c.readout (c.g x) < c.readout (c.b x)))
    (w : List Bool) (K : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      K < c.readout (wordEval c.a c.b w (c.b^[n] c.initial)) := by
  let rank : ℕ → ℕ := fun n => c.readout (ReversedCertificate.binaryInterp c.a c.b n c.initial)
  have heven : ∀ m : ℕ, 0 < m → rank m ≤ rank (2 * m) := by
    intro m hm
    dsimp [rank]
    rw [ReversedCertificate.binaryInterp_even c.a c.b hm]
    exact hda _
  have hodd : ∀ m : ℕ, 0 < m → rank (3 * m + 2) ≤ rank (2 * m + 1) := by
    intro m hm
    dsimp [rank]
    rw [ReversedCertificate.binaryInterp_odd c.a c.b hm]
    exact le_trans (c.readout_monotone
      (ReversedCertificate.ternary_conversion_weak c m hm).2.2) (hdb _)
  let q := 2 ^ w.length - wordLabel w 0
  have hq : 0 < q := by have h := wordLabel_residue_bound w; dsimp [q]; omega
  have hlarge : ∃ L : ℕ, ∀ e t : ℕ, L ≤ e → 0 < t → K < rank (2 ^ e * t - q) := by
    rcases hs with ha | hb
    · apply even_strict_rank_near_powers rank _ hodd K q
      intro m hm
      dsimp [rank]
      rw [ReversedCertificate.binaryInterp_even c.a c.b hm]
      exact ha _
    · have hos : ∀ m : ℕ, 0 < m → rank (3 * m + 2) < rank (2 * m + 1) := by
        intro m hm
        dsimp [rank]
        rw [ReversedCertificate.binaryInterp_odd c.a c.b hm]
        exact lt_of_le_of_lt (c.readout_monotone
          (ReversedCertificate.ternary_conversion_weak c m hm).2.2) (hb _)
      obtain ⟨L, hL⟩ := odd_strict_rank_near_powers rank heven hos (K + 1) q hq
      exact ⟨L, hL⟩
  obtain ⟨L, hL⟩ := hlarge
  refine ⟨L, ?_⟩
  intro n hn
  have hi := hL (w.length + (n + 1)) 1 (by omega) (by omega)
  simp only [Nat.mul_one] at hi
  change K < rank (2 ^ (w.length + (n + 1)) - (2 ^ w.length - wordLabel w 0)) at hi
  rw [← wordLabel_near_power] at hi
  dsimp [rank] at hi
  have hp : 0 < 2 ^ (n + 1) - 1 := by
    have hpow : 0 < 2 ^ n := by positivity
    rw [pow_succ]
    omega
  rwa [binaryInterp_wordLabel c.a c.b w _ hp, binaryInterp_all_ones] at hi

open Matrix ReversedNaturalConditions

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def wordMatrix (A B : Matrix ι ι ℕ) : List Bool → Matrix ι ι ℕ
  | [] => 1
  | bit :: w => (if bit then B else A) * wordMatrix A B w

theorem wordEval_affine (A B : NatAffine ι) (w : List Bool) (x : ι → ℕ) :
    wordEval A.eval B.eval w x =
      wordMatrix A.matrix B.matrix w *ᵥ x + wordEval A.eval B.eval w 0 := by
  induction w with
  | nil => simp [wordEval, wordMatrix]
  | cons bit w ih =>
    cases bit <;> simp only [wordEval, wordMatrix, Bool.false_eq_true, ↓reduceIte]
    all_goals rw [ih]
    all_goals simp only [NatAffine.eval, Matrix.mulVec_add, Matrix.mulVec_mulVec, add_assoc]

theorem observed_wordEval (D A B : NatAffine ι) (i₀ : ι) (w : List Bool) (x : ι → ℕ) :
    D.eval (wordEval A.eval B.eval w x) i₀ =
      (D.matrix i₀ ᵥ* wordMatrix A.matrix B.matrix w) ⬝ᵥ x +
        D.eval (wordEval A.eval B.eval w 0) i₀ := by
  change D.matrix i₀ ⬝ᵥ wordEval A.eval B.eval w x + D.offset i₀ =
    (D.matrix i₀ ᵥ* wordMatrix A.matrix B.matrix w) ⬝ᵥ x +
      (D.matrix i₀ ⬝ᵥ wordEval A.eval B.eval w 0 + D.offset i₀)
  rw [wordEval_affine A B w x, dotProduct_add, dotProduct_mulVec]
  omega

omit [DecidableEq ι] in
theorem natural_reversed_word_b_growth (m : Model ι) (i₀ : ι) (h : WeakRules m)
    (hs : StrictOffset m i₀) (w : List Bool) (K : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      K < m.d.eval (wordEval m.a.eval m.b.eval w (m.b.eval^[n] m.c.offset)) i₀ := by
  let c := ofModel m h i₀
  apply reversed_word_b_growth c _ _ _ w K
  · intro x
    simpa only [NatAffine.eval_comp] using NatAffine.eval_weak h.1 x i₀
  · intro x
    simpa only [NatAffine.eval_comp] using NatAffine.eval_weak h.2.1 x i₀
  · rcases hs with ha | hb
    · left
      intro x
      simpa only [NatAffine.eval_comp] using NatAffine.eval_strict_at h.1 i₀ ha x
    · right
      intro x
      simpa only [NatAffine.eval_comp] using NatAffine.eval_strict_at h.2.1 i₀ hb x

theorem natural_reversed_word_row_growth (m : Model ι) (i₀ : ι) (h : WeakRules m)
    (hs : StrictOffset m i₀) (w : List Bool) (K : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      K < (m.d.matrix i₀ ᵥ* wordMatrix m.a.matrix m.b.matrix w) ⬝ᵥ
        (m.b.eval^[n] m.c.offset) := by
  obtain ⟨N, hN⟩ := natural_reversed_word_b_growth m i₀ h hs w
    (K + m.d.eval (wordEval m.a.eval m.b.eval w 0) i₀)
  refine ⟨N, ?_⟩
  intro n hn
  have hb := hN n hn
  rw [observed_wordEval m.d m.a m.b i₀ w (m.b.eval^[n] m.c.offset)] at hb
  omega

theorem natural_reversed_word_row_nonzero (m : Model ι) (i₀ : ι) (h : WeakRules m)
    (hs : StrictOffset m i₀) (w : List Bool) :
    ∃ j, 0 < (m.d.matrix i₀ ᵥ* wordMatrix m.a.matrix m.b.matrix w) j := by
  classical
  by_contra hn
  have hz : ∀ j, (m.d.matrix i₀ ᵥ* wordMatrix m.a.matrix m.b.matrix w) j = 0 := by
    intro j
    by_contra hne
    exact hn ⟨j, Nat.pos_of_ne_zero hne⟩
  obtain ⟨N, hN⟩ := natural_reversed_word_row_growth m i₀ h hs w 0
  have hb := hN N (by omega)
  simp [dotProduct, hz] at hb

#print axioms even_strict_rank_bounds_input
#print axioms odd_strict_rank_near_powers
#print axioms even_strict_rank_near_powers
#print axioms wordLabel_affine
#print axioms wordLabel_residue_bound
#print axioms wordLabel_pos
#print axioms binaryInterp_wordLabel
#print axioms wordLabel_near_power
#print axioms binaryInterp_all_ones
#print axioms reversed_word_b_growth
#print axioms wordEval_affine
#print axioms observed_wordEval
#print axioms natural_reversed_word_b_growth
#print axioms natural_reversed_word_row_growth
#print axioms natural_reversed_word_row_nonzero

end CollatzResearch.RankGrowth
