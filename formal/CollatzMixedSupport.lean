import CollatzSupportFamily

namespace CollatzResearch.MixedSupport

inductive Digit where
  | a | b | e | f | g
  deriving DecidableEq

def radix : Digit → ℕ
  | .a | .b => 2
  | .e | .f | .g => 3

def residue : Digit → ℕ
  | .a | .e => 0
  | .b | .f => 1
  | .g => 2

def scale : List Digit → ℕ
  | [] => 1
  | k :: w => radix k * scale w

def label : List Digit → ℕ → ℕ
  | [], n => n
  | k :: w, n => radix k * label w n + residue k

def eval {α : Type*} (maps : Digit → α → α) : List Digit → α → α
  | [], x => x
  | k :: w, x => maps k (eval maps w x)

def digitMap {α : Type*} [Preorder α] (c : ReversedCertificate.Data α) : Digit → α → α
  | .a => c.a
  | .b => c.b
  | .e => c.e
  | .f => c.f
  | .g => c.g

theorem scale_pos (w : List Digit) : 0 < scale w := by
  induction w with
  | nil => decide
  | cons k w ih => cases k <;> simp only [scale, radix] <;> omega

theorem label_affine (w : List Digit) (n : ℕ) :
    label w n = scale w * n + label w 0 := by
  induction w with
  | nil => simp [label, scale]
  | cons k w ih => simp only [label, scale, ih]; ring

theorem label_residue_bound (w : List Digit) : label w 0 < scale w := by
  induction w with
  | nil => decide
  | cons k w ih => cases k <;> simp only [label, scale, radix, residue] <;> omega

theorem label_pos (w : List Digit) {n : ℕ} (hn : 0 < n) : 0 < label w n := by
  rw [label_affine]
  have hp := Nat.mul_pos (scale_pos w) hn
  omega

theorem label_near_power (w : List Digit) (n : ℕ) :
    label w (2 ^ (n + 1) - 1) =
      2 ^ (n + 1) * scale w - (scale w - label w 0) := by
  have hres := label_residue_bound w
  have hp : 0 < 2 ^ (n + 1) := by positivity
  have hm := Nat.le_mul_of_pos_right (scale w) hp
  rw [label_affine, Nat.mul_sub_one, Nat.mul_comm (scale w)]
  rw [Nat.mul_comm (scale w)] at hm
  omega

theorem interp_digit_le {α : Type*} [Preorder α] (c : ReversedCertificate.Data α)
    (k : Digit) (n : ℕ) (hn : 0 < n) :
    ReversedCertificate.binaryInterp c.a c.b (radix k * n + residue k) c.initial ≤
      digitMap c k (ReversedCertificate.binaryInterp c.a c.b n c.initial) := by
  cases k
  · simp only [radix, residue, Nat.add_zero, digitMap,
      ReversedCertificate.binaryInterp_even c.a c.b hn, le_refl]
  · simp only [radix, residue, digitMap,
      ReversedCertificate.binaryInterp_odd c.a c.b hn, le_refl]
  · exact (ReversedCertificate.ternary_conversion_weak c n hn).1
  · exact (ReversedCertificate.ternary_conversion_weak c n hn).2.1
  · exact (ReversedCertificate.ternary_conversion_weak c n hn).2.2

theorem interp_label_le {α : Type*} [Preorder α] (c : ReversedCertificate.Data α)
    (hmono : ∀ k, Monotone (digitMap c k)) (w : List Digit) (n : ℕ) (hn : 0 < n) :
    ReversedCertificate.binaryInterp c.a c.b (label w n) c.initial ≤
      eval (digitMap c) w (ReversedCertificate.binaryInterp c.a c.b n c.initial) := by
  induction w with
  | nil => exact le_refl _
  | cons k w ih =>
    exact le_trans (interp_digit_le c k (label w n) (label_pos w hn)) (hmono k ih)

theorem reversed_mixed_b_growth {α : Type*} [Preorder α]
    (c : ReversedCertificate.Data α) (hmono : ∀ k, Monotone (digitMap c k))
    (hda : ∀ x, c.readout x ≤ c.readout (c.a x))
    (hdb : ∀ x, c.readout (c.g x) ≤ c.readout (c.b x))
    (hs : (∀ x, c.readout x < c.readout (c.a x)) ∨
      (∀ x, c.readout (c.g x) < c.readout (c.b x)))
    (w : List Digit) (K : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      K < c.readout (eval (digitMap c) w (c.b^[n] c.initial)) := by
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
  let q := scale w - label w 0
  have hq : 0 < q := by have hb := label_residue_bound w; dsimp [q]; omega
  have hlarge : ∃ L : ℕ, ∀ e t : ℕ, L ≤ e → 0 < t → K < rank (2 ^ e * t - q) := by
    rcases hs with ha | hb
    · apply RankGrowth.even_strict_rank_near_powers rank _ hodd K q
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
      obtain ⟨L, hL⟩ := RankGrowth.odd_strict_rank_near_powers rank heven hos (K + 1) q hq
      exact ⟨L, hL⟩
  obtain ⟨L, hL⟩ := hlarge
  refine ⟨L, ?_⟩
  intro n hn
  have hi := hL (n + 1) (scale w) (by omega) (scale_pos w)
  change K < rank (2 ^ (n + 1) * scale w - (scale w - label w 0)) at hi
  rw [← label_near_power] at hi
  have hp : 0 < 2 ^ (n + 1) - 1 := by
    have hpow : 0 < 2 ^ n := by positivity
    rw [pow_succ]
    omega
  have hm := c.readout_monotone (interp_label_le c hmono w (2 ^ (n + 1) - 1) hp)
  rw [RankGrowth.binaryInterp_all_ones] at hm
  exact lt_of_lt_of_le hi hm

open Matrix ReversedNaturalConditions

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def affineMap (m : Model ι) : Digit → NatAffine ι
  | .a => m.a
  | .b => m.b
  | .e => m.e
  | .f => m.f
  | .g => m.g

def matrixWord (maps : Digit → Matrix ι ι ℕ) : List Digit → Matrix ι ι ℕ
  | [] => 1
  | k :: w => maps k * matrixWord maps w

theorem eval_affine (maps : Digit → NatAffine ι) (w : List Digit) (x : ι → ℕ) :
    eval (fun k => (maps k).eval) w x =
      matrixWord (fun k => (maps k).matrix) w *ᵥ x + eval (fun k => (maps k).eval) w 0 := by
  induction w with
  | nil => simp [eval, matrixWord]
  | cons k w ih =>
    simp only [eval, matrixWord, ih, NatAffine.eval, Matrix.mulVec_add,
      Matrix.mulVec_mulVec, add_assoc]

theorem observed_eval (D : NatAffine ι) (maps : Digit → NatAffine ι)
    (i₀ : ι) (w : List Digit) (x : ι → ℕ) :
    D.eval (eval (fun k => (maps k).eval) w x) i₀ =
      (D.matrix i₀ ᵥ* matrixWord (fun k => (maps k).matrix) w) ⬝ᵥ x +
        D.eval (eval (fun k => (maps k).eval) w 0) i₀ := by
  change D.matrix i₀ ⬝ᵥ eval (fun k => (maps k).eval) w x + D.offset i₀ =
    (D.matrix i₀ ᵥ* matrixWord (fun k => (maps k).matrix) w) ⬝ᵥ x +
      (D.matrix i₀ ⬝ᵥ eval (fun k => (maps k).eval) w 0 + D.offset i₀)
  rw [eval_affine maps w x, dotProduct_add, dotProduct_mulVec]
  omega

omit [DecidableEq ι] in
theorem natural_mixed_b_growth (m : Model ι) (i₀ : ι) (h : WeakRules m)
    (hs : StrictOffset m i₀) (w : List Digit) (K : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      K < m.d.eval (eval (fun k => (affineMap m k).eval) w (m.b.eval^[n] m.c.offset)) i₀ := by
  let c := ofModel m h i₀
  have hm : (fun k => (affineMap m k).eval) = digitMap c := by
    funext k
    cases k <;> rfl
  rw [hm]
  apply reversed_mixed_b_growth c _ _ _ _ w K
  · intro k
    cases k <;> exact NatAffine.eval_monotone _
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

theorem natural_mixed_row_growth (m : Model ι) (i₀ : ι) (h : WeakRules m)
    (hs : StrictOffset m i₀) (w : List Digit) (K : ℕ) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
      K < (m.d.matrix i₀ ᵥ* matrixWord (fun k => (affineMap m k).matrix) w) ⬝ᵥ
        (m.b.eval^[n] m.c.offset) := by
  obtain ⟨N, hN⟩ := natural_mixed_b_growth m i₀ h hs w
    (K + m.d.eval (eval (fun k => (affineMap m k).eval) w 0) i₀)
  refine ⟨N, ?_⟩
  intro n hn
  have hb := hN n hn
  rw [observed_eval m.d (affineMap m) i₀ w (m.b.eval^[n] m.c.offset)] at hb
  omega

theorem mixed_source_support (m : Model ι) (i₀ : ι) (h : WeakRules m)
    (hs : StrictOffset m i₀) (w : List Digit) :
    ∃ k : ℕ, Fintype.card ι ≤ k ∧ k < 2 * Fintype.card ι ∧
      ((m.d.matrix i₀ ᵥ* matrixWord (fun k => (affineMap m k).matrix) w) ᵥ* m.b.matrix ^ k) ⬝ᵥ
        (m.c.offset + m.b.offset) > 0 := by
  letI : Nonempty ι := ⟨i₀⟩
  exact FiniteSourceSupport.unbounded_iterates_have_finite_source_support m.b
    (m.d.matrix i₀ ᵥ* matrixWord (fun k => (affineMap m k).matrix) w) m.c.offset
    (natural_mixed_row_growth m i₀ h hs w)

theorem matrixWord_append (maps : Digit → Matrix ι ι ℕ) (v w : List Digit) :
    matrixWord maps (v ++ w) = matrixWord maps v * matrixWord maps w := by
  induction v with
  | nil => simp [matrixWord]
  | cons k v ih => simp only [List.cons_append, matrixWord, ih, Matrix.mul_assoc]

theorem reversed_closed_safe_family (m : Model ι) (i₀ : ι) (h : WeakRules m)
    (hs : StrictOffset m i₀) :
    ∃ F : Finset (Finset ι), SupportFamily.rowSupport (m.d.matrix i₀) ∈ F ∧
      ∀ S ∈ F, (∀ k : Digit, SupportFamily.successor (affineMap m k).matrix S ∈ F) ∧
        ∃ i ∈ S, i ∈ SupportFamily.sourceGood m.b.matrix (m.c.offset + m.b.offset) := by
  classical
  let maps := fun k => (affineMap m k).matrix
  let F : Finset (Finset ι) := Finset.univ.filter (fun S =>
    ∃ w : List Digit, SupportFamily.rowSupport (m.d.matrix i₀ ᵥ* matrixWord maps w) = S)
  have hF (S : Finset ι) : S ∈ F ↔
      ∃ w : List Digit, SupportFamily.rowSupport (m.d.matrix i₀ ᵥ* matrixWord maps w) = S := by
    simp only [F, Finset.mem_filter, Finset.mem_univ, true_and]
  refine ⟨F, ?_, ?_⟩
  · rw [hF]
    exact ⟨[], by simp [matrixWord]⟩
  · intro S hS
    obtain ⟨w, rfl⟩ := (hF S).mp hS
    constructor
    · intro k
      rw [hF]
      refine ⟨w ++ [k], ?_⟩
      rw [matrixWord_append]
      simp only [matrixWord, Matrix.mul_one]
      rw [← vecMul_vecMul, SupportFamily.support_vecMul]
    · exact SupportFamily.source_support_intersection m.b.matrix _ _
        (mixed_source_support m i₀ h hs w)

#print axioms scale_pos
#print axioms label_affine
#print axioms label_residue_bound
#print axioms label_pos
#print axioms label_near_power
#print axioms interp_digit_le
#print axioms interp_label_le
#print axioms reversed_mixed_b_growth
#print axioms eval_affine
#print axioms observed_eval
#print axioms natural_mixed_b_growth
#print axioms natural_mixed_row_growth
#print axioms mixed_source_support
#print axioms matrixWord_append
#print axioms reversed_closed_safe_family

end CollatzResearch.MixedSupport
