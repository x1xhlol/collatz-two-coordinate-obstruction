import FairEnergyWordCore
import Mathlib.Data.Nat.Choose.Cast
import Mathlib.Tactic

set_option autoImplicit false

noncomputable section

namespace CollatzCylinderPacking.Arithmetic.FairEnergy

private def momentMajorant (d : ℕ) (k : ℝ) : ℝ :=
  match d with
  | 0 => 1
  | 1 => 2 * k
  | 2 => 6 * k ^ 2
  | _ => 26 * k ^ 3

private structure MomentBound {α : Type*} (f x : α → ℝ) (c k : ℝ) : Prop where
  mass_nonneg : ∀ a, 0 ≤ f a
  value_nonneg : ∀ a, 0 ≤ x a
  summable : ∀ d ≤ 3, Summable (fun a => f a * x a ^ d)
  bound : ∀ d ≤ 3, (∑' a, f a * x a ^ d) ≤ c * momentMajorant d k

private def geometricMoment (q : ℝ) (d : ℕ) : ℝ :=
  (1 - q) * match d with
  | 0 => 1 / (1 - q)
  | 1 => 1 / (1 - q) ^ 2
  | 2 => 2 / (1 - q) ^ 3 - 1 / (1 - q) ^ 2
  | _ => 6 / (1 - q) ^ 4 - 6 / (1 - q) ^ 3 + 1 / (1 - q) ^ 2

private theorem cast_choose_three_shift (n : ℕ) :
    ((n + 3).choose 3 : ℝ) = ((n : ℝ) + 3) * (n + 2) * (n + 1) / 6 := by
  have h := Nat.descFactorial_eq_factorial_mul_choose (n + 3) 3
  norm_num [Nat.descFactorial_succ, Nat.descFactorial_zero] at h
  have hc := congrArg (fun a : ℕ => (a : ℝ)) h
  push_cast at hc
  nlinarith

private theorem geometric_moment_hasSum {q : ℝ} (hq : ‖q‖ < 1)
    (d : ℕ) (hd : d ≤ 3) :
    HasSum (fun a : ℕ => ((1 - q) * q ^ a) * ((a : ℝ) + 1) ^ d)
      (geometricMoment q d) := by
  have h0 : HasSum (fun a : ℕ => q ^ a) (1 / (1 - q)) := by
    simpa using hasSum_choose_mul_geometric_of_norm_lt_one 0 hq
  have h1 : HasSum (fun a : ℕ => ((a : ℝ) + 1) * q ^ a)
      (1 / (1 - q) ^ 2) := by
    simpa using hasSum_choose_mul_geometric_of_norm_lt_one 1 hq
  have h2 := hasSum_choose_mul_geometric_of_norm_lt_one 2 hq
  have h3 := hasSum_choose_mul_geometric_of_norm_lt_one 3 hq
  interval_cases d
  · simpa [geometricMoment] using h0.mul_left (1 - q)
  · convert h1.mul_left (1 - q) using 1
    ext a
    ring
  · convert ((h2.mul_left 2).sub h1).mul_left (1 - q) using 1
    · ext a
      simp only [Nat.cast_choose_two, Nat.cast_add, Nat.cast_ofNat]
      ring
    · dsimp [geometricMoment]
      ring
  · convert (((h3.mul_left 6).sub (h2.mul_left 6)).add h1).mul_left (1 - q) using 1
    · ext a
      rw [cast_choose_three_shift]
      simp only [Nat.cast_choose_two, Nat.cast_add, Nat.cast_ofNat]
      ring
    · dsimp [geometricMoment]
      ring

private theorem fair_head_momentBound :
    MomentBound (fun a : ℕ => (1 / 2 : ℝ) ^ (a + 1))
      (fun a => (a : ℝ) + 1) 1 1 := by
  have h (d : ℕ) (hd : d ≤ 3) :
      HasSum (fun a : ℕ => (1 / 2 : ℝ) ^ (a + 1) * ((a : ℝ) + 1) ^ d)
        (geometricMoment (1 / 2) d) := by
    simpa only [pow_succ', show (1 - (1 / 2 : ℝ)) = 1 / 2 by norm_num] using
      geometric_moment_hasSum (q := 1 / 2) (by norm_num) d hd
  refine ⟨fun _ => by positivity, fun _ => by positivity,
    fun d hd => (h d hd).summable, ?_⟩
  intro d hd
  rw [(h d hd).tsum_eq]
  interval_cases d <;> norm_num [geometricMoment, momentMajorant]

private theorem biased_head_momentBound :
    MomentBound (fun a : ℕ => 3 * (1 / 4 : ℝ) ^ (a + 1))
      (fun a => (a : ℝ) + 1) 1 1 := by
  have h (d : ℕ) (hd : d ≤ 3) :
      HasSum (fun a : ℕ => (3 * (1 / 4 : ℝ) ^ (a + 1)) * ((a : ℝ) + 1) ^ d)
        (geometricMoment (1 / 4) d) := by
    convert geometric_moment_hasSum (q := 1 / 4) (by norm_num) d hd using 1
    ext a
    rw [pow_succ']
    ring
  refine ⟨fun _ => by positivity, fun _ => by positivity,
    fun d hd => (h d hd).summable, ?_⟩
  intro d hd
  rw [(h d hd).tsum_eq]
  interval_cases d <;> norm_num [geometricMoment, momentMajorant]

private theorem MomentBound.add {α : Type*} {f g x : α → ℝ} {c e k : ℝ}
    (hf : MomentBound f x c k) (hg : MomentBound g x e k) :
    MomentBound (fun a => f a + g a) x (c + e) k := by
  refine ⟨fun a => add_nonneg (hf.mass_nonneg a) (hg.mass_nonneg a),
    hf.value_nonneg, ?_, ?_⟩
  · intro d hd
    simpa only [add_mul] using (hf.summable d hd).add (hg.summable d hd)
  · intro d hd
    simp only [add_mul]
    rw [(hf.summable d hd).tsum_add (hg.summable d hd)]
    nlinarith [hf.bound d hd, hg.bound d hd]

private theorem MomentBound.mul_const {α : Type*} {f x : α → ℝ} {c k r : ℝ}
    (hf : MomentBound f x c k) (hr : 0 ≤ r) :
    MomentBound (fun a => r * f a) x (r * c) k := by
  refine ⟨fun a => mul_nonneg hr (hf.mass_nonneg a), hf.value_nonneg, ?_, ?_⟩
  · intro d hd
    simpa only [mul_assoc] using (hf.summable d hd).mul_left r
  · intro d hd
    simp only [mul_assoc]
    rw [tsum_mul_left]
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_left (hf.bound d hd) hr

private def momentConvolution (F G : ℕ → ℝ) (d : ℕ) : ℝ :=
  match d with
  | 0 => F 0 * G 0
  | 1 => F 1 * G 0 + F 0 * G 1
  | 2 => F 2 * G 0 + 2 * (F 1 * G 1) + F 0 * G 2
  | _ => F 3 * G 0 + 3 * (F 2 * G 1) + 3 * (F 1 * G 2) + F 0 * G 3

private theorem moment_tensor_hasSum {α β : Type*} {f x : α → ℝ} {g y : β → ℝ}
    {c e k l : ℝ} (hf : MomentBound f x c k) (hg : MomentBound g y e l)
    (d : ℕ) (hd : d ≤ 3) :
    HasSum (fun p : α × β => f p.1 * g p.2 * (x p.1 + y p.2) ^ d)
      (momentConvolution (fun i => ∑' a, f a * x a ^ i)
        (fun j => ∑' b, g b * y b ^ j) d) := by
  have h (i j : ℕ) (hi : i ≤ 3) (hj : j ≤ 3) :
      HasSum (fun p : α × β => (f p.1 * x p.1 ^ i) * (g p.2 * y p.2 ^ j))
        ((∑' a, f a * x a ^ i) * (∑' b, g b * y b ^ j)) := by
    exact (hf.summable i hi).hasSum.mul (hg.summable j hj).hasSum
      ((hf.summable i hi).mul_of_nonneg (hg.summable j hj)
        (fun a => mul_nonneg (hf.mass_nonneg a) (pow_nonneg (hf.value_nonneg a) _))
        (fun b => mul_nonneg (hg.mass_nonneg b) (pow_nonneg (hg.value_nonneg b) _)))
  interval_cases d
  · simpa [momentConvolution] using h 0 0 (by omega) (by omega)
  · convert (h 1 0 (by omega) (by omega)).add (h 0 1 (by omega) (by omega)) using 1
    · ext p
      ring
  · convert ((h 2 0 (by omega) (by omega)).add
      ((h 1 1 (by omega) (by omega)).mul_left 2)).add
      (h 0 2 (by omega) (by omega)) using 1
    · ext p
      ring
  · convert (((h 3 0 (by omega) (by omega)).add
      ((h 2 1 (by omega) (by omega)).mul_left 3)).add
      ((h 1 2 (by omega) (by omega)).mul_left 3)).add
      (h 0 3 (by omega) (by omega)) using 1
    · ext p
      ring

private theorem MomentBound.tensor_step {α β : Type*} {f x : α → ℝ} {g y : β → ℝ}
    {c k : ℝ} (hf : MomentBound f x 1 1) (hg : MomentBound g y c k)
    (hc : 0 ≤ c) (hk : 0 ≤ k) :
    MomentBound (fun p : α × β => f p.1 * g p.2)
      (fun p => x p.1 + y p.2) c (k + 1) := by
  refine ⟨fun p => mul_nonneg (hf.mass_nonneg p.1) (hg.mass_nonneg p.2),
    fun p => add_nonneg (hf.value_nonneg p.1) (hg.value_nonneg p.2),
    fun d hd => (moment_tensor_hasSum hf hg d hd).summable, ?_⟩
  intro d hd
  rw [(moment_tensor_hasSum hf hg d hd).tsum_eq]
  have hp (i j : ℕ) (hi : i ≤ 3) (hj : j ≤ 3) :
      (∑' a, f a * x a ^ i) * (∑' b, g b * y b ^ j) ≤
        momentMajorant i 1 * (c * momentMajorant j k) := by
    have hfi : (∑' a, f a * x a ^ i) ≤ momentMajorant i 1 := by
      simpa using hf.bound i hi
    exact mul_le_mul hfi (hg.bound j hj)
      (tsum_nonneg fun b => mul_nonneg (hg.mass_nonneg b)
        (pow_nonneg (hg.value_nonneg b) _))
      (by interval_cases i <;> norm_num [momentMajorant])
  calc
    momentConvolution _ _ d ≤
        momentConvolution (fun i => momentMajorant i 1)
          (fun j => c * momentMajorant j k) d := by
      interval_cases d
      · exact hp 0 0 (by omega) (by omega)
      · exact add_le_add (hp 1 0 (by omega) (by omega)) (hp 0 1 (by omega) (by omega))
      · exact add_le_add
          (add_le_add (hp 2 0 (by omega) (by omega))
            (mul_le_mul_of_nonneg_left (hp 1 1 (by omega) (by omega)) (by norm_num)))
          (hp 0 2 (by omega) (by omega))
      · exact add_le_add
          (add_le_add
            (add_le_add (hp 3 0 (by omega) (by omega))
              (mul_le_mul_of_nonneg_left (hp 2 1 (by omega) (by omega)) (by norm_num)))
            (mul_le_mul_of_nonneg_left (hp 1 2 (by omega) (by omega)) (by norm_num)))
          (hp 0 3 (by omega) (by omega))
    _ ≤ c * momentMajorant d (k + 1) := by
      interval_cases d <;> simp only [momentConvolution, momentMajorant]
      all_goals nlinarith [mul_nonneg hc hk, mul_nonneg hc (sq_nonneg k)]

private theorem fair_word_momentBound (k : ℕ) :
    MomentBound (fun w : GeometricWord k => (1 / 2 : ℝ) ^ wordLength k w)
      (fun w => (wordLength k w : ℝ)) 1 k := by
  induction k with
  | zero =>
    refine ⟨fun _ => by positivity, fun _ => by positivity, ?_, ?_⟩
    · intro d _
      letI : Finite (GeometricWord 0) := by
        change Finite Unit
        infer_instance
      exact Summable.of_finite
    · intro d hd
      interval_cases d <;> simp [GeometricWord, wordLength, momentMajorant]
  | succ k ih =>
    rw [Nat.cast_add, Nat.cast_one]
    convert fair_head_momentBound.tensor_step ih (by norm_num) (by positivity) using 1
    · ext ⟨a, w⟩
      simp [wordLength, pow_add]
    · ext ⟨a, w⟩
      simp [wordLength]

private def translationWeight (k : ℕ) (w : GeometricWord k) : ℝ :=
  biasedWordWeight k w * (1 + wordTranslation k w)

private theorem biased_tilt (k : ℕ) (w : GeometricWord k) :
    biasedWordWeight k w * ((2 : ℝ) ^ wordLength k w / (3 : ℝ) ^ k) =
      (1 / 2 : ℝ) ^ wordLength k w := by
  unfold biasedWordWeight
  calc
    (3 : ℝ) ^ k * (1 / 4 : ℝ) ^ wordLength k w *
        ((2 : ℝ) ^ wordLength k w / (3 : ℝ) ^ k) =
        ((1 / 4 : ℝ) ^ wordLength k w * (2 : ℝ) ^ wordLength k w) *
          ((3 : ℝ) ^ k / (3 : ℝ) ^ k) := by ring
    _ = (1 / 2 : ℝ) ^ wordLength k w := by
      rw [div_self (by positivity : (3 : ℝ) ^ k ≠ 0), mul_one, ← mul_pow]
      norm_num

private theorem translationWeight_succ (k a : ℕ) (w : GeometricWord k) :
    translationWeight (k + 1) (a, w) =
      (3 * (1 / 4 : ℝ) ^ (a + 1)) *
        (translationWeight k w + (1 / 3) * (1 / 2 : ℝ) ^ wordLength k w) := by
  unfold translationWeight
  rw [biasedWordWeight_succ, wordTranslation_succ, ← biased_tilt k w]
  ring

private theorem translation_word_momentBound (k : ℕ) :
    MomentBound (translationWeight k) (fun w => (wordLength k w : ℝ))
      (1 + (k : ℝ) / 3) k := by
  induction k with
  | zero =>
    refine ⟨fun w => by simp [translationWeight, biasedWordWeight_zero, wordTranslation_zero],
      fun _ => by positivity, ?_, ?_⟩
    · intro d _
      letI : Finite (GeometricWord 0) := by
        change Finite Unit
        infer_instance
      exact Summable.of_finite
    · intro d hd
      interval_cases d <;>
        simp [GeometricWord, wordLength, translationWeight,
          biasedWordWeight_zero, wordTranslation_zero, momentMajorant]
  | succ k ih =>
    have hmix := ih.add ((fair_word_momentBound k).mul_const (r := 1 / 3) (by norm_num))
    have hstep := biased_head_momentBound.tensor_step hmix (by positivity) (by positivity)
    rw [Nat.cast_add, Nat.cast_one]
    convert hstep using 1
    · ext ⟨a, w⟩
      exact translationWeight_succ k a w
    · ext ⟨a, w⟩
      simp only [wordLength, Nat.cast_add, Nat.cast_one]
    · ring

theorem cubicMomentTerm_summable (k : ℕ) : Summable (cubicMomentTerm k) := by
  convert (translation_word_momentBound k).summable 3 (by omega) using 1
  ext w
  unfold cubicMomentTerm translationWeight
  ring

theorem cubicMomentTerm_tsum_le (k : ℕ) :
    (∑' w : GeometricWord k, cubicMomentTerm k w) ≤
      26 * (k : ℝ) ^ 3 + (26 / 3) * (k : ℝ) ^ 4 := by
  have h := (translation_word_momentBound k).bound 3 (by omega)
  have he : (fun w : GeometricWord k =>
      translationWeight k w * (wordLength k w : ℝ) ^ 3) = cubicMomentTerm k := by
    ext w
    unfold cubicMomentTerm translationWeight
    ring
  rw [he] at h
  dsimp [momentMajorant] at h
  nlinarith

#print axioms cubicMomentTerm_summable
#print axioms cubicMomentTerm_tsum_le

noncomputable def quadraticMomentTerm (k : ℕ) (w : GeometricWord k) : ℝ :=
  biasedWordWeight k w * (wordLength k w : ℝ) ^ 2 * (1 + wordTranslation k w)

theorem quadraticMomentTerm_nonneg (k : ℕ) (w : GeometricWord k) :
    0 ≤ quadraticMomentTerm k w := by
  unfold quadraticMomentTerm
  exact mul_nonneg
    (mul_nonneg (biasedWordWeight_nonneg k w) (sq_nonneg _))
    (by linarith [wordTranslation_nonneg k w])

theorem quadraticMomentTerm_summable (k : ℕ) : Summable (quadraticMomentTerm k) := by
  convert (translation_word_momentBound k).summable 2 (by omega) using 1
  ext w
  unfold quadraticMomentTerm translationWeight
  ring

theorem quadraticMomentTerm_tsum_le (k : ℕ) :
    (∑' w : GeometricWord k, quadraticMomentTerm k w) ≤
      6 * (k : ℝ) ^ 2 + 2 * (k : ℝ) ^ 3 := by
  have h := (translation_word_momentBound k).bound 2 (by omega)
  have he : (fun w : GeometricWord k =>
      translationWeight k w * (wordLength k w : ℝ) ^ 2) = quadraticMomentTerm k := by
    ext w
    unfold quadraticMomentTerm translationWeight
    ring
  rw [he] at h
  dsimp [momentMajorant] at h
  nlinarith

#print axioms quadraticMomentTerm_summable
#print axioms quadraticMomentTerm_tsum_le

end CollatzCylinderPacking.Arithmetic.FairEnergy
