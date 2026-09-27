import Mathlib.Data.Real.Basic
import Mathlib.LinearAlgebra.Matrix.DotProduct
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
import Mathlib.Tactic.Linarith

namespace CollatzCertificate

open Matrix

variable {n : Type*} [Fintype n]

abbrev Vec (n : Type*) := n → ℝ
abbrev Mat (n : Type*) := Matrix n n ℝ

def EntrywiseLE (M N : Mat n) : Prop := ∀ i j, M i j ≤ N i j

local infix:50 " ≤ₘ " => EntrywiseLE

lemma rowMul_nonneg {s : Vec n} {M : Mat n}
    (hs : 0 ≤ s) (hM : 0 ≤ₘ M) : 0 ≤ s ᵥ* M := by
  intro j
  exact Finset.sum_nonneg (fun i _ => mul_nonneg (hs i) (hM i j))

lemma rowMul_mono_row {s t : Vec n} {M : Mat n}
    (hst : s ≤ t) (hM : 0 ≤ₘ M) : s ᵥ* M ≤ t ᵥ* M := by
  intro j
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_right (hst i) (hM i j))

lemma rowMul_mono_matrix {s : Vec n} {M N : Mat n}
    (hs : 0 ≤ s) (hMN : M ≤ₘ N) : s ᵥ* M ≤ s ᵥ* N := by
  intro j
  exact Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hMN i j) (hs i))

structure Admissible (A B G : Mat n) (b g s : Vec n) : Prop where
  nonneg : 0 ≤ s
  da : s ≤ s ᵥ* A
  dbMatrix : s ᵥ* G ≤ s ᵥ* B
  dbOffset : s ⬝ᵥ g ≤ s ⬝ᵥ b

theorem admissible_mul_B
    {A B G : Mat n} {b g s : Vec n}
    (hB : 0 ≤ₘ B) (hb : 0 ≤ b)
    (hBA : A * B ≤ₘ B * A) (hGB : B * G ≤ₘ G * B)
    (hgb : B *ᵥ g + b ≤ G *ᵥ b + g)
    (hs : Admissible A B G b g s) :
    Admissible A B G b g (s ᵥ* B) := by
  have hsB := rowMul_nonneg hs.nonneg hB
  have hda : s ᵥ* B ≤ (s ᵥ* B) ᵥ* A := by
    calc
      s ᵥ* B ≤ (s ᵥ* A) ᵥ* B := rowMul_mono_row hs.da hB
      _ = s ᵥ* (A * B) := vecMul_vecMul _ _ _
      _ ≤ s ᵥ* (B * A) := rowMul_mono_matrix hs.nonneg hBA
      _ = (s ᵥ* B) ᵥ* A := (vecMul_vecMul _ _ _).symm
  have hdb : (s ᵥ* B) ᵥ* G ≤ (s ᵥ* B) ᵥ* B := by
    calc
      (s ᵥ* B) ᵥ* G = s ᵥ* (B * G) := vecMul_vecMul _ _ _
      _ ≤ s ᵥ* (G * B) := rowMul_mono_matrix hs.nonneg hGB
      _ = (s ᵥ* G) ᵥ* B := (vecMul_vecMul _ _ _).symm
      _ ≤ (s ᵥ* B) ᵥ* B := rowMul_mono_row hs.dbMatrix hB
  have h1 := dotProduct_le_dotProduct_of_nonneg_right hs.dbMatrix hb
  have h2 := dotProduct_le_dotProduct_of_nonneg_left hgb hs.nonneg
  simp only [dotProduct_add, dotProduct_mulVec] at h2
  refine ⟨hsB, hda, hdb, ?_⟩
  linarith [hs.dbOffset]

theorem admissible_zero_gaps
    {A B G : Mat n} {a b g γ s : Vec n}
    (hB : 0 ≤ₘ B) (ha : 0 ≤ a) (hγ : 0 ≤ γ)
    (hBA : A * B ≤ₘ B * A)
    (hgc : (B * A) *ᵥ γ + B *ᵥ a + b ≤ G *ᵥ γ + g)
    (hs : Admissible A B G b g s) :
    s ⬝ᵥ g = s ⬝ᵥ b ∧ (s ᵥ* B) ⬝ᵥ a = 0 := by
  have hrow : s ᵥ* G ≤ s ᵥ* (B * A) := by
    calc
      s ᵥ* G ≤ s ᵥ* B := hs.dbMatrix
      _ ≤ (s ᵥ* A) ᵥ* B := rowMul_mono_row hs.da hB
      _ = s ᵥ* (A * B) := vecMul_vecMul _ _ _
      _ ≤ s ᵥ* (B * A) := rowMul_mono_matrix hs.nonneg hBA
  have h1 := dotProduct_le_dotProduct_of_nonneg_right hrow hγ
  have h2 := dotProduct_le_dotProduct_of_nonneg_left hgc hs.nonneg
  have h3 := dotProduct_nonneg_of_nonneg (rowMul_nonneg hs.nonneg hB) ha
  simp only [dotProduct_add, dotProduct_mulVec] at h2
  constructor <;> linarith [hs.dbOffset]

variable [DecidableEq n]

lemma rowMul_pow_nonneg {r : Vec n} {B : Mat n}
    (hr : 0 ≤ r) (hB : 0 ≤ₘ B) (k : ℕ) : 0 ≤ r ᵥ* B ^ k := by
  induction k with
  | zero => simpa using hr
  | succ k ih =>
    simpa [pow_succ, vecMul_vecMul] using rowMul_nonneg ih hB

theorem binary_power_closure
    {A B G : Mat n} {a b g γ r : Vec n}
    (hB : 0 ≤ₘ B) (ha : 0 ≤ a) (hb : 0 ≤ b) (hγ : 0 ≤ γ)
    (hBA : A * B ≤ₘ B * A) (hGB : B * G ≤ₘ G * B)
    (hgc : (B * A) *ᵥ γ + B *ᵥ a + b ≤ G *ᵥ γ + g)
    (hgb : B *ᵥ g + b ≤ G *ᵥ b + g)
    (hr : Admissible A B G b g r) :
    ∀ k : ℕ,
      Admissible A B G b g (r ᵥ* B ^ k) ∧
      (r ᵥ* B ^ k) ⬝ᵥ g = (r ᵥ* B ^ k) ⬝ᵥ b ∧
      (r ᵥ* B ^ (k + 1)) ⬝ᵥ a = 0 := by
  have hadm : ∀ k : ℕ, Admissible A B G b g (r ᵥ* B ^ k) := by
    intro k
    induction k with
    | zero => simpa using hr
    | succ k ih =>
      simpa [pow_succ, vecMul_vecMul] using
        admissible_mul_B hB hb hBA hGB hgb ih
  intro k
  have hz := admissible_zero_gaps hB ha hγ hBA hgc (hadm k)
  exact ⟨hadm k, hz.1, by simpa [pow_succ, vecMul_vecMul] using hz.2⟩

lemma polynomial_readout_of_positive_powers_zero
    {B : Mat n} {r a : Vec n}
    (hz : ∀ k : ℕ, (r ᵥ* B ^ (k + 1)) ⬝ᵥ a = 0)
    (p : Polynomial ℝ) :
    (r ᵥ* Polynomial.aeval B p) ⬝ᵥ a = p.coeff 0 * (r ⬝ᵥ a) := by
  induction p using Polynomial.induction_on' with
  | add p q ihp ihq =>
    simp only [map_add, vecMul_add, add_dotProduct, Polynomial.coeff_add]
    rw [ihp, ihq, add_mul]
  | monomial k c =>
    rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one,
      smul_mul_assoc, one_mul, vecMul_smul, smul_dotProduct]
    cases k with
    | zero => simp
    | succ k => simp [hz k]

theorem first_gap_zero_of_det_ne_zero
    {B : Mat n} {r a : Vec n}
    (hz : ∀ k : ℕ, (r ᵥ* B ^ (k + 1)) ⬝ᵥ a = 0)
    (hdet : B.det ≠ 0) : r ⬝ᵥ a = 0 := by
  have hpoly := polynomial_readout_of_positive_powers_zero hz B.charpoly
  rw [Matrix.aeval_self_charpoly, vecMul_zero, zero_dotProduct] at hpoly
  have hc : B.charpoly.coeff 0 ≠ 0 := by
    intro h
    apply hdet
    rw [Matrix.det_eq_sign_charpoly_coeff, h, mul_zero]
  exact (mul_eq_zero.mp hpoly.symm).resolve_left hc

theorem first_gap_zero_of_return_bound
    {B : Mat n} {r a : Vec n} {K : ℝ} {d : ℕ}
    (hr : 0 ≤ r) (ha : 0 ≤ a)
    (hz : ∀ k : ℕ, (r ᵥ* B ^ (k + 1)) ⬝ᵥ a = 0)
    (hbound : r ≤ K • ∑ k ∈ Finset.range d, r ᵥ* B ^ (k + 1)) :
    r ⬝ᵥ a = 0 := by
  have h := dotProduct_le_dotProduct_of_nonneg_right hbound ha
  have hnonneg := dotProduct_nonneg_of_nonneg hr ha
  simp only [smul_dotProduct, sum_dotProduct, hz, Finset.sum_const_zero, smul_zero] at h
  exact le_antisymm h hnonneg

theorem first_gap_zero_of_coordinate_returns
    {B : Mat n} {r a : Vec n}
    (hr : 0 ≤ r) (hB : 0 ≤ₘ B) (ha : 0 ≤ a)
    (hz : ∀ k : ℕ, (r ᵥ* B ^ (k + 1)) ⬝ᵥ a = 0)
    (hreturn : ∀ i, 0 < r i → ∃ k : ℕ, 0 < (r ᵥ* B ^ (k + 1)) i) :
    r ⬝ᵥ a = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  by_cases hri : r i = 0
  · simp [hri]
  have hri' : 0 < r i := lt_of_le_of_ne (hr i) (Ne.symm hri)
  obtain ⟨k, hk⟩ := hreturn i hri'
  have hp := rowMul_pow_nonneg hr hB (k + 1)
  have hterm : (r ᵥ* B ^ (k + 1)) i * a i = 0 := by
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_nonneg (hp j) (ha j))).mp (hz k) i (Finset.mem_univ i)
  have hai : a i = 0 := (mul_eq_zero.mp hterm).resolve_left (ne_of_gt hk)
  simp [hai]

theorem positive_first_gap_has_transient_coordinate
    {B : Mat n} {r a : Vec n}
    (hr : 0 ≤ r) (hB : 0 ≤ₘ B) (ha : 0 ≤ a)
    (hz : ∀ k : ℕ, (r ᵥ* B ^ (k + 1)) ⬝ᵥ a = 0)
    (hgap : 0 < r ⬝ᵥ a) :
    ∃ i, 0 < r i ∧ 0 < a i ∧ ∀ k : ℕ, (r ᵥ* B ^ (k + 1)) i = 0 := by
  obtain ⟨i, _, hi⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun j _ => mul_nonneg (hr j) (ha j))).mp hgap
  have hri : 0 < r i := pos_of_mul_pos_left hi (ha i)
  have hai : 0 < a i := pos_of_mul_pos_right hi (hr i)
  refine ⟨i, hri, hai, ?_⟩
  intro k
  have hp := rowMul_pow_nonneg hr hB (k + 1)
  have hterm : (r ᵥ* B ^ (k + 1)) i * a i = 0 := by
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => mul_nonneg (hp j) (ha j))).mp (hz k) i (Finset.mem_univ i)
  exact (mul_eq_zero.mp hterm).resolve_right (ne_of_gt hai)

theorem ordered_reversed_gaps_zero_of_det_ne_zero
    {A B G : Mat n} {a b g γ r : Vec n}
    (hB : 0 ≤ₘ B) (ha : 0 ≤ a) (hb : 0 ≤ b) (hγ : 0 ≤ γ)
    (hBA : A * B ≤ₘ B * A) (hGB : B * G ≤ₘ G * B)
    (hgc : (B * A) *ᵥ γ + B *ᵥ a + b ≤ G *ᵥ γ + g)
    (hgb : B *ᵥ g + b ≤ G *ᵥ b + g)
    (hr : Admissible A B G b g r) (hdet : B.det ≠ 0) :
    r ⬝ᵥ a = 0 ∧ r ⬝ᵥ (b - g) = 0 := by
  have h := binary_power_closure hB ha hb hγ hBA hGB hgc hgb hr
  refine ⟨first_gap_zero_of_det_ne_zero (fun k => (h k).2.2) hdet, ?_⟩
  have hzero := (h 0).2.1
  simpa [dotProduct_sub] using sub_eq_zero.mpr hzero.symm

omit [DecidableEq n] in
theorem first_gap_le_BAa
    {A B F G : Mat n} {a b e f g r : Vec n}
    (hA : 0 ≤ₘ A) (hB : 0 ≤ₘ B) (hF : 0 ≤ₘ F) (hG : 0 ≤ₘ G)
    (ha : 0 ≤ a) (he : 0 ≤ e) (hf : 0 ≤ f)
    (hgaMatrix : A * F ≤ₘ G * A)
    (hgaOffset : A *ᵥ f + a ≤ G *ᵥ a + g)
    (hfaOffset : B *ᵥ e + b ≤ F *ᵥ a + f)
    (hr : Admissible A B G b g r)
    (hBa : (r ᵥ* B) ⬝ᵥ a = 0) (hbg : r ⬝ᵥ b = r ⬝ᵥ g) :
    r ⬝ᵥ a ≤ (r ᵥ* (B * A)) ⬝ᵥ a := by
  have hGa : (r ᵥ* G) ⬝ᵥ a = 0 := by
    have hle := dotProduct_le_dotProduct_of_nonneg_right hr.dbMatrix ha
    have hnonneg := dotProduct_nonneg_of_nonneg (rowMul_nonneg hr.nonneg hG) ha
    linarith
  have hrow : r ᵥ* F ≤ r ᵥ* (B * A) := by
    calc
      r ᵥ* F ≤ (r ᵥ* A) ᵥ* F := rowMul_mono_row hr.da hF
      _ = r ᵥ* (A * F) := vecMul_vecMul _ _ _
      _ ≤ r ᵥ* (G * A) := rowMul_mono_matrix hr.nonneg hgaMatrix
      _ = (r ᵥ* G) ᵥ* A := (vecMul_vecMul _ _ _).symm
      _ ≤ (r ᵥ* B) ᵥ* A := rowMul_mono_row hr.dbMatrix hA
      _ = r ᵥ* (B * A) := vecMul_vecMul _ _ _
  have h1 := dotProduct_le_dotProduct_of_nonneg_left hgaOffset hr.nonneg
  have h2 := dotProduct_le_dotProduct_of_nonneg_left hfaOffset hr.nonneg
  have h3 := dotProduct_le_dotProduct_of_nonneg_right hr.da hf
  have h4 := dotProduct_nonneg_of_nonneg (rowMul_nonneg hr.nonneg hB) he
  have h5 := dotProduct_le_dotProduct_of_nonneg_right hrow ha
  simp only [dotProduct_add, dotProduct_mulVec] at h1 h2
  linarith

theorem first_gap_zero_of_BA_return_bound
    {A B F G : Mat n} {a b e f g r : Vec n} {K : ℝ} {d : ℕ}
    (hA : 0 ≤ₘ A) (hB : 0 ≤ₘ B) (hF : 0 ≤ₘ F) (hG : 0 ≤ₘ G)
    (ha : 0 ≤ a) (he : 0 ≤ e) (hf : 0 ≤ f)
    (hgaMatrix : A * F ≤ₘ G * A)
    (hgaOffset : A *ᵥ f + a ≤ G *ᵥ a + g)
    (hfaOffset : B *ᵥ e + b ≤ F *ᵥ a + f)
    (hr : Admissible A B G b g r)
    (hz : ∀ k : ℕ, (r ᵥ* B ^ (k + 1)) ⬝ᵥ a = 0)
    (hbg : r ⬝ᵥ b = r ⬝ᵥ g)
    (hbound : r ᵥ* (B * A) ≤ K • ∑ k ∈ Finset.range d, r ᵥ* B ^ (k + 1)) :
    r ⬝ᵥ a = 0 := by
  have hBa : (r ᵥ* B) ⬝ᵥ a = 0 := by simpa using hz 0
  have h1 := first_gap_le_BAa hA hB hF hG ha he hf
    hgaMatrix hgaOffset hfaOffset hr hBa hbg
  have h2 := dotProduct_le_dotProduct_of_nonneg_right hbound ha
  simp only [smul_dotProduct, sum_dotProduct, hz, Finset.sum_const_zero, smul_zero] at h2
  exact le_antisymm (h1.trans h2) (dotProduct_nonneg_of_nonneg hr.nonneg ha)

structure Affine (n : Type*) where
  matrix : Mat n
  offset : Vec n

def Affine.comp (X Y : Affine n) : Affine n :=
  ⟨X.matrix * Y.matrix, X.matrix *ᵥ Y.offset + X.offset⟩

def Affine.Nonnegative (X : Affine n) : Prop :=
  (0 ≤ₘ X.matrix) ∧ 0 ≤ X.offset

def Affine.Weak (X Y : Affine n) : Prop :=
  (Y.matrix ≤ₘ X.matrix) ∧ Y.offset ≤ X.offset

theorem four_affine_rules_gaps_zero_of_det_ne_zero
    (A B G C D : Affine n) (i₀ : n)
    (hA : A.Nonnegative) (hB : B.Nonnegative)
    (hC : C.Nonnegative) (hD : D.Nonnegative)
    (hda : (D.comp A).Weak D)
    (hdb : (D.comp B).Weak (D.comp G))
    (hgc : (G.comp C).Weak (B.comp (A.comp C)))
    (hgb : (G.comp B).Weak (B.comp G))
    (hBA : A.matrix * B.matrix ≤ₘ B.matrix * A.matrix)
    (hdet : B.matrix.det ≠ 0) :
    ((D.comp A).offset - D.offset) i₀ = 0 ∧
    ((D.comp B).offset - (D.comp G).offset) i₀ = 0 := by
  let r : Vec n := D.matrix i₀
  have hr : Admissible A.matrix B.matrix G.matrix B.offset G.offset r := by
    refine ⟨fun j => hD.1 i₀ j, ?_, ?_, ?_⟩
    · intro j
      exact hda.1 i₀ j
    · intro j
      exact hdb.1 i₀ j
    · have h := hdb.2 i₀
      change (D.matrix *ᵥ G.offset) i₀ + D.offset i₀ ≤
        (D.matrix *ᵥ B.offset) i₀ + D.offset i₀ at h
      exact (add_le_add_iff_right (D.offset i₀)).mp h
  have hgc' : (B.matrix * A.matrix) *ᵥ C.offset + B.matrix *ᵥ A.offset + B.offset ≤
      G.matrix *ᵥ C.offset + G.offset := by
    have h := hgc.2
    change B.matrix *ᵥ (A.matrix *ᵥ C.offset + A.offset) + B.offset ≤
      G.matrix *ᵥ C.offset + G.offset at h
    simpa only [mulVec_add, mulVec_mulVec] using h
  have h := ordered_reversed_gaps_zero_of_det_ne_zero
    hB.1 hA.2 hB.2 hC.2 hBA hgb.1 hgc' hgb.2 hr hdet
  constructor
  · change (r ⬝ᵥ A.offset + D.offset i₀) - D.offset i₀ = 0
    linarith [h.1]
  · change (r ⬝ᵥ B.offset + D.offset i₀) -
      (r ⬝ᵥ G.offset + D.offset i₀) = 0
    simpa only [dotProduct_sub, add_sub_add_right_eq_sub] using h.2

#print axioms binary_power_closure
#print axioms first_gap_zero_of_det_ne_zero
#print axioms first_gap_zero_of_return_bound
#print axioms first_gap_zero_of_coordinate_returns
#print axioms positive_first_gap_has_transient_coordinate
#print axioms ordered_reversed_gaps_zero_of_det_ne_zero
#print axioms first_gap_le_BAa
#print axioms first_gap_zero_of_BA_return_bound
#print axioms four_affine_rules_gaps_zero_of_det_ne_zero

end CollatzCertificate
