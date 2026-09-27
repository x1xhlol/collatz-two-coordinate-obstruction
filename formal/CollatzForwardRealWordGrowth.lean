import CollatzReversedRealCertificate
import CollatzForwardFiveCover
import CollatzForwardRealContraction

namespace CollatzResearch.ForwardRealWordGrowth

open Matrix CollatzCertificate RealAffine

inductive Root where
  | e | f | g
  deriving DecidableEq

def Root.value : Root → ℕ
  | .e => 0
  | .f => 1
  | .g => 2

def Root.toFin (h : Root) : Fin 3 := ⟨h.value, by cases h <;> decide⟩

def Root.ofFin (h : Fin 3) : Root := if h.val = 0 then .e else if h.val = 1 then .f else .g

theorem Root.ofFin_toFin (h : Root) : Root.ofFin h.toFin = h := by
  cases h <;> rfl

theorem Root.toFin_ofFin (h : Fin 3) : (Root.ofFin h).toFin = h := by
  fin_cases h <;> rfl

def bit : Bool → ℕ
  | false => 0
  | true => 1

def value : List Bool → ℕ
  | [] => 0
  | b :: w => bit b * 2 ^ w.length + value w

def code (w : List Bool) : ℕ := 2 ^ w.length + value w

def swap : Bool → Root → Root × Bool
  | false, .e => (.e, false)
  | false, .f => (.e, true)
  | false, .g => (.f, false)
  | true, .e => (.f, true)
  | true, .f => (.g, false)
  | true, .g => (.g, true)

def carry : List Bool → Root → Root × List Bool
  | [], h => (h, [])
  | b :: w, h =>
      let s := carry w h
      let t := swap b s.1
      (t.1, t.2 :: s.2)

def rootPrefix : Root → List Bool
  | .e => [true]
  | .f => [false, false]
  | .g => [false, true]

def next (w : List Bool) : List Bool :=
  rootPrefix (carry w .e).1 ++ (carry w .e).2

def stage : ℕ → List Bool
  | 0 => []
  | n + 1 => next (stage n)

def stageRoot (n : ℕ) : Root := (carry (stage n) .e).1

theorem value_lt (w : List Bool) : value w < 2 ^ w.length := by
  induction w with
  | nil => simp [value]
  | cons b w ih =>
    cases b <;> simp only [value, bit, List.length_cons, pow_succ] <;> omega

theorem carry_length (w : List Bool) (h : Root) : (carry w h).2.length = w.length := by
  induction w generalizing h with
  | nil => rfl
  | cons b w ih => simp [carry, ih]

theorem carry_value (w : List Bool) (h : Root) :
    3 * value w + h.value =
      2 ^ w.length * (carry w h).1.value + value (carry w h).2 := by
  induction w generalizing h with
  | nil => simp [carry, value]
  | cons b w ih =>
    have hi := ih h
    have hl := carry_length w h
    generalize hs : carry w h = s at hi hl ⊢
    rcases s with ⟨s, v⟩
    cases b <;> cases s <;>
      simp only [carry, hs, swap, value, bit, Root.value, List.length_cons,
        hl, pow_succ] at * <;> omega

theorem value_append (u v : List Bool) :
    value (u ++ v) = value u * 2 ^ v.length + value v := by
  induction u with
  | nil => simp [value]
  | cons b u ih =>
    simp only [List.cons_append, value, List.length_append, pow_add, ih]
    ring

theorem next_code (w : List Bool) : code (next w) = 3 * code w := by
  have hi := carry_value w .e
  have hl := carry_length w .e
  generalize hs : carry w .e = s at hi hl ⊢
  rcases s with ⟨s, v⟩
  cases s <;>
    simp only [code, next, hs, rootPrefix, value_append, List.length_append,
      List.length_cons, List.length_nil, value, bit, Root.value, hl, pow_add] at * <;> norm_num at * <;> omega

theorem stage_code (n : ℕ) : code (stage n) = 3 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [stage, next_code, ih, pow_succ, Nat.mul_comm]

theorem stage_bounds (n : ℕ) :
    2 ^ (stage n).length ≤ 3 ^ n ∧ 3 ^ n < 2 ^ ((stage n).length + 1) := by
  have hc := stage_code n
  have hv := value_lt (stage n)
  simp only [code] at hc
  rw [pow_succ]
  omega

theorem stage_root_bounds (n : ℕ) :
    (3 + (stageRoot n).value) * 2 ^ (stage n).length ≤ 3 * 3 ^ n ∧
      3 * 3 ^ n < (4 + (stageRoot n).value) * 2 ^ (stage n).length := by
  have hc := stage_code n
  have hi := carry_value (stage n) .e
  have hv := value_lt (carry (stage n) .e).2
  rw [carry_length] at hv
  simp only [code] at hc
  change 3 * value (stage n) + 0 = _ at hi
  change (3 + (carry (stage n) .e).1.value) * _ ≤ _ ∧
    _ < (4 + (carry (stage n) .e).1.value) * _
  constructor <;> nlinarith

theorem power_window_unique (m t : ℕ) (x : ℝ)
    (hm : (2 : ℝ) ^ m ≤ x ∧ x < 2 ^ (m + 1))
    (ht : (2 : ℝ) ^ t < x ∧ x < 2 ^ (t + 1)) : m = t := by
  apply le_antisymm
  · by_contra hh
    have htm : t + 1 ≤ m := by omega
    have hp : (2 : ℝ) ^ (t + 1) ≤ 2 ^ m := pow_le_pow_right₀ (by norm_num) htm
    linarith
  · by_contra hh
    have hmt : m + 1 ≤ t := by omega
    have hp : (2 : ℝ) ^ (m + 1) ≤ 2 ^ t := pow_le_pow_right₀ (by norm_num) hmt
    linarith

theorem stage_five_cover (k : ℕ) (h : Root) :
    ∃ j : ℕ, j < 5 ∧ stageRoot (k + j) = h := by
  let m := (stage k).length
  let x : ℝ := 3 ^ k / 2 ^ m
  have hp : (0 : ℝ) < 2 ^ m := by positivity
  have hb := stage_bounds k
  have hb0 : (2 : ℝ) ^ m ≤ 3 ^ k := by exact_mod_cast hb.1
  have hb1 : (3 : ℝ) ^ k < 2 ^ (m + 1) := by exact_mod_cast hb.2
  have hx0 : 1 ≤ x := by
    exact (le_div_iff₀ hp).mpr (by simpa using hb0)
  have hx1 : x ≤ 2 := by
    apply (div_le_iff₀ hp).mpr
    rw [pow_succ] at hb1
    linarith
  obtain ⟨j, t, hj, hl, hu⟩ := ForwardFiveCover.five_stage_cover x hx0 hx1 h.toFin
  have heq : (3 : ℝ) ^ j * x / 2 ^ t = 3 ^ (k + j) / 2 ^ (m + t) := by
    dsimp [x]
    rw [pow_add, pow_add]
    field_simp
  rw [heq] at hl hu
  have hp' : (0 : ℝ) < 2 ^ (m + t) := by positivity
  have hh : (h.value : ℝ) ≤ 2 := by cases h <;> norm_num [Root.value]
  have hhn : (0 : ℝ) ≤ h.value := Nat.cast_nonneg _
  have hy0 : 1 < (3 : ℝ) ^ (k + j) / 2 ^ (m + t) := by
    change (3 + (h.value : ℝ)) / 3 < _ at hl
    linarith
  have hy1 : (3 : ℝ) ^ (k + j) / 2 ^ (m + t) < 2 := by
    change _ < (4 + (h.value : ℝ)) / 3 at hu
    linarith
  have hc0 : (2 : ℝ) ^ (m + t) < 3 ^ (k + j) := by
    simpa using (lt_div_iff₀ hp').mp hy0
  have hc1 : (3 : ℝ) ^ (k + j) < 2 ^ (m + t + 1) := by
    have hi := (div_lt_iff₀ hp').mp hy1
    rw [pow_succ]
    linarith
  have hn := stage_bounds (k + j)
  have hn0 : (2 : ℝ) ^ (stage (k + j)).length ≤ 3 ^ (k + j) := by
    exact_mod_cast hn.1
  have hn1 : (3 : ℝ) ^ (k + j) < 2 ^ ((stage (k + j)).length + 1) := by
    exact_mod_cast hn.2
  have hm := power_window_unique _ _ _ ⟨hn0, hn1⟩ ⟨hc0, hc1⟩
  have hr := stage_root_bounds (k + j)
  have hr0 : (3 + ((stageRoot (k + j)).value : ℝ)) *
      2 ^ (stage (k + j)).length ≤ 3 * 3 ^ (k + j) := by exact_mod_cast hr.1
  have hr1 : (3 : ℝ) * 3 ^ (k + j) <
      (4 + ((stageRoot (k + j)).value : ℝ)) * 2 ^ (stage (k + j)).length := by
    exact_mod_cast hr.2
  rw [hm] at hr0 hr1
  have hl' := (lt_div_iff₀ hp').mp hl
  have hu' := (div_lt_iff₀ hp').mp hu
  refine ⟨j, hj, ?_⟩
  cases h <;> cases hs : stageRoot (k + j) <;>
    norm_num [Root.toFin, Root.value, hs] at hl' hu' hr0 hr1 ⊢ <;> nlinarith

theorem stage_five_cover_fin (k : ℕ) (h : Fin 3) :
    ∃ j : ℕ, j < 5 ∧ (stageRoot (k + j)).toFin = h := by
  obtain ⟨j, hj, hh⟩ := stage_five_cover k (Root.ofFin h)
  exact ⟨j, hj, by rw [hh, Root.toFin_ofFin]⟩

variable {ι : Type*} [Fintype ι]

structure Data (ι : Type*) [Fintype ι] where
  A : Affine ι
  B : Affine ι
  C : Affine ι
  E : Affine ι
  F : Affine ι
  G : Affine ι
  hA : A.Nonnegative
  hB : B.Nonnegative
  hC : C.Nonnegative
  hE : E.Nonnegative
  hF : F.Nonnegative
  hG : G.Nonnegative
  ae : (A.comp E).Weak (E.comp A)
  af : (A.comp F).Weak (E.comp B)
  ag : (A.comp G).Weak (F.comp A)
  be : (B.comp E).Weak (F.comp B)
  bf : (B.comp F).Weak (G.comp A)
  bg : (B.comp G).Weak (G.comp B)
  ce : (C.comp E).Weak (C.comp B)
  cf : (C.comp F).Weak (C.comp (A.comp A))
  cg : (C.comp G).Weak (C.comp (A.comp B))

def Data.binary (d : Data ι) : Bool → Affine ι
  | false => d.A
  | true => d.B

def Data.ternary (d : Data ι) : Root → Affine ι
  | .e => d.E
  | .f => d.F
  | .g => d.G

def Data.word (d : Data ι) : List Bool → Vec ι → Vec ι
  | [], x => x
  | b :: w, x => eval (d.binary b) (d.word w x)

def Data.gap (d : Data ι) (i : ι) : Root → ℝ
  | .e => (d.C.comp d.E).offset i - (d.C.comp d.B).offset i
  | .f => (d.C.comp d.F).offset i - (d.C.comp (d.A.comp d.A)).offset i
  | .g => (d.C.comp d.G).offset i - (d.C.comp (d.A.comp d.B)).offset i

theorem Data.binary_nonnegative (d : Data ι) (b : Bool) :
    (d.binary b).Nonnegative := by
  cases b
  · exact d.hA
  · exact d.hB

theorem Data.ternary_nonnegative (d : Data ι) (h : Root) :
    (d.ternary h).Nonnegative := by
  cases h
  · exact d.hE
  · exact d.hF
  · exact d.hG

theorem Data.word_nonnegative (d : Data ι) (w : List Bool)
    (x : Vec ι) (hx : 0 ≤ x) : 0 ≤ d.word w x := by
  induction w with
  | nil => exact hx
  | cons b w ih => exact eval_nonnegative (d.binary_nonnegative b) ih

theorem Data.word_append (d : Data ι) (u v : List Bool) (x : Vec ι) :
    d.word (u ++ v) x = d.word u (d.word v x) := by
  induction u with
  | nil => rfl
  | cons b u ih => simp only [List.cons_append, Data.word, ih]

theorem Data.gap_nonnegative (d : Data ι) (i : ι) (h : Root) : 0 ≤ d.gap i h := by
  cases h
  · exact sub_nonneg.mpr (d.ce.2 i)
  · exact sub_nonneg.mpr (d.cf.2 i)
  · exact sub_nonneg.mpr (d.cg.2 i)

theorem Data.swap_eval (d : Data ι) (b : Bool) (h : Root)
    (x : Vec ι) (hx : 0 ≤ x) :
    eval (d.ternary (swap b h).1) (eval (d.binary (swap b h).2) x) ≤
      eval (d.binary b) (eval (d.ternary h) x) := by
  cases b <;> cases h
  · simpa only [swap, Data.ternary, Data.binary, eval_comp] using eval_weak d.ae hx
  · simpa only [swap, Data.ternary, Data.binary, eval_comp] using eval_weak d.af hx
  · simpa only [swap, Data.ternary, Data.binary, eval_comp] using eval_weak d.ag hx
  · simpa only [swap, Data.ternary, Data.binary, eval_comp] using eval_weak d.be hx
  · simpa only [swap, Data.ternary, Data.binary, eval_comp] using eval_weak d.bf hx
  · simpa only [swap, Data.ternary, Data.binary, eval_comp] using eval_weak d.bg hx

theorem Data.carry_eval (d : Data ι) (w : List Bool) (h : Root)
    (x : Vec ι) (hx : 0 ≤ x) :
    eval (d.ternary (carry w h).1) (d.word (carry w h).2 x) ≤
      d.word w (eval (d.ternary h) x) := by
  induction w generalizing h with
  | nil => exact le_rfl
  | cons b w ih =>
    exact (d.swap_eval b (carry w h).1 _
      (d.word_nonnegative _ x hx)).trans
      (eval_monotone (d.binary_nonnegative b).1 (ih h))

theorem Data.root_gap_eval (d : Data ι) (i : ι) (h : Root)
    (x : Vec ι) (hx : 0 ≤ x) :
    eval d.C (d.word (rootPrefix h) x) i + d.gap i h ≤
      eval d.C (eval (d.ternary h) x) i := by
  cases h
  · simpa only [rootPrefix, Data.word, Data.binary, Data.ternary, Data.gap, eval_comp]
      using eval_offset_gap d.ce i hx
  · simpa only [rootPrefix, Data.word, Data.binary, Data.ternary, Data.gap, eval_comp]
      using eval_offset_gap d.cf i hx
  · simpa only [rootPrefix, Data.word, Data.binary, Data.ternary, Data.gap, eval_comp]
      using eval_offset_gap d.cg i hx

theorem Data.next_gap_eval (d : Data ι) (i : ι) (w : List Bool)
    (x : Vec ι) (hx : 0 ≤ x) :
    eval d.C (d.word (next w) x) i + d.gap i (carry w .e).1 ≤
      eval d.C (d.word w (eval d.E x)) i := by
  rw [next, d.word_append]
  exact (d.root_gap_eval i _ _ (d.word_nonnegative _ x hx)).trans
    (eval_monotone d.hC.1 (d.carry_eval w .e x hx) i)

theorem Data.iterate_nonnegative (d : Data ι) (n : ℕ) :
    0 ≤ (eval d.E)^[n] (0 : Vec ι) := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    exact eval_nonnegative d.hE ih

theorem Data.partial_conversion (d : Data ι) (i : ι) (n k : ℕ) (hk : k ≤ n) :
    eval d.C (d.word (stage k) ((eval d.E)^[n - k] 0)) i +
      ∑ j ∈ Finset.range k, d.gap i (stageRoot j) ≤
        eval d.C ((eval d.E)^[n] 0) i := by
  induction k with
  | zero => simp only [stage, Data.word, Nat.sub_zero, Finset.range_zero,
      Finset.sum_empty, add_zero, le_refl]
  | succ k ih =>
    have hp := ih (by omega)
    have hs := d.next_gap_eval i (stage k) ((eval d.E)^[n - (k + 1)] 0)
      (d.iterate_nonnegative _)
    have he : n - k = (n - (k + 1)) + 1 := by omega
    rw [he, Function.iterate_succ_apply'] at hp
    simp only [stage, stageRoot, Finset.sum_range_succ] at *
    linarith

theorem Data.sum_gaps_le (d : Data ι) (i : ι) (n : ℕ) :
    ∑ j ∈ Finset.range n, d.gap i (stageRoot j) ≤
      eval d.C ((eval d.E)^[n] 0) i := by
  have hp := d.partial_conversion i n n le_rfl
  have h0 := eval_nonnegative d.hC (d.word_nonnegative (stage n) 0 le_rfl) i
  simp only [Nat.sub_self, Function.iterate_zero, id_eq] at hp
  exact (le_add_of_nonneg_left h0).trans hp

theorem Data.repeated_e_growth (d : Data ι) (i : ι) (n : ℕ) :
    ((n / 5 : ℕ) : ℝ) * (d.gap i .e + d.gap i .f + d.gap i .g) ≤
      eval d.C ((eval d.E)^[n] 0) i := by
  have hg := ForwardFiveCover.prefix_sum_lower_bound
    (fun k => (stageRoot k).toFin) stage_five_cover_fin
    (fun h => d.gap i (Root.ofFin h)) (fun h => d.gap_nonnegative i _) n
  simp only [Root.ofFin_toFin] at hg
  exact hg.trans (d.sum_gaps_le i n)

theorem Data.gaps_zero_of_bounded (d : Data ι) (i : ι)
    (hb : ∃ K : ℝ, ∀ n : ℕ, eval d.C ((eval d.E)^[n] 0) i ≤ K) :
    d.gap i .e = 0 ∧ d.gap i .f = 0 ∧ d.gap i .g = 0 := by
  have he := d.gap_nonnegative i .e
  have hf := d.gap_nonnegative i .f
  have hg := d.gap_nonnegative i .g
  have hz : d.gap i .e + d.gap i .f + d.gap i .g = 0 := by
    by_contra hh
    have hp : 0 < d.gap i .e + d.gap i .f + d.gap i .g :=
      lt_of_le_of_ne (by linarith) (Ne.symm hh)
    obtain ⟨K, hK⟩ := hb
    obtain ⟨n, hn⟩ := exists_nat_gt (K / (d.gap i .e + d.gap i .f + d.gap i .g))
    have hn' := (div_lt_iff₀ hp).mp hn
    have hi := d.repeated_e_growth i (n * 5)
    norm_num at hi
    linarith [hK (n * 5)]
  exact ⟨by linarith, by linarith, by linarith⟩

theorem Data.gaps_zero_of_contracting_row (d : Data ι) (i : ι)
    (w : Vec ι) (hw : 0 ≤ w) (hdom : d.C.matrix i ≤ w)
    (l : ℝ) (hl : 0 ≤ l) (hl1 : l < 1)
    (hc : w ᵥ* d.A.matrix ≤ l • w) :
    d.gap i .e = 0 ∧ d.gap i .f = 0 ∧ d.gap i .g = 0 := by
  apply d.gaps_zero_of_bounded i
  refine ⟨(w ⬝ᵥ d.A.offset) / (1 - l) + d.C.offset i, ?_⟩
  intro n
  change d.C.matrix i ⬝ᵥ ((eval d.E)^[n] 0) + d.C.offset i ≤ _
  have hi := ForwardRealContraction.observed_ternary_iterates_bounded
    d.A d.E d.hA d.hE d.ae (d.C.matrix i) w (d.hC.1 i) hw hdom l hl hl1 hc n
  linarith

theorem Data.gaps_zero_of_positive_subeigenrow (d : Data ι) (i : ι)
    (w : Vec ι) (hw : ∀ j, 0 < w j)
    (l : ℝ) (hl : 0 ≤ l) (hl1 : l < 1)
    (hc : w ᵥ* d.A.matrix ≤ l • w) :
    d.gap i .e = 0 ∧ d.gap i .f = 0 ∧ d.gap i .g = 0 := by
  letI : Nonempty ι := ⟨i⟩
  obtain ⟨K, _, hK⟩ :=
    ForwardRealContraction.observed_ternary_bounded_of_positive_subeigenrow
      d.A d.E d.hA d.hE d.ae (d.C.matrix i) w (d.hC.1 i) hw l hl hl1 hc
  apply d.gaps_zero_of_bounded i
  refine ⟨K + d.C.offset i, fun n => ?_⟩
  change d.C.matrix i ⬝ᵥ ((eval d.E)^[n] 0) + d.C.offset i ≤ _
  linarith [hK n]

theorem Data.eligible_offsets_eq_of_positive_subeigenrow (d : Data ι) (i : ι)
    (w : Vec ι) (hw : ∀ j, 0 < w j)
    (l : ℝ) (hl : 0 ≤ l) (hl1 : l < 1)
    (hc : w ᵥ* d.A.matrix ≤ l • w) :
    (d.C.comp d.E).offset i = (d.C.comp d.B).offset i ∧
    (d.C.comp d.F).offset i = (d.C.comp (d.A.comp d.A)).offset i ∧
    (d.C.comp d.G).offset i = (d.C.comp (d.A.comp d.B)).offset i := by
  obtain ⟨he, hf, hg⟩ := d.gaps_zero_of_positive_subeigenrow i w hw l hl hl1 hc
  exact ⟨sub_eq_zero.mp he, sub_eq_zero.mp hf, sub_eq_zero.mp hg⟩

end CollatzResearch.ForwardRealWordGrowth
