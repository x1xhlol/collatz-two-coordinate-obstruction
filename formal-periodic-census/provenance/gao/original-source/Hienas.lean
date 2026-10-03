import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import Mathlib.Data.Nat.Log

/-! # Hienas: del encuentro de Lagarias a la coalescencia literal de Gao

Este archivo sólo importa Mathlib: las definiciones se leen sin nada del proyecto.
La unión con el teorema del proyecto está en `GaoLiteral.lean`.

* Gao (1993), pág. 264: n y n+1 *coalescen* si `C^(k)(n) = C^(k)(n+1)`, con el mismo
  número de divisiones por 2 en las k primeras iteraciones, y el 1 no aparece en ninguna
  de las dos trayectorias en las k primeras iteraciones. Se toma la lectura más exigente
  del 1: no aparece en `C^0, ..., C^k`. Cualquier lectura más suave queda cubierta.
* Gao, pág. 265: `d̄_k = 2^-k · #{n < 2^k − 1 : n y n+1 coalescen tras ≤ k iteraciones}`
  y "the conjecture asserts that d̄_k → 1 as k → ∞".
* Gao, pág. 264: `d(x) = x^-1 · #{n < x : n y n+1 coalescen}`; Gao no sabía si tiene límite.
* Lagarias (bibliografía anotada, entrada 68): el conjunto
  `{n : C^(k)(n) = C^(k)(n+1) para algún k ≤ log2 n}` tiene densidad natural uno.

El puente (`puente`): si n y n+1 se encuentran en j ≤ log2 n pasos, entonces `2^j ≤ n`,
y eso basta para que coalescan en el sentido de Gao en ese mismo paso j:
* ninguna trayectoria pasa por 1, porque en i pasos no se baja de `n/2^i`;
* las divisiones por 2 coinciden, porque con t triplicaciones y m mitades
  `3^t·x ≤ 2^m·C^i(x)` y `3·2^m·C^i(x) ≤ 3^t·(3x + 2^i)`: un desequilibrio de una
  división obligaría a `18n ≤ 3n + 3 + 2^j`, imposible con `2^j ≤ n`. -/

open Filter Topology

namespace Hienas

/-- Mapa clásico: n/2 si n es par, 3n+1 si es impar. -/
def C (n : ℕ) : ℕ := if n % 2 = 0 then n / 2 else 3 * n + 1

/-- Divisiones por 2 en los k primeros pasos desde n. -/
def mitades : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, n => (if n % 2 = 0 then 1 else 0) + mitades k (C n)

/-- Pasos 3n+1 en los k primeros pasos desde n. -/
def triples : ℕ → ℕ → ℕ
  | 0, _ => 0
  | k + 1, n => (if n % 2 = 0 then 0 else 1) + triples k (C n)

/-- Coalescencia de Gao en el paso k. -/
def coalescen (n k : ℕ) : Prop :=
  C^[k] n = C^[k] (n + 1) ∧ mitades k n = mitades k (n + 1) ∧
    ∀ i, i ≤ k → C^[i] n ≠ 1 ∧ C^[i] (n + 1) ≠ 1

/-- Decidibilidad computable, para recalcular la tabla 3 de Gao en `GaoLiteral.lean`. -/
instance (n k : ℕ) : Decidable (coalescen n k) := by unfold coalescen; infer_instance

/-- Encuentro de Lagarias: m y m+1 coinciden en a lo sumo log2 m pasos. -/
def encuentro (m : ℕ) : Prop := ∃ k, k ≤ Nat.log 2 m ∧ C^[k] m = C^[k] (m + 1)

open Classical in
/-- La forma de Lagarias: densidad natural uno de los encuentros. -/
def FormaLagarias : Prop :=
  Tendsto (fun N : ℕ => (((Finset.range N).filter encuentro).card : ℝ) / N) atTop (𝓝 1)

open Classical in
/-- `d̄_k` de Gao. -/
noncomputable def dbarra (k : ℕ) : ℝ :=
  (((Finset.range (2 ^ k - 1)).filter (fun n => ∃ j, j ≤ k ∧ coalescen n j)).card : ℝ) / 2 ^ k

/-- La conjetura tal como la escribe Gao: `d̄_k → 1`. -/
def FormaGao : Prop := Tendsto dbarra atTop (𝓝 1)

open Classical in
/-- `d(x)` de Gao, sin tope de pasos. -/
noncomputable def d (x : ℕ) : ℝ :=
  (((Finset.range x).filter (fun n => ∃ j, coalescen n j)).card : ℝ) / x

/-- `d(x) → 1`: el límite que Gao no sabía si existía. -/
def FormaGaoD : Prop := Tendsto d atTop (𝓝 1)

/-! ## Cotas elementales de una trayectoria -/

theorem C_par {n : ℕ} (h : n % 2 = 0) : C n = n / 2 := by simp [C, h]

theorem C_impar {n : ℕ} (h : n % 2 = 1) : C n = 3 * n + 1 := by
  simp [C, show n % 2 ≠ 0 by omega]

/-- Un paso a lo sumo divide por 2. -/
theorem dos_C (n : ℕ) : n ≤ 2 * C n := by
  unfold C; split <;> omega

/-- En i pasos no se baja de n/2^i. -/
theorem cota_inferior : ∀ (i x : ℕ), x ≤ 2 ^ i * C^[i] x := by
  intro i
  induction i with
  | zero => intro x; simp
  | succ i ih =>
    intro x
    rw [Function.iterate_succ_apply, pow_succ]
    calc x ≤ 2 * C x := dos_C x
      _ ≤ 2 * (2 ^ i * C^[i] (C x)) := Nat.mul_le_mul_left 2 (ih (C x))
      _ = 2 ^ i * 2 * C^[i] (C x) := by ring

theorem suma_cuentas : ∀ (k n : ℕ), mitades k n + triples k n = k := by
  intro k
  induction k with
  | zero => intro n; simp [mitades, triples]
  | succ k ih =>
    intro n
    have := ih (C n)
    simp only [mitades, triples]
    split <;> omega

/-- Con t pasos 3n+1 y m mitades en i pasos:
    `3^t·x ≤ 2^m·C^i(x)` y `3·2^m·C^i(x) ≤ 3^t·(3x + 2^i)`. -/
theorem invariante : ∀ (i x : ℕ),
    3 ^ triples i x * x ≤ 2 ^ mitades i x * C^[i] x ∧
    3 * (2 ^ mitades i x * C^[i] x) ≤ 3 ^ triples i x * (3 * x + 2 ^ i) := by
  intro i
  induction i with
  | zero => intro x; simp [mitades, triples]
  | succ i ih =>
    intro x
    obtain ⟨A, B⟩ := ih (C x)
    rw [Function.iterate_succ_apply]
    have hmit : mitades (i + 1) x = (if x % 2 = 0 then 1 else 0) + mitades i (C x) := rfl
    have htri : triples (i + 1) x = (if x % 2 = 0 then 0 else 1) + triples i (C x) := rfl
    rw [hmit, htri]
    have e2 : (2:ℕ) ^ (i + 1) = 2 * 2 ^ i := by rw [pow_succ]; ring
    rw [e2]
    rcases Nat.mod_two_eq_zero_or_one x with h | h
    · have hC : C x = x / 2 := C_par h
      rw [hC] at A B ⊢
      rw [if_pos h, if_pos h]
      generalize mitades i (x / 2) = m at A B ⊢
      generalize triples i (x / 2) = t at A B ⊢
      generalize C^[i] (x / 2) = Z at A B ⊢
      obtain ⟨y, rfl⟩ : ∃ y, x = 2 * y := ⟨x / 2, by omega⟩
      have hy : 2 * y / 2 = y := by omega
      rw [hy] at A B
      have e1 : (2:ℕ) ^ (1 + m) = 2 * 2 ^ m := by rw [pow_add, pow_one]
      rw [zero_add, e1]
      constructor
      · nlinarith [A]
      · nlinarith [B]
    · have hC : C x = 3 * x + 1 := C_impar h
      rw [hC] at A B ⊢
      rw [if_neg (by omega), if_neg (by omega)]
      generalize mitades i (3 * x + 1) = m at A B ⊢
      generalize triples i (3 * x + 1) = t at A B ⊢
      generalize C^[i] (3 * x + 1) = Z at A B ⊢
      have e1 : (3:ℕ) ^ (1 + t) = 3 * 3 ^ t := by rw [pow_add, pow_one]
      rw [zero_add, e1]
      have hP : 3 ^ t ≤ 3 ^ t * 2 ^ i := Nat.le_mul_of_pos_right _ (by positivity)
      constructor
      · nlinarith [A, Nat.zero_le (3 ^ t)]
      · nlinarith [B, hP, Nat.zero_le (3 ^ t)]

/-! ## El puente: un encuentro en ≤ log2 n pasos ya es una coalescencia de Gao -/

/-- La cuenta que impide dos números distintos de divisiones por 2. -/
theorem choque (P Q R S Y m c : ℕ) (hP : 1 ≤ P) (hR : 2 ≤ R) (hS : 3 ≤ S)
    (L : P * S * m ≤ Q * Y) (U : 3 * (Q * R * Y) ≤ P * c) (hc : c < 18 * m) : False := by
  have hRS : 6 ≤ R * S := by nlinarith
  have e1 : 18 * (P * m) ≤ 3 * (R * S) * (P * m) := Nat.mul_le_mul_right _ (by omega)
  have e2 : 3 * (R * S) * (P * m) = 3 * R * (P * S * m) := by ring
  have e3 : 3 * R * (P * S * m) ≤ 3 * R * (Q * Y) := Nat.mul_le_mul_left _ L
  have e4 : 3 * R * (Q * Y) = 3 * (Q * R * Y) := by ring
  have e5 : P * c < P * (18 * m) := Nat.mul_lt_mul_of_pos_left hc (by omega)
  have e6 : P * (18 * m) = 18 * (P * m) := by ring
  omega

/-- Mismo número de divisiones por 2. -/
theorem equilibrio (n j : ℕ) (hn : 2 ^ j ≤ n) (he : C^[j] n = C^[j] (n + 1)) :
    mitades j n = mitades j (n + 1) := by
  obtain ⟨L1, U1⟩ := invariante j n
  obtain ⟨L2, U2⟩ := invariante j (n + 1)
  have s1 := suma_cuentas j n
  have s2 := suma_cuentas j (n + 1)
  rw [← he] at L2 U2
  have hn1 : 1 ≤ n := le_trans Nat.one_le_two_pow hn
  generalize C^[j] n = Y at L1 U1 L2 U2
  generalize mitades j n = h at L1 U1 s1 ⊢
  generalize mitades j (n + 1) = g at L2 U2 s2 ⊢
  generalize triples j n = a at L1 U1 s1
  generalize triples j (n + 1) = b at L2 U2 s2
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · -- h < g: la trayectoria de n+1 dividió más veces
    obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_lt hlt
    obtain rfl : a = b + (e + 1) := by omega
    rw [pow_add] at L1
    rw [show h + e + 1 = h + (e + 1) by omega, pow_add] at U2
    have hR : 2 ≤ 2 ^ (e + 1) := by
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show 1 ≤ e + 1 by omega)
      simpa using this
    have hS : 3 ≤ 3 ^ (e + 1) := by
      have := Nat.pow_le_pow_right (show 0 < 3 by norm_num) (show 1 ≤ e + 1 by omega)
      simpa using this
    have hP : 1 ≤ 3 ^ b := Nat.one_le_pow _ _ (by norm_num)
    exact choque (3 ^ b) (2 ^ h) (2 ^ (e + 1)) (3 ^ (e + 1)) Y n (3 * (n + 1) + 2 ^ j)
      hP hR hS L1 U2 (by omega)
  · -- g < h: la trayectoria de n dividió más veces
    obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_lt hgt
    obtain rfl : b = a + (e + 1) := by omega
    rw [pow_add] at L2
    rw [show g + e + 1 = g + (e + 1) by omega, pow_add] at U1
    have hR : 2 ≤ 2 ^ (e + 1) := by
      have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) (show 1 ≤ e + 1 by omega)
      simpa using this
    have hS : 3 ≤ 3 ^ (e + 1) := by
      have := Nat.pow_le_pow_right (show 0 < 3 by norm_num) (show 1 ≤ e + 1 by omega)
      simpa using this
    have hP : 1 ≤ 3 ^ a := Nat.one_le_pow _ _ (by norm_num)
    exact choque (3 ^ a) (2 ^ g) (2 ^ (e + 1)) (3 ^ (e + 1)) Y (n + 1) (3 * n + 2 ^ j)
      hP hR hS L2 U1 (by omega)

/-- El 1 no aparece en `C^0, ..., C^j` de ninguna de las dos trayectorias. -/
theorem sin_uno (n j : ℕ) (hn : 2 ^ j ≤ n) (he : C^[j] n = C^[j] (n + 1)) :
    ∀ i, i ≤ j → C^[i] n ≠ 1 ∧ C^[i] (n + 1) ≠ 1 := by
  intro i hi
  have hpow : 2 ^ i ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hi
  constructor
  · intro h1
    have hb := cota_inferior i n
    rw [h1, mul_one] at hb
    rcases Nat.lt_or_ge i j with hij | hij
    · have : 2 ^ i < 2 ^ j := Nat.pow_lt_pow_right (by norm_num) hij
      omega
    · have hij' : i = j := le_antisymm hi hij
      subst hij'
      have hb2 := cota_inferior i (n + 1)
      rw [← he, h1, mul_one] at hb2
      omega
  · intro h1
    have hb := cota_inferior i (n + 1)
    rw [h1, mul_one] at hb
    omega

/-- El puente. -/
theorem puente (n : ℕ) (h : encuentro n) : ∃ j, j ≤ Nat.log 2 n ∧ coalescen n j := by
  obtain ⟨j, hj, he⟩ := h
  have hn0 : n ≠ 0 := by
    rintro rfl
    have : j = 0 := by simpa using hj
    subst this
    simp at he
  have hpow : 2 ^ j ≤ n :=
    le_trans (Nat.pow_le_pow_right (by norm_num) hj) (Nat.pow_log_le_self 2 hn0)
  exact ⟨j, hj, he, equilibrio n j hpow he, sin_uno n j hpow he⟩

/-! ## De la densidad de Lagarias a las densidades de Gao -/

open Classical in
theorem gao_de_lagarias (hL : FormaLagarias) : FormaGao := by
  unfold FormaLagarias at hL
  unfold FormaGao
  rw [Metric.tendsto_atTop] at hL ⊢
  intro ε hε
  obtain ⟨N0, hN0⟩ := hL (ε / 2) (by linarith)
  obtain ⟨M, hM⟩ := exists_nat_ge (2 / ε)
  refine ⟨N0 + M, fun k hk => ?_⟩
  have hk2 : k < 2 ^ k := Nat.lt_two_pow_self
  have hkN : N0 ≤ 2 ^ k := by omega
  have hkM : (2:ℝ) / ε ≤ (2:ℝ) ^ k := by
    have h1 : M ≤ 2 ^ k := by omega
    calc (2:ℝ) / ε ≤ M := hM
      _ ≤ ((2 ^ k : ℕ) : ℝ) := by exact_mod_cast h1
      _ = (2:ℝ) ^ k := by push_cast; ring
  have hN := hN0 (2 ^ k) hkN
  have hsub : (Finset.range (2 ^ k)).filter encuentro ⊆
      insert (2 ^ k - 1)
        ((Finset.range (2 ^ k - 1)).filter (fun n => ∃ j, j ≤ k ∧ coalescen n j)) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_range] at hn
    rcases Nat.lt_or_ge n (2 ^ k - 1) with hlt | hge
    · apply Finset.mem_insert_of_mem
      simp only [Finset.mem_filter, Finset.mem_range]
      refine ⟨hlt, ?_⟩
      obtain ⟨j, hj, hc⟩ := puente n hn.2
      refine ⟨j, le_trans hj ?_, hc⟩
      calc Nat.log 2 n ≤ Nat.log 2 (2 ^ k) := Nat.log_mono_right hn.1.le
        _ = k := Nat.log_pow (by norm_num) k
    · have : n = 2 ^ k - 1 := by omega
      rw [this]
      exact Finset.mem_insert_self _ _
  have hA := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
  have hB : ((Finset.range (2 ^ k - 1)).filter
      (fun n => ∃ j, j ≤ k ∧ coalescen n j)).card ≤ 2 ^ k - 1 := by
    calc _ ≤ (Finset.range (2 ^ k - 1)).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = 2 ^ k - 1 := Finset.card_range _
  unfold dbarra
  generalize ((Finset.range (2 ^ k)).filter encuentro).card = A at hA hN
  generalize ((Finset.range (2 ^ k - 1)).filter
      (fun n => ∃ j, j ≤ k ∧ coalescen n j)).card = B at hA hB ⊢
  have hpos : (0:ℝ) < (2:ℝ) ^ k := by positivity
  have hB1 : B + 1 ≤ 2 ^ k := by have := @Nat.one_le_two_pow k; omega
  have hBr : (B:ℝ) + 1 ≤ (2:ℝ) ^ k := by exact_mod_cast hB1
  have hAr : (A:ℝ) ≤ B + 1 := by exact_mod_cast hA
  rw [Real.dist_eq, abs_lt] at hN ⊢
  push_cast at hN
  have hBD : (B:ℝ) / (2:ℝ) ^ k < 1 := (div_lt_one hpos).mpr (by linarith)
  have hAB : (A:ℝ) / (2:ℝ) ^ k - 1 / (2:ℝ) ^ k ≤ (B:ℝ) / (2:ℝ) ^ k := by
    rw [div_sub_div_same]
    gcongr
    linarith
  have hinv : 1 / (2:ℝ) ^ k ≤ ε / 2 := by
    rw [div_le_iff₀ hε] at hkM
    rw [div_le_iff₀ hpos]
    linarith
  constructor <;> linarith [hN.1, hN.2]

open Classical in
theorem d_de_lagarias (hL : FormaLagarias) : FormaGaoD := by
  unfold FormaLagarias at hL
  unfold FormaGaoD
  rw [Metric.tendsto_atTop] at hL ⊢
  intro ε hε
  obtain ⟨N0, hN0⟩ := hL ε hε
  refine ⟨max N0 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  have h := hN0 N (le_trans (le_max_left _ _) hN)
  have hsub : (Finset.range N).filter encuentro ⊆
      (Finset.range N).filter (fun n => ∃ j, coalescen n j) := by
    intro n hn
    simp only [Finset.mem_filter] at hn ⊢
    obtain ⟨j, -, hc⟩ := puente n hn.2
    exact ⟨hn.1, j, hc⟩
  have hA := Finset.card_le_card hsub
  have hB : ((Finset.range N).filter (fun n => ∃ j, coalescen n j)).card ≤ N := by
    calc _ ≤ (Finset.range N).card := Finset.card_le_card (Finset.filter_subset _ _)
      _ = N := Finset.card_range N
  unfold d
  generalize ((Finset.range N).filter encuentro).card = A at hA h
  generalize ((Finset.range N).filter (fun n => ∃ j, coalescen n j)).card = B at hA hB ⊢
  have hpos : (0:ℝ) < N := by exact_mod_cast hN1
  have hAr : (A:ℝ) ≤ B := by exact_mod_cast hA
  have hBr : (B:ℝ) ≤ N := by exact_mod_cast hB
  rw [Real.dist_eq, abs_lt] at h ⊢
  have e1 : (A:ℝ) / N ≤ (B:ℝ) / N := by gcongr
  have e2 : (B:ℝ) / N ≤ 1 := (div_le_one hpos).mpr hBr
  constructor <;> linarith [h.1, h.2]

end Hienas

#print axioms Hienas.puente
#print axioms Hienas.gao_de_lagarias
#print axioms Hienas.d_de_lagarias
