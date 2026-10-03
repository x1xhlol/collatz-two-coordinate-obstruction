import Momentos

/- Unión finita sobre cualquier árbol binario de estados, con multiplicidades.
   La hipótesis de momento es sólo a tiempos deterministas desde una raíz fija. -/

noncomputable section

namespace MaximosGao

open MomentosGao

variable {S : Type}

def indicador (u : S → ℝ) (U : ℝ) (s : S) : ℝ := if U < u s then 1 else 0

def cruce (paso : S → Bool → S) (u : S → ℝ) (U : ℝ) : ℕ → S → ℝ
  | 0, s => indicador u U s
  | n+1, s => if U < u s then 1 else
      (cruce paso u U n (paso s false)+cruce paso u U n (paso s true))/2

theorem indicador_no_negativo (u : S → ℝ) (U : ℝ) (s : S) :
    0 ≤ indicador u U s := by unfold indicador; split <;> norm_num

theorem union_finita (paso : S → Bool → S) (u : S → ℝ) (U : ℝ)
    (n : ℕ) (s : S) : cruce paso u U n s ≤ acumulado paso (indicador u U) n s := by
  have hnn : ∀ m z, 0 ≤ acumulado paso (indicador u U) m z := by
    intro m z
    apply Finset.sum_nonneg
    intro t _
    exact promedio_no_negativo paso _ (indicador_no_negativo u U) t z
  induction n generalizing s with
  | zero => simp [cruce, acumulado, promedio]
  | succ n ih =>
    rw [acumulado_sucesor]
    have h0 := ih (paso s false)
    have h1 := ih (paso s true)
    have hn0 := hnn n (paso s false)
    have hn1 := hnn n (paso s true)
    by_cases hz : U < u s
    · simp only [cruce, indicador, hz, if_true]
      linarith
    · simp only [cruce, indicador, hz, if_false]
      linarith

theorem cola_nivel (paso : S → Bool → S) (u : S → ℝ) (U B : ℝ)
    (n : ℕ) (s : S) (hm : promedio paso (fun z => Real.sqrt (u z)) n s ≤ B) :
    Real.sqrt U*promedio paso (indicador u U) n s ≤ B := by
  have hp : ∀ z, Real.sqrt U*indicador u U z ≤ Real.sqrt (u z) := by
    intro z
    unfold indicador
    split
    · rename_i hz
      simpa using Real.sqrt_le_sqrt (le_of_lt hz)
    · simp [Real.sqrt_nonneg]
  rw [← promedio_escalar]
  exact (promedio_mono paso _ _ hp n s).trans hm

theorem cola_maximo (paso : S → Bool → S) (u : S → ℝ) (U B : ℝ)
    (n : ℕ) (s : S)
    (hm : ∀ t, promedio paso (fun z => Real.sqrt (u z)) t s ≤ B) :
    Real.sqrt U*cruce paso u U n s ≤ B*((n:ℝ)+1) := by
  have hu := mul_le_mul_of_nonneg_left (union_finita paso u U n s) (Real.sqrt_nonneg U)
  have hs : Real.sqrt U*acumulado paso (indicador u U) n s ≤ B*((n:ℝ)+1) := by
    unfold acumulado
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ t ∈ Finset.range (n+1), B := by
        apply Finset.sum_le_sum
        intro t _
        exact cola_nivel paso u U B t s (hm t)
      _ = _ := by simp; ring
  exact hu.trans hs

def paso_marcado (paso : S → Bool → S) (u : S → ℝ) (U : ℝ)
    (s : S × Bool) (b : Bool) : S × Bool :=
  (paso s.1 b, s.2 || decide (U < u (paso s.1 b)))

def peso_marcado (s : S × Bool) : ℝ := if s.2 then 1 else 0

theorem marcado_persiste (paso : S → Bool → S) (u : S → ℝ) (U : ℝ)
    (n : ℕ) (s : S) :
    promedio (paso_marcado paso u U) peso_marcado n (s,true) = 1 := by
  induction n generalizing s with
  | zero => simp [promedio, peso_marcado]
  | succ n ih => simp [promedio, paso_marcado, ih]

theorem cruce_promedio (paso : S → Bool → S) (u : S → ℝ) (U : ℝ)
    (n : ℕ) (s : S) : cruce paso u U n s =
      promedio (paso_marcado paso u U) peso_marcado n (s,decide (U < u s)) := by
  induction n generalizing s with
  | zero => simp [cruce, indicador, promedio, peso_marcado]
  | succ n ih =>
    by_cases hs : U < u s
    · simp [cruce, hs, marcado_persiste]
    · simp [cruce, hs, promedio, paso_marcado, ← ih]

theorem suma_marcados (l : List (S × Bool)) :
    (l.map peso_marcado).sum = ((l.filter (fun w => w.2)).length : ℝ) := by
  induction l with
  | nil => simp
  | cons w l ih =>
    cases hb : w.2 <;> simp [peso_marcado, hb, ih, Nat.cast_add, add_comm]

theorem cruce_conteo (paso : S → Bool → S) (u : S → ℝ) (U : ℝ)
    (n : ℕ) (s : S) : cruce paso u U n s =
      (((hojas (paso_marcado paso u U) n (s, decide (U < u s))).filter
        (fun w => w.2)).length : ℝ) / (2:ℝ)^n := by
  rw [cruce_promedio, promedio_hojas, suma_marcados]

theorem cruce_dominado (paso : S → Bool → S) (u v : S → ℝ) (U : ℝ)
    (hi : ∀ s, indicador u U s ≤ v s)
    (hd : ∀ s, (v (paso s false)+v (paso s true))/2 ≤ v s)
    (n : ℕ) (s : S) : cruce paso u U n s ≤ v s := by
  induction n generalizing s with
  | zero => exact hi s
  | succ n ih =>
    by_cases hs : U < u s
    · simpa [cruce, indicador, hs] using hi s
    · have h0 := ih (paso s false)
      have h1 := ih (paso s true)
      have hpaso := hd s
      simp only [cruce, hs, if_false]
      linarith

#print axioms cola_maximo
#print axioms cruce_conteo
#print axioms cruce_dominado

end MaximosGao
