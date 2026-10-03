/-
Compatibility modification notice, 3 October 2026.
The sole import Mathlib.Analysis.Real.Sqrt was renamed to
Mathlib.Analysis.SpecialFunctions.Sqrt for Lean 4.30.0-rc2 and the pinned
Mathlib revision. No theorem statement or proof text changed. This notice
was added when packaging the compatibility sources.
Original work: Copyright 2026 Omar Javier Said Duran; Apache License 2.0.
See licenses/LICENSE-GAO-APACHE-2.0 and SOURCE-LICENSES.txt in this bundle.
-/

import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.FieldSimp
import cadena_completa

/-!
Promedios finitos bajo bits justos, con la cadena completa absorbente.
No se sustituye un tiempo determinista por una parada aleatoria.
-/

noncomputable section

namespace MomentosGao

def promedio {S : Type} (paso : S → Bool → S) (f : S → ℝ) : ℕ → S → ℝ
  | 0, z => f z
  | n+1, z => (promedio paso f n (paso z false) +
      promedio paso f n (paso z true)) / 2

/- Lista con multiplicidades: dos palabras que llegan al mismo estado
siguen contando dos veces. -/
def hojas {S : Type} (paso : S → Bool → S) : ℕ → S → List S
  | 0, z => [z]
  | n+1, z => hojas paso n (paso z false) ++ hojas paso n (paso z true)

theorem numero_hojas {S : Type} (paso : S → Bool → S) (n : ℕ) (z : S) :
    (hojas paso n z).length = 2^n := by
  induction n generalizing z with
  | zero => simp [hojas]
  | succ n ih => simp [hojas, ih, pow_succ]; omega

theorem promedio_hojas {S : Type} (paso : S → Bool → S) (f : S → ℝ)
    (n : ℕ) (z : S) :
    promedio paso f n z = ((hojas paso n z).map f).sum / (2:ℝ)^n := by
  induction n generalizing z with
  | zero => simp [promedio, hojas]
  | succ n ih =>
    simp only [promedio, hojas, List.map_append, List.sum_append, ih, pow_succ]
    ring

theorem promedio_mono {S : Type} (paso : S → Bool → S)
    (f g : S → ℝ) (h : ∀ z, f z ≤ g z) (n : ℕ) (z : S) :
    promedio paso f n z ≤ promedio paso g n z := by
  induction n generalizing z with
  | zero => exact h z
  | succ n ih =>
    simp only [promedio]
    have h0 := ih (paso z false)
    have h1 := ih (paso z true)
    linarith

theorem promedio_constante {S : Type} (paso : S → Bool → S)
    (c : ℝ) (n : ℕ) (z : S) : promedio paso (fun _ => c) n z = c := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih => simp [promedio, ih]

theorem promedio_escalar {S : Type} (paso : S → Bool → S)
    (f : S → ℝ) (c : ℝ) (n : ℕ) (z : S) :
    promedio paso (fun x => c * f x) n z = c * promedio paso f n z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih => simp only [promedio, ih]; ring

theorem raiz_rama (x y r : ℝ) (hx : 0 ≤ x) (hr : 0 ≤ r)
    (ha : 0 ≤ r^2 - y) :
    Real.sqrt (y*x+1/2) ≤ r*Real.sqrt x+1 := by
  have hs := Real.sqrt_nonneg x
  have hsq := Real.sq_sqrt hx
  have hm := mul_nonneg ha hx
  have hp := mul_nonneg hr hs
  have hprod : (r*Real.sqrt x)^2 = r^2*x := by rw [mul_pow, hsq]
  apply (Real.sqrt_le_left (by nlinarith : 0 ≤ r*Real.sqrt x+1)).2
  nlinarith [sq_nonneg (r*Real.sqrt x)]

theorem deriva_raiz {S : Type} (paso : S → Bool → S) (u : S → ℝ)
    (hu : ∀ z, 0 ≤ u z)
    (h0 : ∀ z, u (paso z false) ≤ (1/2)*u z+1/2)
    (h1 : ∀ z, u (paso z true) ≤ (3/2)*u z+1/2) (z : S) :
    (Real.sqrt (u (paso z false)) + Real.sqrt (u (paso z true)))/2 ≤
      (31/32)*Real.sqrt (u z)+1 := by
  have a := (Real.sqrt_le_sqrt (h0 z)).trans
    (raiz_rama (u z) (1/2) (91/128) (hu z) (by norm_num) (by norm_num))
  have b := (Real.sqrt_le_sqrt (h1 z)).trans
    (raiz_rama (u z) (3/2) (157/128) (hu z) (by norm_num) (by norm_num))
  linarith

theorem momento_arbol {S : Type} (paso : S → Bool → S) (v : S → ℝ)
    (hd : ∀ z, (v (paso z false)+v (paso z true))/2 ≤ (31/32)*v z+1)
    (n : ℕ) (z : S) :
    promedio paso v n z ≤ (31/32:ℝ)^n*v z+32*(1-(31/32:ℝ)^n) := by
  induction n generalizing z with
  | zero => simp [promedio]
  | succ n ih =>
    have h0 := ih (paso z false)
    have h1 := ih (paso z true)
    have hp : 0 ≤ (31/32:ℝ)^n := pow_nonneg (by norm_num) n
    have hm := mul_le_mul_of_nonneg_left (hd z) hp
    simp only [promedio, pow_succ]
    nlinarith

open CadenaCompletaGao

def tamano (z : Estado) : ℝ := (mag (datos z).2 : ℝ) / ((datos z).1 : ℝ)

theorem denominador_positivo (z : Estado) : (0 : ℝ) < ((datos z).1 : ℝ) := by
  cases z with
  | fusion => norm_num [datos]
  | vivo k c =>
    have h := coef_positivo k
    change (0 : ℝ) < (coef k : ℝ)
    exact_mod_cast (show (0 : ℤ) < coef k by omega)

theorem tamano_no_negativo (z : Estado) : 0 ≤ tamano z := by
  apply div_nonneg
  · exact_mod_cast mag_no_negativa (datos z).2
  · exact le_of_lt (denominador_positivo z)

theorem dominacion_real (z : Estado) (b : Bool) :
    tamano (paso z b) ≤ ((1+2*(bitInt b : ℝ))/2)*tamano z+1/2 := by
  have hp := denominador_positivo z
  have hq := denominador_positivo (paso z b)
  have hd := dominacion_cadena z b
  unfold Dominado at hd
  have hr : (2 : ℝ)*(mag (datos (paso z b)).2 : ℝ)*((datos z).1 : ℝ) ≤
      (1+2*(bitInt b : ℝ))*(mag (datos z).2 : ℝ)*((datos (paso z b)).1 : ℝ)+
      ((datos z).1 : ℝ)*((datos (paso z b)).1 : ℝ) := by exact_mod_cast hd
  unfold tamano
  apply (div_le_iff₀ hq).2
  apply (mul_le_mul_iff_left₀ (show 0 < 2*((datos z).1 : ℝ) by linarith)).mp
  convert hr using 1 <;> first | rfl | field_simp [ne_of_gt hp]

theorem momento_cadena (n : ℕ) (z : Estado) :
    promedio paso (fun x => Real.sqrt (tamano x)) n z ≤
      (31/32:ℝ)^n*Real.sqrt (tamano z)+32*(1-(31/32:ℝ)^n) := by
  apply momento_arbol
  apply deriva_raiz paso tamano tamano_no_negativo
  · intro x
    have h := dominacion_real x false
    norm_num [bitInt] at h ⊢
    exact h
  · intro x
    have h := dominacion_real x true
    norm_num [bitInt] at h ⊢
    exact h

theorem momento_raiz (n : ℕ) :
    promedio paso (fun x => Real.sqrt (tamano x)) n (.vivo 0 1) ≤ 32 := by
  have h := momento_cadena n (.vivo 0 1)
  have hp : 0 ≤ (31/32:ℝ)^n := pow_nonneg (by norm_num) n
  have hr : tamano (.vivo 0 1) = 1 := by norm_num [tamano, datos, coef, mag]
  rw [hr, Real.sqrt_one, mul_one] at h
  linarith

noncomputable def indicador (U : ℝ) (z : Estado) : ℝ :=
  if U < tamano z then 1 else 0

theorem markov_puntual (U : ℝ) (z : Estado) :
    Real.sqrt U * indicador U z ≤ Real.sqrt (tamano z) := by
  unfold indicador
  split
  · rename_i h
    simpa using Real.sqrt_le_sqrt (le_of_lt h)
  · simp [Real.sqrt_nonneg]

theorem cola_nivel (n : ℕ) (U : ℝ) :
    Real.sqrt U * promedio paso (indicador U) n (.vivo 0 1) ≤ 32 := by
  rw [← promedio_escalar]
  exact (promedio_mono paso _ _ (markov_puntual U) n (.vivo 0 1)).trans
    (momento_raiz n)

def acumulado {S : Type} (paso : S → Bool → S) (f : S → ℝ)
    (n : ℕ) (z : S) : ℝ := ∑ t ∈ Finset.range (n+1), promedio paso f t z

theorem acumulado_sucesor {S : Type} (paso : S → Bool → S) (f : S → ℝ)
    (n : ℕ) (z : S) :
    acumulado paso f (n+1) z = f z+
      (acumulado paso f n (paso z false)+acumulado paso f n (paso z true))/2 := by
  unfold acumulado
  rw [Finset.sum_range_succ']
  simp only [promedio]
  simp only [div_eq_mul_inv]
  rw [← Finset.sum_mul, Finset.sum_add_distrib]
  ring

theorem indicador_no_negativo (U : ℝ) (z : Estado) : 0 ≤ indicador U z := by
  unfold indicador
  split <;> norm_num

theorem promedio_no_negativo {S : Type} (paso : S → Bool → S) (f : S → ℝ)
    (hf : ∀ z, 0 ≤ f z) (n : ℕ) (z : S) : 0 ≤ promedio paso f n z := by
  have h := promedio_mono paso (fun _ => 0) f hf n z
  simpa [promedio_constante] using h

theorem acumulado_no_negativo (U : ℝ) (n : ℕ) (z : Estado) :
    0 ≤ acumulado paso (indicador U) n z := by
  apply Finset.sum_nonneg
  intro t _
  exact promedio_no_negativo paso _ (indicador_no_negativo U) t z

/- Probabilidad de superar U en alguno de los instantes 0,...,n.
La rama que ya superó U cuenta como éxito independientemente de su futuro. -/
noncomputable def alcanza (U : ℝ) : ℕ → Estado → ℝ
  | 0, z => indicador U z
  | n+1, z => if U < tamano z then 1 else
      (alcanza U n (paso z false)+alcanza U n (paso z true))/2

def paso_marcado (U : ℝ) (w : Estado × Bool) (b : Bool) : Estado × Bool :=
  (paso w.1 b, w.2 || decide (U < tamano (paso w.1 b)))

def peso_marcado (w : Estado × Bool) : ℝ := if w.2 then 1 else 0

theorem marcado_persiste (U : ℝ) (n : ℕ) (z : Estado) :
    promedio (paso_marcado U) peso_marcado n (z,true) = 1 := by
  induction n generalizing z with
  | zero => simp [promedio, peso_marcado]
  | succ n ih => simp [promedio, paso_marcado, ih]

theorem alcanza_promedio (U : ℝ) (n : ℕ) (z : Estado) :
    alcanza U n z = promedio (paso_marcado U) peso_marcado n
      (z, decide (U < tamano z)) := by
  induction n generalizing z with
  | zero => simp [alcanza, promedio, peso_marcado, indicador]
  | succ n ih =>
    by_cases hz : U < tamano z
    · simp [alcanza, hz, marcado_persiste]
    · simp [alcanza, hz, promedio, paso_marcado, ← ih]

theorem suma_marcados (l : List (Estado × Bool)) :
    (l.map peso_marcado).sum = ((l.filter (fun w => w.2)).length : ℝ) := by
  induction l with
  | nil => simp
  | cons w l ih =>
    cases hb : w.2 <;> simp [peso_marcado, hb, ih, Nat.cast_add, add_comm]

theorem alcanza_conteo (U : ℝ) (n : ℕ) (z : Estado) :
    alcanza U n z =
      (((hojas (paso_marcado U) n (z, decide (U < tamano z))).filter
        (fun w => w.2)).length : ℝ) / (2:ℝ)^n := by
  rw [alcanza_promedio, promedio_hojas, suma_marcados]

theorem union_finita (U : ℝ) (n : ℕ) (z : Estado) :
    alcanza U n z ≤ acumulado paso (indicador U) n z := by
  induction n generalizing z with
  | zero => simp [alcanza, acumulado, promedio]
  | succ n ih =>
    rw [acumulado_sucesor]
    have h0 := ih (paso z false)
    have h1 := ih (paso z true)
    have hnn0 := acumulado_no_negativo U n (paso z false)
    have hnn1 := acumulado_no_negativo U n (paso z true)
    by_cases hz : U < tamano z
    · simp only [alcanza, indicador, hz, if_true]
      linarith
    · simp only [alcanza, indicador, hz, if_false]
      linarith

theorem cola_maximo (n : ℕ) (U : ℝ) :
    Real.sqrt U * alcanza U n (.vivo 0 1) ≤ 32*((n:ℝ)+1) := by
  have hu := mul_le_mul_of_nonneg_left (union_finita U n (.vivo 0 1))
    (Real.sqrt_nonneg U)
  have hs : Real.sqrt U * acumulado paso (indicador U) n (.vivo 0 1) ≤
      32*((n:ℝ)+1) := by
    unfold acumulado
    rw [Finset.mul_sum]
    calc
      _ ≤ ∑ t ∈ Finset.range (n+1), (32:ℝ) := by
        apply Finset.sum_le_sum
        intro t _
        exact cola_nivel t U
      _ = _ := by simp; ring
  exact hu.trans hs

theorem envolvente_cf (h : ℕ) (hh : 1 ≤ h) :
    alcanza ((h:ℝ)^4) h (.vivo 0 1) ≤ 66/(h:ℝ) := by
  have hp : (0:ℝ) < h := by exact_mod_cast (show 0 < h by omega)
  have hhreal : (1:ℝ) ≤ h := by exact_mod_cast hh
  have hs : Real.sqrt ((h:ℝ)^4) = (h:ℝ)^2 := by
    rw [show (h:ℝ)^4 = ((h:ℝ)^2)^2 by ring, Real.sqrt_sq (sq_nonneg _)]
  have hc := cola_maximo h ((h:ℝ)^4)
  rw [hs] at hc
  apply (le_div_iff₀ hp).2
  apply (mul_le_mul_iff_left₀ hp).mp
  nlinarith

#print axioms dominacion_real
#print axioms numero_hojas
#print axioms promedio_hojas
#print axioms deriva_raiz
#print axioms momento_arbol
#print axioms momento_cadena
#print axioms momento_raiz
#print axioms cola_nivel
#print axioms union_finita
#print axioms alcanza_promedio
#print axioms alcanza_conteo
#print axioms cola_maximo
#print axioms envolvente_cf

end MomentosGao
