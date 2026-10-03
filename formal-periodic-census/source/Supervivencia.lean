import Resto

/- Supervivencia de la primera excursión: se detiene la cadena al salir
   del interior. La altura k-1 es armónica y crece a lo sumo uno por paso. -/

noncomputable section

namespace SupervivenciaGao

open CadenaCompletaGao MomentosGao RestoGao

def paso_excursion (z : Estado) (b : Bool) : Estado :=
  if RestoGao.interior z then paso z b else z

def altura (z : Estado) : ℝ := match z with
  | .fusion => 0
  | .vivo k _ => ((k-1:ℕ):ℝ)

def vivo (z : Estado) : ℝ := if RestoGao.interior z then 1 else 0

theorem altura_no_negativa (z : Estado) : 0 ≤ altura z := by
  cases z <;> simp [altura]

theorem vivo_no_negativo (z : Estado) : 0 ≤ vivo z := by
  unfold vivo
  cases RestoGao.interior z <;> norm_num

theorem altura_por_vivo (z : Estado) : altura z*vivo z = altura z := by
  cases z with
  | fusion => simp [altura]
  | vivo k c =>
    cases k with
    | zero => simp [altura]
    | succ k => cases k <;> simp [altura, vivo, RestoGao.interior]

theorem altura_armonica (z : Estado) :
    (altura (paso_excursion z false)+altura (paso_excursion z true))/2 = altura z := by
  cases z with
  | fusion => simp [paso_excursion, RestoGao.interior, altura]
  | vivo k c =>
    cases k with
    | zero => simp [paso_excursion, RestoGao.interior, altura]
    | succ k =>
      cases k with
      | zero => simp [paso_excursion, RestoGao.interior, altura]
      | succ k =>
        by_cases hc : c%2=0
        · simp [paso_excursion, RestoGao.interior, paso, altura, hc]
        · simp [paso_excursion, RestoGao.interior, paso, altura, hc]
          ring

theorem altura_paso (z : Estado) (b : Bool) :
    altura (paso_excursion z b) ≤ altura z+1 := by
  cases z with
  | fusion => simp [paso_excursion, RestoGao.interior, altura]
  | vivo k c =>
    cases k with
    | zero => simp [paso_excursion, RestoGao.interior, altura]
    | succ k =>
      cases k with
      | zero => simp [paso_excursion, RestoGao.interior, altura]
      | succ k =>
        cases b <;> by_cases hc : c%2=0 <;>
          simp [paso_excursion, RestoGao.interior, paso, altura, hc] <;> linarith

theorem altura_media (n : ℕ) (z : Estado) :
    promedio paso_excursion altura n z = altura z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih => simp only [promedio, ih, altura_armonica]

theorem altura_acotada_por_vivos (n : ℕ) (z : Estado) :
    promedio paso_excursion altura n z ≤
      (altura z+(n:ℝ))*promedio paso_excursion vivo n z := by
  induction n generalizing z with
  | zero => simp [promedio, altura_por_vivo]
  | succ n ih =>
    have h0 := ih (paso_excursion z false)
    have h1 := ih (paso_excursion z true)
    have p0 := promedio_no_negativo paso_excursion vivo vivo_no_negativo n (paso_excursion z false)
    have p1 := promedio_no_negativo paso_excursion vivo vivo_no_negativo n (paso_excursion z true)
    have a0 := mul_le_mul_of_nonneg_right (altura_paso z false) p0
    have a1 := mul_le_mul_of_nonneg_right (altura_paso z true) p1
    simp only [promedio, Nat.cast_add, Nat.cast_one]
    nlinarith

def supervivencia (n : ℕ) (c : ℤ) : ℝ :=
  promedio paso_excursion vivo n (.vivo 2 c)

theorem supervivencia_armonica (n : ℕ) (c : ℤ) :
    1/((n:ℝ)+1) ≤ supervivencia n c := by
  have h := altura_acotada_por_vivos n (.vivo 2 c)
  rw [altura_media] at h
  norm_num [altura] at h
  apply (div_le_iff₀ (show (0:ℝ) < n+1 by positivity)).2
  unfold supervivencia
  nlinarith

theorem suma_vivos (l : List Estado) :
    (l.map vivo).sum = ((l.filter RestoGao.interior).length : ℝ) := by
  induction l with
  | nil => simp
  | cons z l ih => cases hb : RestoGao.interior z <;> simp [vivo, hb, ih, Nat.cast_add, add_comm]

theorem supervivencia_conteo (n : ℕ) (c : ℤ) :
    supervivencia n c =
      (((hojas paso_excursion n (.vivo 2 c)).filter RestoGao.interior).length : ℝ)/(2:ℝ)^n := by
  unfold supervivencia
  rw [promedio_hojas, suma_vivos]

#print axioms altura_armonica
#print axioms altura_paso
#print axioms altura_media
#print axioms altura_acotada_por_vivos
#print axioms supervivencia_armonica
#print axioms supervivencia_conteo

end SupervivenciaGao
