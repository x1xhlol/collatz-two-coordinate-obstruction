import Repeticion

/- La bandera marca únicamente un paso k=1 -> k=2 de la cadena original. -/

noncomputable section

namespace GuardiasGao

open CadenaCompletaGao MomentosGao EnsayoGao ParametrosVentanaGao RepeticionGao

abbrev EstadoEnsayo := Estado × Bool

def entrada : Estado → Estado → Bool
  | .vivo 1 _, .vivo 2 _ => true
  | _, _ => false

def paso_ensayo (z : EstadoEnsayo) (b : Bool) : EstadoEnsayo :=
  (paso z.1 b, entrada z.1 (paso z.1 b))

def reinicio (z : EstadoEnsayo) : EstadoEnsayo := (z.1,false)

def guardia (C : ℕ) (z : EstadoEnsayo) : Bool := z.2 && match z.1 with
  | .vivo 2 c => decide (c.natAbs≤C)
  | _ => false

def vivo (z : EstadoEnsayo) : Bool := decide (z.1≠.fusion)
def duracion (C : ℕ) : ℕ := horizonte (tiempo (C:ℤ))+duracion_palabra (tiempo (C:ℤ))
def riesgo (C : ℕ) : ℝ :=
  (1/(2:ℝ)^(duracion_palabra (tiempo (C:ℤ))))/(4*((tiempo (C:ℤ):ℝ)+1))

theorem media_base (h : ℕ) (f : Estado → ℝ) (z : EstadoEnsayo) :
    promedio paso_ensayo (fun w => f w.1) h z=promedio paso f h z.1 := by
  induction h generalizing z with
  | zero => rfl
  | succ h ih => simp only [promedio,ih,paso_ensayo]

theorem guardia_estado (C : ℕ) (z : EstadoEnsayo) (hg : guardia C z=true) :
    ∃ c, z.1=.vivo 2 c ∧ c.natAbs≤C := by
  have h := (Bool.and_eq_true_iff.mp hg).2
  cases he : z.1 with
  | fusion => simp [he] at h
  | vivo k c =>
    cases k with
    | zero => simp [he] at h
    | succ k =>
      cases k with
      | zero => simp [he] at h
      | succ k =>
        cases k with
        | zero => exact ⟨c,rfl,by simpa [he] using h⟩
        | succ k => simp [he] at h

theorem complemento (h : ℕ) (z : EstadoEnsayo) :
    promedio paso_ensayo (fun w => indicador (vivo w)) h z+probabilidad_fusion h z.1=1 := by
  have he : ∀ w : EstadoEnsayo, indicador (vivo w)+fusion w.1=1 := by
    intro w
    by_cases hw : w.1=.fusion <;> simp [RepeticionGao.indicador,vivo,fusion,hw]
  have hm := promedio_mono paso_ensayo (fun w => indicador (vivo w)+fusion w.1)
    (fun _ => 1) (fun w => le_of_eq (he w)) h z
  have hm' := promedio_mono paso_ensayo (fun _ => 1)
    (fun w => indicador (vivo w)+fusion w.1) (fun w => le_of_eq (he w).symm) h z
  rw [BandaGao.promedio_suma,media_base,promedio_constante] at hm hm'
  exact le_antisymm hm hm'

theorem riesgo_no_negativo (C : ℕ) : 0≤riesgo C := by unfold riesgo; positivity

theorem riesgo_menor_uno (C : ℕ) : riesgo C≤1 := by
  have he := ensayo_uniforme (C:ℤ) 0 (by simp)
  have hm := promedio_mono paso fusion (fun _ => 1)
    (fun z => by unfold fusion; split <;> norm_num) (duracion C) (.vivo 2 0)
  rw [promedio_constante] at hm
  exact he.trans hm

theorem fallo_bloque (C : ℕ) (z : EstadoEnsayo) (hg : guardia C z=true) :
    promedio paso_ensayo (fun w => indicador (vivo w)) (duracion C) z≤1-riesgo C := by
  obtain ⟨c,he,hc⟩ := guardia_estado C z hg
  have hreal : |(c:ℝ)|≤|((C:ℤ):ℝ)| := by
    have hn : (c.natAbs:ℝ)≤(C:ℝ) := by exact_mod_cast hc
    simpa using hn
  have hp := ensayo_uniforme (C:ℤ) c hreal
  have hm := complemento (duracion C) z
  rw [he] at hm
  change riesgo C≤probabilidad_fusion (duracion C) (.vivo 2 c) at hp
  linarith

def probabilidad_fallos (C j h : ℕ) (z : EstadoEnsayo) : ℝ :=
  fallos paso_ensayo (guardia C) vivo reinicio (duracion C) j h z

theorem fallos_guardados (C j h : ℕ) (z : EstadoEnsayo) :
    probabilidad_fallos C j h z≤(1-riesgo C)^j :=
  fallos_cota paso_ensayo (guardia C) vivo reinicio (duracion C)
    (riesgo C) (riesgo_menor_uno C) (fallo_bloque C) j h z

theorem duracion_positiva (C : ℕ) : 1≤duracion C := by
  have ht := tiempo_minimo (C:ℤ)
  have hh := horizonte_posterior (tiempo (C:ℤ))
  unfold duracion
  omega

theorem fallos_evento (C j h : ℕ) (z : EstadoEnsayo) :
    PalabrasGao.media h (fun bs => RepeticionGao.indicador
      (fallos_palabra paso_ensayo (guardia C) vivo reinicio (duracion C) j bs z))≤
      (1-riesgo C)^j := by
  rw [media_fallos _ _ _ _ _ (duracion_positiva C)]
  exact fallos_guardados C j h z

#print axioms fallos_evento
#print axioms media_base
#print axioms guardia_estado
#print axioms complemento
#print axioms fallo_bloque
#print axioms fallos_guardados

end GuardiasGao
