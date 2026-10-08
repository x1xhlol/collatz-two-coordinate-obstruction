import Guardias

/- Inclusión determinista: suficientes entradas admisibles fuerzan j bloques
   completos en una palabra sin absorción. Se incluye el extremo terminal. -/

noncomputable section

namespace ConteoEnsayosGao

open RestoGao PalabrasGao RepeticionGao

variable {S : Type}

def cuenta (paso : S → Bool → S) (guardia : S → Bool) : List Bool → S → ℕ
  | [], z => if guardia z then 1 else 0
  | b::bs, z => (if guardia z then 1 else 0)+cuenta paso guardia bs (paso z b)

def todos_vivos (paso : S → Bool → S) (vivo : S → Bool) : List Bool → S → Prop
  | [], z => vivo z=true
  | b::bs, z => vivo z=true ∧ todos_vivos paso vivo bs (paso z b)

theorem cuenta_longitud (paso : S → Bool → S) (guardia : S → Bool) (bs : List Bool) (z : S) :
    cuenta paso guardia bs z≤bs.length+1 := by
  induction bs generalizing z with
  | nil => simp [cuenta]; split <;> omega
  | cons b bs ih =>
    have h := ih (paso z b)
    simp only [cuenta,List.length_cons]
    split <;> omega

theorem cuenta_prefijo (paso : S → Bool → S) (guardia : S → Bool)
    (pre post : List Bool) (z : S) :
    cuenta paso guardia (pre++post) z≤pre.length+cuenta paso guardia post (recorre paso pre z) := by
  induction pre generalizing z with
  | nil => simp [recorre]
  | cons b pre ih =>
    have h := ih (paso z b)
    simp only [List.cons_append,cuenta,List.length_cons,recorre]
    split <;> omega

theorem cuenta_reinicio (paso : S → Bool → S) (guardia : S → Bool) (reinicio : S → S)
    (hr : ∀ z b, paso (reinicio z) b=paso z b)
    (bs : List Bool) (z : S) :
    cuenta paso guardia bs z≤cuenta paso guardia bs (reinicio z)+1 := by
  cases bs with
  | nil => simp only [cuenta]; split <;> split <;> omega
  | cons b bs => simp only [cuenta,hr]; split <;> split <;> omega

theorem vivos_sufijo (paso : S → Bool → S) (vivo : S → Bool)
    (pre post : List Bool) (z : S) (hv : todos_vivos paso vivo (pre++post) z) :
    todos_vivos paso vivo post (recorre paso pre z) := by
  induction pre generalizing z with
  | nil => exact hv
  | cons b pre ih => exact ih (paso z b) hv.2

theorem vivos_cabeza (paso : S → Bool → S) (vivo : S → Bool) (bs : List Bool) (z : S)
    (hv : todos_vivos paso vivo bs z) : vivo z=true := by
  cases bs with
  | nil => exact hv
  | cons b bs => exact hv.1

theorem vivos_reinicio (paso : S → Bool → S) (vivo : S → Bool) (reinicio : S → S)
    (hr : ∀ z b, paso (reinicio z) b=paso z b) (hvr : ∀ z, vivo (reinicio z)=vivo z)
    (bs : List Bool) (z : S) (hv : todos_vivos paso vivo bs z) :
    todos_vivos paso vivo bs (reinicio z) := by
  cases bs with
  | nil => simpa [todos_vivos,hvr] using hv
  | cons b bs => simpa only [todos_vivos,hvr,hr] using hv

theorem completa_bloques (paso : S → Bool → S) (guardia vivo : S → Bool)
    (reinicio : S → S) (W : ℕ) (hW : 1≤W)
    (hr : ∀ z b, paso (reinicio z) b=paso z b) (hvr : ∀ z, vivo (reinicio z)=vivo z)
    (j : ℕ) (bs : List Bool) (z : S)
    (hc : 1+j*(W+2)≤cuenta paso guardia bs z) (hv : todos_vivos paso vivo bs z) :
    fallos_palabra paso guardia vivo reinicio W j bs z=true := by
  induction j generalizing bs z with
  | zero => rfl
  | succ j ih =>
    induction bs generalizing z with
    | nil =>
      have hlen := cuenta_longitud paso guardia [] z
      simp only [List.length_nil] at hlen
      nlinarith
    | cons b bs ib =>
      by_cases hg : guardia z=true
      · have hlen := cuenta_longitud paso guardia (b::bs) z
        have hmin : W+3≤1+(j+1)*(W+2) := by nlinarith
        have hw : W≤(b::bs).length := by omega
        let pre := (b::bs).take W
        let post := (b::bs).drop W
        let w := recorre paso pre z
        have hbs : pre++post=b::bs := List.take_append_drop W _
        have hpre : pre.length=W := by
          change ((b::bs).take W).length=W
          rw [List.length_take]
          exact Nat.min_eq_left hw
        have hcp := cuenta_prefijo paso guardia pre post z
        rw [hbs,hpre] at hcp
        have hcr := cuenta_reinicio paso guardia reinicio hr post w
        have hrest : 1+j*(W+2)≤cuenta paso guardia post (reinicio w) := by
          change cuenta paso guardia (b::bs) z≤W+cuenta paso guardia post w at hcp
          nlinarith
        have hvpost := vivos_sufijo paso vivo pre post z (by simpa [hbs] using hv)
        have hvw : vivo w=true := vivos_cabeza paso vivo post w hvpost
        have hvrest := vivos_reinicio paso vivo reinicio hr hvr post w hvpost
        have hcont := ih post (reinicio w) hrest hvrest
        simp only [fallos_palabra]
        rw [busca_admite paso guardia vivo reinicio W hW _ (b::bs) z hg hw]
        change (vivo w && fallos_palabra paso guardia vivo reinicio W j post (reinicio w))=true
        simp [hvw,hcont]
      · have hcnt : 1+(j+1)*(W+2)≤cuenta paso guardia bs (paso z b) := by
          simpa [cuenta,hg] using hc
        have hnext := ib (paso z b) hcnt hv.2
        simpa [fallos_palabra,busca_palabra,hg] using hnext

theorem muerto_recorre (paso : S → Bool → S) (vivo : S → Bool)
    (hm : ∀ z b, vivo z=false → vivo (paso z b)=false)
    (bs : List Bool) (z : S) (hz : vivo z=false) : vivo (recorre paso bs z)=false := by
  induction bs generalizing z with
  | nil => exact hz
  | cons b bs ih => exact ih (paso z b) (hm z b hz)

theorem vivos_terminal (paso : S → Bool → S) (vivo : S → Bool)
    (hm : ∀ z b, vivo z=false → vivo (paso z b)=false)
    (bs : List Bool) (z : S) (hv : vivo (recorre paso bs z)=true) :
    todos_vivos paso vivo bs z := by
  have hz : vivo z=true := by
    cases he : vivo z with
    | true => rfl
    | false =>
      have hf := muerto_recorre paso vivo hm bs z he
      rw [hv] at hf
      contradiction
  induction bs generalizing z with
  | nil => exact hz
  | cons b bs ih =>
    have hchild : vivo (paso z b)=true := by
      cases he : vivo (paso z b) with
      | true => rfl
      | false =>
        have hf := muerto_recorre paso vivo hm bs (paso z b) he
        change vivo (recorre paso bs (paso z b))=true at hv
        rw [hv] at hf
        contradiction
    exact ⟨hz,ih (paso z b) hv hchild⟩

open CadenaCompletaGao GuardiasGao EnsayoGao

def muchas (C j : ℕ) (bs : List Bool) (z : EstadoEnsayo) : Bool :=
  vivo (recorre paso_ensayo bs z) &&
    decide (1+j*(duracion C+2)≤cuenta paso_ensayo (guardia C) bs z)

theorem muchas_fallos (C j : ℕ) (bs : List Bool) (z : EstadoEnsayo) (hm : muchas C j bs z=true) :
    fallos_palabra paso_ensayo (guardia C) vivo reinicio (duracion C) j bs z=true := by
  have hv := (Bool.and_eq_true_iff.mp hm).1
  have hc : 1+j*(duracion C+2)≤cuenta paso_ensayo (guardia C) bs z := by
    simpa using (Bool.and_eq_true_iff.mp hm).2
  have hmuerto : ∀ z b, vivo z=false → vivo (paso_ensayo z b)=false := by
    intro z b hz
    have he : z.1=.fusion := by simpa [vivo] using hz
    simp [vivo,paso_ensayo,paso,he]
  exact completa_bloques paso_ensayo (guardia C) vivo reinicio (duracion C)
    (duracion_positiva C) (fun _ _ => rfl) (fun _ => rfl) j bs z hc
    (vivos_terminal paso_ensayo vivo hmuerto bs z hv)

theorem cota_muchas (C j h : ℕ) (z : EstadoEnsayo) :
    media h (fun bs => indicador (muchas C j bs z))≤(1-riesgo C)^j := by
  have hp : ∀ bs, indicador (muchas C j bs z) ≤ indicador
      (fallos_palabra paso_ensayo (guardia C) vivo reinicio (duracion C) j bs z) := by
    intro bs
    by_cases hm : muchas C j bs z=true
    · simp [indicador,hm,muchas_fallos C j bs z hm]
    · simp [indicador,hm]
      split <;> norm_num
  exact (media_mono h _ _ (fun bs _ => hp bs)).trans (fallos_evento C j h z)

def probabilidad_pocas (C j h : ℕ) (z : EstadoEnsayo) : ℝ :=
  media h (fun bs => indicador (vivo (recorre paso_ensayo bs z) && decide
    (cuenta paso_ensayo (guardia C) bs z<1+j*(duracion C+2))))

theorem supervivencia_por_entradas (C j h : ℕ) (z : EstadoEnsayo) :
    1-probabilidad_fusion h z.1≤probabilidad_pocas C j h z+(1-riesgo C)^j := by
  have hp : ∀ bs, indicador (vivo (recorre paso_ensayo bs z))≤
      indicador (vivo (recorre paso_ensayo bs z) && decide
        (cuenta paso_ensayo (guardia C) bs z<1+j*(duracion C+2)))+
      indicador (muchas C j bs z) := by
    intro bs
    by_cases hc : cuenta paso_ensayo (guardia C) bs z<1+j*(duracion C+2)
    · cases hv : vivo (recorre paso_ensayo bs z) <;> simp [indicador,muchas,hv,hc,show ¬1+j*(duracion C+2)≤cuenta paso_ensayo (guardia C) bs z by omega]
    · have hg : 1+j*(duracion C+2)≤cuenta paso_ensayo (guardia C) bs z := by omega
      simp [indicador,muchas,hc,hg]
  have hm := media_mono h _ _ (fun bs _ => hp bs)
  rw [media_suma,media_recorre paso_ensayo (fun w => indicador (vivo w)) h z] at hm
  have hcomp := complemento h z
  have hmany := cota_muchas C j h z
  change _≤probabilidad_pocas C j h z+_ at hm
  linarith

#print axioms muchas_fallos
#print axioms cota_muchas
#print axioms supervivencia_por_entradas
#print axioms cuenta_prefijo
#print axioms cuenta_reinicio
#print axioms completa_bloques

end ConteoEnsayosGao
