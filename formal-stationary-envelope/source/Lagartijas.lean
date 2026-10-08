import ConteoEnsayos

/- Lagartijas: pocas entradas admisibles en h pasos vivos es improbable.
   Un potencial por huecos entre entradas guardadas: cada hueco empieza en una
   entrada, recorre la excursión (cola H3) y la frontera (potencial geométrico).
   Todo sobre la cadena original y palabras de bits justos; sin condicionar. -/

noncomputable section
open Classical

namespace LagartijasGao

open CadenaCompletaGao MomentosGao RestoGao PalabrasGao GuardiasGao

/-! ## Riesgo de un hueco -/

section Hueco

variable (C : ℕ) (U : ℝ)

/-- Estado de ensayo y marca de magnitud acotada por U hasta ahora. -/
abbrev EstadoHueco := EstadoEnsayo × Bool

def paso_hueco (s : EstadoHueco) (b : Bool) : EstadoHueco :=
  (paso_ensayo s.1 b, s.2 && decide (tamano (paso_ensayo s.1 b).1 ≤ U))

def activo (s : EstadoHueco) : Bool := GuardiasGao.vivo s.1 && s.2

def rama (f : EstadoHueco → ℝ) (s : EstadoHueco) (b : Bool) : ℝ :=
  if guardia C (paso_hueco U s b).1 then 0 else f (paso_hueco U s b)

/-- Probabilidad de seguir n pasos más, vivo y acotado, sin nueva entrada guardada. -/
def riesgo_hueco : ℕ → EstadoHueco → ℝ
  | 0, s => if activo s then 1 else 0
  | n+1, s => if activo s then
      (rama C U (riesgo_hueco n) s false+rama C U (riesgo_hueco n) s true)/2 else 0

theorem riesgo_inactivo (n : ℕ) (s : EstadoHueco) (hs : activo s=false) :
    riesgo_hueco C U n s=0 := by
  cases n <;> simp [riesgo_hueco,hs]

theorem riesgo_cotas (n : ℕ) (s : EstadoHueco) :
    0≤riesgo_hueco C U n s ∧ riesgo_hueco C U n s≤1 := by
  induction n generalizing s with
  | zero => simp only [riesgo_hueco]; split <;> norm_num
  | succ n ih =>
    have hr : ∀ b, 0≤rama C U (riesgo_hueco C U n) s b ∧ rama C U (riesgo_hueco C U n) s b≤1 := by
      intro b
      unfold rama
      split
      · norm_num
      · exact ih _
    have h0 := hr false
    have h1 := hr true
    simp only [riesgo_hueco]
    split
    · constructor <;> linarith [h0.1,h0.2,h1.1,h1.2]
    · norm_num

theorem riesgo_no_negativo (n : ℕ) (s : EstadoHueco) : 0≤riesgo_hueco C U n s :=
  (riesgo_cotas C U n s).1

theorem riesgo_uno (n : ℕ) (s : EstadoHueco) : riesgo_hueco C U n s≤1 :=
  (riesgo_cotas C U n s).2

theorem riesgo_antitono_paso (n : ℕ) (s : EstadoHueco) :
    riesgo_hueco C U (n+1) s≤riesgo_hueco C U n s := by
  induction n generalizing s with
  | zero =>
    have h := riesgo_uno C U 1 s
    by_cases hs : activo s=true
    · simp only [riesgo_hueco,hs,if_true] at h ⊢
      simpa [riesgo_hueco,hs] using h
    · have hf : activo s=false := by simpa using hs
      simp [riesgo_inactivo C U _ s hf]
  | succ n ih =>
    have hr : ∀ b, rama C U (riesgo_hueco C U (n+1)) s b≤rama C U (riesgo_hueco C U n) s b := by
      intro b
      unfold rama
      split
      · rfl
      · exact ih _
    have h0 := hr false
    have h1 := hr true
    conv_lhs => rw [riesgo_hueco]
    conv_rhs => rw [riesgo_hueco]
    split
    · linarith
    · rfl

theorem riesgo_antitono (n k : ℕ) (s : EstadoHueco) :
    riesgo_hueco C U (n+k) s≤riesgo_hueco C U n s := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [← Nat.add_assoc]
    exact (riesgo_antitono_paso C U (n+k) s).trans ih

theorem activo_hijo (s : EstadoHueco) (b : Bool) (h : activo (paso_hueco U s b)=true) :
    activo s=true := by
  have hv : GuardiasGao.vivo (paso_ensayo s.1 b)=true ∧
      (s.2 && decide (tamano (paso_ensayo s.1 b).1≤U))=true := by
    simpa [activo,paso_hueco] using h
  have hok : s.2=true := (Bool.and_eq_true_iff.mp hv.2).1
  have hvivo : GuardiasGao.vivo s.1=true := by
    by_contra hz
    have hf : s.1.1=.fusion := by simpa [GuardiasGao.vivo] using hz
    have hp : (paso_ensayo s.1 b).1=.fusion := by simp [paso_ensayo,hf,paso]
    have hv1 := hv.1
    simp [GuardiasGao.vivo,hp] at hv1
  simp [activo,hvivo,hok]

end Hueco

/-! ## Autómata aumentado y potencial global -/

section Global

variable (C : ℕ) (U : ℝ)

structure Aumentado where
  z : EstadoEnsayo
  i : ℕ
  a : ℕ
  ok : Bool

def paso_aumentado (σ : Aumentado) (b : Bool) : Aumentado :=
  if guardia C (paso_hueco U (σ.z,σ.ok) b).1 then
    ⟨(paso_hueco U (σ.z,σ.ok) b).1,σ.i+1,0,(paso_hueco U (σ.z,σ.ok) b).2⟩
  else ⟨(paso_hueco U (σ.z,σ.ok) b).1,σ.i,σ.a+1,(paso_hueco U (σ.z,σ.ok) b).2⟩

theorem aumentado_hueco (σ : Aumentado) (b : Bool) :
    ((paso_aumentado C U σ b).z,(paso_aumentado C U σ b).ok)=paso_hueco U (σ.z,σ.ok) b := by
  unfold paso_aumentado
  split <;> rfl

theorem aumentado_indice (σ : Aumentado) (b : Bool) :
    σ.i≤(paso_aumentado C U σ b).i := by
  unfold paso_aumentado
  split <;> simp

/-- Hueco demasiado largo: vivo, acotado, menos de N entradas y edad al menos G. -/
def objetivo (N G : ℕ) (σ : Aumentado) : ℝ :=
  if activo (σ.z,σ.ok)=true ∧ σ.i<N ∧ G≤σ.a then 1 else 0

def potencial (N G : ℕ) (q : ℝ) (σ : Aumentado) : ℝ :=
  if activo (σ.z,σ.ok)=true ∧ σ.i<N then
    ((N-1-σ.i:ℕ):ℝ)*q+riesgo_hueco C U (G-σ.a) (σ.z,σ.ok) else 0

theorem potencial_no_negativo (N G : ℕ) (q : ℝ) (hq0 : 0≤q) (σ : Aumentado) :
    0≤potencial C U N G q σ := by
  unfold potencial
  split
  · have := riesgo_no_negativo C U (G-σ.a) (σ.z,σ.ok)
    positivity
  · rfl

theorem objetivo_dominado (N G : ℕ) (q : ℝ) (hq0 : 0≤q) (σ : Aumentado) :
    MaximosGao.indicador (objetivo N G) (1/2) σ≤potencial C U N G q σ := by
  have hpot := potencial_no_negativo C U N G q hq0 σ
  unfold MaximosGao.indicador objetivo
  by_cases ht : activo (σ.z,σ.ok)=true ∧ σ.i<N ∧ G≤σ.a
  · have hr : riesgo_hueco C U (G-σ.a) (σ.z,σ.ok)=1 := by
      rw [show G-σ.a=0 by omega]
      simp [riesgo_hueco,ht.1]
    have hp : potencial C U N G q σ=((N-1-σ.i:ℕ):ℝ)*q+1 := by
      simp [potencial,ht.1,ht.2.1,hr]
    have hA : 0≤((N-1-σ.i:ℕ):ℝ)*q := by positivity
    rw [if_pos ht,if_pos (by norm_num : (1:ℝ)/2<1),hp]
    linarith
  · rw [if_neg ht,if_neg (by norm_num : ¬(1:ℝ)/2<0)]
    exact hpot

/-- Cada hijo del potencial queda bajo la rama del riesgo correspondiente. -/
theorem potencial_hijo (N G : ℕ) (q : ℝ) (hq0 : 0≤q)
    (hq : ∀ s : EstadoHueco, activo s=true → guardia C s.1=true → riesgo_hueco C U G s≤q)
    (σ : Aumentado) (b : Bool) :
    potencial C U N G q (paso_aumentado C U σ b)≤
      ((N-1-σ.i:ℕ):ℝ)*q+rama C U (riesgo_hueco C U (G-σ.a-1)) (σ.z,σ.ok) b := by
  have hA : 0≤((N-1-σ.i:ℕ):ℝ)*q := by positivity
  by_cases hg : guardia C (paso_hueco U (σ.z,σ.ok) b).1=true
  · have he : paso_aumentado C U σ b=
        ⟨(paso_hueco U (σ.z,σ.ok) b).1,σ.i+1,0,(paso_hueco U (σ.z,σ.ok) b).2⟩ := by
      simp [paso_aumentado,hg]
    have hrama : rama C U (riesgo_hueco C U (G-σ.a-1)) (σ.z,σ.ok) b=0 := by
      simp [rama,hg]
    rw [he,hrama]
    unfold potencial
    dsimp only
    split_ifs with hc
    · have hG := hq (paso_hueco U (σ.z,σ.ok) b) (by simpa using hc.1) hg
      have hnat : (N-1-(σ.i+1):ℕ)+1=N-1-σ.i := by omega
      have hcast : ((N-1-(σ.i+1):ℕ):ℝ)+1=((N-1-σ.i:ℕ):ℝ) := by exact_mod_cast hnat
      rw [← hcast,Nat.sub_zero]
      have hq' : riesgo_hueco C U G ((paso_hueco U (σ.z,σ.ok) b).1,
          (paso_hueco U (σ.z,σ.ok) b).2)≤q := by simpa using hG
      nlinarith
    · linarith
  · have hgf : guardia C (paso_hueco U (σ.z,σ.ok) b).1=false := by simpa using hg
    have he : paso_aumentado C U σ b=
        ⟨(paso_hueco U (σ.z,σ.ok) b).1,σ.i,σ.a+1,(paso_hueco U (σ.z,σ.ok) b).2⟩ := by
      simp [paso_aumentado,hgf]
    have hrama : rama C U (riesgo_hueco C U (G-σ.a-1)) (σ.z,σ.ok) b=
        riesgo_hueco C U (G-σ.a-1) (paso_hueco U (σ.z,σ.ok) b) := by
      simp [rama,hgf]
    rw [he,hrama]
    have hR := riesgo_no_negativo C U (G-σ.a-1) (paso_hueco U (σ.z,σ.ok) b)
    unfold potencial
    dsimp only
    split_ifs with hc
    · rw [show G-(σ.a+1)=G-σ.a-1 by omega]
    · linarith

theorem potencial_superarmonico (N G : ℕ) (q : ℝ) (hq0 : 0≤q)
    (hq : ∀ s : EstadoHueco, activo s=true → guardia C s.1=true → riesgo_hueco C U G s≤q)
    (σ : Aumentado) :
    (potencial C U N G q (paso_aumentado C U σ false)+
      potencial C U N G q (paso_aumentado C U σ true))/2≤potencial C U N G q σ := by
  by_cases hσ : activo (σ.z,σ.ok)=true ∧ σ.i<N
  · have h0 := potencial_hijo C U N G q hq0 hq σ false
    have h1 := potencial_hijo C U N G q hq0 hq σ true
    have hp : potencial C U N G q σ=((N-1-σ.i:ℕ):ℝ)*q+riesgo_hueco C U (G-σ.a) (σ.z,σ.ok) := by
      simp [potencial,hσ.1,hσ.2]
    rw [hp]
    by_cases ha : G≤σ.a
    · have hr1 : riesgo_hueco C U (G-σ.a) (σ.z,σ.ok)=1 := by
        rw [show G-σ.a=0 by omega]
        simp [riesgo_hueco,hσ.1]
      have hb : ∀ b, rama C U (riesgo_hueco C U (G-σ.a-1)) (σ.z,σ.ok) b≤1 := by
        intro b
        unfold rama
        split
        · norm_num
        · exact riesgo_uno C U _ _
      have hb0 := hb false
      have hb1 := hb true
      rw [hr1]
      linarith
    · have hr : riesgo_hueco C U (G-σ.a) (σ.z,σ.ok)=
          (rama C U (riesgo_hueco C U (G-σ.a-1)) (σ.z,σ.ok) false+
            rama C U (riesgo_hueco C U (G-σ.a-1)) (σ.z,σ.ok) true)/2 := by
        rw [show G-σ.a=(G-σ.a-1)+1 by omega]
        simp [riesgo_hueco,hσ.1]
      rw [hr]
      linarith
  · have hp : potencial C U N G q σ=0 := by simp [potencial,hσ]
    have hc : ∀ b, potencial C U N G q (paso_aumentado C U σ b)=0 := by
      intro b
      unfold potencial
      split
      · rename_i hc
        exfalso
        apply hσ
        have hh := aumentado_hueco C U σ b
        have ha : activo (σ.z,σ.ok)=true := by
          apply activo_hijo U (σ.z,σ.ok) b
          rw [← hh]
          exact hc.1
        exact ⟨ha,lt_of_le_of_lt (aumentado_indice C U σ b) hc.2⟩
      · rfl
    rw [hp,hc false,hc true]
    norm_num

theorem objetivo_cruce (N G : ℕ) (q : ℝ) (hq0 : 0≤q)
    (hq : ∀ s : EstadoHueco, activo s=true → guardia C s.1=true → riesgo_hueco C U G s≤q)
    (n : ℕ) (σ : Aumentado) :
    MaximosGao.cruce (paso_aumentado C U) (objetivo N G) (1/2) n σ≤potencial C U N G q σ :=
  MaximosGao.cruce_dominado _ _ _ _ (objetivo_dominado C U N G q hq0)
    (potencial_superarmonico C U N G q hq0 hq) n σ

end Global

/-! ## Reloj determinista: sin hueco largo hay N entradas antes de h -/

section Reloj

variable (C : ℕ) (U : ℝ)

theorem aumentado_z (σ : Aumentado) (b : Bool) :
    (paso_aumentado C U σ b).z=paso_ensayo σ.z b := by
  unfold paso_aumentado
  split <;> rfl

theorem aumentado_ok (σ : Aumentado) (b : Bool) :
    (paso_aumentado C U σ b).ok=(σ.ok && decide (tamano (paso ((σ.z).1) b)≤U)) := by
  unfold paso_aumentado
  split <;> rfl

theorem aumentado_reinicio (σ : Aumentado) (b : Bool) (hg : guardia C (paso_ensayo σ.z b)=true) :
    (paso_aumentado C U σ b).i=σ.i+1 ∧ (paso_aumentado C U σ b).a=0 := by
  have hg2 : guardia C (paso_hueco U (σ.z,σ.ok) b).1=true := by simpa [paso_hueco] using hg
  simp [paso_aumentado,hg2]

theorem aumentado_sigue (σ : Aumentado) (b : Bool) (hg : guardia C (paso_ensayo σ.z b)=false) :
    (paso_aumentado C U σ b).i=σ.i ∧ (paso_aumentado C U σ b).a=σ.a+1 := by
  have hg2 : guardia C (paso_hueco U (σ.z,σ.ok) b).1=false := by simpa [paso_hueco] using hg
  simp [paso_aumentado,hg2]

theorem vivo_hijo_ensayo (z : EstadoEnsayo) (b : Bool)
    (h : GuardiasGao.vivo (paso_ensayo z b)=true) : GuardiasGao.vivo z=true := by
  by_contra hz
  have hf : z.1=.fusion := by simpa [GuardiasGao.vivo] using hz
  have hp : (paso_ensayo z b).1=.fusion := by simp [paso_ensayo,hf,paso]
  simp [GuardiasGao.vivo,hp] at h

theorem vivo_recorre_inicio (bs : List Bool) (z : EstadoEnsayo)
    (h : GuardiasGao.vivo (recorre paso_ensayo bs z)=true) : GuardiasGao.vivo z=true := by
  induction bs generalizing z with
  | nil => exact h
  | cons b bs ih => exact vivo_hijo_ensayo z b (ih (paso_ensayo z b) h)

theorem recorre_aumentado_z (bs : List Bool) (σ : Aumentado) :
    (recorre (paso_aumentado C U) bs σ).z=recorre paso_ensayo bs σ.z := by
  induction bs generalizing σ with
  | nil => rfl
  | cons b bs ih =>
    simp only [recorre]
    rw [ih,aumentado_z]

theorem cuenta_aumentado (bs : List Bool) (σ : Aumentado) :
    ConteoEnsayosGao.cuenta paso_ensayo (guardia C) bs σ.z+σ.i=
      (recorre (paso_aumentado C U) bs σ).i+(if guardia C σ.z then 1 else 0) := by
  induction bs generalizing σ with
  | nil => simp only [ConteoEnsayosGao.cuenta,recorre]; omega
  | cons b bs ih =>
    have hi := ih (paso_aumentado C U σ b)
    rw [aumentado_z] at hi
    simp only [ConteoEnsayosGao.cuenta,recorre]
    by_cases hg : guardia C (paso_ensayo σ.z b)=true
    · have hr := (aumentado_reinicio C U σ b hg).1
      rw [hr] at hi
      simp only [hg,if_true] at hi
      omega
    · have hgf : guardia C (paso_ensayo σ.z b)=false := by simpa using hg
      have hr := (aumentado_sigue C U σ b hgf).1
      rw [hr] at hi
      simp only [hgf,Bool.false_eq_true,if_false] at hi
      omega

theorem cruza_cabeza {S : Type} (p : S → Bool → S) (u : S → ℝ) (V : ℝ) (bs : List Bool) (z : S)
    (h : ¬cruza p u V bs z) : u z≤V := cruza_prefijo p u V [] bs z h

theorem reloj_determinista (N G : ℕ) : ∀ (bs : List Bool) (σ : Aumentado) (t : ℕ),
    σ.ok=true → (N≤σ.i ∨ t≤σ.i*G+σ.a) →
    ¬cruza paso tamano U bs σ.z.1 →
    ¬cruza (paso_aumentado C U) (objetivo N G) (1/2) bs σ →
    GuardiasGao.vivo (recorre paso_ensayo bs σ.z)=true →
    N≤(recorre (paso_aumentado C U) bs σ).i ∨
      (t+bs.length≤(recorre (paso_aumentado C U) bs σ).i*G+(recorre (paso_aumentado C U) bs σ).a ∧
        (recorre (paso_aumentado C U) bs σ).a<G) := by
  intro bs
  induction bs with
  | nil =>
    intro σ t hok hinv _ hobj hv
    simp only [recorre,List.length_nil,Nat.add_zero]
    have hv0 : GuardiasGao.vivo σ.z=true := by simpa [recorre] using hv
    have hact : activo (σ.z,σ.ok)=true := by simp [activo,hok,hv0]
    have hno : ¬(activo (σ.z,σ.ok)=true ∧ σ.i<N ∧ G≤σ.a) := by
      intro ht
      apply hobj
      simp only [cruza,objetivo]
      rw [if_pos ht]
      norm_num
    by_cases hN : N≤σ.i
    · exact Or.inl hN
    · right
      rcases hinv with h | h
      · exact absurd h hN
      · refine ⟨h,?_⟩
        by_contra ha
        exact hno ⟨hact,by omega,by omega⟩
  | cons b bs ih =>
    intro σ t hok hinv htam hobj hv
    simp only [cruza,not_or] at htam hobj
    have hv0 : GuardiasGao.vivo σ.z=true := vivo_recorre_inicio (b::bs) σ.z hv
    have hact : activo (σ.z,σ.ok)=true := by simp [activo,hok,hv0]
    have hno : ¬(activo (σ.z,σ.ok)=true ∧ σ.i<N ∧ G≤σ.a) := by
      intro ht
      apply hobj.1
      simp only [objetivo]
      rw [if_pos ht]
      norm_num
    have hok2 : (paso_aumentado C U σ b).ok=true := by
      rw [aumentado_ok]
      have ht := cruza_cabeza paso tamano U bs (paso σ.z.1 b) htam.2
      simp [hok,ht]
    have hinv2 : N≤(paso_aumentado C U σ b).i ∨
        t+1≤(paso_aumentado C U σ b).i*G+(paso_aumentado C U σ b).a := by
      by_cases hN : N≤σ.i
      · exact Or.inl (hN.trans (aumentado_indice C U σ b))
      · right
        have hti : t≤σ.i*G+σ.a := by
          rcases hinv with h | h
          · exact absurd h hN
          · exact h
        have haG : σ.a<G := by
          by_contra ha
          exact hno ⟨hact,by omega,by omega⟩
        by_cases hg : guardia C (paso_ensayo σ.z b)=true
        · obtain ⟨hi,ha⟩ := aumentado_reinicio C U σ b hg
          rw [hi,ha,Nat.succ_mul]
          omega
        · have hgf : guardia C (paso_ensayo σ.z b)=false := by simpa using hg
          obtain ⟨hi,ha⟩ := aumentado_sigue C U σ b hgf
          rw [hi,ha]
          omega
    have hz : (paso_aumentado C U σ b).z=paso_ensayo σ.z b := aumentado_z C U σ b
    have htam2 : ¬cruza paso tamano U bs (paso_aumentado C U σ b).z.1 := by
      rw [hz]
      exact htam.2
    have hv2 : GuardiasGao.vivo (recorre paso_ensayo bs (paso_aumentado C U σ b).z)=true := by
      rw [hz]
      exact hv
    have hr := ih (paso_aumentado C U σ b) (t+1) hok2 hinv2 htam2 hobj.2 hv2
    simp only [recorre,List.length_cons]
    rcases hr with h | h
    · exact Or.inl h
    · right
      exact ⟨by omega,h.2⟩

/-- Estado inicial de la cadena de ensayos y del autómata aumentado. -/
def inicio_ensayo : EstadoEnsayo := (.vivo 0 1,false)

def inicio_aumentado : Aumentado := ⟨inicio_ensayo,0,0,true⟩

theorem muchas_entradas (N G h : ℕ) (hNG : N*G≤h) (bs : List Bool) (hb : bs.length=h)
    (h1 : ¬cruza paso tamano U bs (.vivo 0 1))
    (h2 : ¬cruza (paso_aumentado C U) (objetivo N G) (1/2) bs inicio_aumentado)
    (hv : GuardiasGao.vivo (recorre paso_ensayo bs inicio_ensayo)=true) :
    N≤ConteoEnsayosGao.cuenta paso_ensayo (guardia C) bs inicio_ensayo := by
  have hr := reloj_determinista C U N G bs inicio_aumentado 0 rfl
    (Or.inr (by simp [inicio_aumentado])) h1 h2 hv
  have hc := cuenta_aumentado C U bs inicio_aumentado
  have hg : guardia C inicio_ensayo=false := by simp [guardia,inicio_ensayo]
  have hc2 : ConteoEnsayosGao.cuenta paso_ensayo (guardia C) bs inicio_ensayo=
      (recorre (paso_aumentado C U) bs inicio_aumentado).i := by
    have hz : inicio_aumentado.z=inicio_ensayo := rfl
    have hi : inicio_aumentado.i=0 := rfl
    rw [hz,hi,hg] at hc
    simpa using hc
  rw [hc2]
  rcases hr with h | h
  · exact h
  · by_contra hlt
    have hle : (recorre (paso_aumentado C U) bs inicio_aumentado).i+1≤N := by omega
    have hm := Nat.mul_le_mul_right G hle
    rw [Nat.succ_mul] at hm
    rw [hb] at h
    omega

/-- alcanza y el cruce genérico son la misma recursión. -/
theorem alcanza_cruce (V : ℝ) (n : ℕ) (z : Estado) :
    alcanza V n z=MaximosGao.cruce paso tamano V n z := by
  induction n generalizing z with
  | zero => simp [alcanza,MaximosGao.cruce,MomentosGao.indicador,MaximosGao.indicador]
  | succ n ih => simp only [alcanza,MaximosGao.cruce,ih]

theorem pocas_entradas (N G h : ℕ) (q : ℝ) (hq0 : 0≤q)
    (hq : ∀ s : EstadoHueco, activo s=true → guardia C s.1=true → riesgo_hueco C U G s≤q)
    (hNG : N*G≤h) :
    media h (fun bs => RepeticionGao.indicador (GuardiasGao.vivo (recorre paso_ensayo bs inicio_ensayo) &&
      decide (ConteoEnsayosGao.cuenta paso_ensayo (guardia C) bs inicio_ensayo<N)))≤
      alcanza U h (.vivo 0 1)+potencial C U N G q inicio_aumentado := by
  have hpt : ∀ bs : List Bool, bs.length=h →
      RepeticionGao.indicador (GuardiasGao.vivo (recorre paso_ensayo bs inicio_ensayo) &&
        decide (ConteoEnsayosGao.cuenta paso_ensayo (guardia C) bs inicio_ensayo<N))≤
      marca (cruza paso tamano U bs (.vivo 0 1))+
        marca (cruza (paso_aumentado C U) (objetivo N G) (1/2) bs inicio_aumentado) := by
    intro bs hb
    have hm1 : 0≤marca (cruza paso tamano U bs (.vivo 0 1)) := by unfold marca; split <;> norm_num
    have hm2 : 0≤marca (cruza (paso_aumentado C U) (objetivo N G) (1/2) bs inicio_aumentado) := by
      unfold marca; split <;> norm_num
    by_cases hA : (GuardiasGao.vivo (recorre paso_ensayo bs inicio_ensayo) &&
        decide (ConteoEnsayosGao.cuenta paso_ensayo (guardia C) bs inicio_ensayo<N))=true
    · have hv := (Bool.and_eq_true_iff.mp hA).1
      have hlt : ConteoEnsayosGao.cuenta paso_ensayo (guardia C) bs inicio_ensayo<N := by
        simpa using (Bool.and_eq_true_iff.mp hA).2
      rw [hA]
      by_cases c1 : cruza paso tamano U bs (.vivo 0 1)
      · have e1 : marca (cruza paso tamano U bs (.vivo 0 1))=1 := by simp [marca,c1]
        simp only [RepeticionGao.indicador,if_true]; linarith
      · by_cases c2 : cruza (paso_aumentado C U) (objetivo N G) (1/2) bs inicio_aumentado
        · have e2 : marca (cruza (paso_aumentado C U) (objetivo N G) (1/2) bs inicio_aumentado)=1 := by
            unfold marca; rw [if_pos c2]
          simp only [RepeticionGao.indicador,if_true]; linarith
        · exfalso
          have := muchas_entradas C U N G h hNG bs hb c1 c2 hv
          omega
    · have hf : (GuardiasGao.vivo (recorre paso_ensayo bs inicio_ensayo) &&
          decide (ConteoEnsayosGao.cuenta paso_ensayo (guardia C) bs inicio_ensayo<N))=false := by
        simpa using hA
      rw [hf]
      simp only [RepeticionGao.indicador,Bool.false_eq_true,if_false]
      linarith
  have hm := media_mono h _ _ hpt
  rw [media_suma,media_cruza,media_cruza] at hm
  rw [alcanza_cruce]
  have hc := objetivo_cruce C U N G q hq0 hq h inicio_aumentado
  linarith

end Reloj

/-! ## Un hueco que empieza en una entrada: excursión y frontera -/

section Excursion

variable (C : ℕ) (U : ℝ)

/-- P_z(la excursión sigue en el RestoGao.interior tras k pasos), con la cadena detenida. -/
def surv (k : ℕ) (z : Estado) : ℝ :=
  promedio SupervivenciaGao.paso_excursion SupervivenciaGao.vivo k z

theorem surv_fuera (k : ℕ) (z : Estado) (hz : RestoGao.interior z=false) : surv k z=0 := by
  induction k with
  | zero => simp [surv,promedio,SupervivenciaGao.vivo,hz]
  | succ k ih =>
    unfold surv at ih ⊢
    simp only [promedio,SupervivenciaGao.paso_excursion,hz,Bool.false_eq_true,if_false,ih]
    norm_num

theorem surv_paso (k : ℕ) (z : Estado) (hz : RestoGao.interior z=true) :
    surv (k+1) z=(surv k (paso z false)+surv k (paso z true))/2 := by
  simp [surv,promedio,SupervivenciaGao.paso_excursion,hz]

theorem surv_cotas (k : ℕ) (z : Estado) : 0≤surv k z ∧ surv k z≤1 := by
  have hv0 : ∀ w, 0≤SupervivenciaGao.vivo w := SupervivenciaGao.vivo_no_negativo
  have hv1 : ∀ w, SupervivenciaGao.vivo w≤1 := by
    intro w; unfold SupervivenciaGao.vivo; split <;> norm_num
  constructor
  · exact promedio_no_negativo _ _ hv0 k z
  · have h := promedio_mono SupervivenciaGao.paso_excursion _ (fun _ => 1) hv1 k z
    rwa [promedio_constante] at h

theorem surv_cero (z : Estado) (hz : RestoGao.interior z=true) : surv 0 z=1 := by
  simp [surv,promedio,SupervivenciaGao.vivo,hz]

/-- Desde el RestoGao.interior se sigue en el RestoGao.interior o se sale exactamente a k=1. -/
theorem interior_hijo (z : Estado) (hz : RestoGao.interior z=true) (b : Bool) :
    RestoGao.interior (paso z b)=true ∨ ∃ c, paso z b=.vivo 1 c := by
  cases z with
  | fusion => simp [RestoGao.interior] at hz
  | vivo k c =>
    cases k with
    | zero => simp [RestoGao.interior] at hz
    | succ k =>
      cases k with
      | zero => simp [RestoGao.interior] at hz
      | succ k =>
        by_cases hc : c%2=0
        · left; cases b <;> simp [paso,hc,RestoGao.interior]
        · cases b with
          | false => left; simp [paso,hc,RestoGao.interior]
          | true =>
            cases k with
            | zero => right; exact ⟨(c-coef 1)/2,by simp [paso,hc]⟩
            | succ j => left; simp [paso,hc,RestoGao.interior]

theorem entrada_desde_interior (z w : Estado) (hz : RestoGao.interior z=true) : entrada z w=false := by
  cases z with
  | fusion => simp [RestoGao.interior] at hz
  | vivo k c =>
    cases k with
    | zero => simp [RestoGao.interior] at hz
    | succ k =>
      cases k with
      | zero => simp [RestoGao.interior] at hz
      | succ k => cases w <;> simp [entrada]

theorem guardia_desde_interior (s : EstadoHueco) (hz : RestoGao.interior s.1.1=true) (b : Bool) :
    guardia C (paso_hueco U s b).1=false := by
  simp [paso_hueco,paso_ensayo,guardia,entrada_desde_interior _ _ hz]

def cota_excursion (β : ℝ) (B n : ℕ) (s : EstadoHueco) : ℝ :=
  if activo s=true then
    (if RestoGao.interior s.1.1=true then (if B+1≤n then surv (n-(B+1)) s.1.1+β else 1+β)
     else riesgo_hueco C U n s)
  else 0

theorem riesgo_excursion (β : ℝ) (B : ℕ) (hβ0 : 0≤β)
    (hβ : ∀ (n : ℕ) (s : EstadoHueco) (c : ℤ), B≤n → activo s=true → s.1.1=.vivo 1 c →
      riesgo_hueco C U n s≤β) :
    ∀ (n : ℕ) (s : EstadoHueco), riesgo_hueco C U n s≤cota_excursion C U β B n s := by
  intro n
  induction n with
  | zero =>
    intro s
    unfold cota_excursion
    by_cases ha : activo s=true
    · by_cases hi : RestoGao.interior s.1.1=true
      · simp only [ha,hi,if_true,show ¬(B+1≤0) by omega,if_false]
        have := riesgo_uno C U 0 s
        linarith
      · simp [ha,hi]
    · have hf : activo s=false := by simpa using ha
      simp [hf,riesgo_inactivo C U 0 s hf]
  | succ n ih =>
    intro s
    by_cases ha : activo s=true
    · by_cases hi : RestoGao.interior s.1.1=true
      · by_cases hB : B+1≤n
        · have hcota : cota_excursion C U β B (n+1) s=
              (surv (n-(B+1)) (paso s.1.1 false)+surv (n-(B+1)) (paso s.1.1 true))/2+β := by
            unfold cota_excursion
            rw [if_pos ha,if_pos hi,if_pos (by omega),show n+1-(B+1)=(n-(B+1))+1 by omega,
              surv_paso _ _ hi]
          have hrama : ∀ b, rama C U (riesgo_hueco C U n) s b≤surv (n-(B+1)) (paso s.1.1 b)+β := by
            intro b
            have hg := guardia_desde_interior C U s hi b
            have hw1 : (paso_hueco U s b).1.1=paso s.1.1 b := rfl
            simp only [rama,hg,Bool.false_eq_true,if_false]
            have hc := ih (paso_hueco U s b)
            have hs0 := (surv_cotas (n-(B+1)) (paso s.1.1 b)).1
            unfold cota_excursion at hc
            by_cases hab : activo (paso_hueco U s b)=true
            · rw [if_pos hab] at hc
              by_cases hib : RestoGao.interior (paso_hueco U s b).1.1=true
              · rw [if_pos hib,if_pos hB,hw1] at hc
                exact hc
              · rw [if_neg hib] at hc
                have hib2 : RestoGao.interior (paso s.1.1 b)=false := by simpa [hw1] using hib
                rcases interior_hijo s.1.1 hi b with h | ⟨c,hc1⟩
                · rw [h] at hib2; exact absurd hib2 (by simp)
                · have hβn := hβ n (paso_hueco U s b) c (by omega) hab (by rw [hw1,hc1])
                  rw [surv_fuera _ _ hib2]
                  linarith
            · rw [if_neg hab] at hc
              linarith
          have h0 := hrama false
          have h1 := hrama true
          rw [hcota]
          simp only [riesgo_hueco,ha,if_true]
          linarith
        · have hge : 1≤cota_excursion C U β B (n+1) s := by
            unfold cota_excursion
            rw [if_pos ha,if_pos hi]
            split
            · rw [show n+1-(B+1)=0 by omega,surv_cero _ hi]
              linarith
            · linarith
          have := riesgo_uno C U (n+1) s
          linarith
      · have hf : RestoGao.interior s.1.1=false := by simpa using hi
        unfold cota_excursion
        simp [ha,hf]
    · have hf : activo s=false := by simpa using ha
      unfold cota_excursion
      simp [hf,riesgo_inactivo C U (n+1) s hf]

/-- Riesgo de un hueco desde una entrada: cola de la excursión más frontera. -/
theorem riesgo_entrada (β : ℝ) (B d : ℕ) (hβ0 : 0≤β)
    (hβ : ∀ (n : ℕ) (s : EstadoHueco) (c : ℤ), B≤n → activo s=true → s.1.1=.vivo 1 c →
      riesgo_hueco C U n s≤β)
    (c : ℤ) (bandera : Bool) :
    riesgo_hueco C U (d+B+1) ((.vivo 2 c,bandera),true)≤SupervivenciaGao.supervivencia d c+β := by
  have h := riesgo_excursion C U β B hβ0 hβ (d+B+1) ((.vivo 2 c,bandera),true)
  have ha : activo ((.vivo 2 c,bandera),true)=true := by simp [activo,GuardiasGao.vivo]
  have hi : RestoGao.interior (Estado.vivo 2 c)=true := rfl
  unfold cota_excursion at h
  rw [if_pos ha,if_pos hi,if_pos (by omega),show d+B+1-(B+1)=d by omega] at h
  exact h

end Excursion

/-! ## Frontera: potencial geométrico con la valoración diádica del hueco -/

section Frontera

variable (C : ℕ) (U : ℝ)

def dos_adica (c : ℤ) : ℕ := padicValNat 2 c.natAbs

theorem dos_adica_impar (c : ℤ) (hc : c%2≠0) : dos_adica c=0 := by
  unfold dos_adica
  apply padicValNat.eq_zero_of_not_dvd
  intro h
  have h2 : (2:ℤ) ∣ c := Int.natAbs_dvd_natAbs.mp (by simpa using h)
  omega

theorem dos_adica_doble (e : ℤ) (he : e≠0) : dos_adica (2*e)=dos_adica e+1 := by
  unfold dos_adica
  rw [Int.natAbs_mul]
  have h2 : (2:ℤ).natAbs=2 := rfl
  rw [h2,padicValNat.mul (by norm_num) (Int.natAbs_ne_zero.mpr he),padicValNat_self]
  ring

theorem dos_adica_triple (e : ℤ) (he : e≠0) : dos_adica (3*e)=dos_adica e := by
  unfold dos_adica
  rw [Int.natAbs_mul]
  have h3 : (3:ℤ).natAbs=3 := rfl
  rw [h3,padicValNat.mul (by norm_num) (Int.natAbs_ne_zero.mpr he),
    padicValNat.eq_zero_of_not_dvd (by decide : ¬2 ∣ 3)]
  ring

theorem dos_adica_mitad (c : ℤ) (hc0 : c≠0) (hc : c%2=0) : dos_adica (c/2)+1=dos_adica c := by
  have he : c=2*(c/2) := by omega
  have hne : c/2≠0 := by omega
  conv_rhs => rw [he]
  rw [dos_adica_doble _ hne]

theorem dos_adica_tres_mitad (c : ℤ) (hc0 : c≠0) (hc : c%2=0) :
    dos_adica (3*c/2)+1=dos_adica c := by
  have he : 3*c/2=3*(c/2) := by omega
  have hne : c/2≠0 := by omega
  rw [he,dos_adica_triple _ hne,dos_adica_mitad c hc0 hc]

theorem dos_adica_cota (c : ℤ) (hc0 : c≠0) : (2:ℝ)^(dos_adica c)≤(c.natAbs:ℝ) := by
  have hd : 2^(dos_adica c) ∣ c.natAbs := pow_padicValNat_dvd
  have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr hc0) hd
  exact_mod_cast hle

theorem mag_real (c : ℤ) : ((mag c:ℤ):ℝ)=(c.natAbs:ℝ) := by
  have h : mag c=(c.natAbs:ℤ) := by
    unfold mag
    split
    · rename_i hn
      rw [Int.ofNat_natAbs_of_nonpos (le_of_lt hn)]
    · rename_i hn
      rw [Int.natAbs_of_nonneg (by omega)]
  rw [h]
  simp

theorem tamano_vivo (k : ℕ) (c : ℤ) : tamano (.vivo k c)=(c.natAbs:ℝ)/((3:ℝ)^k) := by
  unfold tamano
  simp only [datos]
  rw [mag_real,coef_es_potencia]
  push_cast
  ring

def peso (θ : ℝ) (V : ℕ) : Estado → ℝ
  | .vivo 0 c => 2*θ^(dos_adica c+1)
  | .vivo 1 c => if c%2=0 then 2 else θ^(V+2)
  | _ => 0

def en_frontera : Estado → Prop
  | .vivo 0 c => c≠0
  | .vivo 1 _ => True
  | _ => False

def contribucion (θ : ℝ) (V : ℕ) (s : EstadoHueco) (b : Bool) : ℝ :=
  if guardia C (paso_hueco U s b).1=false ∧ activo (paso_hueco U s b)=true then
    peso θ V (paso s.1.1 b) else 0

variable (θ : ℝ) (V : ℕ)

theorem peso_no_negativo (hθ1 : 1≤θ) (z : Estado) : 0≤peso θ V z := by
  have hθ0 : 0≤θ := by linarith
  cases z with
  | fusion => simp [peso]
  | vivo k c =>
    cases k with
    | zero => simp only [peso]; positivity
    | succ k =>
      cases k with
      | zero => simp only [peso]; split <;> positivity
      | succ k => simp [peso]

theorem peso_uno_cota (hθ1 : 1≤θ) (hθ : θ^(V+3)≤4-2*θ) (c : ℤ) : peso θ V (.vivo 1 c)≤2 := by
  simp only [peso]
  split
  · rfl
  · have hm : θ^(V+2)≤θ^(V+3) := pow_le_pow_right₀ hθ1 (by omega)
    linarith

theorem peso_uno_minimo (hθ1 : 1≤θ) (z : Estado) (hz : en_frontera z) : 1≤peso θ V z := by
  cases z with
  | fusion => simp [en_frontera] at hz
  | vivo k c =>
    cases k with
    | zero =>
      simp only [peso]
      have := one_le_pow₀ (n:=dos_adica c+1) hθ1
      linarith
    | succ k =>
      cases k with
      | zero =>
        simp only [peso]
        split
        · norm_num
        · exact one_le_pow₀ hθ1
      | succ k => simp [en_frontera] at hz

theorem contribucion_cota (hθ1 : 1≤θ) (s : EstadoHueco) (b : Bool) :
    0≤contribucion C U θ V s b ∧ contribucion C U θ V s b≤peso θ V (paso s.1.1 b) := by
  have hp := peso_no_negativo θ V hθ1 (paso s.1.1 b)
  unfold contribucion
  split
  · exact ⟨hp,le_rfl⟩
  · exact ⟨le_rfl,hp⟩

theorem activo_tamano (s : EstadoHueco) (b : Bool) (h : activo (paso_hueco U s b)=true) :
    tamano (paso s.1.1 b)≤U := by
  have h2 : (s.2 && decide (tamano (paso s.1.1 b)≤U))=true := by
    have := (Bool.and_eq_true_iff.mp h).2
    simpa [paso_hueco,paso_ensayo] using this
  simpa using (Bool.and_eq_true_iff.mp h2).2

theorem paso_cero_par (c : ℤ) (hc : c%2=0) (b : Bool) :
    paso (.vivo 0 c) b=.vivo 0 (if b then 3*c/2 else c/2) := by
  simp [paso,hc]

theorem paso_cero_impar (c : ℤ) (hc : c%2≠0) (b : Bool) :
    paso (.vivo 0 c) b=.vivo 1 (if b then (1-3*c)/2 else (3*c+1)/2) := by
  simp [paso,hc]

theorem paso_uno_par (c : ℤ) (hc : c%2=0) (b : Bool) :
    paso (.vivo 1 c) b=.vivo 1 (if b then (3*c+1-3)/2 else c/2) := by
  have h : paso (.vivo (0+1) c) b=.vivo (0+1) (if b then (3*c+1-coef (0+1))/2 else c/2) := by
    simp only [paso,hc,if_true]
  simpa [coef] using h

theorem paso_uno_impar_falso (c : ℤ) (hc : c%2≠0) :
    paso (.vivo 1 c) false=.vivo 2 ((3*c+1)/2) := by
  have h : paso (.vivo (0+1) c) false=.vivo (0+2) ((3*c+1)/2) := by
    simp [paso,hc]
  simpa using h

theorem paso_uno_impar_cierto (c : ℤ) (hc : c%2≠0) :
    paso (.vivo 1 c) true=if c=1 then .fusion else .vivo 0 (mag ((c-1)/2)) := by
  have h : paso (.vivo (0+1) c) true=if c=1 then .fusion else .vivo 0 (mag ((c-1)/2)) := by
    simp [paso,hc]
  simpa using h

/-- Una entrada no guardada deja la magnitud por encima de U. -/
theorem entrada_sin_guardia (hCU : 9*U≤(C:ℝ)) (s : EstadoHueco) (c : ℤ) (hs : s.1.1=.vivo 1 c)
    (hc : c%2≠0) :
    ¬(guardia C (paso_hueco U s false).1=false ∧ activo (paso_hueco U s false)=true) := by
  rintro ⟨hg,ha⟩
  have hp := paso_uno_impar_falso c hc
  have ht := activo_tamano U s false ha
  rw [hs,hp,tamano_vivo] at ht
  have hw : (paso_hueco U s false).1=(.vivo 2 ((3*c+1)/2),true) := by
    simp [paso_hueco,paso_ensayo,hs,hp,entrada]
  rw [hw] at hg
  have hgc : ¬(((3*c+1)/2).natAbs≤C) := by simpa [guardia] using hg
  have hlt : (C:ℝ)<(((3*c+1)/2).natAbs:ℝ) := by exact_mod_cast (Nat.lt_of_not_le hgc)
  have h9 : ((3:ℝ)^2)=9 := by norm_num
  rw [h9] at ht
  have := (div_le_iff₀ (by norm_num : (0:ℝ)<9)).mp ht
  linarith

theorem cierre_frontera (s : EstadoHueco) (hs : en_frontera s.1.1) (b : Bool)
    (hcond : guardia C (paso_hueco U s b).1=false ∧ activo (paso_hueco U s b)=true)
    (hCU : 9*U≤(C:ℝ)) :
    en_frontera (paso s.1.1 b) := by
  rcases hz : s.1.1 with _ | ⟨k,c⟩
  · rw [hz] at hs; simp [en_frontera] at hs
  · rw [hz] at hs
    cases k with
    | zero =>
      have hc0 : c≠0 := hs
      by_cases hc : c%2=0
      · rw [paso_cero_par c hc]
        cases b <;> simp [en_frontera] <;> omega
      · rw [paso_cero_impar c hc]
        simp [en_frontera]
    | succ k =>
      cases k with
      | zero =>
        by_cases hc : c%2=0
        · rw [paso_uno_par c hc]
          simp [en_frontera]
        · cases b with
          | false => exact absurd hcond (entrada_sin_guardia C U hCU s c hz hc)
          | true =>
            rw [paso_uno_impar_cierto c hc]
            by_cases h1 : c=1
            · exfalso
              have ha := hcond.2
              have hp := paso_uno_impar_cierto c hc
              rw [if_pos h1] at hp
              have hf : (paso_hueco U s true).1.1=.fusion := by
                show paso s.1.1 true=.fusion
                rw [hz]
                exact hp
              simp [activo,GuardiasGao.vivo,hf] at ha
            · simp only [h1,if_false,en_frontera]
              unfold mag
              split <;> omega
      | succ k => simp [en_frontera] at hs

theorem deriva_frontera (hθ1 : 1≤θ) (hθ : θ^(V+3)≤4-2*θ) (hUV : U≤(2:ℝ)^V)
    (hCU : 9*U≤(C:ℝ)) (s : EstadoHueco) (hs : en_frontera s.1.1) :
    θ*((contribucion C U θ V s false+contribucion C U θ V s true)/2)≤peso θ V s.1.1 := by
  have hθ0 : 0≤θ := by linarith
  have cf := contribucion_cota C U θ V hθ1 s false
  have ct := contribucion_cota C U θ V hθ1 s true
  rcases hz : s.1.1 with _ | ⟨k,c⟩
  · rw [hz] at hs; simp [en_frontera] at hs
  · rw [hz] at hs cf ct
    cases k with
    | zero =>
      have hc0 : c≠0 := hs
      by_cases hc : c%2=0
      · rw [paso_cero_par c hc] at cf ct
        simp only [Bool.false_eq_true,if_false,if_true,peso] at cf ct
        rw [dos_adica_mitad c hc0 hc] at cf
        rw [dos_adica_tres_mitad c hc0 hc] at ct
        simp only [peso]
        have hp : θ*θ^(dos_adica c)=θ^(dos_adica c+1) := by ring
        nlinarith [cf.1,cf.2,ct.1,ct.2]
      · rw [paso_cero_impar c hc] at cf ct
        have hf := peso_uno_cota θ V hθ1 hθ ((3*c+1)/2)
        have ht := peso_uno_cota θ V hθ1 hθ ((1-3*c)/2)
        simp only [Bool.false_eq_true,if_false,if_true] at cf ct
        simp only [peso,dos_adica_impar c hc,Nat.zero_add,pow_one]
        nlinarith [cf.1,cf.2,ct.1,ct.2]
    | succ k =>
      cases k with
      | zero =>
        by_cases hc : c%2=0
        · rw [paso_uno_par c hc] at cf ct
          simp only [Bool.false_eq_true,if_false,if_true,peso] at cf ct
          simp only [peso,hc,if_true]
          have hA : θ*θ^(V+2)=θ^(V+3) := by ring
          by_cases hm : (c/2)%2=0
          · have hm2 : ¬((3*c+1-3)/2)%2=0 := by omega
            rw [if_pos hm] at cf
            rw [if_neg hm2] at ct
            nlinarith [cf.1,cf.2,ct.1,ct.2]
          · have hm2 : ((3*c+1-3)/2)%2=0 := by omega
            rw [if_neg hm] at cf
            rw [if_pos hm2] at ct
            nlinarith [cf.1,cf.2,ct.1,ct.2]
        · have hcf0 : contribucion C U θ V s false=0 := by
            unfold contribucion
            rw [if_neg (entrada_sin_guardia C U hCU s c hz hc)]
          have hct : contribucion C U θ V s true≤2*θ^(V+1) := by
            unfold contribucion
            split
            · rename_i hcond
              rw [hz,paso_uno_impar_cierto c hc]
              by_cases h1 : c=1
              · simp [h1,peso]
                positivity
              · simp only [h1,if_false,peso]
                have ht := activo_tamano U s true hcond.2
                rw [hz,paso_uno_impar_cierto c hc,if_neg h1,tamano_vivo] at ht
                simp only [pow_zero,div_one] at ht
                have hg0 : mag ((c-1)/2)≠0 := by unfold mag; split <;> omega
                have hd := dos_adica_cota _ hg0
                have hle : (2:ℝ)^(dos_adica (mag ((c-1)/2)))≤(2:ℝ)^V := by linarith
                have hdV : dos_adica (mag ((c-1)/2))≤V :=
                  (pow_le_pow_iff_right₀ (by norm_num : (1:ℝ)<2)).mp hle
                have hpow : θ^(dos_adica (mag ((c-1)/2))+1)≤θ^(V+1) :=
                  pow_le_pow_right₀ hθ1 (by omega)
                linarith
            · positivity
          rw [hcf0]
          simp only [peso,hc,if_false]
          have hA : θ*θ^(V+1)=θ^(V+2) := by ring
          nlinarith [ct.1]
      | succ k => simp [en_frontera] at hs

theorem riesgo_frontera (hθ1 : 1≤θ) (hθ : θ^(V+3)≤4-2*θ) (hUV : U≤(2:ℝ)^V)
    (hCU : 9*U≤(C:ℝ)) :
    ∀ (r : ℕ) (s : EstadoHueco), activo s=true → en_frontera s.1.1 →
      riesgo_hueco C U r s≤peso θ V s.1.1/θ^r := by
  have hθ0 : 0<θ := by linarith
  intro r
  induction r with
  | zero =>
    intro s ha hs
    simp only [riesgo_hueco,ha,if_true,pow_zero,div_one]
    exact peso_uno_minimo θ V hθ1 _ hs
  | succ r ih =>
    intro s ha hs
    have hpow : 0<θ^r := pow_pos hθ0 r
    have hrama : ∀ b, rama C U (riesgo_hueco C U r) s b≤contribucion C U θ V s b/θ^r := by
      intro b
      have hc := contribucion_cota C U θ V hθ1 s b
      unfold rama
      by_cases hg : guardia C (paso_hueco U s b).1=true
      · rw [if_pos hg]
        exact div_nonneg hc.1 (le_of_lt hpow)
      · have hgf : guardia C (paso_hueco U s b).1=false := by simpa using hg
        rw [if_neg hg]
        by_cases hab : activo (paso_hueco U s b)=true
        · have hfr := cierre_frontera C U s hs b ⟨hgf,hab⟩ hCU
          have hr := ih (paso_hueco U s b) hab hfr
          have hce : contribucion C U θ V s b=peso θ V (paso s.1.1 b) := by
            unfold contribucion
            rw [if_pos ⟨hgf,hab⟩]
          rw [hce]
          exact hr
        · have hf : activo (paso_hueco U s b)=false := by simpa using hab
          rw [riesgo_inactivo C U r _ hf]
          exact div_nonneg hc.1 (le_of_lt hpow)
    have hd := deriva_frontera C U θ V hθ1 hθ hUV hCU s hs
    have h0 := hrama false
    have h1 := hrama true
    simp only [riesgo_hueco,ha,if_true]
    rw [pow_succ]
    have hsum : (rama C U (riesgo_hueco C U r) s false+rama C U (riesgo_hueco C U r) s true)/2≤
        ((contribucion C U θ V s false+contribucion C U θ V s true)/2)/θ^r := by
      have : (contribucion C U θ V s false+contribucion C U θ V s true)/2/θ^r=
          (contribucion C U θ V s false/θ^r+contribucion C U θ V s true/θ^r)/2 := by ring
      rw [this]
      linarith
    have hmid : ((contribucion C U θ V s false+contribucion C U θ V s true)/2)≤peso θ V s.1.1/θ := by
      rw [le_div_iff₀ (by linarith)]
      linarith
    calc
      _ ≤ ((contribucion C U θ V s false+contribucion C U θ V s true)/2)/θ^r := hsum
      _ ≤ (peso θ V s.1.1/θ)/θ^r := div_le_div_of_nonneg_right hmid (le_of_lt hpow)
      _ = peso θ V s.1.1/(θ^r*θ) := by rw [div_div,mul_comm]

/-- Frontera tras volver a k=1: riesgo de más de B pasos sin entrada. -/
theorem frontera_uno (hθ1 : 1≤θ) (hθ : θ^(V+3)≤4-2*θ) (hUV : U≤(2:ℝ)^V)
    (hCU : 9*U≤(C:ℝ)) (B : ℕ) :
    ∀ (n : ℕ) (s : EstadoHueco) (c : ℤ), B≤n → activo s=true → s.1.1=.vivo 1 c →
      riesgo_hueco C U n s≤2/θ^B := by
  intro n s c hn ha hs
  have hm := riesgo_antitono C U B (n-B) s
  rw [show B+(n-B)=n by omega] at hm
  have hf := riesgo_frontera C U θ V hθ1 hθ hUV hCU B s ha (by rw [hs]; trivial)
  have hp := peso_uno_cota θ V hθ1 hθ c
  rw [hs] at hf
  have hpos : 0<θ^B := pow_pos (by linarith) B
  calc
    _ ≤ peso θ V (.vivo 1 c)/θ^B := hm.trans hf
    _ ≤ 2/θ^B := div_le_div_of_nonneg_right hp (le_of_lt hpos)

/-- El primer hueco, desde (0,1). -/
theorem frontera_inicio (hθ1 : 1≤θ) (hθ : θ^(V+3)≤4-2*θ) (hUV : U≤(2:ℝ)^V)
    (hCU : 9*U≤(C:ℝ)) (B G : ℕ) (hG : B+1≤G) :
    riesgo_hueco C U G (inicio_ensayo,true)≤2/θ^B := by
  have hm := riesgo_antitono C U (B+1) (G-(B+1)) (inicio_ensayo,true)
  rw [show B+1+(G-(B+1))=G by omega] at hm
  have ha : activo (inicio_ensayo,true)=true := by simp [activo,inicio_ensayo,GuardiasGao.vivo]
  have hf := riesgo_frontera C U θ V hθ1 hθ hUV hCU (B+1) (inicio_ensayo,true) ha
    (by simp [inicio_ensayo,en_frontera])
  have hp : peso θ V (inicio_ensayo,true).1.1=2*θ := by
    simp [peso,inicio_ensayo,dos_adica]
  rw [hp] at hf
  have hθ0 : 0<θ := by linarith
  have he : 2*θ/θ^(B+1)=2/θ^B := by
    rw [pow_succ]
    field_simp
  linarith

end Frontera

/-! ## Ensamblaje abstracto -/

section Abstracto

variable (C : ℕ) (U : ℝ)

/-- Con cualquier cola de excursión ε y el potencial de frontera. -/
theorem pocas_entradas_abstracta (N h d B V : ℕ) (θ ε : ℝ) (hN : 1≤N)
    (hNG : N*(d+B+1)≤h) (hθ1 : 1≤θ) (hθ : θ^(V+3)≤4-2*θ) (hUV : U≤(2:ℝ)^V)
    (hCU : 9*U≤(C:ℝ)) (hsurv : ∀ c : ℤ, SupervivenciaGao.supervivencia d c≤ε) :
    media h (fun bs => RepeticionGao.indicador (GuardiasGao.vivo (recorre paso_ensayo bs inicio_ensayo) &&
      decide (ConteoEnsayosGao.cuenta paso_ensayo (guardia C) bs inicio_ensayo<N)))≤
      alcanza U h (.vivo 0 1)+((N:ℝ)-1)*(ε+2/θ^B)+2/θ^B := by
  have hθ0 : 0<θ := by linarith
  have hβ0 : 0≤2/θ^B := by positivity
  have hε0 : 0≤ε := by
    have h0 := hsurv 0
    have := (surv_cotas d (.vivo 2 0)).1
    unfold surv at this
    unfold SupervivenciaGao.supervivencia at h0
    linarith
  have hβ := frontera_uno C U θ V hθ1 hθ hUV hCU B
  have hq : ∀ s : EstadoHueco, activo s=true → guardia C s.1=true →
      riesgo_hueco C U (d+B+1) s≤ε+2/θ^B := by
    intro s ha hg
    obtain ⟨c,hc,_⟩ := guardia_estado C s.1 hg
    have hok : s.2=true := (Bool.and_eq_true_iff.mp ha).2
    have hs : s=((.vivo 2 c,s.1.2),true) := by
      rcases s with ⟨⟨z,f⟩,o⟩
      simp only at hc hok
      rw [hc,hok]
    rw [hs]
    have he := riesgo_entrada C U (2/θ^B) B d hβ0 hβ c s.1.2
    linarith [hsurv c]
  have hp := pocas_entradas C U N (d+B+1) h (ε+2/θ^B) (by positivity) hq hNG
  have hpot : potencial C U N (d+B+1) (ε+2/θ^B) inicio_aumentado≤
      ((N:ℝ)-1)*(ε+2/θ^B)+2/θ^B := by
    have hi := frontera_inicio C U θ V hθ1 hθ hUV hCU B (d+B+1) (by omega)
    have ha : activo (inicio_aumentado.z,inicio_aumentado.ok)=true := by
      simp [activo,inicio_aumentado,inicio_ensayo,GuardiasGao.vivo]
    have hcast : ((N-1-0:ℕ):ℝ)=(N:ℝ)-1 := by
      rw [Nat.sub_zero,Nat.cast_sub hN]
      simp
    unfold potencial
    rw [if_pos ⟨ha,by simp [inicio_aumentado]; omega⟩]
    simp only [inicio_aumentado,Nat.sub_zero] at hi ⊢
    rw [show ((N-1:ℕ):ℝ)=(N:ℝ)-1 by rw [Nat.cast_sub hN]; simp]
    linarith
  linarith

end Abstracto

/-! ## Parámetros de Lagartijas: N=2^m, h=N^6, C=9h^4 -/

section Parametros

theorem crecimiento (j : ℕ) : 64*((j+10)+1)≤2^(j+10) := by
  induction j with
  | zero => decide
  | succ j ih =>
    rw [show j+1+10=(j+10)+1 by omega,Nat.pow_succ]
    omega

theorem pow_uno_mas (x : ℝ) (k : ℕ) (hx : 0≤x) (hkx : (k:ℝ)*x≤1/4) : (1+x)^k≤4/3 := by
  rcases Nat.eq_zero_or_pos k with hk | hk
  · subst hk; norm_num
  · have hk1 : (1:ℝ)≤k := by exact_mod_cast hk
    have hx4 : x≤1/4 := by nlinarith
    have hb := one_add_mul_le_pow (a:=-x) (by linarith) k
    have hm : (1-x)^k≥3/4 := by
      have : (1+ -x)^k=(1-x)^k := by ring
      nlinarith
    have hprod : (1+x)^k*(1-x)^k≤1 := by
      rw [← mul_pow]
      apply pow_le_one₀
      · nlinarith
      · nlinarith
    have hpos : 0<(1-x)^k := by linarith
    have h1 : (1+x)^k≤1/(1-x)^k := by
      rw [le_div_iff₀ hpos]
      exact hprod
    have h2 : 1/(1-x)^k≤4/3 := by
      rw [div_le_iff₀ hpos]
      linarith
    linarith

theorem theta_deriva (V : ℕ) :
    (1+1/((4*(V+3):ℕ):ℝ))^(V+3)≤4-2*(1+1/((4*(V+3):ℕ):ℝ)) := by
  have hn : (12:ℝ)≤((4*(V+3):ℕ):ℝ) := by
    have : 12≤4*(V+3) := by omega
    exact_mod_cast this
  have hx : 0≤1/((4*(V+3):ℕ):ℝ) := by positivity
  have hx12 : 1/((4*(V+3):ℕ):ℝ)≤1/12 := by
    apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) hn
  have hkx : ((V+3:ℕ):ℝ)*(1/((4*(V+3):ℕ):ℝ))=1/4 := by
    push_cast
    field_simp
  have hp := pow_uno_mas (1/((4*(V+3):ℕ):ℝ)) (V+3) hx (le_of_eq hkx)
  linarith

theorem theta_potencia (n K : ℕ) (hn : 1≤n) :
    (2:ℝ)^K≤(1+1/(n:ℝ))^(n*K) := by
  have hn0 : (0:ℝ)<n := by exact_mod_cast hn
  have hb := one_add_mul_le_pow (a:=1/(n:ℝ)) (by
    have : 0≤1/(n:ℝ) := by positivity
    linarith) n
  have h2 : (2:ℝ)≤(1+1/(n:ℝ))^n := by
    have : (n:ℝ)*(1/(n:ℝ))=1 := by field_simp
    linarith
  rw [pow_mul]
  exact pow_le_pow_left₀ (by norm_num) h2 K

theorem log_cuarta (m : ℕ) (hm : 1≤m) : Nat.log 2 (2^(4*m)+2)=4*m := by
  apply Nat.log_eq_of_pow_le_of_lt_pow
  · omega
  · have h4 : 4≤2^(4*m) := by
      calc 4=2^2 := by norm_num
        _ ≤ 2^(4*m) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [pow_succ]
    omega

/-- H3 instanciada: excursiones de más de d=N^4(10m+3) pasos cuestan <=3/N^2. -/
theorem cola_parametros (m : ℕ) (hm : 1≤m) (c : ℤ) :
    SupervivenciaGao.supervivencia ((2^m)^4*(10*m+3)) c≤3/((2^m:ℕ):ℝ)^2 := by
  have ha : 2+Nat.log 2 ((2^m)^4+2)≤4*m+2 := by
    rw [← pow_mul,show m*4=4*m by ring,log_cuarta m hm]
    omega
  have hd : (2^m)^4*(10*m+3)=(2^m)^4*((4*m+2)+(6*m)+1) := by ring
  have h := RelojGao.cola_excursion ((2^m)^2) ((2^m)^4) (4*m+2) (6*m) c
    (Nat.one_le_pow _ _ (by positivity)) (Nat.one_le_pow _ _ (by positivity)) ha
  rw [← hd] at h
  have hN : (0:ℝ)<((2^m:ℕ):ℝ) := by positivity
  set N : ℝ := ((2^m:ℕ):ℝ) with hNdef
  have hL : (((2^m)^2:ℕ):ℝ)=N^2 := by rw [hNdef]; push_cast; ring
  have hn : (((2^m)^4:ℕ):ℝ)=N^4 := by rw [hNdef]; push_cast; ring
  have hs : (2:ℝ)^(6*m)=N^6 := by rw [hNdef]; push_cast; rw [← pow_mul]; ring_nf
  rw [hL,hn,hs] at h
  have h1 : (N^2-1)/N^4≤1/N^2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_pos hN 2,pow_pos hN 4]
  have h2 : N^4/N^6=1/N^2 := by field_simp
  have h3 : 1/N^2+1/N^2+1/N^2=3/N^2 := by ring
  linarith

theorem presupuesto_lagartijas (m : ℕ) (hm : 10≤m) :
    2^m*((2^m)^4*(10*m+3)+(96*m+12)*(19*m+3)+1)≤(2^m)^6 := by
  obtain ⟨j,rfl⟩ : ∃ j, m=j+10 := ⟨m-10,by omega⟩
  have hc := crecimiento j
  generalize hn : 2^(j+10)=n at hc ⊢
  generalize hk : j+10=k at hc ⊢
  have h1 : 4*(10*k+3)+4≤n := by omega
  have h2 : 4*((96*k+12)*(19*k+3)+1)≤8*(64*(k+1))^2 := by nlinarith
  have h3 : (64*(k+1))^2≤n^2 := Nat.pow_le_pow_left hc 2
  have hn8 : 8≤n := by omega
  have h4 : 8*n^2≤n^5 := by
    have h83 : 8≤n^3 := le_trans hn8 (Nat.le_self_pow (by norm_num) n)
    calc 8*n^2 ≤ n^3*n^2 := Nat.mul_le_mul_right _ h83
      _ = n^5 := by ring
  have h5 : n^4*(4*(10*k+3)+4)≤n^4*n := Nat.mul_le_mul_left _ h1
  have h6 : n^4*n=n^5 := by ring
  have e : n^4*(4*(10*k+3)+4)=4*(n^4*(10*k+3))+4*n^4 := by ring
  have hG : n^4*(10*k+3)+(96*k+12)*(19*k+3)+1≤n^5 := by omega
  calc n*(n^4*(10*k+3)+(96*k+12)*(19*k+3)+1) ≤ n*n^5 := Nat.mul_le_mul_left _ hG
    _ = n^6 := by ring

end Parametros

/-! ## Lagartijas y CF_F -/

section Final

/-- Lagartijas: con N=2^m, h=N^6 y C=9h^4, para m>=10,
    P(sigma>h y menos de N entradas admisibles) <= 3/N+66/h+1/(4h^3). -/
theorem lagartijas (m : ℕ) (hm : 10≤m) :
    media ((2^m)^6) (fun bs => RepeticionGao.indicador
      (GuardiasGao.vivo (recorre paso_ensayo bs inicio_ensayo) &&
        decide (ConteoEnsayosGao.cuenta paso_ensayo (guardia (9*((2^m)^6)^4)) bs inicio_ensayo<2^m)))≤
      3/((2^m:ℕ):ℝ)+66/(((2^m)^6:ℕ):ℝ)+1/(4*(((2^m)^6:ℕ):ℝ)^3) := by
  set N := 2^m with hNdef
  set h := N^6 with hhdef
  have hN1 : 1≤N := Nat.one_le_pow _ _ (by norm_num)
  have hh1 : 1≤h := Nat.one_le_pow _ _ (by omega)
  set V := 24*m with hV
  set θ : ℝ := 1+1/((4*(V+3):ℕ):ℝ) with hθdef
  set B := (4*(V+3))*(19*m+3) with hBdef
  have hθ1 : 1≤θ := by
    have : 0≤1/((4*(V+3):ℕ):ℝ) := by positivity
    linarith
  have hθ := theta_deriva V
  have hU : (((h:ℕ):ℝ))^4≤(2:ℝ)^V := by
    have e1 : ((h:ℕ):ℝ)=(2:ℝ)^(6*m) := by
      rw [hhdef,hNdef]; push_cast; rw [← pow_mul]; ring_nf
    rw [e1,← pow_mul,hV]
    apply le_of_eq
    ring_nf
  have hCU : 9*((h:ℕ):ℝ)^4≤((9*h^4:ℕ):ℝ) := by push_cast; rfl
  have hB : B=(96*m+12)*(19*m+3) := by rw [hBdef]; ring
  have hNG : N*((2^m)^4*(10*m+3)+B+1)≤h := by
    rw [hB]
    exact presupuesto_lagartijas m hm
  have hmain := pocas_entradas_abstracta (9*h^4) (((h:ℕ):ℝ)^4) N h ((2^m)^4*(10*m+3)) B V θ
    (3/((N:ℕ):ℝ)^2) hN1 hNG hθ1 hθ hU hCU (cola_parametros m (by omega))
  have hC1 := envolvente_cf h hh1
  -- frontera: N*2/θ^B <= 1/(4h^3)
  have hNr : (0:ℝ)<((N:ℕ):ℝ) := by positivity
  have hθB : (2:ℝ)^(19*m+3)≤θ^B := by
    have := theta_potencia (4*(V+3)) (19*m+3) (by omega)
    rw [hBdef]
    simpa [hθdef] using this
  have hβ : ((N:ℕ):ℝ)*(2/θ^B)≤1/(4*((h:ℕ):ℝ)^3) := by
    have hpos : (0:ℝ)<θ^B := by positivity
    have hN' : ((N:ℕ):ℝ)=(2:ℝ)^m := by rw [hNdef]; push_cast; ring
    have hh' : ((h:ℕ):ℝ)=(2:ℝ)^(6*m) := by rw [hhdef,hNdef]; push_cast; rw [← pow_mul]; ring_nf
    rw [hN',hh']
    rw [show (2:ℝ)^m*(2/θ^B)=2^(m+1)/θ^B by ring]
    rw [div_le_div_iff₀ hpos (by positivity)]
    have e : (2:ℝ)^(m+1)*(4*((2:ℝ)^(6*m))^3)=2^(19*m+3) := by
      rw [← pow_mul]
      have : (4:ℝ)=2^2 := by norm_num
      rw [this,← pow_add,← pow_add]
      ring_nf
    linarith
  have hexc : (((N:ℕ):ℝ)-1)*(3/((N:ℕ):ℝ)^2)≤3/((N:ℕ):ℝ) := by
    rw [div_eq_mul_inv,div_eq_mul_inv]
    have hinv : ((N:ℕ):ℝ)⁻¹*((N:ℕ):ℝ)=1 := inv_mul_cancel₀ (ne_of_gt hNr)
    have hi2 : (((N:ℕ):ℝ)^2)⁻¹=((N:ℕ):ℝ)⁻¹*((N:ℕ):ℝ)⁻¹ := by rw [sq,mul_inv]
    rw [hi2]
    have hi0 : 0≤((N:ℕ):ℝ)⁻¹ := by positivity
    nlinarith
  have hsplit : (((N:ℕ):ℝ)-1)*(3/((N:ℕ):ℝ)^2+2/θ^B)+2/θ^B=
      (((N:ℕ):ℝ)-1)*(3/((N:ℕ):ℝ)^2)+((N:ℕ):ℝ)*(2/θ^B) := by ring
  have hU4 : ((h:ℕ):ℝ)^4=((h:ℝ))^4 := rfl
  have hsame : alcanza (((h:ℕ):ℝ)^4) h (.vivo 0 1)≤66/((h:ℕ):ℝ) := hC1
  linarith [hmain,hsplit,hexc,hβ,hsame]

/-- CF_F formal: el protocolo guardado con J ensayos que caben en N entradas. -/
theorem cf_f (m : ℕ) (hm : 10≤m) (J : ℕ)
    (hJ : 1+J*(duracion (9*((2^m)^6)^4)+2)≤2^m) :
    1-EnsayoGao.probabilidad_fusion ((2^m)^6) (.vivo 0 1)≤
      3/((2^m:ℕ):ℝ)+66/(((2^m)^6:ℕ):ℝ)+1/(4*(((2^m)^6:ℕ):ℝ)^3)+
        (1-riesgo (9*((2^m)^6)^4))^J := by
  have hs := ConteoEnsayosGao.supervivencia_por_entradas (9*((2^m)^6)^4) J ((2^m)^6) inicio_ensayo
  have hp : ConteoEnsayosGao.probabilidad_pocas (9*((2^m)^6)^4) J ((2^m)^6) inicio_ensayo≤
      media ((2^m)^6) (fun bs => RepeticionGao.indicador
        (GuardiasGao.vivo (recorre paso_ensayo bs inicio_ensayo) &&
          decide (ConteoEnsayosGao.cuenta paso_ensayo (guardia (9*((2^m)^6)^4)) bs inicio_ensayo<2^m))) := by
    unfold ConteoEnsayosGao.probabilidad_pocas
    apply media_mono
    intro bs _
    unfold RepeticionGao.indicador
    by_cases hv : GuardiasGao.vivo (recorre paso_ensayo bs inicio_ensayo)=true
    · by_cases hc : ConteoEnsayosGao.cuenta paso_ensayo (guardia (9*((2^m)^6)^4)) bs inicio_ensayo<
          1+J*(duracion (9*((2^m)^6)^4)+2)
      · have hc2 : ConteoEnsayosGao.cuenta paso_ensayo (guardia (9*((2^m)^6)^4)) bs inicio_ensayo<2^m := by
          omega
        simp [hv,hc,hc2]
      · simp only [hv,hc,decide_false,Bool.and_false,Bool.true_and,Bool.false_eq_true,if_false]
        split <;> norm_num
    · have hvf : GuardiasGao.vivo (recorre paso_ensayo bs inicio_ensayo)=false := by simpa using hv
      simp [hvf]
  have hl := lagartijas m hm
  have hz : inicio_ensayo.1=Estado.vivo 0 1 := rfl
  rw [hz] at hs
  linarith

/-- El número de ensayos de CF_F cabe en N entradas. -/
theorem ensayos_caben (N W : ℕ) (hN : 1≤N) : 1+((N-1)/(W+2))*(W+2)≤N := by
  have := Nat.div_mul_le_self (N-1) (W+2)
  omega

end Final

#print axioms riesgo_antitono
#print axioms potencial_superarmonico
#print axioms objetivo_cruce
#print axioms reloj_determinista
#print axioms muchas_entradas
#print axioms pocas_entradas
#print axioms interior_hijo
#print axioms riesgo_excursion
#print axioms riesgo_entrada
#print axioms deriva_frontera
#print axioms riesgo_frontera
#print axioms frontera_uno
#print axioms frontera_inicio
#print axioms pocas_entradas_abstracta
#print axioms cola_parametros
#print axioms presupuesto_lagartijas
#print axioms lagartijas
#print axioms cf_f
#print axioms ensayos_caben

end LagartijasGao
