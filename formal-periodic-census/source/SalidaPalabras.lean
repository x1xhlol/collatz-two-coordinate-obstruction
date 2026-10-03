import Palabras

/- Primera salida como prefijo de la misma palabra de bits. -/

noncomputable section

namespace SalidaPalabrasGao

open CadenaCompletaGao RestoGao SupervivenciaGao PalabrasGao

theorem recorre_fuera (bs : List Bool) (z : Estado) (hz : RestoGao.interior z=false) :
    recorre paso_excursion bs z = z := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simpa [recorre, paso_excursion, hz] using ih

theorem recorre_prefijo (bs : List Bool) (z : Estado) (hi : prefijo_interior z bs) :
    recorre paso_excursion bs z = recorre paso bs z := by
  induction bs generalizing z with
  | nil => rfl
  | cons b bs ih => simpa [recorre, paso_excursion, hi.1] using ih (paso z b) hi.2

theorem hijo_salida (z : Estado) (b : Bool) (hz : RestoGao.interior z=true) :
    RestoGao.interior (paso z b)=true ∨ ∃ d, paso z b=.vivo 1 d := by
  cases z with
  | fusion => simp [RestoGao.interior] at hz
  | vivo k c =>
    cases k with
    | zero => simp [RestoGao.interior] at hz
    | succ k =>
      cases k with
      | zero => simp [RestoGao.interior] at hz
      | succ k => exact hijo_interior_o_salida k c b

theorem primera_salida (bs : List Bool) (z : Estado) (hz : RestoGao.interior z=true)
    (hs : RestoGao.interior (recorre paso_excursion bs z)=false) :
    ∃ pre post d, bs=pre++post ∧ pre≠[] ∧ prefijo_interior z pre ∧
      recorre paso pre z=.vivo 1 d := by
  induction bs generalizing z with
  | nil => simp [recorre, hz] at hs
  | cons b bs ih =>
    have hpaso : paso_excursion z b=paso z b := by simp [paso_excursion, hz]
    simp only [recorre, hpaso] at hs
    rcases hijo_salida z b hz with hi | ⟨d,hd⟩
    · obtain ⟨pre,post,d,hbs,_,hp,he⟩ := ih (paso z b) hi hs
      refine ⟨b::pre,post,d,?_,by simp,?_,?_⟩
      · simp [hbs]
      · exact ⟨hz,hp⟩
      · exact he
    · exact ⟨[b],bs,d,rfl,by simp,⟨hz,True.intro⟩,hd⟩

theorem supervivencia_prefijo (pre post : List Bool) (z : Estado) (d : ℤ) (T : ℕ)
    (hp : prefijo_interior z pre) (he : recorre paso pre z=.vivo 1 d)
    (hs : RestoGao.interior (recorre paso_excursion ((pre++post).take T) z)=true) :
    T < pre.length := by
  by_contra h
  have ht : pre.length ≤ T := by omega
  rw [List.take_append, List.take_of_length_le ht, recorre_append,
    recorre_prefijo pre z hp, he,
    recorre_fuera _ (.vivo 1 d) (by rfl)] at hs
  simp [RestoGao.interior] at hs

theorem producto_prefijo (T : ℕ) (pre post : List Bool) (ht : T ≤ pre.length)
    (hp : ¬cruce_producto T (pre++post)) :
    |recorre ProductoGao.paso_producto pre 1| ≤ 1 := by
  unfold cruce_producto at hp
  have he : (pre++post).take T = pre.take T := by
    rw [List.take_append]
    simp [show T-pre.length=0 by omega]
  have hd : (pre++post).drop T=pre.drop T++post := by
    rw [List.drop_append]
    simp [show T-pre.length=0 by omega]
  rw [he, hd] at hp
  -- El cruce controla también el último estado del prefijo.
  have h := cruza_prefijo ProductoGao.paso_producto abs 1 (pre.drop T) post
    (recorre ProductoGao.paso_producto (pre.take T) 1) hp
  rw [← recorre_append, List.take_append_drop] at h
  exact h

theorem termino_inicial (T : ℕ) (pre post : List Bool) (c : ℤ)
    (ht : T ≤ pre.length) (hp : ¬cruce_producto T (pre++post))
    (hc : ProductoGao.rho^T*|((c:ℝ)/9)| ≤ 1) :
    |(pre.map factor).prod*((c:ℝ)/9)| ≤ 1 := by
  have h := producto_prefijo T pre post ht hp
  rw [ProductoGao.producto_palabra] at h
  simp only [mul_one, abs_div, abs_of_nonneg (pow_nonneg
    (by norm_num [ProductoGao.rho] : (0:ℝ) ≤ ProductoGao.rho) _)] at h
  have hp0 : 0 < ProductoGao.rho^pre.length := pow_pos (by norm_num [ProductoGao.rho]) _
  have hprod : |(pre.map factor).prod| ≤ ProductoGao.rho^pre.length := by
    have hh := (div_le_iff₀ hp0).1 h
    simpa using hh
  have hpot : ProductoGao.rho^pre.length ≤ ProductoGao.rho^T :=
    pow_le_pow_of_le_one (by norm_num [ProductoGao.rho]) (by norm_num [ProductoGao.rho]) ht
  rw [abs_mul]
  exact (mul_le_mul_of_nonneg_right (hprod.trans hpot) (abs_nonneg _)).trans hc

def salida_buena (T : ℕ) (c : ℤ) (R : ℝ) (bs : List Bool) : Prop :=
  ∃ pre post d, bs=pre++post ∧ T<pre.length ∧
    prefijo_interior (.vivo 2 c) pre ∧ recorre paso pre (.vivo 2 c)=.vivo 1 d ∧
    |(d:ℝ)| ≤ 3*(R+1)

theorem salida_de_controles (T : ℕ) (c : ℤ) (R : ℝ) (bs : List Bool)
    (hi : RestoGao.interior (recorre paso_excursion (bs.take T) (.vivo 2 c))=true)
    (hs : RestoGao.interior (recorre paso_excursion bs (.vivo 2 c))=false)
    (hp : ¬cruce_producto T bs)
    (hw : ¬cruza paso_w (fun z => |z.resto|) R bs (RestoGao.inicial c))
    (hc : ProductoGao.rho^T*|((c:ℝ)/9)| ≤ 1) : salida_buena T c R bs := by
  obtain ⟨pre,post,d,hbs,_,hpre,he⟩ := primera_salida bs (.vivo 2 c) rfl hs
  rw [hbs] at hi hp hw
  have ht := supervivencia_prefijo pre post (.vivo 2 c) d T hpre he hi
  have hprod := termino_inicial T pre post c (by omega) hp hc
  have hresto := cruza_prefijo paso_w (fun z => |z.resto|) R pre post (RestoGao.inicial c) hw
  exact ⟨pre,post,d,hbs,ht,hpre,he,salida_controlada pre c d R hpre he hprod hresto⟩

#print axioms primera_salida
#print axioms supervivencia_prefijo
#print axioms producto_prefijo
#print axioms termino_inicial
#print axioms salida_de_controles

end SalidaPalabrasGao
