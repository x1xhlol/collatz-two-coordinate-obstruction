import Hormigas

/- Absorción a horizonte fijo después de una oportunidad de primera salida. -/

noncomputable section

namespace EnsayoGao

open CadenaCompletaGao MomentosGao RestoGao SupervivenciaGao
open PalabrasGao SalidaPalabrasGao VentanaGao ParametrosVentanaGao HormigasGao

def fusion (z : Estado) : ℝ := if z=.fusion then 1 else 0
def probabilidad_fusion (n : ℕ) (z : Estado) : ℝ := promedio paso fusion n z

theorem fusion_no_negativa (z : Estado) : 0≤fusion z := by unfold fusion; split <;> norm_num

theorem probabilidad_no_negativa (n : ℕ) (z : Estado) : 0≤probabilidad_fusion n z :=
  promedio_no_negativo paso fusion fusion_no_negativa n z

theorem fusion_absorbente (n : ℕ) : probabilidad_fusion n .fusion=1 := by
  induction n with
  | zero => simp [probabilidad_fusion,promedio,fusion]
  | succ n ih => simpa [probabilidad_fusion,promedio,paso] using ih

theorem palabra_piso (bs : List Bool) (n : ℕ) (z : Estado)
    (hl : bs.length≤n) (hf : recorre paso bs z=.fusion) :
    1/(2:ℝ)^bs.length ≤ probabilidad_fusion n z := by
  induction bs generalizing n z with
  | nil =>
    simp only [recorre] at hf
    subst z
    simp [fusion_absorbente]
  | cons b bs ih =>
    cases n with
    | zero => simp at hl
    | succ n =>
      have hi := ih n (paso z b) (by simp only [List.length_cons] at hl; omega) hf
      have h0 := probabilidad_no_negativa n (paso z false)
      have h1 := probabilidad_no_negativa n (paso z true)
      have hp : probabilidad_fusion (n+1) z=
          (probabilidad_fusion n (paso z false)+probabilidad_fusion n (paso z true))/2 := rfl
      rw [hp]
      simp only [List.length_cons,pow_succ]
      have he : 1/((2:ℝ)^bs.length*2)=(1/(2:ℝ)^bs.length)/2 := by ring
      rw [he]
      cases b <;> linarith

theorem palabra_piso_uniforme (bs : List Bool) (D n : ℕ) (z : Estado)
    (hl : bs.length≤D) (hn : D≤n) (hf : recorre paso bs z=.fusion) :
    1/(2:ℝ)^D ≤ probabilidad_fusion n z := by
  have hp : (2:ℝ)^bs.length≤(2:ℝ)^D := by
    exact_mod_cast (Nat.pow_le_pow_right (by decide : 0<2) hl)
  exact (one_div_le_one_div_of_le (by positivity) hp).trans
    (palabra_piso bs n z (hl.trans hn) hf)

def premio (G : ℕ) : Estado → ℝ
  | .vivo 1 c => if c.natAbs≤G then 1 else 0
  | _ => 0

theorem premio_no_negativo (G : ℕ) (z : Estado) : 0≤premio G z := by
  cases z with
  | fusion => simp [premio]
  | vivo k c => cases k with
    | zero => simp [premio]
    | succ k => cases k <;> simp [premio]; split <;> norm_num

theorem premio_piso (G D n : ℕ) (hD : 16*(Nat.clog 2 (G+2)+1)^2≤D) (hn : D≤n)
    (z : Estado) : (1/(2:ℝ)^D)*premio G z ≤ probabilidad_fusion n z := by
  cases z with
  | fusion => simpa [premio] using probabilidad_no_negativa n .fusion
  | vivo k c =>
    cases k with
    | zero => simpa [premio] using probabilidad_no_negativa n (.vivo 0 c)
    | succ k =>
      cases k with
      | succ k => simpa [premio] using probabilidad_no_negativa n (.vivo (k+2) c)
      | zero =>
        by_cases hc : c.natAbs≤G
        · simp only [premio,hc,if_true,mul_one]
          obtain ⟨bs,hl,hf⟩ := palabra_hormigas c
          exact palabra_piso_uniforme bs D n (.vivo 1 c)
            (hl.trans ((longitud_mono c G hc).trans hD)) hn hf
        · simpa [premio,hc] using probabilidad_no_negativa n (.vivo 1 c)

theorem promedio_quieto {S : Type} (p : S → Bool → S) (f : S → ℝ) (n : ℕ) (z : S)
    (hp : ∀ b, p z b=z) : promedio p f n z=f z := by
  induction n with
  | zero => rfl
  | succ n ih => simp [promedio,hp,ih]

theorem relevo (H G D : ℕ) (hD : 16*(Nat.clog 2 (G+2)+1)^2≤D) (z : Estado) :
    (1/(2:ℝ)^D)*promedio paso_excursion (premio G) H z ≤
      probabilidad_fusion (H+D) z := by
  induction H generalizing z with
  | zero => simpa [promedio] using premio_piso G D D hD le_rfl z
  | succ H ih =>
    by_cases hi : RestoGao.interior z=true
    · have h0 := ih (paso z false)
      have h1 := ih (paso z true)
      simp only [promedio,paso_excursion,hi,if_true,Nat.succ_add]
      change (1/(2:ℝ)^D)*((promedio paso_excursion (premio G) H (paso z false)+
        promedio paso_excursion (premio G) H (paso z true))/2) ≤
        (probabilidad_fusion (H+D) (paso z false)+probabilidad_fusion (H+D) (paso z true))/2
      linarith
    · have hq : ∀ b, paso_excursion z b=z := by intro b; simp [paso_excursion,hi]
      rw [promedio_quieto _ _ _ _ hq]
      exact premio_piso G D (H+1+D) hD (by omega) z

theorem salida_premio (T G : ℕ) (c : ℤ) (R : ℝ) (hG : 3*(R+1)≤(G:ℝ)) (bs : List Bool) :
    marca (salida_buena T c R bs) ≤ premio G (recorre paso_excursion bs (.vivo 2 c)) := by
  classical
  by_cases hs : salida_buena T c R bs
  · obtain ⟨pre,post,d,hbs,_,hi,he,hd⟩ := hs
    have hdn : d.natAbs≤G := by
      have hr : (d.natAbs:ℝ)≤(G:ℝ) := by simpa using hd.trans hG
      exact_mod_cast hr
    have hf : recorre paso_excursion bs (.vivo 2 c)=.vivo 1 d := by
      rw [hbs,recorre_append,recorre_prefijo pre _ hi,he,recorre_fuera _ _ (by rfl)]
    have hmarca : marca (salida_buena T c R bs)=1 := by
      apply if_pos
      exact ⟨pre,post,d,hbs,by assumption,hi,he,hd⟩
    rw [hmarca,hf]
    simp [premio,hdn]
  · simpa [marca,hs] using premio_no_negativo G (recorre paso_excursion bs (.vivo 2 c))

theorem salida_a_fusion (T H G D : ℕ) (c : ℤ) (R : ℝ)
    (hG : 3*(R+1)≤(G:ℝ)) (hD : 16*(Nat.clog 2 (G+2)+1)^2≤D) :
    (1/(2:ℝ)^D)*probabilidad_salida T H c R ≤ probabilidad_fusion (H+D) (.vivo 2 c) := by
  have hm := media_mono H _ _ (fun bs _ => salida_premio T G c R hG bs)
  rw [media_recorre] at hm
  exact (mul_le_mul_of_nonneg_left hm (by positivity)).trans (relevo H G D hD (.vivo 2 c))

def gap_salida (T : ℕ) : ℕ := 3*((128*(horizonte T+1)*(T+1))^2+1)
def duracion_palabra (T : ℕ) : ℕ := 16*(Nat.clog 2 (gap_salida T+2)+1)^2

theorem gap_radio (T : ℕ) :
    3*(radio (horizonte T) ((T:ℝ)+1)+1)=(gap_salida T:ℝ) := by
  simp [gap_salida,radio]

theorem ensayo_uniforme (C c : ℤ) (hc : |(c:ℝ)|≤|(C:ℝ)|) :
    (1/(2:ℝ)^(duracion_palabra (tiempo C)))/(4*((tiempo C:ℝ)+1)) ≤
      probabilidad_fusion (horizonte (tiempo C)+duracion_palabra (tiempo C)) (.vivo 2 c) := by
  have hv := ventana_uniforme C c hc
  have hf := salida_a_fusion (tiempo C) (horizonte (tiempo C)) (gap_salida (tiempo C))
    (duracion_palabra (tiempo C)) c (radio (horizonte (tiempo C)) ((tiempo C:ℝ)+1))
    (le_of_eq (gap_radio _)) le_rfl
  have hm := mul_le_mul_of_nonneg_left hv
    (by positivity : 0≤1/(2:ℝ)^(duracion_palabra (tiempo C)))
  calc
    _ = (1/(2:ℝ)^(duracion_palabra (tiempo C)))*(1/(4*((tiempo C:ℝ)+1))) := by ring
    _ ≤ _ := hm.trans hf

#print axioms palabra_piso_uniforme
#print axioms premio_piso
#print axioms relevo
#print axioms salida_premio
#print axioms salida_a_fusion
#print axioms ensayo_uniforme

end EnsayoGao
