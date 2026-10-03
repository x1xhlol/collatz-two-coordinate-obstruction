import SalidaPalabras

/- Ventana conjunta sobre una sola palabra; la resta no usa independencia. -/

noncomputable section
open Classical

namespace VentanaGao

open CadenaCompletaGao MomentosGao RestoGao SupervivenciaGao
open PalabrasGao SalidaPalabrasGao ProductoGao RelojGao

theorem resta_eventos (A B C D E : Prop) (h : A → ¬B → ¬C → ¬D → E) :
    marca A ≤ marca E+marca B+marca C+marca D := by
  by_cases ha : A <;> by_cases hb : B <;> by_cases hc : C <;>
    by_cases hd : D <;> by_cases he : E <;> norm_num [marca, ha, hb, hc, hd, he] at *

theorem marca_interior (z : Estado) : marca (RestoGao.interior z=true)=vivo z := by
  cases he : RestoGao.interior z <;> simp [marca, vivo, he]

def probabilidad_salida (T H : ℕ) (c : ℤ) (R : ℝ) : ℝ :=
  media H (fun bs => marca (salida_buena T c R bs))

theorem ventana_union (T D : ℕ) (c : ℤ) (R : ℝ)
    (hc : rho^T*|((c:ℝ)/9)| ≤ 1) :
    supervivencia T c ≤ probabilidad_salida T (T+D) c R+
      supervivencia (T+D) c+cruce_desde T D+
      MaximosGao.cruce paso_w (fun z => |z.resto|) R (T+D) (RestoGao.inicial c) := by
  have hp : ∀ bs : List Bool,
      vivo (recorre paso_excursion (bs.take T) (.vivo 2 c)) ≤
        marca (salida_buena T c R bs)+vivo (recorre paso_excursion bs (.vivo 2 c))+
        marca (cruce_producto T bs)+
        marca (cruza paso_w (fun z => |z.resto|) R bs (RestoGao.inicial c)) := by
    intro bs
    have h := resta_eventos
      (RestoGao.interior (recorre paso_excursion (bs.take T) (.vivo 2 c))=true)
      (RestoGao.interior (recorre paso_excursion bs (.vivo 2 c))=true)
      (cruce_producto T bs)
      (cruza paso_w (fun z => |z.resto|) R bs (RestoGao.inicial c))
      (salida_buena T c R bs) (by
        intro hi hs hp hw
        have hs' : RestoGao.interior (recorre paso_excursion bs (.vivo 2 c))=false := by
          cases he : RestoGao.interior (recorre paso_excursion bs (.vivo 2 c)) <;> simp_all
        exact salida_de_controles T c R bs hi hs' hp hw hc)
    rw [marca_interior, marca_interior] at h
    exact h
  have hm := media_mono (T+D) _ _ (fun bs _ => hp bs)
  rw [media_take T D (fun bs => vivo (recorre paso_excursion bs (.vivo 2 c))),
    media_recorre, media_suma, media_suma, media_suma,
    media_recorre, media_producto, media_cruza] at hm
  exact hm

def radio (H : ℕ) (Q : ℝ) : ℝ := (128*((H:ℝ)+1)*Q)^2

theorem ventana_cota (T H : ℕ) (c : ℤ) (Q : ℝ) (hTH : T ≤ H) (hQ : 0<Q)
    (hc : rho^T*|((c:ℝ)/9)| ≤ 1) :
    1/((T:ℝ)+1)-supervivencia H c-razon^T-1/(4*Q) ≤
      probabilidad_salida T H c (radio H Q) := by
  have hu := ventana_union T (H-T) c (radio H Q) hc
  have he : T+(H-T)=H := by omega
  rw [he] at hu
  have hs := supervivencia_armonica T c
  have hp := producto_desde T (H-T)
  have hw := coste_resto_ventana H c Q hQ
  change MaximosGao.cruce paso_w (fun z => |z.resto|) (radio H Q) H
    (RestoGao.inicial c) ≤ 1/(4*Q) at hw
  linarith

theorem ventana_reloj (T L n a s : ℕ) (c : ℤ) (hL : 1≤L) (hn : 1≤n)
    (ha : 2+Nat.log 2 (n+2) ≤ a) (hTH : T ≤ n*(a+s+1))
    (hc : rho^T*|((c:ℝ)/9)| ≤ 1) :
    1/((T:ℝ)+1)-(1/(L:ℝ)+((L:ℝ)-1)/(n:ℝ)+(n:ℝ)/(2:ℝ)^s)-razon^T-
      1/(4*((T:ℝ)+1)) ≤
      probabilidad_salida T (n*(a+s+1)) c (radio (n*(a+s+1)) ((T:ℝ)+1)) := by
  have hv := ventana_cota T (n*(a+s+1)) c ((T:ℝ)+1) hTH (by positivity) hc
  have hr := cola_excursion L n a s c hL hn ha
  linarith

theorem ventana_cuarto (T L n a s : ℕ) (c : ℤ) (hL : 1≤L) (hn : 1≤n)
    (ha : 2+Nat.log 2 (n+2) ≤ a) (hTH : T ≤ n*(a+s+1))
    (hc : rho^T*|((c:ℝ)/9)| ≤ 1)
    (hr : 1/(L:ℝ)+((L:ℝ)-1)/(n:ℝ)+(n:ℝ)/(2:ℝ)^s ≤ 1/(4*((T:ℝ)+1)))
    (hp : razon^T ≤ 1/(4*((T:ℝ)+1))) :
    1/(4*((T:ℝ)+1)) ≤
      probabilidad_salida T (n*(a+s+1)) c (radio (n*(a+s+1)) ((T:ℝ)+1)) := by
  have h := ventana_reloj T L n a s c hL hn ha hTH hc
  have he : 1/((T:ℝ)+1)=4*(1/(4*((T:ℝ)+1))) := by field_simp
  linarith

#print axioms resta_eventos
#print axioms ventana_union
#print axioms ventana_cota
#print axioms ventana_reloj
#print axioms ventana_cuarto

end VentanaGao
