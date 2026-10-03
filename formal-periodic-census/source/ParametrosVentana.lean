import Ventana

/- Parámetros enteros de VH; no se usan aproximaciones decimales. -/

noncomputable section

namespace ParametrosVentanaGao

open ProductoGao VentanaGao

set_option maxRecDepth 20000
set_option exponentiation.threshold 4096

theorem producto_base : 4*(1024+1)*61^1024 ≤ (62:ℕ)^1024 := by decide

theorem producto_entero (T : ℕ) (hT : 1024 ≤ T) :
    4*(T+1)*61^T ≤ 62^T := by
  induction T, hT using Nat.le_induction with
  | base => exact producto_base
  | succ T hT ih =>
    have hcoef : 61*(T+2) ≤ 62*(T+1) := by omega
    have h1 := Nat.mul_le_mul_left 62 ih
    have h2 := Nat.mul_le_mul_right (4*61^T) hcoef
    rw [pow_succ, pow_succ]
    nlinarith

theorem producto_cuarto (T : ℕ) (hT : 1024 ≤ T) :
    razon^T ≤ 1/(4*((T:ℝ)+1)) := by
  have h : 4*((T:ℝ)+1)*(61:ℝ)^T ≤ (62:ℝ)^T := by
    exact_mod_cast producto_entero T hT
  unfold razon
  rw [div_pow]
  apply (div_le_div_iff₀ (by positivity : (0:ℝ)<62^T)
    (by positivity : (0:ℝ)<4*((T:ℝ)+1))).2
  nlinarith

theorem contraccion_bloque : (rho^32*2:ℝ) ≤ 1 := by norm_num [rho]

theorem contraccion_entera (m T : ℕ) (c : ℤ) (hT : 32*m ≤ T)
    (hc : |(c:ℝ)| ≤ (2:ℝ)^m) : rho^T*|((c:ℝ)/9)| ≤ 1 := by
  have hpow : rho^T ≤ rho^(32*m) :=
    pow_le_pow_of_le_one (by norm_num [rho]) (by norm_num [rho]) hT
  have habs : |((c:ℝ)/9)| ≤ (2:ℝ)^m := by
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ)<9)]
    have hn := abs_nonneg (c:ℝ)
    linarith
  have hprod : rho^(32*m)*(2:ℝ)^m ≤ 1 := by
    rw [pow_mul, ← mul_pow]
    exact pow_le_one₀ (by norm_num [rho]) contraccion_bloque
  exact (mul_le_mul hpow habs (abs_nonneg _) (pow_nonneg (by norm_num [rho]) _)).trans hprod

def m_inicial (c : ℤ) : ℕ := Nat.clog 2 (2+c.natAbs)
def tiempo (c : ℤ) : ℕ := 32*max 32 (m_inicial c)
def techo (T : ℕ) : ℕ := 16*(T+1)
def cantidad (T : ℕ) : ℕ := (techo T)^2
def umbral (T : ℕ) : ℕ := 2+Nat.log 2 (cantidad T+2)
def margen (T : ℕ) : ℕ := 3*Nat.clog 2 (cantidad T+1)
def horizonte (T : ℕ) : ℕ := cantidad T*(umbral T+margen T+1)

theorem tiempo_minimo (c : ℤ) : 1024 ≤ tiempo c := by
  have h := le_max_left 32 (m_inicial c)
  unfold tiempo
  omega

theorem contraccion_inicial (c : ℤ) : rho^(tiempo c)*|((c:ℝ)/9)| ≤ 1 := by
  apply contraccion_entera (m_inicial c) (tiempo c) c
  · unfold tiempo
    exact Nat.mul_le_mul_left 32 (le_max_right _ _)
  · have h := Nat.le_pow_clog (by decide : 1<2) (2+c.natAbs)
    have hn : c.natAbs ≤ 2^(m_inicial c) := by unfold m_inicial; omega
    have hr : (c.natAbs:ℝ) ≤ (2:ℝ)^(m_inicial c) := by exact_mod_cast hn
    simpa using hr

theorem margen_cubo (n : ℕ) : n^3 ≤ 2^(3*Nat.clog 2 (n+1)) := by
  have h := Nat.le_pow_clog (by decide : 1<2) (n+1)
  have hp := Nat.pow_le_pow_left (show n ≤ 2^Nat.clog 2 (n+1) by omega) 3
  simpa only [← pow_mul, Nat.mul_comm] using hp

theorem coste_margen (n : ℕ) (hn : 1≤n) :
    (n:ℝ)/(2:ℝ)^(3*Nat.clog 2 (n+1)) ≤ 1/(n:ℝ)^2 := by
  have hd : (n:ℝ)^3 ≤ (2:ℝ)^(3*Nat.clog 2 (n+1)) := by exact_mod_cast margen_cubo n
  have hnR : (0:ℝ)<n := by exact_mod_cast (show 0<n by omega)
  apply (div_le_div_iff₀ (by positivity) (by positivity)).2
  nlinarith

theorem coste_reloj (T : ℕ) :
    1/(techo T:ℝ)+((techo T:ℝ)-1)/(cantidad T:ℝ)+
      (cantidad T:ℝ)/(2:ℝ)^(margen T) ≤ 1/(4*((T:ℝ)+1)) := by
  have hn : 1 ≤ cantidad T := by
    have hp : 0 < cantidad T := by unfold cantidad techo; positivity
    omega
  have hm := coste_margen (cantidad T) hn
  change (cantidad T:ℝ)/(2:ℝ)^(margen T) ≤ 1/(cantidad T:ℝ)^2 at hm
  have hQ : 0<(T:ℝ)+1 := by positivity
  have hbase : 1/(techo T:ℝ)+((techo T:ℝ)-1)/(cantidad T:ℝ)+
      1/(cantidad T:ℝ)^2 ≤ 1/(4*((T:ℝ)+1)) := by
    simp only [techo, cantidad, Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_ofNat, Nat.cast_pow]
    field_simp
    nlinarith [sq_nonneg (T:ℝ)]
  linarith

theorem horizonte_posterior (T : ℕ) : T ≤ horizonte T := by
  have hn : T ≤ cantidad T := by unfold cantidad techo; nlinarith
  have hh : cantidad T ≤ cantidad T*(umbral T+margen T+1) := by nlinarith
  exact hn.trans hh

theorem ventana_contraccion (T : ℕ) (c : ℤ) (hT : 1024≤T)
    (hc : rho^T*|((c:ℝ)/9)| ≤ 1) :
    1/(4*((T:ℝ)+1)) ≤ probabilidad_salida T (horizonte T) c
      (radio (horizonte T) ((T:ℝ)+1)) := by
  apply ventana_cuarto T (techo T) (cantidad T) (umbral T) (margen T) c
  · unfold techo; omega
  · have hp : 0 < cantidad T := by unfold cantidad techo; positivity
    omega
  · exact le_rfl
  · exact horizonte_posterior _
  · exact hc
  · exact coste_reloj _
  · exact producto_cuarto _ hT

theorem ventana_explicita (c : ℤ) :
    1/(4*((tiempo c:ℝ)+1)) ≤ probabilidad_salida (tiempo c) (horizonte (tiempo c)) c
      (radio (horizonte (tiempo c)) ((tiempo c:ℝ)+1)) :=
  ventana_contraccion _ c (tiempo_minimo c) (contraccion_inicial c)

/- Los ensayos pueden fijar sus parámetros con una cota C conocida al inicio. -/
theorem ventana_uniforme (C c : ℤ) (hc : |(c:ℝ)| ≤ |(C:ℝ)|) :
    1/(4*((tiempo C:ℝ)+1)) ≤ probabilidad_salida (tiempo C) (horizonte (tiempo C)) c
      (radio (horizonte (tiempo C)) ((tiempo C:ℝ)+1)) := by
  apply ventana_contraccion _ c (tiempo_minimo C)
  have hdiv : |((c:ℝ)/9)| ≤ |((C:ℝ)/9)| := by
    rw [abs_div, abs_div]
    exact div_le_div_of_nonneg_right hc (abs_nonneg _)
  exact (mul_le_mul_of_nonneg_left hdiv (pow_nonneg (by norm_num [rho]) _)).trans
    (contraccion_inicial C)

#print axioms producto_entero
#print axioms producto_cuarto
#print axioms contraccion_inicial
#print axioms coste_reloj
#print axioms horizonte_posterior
#print axioms ventana_explicita
#print axioms ventana_uniforme

end ParametrosVentanaGao
