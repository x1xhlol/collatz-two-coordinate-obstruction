import Lagartijas

/- Martas: el lado derecho de CF_F tiende a cero. En consecuencia la cadena
   original desde (0,1) fusiona con probabilidad que tiende a 1 cuando el
   horizonte crece. Cotas de los parámetros de EF por potencias de dos. -/

noncomputable section

namespace MartasGao

open CadenaCompletaGao MomentosGao ParametrosVentanaGao EnsayoGao GuardiasGao LagartijasGao

/-! ## Parámetros de EF acotados por potencias de dos -/

theorem lineal_potencia (L : ℕ) : 8*L+46≤2^(L+6) := by
  induction L with
  | zero => norm_num
  | succ L ih => rw [show L+1+6=(L+6)+1 by ring,pow_succ]; omega

theorem cuadratica_potencia (L : ℕ) : 16*(8*L+53)^2+2≤2^(3*L+16) := by
  induction L with
  | zero => norm_num
  | succ L ih =>
    have hp : 16*(8*(L+1)+53)^2+2≤8*(16*(8*L+53)^2+2) := by ring_nf; nlinarith
    calc 16*(8*(L+1)+53)^2+2 ≤ 8*(16*(8*L+53)^2+2) := hp
      _ ≤ 8*2^(3*L+16) := by omega
      _ = 2^(3*(L+1)+16) := by rw [show 3*(L+1)+16=(3*L+16)+3 by ring,pow_add]; ring

theorem cantidad_cota (T L : ℕ) (hT : T+1≤2^(L+1)) : cantidad T≤2^(2*L+10) := by
  unfold cantidad techo
  have h : 16*(T+1)≤2^(L+5) := by
    have e : 2^(L+5)=16*2^(L+1) := by rw [show L+5=(L+1)+4 by ring,pow_add]; ring
    omega
  calc (16*(T+1))^2 ≤ (2^(L+5))^2 := Nat.pow_le_pow_left h 2
    _ = 2^(2*L+10) := by rw [← pow_mul]; congr 1; ring

theorem umbral_cota (T L : ℕ) (hT : T+1≤2^(L+1)) : umbral T≤2*L+12 := by
  unfold umbral
  have hc := cantidad_cota T L hT
  have hlt : cantidad T+2<2^(2*L+11) := by
    have e : 2^(2*L+11)=2*2^(2*L+10) := by rw [show 2*L+11=(2*L+10)+1 by ring,pow_succ]; ring
    have h2 : 4≤2^(2*L+10) := by
      calc 4=2^2 := by norm_num
        _ ≤ 2^(2*L+10) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hlog := Nat.log_lt_of_lt_pow (by omega) hlt
  omega

theorem margen_cota (T L : ℕ) (hT : T+1≤2^(L+1)) : margen T≤6*L+33 := by
  unfold margen
  have hc := cantidad_cota T L hT
  have hle : cantidad T+1≤2^(2*L+11) := by
    have e : 2^(2*L+11)=2*2^(2*L+10) := by rw [show 2*L+11=(2*L+10)+1 by ring,pow_succ]; ring
    have h1 : 1≤2^(2*L+10) := Nat.one_le_two_pow
    omega
  have hclog := Nat.clog_le_of_le_pow hle
  omega

theorem horizonte_cota (T L : ℕ) (hT : T+1≤2^(L+1)) : horizonte T≤2^(3*L+16) := by
  unfold horizonte
  have hc := cantidad_cota T L hT
  have hu := umbral_cota T L hT
  have hm := margen_cota T L hT
  have hl := lineal_potencia L
  have hs : umbral T+margen T+1≤2^(L+6) := by omega
  calc cantidad T*(umbral T+margen T+1) ≤ 2^(2*L+10)*2^(L+6) := Nat.mul_le_mul hc hs
    _ = 2^(3*L+16) := by rw [← pow_add]; congr 1; ring

theorem palabra_cota (T L : ℕ) (hT : T+1≤2^(L+1)) : duracion_palabra T≤16*(8*L+53)^2 := by
  unfold duracion_palabra gap_salida
  have hH := horizonte_cota T L hT
  have hH1 : horizonte T+1≤2^(3*L+17) := by
    have e : 2^(3*L+17)=2*2^(3*L+16) := by rw [show 3*L+17=(3*L+16)+1 by ring,pow_succ]; ring
    have h1 : 1≤2^(3*L+16) := Nat.one_le_two_pow
    omega
  have hprod : 128*(horizonte T+1)*(T+1)≤2^(4*L+25) := by
    calc 128*(horizonte T+1)*(T+1) ≤ 128*2^(3*L+17)*2^(L+1) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ hH1) hT
      _ = 2^(4*L+25) := by
          rw [show (128:ℕ)=2^7 by norm_num,← pow_add,← pow_add]; congr 1; ring
  have hsq : (128*(horizonte T+1)*(T+1))^2≤2^(8*L+50) := by
    calc (128*(horizonte T+1)*(T+1))^2 ≤ (2^(4*L+25))^2 := Nat.pow_le_pow_left hprod 2
      _ = 2^(8*L+50) := by rw [← pow_mul]; congr 1; ring
  have hg : 3*((128*(horizonte T+1)*(T+1))^2+1)+2≤2^(8*L+52) := by
    have e : 2^(8*L+52)=4*2^(8*L+50) := by rw [show 8*L+52=(8*L+50)+2 by ring,pow_add]; ring
    have h5 : 5≤2^(8*L+50) := by
      calc 5≤2^3 := by norm_num
        _ ≤ 2^(8*L+50) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hclog := Nat.clog_le_of_le_pow hg
  have hb : Nat.clog 2 (3*((128*(horizonte T+1)*(T+1))^2+1)+2)+1≤8*L+53 := by omega
  have := Nat.pow_le_pow_left hb 2
  omega

theorem duracion_cota (T L : ℕ) (hT : T+1≤2^(L+1)) :
    horizonte T+duracion_palabra T+2≤2^(3*L+17) := by
  have hH := horizonte_cota T L hT
  have hD := palabra_cota T L hT
  have hq := cuadratica_potencia L
  have e : 2^(3*L+17)=2*2^(3*L+16) := by rw [show 3*L+17=(3*L+16)+1 by ring,pow_succ]; ring
  omega

/-! ## El tiempo de la ventana para C_m=9h^4 -/

def cota_m (m : ℕ) : ℕ := 9*((2^m)^6)^4

theorem tiempo_cota (m : ℕ) (hm : 1≤m) : tiempo ((cota_m m:ℕ):ℤ)≤1024*m := by
  unfold tiempo m_inicial
  have hn : ((cota_m m:ℕ):ℤ).natAbs=cota_m m := Int.natAbs_natCast _
  rw [hn]
  have hp : cota_m m=9*2^(24*m) := by
    unfold cota_m
    rw [← pow_mul,← pow_mul]
    congr 2
    ring
  have hle : 2+cota_m m≤2^(24*m+4) := by
    rw [hp,pow_add]
    have : 1≤2^(24*m) := Nat.one_le_two_pow
    omega
  have hc := Nat.clog_le_of_le_pow hle
  rcases le_total 32 (Nat.clog 2 (2+cota_m m)) with h | h
  · rw [max_eq_right h]; omega
  · rw [max_eq_left h]; omega

/-! ## Número de ensayos y riesgo -/

theorem riesgo_forma (C : ℕ) :
    riesgo C=(1/(2:ℝ)^(duracion_palabra (tiempo (C:ℤ))))/(4*((tiempo (C:ℤ):ℝ)+1)) := rfl

theorem riesgo_cota_general (T D L Dm : ℕ) (hD : D≤Dm) (hT : 4*(T+1)≤2^(L+3)) :
    (1:ℝ)/2^(Dm+(L+3))≤(1/(2:ℝ)^D)/(4*((T:ℝ)+1)) := by
  have hT4 : 4*((T:ℝ)+1)≤(2:ℝ)^(L+3) := by exact_mod_cast hT
  have hD2 : (2:ℝ)^D≤(2:ℝ)^Dm := pow_le_pow_right₀ (by norm_num) hD
  rw [div_div,pow_add]
  apply one_div_le_one_div_of_le (by positivity)
  exact mul_le_mul hD2 hT4 (by positivity) (by positivity)

theorem complemento_potencia (p : ℝ) (J : ℕ) (hp0 : 0≤p) (hp1 : p≤1) :
    (1-p)^J≤1/(1+J*p) := by
  have hb := one_add_mul_le_pow (a:=p) (by linarith) J
  have hprod : (1-p)^J*(1+p)^J≤1 := by
    rw [← mul_pow]
    apply pow_le_one₀
    · nlinarith
    · nlinarith
  have hpos : 0<(1+p)^J := pow_pos (by linarith) J
  have hq : 0<1+(J:ℝ)*p := by positivity
  have h1 : (1-p)^J≤1/(1+p)^J := by
    rw [le_div_iff₀ hpos]; exact hprod
  have h2 : 1/(1+p)^J≤1/(1+(J:ℝ)*p) := one_div_le_one_div_of_le hq hb
  linarith

theorem ensayos_grandes (K m : ℕ) (hm : 10≤m)
    (hbig : K+4*Nat.log 2 m+62+16*(8*Nat.log 2 m+133)^2≤m) :
    (2:ℝ)^K≤((((2^m-1)/(duracion (cota_m m)+2):ℕ)):ℝ)*riesgo (cota_m m) := by
  set T := tiempo ((cota_m m:ℕ):ℤ) with hTdef
  set ℓ := Nat.log 2 m with hℓ
  set L := Nat.log 2 T with hLdef
  have hT1024 : 1024≤T := tiempo_minimo _
  have hTm := tiempo_cota m (by omega)
  have hTL : T+1≤2^(L+1) := Nat.lt_pow_succ_log_self (by norm_num) T
  have hmℓ : m<2^(ℓ+1) := Nat.lt_pow_succ_log_self (by norm_num) m
  have hLℓ : L≤ℓ+10 := by
    have hlt : T<2^(ℓ+11) := by
      have e : 2^(ℓ+11)=1024*2^(ℓ+1) := by rw [show ℓ+11=(ℓ+1)+10 by ring,pow_add]; ring
      omega
    have := Nat.log_lt_of_lt_pow (by omega) hlt
    omega
  set W := duracion (cota_m m) with hWdef
  have hW : W+2≤2^(3*L+17) := by
    have := duracion_cota T L hTL
    simp only [hWdef,duracion]
    rw [← hTdef]
    omega
  set D := duracion_palabra T with hDdef
  have hD : D≤16*(8*L+53)^2 := palabra_cota T L hTL
  have hDℓ : 16*(8*L+53)^2≤16*(8*ℓ+133)^2 := by
    have : 8*L+53≤8*ℓ+133 := by omega
    have := Nat.pow_le_pow_left this 2
    omega
  -- número de ensayos
  set J := (2^m-1)/(W+2) with hJdef
  have hmL : 3*L+18≤m := by nlinarith
  have hJ : 2^(m-(3*L+18))≤J := by
    have hdm := Nat.div_add_mod (2^m-1) (W+2)
    have hmod := Nat.mod_lt (2^m-1) (show 0<W+2 by omega)
    rw [← hJdef] at hdm
    have hone : 1≤2^m := Nat.one_le_two_pow
    have h1 : 2^m≤(W+2)*(J+1) := by rw [Nat.mul_succ]; omega
    have h2 : (W+2)*(J+1)≤2^(3*L+17)*(J+1) := Nat.mul_le_mul_right _ hW
    have h3 : 2^(3*L+17)*(2*2^(m-(3*L+18)))=2^m := by
      rw [show 2^m=2^(3*L+18)*2^(m-(3*L+18)) by rw [← pow_add]; congr 1; omega,
        show 3*L+18=(3*L+17)+1 by ring,pow_succ]
      ring
    have h4 : 2*2^(m-(3*L+18))≤J+1 :=
      Nat.le_of_mul_le_mul_left (by rw [h3]; exact h1.trans h2) (by positivity)
    have h5 : 1≤2^(m-(3*L+18)) := Nat.one_le_two_pow
    omega
  -- riesgo
  have hT4 : 4*(T+1)≤2^(L+3) := by
    have e : 2^(L+3)=4*2^(L+1) := by rw [show L+3=(L+1)+2 by ring,pow_add]; ring
    omega
  have hp : (1:ℝ)/2^(16*(8*L+53)^2+(L+3))≤riesgo (cota_m m) := by
    rw [riesgo_forma]
    exact riesgo_cota_general T D L (16*(8*L+53)^2) hD hT4
  -- producto
  have hexp : K+(16*(8*L+53)^2+(L+3))≤m-(3*L+18) := by omega
  have hJr : (2:ℝ)^(m-(3*L+18))≤(J:ℝ) := by exact_mod_cast hJ
  have hpos : (0:ℝ)<2^(16*(8*L+53)^2+(L+3)) := by positivity
  calc (2:ℝ)^K = (2:ℝ)^(K+(16*(8*L+53)^2+(L+3)))*(1/2^(16*(8*L+53)^2+(L+3))) := by
        rw [pow_add]; field_simp
    _ ≤ (2:ℝ)^(m-(3*L+18))*(1/2^(16*(8*L+53)^2+(L+3))) := by
        apply mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hexp) (by positivity)
    _ ≤ (J:ℝ)*riesgo (cota_m m) :=
        mul_le_mul hJr hp (by positivity) (Nat.cast_nonneg J)

theorem cola_ensayos (K m : ℕ) (hm : 10≤m)
    (hbig : K+4*Nat.log 2 m+62+16*(8*Nat.log 2 m+133)^2≤m) :
    (1-riesgo (cota_m m))^((2^m-1)/(duracion (cota_m m)+2))≤1/2^K := by
  have h := ensayos_grandes K m hm hbig
  have hc := complemento_potencia (riesgo (cota_m m)) ((2^m-1)/(duracion (cota_m m)+2))
    (riesgo_no_negativo _) (riesgo_menor_uno _)
  have hpos : (0:ℝ)<2^K := by positivity
  have h2 : 1/(1+(((2^m-1)/(duracion (cota_m m)+2):ℕ):ℝ)*riesgo (cota_m m))≤1/2^K :=
    one_div_le_one_div_of_le hpos (by linarith)
  linarith

/-! ## Crecimiento: existe m con la hipótesis de tamaño -/

theorem polilog (ℓ : ℕ) (hℓ : 22≤ℓ) : 2*(4*ℓ+62+16*(8*ℓ+133)^2)≤2^ℓ := by
  induction ℓ, hℓ using Nat.le_induction with
  | base => norm_num
  | succ ℓ hℓ ih =>
    have hp : 2*(4*(ℓ+1)+62+16*(8*(ℓ+1)+133)^2)≤2*(2*(4*ℓ+62+16*(8*ℓ+133)^2)) := by
      ring_nf; nlinarith
    calc 2*(4*(ℓ+1)+62+16*(8*(ℓ+1)+133)^2) ≤ 2*(2*(4*ℓ+62+16*(8*ℓ+133)^2)) := hp
      _ ≤ 2*2^ℓ := by omega
      _ = 2^(ℓ+1) := by rw [pow_succ]; ring

theorem existe_m (K : ℕ) : ∃ m, 10≤m ∧ K+3≤m ∧
    K+4*Nat.log 2 m+62+16*(8*Nat.log 2 m+133)^2≤m := by
  have hn22 : 22≤max 22 (K+2) := le_max_left _ _
  have hnK : K+2≤max 22 (K+2) := le_max_right _ _
  have hK2 : 2^(K+2)≤2^(max 22 (K+2)) := Nat.pow_le_pow_right (by norm_num) hnK
  have hKl : K+2<2^(K+2) := Nat.lt_two_pow_self
  refine ⟨2^(max 22 (K+2)),?_,?_,?_⟩
  · calc 10≤2^4 := by norm_num
      _ ≤ 2^(max 22 (K+2)) := Nat.pow_le_pow_right (by norm_num) (by omega)
  · omega
  · rw [Nat.log_pow (by norm_num)]
    have hp := polilog (max 22 (K+2)) hn22
    have hK : 2*K≤2^(max 22 (K+2)) := by
      have e : 2^(K+2)=4*2^K := by rw [pow_add]; ring
      have h2 := Nat.lt_two_pow_self (n:=K)
      omega
    omega

/-! ## Martas: la fusión es casi segura -/

theorem fusion_paso (n : ℕ) (z : Estado) :
    probabilidad_fusion n z≤probabilidad_fusion (n+1) z := by
  induction n generalizing z with
  | zero =>
    unfold probabilidad_fusion
    simp only [promedio]
    have h0 := fusion_no_negativa (paso z false)
    have h1 := fusion_no_negativa (paso z true)
    cases z with
    | fusion => simp [fusion,paso]
    | vivo k c =>
      have hz : fusion (Estado.vivo k c)=0 := by simp [fusion]
      rw [hz]
      linarith
  | succ n ih =>
    have h0 := ih (paso z false)
    have h1 := ih (paso z true)
    unfold probabilidad_fusion at h0 h1 ⊢
    show (promedio paso fusion n (paso z false)+promedio paso fusion n (paso z true))/2≤
      (promedio paso fusion (n+1) (paso z false)+promedio paso fusion (n+1) (paso z true))/2
    linarith

theorem fusion_monotona (h k : ℕ) (z : Estado) :
    probabilidad_fusion h z≤probabilidad_fusion (h+k) z := by
  induction k with
  | zero => simp
  | succ k ih => exact ih.trans (fusion_paso (h+k) z)

theorem martas (ε : ℝ) (hε : 0<ε) : ∃ h0 : ℕ, ∀ h, h0≤h →
    1-probabilidad_fusion h (.vivo 0 1)≤ε := by
  obtain ⟨K,hK⟩ : ∃ K : ℕ, 4/(2:ℝ)^K≤ε := by
    obtain ⟨K,hK⟩ := pow_unbounded_of_one_lt (4/ε) (by norm_num : (1:ℝ)<2)
    refine ⟨K,?_⟩
    rw [div_le_iff₀ (by positivity)]
    rw [div_lt_iff₀ hε] at hK
    linarith
  obtain ⟨m,hm10,hmK,hbig⟩ := existe_m K
  refine ⟨(2^m)^6,fun h hh => ?_⟩
  have hJ := ensayos_caben (2^m) (duracion (9*((2^m)^6)^4)) (Nat.one_le_two_pow)
  have hcf := cf_f m hm10 _ hJ
  have hcola := cola_ensayos K m hm10 hbig
  unfold cota_m at hcola
  have hmono := fusion_monotona ((2^m)^6) (h-(2^m)^6) (.vivo 0 1)
  rw [Nat.add_sub_cancel' hh] at hmono
  -- términos pequeños
  have hK0 : (0:ℝ)<2^K := by positivity
  have hN : (2:ℝ)^(K+3)≤((2^m:ℕ):ℝ) := by
    push_cast
    exact pow_le_pow_right₀ (by norm_num) hmK
  have hhK : (2:ℝ)^(K+7)≤(((2^m)^6:ℕ):ℝ) := by
    push_cast
    rw [← pow_mul]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have t1 : 3/((2^m:ℕ):ℝ)≤1/2^K := by
    rw [div_le_div_iff₀ (by positivity) hK0]
    have : (2:ℝ)^(K+3)=8*2^K := by rw [pow_add]; ring
    nlinarith
  have t2 : 66/(((2^m)^6:ℕ):ℝ)≤1/2^K := by
    rw [div_le_div_iff₀ (by positivity) hK0]
    have : (2:ℝ)^(K+7)=128*2^K := by rw [pow_add]; ring
    nlinarith
  have t3 : 1/(4*(((2^m)^6:ℕ):ℝ)^3)≤1/2^K := by
    apply one_div_le_one_div_of_le hK0
    have h1 : (1:ℝ)≤(((2^m)^6:ℕ):ℝ) := by exact_mod_cast Nat.one_le_pow _ _ (by positivity)
    have h2 : (2:ℝ)^K≤(((2^m)^6:ℕ):ℝ) := by
      refine le_trans ?_ hhK
      exact pow_le_pow_right₀ (by norm_num) (by omega)
    have h3 : (((2^m)^6:ℕ):ℝ)≤(((2^m)^6:ℕ):ℝ)^3 := by
      nlinarith [pow_le_pow_left₀ (by norm_num) h1 2]
    nlinarith
  have h4 : 4/(2:ℝ)^K=1/2^K+1/2^K+1/2^K+1/2^K := by ring
  linarith

end MartasGao

#print axioms MartasGao.duracion_cota
#print axioms MartasGao.tiempo_cota
#print axioms MartasGao.ensayos_grandes
#print axioms MartasGao.cola_ensayos
#print axioms MartasGao.existe_m
#print axioms MartasGao.fusion_monotona
#print axioms MartasGao.martas
