import Supervivencia

/- Excursión detenida al alcanzar altura 0 o L. Se controla el número
   de pasos mixtos, no el tiempo físico que incluye pasos compartidos. -/

noncomputable section

namespace BandaGao

open CadenaCompletaGao MomentosGao RestoGao SupervivenciaGao

def mixto : Estado → ℕ
  | .vivo (_+2) c => if c%2=0 then 0 else 1
  | _ => 0

theorem altura_segundo_momento (z : Estado) :
    (altura (paso_excursion z false)^2+altura (paso_excursion z true)^2)/2 =
      altura z^2+(mixto z:ℝ) := by
  cases z with
  | fusion => simp [paso_excursion, RestoGao.interior, altura, mixto]
  | vivo k c =>
    cases k with
    | zero => simp [paso_excursion, RestoGao.interior, altura, mixto]
    | succ k =>
      cases k with
      | zero => simp [paso_excursion, RestoGao.interior, altura, mixto]
      | succ k =>
        by_cases hc : c%2=0
        · simp [paso_excursion, RestoGao.interior, paso, altura, mixto, hc]
        · simp [paso_excursion, RestoGao.interior, paso, altura, mixto, hc]
          ring

def paso_banda (L : ℕ) (z : Estado) (b : Bool) : Estado :=
  if altura z < (L:ℝ) then paso_excursion z b else z

def altura_banda (L : ℕ) (z : Estado) : ℝ := min (altura z) (L:ℝ)

def mixto_banda (L : ℕ) (z : Estado) : ℕ :=
  if altura z < (L:ℝ) then mixto z else 0

def energia (L : ℕ) (z : Estado) : ℝ := altura_banda L z*((L:ℝ)-altura_banda L z)

theorem altura_entera (z : Estado) : ∃ n : ℕ, altura z=(n:ℝ) := by
  cases z with
  | fusion => exact ⟨0,by simp [altura]⟩
  | vivo k c => exact ⟨k-1,rfl⟩

theorem altura_abierta (L : ℕ) (z : Estado) (hz : altura z < (L:ℝ)) :
    altura z+1 ≤ (L:ℝ) := by
  obtain ⟨n,hn⟩ := altura_entera z
  rw [hn] at hz ⊢
  have hnL : n<L := by exact_mod_cast hz
  exact_mod_cast Nat.add_one_le_iff.mpr hnL

theorem altura_banda_no_negativa (L : ℕ) (z : Estado) : 0 ≤ altura_banda L z := by
  exact le_min (altura_no_negativa z) (by positivity)

theorem energia_no_negativa (L : ℕ) (z : Estado) : 0 ≤ energia L z := by
  exact mul_nonneg (altura_banda_no_negativa L z) (sub_nonneg.mpr (min_le_right _ _))

theorem altura_banda_armonica (L : ℕ) (z : Estado) :
    (altura_banda L (paso_banda L z false)+altura_banda L (paso_banda L z true))/2 =
      altura_banda L z := by
  by_cases hz : altura z < (L:ℝ)
  · have h0 := (altura_paso z false).trans (altura_abierta L z hz)
    have h1 := (altura_paso z true).trans (altura_abierta L z hz)
    simpa [paso_banda, hz, altura_banda, min_eq_left h0, min_eq_left h1,
      min_eq_left (le_of_lt hz)] using altura_armonica z
  · simp [paso_banda, hz]

theorem energia_deriva (L : ℕ) (z : Estado) :
    (energia L (paso_banda L z false)+energia L (paso_banda L z true))/2 =
      energia L z-(mixto_banda L z:ℝ) := by
  by_cases hz : altura z < (L:ℝ)
  · have h0 := (altura_paso z false).trans (altura_abierta L z hz)
    have h1 := (altura_paso z true).trans (altura_abierta L z hz)
    have he := altura_segundo_momento z
    have hh := congrArg (fun x : ℝ => (L:ℝ)*x) (altura_armonica z)
    simp only [paso_banda, hz, if_true, energia, altura_banda, mixto_banda,
      min_eq_left h0, min_eq_left h1, min_eq_left (le_of_lt hz)]
    nlinarith
  · simp [paso_banda, mixto_banda, hz]

theorem altura_banda_media (L n : ℕ) (z : Estado) :
    promedio (paso_banda L) (altura_banda L) n z = altura_banda L z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih => simp only [promedio, ih, altura_banda_armonica]

def cuenta_mixtos (L : ℕ) : ℕ → Estado → ℝ
  | 0, _ => 0
  | n+1, z => (mixto_banda L z:ℝ)+
      (cuenta_mixtos L n (paso_banda L z false)+cuenta_mixtos L n (paso_banda L z true))/2

theorem balance_energia (L n : ℕ) (z : Estado) :
    promedio (paso_banda L) (energia L) n z+cuenta_mixtos L n z = energia L z := by
  induction n generalizing z with
  | zero => simp [promedio, cuenta_mixtos]
  | succ n ih =>
    have h0 := ih (paso_banda L z false)
    have h1 := ih (paso_banda L z true)
    have hd := energia_deriva L z
    simp only [promedio, cuenta_mixtos]
    linarith

theorem cuenta_acotada (L n : ℕ) (c : ℤ) (hL : 1 ≤ L) :
    cuenta_mixtos L n (.vivo 2 c) ≤ (L:ℝ)-1 := by
  have he := balance_energia L n (.vivo 2 c)
  have hn := promedio_no_negativo (paso_banda L) (energia L) (energia_no_negativa L) n (.vivo 2 c)
  have hLr : (1:ℝ) ≤ L := by exact_mod_cast hL
  have hr : energia L (.vivo 2 c) = (L:ℝ)-1 := by
    norm_num [energia, altura_banda, altura, min_eq_left hLr]
  rw [hr] at he
  linarith

def toca_techo (L : ℕ) (z : Estado) : ℝ := if (L:ℝ) ≤ altura z then 1 else 0

theorem coste_techo (L n : ℕ) (c : ℤ) (hL : 1 ≤ L) :
    promedio (paso_banda L) (toca_techo L) n (.vivo 2 c) ≤ 1/(L:ℝ) := by
  have hp : ∀ z, (L:ℝ)*toca_techo L z ≤ altura_banda L z := by
    intro z
    by_cases hz : (L:ℝ) ≤ altura z
    · simp [toca_techo, hz, altura_banda]
    · simpa [toca_techo, hz] using altura_banda_no_negativa L z
  have h := promedio_mono (paso_banda L) _ _ hp n (.vivo 2 c)
  rw [promedio_escalar, altura_banda_media] at h
  have hLr : (1:ℝ) ≤ L := by exact_mod_cast hL
  have hr : altura_banda L (.vivo 2 c) = 1 := by
    norm_num [altura_banda, altura, min_eq_left hLr]
  rw [hr] at h
  apply (le_div_iff₀ (show (0:ℝ) < L by linarith)).2
  nlinarith

def paso_contador (L : ℕ) (s : Estado × ℕ) (b : Bool) : Estado × ℕ :=
  (paso_banda L s.1 b, s.2+mixto_banda L s.1)

theorem media_contador (L h : ℕ) (z : Estado) (j : ℕ) :
    promedio (paso_contador L) (fun s => (s.2:ℝ)) h (z,j) =
      (j:ℝ)+cuenta_mixtos L h z := by
  induction h generalizing z j with
  | zero => simp [promedio, cuenta_mixtos]
  | succ h ih =>
    simp only [promedio, paso_contador, ih, cuenta_mixtos, Nat.cast_add]
    ring

def supera_cuenta (n : ℕ) (s : Estado × ℕ) : ℝ := if n ≤ s.2 then 1 else 0

theorem coste_cuenta (L h n : ℕ) (c : ℤ) (hL : 1 ≤ L) (hn : 1 ≤ n) :
    promedio (paso_contador L) (supera_cuenta n) h (.vivo 2 c,0) ≤
      ((L:ℝ)-1)/(n:ℝ) := by
  have hp : ∀ s : Estado × ℕ, (n:ℝ)*supera_cuenta n s ≤ (s.2:ℝ) := by
    intro s
    by_cases hs : n ≤ s.2
    · simp only [supera_cuenta, hs, if_true, mul_one]
      exact_mod_cast hs
    · simp [supera_cuenta, hs]
  have hprom := promedio_mono (paso_contador L) _ _ hp h (.vivo 2 c,0)
  rw [promedio_escalar, media_contador] at hprom
  have hc := cuenta_acotada L h c hL
  have hnR : (0:ℝ) < n := by exact_mod_cast (show 0<n by omega)
  apply (le_div_iff₀ hnR).2
  norm_num at hprom
  nlinarith

theorem promedio_suma {S : Type} (p : S → Bool → S) (f g : S → ℝ)
    (h : ℕ) (s : S) : promedio p (fun z => f z+g z) h s =
      promedio p f h s+promedio p g h s := by
  induction h generalizing s with
  | zero => rfl
  | succ h ih => simp only [promedio, ih]; ring

theorem media_base (L h : ℕ) (f : Estado → ℝ) (z : Estado) (j : ℕ) :
    promedio (paso_contador L) (fun s => f s.1) h (z,j) =
      promedio (paso_banda L) f h z := by
  induction h generalizing z j with
  | zero => rfl
  | succ h ih => simp only [promedio, paso_contador, ih]

def malo_banda (L n : ℕ) (s : Estado × ℕ) : ℝ :=
  if (L:ℝ) ≤ altura s.1 ∨ n ≤ s.2 then 1 else 0

theorem coste_banda (L h n : ℕ) (c : ℤ) (hL : 1 ≤ L) (hn : 1 ≤ n) :
    promedio (paso_contador L) (malo_banda L n) h (.vivo 2 c,0) ≤
      1/(L:ℝ)+((L:ℝ)-1)/(n:ℝ) := by
  have hp : ∀ s, malo_banda L n s ≤ toca_techo L s.1+supera_cuenta n s := by
    intro s
    by_cases ht : (L:ℝ) ≤ altura s.1 <;> by_cases hc : n ≤ s.2 <;>
      simp [malo_banda, toca_techo, supera_cuenta, ht, hc]
  have hprom := promedio_mono (paso_contador L) _ _ hp h (.vivo 2 c,0)
  rw [promedio_suma, media_base] at hprom
  have h1 := coste_techo L h c hL
  have h2 := coste_cuenta L h n c hL hn
  linarith

def paso_original (s : Estado × ℕ) (b : Bool) : Estado × ℕ :=
  (paso_excursion s.1 b, s.2+mixto s.1)

def relacion (L : ℕ) (a b : Estado × ℕ) : Prop :=
  (L:ℝ) ≤ altura b.1 ∨ a=b

theorem relacion_paso (L : ℕ) (a b : Estado × ℕ) (bit : Bool)
    (hr : relacion L a b) : relacion L (paso_original a bit) (paso_contador L b bit) := by
  rcases hr with ht | heq
  · left
    simpa [paso_contador, paso_banda, not_lt.mpr ht] using ht
  · subst a
    by_cases ht : (L:ℝ) ≤ altura b.1
    · left
      simpa [paso_contador, paso_banda, not_lt.mpr ht] using ht
    · right
      simp [paso_original, paso_contador, paso_banda, mixto_banda, lt_of_not_ge ht]

theorem promedio_relacion {S T : Type} (p : S → Bool → S) (q : T → Bool → T)
    (R : S → T → Prop) (f : S → ℝ) (g : T → ℝ)
    (hr : ∀ a b, R a b → ∀ bit, R (p a bit) (q b bit))
    (hf : ∀ a b, R a b → f a ≤ g b)
    (h : ℕ) (a : S) (b : T) (hab : R a b) : promedio p f h a ≤ promedio q g h b := by
  induction h generalizing a b with
  | zero => exact hf a b hab
  | succ h ih =>
    have h0 := ih _ _ (hr a b hab false)
    have h1 := ih _ _ (hr a b hab true)
    simp only [promedio]
    linarith

theorem cola_mixtos_original (L h n : ℕ) (c : ℤ) (hL : 1 ≤ L) (hn : 1 ≤ n) :
    promedio paso_original (supera_cuenta n) h (.vivo 2 c,0) ≤
      1/(L:ℝ)+((L:ℝ)-1)/(n:ℝ) := by
  have hf : ∀ a b, relacion L a b → supera_cuenta n a ≤ malo_banda L n b := by
    intro a b hr
    rcases hr with ht | heq
    · unfold supera_cuenta malo_banda
      simp only [ht, true_or, if_true]
      split <;> norm_num
    · subst a
      by_cases ht : (L:ℝ) ≤ altura b.1 <;> by_cases hc : n ≤ b.2 <;>
        simp [supera_cuenta, malo_banda, ht, hc]
  have hprom := promedio_relacion paso_original (paso_contador L) (relacion L)
    (supera_cuenta n) (malo_banda L n)
    (fun a b hr bit => relacion_paso L a b bit hr) hf h
    (.vivo 2 c,0) (.vivo 2 c,0) (Or.inr rfl)
  exact hprom.trans (coste_banda L h n c hL hn)

theorem cola_mixtos_cuadrada (L h : ℕ) (c : ℤ) (hL : 1 ≤ L) :
    promedio paso_original (supera_cuenta (L^2)) h (.vivo 2 c,0) ≤ 2/(L:ℝ) := by
  have hn : 1 ≤ L^2 := by nlinarith
  have hprom := cola_mixtos_original L h (L^2) c hL hn
  have hp : (0:ℝ) < L := by exact_mod_cast (show 0<L by omega)
  have hid : (1/(L:ℝ))*(L:ℝ)^2 = (L:ℝ) := by field_simp
  have hc : ((L:ℝ)-1)/(L:ℝ)^2 ≤ 1/(L:ℝ) := by
    apply (div_le_iff₀ (show (0:ℝ) < (L:ℝ)^2 by positivity)).2
    rw [hid]
    linarith
  rw [Nat.cast_pow] at hprom
  calc
    _ ≤ 1/(L:ℝ)+((L:ℝ)-1)/(L:ℝ)^2 := hprom
    _ ≤ 1/(L:ℝ)+1/(L:ℝ) := by linarith
    _ = 2/(L:ℝ) := by ring

#print axioms altura_segundo_momento
#print axioms altura_banda_armonica
#print axioms energia_deriva
#print axioms balance_energia
#print axioms cuenta_acotada
#print axioms coste_techo
#print axioms media_contador
#print axioms coste_cuenta
#print axioms coste_banda
#print axioms relacion_paso
#print axioms cola_mixtos_original
#print axioms cola_mixtos_cuadrada

end BandaGao
