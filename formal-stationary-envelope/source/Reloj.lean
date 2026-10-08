import UmbralRachas

/- Reloj físico por bloques deterministas de bits justos. El contador
   registra los pasos mixtos, incluido el de salida de la excursión. -/

noncomputable section

namespace RelojGao

open CadenaCompletaGao MomentosGao SupervivenciaGao BandaGao
open RachasEnterasGao UmbralRachasGao

theorem altura_por_mixtos (z : Estado) (b : Bool) :
    altura (paso_excursion z b) ≤ altura z+(mixto z:ℝ) := by
  cases z with
  | fusion => simp [paso_excursion, RestoGao.interior, altura, mixto]
  | vivo k c =>
    cases k with
    | zero => simp [paso_excursion, RestoGao.interior, altura, mixto]
    | succ k =>
      cases k with
      | zero => simp [paso_excursion, RestoGao.interior, altura, mixto]
      | succ k =>
        cases b <;> by_cases hc : c%2=0 <;>
          simp [paso_excursion, RestoGao.interior, paso, altura, mixto, hc] <;> linarith

def EstadoReloj := {z : Estado × ℕ // altura z.1 ≤ (z.2:ℝ)+1}

def paso_reloj (z : EstadoReloj) (b : Bool) : EstadoReloj :=
  ⟨paso_original z.val b, by
    have h := altura_por_mixtos z.val.1 b
    have hz := z.property
    simp only [paso_original, Nat.cast_add]
    linarith⟩

def inicial (c : ℤ) : EstadoReloj := ⟨(.vivo 2 c,0), by norm_num [altura]⟩

def retraso (j : ℕ) (z : Estado × ℕ) : ℝ :=
  if RestoGao.interior z.1 = true ∧ z.2 < j then 1 else 0

theorem retraso_cota (j : ℕ) (z : Estado × ℕ) : retraso j z ≤ 1 := by
  unfold retraso
  split <;> norm_num

theorem promedio_imposible (h j : ℕ) (z : Estado × ℕ) (hj : j ≤ z.2) :
    promedio paso_original (retraso j) h z = 0 := by
  induction h generalizing z with
  | zero => simp [promedio, retraso, show ¬z.2<j by omega]
  | succ h ih =>
    have h0 := ih (paso_original z false) (by simp only [paso_original]; omega)
    have h1 := ih (paso_original z true) (by simp only [paso_original]; omega)
    simp [promedio, h0, h1]

theorem paso_fuera (z : Estado × ℕ) (b : Bool) (hz : RestoGao.interior z.1 = false) :
    paso_original z b = z := by
  rcases z with ⟨z,j⟩
  cases z with
  | fusion => simp [paso_original, paso_excursion, mixto, RestoGao.interior]
  | vivo k c =>
    cases k with
    | zero => simp [paso_original, paso_excursion, mixto, RestoGao.interior]
    | succ k => cases k <;> simp_all [paso_original, paso_excursion, mixto, RestoGao.interior]

theorem promedio_fuera (h j : ℕ) (z : Estado × ℕ)
    (hz : RestoGao.interior z.1 = false) : promedio paso_original (retraso j) h z = 0 := by
  induction h with
  | zero => simp [promedio, retraso, hz]
  | succ h ih => simp [promedio, paso_fuera z false hz, paso_fuera z true hz, ih]

theorem media_reloj (h : ℕ) (f : Estado × ℕ → ℝ) (z : EstadoReloj) :
    promedio paso_reloj (fun w => f w.val) h z = promedio paso_original f h z.val := by
  induction h generalizing z with
  | zero => rfl
  | succ h ih => simp only [promedio, ih, paso_reloj]

theorem sin_progreso (h : ℕ) (z : Estado × ℕ) :
    promedio paso_original (retraso (z.2+1)) h z ≤ racha_cadena h z.1 := by
  induction h generalizing z with
  | zero => exact retraso_cota _ _
  | succ h ih =>
    rcases z with ⟨z,j⟩
    cases z with
    | fusion => simp [promedio_fuera, RestoGao.interior, racha_cadena]
    | vivo k c =>
      cases k with
      | zero => simp [promedio_fuera, RestoGao.interior, racha_cadena]
      | succ k =>
        cases k with
        | zero => simp [promedio_fuera, RestoGao.interior, racha_cadena]
        | succ k =>
          by_cases hc : c%2=0
          · have h0 := ih (paso_original (.vivo (k+2) c,j) false)
            have h1 := ih (paso_original (.vivo (k+2) c,j) true)
            simp only [paso_original, paso_excursion, RestoGao.interior, if_true,
              mixto, hc, Nat.add_zero] at h0 h1
            simpa only [promedio, racha_cadena, hc, if_true, paso_original,
              paso_excursion, RestoGao.interior, mixto, Nat.add_zero] using
              div_le_div_of_nonneg_right (add_le_add h0 h1) (by norm_num : (0:ℝ) ≤ 2)
          · have h0 := promedio_imposible h (j+1)
              (paso_original (.vivo (k+2) c,j) false)
              (by simp [paso_original, mixto, hc])
            have h1 := promedio_imposible h (j+1)
              (paso_original (.vivo (k+2) c,j) true)
              (by simp [paso_original, mixto, hc])
            simp only [promedio, h0, h1, racha_cadena, hc, if_false]
            norm_num

theorem promedio_componer {S : Type} (p : S → Bool → S) (f : S → ℝ)
    (m n : ℕ) (z : S) : promedio p f (m+n) z =
      promedio p (fun w => promedio p f n w) m z := by
  induction m generalizing z with
  | zero => simp [promedio]
  | succ m ih => simp only [Nat.succ_add, promedio, ih]

theorem bloque (n j a s : ℕ) (z : EstadoReloj) (hj : j < n)
    (ha : 2+Nat.log 2 (n+2) ≤ a) :
    promedio paso_reloj (fun w => retraso (j+1) w.val) (a+s+1) z ≤
      retraso j z.val+1/(2:ℝ)^s := by
  rw [media_reloj]
  have hp : 0 ≤ 1/(2:ℝ)^s := by positivity
  by_cases hz : RestoGao.interior z.val.1 = true
  · by_cases hc : z.val.2 < j
    · have hle := promedio_mono paso_original (retraso (j+1)) (fun _ => 1)
        (retraso_cota (j+1)) (a+s+1) z.val
      rw [promedio_constante] at hle
      simp only [retraso, hz, hc, and_self, if_true]
      linarith
    · by_cases he : z.val.2=j
      · have hn := sin_progreso (a+s+1) z.val
        rw [he] at hn
        have hr : racha_cadena (a+s+1) z.val.1 ≤ 1/(2:ℝ)^s := by
          have hi := z.property
          cases hbase : z.val.1 with
          | fusion => simp [hbase, RestoGao.interior] at hz
          | vivo k c =>
            cases k with
            | zero => simp [hbase, RestoGao.interior] at hz
            | succ k =>
              cases k with
              | zero => simp [hbase, RestoGao.interior] at hz
              | succ k =>
                rw [hbase, he] at hi
                simp only [altura, Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at hi
                have hk : k ≤ j := by exact_mod_cast (show (k:ℝ) ≤ (j:ℝ) by linarith)
                have hlog : Nat.log 2 (k+2) ≤ Nat.log 2 (n+2) := Nat.log_mono_right (by omega)
                have ho := orden_cota (k+2) (by omega)
                have hu := cola_umbral k (a+1) s c (by omega)
                simpa only [hbase, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hu
        simp only [retraso, hz, hc, and_false, if_false, zero_add]
        exact hn.trans hr
      · have hge : j+1 ≤ z.val.2 := by omega
        rw [promedio_imposible _ _ _ hge]
        simp [retraso, hc]
  · have hf : RestoGao.interior z.val.1 = false := by
      cases heq : RestoGao.interior z.val.1 <;> simp_all
    rw [promedio_fuera _ _ _ hf]
    simp [retraso, hf]

theorem reloj_bloques (n j a s : ℕ) (z : EstadoReloj) (hj : j ≤ n)
    (ha : 2+Nat.log 2 (n+2) ≤ a) :
    promedio paso_reloj (fun w => retraso j w.val) (j*(a+s+1)) z ≤
      (j:ℝ)/(2:ℝ)^s := by
  induction j with
  | zero => simp [promedio, retraso]
  | succ j ih =>
    have hi := ih (by omega)
    have hb := promedio_mono paso_reloj
      (fun w => promedio paso_reloj (fun v => retraso (j+1) v.val) (a+s+1) w)
      (fun w => retraso j w.val+1/(2:ℝ)^s)
      (fun w => bloque n j a s w (by omega) ha) (j*(a+s+1)) z
    rw [promedio_suma, promedio_constante] at hb
    rw [Nat.succ_mul, promedio_componer]
    simp only [Nat.cast_add, Nat.cast_one]
    calc
      _ ≤ promedio paso_reloj (fun w => retraso j w.val) (j*(a+s+1)) z+1/(2:ℝ)^s := hb
      _ ≤ (j:ℝ)/(2:ℝ)^s+1/(2:ℝ)^s := by linarith
      _ = ((j:ℝ)+1)/(2:ℝ)^s := by ring

/- M6: probabilidad de seguir vivo con menos de n mixtos en el horizonte.
   Equivale a que min(tau, tiempo del n-ésimo mixto) sea mayor que H. -/
theorem reloj_original (n a s : ℕ) (c : ℤ)
    (ha : 2+Nat.log 2 (n+2) ≤ a) :
    promedio paso_original (retraso n) (n*(a+s+1)) (.vivo 2 c,0) ≤
      (n:ℝ)/(2:ℝ)^s := by
  have h := reloj_bloques n n a s (inicial c) le_rfl ha
  rw [media_reloj] at h
  exact h

theorem media_excursion (h : ℕ) (f : Estado → ℝ) (z : Estado) (j : ℕ) :
    promedio paso_original (fun w => f w.1) h (z,j) = promedio paso_excursion f h z := by
  induction h generalizing z j with
  | zero => rfl
  | succ h ih => simp only [promedio, paso_original, ih]

/- H3: cola del tiempo físico de la primera excursión; c es cualquier entero. -/
theorem cola_excursion (L n a s : ℕ) (c : ℤ) (hL : 1 ≤ L) (hn : 1 ≤ n)
    (ha : 2+Nat.log 2 (n+2) ≤ a) :
    supervivencia (n*(a+s+1)) c ≤
      1/(L:ℝ)+((L:ℝ)-1)/(n:ℝ)+(n:ℝ)/(2:ℝ)^s := by
  have hp : ∀ z : Estado × ℕ, vivo z.1 ≤ retraso n z+supera_cuenta n z := by
    intro z
    by_cases hi : RestoGao.interior z.1=true <;> by_cases hj : n ≤ z.2 <;>
      simp [vivo, retraso, supera_cuenta, hi, hj, show z.2<n ↔ ¬n≤z.2 by omega]
  have hprom := promedio_mono paso_original _ _ hp (n*(a+s+1)) (.vivo 2 c,0)
  rw [promedio_suma, media_excursion] at hprom
  have hr := reloj_original n a s c ha
  have hm := cola_mixtos_original L (n*(a+s+1)) n c hL hn
  unfold supervivencia
  linarith

#print axioms altura_por_mixtos
#print axioms media_reloj
#print axioms sin_progreso
#print axioms promedio_componer
#print axioms bloque
#print axioms reloj_bloques
#print axioms reloj_original
#print axioms media_excursion
#print axioms cola_excursion

end RelojGao
