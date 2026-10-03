import Ensayo

/- Búsqueda truncada y bloques admitidos por información presente. -/

noncomputable section

namespace RepeticionGao

open MomentosGao
open RestoGao PalabrasGao

variable {S : Type}

def indicador (b : Bool) : ℝ := if b then 1 else 0

def busca (paso : S → Bool → S) (guardia vivo : S → Bool) (reinicio : S → S)
    (W : ℕ) (continuar : ℕ → S → ℝ) : ℕ → S → ℝ
  | 0, _ => 0
  | h+1, z => if guardia z && decide (W≤h+1) then
      promedio paso (fun w => if vivo w then continuar (h+1-W) (reinicio w) else 0) W z
    else (busca paso guardia vivo reinicio W continuar h (paso z false)+
      busca paso guardia vivo reinicio W continuar h (paso z true))/2

def fallos (paso : S → Bool → S) (guardia vivo : S → Bool) (reinicio : S → S)
    (W : ℕ) : ℕ → ℕ → S → ℝ
  | 0, _, _ => 1
  | j+1, h, z => busca paso guardia vivo reinicio W
      (fun t w => fallos paso guardia vivo reinicio W j t w) h z

theorem busca_cota (paso : S → Bool → S) (guardia vivo : S → Bool) (reinicio : S → S)
    (W : ℕ) (continuar : ℕ → S → ℝ) (p M : ℝ) (hp : p≤1) (hM : 0≤M)
    (hc : ∀ h z, continuar h z≤M)
    (hr : ∀ z, guardia z=true → promedio paso (fun w => indicador (vivo w)) W z≤1-p)
    (h : ℕ) (z : S) : busca paso guardia vivo reinicio W continuar h z≤(1-p)*M := by
  induction h generalizing z with
  | zero => simp only [busca]; exact mul_nonneg (by linarith) hM
  | succ h ih =>
    by_cases hg : (guardia z && decide (W≤h+1))=true
    · have hg' : guardia z=true := (Bool.and_eq_true_iff.mp hg).1
      have hf : ∀ w, (if vivo w then continuar (h+1-W) (reinicio w) else 0)≤
          M*indicador (vivo w) := by
        intro w
        cases vivo w <;> simp [indicador,hc]
      have hm := promedio_mono paso _ _ hf W z
      rw [promedio_escalar] at hm
      have hb := mul_le_mul_of_nonneg_left (hr z hg') hM
      simp only [busca,hg,if_true]
      nlinarith
    · simp only [busca,hg,Bool.false_eq_true,if_false]
      have h0 := ih (paso z false)
      have h1 := ih (paso z true)
      linarith

theorem fallos_cota (paso : S → Bool → S) (guardia vivo : S → Bool) (reinicio : S → S)
    (W : ℕ) (p : ℝ) (hp : p≤1)
    (hr : ∀ z, guardia z=true → promedio paso (fun w => indicador (vivo w)) W z≤1-p)
    (j h : ℕ) (z : S) : fallos paso guardia vivo reinicio W j h z≤(1-p)^j := by
  induction j generalizing h z with
  | zero => simp [fallos]
  | succ j ih =>
    have hc := busca_cota paso guardia vivo reinicio W
      (fun t w => fallos paso guardia vivo reinicio W j t w)
      p ((1-p)^j) hp (pow_nonneg (by linarith) _) ih hr h z
    simpa [fallos,pow_succ,mul_comm] using hc

def busca_palabra (paso : S → Bool → S) (guardia vivo : S → Bool) (reinicio : S → S)
    (W : ℕ) (continuar : List Bool → S → Bool) : List Bool → S → Bool
  | [], _ => false
  | b::bs, z => if guardia z && decide (W≤(b::bs).length) then
      let w := recorre paso ((b::bs).take W) z
      vivo w && continuar ((b::bs).drop W) (reinicio w)
    else busca_palabra paso guardia vivo reinicio W continuar bs (paso z b)

def fallos_palabra (paso : S → Bool → S) (guardia vivo : S → Bool) (reinicio : S → S)
    (W : ℕ) : ℕ → List Bool → S → Bool
  | 0, _, _ => true
  | j+1, bs, z => busca_palabra paso guardia vivo reinicio W
      (fun post w => fallos_palabra paso guardia vivo reinicio W j post w) bs z

theorem busca_admite (paso : S → Bool → S) (guardia vivo : S → Bool) (reinicio : S → S)
    (W : ℕ) (hW : 1≤W) (continuar : List Bool → S → Bool) (bs : List Bool) (z : S)
    (hg : guardia z=true) (hw : W≤bs.length) :
    busca_palabra paso guardia vivo reinicio W continuar bs z=
      (vivo (recorre paso (bs.take W) z) &&
        continuar (bs.drop W) (reinicio (recorre paso (bs.take W) z))) := by
  cases bs with
  | nil => simp at hw; omega
  | cons b bs =>
    simp only [List.length_cons] at hw
    simp [busca_palabra,hg,hw]

theorem media_busca (paso : S → Bool → S) (guardia vivo : S → Bool) (reinicio : S → S)
    (W : ℕ) (hW : 1≤W) (continuar : List Bool → S → Bool) (h : ℕ) (z : S) :
    media h (fun bs => indicador (busca_palabra paso guardia vivo reinicio W continuar bs z)) =
      busca paso guardia vivo reinicio W
        (fun n w => media n (fun post => indicador (continuar post w))) h z := by
  induction h generalizing z with
  | zero => simp [media,busca_palabra,indicador,busca]
  | succ h ih =>
    by_cases hg : (guardia z && decide (W≤h+1))=true
    · have hguard := (Bool.and_eq_true_iff.mp hg).1
      have htiempo : W≤h+1 := by simpa using (Bool.and_eq_true_iff.mp hg).2
      have hsum : W+(h+1-W)=h+1 := by omega
      let f : List Bool → ℝ := fun bs =>
        if vivo (recorre paso (bs.take W) z) then
          indicador (continuar (bs.drop W) (reinicio (recorre paso (bs.take W) z))) else 0
      have he : media (h+1) (fun bs => indicador
          (busca_palabra paso guardia vivo reinicio W continuar bs z))=media (h+1) f := by
        apply media_congr
        intro bs hbs
        rw [busca_admite paso guardia vivo reinicio W hW continuar bs z hguard (by omega)]
        cases hv : vivo (recorre paso (bs.take W) z) <;> simp [f,indicador,hv]
      rw [he]
      rw [show media (h+1) f=media (W+(h+1-W)) f by rw [hsum],media_append]
      have hf : ∀ pre, pre.length=W → media (h+1-W) (fun post => f (pre++post))=
          (if vivo (recorre paso pre z) then media (h+1-W)
            (fun post => indicador (continuar post (reinicio (recorre paso pre z)))) else 0) := by
        intro pre hp
        simp only [f,←hp,List.take_left,List.drop_left]
        cases vivo (recorre paso pre z) <;> simp [media_constante]
      rw [media_congr W _ _ hf,
        media_recorre paso (fun w => if vivo w then
          media (h+1-W) (fun post => indicador (continuar post (reinicio w))) else 0) W z]
      simp only [busca,hg,if_true]
    · have he (b : Bool) : media h (fun bs => indicador
          (busca_palabra paso guardia vivo reinicio W continuar (b::bs) z))=
          media h (fun bs => indicador
            (busca_palabra paso guardia vivo reinicio W continuar bs (paso z b))) := by
        apply media_congr
        intro bs hbs
        simp [busca_palabra,hbs,hg]
      rw [media,he false,he true,ih,ih]
      simp only [busca,hg,Bool.false_eq_true,if_false]

theorem media_fallos (paso : S → Bool → S) (guardia vivo : S → Bool) (reinicio : S → S)
    (W : ℕ) (hW : 1≤W) (j h : ℕ) (z : S) :
    media h (fun bs => indicador (fallos_palabra paso guardia vivo reinicio W j bs z))=
      fallos paso guardia vivo reinicio W j h z := by
  induction j generalizing h z with
  | zero => simp [fallos_palabra,indicador,media_constante,fallos]
  | succ j ih =>
    simp only [fallos_palabra,media_busca paso guardia vivo reinicio W hW,ih,fallos]

#print axioms media_busca
#print axioms media_fallos
#print axioms busca_cota
#print axioms fallos_cota

end RepeticionGao
