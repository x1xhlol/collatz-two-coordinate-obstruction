import Reloj
import Producto

/- Un único espacio finito de palabras para combinar eventos dependientes. -/

noncomputable section
open Classical

namespace PalabrasGao

open MomentosGao RestoGao

def media : ℕ → (List Bool → ℝ) → ℝ
  | 0, f => f []
  | n+1, f => (media n (fun bs => f (false::bs))+media n (fun bs => f (true::bs)))/2

def marca (P : Prop) : ℝ := if P then 1 else 0

theorem media_constante (n : ℕ) (x : ℝ) : media n (fun _ => x) = x := by
  induction n with
  | zero => rfl
  | succ n ih => simp [media, ih]

theorem media_mono (n : ℕ) (f g : List Bool → ℝ)
    (h : ∀ bs, bs.length=n → f bs ≤ g bs) : media n f ≤ media n g := by
  induction n generalizing f g with
  | zero => simpa [media] using h [] rfl
  | succ n ih =>
    have h0 := ih (fun bs => f (false::bs)) (fun bs => g (false::bs))
      (fun bs hb => h (false::bs) (by simp [hb]))
    have h1 := ih (fun bs => f (true::bs)) (fun bs => g (true::bs))
      (fun bs hb => h (true::bs) (by simp [hb]))
    simp only [media]
    linarith

theorem media_congr (n : ℕ) (f g : List Bool → ℝ)
    (h : ∀ bs, bs.length=n → f bs = g bs) : media n f = media n g := by
  apply le_antisymm
  · exact media_mono n f g (fun bs hb => le_of_eq (h bs hb))
  · exact media_mono n g f (fun bs hb => le_of_eq (h bs hb).symm)

theorem media_suma (n : ℕ) (f g : List Bool → ℝ) :
    media n (fun bs => f bs+g bs) = media n f+media n g := by
  induction n generalizing f g with
  | zero => rfl
  | succ n ih => simp only [media, ih]; ring

theorem media_recorre {S : Type} (p : S → Bool → S) (f : S → ℝ) (n : ℕ) (z : S) :
    media n (fun bs => f (recorre p bs z)) = promedio p f n z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih => simp only [media, recorre, ih, promedio]

theorem media_append (m n : ℕ) (f : List Bool → ℝ) :
    media (m+n) f = media m (fun pre => media n (fun post => f (pre++post))) := by
  induction m generalizing f with
  | zero => simp [media]
  | succ m ih => simp only [Nat.succ_add, media, ih, List.cons_append]

theorem media_take (m n : ℕ) (f : List Bool → ℝ) :
    media (m+n) (fun bs => f (bs.take m)) = media m f := by
  induction m generalizing f with
  | zero => simp [media, media_constante]
  | succ m ih =>
    simp only [Nat.succ_add, media, List.take_succ_cons]
    rw [ih (fun bs => f (false::bs)), ih (fun bs => f (true::bs))]

def cruza {S : Type} (p : S → Bool → S) (u : S → ℝ) (U : ℝ) : List Bool → S → Prop
  | [], z => U < u z
  | b::bs, z => U < u z ∨ cruza p u U bs (p z b)

theorem media_cruza {S : Type} (p : S → Bool → S) (u : S → ℝ) (U : ℝ)
    (n : ℕ) (z : S) :
    media n (fun bs => marca (cruza p u U bs z)) = MaximosGao.cruce p u U n z := by
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    by_cases hz : U < u z
    · simp [media, cruza, hz, marca, media_constante, MaximosGao.cruce]
    · simp only [media, cruza, hz, false_or, ih, MaximosGao.cruce, if_false]

theorem cruza_prefijo {S : Type} (p : S → Bool → S) (u : S → ℝ) (U : ℝ)
    (pre post : List Bool) (z : S) (h : ¬cruza p u U (pre++post) z) :
    u (recorre p pre z) ≤ U := by
  induction pre generalizing z with
  | nil =>
    cases post <;> simp only [List.nil_append, cruza, not_or] at h
    · exact le_of_not_gt h
    · exact le_of_not_gt h.1
  | cons b pre ih =>
    simp only [List.cons_append, cruza, not_or] at h
    exact ih (p z b) h.2

theorem recorre_append {S : Type} (p : S → Bool → S) (pre post : List Bool) (z : S) :
    recorre p (pre++post) z = recorre p post (recorre p pre z) := by
  induction pre generalizing z with
  | nil => rfl
  | cons b pre ih => exact ih (p z b)

def cruce_producto (T : ℕ) (bs : List Bool) : Prop :=
  cruza ProductoGao.paso_producto abs 1 (bs.drop T)
    (recorre ProductoGao.paso_producto (bs.take T) 1)

theorem media_producto (T D : ℕ) :
    media (T+D) (fun bs => marca (cruce_producto T bs)) = ProductoGao.cruce_desde T D := by
  rw [media_append]
  have h : ∀ pre, pre.length=T →
      media D (fun post => marca (cruce_producto T (pre++post))) =
      MaximosGao.cruce ProductoGao.paso_producto abs 1 D
        (recorre ProductoGao.paso_producto pre 1) := by
    intro pre hp
    simp only [cruce_producto, ← hp, List.take_left, List.drop_left]
    exact media_cruza _ _ _ _ _
  rw [media_congr T _ _ h, media_recorre]
  rfl

#print axioms media_recorre
#print axioms media_take
#print axioms media_cruza
#print axioms cruza_prefijo
#print axioms media_producto

end PalabrasGao
