import Martas

/- Tejonas: los pares reales (x,y) bajo el mapa atajo, con sus conteos impares,
   siguen exactamente la cadena de Gao. El estado canónico de un par real
   evoluciona por `paso` con la paridad del ancla como bit. -/

namespace TejonasGao

open CadenaCompletaGao

/-! ## Mapa atajo y pares reales -/

def Tm (x : ℤ) : ℤ := if x%2=0 then x/2 else (3*x+1)/2

def imp (x : ℤ) : ℕ := if x%2=0 then 0 else 1

structure Par where
  x : ℤ
  y : ℤ
  p : ℕ
  q : ℕ

def paso_par (s : Par) : Par := ⟨Tm s.x,Tm s.y,s.p+imp s.x,s.q+imp s.y⟩

def anclax (s : Par) : Prop := s.p<s.q ∨ (s.p=s.q ∧ s.x<s.y)

instance (s : Par) : Decidable (anclax s) := by unfold anclax; infer_instance

def canon (s : Par) : Estado :=
  if s.p=s.q ∧ s.x=s.y then .fusion
  else if anclax s then .vivo (s.q-s.p) (s.y-3^(s.q-s.p)*s.x)
  else .vivo (s.p-s.q) (s.x-3^(s.p-s.q)*s.y)

def bit (s : Par) : Bool := if anclax s then decide (s.x%2=1) else decide (s.y%2=1)

def gira (s : Par) : Par := ⟨s.y,s.x,s.q,s.p⟩

theorem Tm_par (x : ℤ) (h : x%2=0) : Tm x=x/2 := by simp [Tm,h]
theorem Tm_impar (x : ℤ) (h : x%2=1) : Tm x=(3*x+1)/2 := by simp [Tm,show x%2≠0 by omega]
theorem imp_par (x : ℤ) (h : x%2=0) : imp x=0 := by simp [imp,h]
theorem imp_impar (x : ℤ) (h : x%2=1) : imp x=1 := by simp [imp,show x%2≠0 by omega]

theorem canon_fusion (s : Par) (h : s.p=s.q ∧ s.x=s.y) : canon s=.fusion := by
  simp [canon,h]

theorem canon_ancla (s : Par) (ha : anclax s) :
    canon s=.vivo (s.q-s.p) (s.y-3^(s.q-s.p)*s.x) := by
  have hf : ¬(s.p=s.q ∧ s.x=s.y) := by
    rintro ⟨h1,h2⟩; unfold anclax at ha; omega
  simp only [canon,hf,ha,if_false,if_true]

theorem canon_otro (s : Par) (hf : ¬(s.p=s.q ∧ s.x=s.y)) (ha : ¬anclax s) :
    canon s=.vivo (s.p-s.q) (s.x-3^(s.p-s.q)*s.y) := by
  simp only [canon,hf,ha,if_false]

theorem tres_impar (k : ℕ) : (3:ℤ)^k%2=1 := by
  induction k with
  | zero => norm_num
  | succ k ih => rw [pow_succ]; omega

theorem por_impar (A x : ℤ) (hA : A%2=1) : (A*x)%2=x%2 := by
  rw [Int.mul_emod,hA]; simp

/-! ## Transiciones de la cadena en cada nivel -/

theorem paso_nivel_par (j : ℕ) (c : ℤ) (hc : c%2=0) (b : Bool) :
    paso (.vivo (j+1) c) b=.vivo (j+1) (if b then (3*c+1-3^(j+1))/2 else c/2) := by
  simp [paso,hc,coef_es_potencia]

theorem paso_nivel_impar_falso (j : ℕ) (c : ℤ) (hc : c%2=1) :
    paso (.vivo (j+1) c) false=.vivo (j+2) ((3*c+1)/2) := by
  simp [paso,show c%2≠0 by omega]

theorem paso_nivel_impar_alto (i : ℕ) (c : ℤ) (hc : c%2=1) :
    paso (.vivo (i+2) c) true=.vivo (i+1) ((c-3^(i+1))/2) := by
  simp [paso,show c%2≠0 by omega,coef_es_potencia]

theorem paso_uno_impar (c : ℤ) (hc : c%2=1) :
    paso (.vivo 1 c) true=if c=1 then .fusion else .vivo 0 (mag ((c-1)/2)) := by
  have h : paso (.vivo (0+1) c) true=if c=1 then .fusion else .vivo 0 (mag ((c-1)/2)) := by
    simp [paso,show c%2≠0 by omega]
  simpa using h

theorem paso_cero (c : ℤ) (b : Bool) :
    paso (.vivo 0 c) b=if c%2=0 then .vivo 0 (if b then 3*c/2 else c/2)
      else .vivo 1 (if b then (1-3*c)/2 else (3*c+1)/2) := by
  simp [paso]

/-! ## Invariante de un paso con el ancla en x -/

theorem mag_pos (c : ℤ) (h : 0<c) : mag c=c := by unfold mag; split <;> omega
theorem mag_neg (c : ℤ) (h : c<0) : mag c=-c := by unfold mag; split <;> omega

/-- Nivel 0: mismos conteos y x<y. -/
theorem canon_paso_cero (x y : ℤ) (p : ℕ) (hxy : x<y) :
    canon (paso_par ⟨x,y,p,p⟩)=paso (canon ⟨x,y,p,p⟩) (bit ⟨x,y,p,p⟩) := by
  have ha : anclax ⟨x,y,p,p⟩ := Or.inr ⟨rfl,hxy⟩
  rw [canon_ancla _ ha]
  simp only [Nat.sub_self,pow_zero,one_mul,bit,ha,if_true,paso_cero]
  rcases Int.emod_two_eq_zero_or_one x with hx | hx <;>
    rcases Int.emod_two_eq_zero_or_one y with hy | hy
  · -- ambos pares
    have e : paso_par ⟨x,y,p,p⟩=⟨x/2,y/2,p,p⟩ := by
      simp [paso_par,Tm_par x hx,Tm_par y hy,imp_par x hx,imp_par y hy]
    rw [e,canon_ancla _ (by unfold anclax; dsimp only; omega)]
    simp only [Nat.sub_self,pow_zero,one_mul,hx]
    rw [if_pos (by omega)]
    simp only [show ¬(0:ℤ)=1 by norm_num,decide_false,Bool.false_eq_true,if_false]
    congr 1; omega
  · -- x par, y impar
    have e : paso_par ⟨x,y,p,p⟩=⟨x/2,(3*y+1)/2,p,p+1⟩ := by
      simp [paso_par,Tm_par x hx,Tm_impar y hy,imp_par x hx,imp_impar y hy]
    rw [e,canon_ancla _ (by unfold anclax; dsimp only; omega)]
    rw [if_neg (by omega)]
    simp only [hx,show ¬(0:ℤ)=1 by norm_num,decide_false,Bool.false_eq_true,if_false,
      show p+1-p=1 by omega,pow_one]
    congr 1; omega
  · -- x impar, y par
    have e : paso_par ⟨x,y,p,p⟩=⟨(3*x+1)/2,y/2,p+1,p⟩ := by
      simp [paso_par,Tm_impar x hx,Tm_par y hy,imp_impar x hx,imp_par y hy]
    rw [e,canon_otro _ (by simp) (by simp [anclax])]
    rw [if_neg (by omega)]
    simp only [hx,decide_true,if_true,show p+1-p=1 by omega,pow_one]
    congr 1; omega
  · -- ambos impares
    have e : paso_par ⟨x,y,p,p⟩=⟨(3*x+1)/2,(3*y+1)/2,p+1,p+1⟩ := by
      simp [paso_par,Tm_impar x hx,Tm_impar y hy,imp_impar x hx,imp_impar y hy]
    rw [e,canon_ancla _ (by unfold anclax; dsimp only; omega)]
    simp only [Nat.sub_self,pow_zero,one_mul,hx,decide_true,if_true]
    rw [if_pos (by omega)]
    congr 1; omega

/-- Niveles k=j+1>=1 con el ancla en x. -/
theorem canon_paso_alto (x y : ℤ) (p j : ℕ) :
    canon (paso_par ⟨x,y,p,p+(j+1)⟩)=paso (canon ⟨x,y,p,p+(j+1)⟩) (bit ⟨x,y,p,p+(j+1)⟩) := by
  have ha : anclax ⟨x,y,p,p+(j+1)⟩ := by unfold anclax; dsimp only; omega
  rw [canon_ancla _ ha]
  simp only [bit,ha,if_true,show p+(j+1)-p=j+1 by omega]
  set A : ℤ := 3^(j+1) with hAdef
  have hA : A%2=1 := tres_impar (j+1)
  have hAx : (A*x)%2=x%2 := por_impar A x hA
  rcases Int.emod_two_eq_zero_or_one x with hx | hx <;>
    rcases Int.emod_two_eq_zero_or_one y with hy | hy
  · -- ambos pares: c par, bit 0
    have hc : (y-A*x)%2=0 := by omega
    have e : paso_par ⟨x,y,p,p+(j+1)⟩=⟨x/2,y/2,p,p+(j+1)⟩ := by
      simp [paso_par,Tm_par x hx,Tm_par y hy,imp_par x hx,imp_par y hy]
    rw [e,canon_ancla _ (by unfold anclax; dsimp only; omega)]
    simp only [show p+(j+1)-p=j+1 by omega,hx,show ¬(0:ℤ)=1 by norm_num,decide_false]
    rw [paso_nivel_par j _ hc false]
    simp only [Bool.false_eq_true,if_false]
    have h2 : A*x=2*(A*(x/2)) := by
      have : x=2*(x/2) := by omega
      conv_lhs => rw [this]
      ring
    try rw [← hAdef]
    congr 1; omega
  · -- x par, y impar: c impar, bit 0, sube un nivel
    have hc : (y-A*x)%2=1 := by omega
    have e : paso_par ⟨x,y,p,p+(j+1)⟩=⟨x/2,(3*y+1)/2,p,p+(j+1)+1⟩ := by
      simp [paso_par,Tm_par x hx,Tm_impar y hy,imp_par x hx,imp_impar y hy]
    rw [e,canon_ancla _ (by unfold anclax; dsimp only; omega)]
    simp only [show p+(j+1)+1-p=j+2 by omega,hx,show ¬(0:ℤ)=1 by norm_num,decide_false]
    rw [paso_nivel_impar_falso j _ hc]
    have h2 : A*x=2*(A*(x/2)) := by
      have : x=2*(x/2) := by omega
      conv_lhs => rw [this]
      ring
    have h3 : (3:ℤ)^(j+2)*(x/2)=3*(A*(x/2)) := by rw [hAdef]; ring
    rw [h3]
    congr 1; omega
  · -- x impar, y par: c impar, bit 1, baja un nivel
    have hc : (y-A*x)%2=1 := by omega
    simp only [hx,decide_true]
    cases j with
    | zero =>
      -- de k=1 a k=0
      have hA3 : A=3 := by rw [hAdef]; norm_num
      have e : paso_par ⟨x,y,p,p+(0+1)⟩=⟨(3*x+1)/2,y/2,p+1,p+(0+1)⟩ := by
        simp [paso_par,Tm_impar x hx,Tm_par y hy,imp_impar x hx,imp_par y hy]
      rw [e]
      have hc1 : (y-A*x)%2=1 := hc
      rw [show (0:ℕ)+1=1 by rfl,paso_uno_impar _ hc1]
      by_cases h1 : y-A*x=1
      · rw [if_pos h1,canon_fusion]
        dsimp only
        constructor
        · omega
        · rw [hA3] at h1; omega
      · rw [if_neg h1]
        rw [hA3] at h1 ⊢
        by_cases hlt : (3*x+1)/2<y/2
        · rw [canon_ancla _ (by unfold anclax; dsimp only; omega)]
          simp only [show p+(0+1)-(p+1)=0 by omega,pow_zero,one_mul]
          rw [mag_pos _ (by omega)]
          congr 1; omega
        · have hne : (3*x+1)/2≠y/2 := by omega
          rw [canon_otro _ (by dsimp only; omega) (by unfold anclax; dsimp only; omega)]
          simp only [show p+1-(p+(0+1))=0 by omega,pow_zero,one_mul]
          rw [mag_neg _ (by omega)]
          congr 1; omega
    | succ i =>
      set B : ℤ := 3^(i+1) with hBdef
      have hAB : A=3*B := by rw [hAdef,hBdef]; ring
      have e : paso_par ⟨x,y,p,p+(i+1+1)⟩=⟨(3*x+1)/2,y/2,p+1,p+(i+1+1)⟩ := by
        simp [paso_par,Tm_impar x hx,Tm_par y hy,imp_impar x hx,imp_par y hy]
      rw [e,canon_ancla _ (by unfold anclax; dsimp only; omega)]
      simp only [show p+(i+1+1)-(p+1)=i+1 by omega]
      rw [show i+1+1=i+2 by rfl,paso_nivel_impar_alto i _ hc]
      have h2 : B*(3*x+1)=2*(B*((3*x+1)/2)) := by
        have : 3*x+1=2*((3*x+1)/2) := by omega
        conv_lhs => rw [this]
        ring
      have h3 : B*(3*x+1)=3*(B*x)+B := by ring
      have h4 : A*x=3*(B*x) := by rw [hAB]; ring
      try rw [← hBdef]
      congr 1; omega
  · -- ambos impares: c par, bit 1, mismo nivel
    have hc : (y-A*x)%2=0 := by omega
    have e : paso_par ⟨x,y,p,p+(j+1)⟩=⟨(3*x+1)/2,(3*y+1)/2,p+1,p+(j+1)+1⟩ := by
      simp [paso_par,Tm_impar x hx,Tm_impar y hy,imp_impar x hx,imp_impar y hy]
    rw [e,canon_ancla _ (by unfold anclax; dsimp only; omega)]
    simp only [show p+(j+1)+1-(p+1)=j+1 by omega,hx,decide_true]
    rw [paso_nivel_par j _ hc true]
    simp only [if_true]
    have h2 : A*(3*x+1)=2*(A*((3*x+1)/2)) := by
      have : 3*x+1=2*((3*x+1)/2) := by omega
      conv_lhs => rw [this]
      ring
    have h3 : A*(3*x+1)=3*(A*x)+A := by ring
    try rw [← hAdef]
    congr 1; omega

/-! ## Invariante general por simetría -/

theorem canon_paso_x (s : Par) (ha : anclax s) : canon (paso_par s)=paso (canon s) (bit s) := by
  obtain ⟨x,y,p,q⟩ := s
  rcases ha with h | ⟨h,hxy⟩
  · obtain ⟨j,rfl⟩ : ∃ j, q=p+(j+1) := ⟨q-p-1,by dsimp only at h; omega⟩
    exact canon_paso_alto x y p j
  · dsimp only at h hxy
    subst h
    exact canon_paso_cero x y p hxy

theorem gira_ancla (s : Par) (hf : ¬(s.p=s.q ∧ s.x=s.y)) (ha : ¬anclax s) : anclax (gira s) := by
  unfold anclax at ha ⊢
  simp only [gira]
  omega

theorem canon_gira (s : Par) : canon (gira s)=canon s := by
  by_cases hf : s.p=s.q ∧ s.x=s.y
  · rw [canon_fusion s hf,canon_fusion]; simp only [gira]; omega
  · have hfg : ¬((gira s).p=(gira s).q ∧ (gira s).x=(gira s).y) := by
      simp only [gira]; omega
    by_cases ha : anclax s
    · have hng : ¬anclax (gira s) := by unfold anclax at ha ⊢; simp only [gira]; omega
      rw [canon_otro _ hfg hng,canon_ancla _ ha]
      rfl
    · rw [canon_ancla _ (gira_ancla s hf ha),canon_otro _ hf ha]
      rfl

theorem bit_gira (s : Par) : bit (gira s)=bit s := by
  by_cases hf : s.p=s.q ∧ s.x=s.y
  · have h1 : ¬anclax s := by unfold anclax; omega
    have h2 : ¬anclax (gira s) := by unfold anclax; simp only [gira]; omega
    unfold bit
    rw [if_neg h2,if_neg h1]
    show decide (s.x%2=1)=decide (s.y%2=1)
    simp only [hf.2]
  · by_cases ha : anclax s
    · have hng : ¬anclax (gira s) := by unfold anclax at ha ⊢; simp only [gira]; omega
      unfold bit
      rw [if_neg hng,if_pos ha]
      rfl
    · unfold bit
      rw [if_pos (gira_ancla s hf ha),if_neg ha]
      rfl

theorem canon_paso (s : Par) : canon (paso_par s)=paso (canon s) (bit s) := by
  by_cases hf : s.p=s.q ∧ s.x=s.y
  · rw [canon_fusion s hf]
    have h2 : (paso_par s).p=(paso_par s).q ∧ (paso_par s).x=(paso_par s).y := by
      obtain ⟨h1,h2⟩ := hf
      simp only [paso_par,h1,h2,and_self]
    rw [canon_fusion _ h2]
    simp [paso]
  · by_cases ha : anclax s
    · exact canon_paso_x s ha
    · have hg := canon_paso_x (gira s) (gira_ancla s hf ha)
      have e : paso_par (gira s)=gira (paso_par s) := rfl
      rw [e,canon_gira,canon_gira,bit_gira] at hg
      exact hg

/-! ## Clases residuales: representación afín -/

structure Rep where
  p : ℕ
  a : ℤ
  q : ℕ
  b : ℤ

def par_rep (R : Rep) (m : ℤ) : Par := ⟨3^R.p*m+R.a,3^R.q*m+R.b,R.p,R.q⟩

def sig (R : Rep) (d : ℤ) : Rep :=
  ⟨R.p+imp (3^R.p*d+R.a),Tm (3^R.p*d+R.a),R.q+imp (3^R.q*d+R.b),Tm (3^R.q*d+R.b)⟩

theorem afin (P : ℕ) (a d l : ℤ) :
    Tm (3^P*(2*l+d)+a)=3^(P+imp (3^P*d+a))*l+Tm (3^P*d+a) ∧
      imp (3^P*(2*l+d)+a)=imp (3^P*d+a) := by
  set z := 3^P*d+a with hz
  have hx : 3^P*(2*l+d)+a=2*(3^P*l)+z := by rw [hz]; ring
  rw [hx]
  rcases Int.emod_two_eq_zero_or_one z with h | h
  · have h2 : (2*(3^P*l)+z)%2=0 := by omega
    rw [Tm_par _ h2,Tm_par _ h,imp_par _ h2,imp_par _ h,Nat.add_zero]
    constructor
    · omega
    · rfl
  · have h2 : (2*(3^P*l)+z)%2=1 := by omega
    rw [Tm_impar _ h2,Tm_impar _ h,imp_impar _ h2,imp_impar _ h,pow_succ]
    constructor
    · have e : 3*(2*(3^P*l)+z)+1=2*(3^P*3*l)+(3*z+1) := by ring
      rw [e]
      omega
    · rfl

theorem paso_rep (R : Rep) (d l : ℤ) :
    paso_par (par_rep R (2*l+d))=par_rep (sig R d) l := by
  obtain ⟨h1,h2⟩ := afin R.p R.a d l
  obtain ⟨h3,h4⟩ := afin R.q R.b d l
  simp only [paso_par,par_rep,sig,h1,h2,h3,h4]

theorem ancla_rep (R : Rep) (m : ℤ) : anclax (par_rep R m) ↔ anclax (par_rep R 0) := by
  unfold anclax par_rep
  simp only [mul_zero,zero_add]
  constructor
  · rintro (h | ⟨h1,h2⟩)
    · exact Or.inl h
    · right; refine ⟨h1,?_⟩; rw [h1] at h2; linarith
  · rintro (h | ⟨h1,h2⟩)
    · exact Or.inl h
    · right; refine ⟨h1,?_⟩; rw [h1]; linarith

theorem canon_rep (R : Rep) (m : ℤ) : canon (par_rep R m)=canon (par_rep R 0) := by
  have hf : (R.p=R.q ∧ 3^R.p*m+R.a=3^R.q*m+R.b) ↔ (R.p=R.q ∧ R.a=R.b) := by
    constructor
    · rintro ⟨h1,h2⟩; rw [h1] at h2; exact ⟨h1,by linarith⟩
    · rintro ⟨h1,h2⟩; rw [h1,h2]; exact ⟨rfl,rfl⟩
  by_cases hfu : R.p=R.q ∧ R.a=R.b
  · rw [canon_fusion _ (by simp only [par_rep]; exact hf.mpr hfu),
      canon_fusion _ (by simp only [par_rep,mul_zero,zero_add]; exact hfu)]
  · have hf1 : ¬((par_rep R m).p=(par_rep R m).q ∧ (par_rep R m).x=(par_rep R m).y) := by
      simp only [par_rep]; exact fun h => hfu (hf.mp h)
    have hf0 : ¬((par_rep R 0).p=(par_rep R 0).q ∧ (par_rep R 0).x=(par_rep R 0).y) := by
      simp only [par_rep,mul_zero,zero_add]; exact hfu
    by_cases ha : anclax (par_rep R 0)
    · have ham := (ancla_rep R m).mpr ha
      rw [canon_ancla _ ham,canon_ancla _ ha]
      have hpq : R.p≤R.q := by unfold anclax par_rep at ha; dsimp only at ha; omega
      simp only [par_rep,mul_zero,zero_add]
      congr 1
      have e : (3:ℤ)^(R.q-R.p)*3^R.p=3^R.q := by rw [← pow_add]; congr 1; omega
      rw [mul_add,← mul_assoc,e]
      ring
    · have ham : ¬anclax (par_rep R m) := fun h => ha ((ancla_rep R m).mp h)
      rw [canon_otro _ hf1 ham,canon_otro _ hf0 ha]
      have hqp : R.q≤R.p := by unfold anclax par_rep at ha; dsimp only at ha; omega
      simp only [par_rep,mul_zero,zero_add]
      congr 1
      have e : (3:ℤ)^(R.p-R.q)*3^R.q=3^R.p := by rw [← pow_add]; congr 1; omega
      rw [mul_add,← mul_assoc,e]
      ring

theorem decide_uno_mas (z : ℤ) : decide ((1+z)%2=1)=!decide (z%2=1) := by
  by_cases hz : z%2=1
  · have h : ¬((1+z)%2=1) := by omega
    simp [hz,h]
  · have h : (1+z)%2=1 := by omega
    simp [hz,h]

theorem bit_rep (R : Rep) : bit (par_rep R 1)=!bit (par_rep R 0) := by
  have ha := ancla_rep R 1
  have hp1 : ((3:ℤ)^R.p+R.a)%2=(1+R.a)%2 := by
    have := tres_impar R.p; omega
  have hq1 : ((3:ℤ)^R.q+R.b)%2=(1+R.b)%2 := by
    have := tres_impar R.q; omega
  by_cases h0 : anclax (par_rep R 0)
  · have h1 := ha.mpr h0
    unfold bit
    rw [if_pos h1,if_pos h0]
    simp only [par_rep,mul_one,mul_zero,zero_add,hp1]
    exact decide_uno_mas R.a
  · have h1 : ¬anclax (par_rep R 1) := fun h => h0 (ha.mp h)
    unfold bit
    rw [if_neg h1,if_neg h0]
    simp only [par_rep,mul_one,mul_zero,zero_add,hq1]
    exact decide_uno_mas R.b

theorem sig_canon (R : Rep) (d : ℤ) :
    canon (par_rep (sig R d) 0)=paso (canon (par_rep R 0)) (bit (par_rep R d)) := by
  have h := paso_rep R d 0
  simp only [mul_zero,zero_add] at h
  rw [← h,canon_paso,canon_rep R d]

/-! ## Transporte: suma sobre clases = promedio de la cadena -/

def iter (t : ℕ) (s : Par) : Par := (paso_par)^[t] s

theorem suma_pares (n : ℕ) (g : ℕ → ℝ) :
    ∑ i ∈ Finset.range (2*n),g i=∑ l ∈ Finset.range n,(g (2*l)+g (2*l+1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2*(n+1)=2*n+1+1 by ring,Finset.sum_range_succ,Finset.sum_range_succ,ih,
      Finset.sum_range_succ]
    ring

theorem suma_rep (f : Estado → ℝ) (t : ℕ) : ∀ R : Rep,
    ∑ m ∈ Finset.range (2^t),f (canon (iter t (par_rep R m)))=
      (2:ℝ)^t*MomentosGao.promedio paso f t (canon (par_rep R 0)) := by
  induction t with
  | zero =>
    intro R
    simp [iter,MomentosGao.promedio]
  | succ t ih =>
    intro R
    rw [pow_succ,mul_comm (2^t) 2,suma_pares]
    have hd : ∀ (d : ℕ) (l : ℕ), d<2 →
        f (canon (iter (t+1) (par_rep R ((2*l+d:ℕ):ℤ))))=
          f (canon (iter t (par_rep (sig R d) l))) := by
      intro d l _
      simp only [iter,Function.iterate_succ_apply]
      congr 3
      rw [← paso_rep R d l]
      push_cast
      ring_nf
    have h0 : ∀ l ∈ Finset.range (2^t),
        f (canon (iter (t+1) (par_rep R ((2*l:ℕ):ℤ))))+f (canon (iter (t+1) (par_rep R ((2*l+1:ℕ):ℤ))))=
          f (canon (iter t (par_rep (sig R 0) l)))+f (canon (iter t (par_rep (sig R 1) l))) := by
      intro l _
      have a := hd 0 l (by norm_num)
      have b := hd 1 l (by norm_num)
      simp only [Nat.add_zero,Nat.cast_zero,Nat.cast_one] at a b
      rw [a,b]
    rw [Finset.sum_congr rfl h0,Finset.sum_add_distrib,ih (sig R 0),ih (sig R 1),
      sig_canon,sig_canon]
    rw [bit_rep R]
    simp only [MomentosGao.promedio]
    cases bit (par_rep R 0) <;> simp only [Bool.not_false,Bool.not_true] <;> ring

/-- Transporte: pares (n,n+1) con n<2^t frente a la cadena desde (0,1). -/
theorem transporte (f : Estado → ℝ) (t : ℕ) :
    ∑ n ∈ Finset.range (2^t),f (canon (iter t ⟨n,n+1,0,0⟩))=
      (2:ℝ)^t*MomentosGao.promedio paso f t (.vivo 0 1) := by
  have h := suma_rep f t ⟨0,0,0,1⟩
  have e : ∀ m : ℤ, par_rep ⟨0,0,0,1⟩ m=⟨m,m+1,0,0⟩ := by
    intro m; simp [par_rep]
  have c0 : canon (par_rep ⟨0,0,0,1⟩ 0)=.vivo 0 1 := by
    rw [e]; rw [canon_ancla _ (by unfold anclax; dsimp only; omega)]; norm_num
  rw [c0] at h
  simp only [e] at h
  exact h

/-! ## Periodicidad: el estado a tiempo t sólo depende de n módulo 2^t -/

theorem iter_rep (t : ℕ) : ∀ (R : Rep) (r : ℕ), ∃ R' : Rep, ∀ m' : ℤ,
    iter t (par_rep R (2^t*m'+r))=par_rep R' m' := by
  induction t with
  | zero =>
    intro R r
    refine ⟨⟨R.p,3^R.p*r+R.a,R.q,3^R.q*r+R.b⟩,fun m' => ?_⟩
    simp only [iter,Function.iterate_zero,id,pow_zero,one_mul,par_rep]
    congr 1 <;> ring
  | succ t ih =>
    intro R r
    obtain ⟨R',hR'⟩ := ih (sig R (r%2:ℕ)) (r/2)
    refine ⟨R',fun m' => ?_⟩
    have e : (2:ℤ)^(t+1)*m'+(r:ℤ)=2*(2^t*m'+((r/2:ℕ):ℤ))+((r%2:ℕ):ℤ) := by
      have hr : (r:ℤ)=2*((r/2:ℕ):ℤ)+((r%2:ℕ):ℤ) := by omega
      rw [pow_succ]
      linarith
    simp only [iter,Function.iterate_succ_apply] at hR' ⊢
    rw [e,paso_rep]
    exact hR' m'

theorem canon_modulo (t n : ℕ) :
    canon (iter t ⟨n,n+1,0,0⟩)=canon (iter t ⟨(n%2^t:ℕ),(n%2^t:ℕ)+1,0,0⟩) := by
  have e : ∀ m : ℤ, par_rep ⟨0,0,0,1⟩ m=⟨m,m+1,0,0⟩ := by intro m; simp [par_rep]
  obtain ⟨R',hR'⟩ := iter_rep t ⟨0,0,0,1⟩ (n%2^t)
  have h1 := hR' ((n/2^t:ℕ):ℤ)
  have h0 := hR' 0
  have hn : (2:ℤ)^t*((n/2^t:ℕ):ℤ)+((n%2^t:ℕ):ℤ)=(n:ℤ) := by
    have := Nat.div_add_mod n (2^t)
    exact_mod_cast this
  rw [hn,e] at h1
  rw [mul_zero,zero_add,e] at h0
  rw [h1,h0,canon_rep R' ((n/2^t:ℕ):ℤ)]

/-! ## Del mapa atajo al mapa clásico -/

def collatz (n : ℕ) : ℕ := if n%2=0 then n/2 else 3*n+1

theorem Tm_collatz (n : ℕ) :
    Tm (n:ℤ)=((if n%2=0 then collatz n else collatz (collatz n) : ℕ):ℤ) ∧
      imp (n:ℤ)=(if n%2=0 then 0 else 1) := by
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · have hz : (n:ℤ)%2=0 := by exact_mod_cast congrArg (fun k : ℕ => (k:ℤ)) h
    simp only [h,if_true,Tm_par _ hz,imp_par _ hz,collatz]
    constructor
    · push_cast; rfl
    · trivial
  · have hz : (n:ℤ)%2=1 := by exact_mod_cast congrArg (fun k : ℕ => (k:ℤ)) h
    have h2 : (3*n+1)%2=0 := by omega
    simp only [show ¬(n%2=0) by omega,if_false,Tm_impar _ hz,imp_impar _ hz,collatz,h2,if_true]
    constructor
    · push_cast
      have : (3*(n:ℤ)+1)/2=((3*n+1)/2:ℕ) := by push_cast; omega
      exact this
    · trivial

/-- Tras t pasos del atajo, cada miembro es un iterado clásico con t+(impares) pasos. -/
theorem iter_collatz (t : ℕ) : ∀ n m : ℕ, ∃ p q : ℕ,
    iter t ⟨n,m,0,0⟩=⟨((collatz^[t+p] n : ℕ):ℤ),((collatz^[t+q] m : ℕ):ℤ),p,q⟩ ∧ p≤t ∧ q≤t := by
  induction t with
  | zero =>
    intro n m
    exact ⟨0,0,by simp [iter],le_refl _,le_refl _⟩
  | succ t ih =>
    intro n m
    obtain ⟨p,q,h,hp,hq⟩ := ih n m
    obtain ⟨hx1,hx2⟩ := Tm_collatz (collatz^[t+p] n)
    obtain ⟨hy1,hy2⟩ := Tm_collatz (collatz^[t+q] m)
    have hs : iter (t+1) ⟨n,m,0,0⟩=paso_par (iter t ⟨n,m,0,0⟩) := by
      simp only [iter,Function.iterate_succ_apply']
    rw [hs,h]
    simp only [paso_par,hx1,hx2,hy1,hy2]
    refine ⟨p+(if collatz^[t+p] n%2=0 then 0 else 1),q+(if collatz^[t+q] m%2=0 then 0 else 1),?_,?_,?_⟩
    · congr 1
      · split
        · rw [show t+1+(p+0)=(t+p)+1 by ring,Function.iterate_succ_apply']
        · rw [show t+1+(p+1)=(t+p)+1+1 by ring,Function.iterate_succ_apply',
            Function.iterate_succ_apply']
      · split
        · rw [show t+1+(q+0)=(t+q)+1 by ring,Function.iterate_succ_apply']
        · rw [show t+1+(q+1)=(t+q)+1+1 by ring,Function.iterate_succ_apply',
            Function.iterate_succ_apply']
    · split <;> omega
    · split <;> omega

theorem fusion_clasica (t n : ℕ) (h : canon (iter t ⟨n,n+1,0,0⟩)=.fusion) :
    ∃ k, k≤2*t ∧ collatz^[k] n=collatz^[k] (n+1) := by
  obtain ⟨p,q,e,hp,hq⟩ := iter_collatz t n (n+1)
  have hf : (iter t ⟨n,n+1,0,0⟩).p=(iter t ⟨n,n+1,0,0⟩).q ∧
      (iter t ⟨n,n+1,0,0⟩).x=(iter t ⟨n,n+1,0,0⟩).y := by
    by_contra hne
    unfold canon at h
    rw [if_neg hne] at h
    split at h <;> simp at h
  have e' : ((n:ℤ))=(n:ℤ) := rfl
  rw [show ((n+1:ℕ):ℤ)=(n:ℤ)+1 by push_cast; rfl] at e
  rw [e] at hf
  obtain ⟨hpq,hxy⟩ := hf
  dsimp only at hpq hxy
  subst hpq
  exact ⟨t+p,by omega,by exact_mod_cast hxy⟩

/-! ## Conteo por bloques y densidad -/

open Classical in
theorem conteo_bloques (N M : ℕ) (hM : 0<M) (S : Finset ℕ) (hS : S ⊆ Finset.range M) :
    (N/M)*S.card≤((Finset.range N).filter (fun n => n%M ∈ S)).card := by
  have hinj : Set.InjOn (fun jr : ℕ × ℕ => jr.1*M+jr.2) ↑(Finset.range (N/M) ×ˢ S) := by
    rintro ⟨j1,r1⟩ h1 ⟨j2,r2⟩ h2 heq
    simp only [Finset.coe_product,Set.mem_prod,Finset.mem_coe,Finset.mem_range] at h1 h2
    have hr1 := Finset.mem_range.mp (hS h1.2)
    have hr2 := Finset.mem_range.mp (hS h2.2)
    simp only at heq
    have hm1 : (j1*M+r1)%M=r1 := by rw [Nat.mul_comm,Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hr1
    have hm2 : (j2*M+r2)%M=r2 := by rw [Nat.mul_comm,Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hr2
    have hr : r1=r2 := by rw [← hm1,← hm2,heq]
    subst hr
    have hj : j1*M=j2*M := by omega
    have := Nat.eq_of_mul_eq_mul_right hM hj
    subst this
    rfl
  have hsub : (Finset.range (N/M) ×ˢ S).image (fun jr : ℕ × ℕ => jr.1*M+jr.2) ⊆
      (Finset.range N).filter (fun n => n%M ∈ S) := by
    intro n hn
    simp only [Finset.mem_image,Finset.mem_product,Finset.mem_range] at hn
    obtain ⟨⟨j,r⟩,⟨hj,hr⟩,rfl⟩ := hn
    have hrM := Finset.mem_range.mp (hS hr)
    simp only [Finset.mem_filter,Finset.mem_range]
    constructor
    · have h1 : (j+1)*M≤(N/M)*M := Nat.mul_le_mul_right _ hj
      have h2 := Nat.div_mul_le_self N M
      rw [Nat.succ_mul] at h1
      omega
    · rw [Nat.mul_comm,Nat.mul_add_mod,Nat.mod_eq_of_lt hrM]; exact hr
  have hc := Finset.card_le_card hsub
  rw [Finset.card_image_of_injOn hinj,Finset.card_product,Finset.card_range] at hc
  exact hc

/-- El conjunto de Gao: n y n+1 se encuentran en a lo sumo log2 n pasos clásicos. -/
def gao_encuentro (n : ℕ) : Prop := ∃ k, k≤Nat.log 2 n ∧ collatz^[k] n=collatz^[k] (n+1)

open Classical in
/-- Conjetura de Gao (1993), según Lagarias: densidad natural uno. -/
theorem gao (ε : ℝ) (hε : 0<ε) : ∃ N0 : ℕ, ∀ N, N0≤N →
    (1-ε)*(N:ℝ)≤(((Finset.range N).filter gao_encuentro).card:ℝ) := by
  obtain ⟨t,ht⟩ := MartasGao.martas (ε/2) (by linarith)
  have hPt := ht t le_rfl
  set S := (Finset.range (2^t)).filter
    (fun r : ℕ => canon (iter t ⟨(r:ℤ),(r:ℤ)+1,0,0⟩)=.fusion) with hSdef
  -- |S| = 2^t * P(fusión hasta t)
  have hS : (S.card:ℝ)=(2:ℝ)^t*EnsayoGao.probabilidad_fusion t (.vivo 0 1) := by
    have h := transporte EnsayoGao.fusion t
    unfold EnsayoGao.probabilidad_fusion
    rw [← h,hSdef,Finset.card_filter]
    push_cast
    apply Finset.sum_congr rfl
    intro n _
    unfold EnsayoGao.fusion
    split <;> simp_all
  have hS2 : (2:ℝ)^t*(1-ε/2)≤S.card := by
    rw [hS]
    have : 0<(2:ℝ)^t := by positivity
    nlinarith
  refine ⟨Nat.ceil (2*((2:ℝ)^t+(4:ℝ)^t)/ε),fun N hN => ?_⟩
  have hNr : 2*((2:ℝ)^t+(4:ℝ)^t)/ε≤N := le_trans (Nat.le_ceil _) (by exact_mod_cast hN)
  -- inclusión: clase fusionada y n>=4^t implica encuentro de Gao
  have hsub : ((Finset.range N).filter (fun n => n%2^t ∈ S)).filter (fun n => 4^t≤n) ⊆
      (Finset.range N).filter gao_encuentro := by
    intro n hn
    simp only [Finset.mem_filter,Finset.mem_range] at hn ⊢
    obtain ⟨⟨hnN,hmod⟩,h4⟩ := hn
    refine ⟨hnN,?_⟩
    have hc : canon (iter t ⟨n,n+1,0,0⟩)=.fusion := by
      rw [canon_modulo]
      simp only [hSdef,Finset.mem_filter] at hmod
      push_cast at hmod ⊢
      exact hmod.2
    obtain ⟨k,hk,hkeq⟩ := fusion_clasica t n hc
    refine ⟨k,?_,hkeq⟩
    have hlog : 2*t≤Nat.log 2 n := by
      apply Nat.le_log_of_pow_le (by norm_num)
      rw [pow_mul]
      norm_num
      exact h4
    omega
  have hcb := conteo_bloques N (2^t) (by positivity) S (Finset.filter_subset _ _)
  -- los n<4^t son a lo sumo 4^t
  have hpeq : ((Finset.range N).filter (fun n => n%2^t ∈ S)).card≤
      (((Finset.range N).filter (fun n => n%2^t ∈ S)).filter (fun n => 4^t≤n)).card+4^t := by
    have hsplit := Finset.filter_card_add_filter_neg_card_eq_card
      (s:=(Finset.range N).filter (fun n => n%2^t ∈ S)) (fun n => 4^t≤n)
    have hsmall : (((Finset.range N).filter (fun n => n%2^t ∈ S)).filter (fun n => ¬4^t≤n)).card≤4^t := by
      calc _ ≤ (Finset.range (4^t)).card := by
            apply Finset.card_le_card
            intro n hn
            simp only [Finset.mem_filter,Finset.mem_range] at hn ⊢
            omega
        _ = 4^t := Finset.card_range _
    omega
  have hmain : ((N/2^t)*S.card:ℕ)≤(((Finset.range N).filter gao_encuentro).card)+4^t := by
    have := Finset.card_le_card hsub
    omega
  -- aritmética real
  have hdiv : ((N:ℝ)/(2:ℝ)^t-1)≤((N/2^t:ℕ):ℝ) := by
    have h := Nat.lt_div_mul_add (a:=N) (b:=2^t) (by positivity)
    have h' : (N:ℝ)<((N/2^t:ℕ):ℝ)*(2:ℝ)^t+(2:ℝ)^t := by exact_mod_cast h
    have hp : (0:ℝ)<2^t := by positivity
    rw [div_sub_one (ne_of_gt hp),div_le_iff₀ hp]
    linarith
  have hmainr : (((N/2^t:ℕ):ℝ))*(S.card:ℝ)≤(((Finset.range N).filter gao_encuentro).card:ℝ)+(4:ℝ)^t := by
    exact_mod_cast hmain
  have hp : (0:ℝ)<2^t := by positivity
  have hcard0 : (0:ℝ)≤S.card := Nat.cast_nonneg _
  have hSle : (S.card:ℝ)≤(2:ℝ)^t := by
    have : S.card≤2^t := by
      calc S.card ≤ (Finset.range (2^t)).card := Finset.card_le_card (Finset.filter_subset _ _)
        _ = 2^t := Finset.card_range _
    exact_mod_cast this
  have hlow : ((N:ℝ)/(2:ℝ)^t-1)*(S.card:ℝ)≤(((Finset.range N).filter gao_encuentro).card:ℝ)+(4:ℝ)^t :=
    le_trans (mul_le_mul_of_nonneg_right hdiv hcard0) hmainr
  have hexp : ((N:ℝ)/(2:ℝ)^t-1)*(S.card:ℝ)=(N:ℝ)*((S.card:ℝ)/(2:ℝ)^t)-S.card := by
    field_simp
  have hfrac : 1-ε/2≤(S.card:ℝ)/(2:ℝ)^t := by
    rw [le_div_iff₀ hp]; linarith
  have hNpos : (0:ℝ)≤N := Nat.cast_nonneg _
  have hNε : 2*((2:ℝ)^t+(4:ℝ)^t)≤ε*N := by
    rw [div_le_iff₀ hε] at hNr; linarith
  nlinarith

end TejonasGao

#print axioms TejonasGao.canon_paso
#print axioms TejonasGao.suma_rep
#print axioms TejonasGao.transporte
#print axioms TejonasGao.canon_modulo
#print axioms TejonasGao.iter_collatz
#print axioms TejonasGao.fusion_clasica
#print axioms TejonasGao.conteo_bloques
#print axioms TejonasGao.gao
