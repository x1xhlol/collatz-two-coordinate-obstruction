import ParametrosVentana

/- Palabras de absorción para la transición entera original.
   Se conserva el signo del offset y sólo se normaliza el gap en k=0. -/

namespace HormigasGao

open CadenaCompletaGao RestoGao PalabrasGao

theorem mag_mitad (c : ℤ) (hc : c%2=0) : 2*mag (c/2)=mag c := by
  unfold mag
  split <;> split <;> omega

theorem dividir_offset (m : ℕ) (c : ℤ) (hc : c≠0) (hm : mag c<(2:ℤ)^m) :
    ∃ bs d, bs.length≤m ∧ d%2=1 ∧ mag d≤mag c ∧
      (c<0 → d<0) ∧ recorre paso bs (.vivo 1 c)=.vivo 1 d := by
  induction m generalizing c with
  | zero => simp only [pow_zero] at hm; unfold mag at hm; split at hm <;> omega
  | succ m ih =>
    by_cases hp : c%2=0
    · have he := mag_mitad c hp
      have hn : c/2≠0 := by omega
      have hlim : mag (c/2)<(2:ℤ)^m := by rw [pow_succ] at hm; omega
      obtain ⟨bs,d,hl,hd,hmag,hneg,hrec⟩ := ih (c/2) hn hlim
      refine ⟨false::bs,d,by simp; omega,hd,?_,?_,?_⟩
      · have hpos := mag_no_negativa (c/2); omega
      · intro h; exact hneg (by omega)
      · simpa [recorre, paso, hp] using hrec
    · exact ⟨[],c,by simp,by omega,le_rfl,fun h => h,rfl⟩

theorem gap_uno : recorre paso [false,false,true] (.vivo 0 1)=.fusion := by
  decide

/- Un viaje consume a lo sumo m+3 bits y reduce el gap por 5/6,
   salvo que ya alcance la fusión. -/
theorem viaje (m : ℕ) (g : ℤ) (hg : 1≤g) (hm : g<(2:ℤ)^m) :
    ∃ bs z, bs.length≤m+3 ∧ recorre paso bs (.vivo 0 g)=z ∧
      (z=.fusion ∨ ∃ d, 1≤d ∧ d≤g ∧ 6*d≤5*g ∧ z=.vivo 0 d) := by
  by_cases h1 : g=1
  · subst g
    exact ⟨[false,false,true],.fusion,by simp,gap_uno,Or.inl rfl⟩
  by_cases hp : g%2=0
  · refine ⟨[false],.vivo 0 (g/2),by simp,by simp [recorre,paso,hp],Or.inr ?_⟩
    exact ⟨g/2,by omega,by omega,by omega,rfl⟩
  · have h3 : 3≤g := by omega
    let c : ℤ := (1-3*g)/2
    have hc : c<0 := by dsimp [c]; omega
    have hmag : mag c<(2:ℤ)^(m+1) := by
      dsimp [c]
      rw [pow_succ]
      unfold mag
      split <;> omega
    obtain ⟨bs,d,hl,hd,hmd,hneg,hrec⟩ := dividir_offset (m+1) c (by omega) hmag
    have hdneg := hneg hc
    have hde : d≠1 := by omega
    have hpar : d%2≠0 := by omega
    let nuevo : ℤ := mag ((d-1)/2)
    have hn : 1≤nuevo ∧ nuevo≤g ∧ 6*nuevo≤5*g := by
      have hm' : -d ≤ -c := by simpa [mag,hdneg,hc] using hmd
      have hmitad : (d-1)/2<0 := by omega
      simp only [nuevo,mag,if_pos hmitad]
      dsimp [c] at hm'
      omega
    refine ⟨true::(bs++[true]),.vivo 0 nuevo,?_,?_,Or.inr ⟨nuevo,hn.1,hn.2.1,hn.2.2,rfl⟩⟩
    · simp only [List.length_cons,List.length_append,List.length_nil]
      omega
    · simp only [recorre,paso,hp,if_false,if_true]
      change recorre paso (bs++[true]) (.vivo 1 c)=.vivo 0 nuevo
      rw [recorre_append,hrec]
      simp [recorre,paso,hpar,hde,nuevo]

theorem viajes (j m : ℕ) (g : ℤ) (hg : 1≤g) (hm : g<(2:ℤ)^m) :
    ∃ bs z, bs.length≤j*(m+3) ∧ recorre paso bs (.vivo 0 g)=z ∧
      (z=.fusion ∨ ∃ d, 1≤d ∧ d≤g ∧ (6:ℤ)^j*d≤5^j*g ∧ z=.vivo 0 d) := by
  induction j generalizing g with
  | zero => exact ⟨[],.vivo 0 g,by simp,rfl,Or.inr ⟨g,hg,le_rfl,by simp,rfl⟩⟩
  | succ j ih =>
    obtain ⟨pre,z,hl,hr,hz⟩ := viaje m g hg hm
    rcases hz with hz | ⟨d,hd,hdg,hcontr,hz⟩
    · refine ⟨pre,z,?_,hr,Or.inl hz⟩
      nlinarith
    · rw [hz] at hr
      obtain ⟨post,w,hlp,hrp,hw⟩ := ih d hd (lt_of_le_of_lt hdg hm)
      refine ⟨pre++post,w,?_,?_,?_⟩
      · simp only [List.length_append]
        nlinarith
      · rw [recorre_append,hr,hrp]
      · rcases hw with hw | ⟨e,he,hed,hpow,hw⟩
        · exact Or.inl hw
        · refine Or.inr ⟨e,he,hed.trans hdg,?_,hw⟩
          have h5 := mul_le_mul_of_nonneg_left hcontr (pow_nonneg (by norm_num : (0:ℤ)≤5) j)
          have h6 := mul_le_mul_of_nonneg_left hpow (by norm_num : (0:ℤ)≤6)
          rw [pow_succ,pow_succ]
          nlinarith

theorem absorcion_gap (m : ℕ) (g : ℤ) (hg : 1≤g) (hm : g<(2:ℤ)^m) :
    ∃ bs, bs.length≤4*m*(m+3)+3 ∧ recorre paso bs (.vivo 0 g)=.fusion := by
  induction m generalizing g with
  | zero => norm_num at hm; omega
  | succ m ih =>
    obtain ⟨pre,z,hl,hr,hz⟩ := viajes 4 (m+1) g hg hm
    rcases hz with hz | ⟨d,hd,_,hcontr,hz⟩
    · refine ⟨pre,?_,hr.trans hz⟩
      nlinarith
    · have hsmall : d<(2:ℤ)^m := by
        norm_num at hcontr
        rw [pow_succ] at hm
        have hpos : 0<(2:ℤ)^m := pow_pos (by decide) _
        omega
      obtain ⟨post,hlp,hrp⟩ := ih d hd hsmall
      refine ⟨pre++post,?_,?_⟩
      · simp only [List.length_append]
        nlinarith
      · rw [recorre_append,hr,hz,hrp]

theorem absorcion_offset (m : ℕ) (c : ℤ) (hm : mag c<(2:ℤ)^m) :
    ∃ bs, bs.length≤16*(m+1)^2 ∧ recorre paso bs (.vivo 1 c)=.fusion := by
  by_cases hc : c=0
  · subst c
    refine ⟨[true,true,false,false,true],?_,by decide⟩
    simp only [List.length_cons,List.length_nil]
    have hp : 0<(m+1)^2 := by positivity
    omega
  obtain ⟨pre,d,hl,hd,hmag,_,hr⟩ := dividir_offset m c hc hm
  by_cases h1 : d=1
  · refine ⟨pre++[true],?_,?_⟩
    · simp only [List.length_append,List.length_cons,List.length_nil]
      nlinarith
    · rw [recorre_append,hr,h1]
      decide
  · let g : ℤ := mag ((d-1)/2)
    have hg : 1≤g ∧ g≤mag d := by
      dsimp [g]
      unfold mag
      split <;> split <;> omega
    obtain ⟨post,hlp,hrp⟩ := absorcion_gap m g hg.1 (lt_of_le_of_lt (hg.2.trans hmag) hm)
    refine ⟨pre++(true::post),?_,?_⟩
    · simp only [List.length_append,List.length_cons]
      nlinarith
    · rw [recorre_append,hr]
      simpa [recorre,paso,show ¬d%2=0 by omega,h1,g] using hrp

def longitud (c : ℤ) : ℕ := 16*(Nat.clog 2 (2+c.natAbs)+1)^2

theorem longitud_mono (c : ℤ) (G : ℕ) (hc : c.natAbs≤G) :
    longitud c ≤ 16*(Nat.clog 2 (G+2)+1)^2 := by
  have hlog := Nat.clog_mono_right 2 (show 2+c.natAbs≤G+2 by omega)
  exact Nat.mul_le_mul_left 16 (Nat.pow_le_pow_left (by omega) 2)

theorem palabra_hormigas (c : ℤ) :
    ∃ bs, bs.length≤longitud c ∧ recorre paso bs (.vivo 1 c)=.fusion := by
  have h := Nat.le_pow_clog (by decide : 1<2) (2+c.natAbs)
  have he : mag c=(c.natAbs:ℤ) := by
    rw [Int.natCast_natAbs]
    unfold mag
    split <;> simp_all [abs_of_neg,abs_of_nonneg]
  apply absorcion_offset (Nat.clog 2 (2+c.natAbs)) c
  rw [he]
  exact_mod_cast (show c.natAbs<2^Nat.clog 2 (2+c.natAbs) by omega)

#print axioms dividir_offset
#print axioms viaje
#print axioms viajes
#print axioms absorcion_gap
#print axioms absorcion_offset
#print axioms palabra_hormigas

end HormigasGao
