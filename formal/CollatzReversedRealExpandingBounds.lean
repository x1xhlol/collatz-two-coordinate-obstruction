import CollatzReversedRealExpandingPrefix

namespace CollatzResearch.RealExpandingBounds

open Matrix CollatzCertificate RealAffine

set_option maxHeartbeats 1000000

theorem map_binaryInterp {α β : Type*} (f : α → β) (a b : α → α) (A B : β → β)
    (ha : ∀ x, f (a x)=A (f x)) (hb : ∀ x, f (b x)=B (f x)) (n : ℕ) (x : α) :
    f (ReversedCertificate.binaryInterp a b n x)=
      ReversedCertificate.binaryInterp A B n (f x) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    conv_lhs => rw [ReversedCertificate.binaryInterp]
    conv_rhs => rw [ReversedCertificate.binaryInterp]
    by_cases hn : n≤1
    · simp only [hn,reduceIte]
    · simp only [hn,reduceIte]
      have hd : n/2<n := by omega
      split_ifs <;> simp only [ha,hb,ih (n/2) hd]

theorem real_ternary_conversion (A B C D E F G : Affine (Fin 2))
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G) (n : ℕ) (hn : 0<n) :
    ReversedCertificate.binaryInterp (eval A) (eval B) (3*n) C.offset ≤
      eval E (ReversedCertificate.binaryInterp (eval A) (eval B) n C.offset) ∧
    ReversedCertificate.binaryInterp (eval A) (eval B) (3*n+1) C.offset ≤
      eval F (ReversedCertificate.binaryInterp (eval A) (eval B) n C.offset) ∧
    ReversedCertificate.binaryInterp (eval A) (eval B) (3*n+2) C.offset ≤
      eval G (ReversedCertificate.binaryInterp (eval A) (eval B) n C.offset) := by
  let c : ReversedCertificate.Data {x : Vec (Fin 2) // 0 ≤ x} := {
    a := fun x => ⟨eval A x.1,eval_nonnegative hA x.2⟩
    b := fun x => ⟨eval B x.1,eval_nonnegative hB x.2⟩
    e := fun x => ⟨eval E x.1,eval_nonnegative hE x.2⟩
    f := fun x => ⟨eval F x.1,eval_nonnegative hF x.2⟩
    g := fun x => ⟨eval G x.1,eval_nonnegative hG x.2⟩
    initial := ⟨C.offset,hC.2⟩
    readout := fun _ => 0
    a_monotone := fun _ _ hx => eval_monotone hA.1 hx
    b_monotone := fun _ _ hx => eval_monotone hB.1 hx
    readout_monotone := fun _ _ _ => le_rfl
    ea := fun x => by simpa only [eval_comp] using eval_weak h.ea x.2
    fa := fun x => by simpa only [eval_comp] using eval_weak h.fa x.2
    ga := fun x => by simpa only [eval_comp] using eval_weak h.ga x.2
    eb := fun x => by simpa only [eval_comp] using eval_weak h.eb x.2
    fb := fun x => by simpa only [eval_comp] using eval_weak h.fb x.2
    gb := fun x => by simpa only [eval_comp] using eval_weak h.gb x.2
    ec := h.ec.2
    fc := h.fc.2
    gc := h.gc.2
  }
  have hm (k : ℕ) :
      (ReversedCertificate.binaryInterp c.a c.b k c.initial).1=
      ReversedCertificate.binaryInterp (eval A) (eval B) k C.offset :=
    map_binaryInterp Subtype.val c.a c.b (eval A) (eval B)
      (fun _ => rfl) (fun _ => rfl) k c.initial
  have hh := ReversedCertificate.ternary_conversion_weak c n hn
  change (ReversedCertificate.binaryInterp c.a c.b (3*n) c.initial).1 ≤
      eval E (ReversedCertificate.binaryInterp c.a c.b n c.initial).1 ∧
    (ReversedCertificate.binaryInterp c.a c.b (3*n+1) c.initial).1 ≤
      eval F (ReversedCertificate.binaryInterp c.a c.b n c.initial).1 ∧
    (ReversedCertificate.binaryInterp c.a c.b (3*n+2) c.initial).1 ≤
      eval G (ReversedCertificate.binaryInterp c.a c.b n c.initial).1 at hh
  simpa only [hm] using hh

theorem vector_bounded_by_positive_ray (x u : Vec (Fin 2)) (hu : ∀ i, 0<u i) :
    ∃ K : ℝ, 0≤K ∧ x≤K • u := by
  let K := max 0 (max (x 0/u 0) (x 1/u 1))
  refine ⟨K,le_max_left _ _,?_⟩
  intro i
  fin_cases i
  · exact (div_le_iff₀ (hu 0)).mp (le_trans (le_max_left _ _) (le_max_right _ _))
  · exact (div_le_iff₀ (hu 1)).mp (le_trans (le_max_right _ _) (le_max_right _ _))

theorem eval_upper_on_ray (T : Affine (Fin 2)) (u : Vec (Fin 2)) (l M s : ℝ)
    (hmat : T.matrix *ᵥ u≤l • u) (hoff : T.offset≤M • u) (hs : 0≤s) :
    eval T (s • u)≤(l*s+M) • u := by
  intro i
  have hm := mul_le_mul_of_nonneg_left (hmat i) hs
  have ho := hoff i
  simp only [eval,Matrix.mulVec_smul,Pi.add_apply,Pi.smul_apply,smul_eq_mul] at hm ho ⊢
  nlinarith only [hm,ho]

theorem ternary_window_upper_bound (A B C D E F G : Affine (Fin 2))
    (hA : A.Nonnegative) (hB : B.Nonnegative) (hC : C.Nonnegative)
    (hE : E.Nonnegative) (hF : F.Nonnegative) (hG : G.Nonnegative)
    (h : ReversedRealWeak A B C D E F G)
    (u : Vec (Fin 2)) (l K M : ℝ) (hu : 0≤u) (hl : 1≤l) (hK : 0≤K) (hM : 0≤M)
    (hinit : C.offset≤K • u)
    (hEmat : E.matrix *ᵥ u≤l • u) (hFmat : F.matrix *ᵥ u≤l • u)
    (hGmat : G.matrix *ᵥ u≤l • u)
    (hEoff : E.offset≤M • u) (hFoff : F.offset≤M • u) (hGoff : G.offset≤M • u)
    (k n : ℕ) (hlo : 3^k≤n) (hhi : n<2*3^k) :
    ReversedCertificate.binaryInterp (eval A) (eval B) n C.offset≤
      ((K+(k:ℝ)*M)*l^k) • u := by
  induction k generalizing n with
  | zero =>
    have hn : n=1 := by simp only [pow_zero] at hlo hhi; omega
    subst n
    simpa only [ReversedCertificate.binaryInterp_one,Nat.cast_zero,zero_mul,
      add_zero,pow_zero,mul_one] using hinit
  | succ k ih =>
    have hlo' : 3^k≤n/3 := by rw [pow_succ] at hlo; omega
    have hhi' : n/3<2*3^k := by rw [pow_succ] at hhi; omega
    have hq : 0<n/3 := lt_of_lt_of_le (pow_pos (by decide) k) hlo'
    have hb := ih (n/3) hlo' hhi'
    have hc := real_ternary_conversion A B C D E F G hA hB hC hE hF hG h (n/3) hq
    have hs : 0≤(K+(k:ℝ)*M)*l^k :=
      mul_nonneg (add_nonneg hK (mul_nonneg (Nat.cast_nonneg k) hM))
        (pow_nonneg (le_trans (by norm_num) hl) k)
    have hpow : 1≤l^(k+1) := one_le_pow₀ hl
    have hscalar : l*((K+(k:ℝ)*M)*l^k)+M≤(K+((k+1:ℕ):ℝ)*M)*l^(k+1) := by
      rw [Nat.cast_add,Nat.cast_one,pow_succ] at *
      nlinarith only [mul_nonneg hM (sub_nonneg.mpr hpow)]
    have hbound (T : Affine (Fin 2)) (hT : T.Nonnegative)
        (hmat : T.matrix *ᵥ u≤l • u) (hoff : T.offset≤M • u) :
        eval T (ReversedCertificate.binaryInterp (eval A) (eval B) (n/3) C.offset)≤
          ((K+((k+1:ℕ):ℝ)*M)*l^(k+1)) • u := by
      apply le_trans (eval_monotone hT.1 hb)
      apply le_trans (eval_upper_on_ray T u l M _ hmat hoff hs)
      intro i
      exact mul_le_mul_of_nonneg_right hscalar (hu i)
    have hmod : n%3=0 ∨ n%3=1 ∨ n%3=2 := by omega
    rcases hmod with hr | hr | hr
    · have hn : n=3*(n/3) := by omega
      rw [hn]
      exact le_trans hc.1 (hbound E hE hEmat hEoff)
    · have hn : n=3*(n/3)+1 := by omega
      rw [hn]
      exact le_trans hc.2.1 (hbound F hF hFmat hFoff)
    · have hn : n=3*(n/3)+2 := by omega
      rw [hn]
      exact le_trans hc.2.2 (hbound G hG hGmat hGoff)

end CollatzResearch.RealExpandingBounds

#print axioms CollatzResearch.RealExpandingBounds.map_binaryInterp
#print axioms CollatzResearch.RealExpandingBounds.real_ternary_conversion
#print axioms CollatzResearch.RealExpandingBounds.vector_bounded_by_positive_ray
#print axioms CollatzResearch.RealExpandingBounds.eval_upper_on_ray
#print axioms CollatzResearch.RealExpandingBounds.ternary_window_upper_bound
