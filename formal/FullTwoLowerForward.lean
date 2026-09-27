import FullTwoBasic
import FullTwoLowerScalar

namespace CollatzResearch.FullTwoLower

open Matrix CollatzCertificate FullTwo

theorem comp_offset_entry (X Y : Aff2) (i : Fin 2) :
    (X.comp Y).offset i = X.matrix i 0 * Y.offset 0 +
      X.matrix i 1 * Y.offset 1 + X.offset i := by
  simp only [Affine.comp, Pi.add_apply, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem comp_matrix_entry (X Y : Aff2) (i j : Fin 2) :
    (X.comp Y).matrix i j = X.matrix i 0 * Y.matrix 0 j +
      X.matrix i 1 * Y.matrix 1 j := by
  simp only [Affine.comp, Matrix.mul_apply, Fin.sum_univ_two]

theorem lower_forward_parameters
    (qa qb qe qf qg za zb ze zf zg ha hb he hf hg ka kb ke kf kg : ℝ)
    (C D : Aff2)
    (hA : Admissible (lower qa za ha ka))
    (hB : Admissible (lower qb zb hb kb))
    (hC : Admissible C) (hD : Admissible D)
    (hE : Admissible (lower qe ze he ke))
    (hF : Admissible (lower qf zf hf kf))
    (hG : Admissible (lower qg zg hg kg))
    (hw : ForwardWeak (lower qa za ha ka) (lower qb zb hb kb) C D
      (lower qe ze he ke) (lower qf zf hf kf) (lower qg zg hg kg)) :
    ForwardGapsZero (lower qa za ha ka) (lower qb zb hb kb) C D
      (lower qe ze he ke) (lower qf zf hf kf) (lower qg zg hg kg) := by
  have nqa : 0 ≤ qa := by simpa [lower] using hA.1.1 1 0
  have nqb : 0 ≤ qb := by simpa [lower] using hB.1.1 1 0
  have nqe : 0 ≤ qe := by simpa [lower] using hE.1.1 1 0
  have nqf : 0 ≤ qf := by simpa [lower] using hF.1.1 1 0
  have nqg : 0 ≤ qg := by simpa [lower] using hG.1.1 1 0
  have nza : 0 ≤ za := by simpa [lower] using hA.1.1 1 1
  have nzb : 0 ≤ zb := by simpa [lower] using hB.1.1 1 1
  have nze : 0 ≤ ze := by simpa [lower] using hE.1.1 1 1
  have nzf : 0 ≤ zf := by simpa [lower] using hF.1.1 1 1
  have nzg : 0 ≤ zg := by simpa [lower] using hG.1.1 1 1
  have nha : 0 ≤ ha := by simpa [lower] using hA.1.2 0
  have nhb : 0 ≤ hb := by simpa [lower] using hB.1.2 0
  have nhe : 0 ≤ he := by simpa [lower] using hE.1.2 0
  have nhf : 0 ≤ hf := by simpa [lower] using hF.1.2 0
  have nhg : 0 ≤ hg := by simpa [lower] using hG.1.2 0
  have nka : 0 ≤ ka := by simpa [lower] using hA.1.2 1
  have nkb : 0 ≤ kb := by simpa [lower] using hB.1.2 1
  have nke : 0 ≤ ke := by simpa [lower] using hE.1.2 1
  have nkf : 0 ≤ kf := by simpa [lower] using hF.1.2 1
  have nkg : 0 ≤ kg := by simpa [lower] using hG.1.2 1
  have haf₀ := hw.af.2 0
  have hag₀ := hw.ag.2 0
  have hbe₀ := hw.be.2 0
  have hbf₀ := hw.bf.2 0
  simp [comp_offset_entry, lower] at haf₀ hag₀ hbe₀ hbf₀
  have hhe : he = hf := by linarith only [haf₀, hag₀, hbe₀, hbf₀]
  have hhg : hg = hf := by linarith only [haf₀, hag₀, hbe₀, hbf₀]
  have hhb : hb = ha := by linarith only [haf₀, hag₀, hbe₀, hbf₀]
  subst he
  subst hg
  subst hb
  have hru : hf ≤ ha := by
    have h := hw.bd.2 0
    simpa [comp_offset_entry, lower] using h
  let c0 := C.matrix 0 0
  let c1 := C.matrix 0 1
  let d0 := D.matrix 0 0
  let d1 := D.matrix 1 0
  have nc0 : 0 ≤ c0 := hC.1.1 0 0
  have pc0 : 0 < c0 := lt_of_lt_of_le zero_lt_one hC.2
  have nc1 : 0 ≤ c1 := hC.1.1 0 1
  have nd0 : 0 ≤ d0 := hD.1.1 0 0
  have pd0 : 0 < d0 := lt_of_lt_of_le zero_lt_one hD.2
  have nd1 : 0 ≤ d1 := hD.1.1 1 0
  have hce : c0 * ha + c1 * kb ≤ c0 * hf + c1 * ke := by
    have h := hw.ce.2 0
    simpa [c0, c1, comp_offset_entry, lower] using h
  have hcf : c0 * (ha + ha) + c1 * (qa * ha + za * ka + ka) ≤
      c0 * hf + c1 * kf := by
    have h := hw.cf.2 0
    simpa [c0, c1, comp_offset_entry, lower] using h
  have hcg : c0 * (ha + ha) + c1 * (qa * ha + za * kb + ka) ≤
      c0 * hf + c1 * kg := by
    have h := hw.cg.2 0
    simpa [c0, c1, comp_offset_entry, lower] using h
  have finish (hr : ha = 0) (hu : hf = 0)
      (hke : c1 * ke = c1 * kb)
      (hkf : c1 * kf = c1 * (za * ka + ka))
      (hkg : c1 * kg = c1 * (za * kb + ka)) :
      ForwardGapsZero (lower qa za ha ka) (lower qb zb ha kb) C D
        (lower qe ze hf ke) (lower qf zf hf kf) (lower qg zg hf kg) := by
    constructor <;>
      simp [comp_offset_entry, lower, hr, hu]
    · simpa [c1] using hke
    · simpa [c1] using hkf
    · simpa [c1] using hkg
  by_cases hc1 : c1 = 0
  · have hh : c0 * (ha + ha) ≤ c0 * hf := by simpa [hc1] using hcf
    have hh' := le_of_mul_le_mul_left hh pc0
    have hr : ha = 0 := by linarith only [hh', hru, nha]
    have hu : hf = 0 := by linarith only [hru, hr, nhf]
    exact finish hr hu (by simp [hc1]) (by simp [hc1]) (by simp [hc1])
  · have pc1 : 0 < c1 := lt_of_le_of_ne nc1 (Ne.symm hc1)
    have ze_b : zb ≤ ze := by
      have h := hw.ce.1 0 1
      have hh : c1 * zb ≤ c1 * ze := by
        simpa [c1, comp_matrix_entry, lower] using h
      exact le_of_mul_le_mul_left hh pc1
    have zf_aa : za * za ≤ zf := by
      have h := hw.cf.1 0 1
      have hh : c1 * (za * za) ≤ c1 * zf := by
        simpa [c1, comp_matrix_entry, lower] using h
      exact le_of_mul_le_mul_left hh pc1
    have qbe : qb ≤ qe := by
      have h := hw.ce.1 0 0
      have hh : c0 + c1 * qb ≤ c0 + c1 * qe := by
        simpa [c0, c1, comp_matrix_entry, lower] using h
      exact le_of_mul_le_mul_left (by linarith only [hh]) pc1
    have qfaa : za * qa + qa ≤ qf := by
      have h := hw.cf.1 0 0
      have hh : c0 + c1 * (qa + za * qa) ≤ c0 + c1 * qf := by
        simpa [c0, c1, comp_matrix_entry, lower] using h
      have := le_of_mul_le_mul_left (by linarith only [hh] :
        c1 * (qa + za * qa) ≤ c1 * qf) pc1
      linarith only [this]
    have qgab : za * qb + qa ≤ qg := by
      have h := hw.cg.1 0 0
      have hh : c0 + c1 * (qa + za * qb) ≤ c0 + c1 * qg := by
        simpa [c0, c1, comp_matrix_entry, lower] using h
      have := le_of_mul_le_mul_left (by linarith only [hh] :
        c1 * (qa + za * qb) ≤ c1 * qg) pc1
      linarith only [this]
    have zaf := hw.af.1 1 1
    have zag := hw.ag.1 1 1
    have zbe := hw.be.1 1 1
    have zbf := hw.bf.1 1 1
    have qae := hw.ae.1 1 0
    have qaf := hw.af.1 1 0
    have qag := hw.ag.1 1 0
    have qbe' := hw.be.1 1 0
    have qbf := hw.bf.1 1 0
    simp [comp_matrix_entry, lower] at zaf zag zbe zbf qae qaf qag qbe' qbf
    have qbd : zg * d1 + qg * d0 ≤ zb * d1 + qb * d0 := by
      have h := hw.bd.1 1 0
      simpa [d0, d1, comp_matrix_entry, lower,
        add_comm] using h
    have hscalar : FullTwoLowerScalar.ForwardWeak za zb ze zf zg
        (qa * d0) (qb * d0) (qe * d0) (qf * d0) (qg * d0) d1 := by
      refine ⟨nza, nzb, nze, nzf, nzg, mul_nonneg nqa nd0, mul_nonneg nqb nd0,
        mul_nonneg nqe nd0, mul_nonneg nqf nd0, mul_nonneg nqg nd0, nd1,
        ze_b, zf_aa, zaf, zag, zbe, zbf, qbd, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · nlinarith only [mul_le_mul_of_nonneg_right qae nd0]
      · nlinarith only [mul_le_mul_of_nonneg_right qaf nd0]
      · nlinarith only [mul_le_mul_of_nonneg_right qag nd0]
      · nlinarith only [mul_le_mul_of_nonneg_right qbe' nd0]
      · nlinarith only [mul_le_mul_of_nonneg_right qbf nd0]
      · exact mul_le_mul_of_nonneg_right qbe nd0
      · nlinarith only [mul_le_mul_of_nonneg_right qfaa nd0]
      · nlinarith only [mul_le_mul_of_nonneg_right qgab nd0]
    rcases FullTwoLowerScalar.forward_classification hscalar with hqzero | hexception
    · rcases hqzero with ⟨hqa, hqb, hqe, hqf, hqg⟩
      have qa0 : qa = 0 := (mul_eq_zero.mp hqa).resolve_right (ne_of_gt pd0)
      have qb0 : qb = 0 := (mul_eq_zero.mp hqb).resolve_right (ne_of_gt pd0)
      have qe0 : qe = 0 := (mul_eq_zero.mp hqe).resolve_right (ne_of_gt pd0)
      have qf0 : qf = 0 := (mul_eq_zero.mp hqf).resolve_right (ne_of_gt pd0)
      have qg0 : qg = 0 := (mul_eq_zero.mp hqg).resolve_right (ne_of_gt pd0)
      have kr : FullTwoLowerScalar.ForwardWeak za zb ze zf zg ka kb ke kf kg
          (D.offset 1) := by
        refine ⟨nza, nzb, nze, nzf, nzg, nka, nkb, nke, nkf, nkg, hD.1.2 1,
          ze_b, zf_aa, zaf, zag, zbe, zbf, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
        · simpa [comp_offset_entry, lower,
            qb0, qg0] using hw.bd.2 1
        · simpa [comp_offset_entry, lower,
            qa0, qe0] using hw.ae.2 1
        · simpa [comp_offset_entry, lower,
            qa0, qe0] using hw.af.2 1
        · simpa [comp_offset_entry, lower,
            qa0, qf0] using hw.ag.2 1
        · simpa [comp_offset_entry, lower,
            qb0, qf0] using hw.be.2 1
        · simpa [comp_offset_entry, lower,
            qb0, qg0] using hw.bf.2 1
        · apply le_of_mul_le_mul_left (a := c1) _ pc1
          nlinarith only [hce, mul_nonneg nc0 (sub_nonneg.mpr hru)]
        · apply le_of_mul_le_mul_left (a := c1) _ pc1
          have hn : 0 ≤ ha + ha - hf := by linarith only [hru, nha]
          have hh := hcf
          rw [qa0, zero_mul, zero_add] at hh
          nlinarith only [hh, mul_nonneg nc0 hn]
        · apply le_of_mul_le_mul_left (a := c1) _ pc1
          have hn : 0 ≤ ha + ha - hf := by linarith only [hru, nha]
          have hh := hcg
          rw [qa0, zero_mul, zero_add] at hh
          nlinarith only [hh, mul_nonneg nc0 hn]
      obtain ⟨hke, hkf, hkg⟩ := FullTwoLowerScalar.forward_gaps_zero kr
      have hh : c0 * (ha + ha) ≤ c0 * hf := by
        have hh := hcf
        rw [qa0, zero_mul, zero_add, hkf] at hh
        linarith only [hh]
      have hh' := le_of_mul_le_mul_left hh pc0
      have hr : ha = 0 := by linarith only [hh', hru, nha]
      have hu : hf = 0 := by linarith only [hru, hr, nhf]
      exact finish hr hu (congrArg (c1 * ·) hke) (congrArg (c1 * ·) hkf)
        (congrArg (c1 * ·) hkg)
    · rcases hexception with ⟨za0, zb0, ze0, zf0, zg0, hqapos, hqb, hqe, hqf, hqg⟩
      have qb_eq : qb = qa := mul_right_cancel₀ (ne_of_gt pd0) hqb
      have qe_eq : qe = qa := mul_right_cancel₀ (ne_of_gt pd0) hqe
      have qf_eq : qf = qa := mul_right_cancel₀ (ne_of_gt pd0) hqf
      have qg_eq : qg = qa := mul_right_cancel₀ (ne_of_gt pd0) hqg
      have hag : qa * ha + kf ≤ qa * hf + ka := by
        simpa [comp_offset_entry, lower,
          za0, zf0, qf_eq] using hw.ag.2 1
      have hcp : 0 < c0 + c1 * qa := add_pos_of_pos_of_nonneg pc0 (mul_nonneg nc1 nqa)
      have hh : (c0 + c1 * qa) * (ha + ha) ≤ (c0 + c1 * qa) * hf := by
        have hh := hcf
        rw [za0, zero_mul, add_zero] at hh
        nlinarith only [hh, mul_le_mul_of_nonneg_left hag nc1]
      have hh' := le_of_mul_le_mul_left hh hcp
      have hr : ha = 0 := by linarith only [hh', hru, nha]
      have hu : hf = 0 := by linarith only [hru, hr, nhf]
      have kae : ke ≤ ka := by
        simpa [comp_offset_entry, lower,
          hr, hu, za0, ze0] using hw.ae.2 1
      have kaf : kf ≤ ka := by
        simpa [comp_offset_entry, lower,
          hr, hu, za0, zf0] using hw.ag.2 1
      have kbf : kf ≤ kb := by
        simpa [comp_offset_entry, lower,
          hr, hu, zb0, zf0] using hw.be.2 1
      have kbg : kg ≤ kb := by
        simpa [comp_offset_entry, lower,
          hr, hu, zb0, zg0] using hw.bf.2 1
      have kbe : kb ≤ ke := by
        apply le_of_mul_le_mul_left (a := c1) _ pc1
        simpa [hr, hu] using hce
      have kfa : ka ≤ kf := by
        apply le_of_mul_le_mul_left (a := c1) _ pc1
        simpa [hr, hu, za0] using hcf
      have kga : ka ≤ kg := by
        apply le_of_mul_le_mul_left (a := c1) _ pc1
        simpa [hr, hu, za0] using hcg
      have hke : ke = kb := by linarith only [kae, kfa, kbf, kbe]
      have hkf : kf = za * ka + ka := by simp only [za0, zero_mul, zero_add]; linarith only [kaf, kfa]
      have hkg : kg = za * kb + ka := by simp only [za0, zero_mul, zero_add]; linarith only [kbg, kbe, kae, kga]
      exact finish hr hu (congrArg (c1 * ·) hke) (congrArg (c1 * ·) hkf)
        (congrArg (c1 * ·) hkg)

theorem lower_forward_gaps_zero (A B C D E F G : Aff2)
    (hA : Admissible A) (hB : Admissible B) (hC : Admissible C)
    (hD : Admissible D) (hE : Admissible E) (hF : Admissible F) (hG : Admissible G)
    (lA : Lower A) (lB : Lower B) (lE : Lower E) (lF : Lower F) (lG : Lower G)
    (hw : ForwardWeak A B C D E F G) : ForwardGapsZero A B C D E F G := by
  obtain ⟨qa, za, ha, ka, rfl⟩ : ∃ q z h k, A = lower q z h k :=
    ⟨_, _, _, _, eq_lower A lA⟩
  obtain ⟨qb, zb, hb, kb, rfl⟩ : ∃ q z h k, B = lower q z h k :=
    ⟨_, _, _, _, eq_lower B lB⟩
  obtain ⟨qe, ze, he, ke, rfl⟩ : ∃ q z h k, E = lower q z h k :=
    ⟨_, _, _, _, eq_lower E lE⟩
  obtain ⟨qf, zf, hf, kf, rfl⟩ : ∃ q z h k, F = lower q z h k :=
    ⟨_, _, _, _, eq_lower F lF⟩
  obtain ⟨qg, zg, hg, kg, rfl⟩ : ∃ q z h k, G = lower q z h k :=
    ⟨_, _, _, _, eq_lower G lG⟩
  exact lower_forward_parameters qa qb qe qf qg za zb ze zf zg ha hb he hf hg ka kb ke kf kg
    C D hA hB hC hD hE hF hG hw

#print axioms lower_forward_parameters
#print axioms lower_forward_gaps_zero

end CollatzResearch.FullTwoLower
