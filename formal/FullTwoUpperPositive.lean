import FullTwoUpperAlgebra
import FullTwoUpperDegenerate
import FullTwoUpperUnit

namespace CollatzResearch.FullTwoUpper

set_option maxHeartbeats 1200000
set_option linter.unusedSimpArgs false

theorem positive_slope_partition (m : Data) (w : Weak m)
    (ha : 0 < m.za) (hb : 0 < m.zb) :
    m.ze=m.zf ∧ m.zg=m.zf ∧ (m.zf=0 ∨ m.za=m.zb) := by
  obtain ⟨af,ag,be,bf⟩ := slope_equalities m w
  have ef : m.ze=m.zf := by nlinarith only [be,hb]
  have gf : m.zg=m.zf := by nlinarith only [ag,ha]
  refine ⟨ef,gf,?_⟩
  by_cases hf : m.zf=0
  · exact Or.inl hf
  · have hfp : 0 < m.zf := lt_of_le_of_ne w.zf (Ne.symm hf)
    right
    rw [ef] at af
    nlinarith only [af,hfp]

theorem high_ternary_zero_k (m : Data) (w : Weak m)
    (ab : m.zb=m.za) (ef : m.ze=m.zf) (gf : m.zg=m.zf)
    (ha : 1 ≤ m.za) (hgt : m.za < m.zf) :
    m.ka=0 ∧ m.kb=0 ∧ m.ke=0 ∧ m.kf=0 ∧ m.kg=0 := by
  have bg := w.bg_k
  have bd := w.bd_k
  have ag := w.ag_k
  have af := w.af_k
  rw [ab,gf] at bg bd
  rw [ef] at af
  have kgkb : m.kg ≤ m.kb := by
    nlinarith only [bd,mul_nonneg (le_of_lt (sub_pos.mpr hgt)) w.tau]
  have hz : m.kb=0 := by
    have hx := mul_nonneg (sub_nonneg.mpr ha) (sub_nonneg.mpr kgkb)
    nlinarith only [bg,hx,w.kb,hgt]
  have gz : m.kg=0 := by linarith only [kgkb,hz,w.kg]
  have az : m.ka=0 := by
    rw [gz,mul_zero] at ag
    nlinarith only [ag,w.ka,w.kf,ha,hgt]
  have fz : m.kf=0 := by
    rw [gz,az,mul_zero,zero_add] at ag
    linarith only [ag,w.kf]
  have ez : m.ke=0 := by
    rw [az,hz,fz,mul_zero,zero_add] at af
    linarith only [af,w.ke]
  exact ⟨az,hz,ez,fz,gz⟩

theorem low_ternary_zero_q (m : Data) (w : Weak m)
    (ab : m.zb=m.za) (ef : m.ze=m.zf) (gf : m.zg=m.zf)
    (ha : 1 < m.za) (_hf : 1 ≤ m.zf) (hfa : m.zf ≤ m.za) :
    m.qa=0 ∧ m.qb=0 ∧ m.qe=0 ∧ m.qf=0 ∧ m.qg=0 := by
  have ce := w.ce_q
  have cf := w.cf_q
  have cg := w.cg_q
  rw [ab,ef] at ce
  rw [ab,gf] at cg
  have e : m.qb ≤ m.qe := by
    nlinarith only [ce,mul_nonneg w.kap (sub_nonneg.mpr hfa)]
  have aa : m.zf ≤ m.za*m.za := by
    nlinarith only [hfa,ha,mul_nonneg (le_of_lt (sub_pos.mpr ha)) w.za]
  have f : (1+m.za)*m.qa ≤ m.qf := by
    nlinarith only [cf,mul_nonneg w.kap (sub_nonneg.mpr aa)]
  have g : m.qb+m.za*m.qa ≤ m.qg := by
    nlinarith only [cg,mul_nonneg w.kap (sub_nonneg.mpr aa)]
  have pq : 2*(m.qa+m.qb) ≤ m.qe+m.qf+m.qg := by
    nlinarith only [e,f,g,w.qa,mul_nonneg (le_of_lt (sub_pos.mpr ha)) w.qa]
  obtain ⟨agg,_,_⟩ := aggregate_nonneg m w
  rw [ab,ef,gf] at agg
  have h1 := mul_nonneg (sub_nonneg.mpr hfa) (add_nonneg w.qa w.qb)
  have h2 := mul_nonneg (le_of_lt (sub_pos.mpr ha)) (sub_nonneg.mpr pq)
  have qzero : m.qa+m.qb=0 := by
    nlinarith only [agg,h1,h2,ha,add_nonneg w.qa w.qb]
  have pzero : m.qe+m.qf+m.qg=0 := by
    have hq : m.qb = -m.qa := by linarith only [qzero]
    rw [hq] at agg
    nlinarith only [agg,ha,add_nonneg (add_nonneg w.qe w.qf) w.qg]
  exact ⟨by linarith only [qzero,w.qa,w.qb],
    by linarith only [qzero,w.qa,w.qb],
    by linarith only [pzero,w.qe,w.qf,w.qg],
    by linarith only [pzero,w.qe,w.qf,w.qg],
    by linarith only [pzero,w.qe,w.qf,w.qg]⟩


theorem positive_small_zero_k (m : Data) (w : Weak m) (ex : ExactSwaps m)
    (ha : 0 < m.za) (hf : 0 < m.zf)
    (ab : m.zb=m.za) (ef : m.ze=m.zf) (gf : m.zg=m.zf)
    (small : m.za < 1 ∨ m.zf < 1)
    (qpos : 0 < m.qa+m.qb+(m.qe+m.qf+m.qg))
    (kpos : 0 < m.ka+m.kb+(m.ke+m.kf+m.kg)) :
    m.ka=0 ∧ m.kb=0 ∧ m.ke=0 ∧ m.kf=0 ∧ m.kg=0 := by
  have aq := ex.ae_q
  have fq := ex.af_q
  have gq := ex.ag_q
  have eq := ex.be_q
  have bq := ex.bg_q
  simp only [ab,ef,gf] at aq fq gq eq bq
  have qt := triangular_resonance 1 1 m.za m.zf m.qa m.qb m.qe m.qf m.qg
    (by norm_num) (by norm_num) ha
    (by nlinarith only [aq]) (by nlinarith only [fq]) (by nlinarith only [gq])
    (by nlinarith only [eq]) (by nlinarith only [bq])
  have qnormal : m.qa=m.qb ∧ m.qe=m.qf ∧ m.qe=m.qg ∧
      (1-m.za)*m.qe=(1-m.zf)*m.qa := by
    rcases qt with h | h
    · exact h
    · rcases small with hs | hs <;> rcases h with ⟨ht,hf⟩ <;> linarith
  obtain ⟨qab,qef,qeg,qrel⟩ := qnormal
  have qp : 0 < m.qa+m.qe := by
    rw [← qab,← qef,← qeg] at qpos
    linarith only [qpos,w.qa,w.qe]
  obtain ⟨l,lp,la,le⟩ := common_form m.za m.zf m.qa m.qe w.qa w.qe qp small qrel
  have qform : QForm m l :=
    ⟨la,by rw [ab,← qab]; exact la,by rw [ef]; exact le,
      by rw [← qef]; exact le,by rw [gf,← qeg]; exact le⟩
  have ak := ex.ae_k
  have fk := ex.af_k
  have gk := ex.ag_k
  have ek := ex.be_k
  have bk := ex.bg_k
  simp only [ab,ef,gf] at ak fk gk ek bk
  have kt := triangular_resonance m.za m.zf 1 1 m.ka m.kb m.ke m.kf m.kg
    ha hf (by norm_num)
    (by nlinarith only [ak]) (by nlinarith only [fk]) (by nlinarith only [gk])
    (by nlinarith only [ek]) (by nlinarith only [bk])
  rcases kt with knormal | exceptional
  · obtain ⟨kab,kef,keg,krel⟩ := knormal
    have kp : 0 < m.ka+m.ke := by
      rw [← kab,← kef,← keg] at kpos
      linarith only [kpos,w.ka,w.ke]
    have krel' : (1-m.za)*m.ke=(1-m.zf)*m.ka := by nlinarith only [krel]
    obtain ⟨u,up,ua,ue⟩ := common_form m.za m.zf m.ka m.ke w.ka w.ke kp small krel'
    have kform : KForm m u :=
      ⟨ua,by rw [ab,← kab]; exact ua,by rw [ef]; exact ue,
        by rw [← kef]; exact ue,by rw [gf,← keg]; exact ue⟩
    exact fixed_form_zero_k m w ex l u lp (le_of_lt up) qform kform
  · obtain ⟨ht,hs⟩ := exceptional
    have ht' : m.za=(1:ℝ)/2 := by linarith
    have hs' : m.zf=(1:ℝ)/3 := by linarith
    have ce := w.ce_q
    have cf := w.cf_q
    rw [qform.b,qform.e,ab,ef,ht',hs'] at ce
    rw [qform.a,qform.f,ht',hs'] at cf
    have hc : m.kap=l := by nlinarith only [ce,cf]
    exact matching_boundary_zero_k m w ex l lp qform hc

theorem zero_ternary_zero_k (m : Data) (w : Weak m) (ex : ExactSwaps m)
    (ha : 0 < m.za) (hb : 0 < m.zb)
    (ez : m.ze=0) (fz : m.zf=0) (gz : m.zg=0)
    (qpos : 0 < m.qa+m.qb+(m.qe+m.qf+m.qg)) :
    m.ka=0 ∧ m.kb=0 ∧ m.ke=0 ∧ m.kf=0 ∧ m.kg=0 := by
  have aq := ex.ae_q
  have fq := ex.af_q
  have gq := ex.ag_q
  have eq := ex.be_q
  have bq := ex.bg_q
  have xq := ex.bf_q
  simp only [ez,fz,gz,mul_zero,zero_mul,add_zero,zero_add] at aq fq gq eq bq xq
  have ef : m.qe=m.qf := by
    have hz : (1+m.zb)*(m.qf-m.qe)=0 := by nlinarith only [fq,eq]
    have := (mul_eq_zero.mp hz).resolve_left (by linarith)
    linarith
  have gf : m.qg=m.qf := by
    have hz : (1+m.za)*(m.qg-m.qf)=0 := by nlinarith only [gq,xq]
    have := (mul_eq_zero.mp hz).resolve_left (by linarith)
    linarith
  have qform : QForm m m.qe := by
    constructor
    · nlinarith only [aq]
    · rw [gf,← ef] at bq
      nlinarith only [bq]
    · simp [ez]
    · simp [fz,ef]
    · simp [gz,ef,gf]
  have qp : 0 < m.qe := q_form_parameter_pos m m.qe w.qe qform qpos
  have ak := ex.ae_k
  have fk := ex.af_k
  have gk := ex.ag_k
  have bk := ex.bg_k
  simp only [ez,fz,gz,mul_zero,zero_mul,add_zero,zero_add] at ak fk gk bk
  have kf : m.kf=m.ke := by nlinarith only [ak,fk,ha]
  have kg : m.kg=m.ke := by
    rw [kf] at gk
    nlinarith only [ak,gk,ha]
  have kform : KForm m m.ke := by
    constructor
    · nlinarith only [ak]
    · rw [kg] at bk
      nlinarith only [bk]
    · simp [ez]
    · simp [fz,kf]
    · simp [gz,kg]
  exact fixed_form_zero_k m w ex m.qe m.ke qp w.ke qform kform


theorem positive_zero_gaps (m : Data) (w : Weak m)
    (ha : 0 < m.za) (hb : 0 < m.zb) : ZeroGaps m := by
  by_cases hq : 0 < m.qa+m.qb+(m.qe+m.qf+m.qg)
  swap
  · have a : m.qa=0 := by linarith only [hq,w.qa,w.qb,w.qe,w.qf,w.qg]
    have b : m.qb=0 := by linarith only [hq,w.qa,w.qb,w.qe,w.qf,w.qg]
    have e : m.qe=0 := by linarith only [hq,w.qa,w.qb,w.qe,w.qf,w.qg]
    have f : m.qf=0 := by linarith only [hq,w.qa,w.qb,w.qe,w.qf,w.qg]
    have g : m.qg=0 := by linarith only [hq,w.qa,w.qb,w.qe,w.qf,w.qg]
    exact q_zero_gaps m w a b e f g
  by_cases hk : 0 < m.ka+m.kb+(m.ke+m.kf+m.kg)
  swap
  · have a : m.ka=0 := by linarith only [hk,w.ka,w.kb,w.ke,w.kf,w.kg]
    have b : m.kb=0 := by linarith only [hk,w.ka,w.kb,w.ke,w.kf,w.kg]
    have e : m.ke=0 := by linarith only [hk,w.ka,w.kb,w.ke,w.kf,w.kg]
    have f : m.kf=0 := by linarith only [hk,w.ka,w.kb,w.ke,w.kf,w.kg]
    have g : m.kg=0 := by linarith only [hk,w.ka,w.kb,w.ke,w.kf,w.kg]
    exact k_zero_gaps m w a b e f g
  obtain ⟨ef,gf,hcases⟩ := positive_slope_partition m w ha hb
  rcases hcases with fz | ab
  · have ez : m.ze=0 := ef.trans fz
    have gz : m.zg=0 := gf.trans fz
    have ex := exact_of_negative m w (Or.inr (by rw [ez,fz,gz]; norm_num)) hq hk
    obtain ⟨a,b,e,f,g⟩ := zero_ternary_zero_k m w ex ha hb ez fz gz hq
    exact k_zero_gaps m w a b e f g
  · have ab' : m.zb=m.za := ab.symm
    by_cases hf : m.zf=0
    · have ez : m.ze=0 := ef.trans hf
      have gz : m.zg=0 := gf.trans hf
      have ex := exact_of_negative m w (Or.inr (by rw [ez,hf,gz]; norm_num)) hq hk
      obtain ⟨a,b,e,f,g⟩ := zero_ternary_zero_k m w ex ha hb ez hf gz hq
      exact k_zero_gaps m w a b e f g
    have hfp : 0 < m.zf := lt_of_le_of_ne w.zf (Ne.symm hf)
    by_cases small : m.za < 1 ∨ m.zf < 1
    · have hn : m.za+m.zb < 2 ∨ m.ze+m.zf+m.zg < 3 := by
        rcases small with h | h
        · exact Or.inl (by rw [ab']; linarith)
        · exact Or.inr (by rw [ef,gf]; linarith)
      have ex := exact_of_negative m w hn hq hk
      obtain ⟨a,b,e,f,g⟩ := positive_small_zero_k m w ex ha hfp ab' ef gf small hq hk
      exact k_zero_gaps m w a b e f g
    · have ha1 : 1 ≤ m.za := le_of_not_gt (fun h => small (Or.inl h))
      have hf1 : 1 ≤ m.zf := le_of_not_gt (fun h => small (Or.inr h))
      by_cases hgt : m.za < m.zf
      · obtain ⟨a,b,e,f,g⟩ := high_ternary_zero_k m w ab' ef gf ha1 hgt
        exact k_zero_gaps m w a b e f g
      · have hle : m.zf ≤ m.za := le_of_not_gt hgt
        by_cases hunit : m.za=1
        · have zf1 : m.zf=1 := by linarith only [hf1,hle,hunit]
          exact unit_zero_gaps m w hunit (ab'.trans hunit) (ef.trans zf1) zf1 (gf.trans zf1)
        · have hat : 1 < m.za := lt_of_le_of_ne ha1 (Ne.symm hunit)
          obtain ⟨a,b,e,f,g⟩ := low_ternary_zero_q m w ab' ef gf hat hf1 hle
          exact q_zero_gaps m w a b e f g

#print axioms positive_zero_gaps

end CollatzResearch.FullTwoUpper
