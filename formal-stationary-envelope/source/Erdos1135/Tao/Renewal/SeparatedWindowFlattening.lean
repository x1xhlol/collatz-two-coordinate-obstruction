import Erdos1135.Tao.Renewal.SeparatedWindowGeometry

/-!
# Countable Disjoint Window Flattening

This neutral leaf flattens a possibly infinite family of pairwise disjoint
finite windows into the ambient summation type.  No finite or countable
instance is imposed on the center index: injectivity into the summable ambient
lattice supplies the required support control.
-/

namespace Erdos1135
namespace Tao

noncomputable section

open scoped BigOperators

/-- A pairwise disjoint family of finite windows has total mass at most the
ambient nonnegative summable mass. -/
theorem taoSection7_tsum_finset_sum_le_tsum_of_pairwiseDisjoint
    {ι α : Type*} [DecidableEq α]
    (S : Set ι) (W : ι → Finset α) (K : α → ℝ)
    (hdisj : S.PairwiseDisjoint W)
    (hK0 : ∀ x, 0 ≤ K x)
    (hK : Summable K) :
    (∑' i : S, (W i.1).sum K) ≤ ∑' x : α, K x := by
  let flat : (Σ i : S, ↥(W i.1)) → α := fun p => p.2.1
  have hflat : Function.Injective flat := by
    rintro ⟨i, x⟩ ⟨j, y⟩ hxy
    change (x : α) = (y : α) at hxy
    have hij : i = j := by
      apply Subtype.ext
      by_contra hne
      have hW : Disjoint (W i.1) (W j.1) :=
        hdisj i.2 j.2 hne
      have hxj : (x : α) ∈ W j.1 := hxy.symm ▸ y.2
      exact (Finset.disjoint_left.mp hW) x.2 hxj
    subst j
    have hxy' : x = y := Subtype.ext hxy
    subst y
    rfl
  have hflatSummable : Summable (K ∘ flat) :=
    hK.comp_injective hflat
  have hsigma :
      (∑' p : (Σ i : S, ↥(W i.1)), K (flat p)) =
        ∑' i : S, ∑' x : ↥(W i.1), K x.1 := by
    simpa only [Function.comp_apply, flat] using
      hflatSummable.tsum_sigma'
        (fun i =>
          (hasSum_fintype (fun x : ↥(W i.1) => K x.1)).summable)
  have hfiber (i : S) :
      (∑' x : ↥(W i.1), K x.1) = (W i.1).sum K := by
    rw [tsum_fintype, ← Finset.attach_eq_univ]
    exact Finset.sum_attach (W i.1) K
  calc
    (∑' i : S, (W i.1).sum K) =
        ∑' i : S, ∑' x : ↥(W i.1), K x.1 :=
      tsum_congr fun i => (hfiber i).symm
    _ = ∑' p : (Σ i : S, ↥(W i.1)), K (flat p) := hsigma.symm
    _ ≤ ∑' x : α, K x := by
      simpa only [Function.comp_apply] using
        tsum_comp_le_tsum_of_inj hK hK0 hflat

/-- Countable separated integer centers have total exact-window mass at most
the ambient integer-lattice mass. -/
theorem taoSection7_tsum_centeredHalfOpenIntWindow_le_tsum
    (centers : Set ℤ) (d : ℕ) (K : ℤ → ℝ)
    (hsep : centers.Pairwise
      (fun c₁ c₂ => (d : ℤ) ≤ |c₁ - c₂|))
    (hK0 : ∀ z, 0 ≤ K z)
    (hK : Summable K) :
    (∑' c : centers,
      (taoSection7CenteredHalfOpenIntWindow d c.1).sum K) ≤
        ∑' z : ℤ, K z := by
  refine taoSection7_tsum_finset_sum_le_tsum_of_pairwiseDisjoint
    centers (taoSection7CenteredHalfOpenIntWindow d) K ?_ hK0 hK
  intro c₁ hc₁ c₂ hc₂ hne
  exact taoSection7CenteredHalfOpenIntWindow_disjoint_of_width_le_abs_sub
    (hsep hc₁ hc₂ hne)

end
end Tao
end Erdos1135
