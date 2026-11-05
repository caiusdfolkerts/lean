module

public import PaperVerification.ToricNormalAllocation
public import PaperVerification.ToricBundleFanAllocation

@[expose] public section

/-! # Bounded parity allocation on an actual finite set of primitive normals -/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

theorem finset_bounded_parity_split {ι : Type*} (s : Finset ι) {R : ℕ}
    (hs : s.card ≤ R) (m p : ι → ℤ) (hm : ∀ u ∈ s, 0 < m u)
    (hbudget : (∑ u ∈ s, m u) + 3 ≤ 2 * (R : ℤ)) :
    ∃ h k : ι → ℕ,
      (∀ u ∈ s, (h u : ℤ) + (k u : ℤ) = m u) ∧
      (∑ u ∈ s, h u) ≤ R ∧ (∑ u ∈ s, k u) ≤ R ∧
      (∀ u ∈ s, ∃ w : ℤ, (h u : ℤ) - p u = w + w) := by
  let m' : Fin s.card → ℤ := fun j => m (s.equivFin.symm j)
  let p' : Fin s.card → ℤ := fun j => p (s.equivFin.symm j)
  have hm' (j : Fin s.card) : 0 < m' j := hm _ (s.equivFin.symm j).property
  have hbudget' : (∑ j, m' j) + 3 ≤ 2 * (R : ℤ) := by
    simpa only [m', sum_finsetIntegerRestriction] using hbudget
  obtain ⟨h', k', hh', hk', hsum', hH', hK', w, hw⟩ :=
    PaperVerification.Toric.bounded_parity_split_integer hs m' p' hm' hbudget'
  let hZ := finsetIntegerExtension s h'
  let kZ := finsetIntegerExtension s k'
  let h : ι → ℕ := fun u => (hZ u).toNat
  let k : ι → ℕ := fun u => (kZ u).toNat
  have hcast (u : ι) (hu : u ∈ s) : (h u : ℤ) = hZ u := by
    apply Int.toNat_of_nonneg
    change 0 ≤ finsetIntegerExtension s h' u
    rw [finsetIntegerExtension_apply s h' hu]
    exact hh' _
  have kcast (u : ι) (hu : u ∈ s) : (k u : ℤ) = kZ u := by
    apply Int.toNat_of_nonneg
    change 0 ≤ finsetIntegerExtension s k' u
    rw [finsetIntegerExtension_apply s k' hu]
    exact hk' _
  refine ⟨h, k, ?_, ?_, ?_, ?_⟩
  · intro u hu
    rw [hcast u hu, kcast u hu]
    change finsetIntegerExtension s h' u + finsetIntegerExtension s k' u = m u
    rw [finsetIntegerExtension_apply s h' hu, finsetIntegerExtension_apply s k' hu]
    have hsum := congrFun hsum' (s.equivFin ⟨u, hu⟩)
    simpa only [Pi.add_apply, m', Equiv.symm_apply_apply] using hsum
  · have htotal : ((∑ u ∈ s, h u : ℕ) : ℤ) = ∑ j, h' j := by
      rw [Nat.cast_sum, Finset.sum_congr rfl hcast, sum_finsetIntegerExtension]
    have htotal' : ((∑ u ∈ s, h u : ℕ) : ℤ) ≤ R := htotal.symm ▸ hH'
    exact_mod_cast htotal'
  · have htotal : ((∑ u ∈ s, k u : ℕ) : ℤ) = ∑ j, k' j := by
      rw [Nat.cast_sum, Finset.sum_congr rfl kcast, sum_finsetIntegerExtension]
    have htotal' : ((∑ u ∈ s, k u : ℕ) : ℤ) ≤ R := htotal.symm ▸ hK'
    exact_mod_cast htotal'
  · intro u hu
    refine ⟨w (s.equivFin ⟨u, hu⟩), ?_⟩
    rw [hcast u hu]
    change finsetIntegerExtension s h' u - p u = _
    rw [finsetIntegerExtension_apply s h' hu]
    have he := congrFun hw (s.equivFin ⟨u, hu⟩)
    simpa only [Pi.sub_apply, Pi.add_apply, p', Equiv.symm_apply_apply] using he

end PaperVerification.ToricGeometry
