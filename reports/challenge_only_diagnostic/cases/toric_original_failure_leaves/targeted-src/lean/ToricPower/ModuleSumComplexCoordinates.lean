module

public import ToricPower.ModuleDirectSumFreeCoordinates

/-! # Full free coordinates of an unrestricted sum of complexes

These are coordinates of the actual direct-sum complex. The
differential stays in the same summand; all off-diagonal entries are
zero because of the genuine dependent-finitely-supported map.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped Classical

namespace ToricPower.ModuleDirectSum

variable (k : Type) [CommRing k] {I : Type}
  (K : I → CochainComplex (ModuleCat.{0} k) ℕ)
  (J : I → ℕ → Type) (coordinates : ∀ i q, (K i).X q ≃ₗ[k] (J i q →₀ k))

theorem complex_d_single (p q : ℕ) (i : I) (x : (K i).X p) :
    (complex k K).d p q (DFinsupp.single i x) =
      DFinsupp.single i ((K i).d p q x) := by
  change DFinsupp.mapRange.linearMap (fun t : I => ((K t).d p q).hom)
    (DFinsupp.single i x) = _
  simp only [DFinsupp.mapRange.linearMap_apply,DFinsupp.mapRange_single]

theorem complexCoordinates_d_single_self (p q : ℕ) (i : I)
    (j : J i p) (t : J i q) (r : k) :
    complexCoordinates k K J coordinates q
      ((complex k K).d p q
        ((complexCoordinates k K J coordinates p).symm (Finsupp.single ⟨i,j⟩ r))) ⟨i,t⟩ =
      coordinates i q ((K i).d p q ((coordinates i p).symm (Finsupp.single j r))) t := by
  rw [complexCoordinates_symm_single_dfinsupp,complex_d_single,complexCoordinates_apply,
    show ((show Π₀ l : I, (K l).X q from
      DFinsupp.single i ((K i).d p q ((coordinates i p).symm (Finsupp.single j r)))) i) =
        ((K i).d p q ((coordinates i p).symm (Finsupp.single j r))) from
      DFinsupp.single_eq_same]

theorem complexCoordinates_d_single_ne (p q : ℕ) (i l : I) (different : l ≠ i)
    (j : J i p) (t : J l q) (r : k) :
    complexCoordinates k K J coordinates q
      ((complex k K).d p q
        ((complexCoordinates k K J coordinates p).symm (Finsupp.single ⟨i,j⟩ r))) ⟨l,t⟩ = 0 := by
  rw [complexCoordinates_symm_single_dfinsupp,complex_d_single,complexCoordinates_apply]
  change coordinates l q
    ((DFinsupp.single i ((K i).d p q ((coordinates i p).symm (Finsupp.single j r))) :
      Π₀ t : I, (K t).X q) l) t = 0
  rw [DFinsupp.single_eq_of_ne different,map_zero,Finsupp.zero_apply]

end ToricPower.ModuleDirectSum

namespace ToricPower

variable (k : Type) [CommRing k]

/-- Identical actual differential columns give an isomorphism of the
original complexes through their specified full free coordinates. -/
def cochainIsoOfFreeCoordinates
    (K L : CochainComplex (ModuleCat.{0} k) ℕ) (I : ℕ → Type)
    (first : ∀ q, K.X q ≃ₗ[k] (I q →₀ k))
    (second : ∀ q, L.X q ≃ₗ[k] (I q →₀ k))
    (same : ∀ (q : ℕ) (i : I q) (r : k),
      first (q+1) (K.d q (q+1) ((first q).symm (Finsupp.single i r))) =
        second (q+1) (L.d q (q+1) ((second q).symm (Finsupp.single i r)))) : K ≅ L :=
  HomologicalComplex.Hom.isoOfComponents
    (fun q => ((first q).trans (second q).symm).toModuleIso) (by
      intro q p relation
      obtain rfl : q+1 = p := relation
      have maps :
          (first (q+1)).toLinearMap.comp ((K.d q (q+1)).hom.comp (first q).symm.toLinearMap) =
        (second (q+1)).toLinearMap.comp ((L.d q (q+1)).hom.comp (second q).symm.toLinearMap) :=
          Finsupp.lhom_ext (same q)
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro x
      apply (second (q+1)).injective
      change second (q+1) (L.d q (q+1) ((second q).symm (first q x))) =
        second (q+1) ((second (q+1)).symm (first (q+1) (K.d q (q+1) x)))
      rw [LinearEquiv.apply_symm_apply]
      have value := DFunLike.congr_fun maps (first q x)
      simpa only [LinearMap.comp_apply,LinearEquiv.coe_coe,LinearEquiv.symm_apply_apply]
        using value.symm)

end ToricPower

end
