module

public import ToricPower.ArrangementCochainFreeCoordinates

/-! # Full free coordinates for the original cellular chain complex

Finite cellwise biproducts are combined with arbitrary coefficient
bases. No finiteness of the Laurent coefficient bases is required.
The differential is still the original signed incidence column.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (k : Type) [CommRing k]
  (F : (IncidenceObject A)ᵒᵖ ⥤ ModuleCat.{0} k)

local instance chainFreeCellsFintype (q : ℕ) : Fintype (NormalizedCell A q) := Fintype.ofFinite _

variable (I : IncidenceObject A → Type)
  (coordinates : ∀ c, F.obj (op c) ≃ₗ[k] (I c →₀ k))

def cellularChainFreeCoordinates (q : ℕ) :
    (arrangementCellularChainComplex A k F).X q ≃ₗ[k]
      ((Σ i : NormalizedCell A q, I ⟨q,i⟩) →₀ k) :=
  (ModuleCat.biproductIsoPi
    (fun i : NormalizedCell A q => F.obj (op ⟨q,i⟩))).toLinearEquiv.trans
      ((LinearEquiv.piCongrRight (fun i : NormalizedCell A q => coordinates ⟨q,i⟩)).trans
        (Finsupp.sigmaFinsuppLEquivPiFinsupp k).symm)

theorem cellularChainFreeCoordinates_apply (q : ℕ)
    (x : (arrangementCellularChainComplex A k F).X q)
    (i : NormalizedCell A q) (a : I ⟨q,i⟩) :
    cellularChainFreeCoordinates A k F I coordinates q x ⟨i,a⟩ =
      coordinates ⟨q,i⟩
        (biproduct.π (fun j : NormalizedCell A q => F.obj (op ⟨q,j⟩)) i x) a := by
  change coordinates ⟨q,i⟩
    (((ModuleCat.biproductIsoPi (fun j : NormalizedCell A q => F.obj (op ⟨q,j⟩))).hom x) i) a = _
  rw [moduleBiproductIsoPi_hom_apply]

theorem cellularChainFreeCoordinates_generator (q : ℕ)
    (i : NormalizedCell A q) (a : I ⟨q,i⟩) (r : k) :
    cellularChainFreeCoordinates A k F I coordinates q
      (biproduct.ι (fun j : NormalizedCell A q => F.obj (op ⟨q,j⟩)) i
        ((coordinates ⟨q,i⟩).symm (Finsupp.single a r))) =
      Finsupp.single ⟨i,a⟩ r := by
  ext p
  rcases p with ⟨j,b⟩
  rw [cellularChainFreeCoordinates_apply,← ModuleCat.comp_apply]
  by_cases equal : i=j
  · subst j
    rw [biproduct.ι_π_self,ModuleCat.id_apply,LinearEquiv.apply_symm_apply]
    simp only [Finsupp.single_apply,Sigma.mk.inj_iff,heq_eq_eq,true_and]
  · rw [biproduct.ι_π_ne _ equal]
    change coordinates ⟨q,j⟩ 0 b = _
    rw [map_zero,Finsupp.zero_apply]
    exact (Finsupp.single_eq_of_ne (fun h => equal (congrArg Sigma.fst h).symm)).symm

theorem cellularChainFreeCoordinates_symm_single (q : ℕ)
    (i : NormalizedCell A q) (a : I ⟨q,i⟩) (r : k) :
    (cellularChainFreeCoordinates A k F I coordinates q).symm (Finsupp.single ⟨i,a⟩ r) =
      biproduct.ι (fun j : NormalizedCell A q => F.obj (op ⟨q,j⟩)) i
        ((coordinates ⟨q,i⟩).symm (Finsupp.single a r)) := by
  apply (cellularChainFreeCoordinates A k F I coordinates q).injective
  rw [LinearEquiv.apply_symm_apply,cellularChainFreeCoordinates_generator]

/-- Every original differential column, with its full coefficient map. -/
theorem cellularChainFreeCoordinates_d_generator (q : ℕ)
    (j : NormalizedCell A (q+1)) (a : I ⟨q+1,j⟩) (r : k)
    (i : NormalizedCell A q) (b : I ⟨q,i⟩) :
    cellularChainFreeCoordinates A k F I coordinates q
      ((arrangementCellularChainComplex A k F).d (q+1) q
        ((cellularChainFreeCoordinates A k F I coordinates (q+1)).symm
          (Finsupp.single ⟨j,a⟩ r))) ⟨i,b⟩ =
      Finsupp.linearCombination k
        (fun p : NormalizedCell A q × (Fin n → ℤ) =>
          coordinates ⟨q,i⟩
            (biproduct.π (fun t : NormalizedCell A q => F.obj (op ⟨q,t⟩)) i
              (biproduct.ι (fun t : NormalizedCell A q => F.obj (op ⟨q,t⟩)) p.1
                (cellularCoefficientHom A F j p.1 p.2
                  ((coordinates ⟨q+1,j⟩).symm (Finsupp.single a r))))) b)
        (diagonalGlobalColumn k A q j) := by
  rw [cellularChainFreeCoordinates_symm_single,cellularChainFreeCoordinates_apply]
  let evaluate : (F.obj (op ⟨q+1,j⟩) ⟶ arrangementCellularTerm A F q) →ₗ[k] k :=
    (Finsupp.lapply (R := k) (M := k) b).comp
      ((coordinates ⟨q,i⟩).toLinearMap.comp
        ((biproduct.π (fun t : NormalizedCell A q => F.obj (op ⟨q,t⟩)) i).hom.comp
          ((LinearMap.applyₗ (R := k)
            ((coordinates ⟨q+1,j⟩).symm (Finsupp.single a r))).comp
              ModuleCat.homLinearEquiv.toLinearMap)))
  change evaluate
    (biproduct.ι (fun t : NormalizedCell A (q+1) => F.obj (op ⟨q+1,t⟩)) j ≫
      (arrangementCellularChainComplex A k F).d (q+1) q) = _
  rw [arrangementCellularChainComplex_d,arrangementCellularBoundary_column]
  change evaluate (Finsupp.linearCombination k _ (diagonalGlobalColumn k A q j)) = _
  exact Finsupp.apply_linearCombination k evaluate _ _

end ToricPower.IntegralArrangement

end
