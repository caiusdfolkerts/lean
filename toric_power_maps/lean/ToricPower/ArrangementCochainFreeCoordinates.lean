module

public import ToricPower.ArrangementRepresentableTerms

/-!
# Free coefficient coordinates for the actual cellular differential

For explicitly supplied bases of the coefficient modules, the actual
cochain term has the induced cell-and-basis coordinates. Its differential
is computed from the original geometric incidence columns. This generic
matrix interface is used with the genuine full Laurent coefficient
diagram and with its individual character fibers.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (k : Type) [CommRing k]
  (F : IncidenceObject A ⥤ ModuleCat.{0} k)

local instance cochainFreeCellsFintype (q : ℕ) :
    Fintype (NormalizedCell A q) := Fintype.ofFinite _

local instance cochainFreeOppositeBiproducts : HasFiniteBiproducts (ModuleCat.{0} k)ᵒᵖ :=
  HasFiniteBiproducts.of_hasFiniteProducts

@[reassoc]
theorem arrangementCellularCochainInclusion_projection_self (q : ℕ)
    (i : NormalizedCell A q) :
    arrangementCellularCochainInclusion A k F q i ≫
      arrangementCellularCochainProjection A k F q i = 𝟙 (F.obj ⟨q, i⟩) := by
  change (biproduct.π (fun i : NormalizedCell A q => F.op.obj (op ⟨q, i⟩)) i).unop ≫
    (biproduct.ι (fun i : NormalizedCell A q => F.op.obj (op ⟨q, i⟩)) i).unop = _
  rw [← unop_comp, biproduct.ι_π_self, unop_id]
  rfl

@[reassoc]
theorem arrangementCellularCochainInclusion_projection_ne (q : ℕ)
    (i j : NormalizedCell A q) (different : i ≠ j) :
    arrangementCellularCochainInclusion A k F q i ≫
      arrangementCellularCochainProjection A k F q j = 0 := by
  change (biproduct.π (fun i : NormalizedCell A q => F.op.obj (op ⟨q, i⟩)) i).unop ≫
    (biproduct.ι (fun i : NormalizedCell A q => F.op.obj (op ⟨q, i⟩)) j).unop = _
  rw [← unop_comp, biproduct.ι_π_ne _ different.symm, unop_zero]

variable (I : IncidenceObject A → Type)
  (coordinates : ∀ c, F.obj c ≃ₗ[k] (I c →₀ k))

/-- The genuine termwise free coordinates, with no restriction on the
size of an individual coefficient basis. -/
def cellularCochainFreeCoordinates (q : ℕ) :
    (arrangementCellularCochainComplex A k F).X q ≃ₗ[k]
      ((Σ i : NormalizedCell A q, I ⟨q, i⟩) →₀ k) :=
  ((arrangementCellularCochainTermIso A k F q) ≪≫
    ModuleCat.biproductIsoPi
      (fun i : NormalizedCell A q => F.obj ⟨q, i⟩)).toLinearEquiv.trans
    ((LinearEquiv.piCongrRight (fun i : NormalizedCell A q => coordinates ⟨q, i⟩)).trans
      (Finsupp.sigmaFinsuppLEquivPiFinsupp k).symm)

/-- A coordinate is exactly the corresponding coefficient projection. -/
theorem cellularCochainFreeCoordinates_apply (q : ℕ)
    (v : (arrangementCellularCochainComplex A k F).X q)
    (i : NormalizedCell A q) (a : I ⟨q, i⟩) :
    cellularCochainFreeCoordinates A k F I coordinates q v ⟨i, a⟩ =
      coordinates ⟨q, i⟩ (arrangementCellularCochainProjection A k F q i v) a := by
  change coordinates ⟨q, i⟩
    (((ModuleCat.biproductIsoPi (fun i : NormalizedCell A q => F.obj ⟨q, i⟩)).hom
      ((arrangementCellularCochainTermIso A k F q).hom v)) i) a = _
  rw [moduleBiproductIsoPi_hom_apply]
  exact congrArg (fun x => coordinates ⟨q, i⟩ x a)
    (ConcreteCategory.congr_hom (arrangementCellularCochainTermIso_projection A k F q i) v)

/-- The displayed free generator is the actual inclusion of the
chosen coefficient generator into its cell. -/
theorem cellularCochainFreeCoordinates_generator (q : ℕ)
    (i : NormalizedCell A q) (a : I ⟨q, i⟩) (r : k) :
    cellularCochainFreeCoordinates A k F I coordinates q
      (arrangementCellularCochainInclusion A k F q i
        ((coordinates ⟨q, i⟩).symm (Finsupp.single a r))) =
      Finsupp.single ⟨i, a⟩ r := by
  ext p
  rcases p with ⟨j, b⟩
  rw [cellularCochainFreeCoordinates_apply, ← ModuleCat.comp_apply]
  by_cases equal : i = j
  · subst j
    rw [arrangementCellularCochainInclusion_projection_self, ModuleCat.id_apply,
      LinearEquiv.apply_symm_apply]
    simp only [Finsupp.single_apply, Sigma.mk.inj_iff, heq_eq_eq, true_and]
  · rw [arrangementCellularCochainInclusion_projection_ne A k F q i j equal]
    change coordinates ⟨q, j⟩ 0 b = _
    rw [map_zero, Finsupp.zero_apply]
    symm
    exact Finsupp.single_eq_of_ne (fun h => equal (congrArg Sigma.fst h).symm)

/-- The inverse coordinates therefore recover the actual cochain
generator, rather than a generator imposed on another complex. -/
theorem cellularCochainFreeCoordinates_symm_single (q : ℕ)
    (i : NormalizedCell A q) (a : I ⟨q, i⟩) (r : k) :
    (cellularCochainFreeCoordinates A k F I coordinates q).symm (Finsupp.single ⟨i, a⟩ r) =
      arrangementCellularCochainInclusion A k F q i
        ((coordinates ⟨q, i⟩).symm (Finsupp.single a r)) := by
  apply (cellularCochainFreeCoordinates A k F I coordinates q).injective
  rw [LinearEquiv.apply_symm_apply, cellularCochainFreeCoordinates_generator]

/-- The actual cellular differential in arbitrary literal free
coordinates. The original geometric column supplies every scalar. -/
theorem cellularCochainFreeCoordinates_differential (q : ℕ)
    (v : (arrangementCellularCochainComplex A k F).X q)
    (j : NormalizedCell A (q + 1)) (b : I ⟨q + 1, j⟩) :
    cellularCochainFreeCoordinates A k F I coordinates (q + 1)
      ((arrangementCellularCochainComplex A k F).d q (q + 1) v) ⟨j, b⟩ =
      Finsupp.linearCombination k
        (fun p : NormalizedCell A q × (Fin n → ℤ) =>
          coordinates ⟨q + 1, j⟩
            ((cellularCoefficientHom A F.op j p.1 p.2).unop
              (arrangementCellularCochainProjection A k F q p.1 v)) b)
        (diagonalGlobalColumn k A q j) := by
  rw [cellularCochainFreeCoordinates_apply]
  let evaluate :
      ((arrangementCellularCochainComplex A k F).X q ⟶ F.obj ⟨q + 1, j⟩) →ₗ[k] k :=
    (Finsupp.lapply (R := k) (M := k) b).comp
      ((coordinates ⟨q + 1, j⟩).toLinearMap.comp
        ((LinearMap.applyₗ (R := k) v).comp (ModuleCat.homLinearEquiv).toLinearMap))
  change evaluate ((arrangementCellularCochainComplex A k F).d q (q + 1) ≫
    arrangementCellularCochainProjection A k F (q + 1) j) = _
  rw [arrangementCellularCochain_d_column]
  exact Finsupp.apply_linearCombination k evaluate _ _

end ToricPower.IntegralArrangement
