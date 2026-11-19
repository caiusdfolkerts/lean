module

public import ToricPower.ArrangementCochainCoordinates
public import ToricPower.ArrangementLaurentLabels
public import ToricPower.CellularCovariantLabels
public import ToricPower.CellularFoundations
public import ToricPower.VectorCopowerFree
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.LinearAlgebra.Finsupp.SumProd

/-!
# Actual representable cellular terms in full monomial coordinates

The terms below are those of the already constructed cellular functor,
evaluated on the genuine free representable. Canonical coproduct and
biproduct universal properties remove the auxiliary choices of bases.
The resulting indices retain each actual incidence and every permitted
Laurent character. Their exhaustive reindexing is the geometric costalk
index, not a finite approximation to the character lattice.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits
open scoped Classical

namespace ToricPower

variable {k : Type} [CommRing k] {I : Type} [Finite I]

/-- The canonical module biproduct comparison has the literal
coordinate projections. -/
theorem moduleBiproductIsoPi_hom_apply (F : I → ModuleCat.{0} k)
    (x : (⨁ F : ModuleCat.{0} k)) (i : I) :
    (ModuleCat.biproductIsoPi F).hom x i = biproduct.π F i x := by
  have projection : (ModuleCat.biproductIsoPi F).hom ≫
      ModuleCat.ofHom (LinearMap.proj i : (∀ i, F i) →ₗ[k] F i) = biproduct.π F i := by
    rw [← ModuleCat.biproductIsoPi_inv_comp_π, Iso.hom_inv_id_assoc]
  exact ConcreteCategory.congr_hom projection x

namespace IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (S : Set (Fin s))
  (k : Type) [Field k] (c : IncidenceObject A)

local instance representableTermsCellsFintype (q : ℕ) :
    Fintype (NormalizedCell A q) := Fintype.ofFinite _

local instance representableTermsHomFintype (d : IncidenceObject A) :
    Fintype (c ⟶ d) := Fintype.ofFinite _

local notation "Q" => reflectedLaurentDiagram A S k
local notation "Rep" => Cellular.representable k c
local notation "Coefficients" => Cellular.covariantCopowerDiagram k Q Rep

/-- The actual complex whose fixed-weight fibers will be compared with
the geometric costalk complex. -/
def representableLaurentCellularComplex : CochainComplex (ModuleCat.{0} k) ℕ :=
  (arrangementCellularRealization A k Q).obj Rep

/-- A single coefficient object has one literal copy of its full
Laurent module for each genuine incidence from the representing cell. -/
def representableLaurentCellCoordinates (q : ℕ) (e : NormalizedCell A q) :
    (Coefficients).obj ⟨q, e⟩ ≃ₗ[k]
      ((Σ f : c ⟶ (⟨q, e⟩ : IncidenceObject A),
        ReflectedLaurentWeight A S ⟨q, e⟩) →₀ k) :=
  ((Cellular.vectorCopowerFreeBiproductIso k ((Q).obj ⟨q, e⟩)
      (c ⟶ (⟨q, e⟩ : IncidenceObject A))) ≪≫
    ModuleCat.biproductIsoPi (fun _ : c ⟶ (⟨q, e⟩ : IncidenceObject A) =>
      (Q).obj ⟨q, e⟩)).toLinearEquiv.trans
        (Finsupp.sigmaFinsuppLEquivPiFinsupp k).symm

/-- The actual cellular term, in genuine incidence and full Laurent
coordinates. Both finite biproduct comparisons are canonical. -/
def representableLaurentTermCoordinates (q : ℕ) :
    (representableLaurentCellularComplex A S k c).X q ≃ₗ[k]
      (RepresentableLaurentIndex A S c q →₀ k) :=
  ((arrangementCellularCochainTermIso A k Coefficients q) ≪≫
    ModuleCat.biproductIsoPi
      (fun e : NormalizedCell A q => (Coefficients).obj ⟨q, e⟩)).toLinearEquiv.trans
    ((LinearEquiv.piCongrRight (representableLaurentCellCoordinates A S k c q)).trans
      (Finsupp.sigmaFinsuppLEquivPiFinsupp k).symm)

/-- Reading a literal coefficient commutes with the actual cochain
projection to its normalized cell. -/
theorem representableLaurentTermCoordinates_apply (q : ℕ)
    (x : (representableLaurentCellularComplex A S k c).X q)
    (e : NormalizedCell A q) (f : c ⟶ (⟨q, e⟩ : IncidenceObject A))
    (m : ReflectedLaurentWeight A S ⟨q, e⟩) :
    representableLaurentTermCoordinates A S k c q x ⟨e, f, m⟩ =
      representableLaurentCellCoordinates A S k c q e
        (arrangementCellularCochainProjection A k Coefficients q e x) ⟨f, m⟩ := by
  change representableLaurentCellCoordinates A S k c q e
      (((ModuleCat.biproductIsoPi
        (fun e : NormalizedCell A q => (Coefficients).obj ⟨q, e⟩)).hom
        ((arrangementCellularCochainTermIso A k Coefficients q).hom x)) e) ⟨f, m⟩ = _
  rw [moduleBiproductIsoPi_hom_apply]
  exact congrArg (fun y => representableLaurentCellCoordinates A S k c q e y ⟨f, m⟩)
    (ConcreteCategory.congr_hom
      (arrangementCellularCochainTermIso_projection A k Coefficients q e) x)

/-- The same actual term regrouped by every integral total character.
Each individual fiber is finite for the separately proved costalk reason. -/
def representableLaurentTermWeightCoordinates (q : ℕ) :
    (representableLaurentCellularComplex A S k c).X q ≃ₗ[k]
      ((Σ m : Fin n → ℤ, RepresentableCostalkIndex A c S m q) →₀ k) :=
  (representableLaurentTermCoordinates A S k c q).trans
    (representableLaurentCoefficientsEquiv A S k c q)

end IntegralArrangement
end ToricPower
