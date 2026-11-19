module

public import ToricPower.ArrangementCellularHomTarget
public import ToricPower.FiniteBiproductCoefficientNaturality
public import ToricPower.LinearHomFromCochainToSingleNaturality

/-! # Target naturality of actual cellular Hom chains

The full comparison commutes with every coefficient morphism. It can
therefore be applied to the differential of an actual injective target
complex, not merely to individual sheaves or cohomology groups.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (k : Type) [CommRing k]
  {B : Type*} [Category.{0} B] [Abelian B] [Linear k B] [HasFiniteBiproducts B]
  (Q : IncidenceObject A ⥤ B)

local instance targetNaturalCellFintype (q : ℕ) : Fintype (NormalizedCell A q) :=
  Fintype.ofFinite _
local instance targetNaturalOppositeBiproduct : HasFiniteBiproducts Bᵒᵖ :=
  HasFiniteBiproducts.of_hasFiniteProducts

def cellularHomCoefficientFunctor : B ⥤ (IncidenceObject A)ᵒᵖ ⥤ ModuleCat k :=
  linearYoneda k B ⋙
    (Functor.whiskeringLeft (IncidenceObject A)ᵒᵖ Bᵒᵖ (ModuleCat k)).obj Q.op

def cellularOrdinaryHomFunctor : B ⥤ ChainComplex (ModuleCat k) ℕ where
  obj M := ordinaryCochainCoefficients k (arrangementCellularCochainComplex A k Q) M
  map f := ordinaryCochainCoefficientsMap k (arrangementCellularCochainComplex A k Q) f
  map_id M := by
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro g
    exact Category.comp_id g
  map_comp f g := by
    apply HomologicalComplex.Hom.ext
    funext q
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro h
    exact (Category.assoc h f g).symm

/-- The comparison retains the original coefficient maps in every degree. -/
theorem cellularHomTargetComplexIso_target {M N : B} (f : M ⟶ N) :
    (cellularOrdinaryHomFunctor A k Q).map f ≫
      (cellularHomTargetComplexIso A k Q N).hom =
    (cellularHomTargetComplexIso A k Q M).hom ≫
      (arrangementCellularChainFunctor A k).map
        ((cellularHomCoefficientFunctor A k Q).map f) := by
  apply HomologicalComplex.Hom.ext
  funext q
  exact mapBiproduct_coefficient_naturality
    (fun c : NormalizedCell A q => Q.op.obj (op ⟨q,c⟩)) ((linearYoneda k B).map f)

def cellularHomTargetFunctorIso :
    cellularOrdinaryHomFunctor A k Q ≅
      cellularHomCoefficientFunctor A k Q ⋙ arrangementCellularChainFunctor A k :=
  NatIso.ofComponents (cellularHomTargetComplexIso A k Q)
    (fun f => cellularHomTargetComplexIso_target A k Q f)

end ToricPower.IntegralArrangement

end

