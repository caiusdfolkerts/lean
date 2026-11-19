module

public import ToricPower.ArrangementCellularSectionGenerators
public import ToricPower.ArrangementLaurentTopExact
public import ToricPower.ArrangementToricMinimalCoface
public import ToricPower.ArrangementRepresentedTensorSections

/-!
# Actual affine sections of the original chosen top coface

The source map is the original cellular copower inclusion. The affine
comparison takes that very map to the full Laurent top inclusion,
without changing its scalar coefficients or discarding characters.
The actual inverse-right frame then gives the same result after tensoring.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "Cells" => IncidenceObject A
local notation "X" => fan.algebraicRealization
local notation "Q" => arrangementDualLeftCartierDiagram fan nonempty regular basis rays
local notation "R" => arrangementDualRightCartierDiagram fan nonempty regular basis rays
local notation "Φ" => arrangementCellularSheafRealization fan nonempty regular basis rays
local notation "singleSheaf" => HomologicalComplex.single (Scheme.Modules X) (ComplexShape.up ℕ) n
local notation "singleScalar" => HomologicalComplex.single (ModuleCat ℂ) (ComplexShape.up ℕ) n

local instance topCofaceSectionsModuleBiproducts : HasFiniteBiproducts (X).Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- The literal top-cell summand in the original module-sheaf complex. -/
def arrangementSheafTopCofaceInclusion (c : Cells) (d : NormalizedCell A n)
    (f : c ⟶ (⟨n,d⟩ : Cells)) :
    (singleSheaf).obj ((Q).obj ⟨n,d⟩) ⟶ (Φ).obj (Cellular.representable ℂ c) :=
  HomologicalComplex.mkHomFromSingle
    (Cellular.vectorCopowerInclusion ℂ ((Q).obj ⟨n,d⟩)
      ((Cellular.representable ℂ c).obj ⟨n,d⟩) (ModuleCat.freeMk f) ≫
      arrangementCellularCochainInclusion A ℂ
        (Cellular.covariantCopowerDiagram ℂ Q (Cellular.representable ℂ c)) n d)
    (fun q relation => by
      have above : n < q := by have successor : q = n+1 := relation.symm; omega
      exact (arrangementCellularCochainComplex_isZero_X_above A ℂ
        (Cellular.covariantCopowerDiagram ℂ Q (Cellular.representable ℂ c))
          q above).eq_of_tgt _ _)

/-- The canonical image of that map in actual scalar sections. -/
def arrangementSheafTopCofaceSections (σ : fan.cones) (c : Cells)
    (d : NormalizedCell A n) (f : c ⟶ (⟨n,d⟩ : Cells)) :
    (singleScalar).obj
        ((FiniteCover.schemeBaseSections ℂ X (fan.affineToricChartι σ).opensRange).obj
          ((Q).obj ⟨n,d⟩)) ⟶
      ((FiniteCover.schemeBaseSections ℂ X (fan.affineToricChartι σ).opensRange).mapHomologicalComplex
        (.up ℕ)).obj ((Φ).obj (Cellular.representable ℂ c)) :=
  (HomologicalComplex.singleMapHomologicalComplex
    (FiniteCover.schemeBaseSections ℂ X (fan.affineToricChartι σ).opensRange)
      (.up ℕ) n).inv.app ((Q).obj ⟨n,d⟩) ≫
    ((FiniteCover.schemeBaseSections ℂ X (fan.affineToricChartι σ).opensRange).mapHomologicalComplex
      (.up ℕ)).map (arrangementSheafTopCofaceInclusion fan nonempty regular basis rays c d f)

/-- Exact comparison of the original map, at all degrees. -/
@[reassoc]
theorem arrangementSheafTopCofaceSections_comparison (σ : fan.cones) (c : Cells)
    (d : NormalizedCell A n) (f : c ⟶ (⟨n,d⟩ : Cells)) :
    arrangementSheafTopCofaceSections fan nonempty regular basis rays σ c d f ≫
      (arrangementSheafAffineSectionsIso fan nonempty regular basis rays σ
        (Cellular.representable ℂ c)).hom =
    (singleScalar).map ((reflectedToricSectionsDiagramIso
      fan nonempty regular basis rays σ).inv.app ⟨n,d⟩) ≫
      representedLaurentTopCofaceInclusion A (fanConeRaySet fan rays σ) c ℂ d f := by
  apply HomologicalComplex.from_single_hom_ext
  simp only [arrangementSheafTopCofaceSections, arrangementSheafTopCofaceInclusion,
    representedLaurentTopCofaceInclusion, HomologicalComplex.comp_f,
    HomologicalComplex.singleMapHomologicalComplex_inv_app_self,
    HomologicalComplex.single_map_f_self, HomologicalComplex.mkHomFromSingle_f,
    Functor.mapHomologicalComplex_map_f, Category.assoc, Iso.inv_hom_id_assoc]
  rw [← Functor.map_comp_assoc, Iso.inv_hom_id_assoc]
  exact congrArg (fun t => (HomologicalComplex.singleObjXSelf (.up ℕ) n
    ((FiniteCover.schemeBaseSections ℂ X (fan.affineToricChartι σ).opensRange).obj
      ((Q).obj ⟨n,d⟩))).hom ≫ t)
    (arrangementSheafAffineSectionsIso_generator fan nonempty regular basis rays σ
      (Cellular.representable ℂ c) n d (ModuleCat.freeMk f))

/-- The chosen genuine top coface induces a quasi-isomorphism in the
complete affine scalar complex. -/
theorem arrangementSheafTopCofaceInclusion_sections_quasiIso (σ : fan.cones) (c : Cells) :
    let p := arrangementMinimalTopCoface fan regular basis rays σ c
    QuasiIso (((FiniteCover.schemeBaseSections ℂ X
      (fan.affineToricChartι σ).opensRange).mapHomologicalComplex (.up ℕ)).map
        (arrangementSheafTopCofaceInclusion fan nonempty regular basis rays c p.val.1 p.val.2)) := by
  let p := arrangementMinimalTopCoface fan regular basis rays σ c
  haveI scalarQuasiIso : QuasiIso
      (representedLaurentTopCofaceInclusion A (fanConeRaySet fan rays σ) c ℂ p.val.1 p.val.2) :=
    representedLaurentTopCofaceInclusion_quasiIso A (fanConeRaySet fan rays σ) c ℂ
      (arrangementMinimalCharacter_strictDirection fan basis rays σ)
      (arrangementMinimalCharacter fan regular basis rays σ c)
      (arrangementMinimalCharacter_ray fan regular basis rays σ c) p
  haveI compositeQuasiIso : QuasiIso
      (arrangementSheafTopCofaceSections fan nonempty regular basis rays σ c p.val.1 p.val.2 ≫
        (arrangementSheafAffineSectionsIso fan nonempty regular basis rays σ
          (Cellular.representable ℂ c)).hom) := by
    rw [arrangementSheafTopCofaceSections_comparison]
    infer_instance
  haveI sourceQuasiIso : QuasiIso
      (arrangementSheafTopCofaceSections fan nonempty regular basis rays σ c p.val.1 p.val.2) :=
    quasiIso_of_comp_right
    (arrangementSheafTopCofaceSections fan nonempty regular basis rays σ c p.val.1 p.val.2)
    (arrangementSheafAffineSectionsIso fan nonempty regular basis rays σ
      (Cellular.representable ℂ c)).hom
  change QuasiIso (((FiniteCover.schemeBaseSections ℂ X
    (fan.affineToricChartι σ).opensRange).mapHomologicalComplex (.up ℕ)).map
      (arrangementSheafTopCofaceInclusion fan nonempty regular basis rays c p.val.1 p.val.2))
  apply (quasiIso_iff_comp_left
    ((HomologicalComplex.singleMapHomologicalComplex
      (FiniteCover.schemeBaseSections ℂ X (fan.affineToricChartι σ).opensRange)
        (.up ℕ) n).inv.app ((Q).obj ⟨n,p.val.1⟩)) _).mp
  exact sourceQuasiIso

/-- The actual chosen inverse-right frame transports this same
quasi-isomorphism after tensoring, naturally on the entire complex. -/
theorem arrangementSheafTopCofaceInclusion_tensor_sections_quasiIso
    (σ : fan.cones) (c : Cells) :
    let p := arrangementMinimalTopCoface fan regular basis rays σ c
    QuasiIso (((FiniteCover.schemeBaseSections ℂ X
      (fan.affineToricChartι σ).opensRange).mapHomologicalComplex (.up ℕ)).map
        (((tensorRight ((R).obj c)).mapHomologicalComplex (.up ℕ)).map
          (arrangementSheafTopCofaceInclusion fan nonempty regular basis rays c p.val.1 p.val.2))) := by
  let p := arrangementMinimalTopCoface fan regular basis rays σ c
  let f := arrangementSheafTopCofaceInclusion fan nonempty regular basis rays c p.val.1 p.val.2
  let e := schemeTensorFrameComplexGlobalSectionsIso (fan.affineToricChartι σ) ((R).obj c)
    (arrangementInverseRightAffineFrame fan nonempty regular basis rays σ c) ℂ (.up ℕ)
  haveI originalQuasiIso : QuasiIso (((FiniteCover.schemeBaseSections ℂ X
      (fan.affineToricChartι σ).opensRange).mapHomologicalComplex (.up ℕ)).map f) :=
    arrangementSheafTopCofaceInclusion_sections_quasiIso fan nonempty regular basis rays σ c
  haveI compositeQuasiIso : QuasiIso
      (((FiniteCover.schemeBaseSections ℂ X (fan.affineToricChartι σ).opensRange).mapHomologicalComplex
        (.up ℕ)).map (((tensorRight ((R).obj c)).mapHomologicalComplex (.up ℕ)).map f) ≫
          e.hom.app ((Φ).obj (Cellular.representable ℂ c))) := by
    erw [e.hom.naturality f]
    infer_instance
  exact quasiIso_of_comp_right _ (e.hom.app ((Φ).obj (Cellular.representable ℂ c)))

end ToricPower

end

