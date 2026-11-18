module

public import ToricPower.ArrangementTopCofaceSections
public import ToricPower.ArrangementTopCofaceChart
public import ToricPower.QuasicoherentShapeDetection
public import ToricPower.ArrangementRepresentedQuasicoherentAugmentation

/-!
# The original represented augmentation is a quasi-isomorphism

On every smooth affine chart one genuine top coface supplies a
quasi-isomorphism into the complete represented cellular complex.
Its composite with the original augmentation is a chart isomorphism:
the original incidence is a monomial unit and the original diagonal
top quotient is invertible. Two-out-of-three and exact affine detection
prove the actual global augmentation, with its original source maps.
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
local notation "J" => dualDiagonalLineSheaf fan nonempty regular basis rays

local instance representedTopExactModuleBiproducts : HasFiniteBiproducts (X).Modules :=
  HasFiniteBiproducts.of_hasFiniteProducts

/-- The original cellular sheaf terms are quasicoherent, through the
canonical underlying comparison with the actual quasicoherent complex. -/
theorem arrangementCellularSheafRealization_term_quasicoherent
    (M : Cells ⥤ ModuleCat ℂ) (q : ℕ) :
    (((Φ).obj M).X q).IsQuasicoherent := by
  let e := (HomologicalComplex.eval (X).Modules (.up ℕ) q).mapIso
    (arrangementCellularUnderlyingIso fan nonempty regular basis rays M)
  exact (SheafOfModules.isQuasicoherent (X).ringCatSheaf).prop_of_iso e
    (((arrangementQuasicoherentCellularRealization fan nonempty regular basis rays).obj M).X q).property

/-- The local calculation concerns the actual map of full scalar
complexes, including every character and every original differential. -/
theorem arrangementRepresentedTopAugmentation_sections_quasiIso (σ : fan.cones) (c : Cells) :
    QuasiIso (((FiniteCover.schemeBaseSections ℂ X
      (fan.affineToricChartι σ).opensRange).mapHomologicalComplex (.up ℕ)).map
        (arrangementRepresentedTopAugmentation fan nonempty regular basis rays c)) := by
  let p := arrangementMinimalTopCoface fan regular basis rays σ c
  let t := arrangementSheafTopCofaceInclusion fan nonempty regular basis rays c p.val.1 p.val.2
  let T := tensorRight ((R).obj c)
  let TC := T.mapHomologicalComplex (.up ℕ)
  let G := FiniteCover.schemeBaseSections ℂ X (fan.affineToricChartι σ).opensRange
  let GC := G.mapHomologicalComplex (.up ℕ)
  let a := arrangementRepresentedTopAugmentation fan nonempty regular basis rays c
  let b := TC.map t ≫ a
  let inc := Cellular.vectorCopowerInclusion ℂ ((Q).obj ⟨n,p.val.1⟩)
    ((Cellular.representable ℂ c).obj ⟨n,p.val.1⟩) (ModuleCat.freeMk p.val.2) ≫
      arrangementCellularCochainInclusion A ℂ
        (Cellular.covariantCopowerDiagram ℂ Q (Cellular.representable ℂ c)) n p.val.1
  let coefficient := inc ▷ ((R).obj c) ≫ singleAugmentationComponent a
  haveI localCoefficient : IsIso
      ((Scheme.Modules.restrictFunctor (fan.affineToricChartι σ)).map coefficient) :=
    arrangementMinimalTopCoface_augmentationCoefficient_restrict_isIso
      fan nonempty regular basis rays σ c
  haveI scalarCoefficient : IsIso (G.map coefficient) := by
    exact (NatIso.isIso_map_iff
      (restrictionGlobalBaseSectionsIso ℂ (fan.affineToricChartι σ)) coefficient).mp (by
        change IsIso ((FiniteCover.schemeBaseSections ℂ (fan.affineToricChart σ) ⊤).map
          ((Scheme.Modules.restrictFunctor (fan.affineToricChartι σ)).map coefficient))
        infer_instance)
  have component :
      T.map (HomologicalComplex.singleObjXSelf (.up ℕ) n ((Q).obj ⟨n,p.val.1⟩)).inv ≫
        b.f n ≫ (HomologicalComplex.singleObjXSelf (.up ℕ) n J).hom = coefficient := by
    simp only [b, t, TC, arrangementSheafTopCofaceInclusion,
      HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      HomologicalComplex.mkHomFromSingle_f, Functor.map_comp, Category.assoc]
    rw [← T.map_comp_assoc, Iso.inv_hom_id, T.map_id, Category.id_comp]
    change _ = T.map inc ≫ a.f n ≫
      (HomologicalComplex.singleObjXSelf (.up ℕ) n J).hom
    simp only [inc, T.map_comp, Category.assoc]
  haveI compositeIso : IsIso (GC.map b) := by
    haveI components (q : ℕ) : IsIso ((GC.map b).f q) := by
      by_cases equal : q = n
      · subst q
        have mapped := congrArg G.map component
        simp only [Functor.map_comp] at mapped
        haveI conjugate : IsIso
            (G.map (T.map (HomologicalComplex.singleObjXSelf (.up ℕ) n
                ((Q).obj ⟨n,p.val.1⟩)).inv) ≫ G.map (b.f n) ≫
              G.map (HomologicalComplex.singleObjXSelf (.up ℕ) n J).hom) := by
          rw [mapped]
          infer_instance
        haveI middle : IsIso (G.map (b.f n) ≫
            G.map (HomologicalComplex.singleObjXSelf (.up ℕ) n J).hom) :=
          IsIso.of_isIso_comp_left
            (G.map (T.map (HomologicalComplex.singleObjXSelf (.up ℕ) n
              ((Q).obj ⟨n,p.val.1⟩)).inv)) _
        exact IsIso.of_isIso_comp_right (G.map (b.f n))
          (G.map (HomologicalComplex.singleObjXSelf (.up ℕ) n J).hom)
      · exact (G.map_isZero (T.map_isZero
          (HomologicalComplex.isZero_single_obj_X (.up ℕ) n ((Q).obj ⟨n,p.val.1⟩) q equal))).isIso
          (G.map_isZero (HomologicalComplex.isZero_single_obj_X (.up ℕ) n J q equal)) _
    exact HomologicalComplex.Hom.isIso_of_components _
  haveI sourceQuasiIso : QuasiIso (GC.map (TC.map t)) :=
    arrangementSheafTopCofaceInclusion_tensor_sections_quasiIso fan nonempty regular basis rays σ c
  haveI composedQuasiIso : QuasiIso (GC.map (TC.map t) ≫ GC.map a) := by
    rw [← GC.map_comp]
    change QuasiIso (GC.map b)
    infer_instance
  exact quasiIso_of_comp_left (GC.map (TC.map t)) (GC.map a)

/-- The exact original represented top quotient is a global
quasi-isomorphism, with no assumed counit or reconstruction identity. -/
theorem arrangementRepresentedTopAugmentation_quasiIso (c : Cells) :
    QuasiIso (arrangementRepresentedTopAugmentation fan nonempty regular basis rays c) := by
  letI rightQCoh : ((R).obj c).IsQuasicoherent := by
    letI := toricSchemeIntegral fan nonempty
    change (invariantCartierDivisor fan nonempty regular
      (arrangementDualRightCoefficients fan basis rays c)).sheaf.IsQuasicoherent
    infer_instance
  letI lineQCoh : (J).IsQuasicoherent := by
    letI := dualDiagonalLineSheaf_isInvertible fan nonempty regular basis rays
    infer_instance
  apply quasicoherent_complex_quasiIso_of_affineSections ℂ
    (fun σ : fan.cones => (fan.affineToricChartι σ).opensRange)
    fan.affineToricOpenCover.isOpenCover_opensRange
    (fun σ => isAffineOpen_opensRange (fan.affineToricChartι σ))
    (arrangementRepresentedTopAugmentation fan nonempty regular basis rays c)
  · intro q
    letI := arrangementCellularSheafRealization_term_quasicoherent
      fan nonempty regular basis rays (Cellular.representable ℂ c) q
    change ((((Φ).obj (Cellular.representable ℂ c)).X q) ⊗ ((R).obj c)).IsQuasicoherent
    infer_instance
  · intro q
    by_cases equal : q = n
    · subst q
      exact (SheafOfModules.isQuasicoherent (X).ringCatSheaf).prop_of_iso
        (HomologicalComplex.singleObjXSelf (.up ℕ) n J).symm inferInstance
    · exact (SheafOfModules.isQuasicoherent (X).ringCatSheaf).prop_of_isZero
        (HomologicalComplex.isZero_single_obj_X (.up ℕ) n J q equal)
  · intro σ
    exact arrangementRepresentedTopAugmentation_sections_quasiIso fan nonempty regular basis rays σ c

/-- The genuine source-natural augmentation in quasicoherent sheaves
now has its full represented quasi-isomorphism proof. -/
theorem arrangementRepresentedQuasicoherentAugmentation_quasiIso (c : Cells) :
    QuasiIso ((arrangementRepresentedQuasicoherentAugmentation
      fan nonempty regular basis rays).app (Opposite.op c)) := by
  letI := arrangementRepresentedTopAugmentation_quasiIso fan nonempty regular basis rays c
  exact arrangementRepresentedQuasicoherentAugmentation_quasiIso_of_top fan nonempty regular basis rays c

/-- Its original top quotient is epi, in every coefficient degree. -/
theorem arrangementRepresentedQuasicoherentAugmentation_epi (c : Cells) :
    Epi ((arrangementRepresentedQuasicoherentAugmentation
      fan nonempty regular basis rays).app (Opposite.op c)) := by
  letI := arrangementRepresentedTopAugmentation_quasiIso fan nonempty regular basis rays c
  exact arrangementRepresentedQuasicoherentAugmentation_epi_of_top fan nonempty regular basis rays c

end ToricPower

end

