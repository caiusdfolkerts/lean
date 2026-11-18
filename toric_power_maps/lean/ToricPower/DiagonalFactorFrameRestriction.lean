module

public import ToricPower.DiagonalAugmentationFrameTransport
public import ToricPower.SchemePullbackSectionCoherence

/-!
# Restriction of the two actual diagonal factor frames

The comparison maps in the diagonal construction are the prescribed
pullback composition maps, the prescribed comparison with open restriction,
and the prescribed structure-sheaf maps. This file normalizes that entire
path before evaluating a Cartier frame. In particular, the normalization
does not replace the path by an arbitrary isomorphism of line sheaves.

Development source pending checking by the pinned Lean compiler.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open TauCeti.Toric ToricPower.IntegralArrangement Opposite



namespace ToricPower

universe u

/-- An actual frame over an open sends one on a smaller open to the
restriction of its frame section on the whole open. -/
theorem overFrame_one_restrict {X : Scheme.{u}} (M : X.Modules)
    {U W : X.Opens} (h : W ≤ U)
    (frame : (SheafOfModules.unit X.ringCatSheaf).over U ≅ M.over U) :
    frame.hom.val.app (op (Over.mk (homOfLE h))) (1 : Γ(X, W)) =
      M.presheaf.map (homOfLE h).op
        (frame.hom.val.app (op (Over.mk (𝟙 U))) (1 : Γ(X, U))) := by
  let comparison : Over.mk (homOfLE h) ⟶ Over.mk (𝟙 U) :=
    Over.homMk (homOfLE h)
  have naturality := ConcreteCategory.congr_hom
    (frame.hom.val.naturality comparison.op) (1 : Γ(X, U))
  change frame.hom.val.app (op (Over.mk (homOfLE h)))
      (X.presheaf.map (homOfLE h).op (1 : Γ(X, U))) =
    M.presheaf.map (homOfLE h).op
      (frame.hom.val.app (op (Over.mk (𝟙 U))) (1 : Γ(X, U))) at naturality
  rw [map_one] at naturality
  exact naturality

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {latticeMap : N →+ V}
  (fan : Fan latticeMap) (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  (σ τ : fan.cones)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "chart" => diagonalProductChartι fan basis rays σ τ
local notation "overlap" => fan.affineToricChartι (σ ⊓ τ)
local notation "g" => Spec.map (CommRingCat.ofHom (diagonalChartToIntersection fan basis rays σ τ))
local notation "leftMap" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (diagonalProductFirstCoordinate fan basis rays σ τ)))
local notation "rightMap" => Spec.map (CommRingCat.ofHom
  (AlgHom.toRingHom (diagonalProductSecondCoordinate fan basis rays σ τ)))

local instance : IsOpenImmersion (fan.affineToricOverlapLeft σ τ) := by
  haveI : IsOpenImmersion
      (fan.affineToricOverlapLeft σ τ ≫ fan.affineToricChartι σ) := by
    rw [fan.affineToricOverlapLeft_comp_affineToricChartι]
    infer_instance
  exact IsOpenImmersion.of_comp _ (fan.affineToricChartι σ)

local instance : IsOpenImmersion (fan.affineToricOverlapRight σ τ) := by
  haveI : IsOpenImmersion
      (fan.affineToricOverlapRight σ τ ≫ fan.affineToricChartι τ) := by
    rw [fan.affineToricOverlapRight_comp_affineToricChartι]
    infer_instance
  exact IsOpenImmersion.of_comp _ (fan.affineToricChartι τ)

/-- The first coordinate of the actual affine diagonal is the actual
overlap inclusion, with no chosen abstract identification of these maps. -/
theorem diagonalChartToIntersection_first :
    g ≫ leftMap = fan.affineToricOverlapLeft σ τ := by
  apply (cancel_mono (fan.affineToricChartι σ)).mp
  rw [Category.assoc, ← diagonalProductChartι_first,
    ← Category.assoc, ← (diagonalProductChart_isPullback fan basis rays σ τ).w,
    Category.assoc, toricDiagonalFirst, pullback.diagonal_fst, Category.comp_id,
    fan.affineToricOverlapLeft_comp_affineToricChartι]

/-- The second coordinate of the actual affine diagonal is the actual
second overlap inclusion. -/
theorem diagonalChartToIntersection_second :
    g ≫ rightMap = fan.affineToricOverlapRight σ τ := by
  apply (cancel_mono (fan.affineToricChartι τ)).mp
  rw [Category.assoc, ← diagonalProductChartι_second,
    ← Category.assoc, ← (diagonalProductChart_isPullback fan basis rays σ τ).w,
    Category.assoc, toricDiagonalSecond, pullback.diagonal_snd, Category.comp_id,
    fan.affineToricOverlapRight_comp_affineToricChartι]

/-- The first frame restricted through the complete actual diagonal
square is the literal Cartier frame on the overlap image. -/
theorem diagonalRestrictedFirstFrameMap_image {d : ℕ}
    (c : NormalizedCell A d) :
    Scheme.Modules.Hom.app
        (diagonalRestrictedFirstFrameMap fan nonempty regular basis rays σ τ c) ⊤ (1 : Γ(fan.affineToricChart (σ ⊓ τ), ⊤)) =
      (invariantCartierSheafChartTrivialization fan nonempty regular
        (diagonalLeftCoefficients fan basis rays c) σ).hom.val.app
        (op (Over.mk (homOfLE (show overlap ''ᵁ ⊤ ≤
          (fan.affineToricChartι σ).opensRange by
            simpa only [← Scheme.Hom.comp_image,
              fan.affineToricOverlapLeft_comp_affineToricChartι] using
              (fan.affineToricChartι σ).image_le_opensRange
                (fan.affineToricOverlapLeft σ τ ''ᵁ ⊤)))))
        (1 : Γ(fan.algebraicRealization, overlap ''ᵁ ⊤)) := by
  letI := toricSchemeIntegral fan nonempty
  have first := diagonalChartToIntersection_first fan basis rays σ τ
  haveI : IsOpenImmersion (g ≫ leftMap) := by
    rw [first]
    infer_instance
  have triangle : (g ≫ leftMap) ≫ fan.affineToricChartι σ = overlap := by
    rw [first, fan.affineToricOverlapLeft_comp_affineToricChartι]
  have path := Scheme.Modules.section_square_frame_restriction
    (toricDiagonal fan) (toricDiagonalFirst fan) overlap chart g
    (fan.affineToricChartι σ) leftMap
    (pullback.diagonal_fst fan.algebraicRealizationStructureMap)
    (diagonalProductChart_isPullback fan basis rays σ τ).w
    (diagonalProductChartι_first fan basis rays σ τ) triangle
    (diagonalLeftSheaf fan nonempty regular basis rays c)
    (toricCartierAffineFrame fan nonempty regular
      (diagonalLeftCoefficients fan basis rays c) σ).hom
  have normalized :
      diagonalRestrictedFirstFrameMap fan nonempty regular basis rays σ τ c =
      (Scheme.Modules.restrictUnitIso (g ≫ leftMap)).inv ≫
        (Scheme.Modules.restrictFunctor (g ≫ leftMap)).map
          (toricCartierAffineFrame fan nonempty regular
            (diagonalLeftCoefficients fan basis rays c) σ).hom ≫
        (Scheme.Modules.restrictFunctorComp (g ≫ leftMap)
          (fan.affineToricChartι σ)).inv.app _ ≫
        (Scheme.Modules.restrictFunctorCongr triangle).hom.app _ := by
    simpa only [diagonalLeftSheaf, diagonalRestrictedFirstFrameMap, diagonalFirstCartierFrame,
      schemeFrameTransport, schemePullbackFrame, diagonalFirstPullbackComparison,
      diagonalFirstPullbackIso, Scheme.Modules.sectionPullbackIso,
      toricCartierPullbackFrame, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, NatTrans.comp_app,
      Functor.map_comp, Category.assoc] using path
  rw [normalized]
  exact Scheme.Modules.restriction_composite_frame_one (g ≫ leftMap)
    (fan.affineToricChartι σ) overlap triangle _ _ ⊤

/-- The second factor has the same literal restriction normalization. -/
theorem diagonalRestrictedSecondFrameMap_image {d : ℕ}
    (c : NormalizedCell A d) :
    Scheme.Modules.Hom.app
        (diagonalRestrictedSecondFrameMap fan nonempty regular basis rays σ τ c) ⊤ (1 : Γ(fan.affineToricChart (σ ⊓ τ), ⊤)) =
      (invariantCartierSheafChartTrivialization fan nonempty regular
        (diagonalRightCoefficients fan basis rays c) τ).hom.val.app
        (op (Over.mk (homOfLE (show overlap ''ᵁ ⊤ ≤
          (fan.affineToricChartι τ).opensRange by
            simpa only [← Scheme.Hom.comp_image,
              fan.affineToricOverlapRight_comp_affineToricChartι] using
              (fan.affineToricChartι τ).image_le_opensRange
                (fan.affineToricOverlapRight σ τ ''ᵁ ⊤)))))
        (1 : Γ(fan.algebraicRealization, overlap ''ᵁ ⊤)) := by
  letI := toricSchemeIntegral fan nonempty
  have second := diagonalChartToIntersection_second fan basis rays σ τ
  haveI : IsOpenImmersion (g ≫ rightMap) := by
    rw [second]
    infer_instance
  have triangle : (g ≫ rightMap) ≫ fan.affineToricChartι τ = overlap := by
    rw [second, fan.affineToricOverlapRight_comp_affineToricChartι]
  have path := Scheme.Modules.section_square_frame_restriction
    (toricDiagonal fan) (toricDiagonalSecond fan) overlap chart g
    (fan.affineToricChartι τ) rightMap
    (pullback.diagonal_snd fan.algebraicRealizationStructureMap)
    (diagonalProductChart_isPullback fan basis rays σ τ).w
    (diagonalProductChartι_second fan basis rays σ τ) triangle
    (diagonalRightSheaf fan nonempty regular basis rays c)
    (toricCartierAffineFrame fan nonempty regular
      (diagonalRightCoefficients fan basis rays c) τ).hom
  have normalized :
      diagonalRestrictedSecondFrameMap fan nonempty regular basis rays σ τ c =
      (Scheme.Modules.restrictUnitIso (g ≫ rightMap)).inv ≫
        (Scheme.Modules.restrictFunctor (g ≫ rightMap)).map
          (toricCartierAffineFrame fan nonempty regular
            (diagonalRightCoefficients fan basis rays c) τ).hom ≫
        (Scheme.Modules.restrictFunctorComp (g ≫ rightMap)
          (fan.affineToricChartι τ)).inv.app _ ≫
        (Scheme.Modules.restrictFunctorCongr triangle).hom.app _ := by
    simpa only [diagonalRightSheaf, diagonalRestrictedSecondFrameMap, diagonalSecondCartierFrame,
      schemeFrameTransport, schemePullbackFrame, diagonalSecondPullbackComparison,
      diagonalSecondPullbackIso, Scheme.Modules.sectionPullbackIso,
      toricCartierPullbackFrame, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, Iso.symm_inv,
      Functor.mapIso_hom, Iso.app_hom, Iso.app_inv, NatTrans.comp_app,
      Functor.map_comp, Category.assoc] using path
  rw [normalized]
  exact Scheme.Modules.restriction_composite_frame_one (g ≫ rightMap)
    (fan.affineToricChartι τ) overlap triangle _ _ ⊤

/-- The intersection chart open lies in the first chart open. -/
theorem diagonalOverlapOpen_le_first :
    (overlap).opensRange ≤ (fan.affineToricChartι σ).opensRange := by
  change Set.range overlap ⊆ Set.range (fan.affineToricChartι σ)
  rintro _ ⟨x, rfl⟩
  refine ⟨fan.affineToricOverlapLeft σ τ x, ?_⟩
  rw [← Scheme.Hom.comp_apply, fan.affineToricOverlapLeft_comp_affineToricChartι]
  rfl

/-- The intersection chart open lies in the second chart open. -/
theorem diagonalOverlapOpen_le_second :
    (overlap).opensRange ≤ (fan.affineToricChartι τ).opensRange := by
  change Set.range overlap ⊆ Set.range (fan.affineToricChartι τ)
  rintro _ ⟨x, rfl⟩
  refine ⟨fan.affineToricOverlapRight σ τ x, ?_⟩
  rw [← Scheme.Hom.comp_apply, fan.affineToricOverlapRight_comp_affineToricChartι]
  rfl

/-- The first actual factor path evaluates to the specified Cartier
frame section restricted to the actual intersection open. -/
theorem diagonalRestrictedFirstFrameMap_top {d : ℕ}
    (c : NormalizedCell A d) :
    Scheme.Modules.Hom.app
        (diagonalRestrictedFirstFrameMap fan nonempty regular basis rays σ τ c) ⊤ (1 : Γ(fan.affineToricChart (σ ⊓ τ), ⊤)) =
      (diagonalLeftSheaf fan nonempty regular basis rays c).presheaf.map
        (eqToHom (overlap).image_top_eq_opensRange).op
        ((diagonalLeftSheaf fan nonempty regular basis rays c).presheaf.map
          (homOfLE (diagonalOverlapOpen_le_first fan σ τ)).op
          ((invariantCartierSheafChartTrivialization fan nonempty regular
            (diagonalLeftCoefficients fan basis rays c) σ).hom.val.app
            (op (Over.mk (𝟙 (fan.affineToricChartι σ).opensRange)))
            (1 : Γ(fan.algebraicRealization, (fan.affineToricChartι σ).opensRange)))) := by
  letI := toricSchemeIntegral fan nonempty
  rw [diagonalRestrictedFirstFrameMap_image, overFrame_one_restrict]
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  rfl

/-- The analogous exact restriction formula for the second factor. -/
theorem diagonalRestrictedSecondFrameMap_top {d : ℕ}
    (c : NormalizedCell A d) :
    Scheme.Modules.Hom.app
        (diagonalRestrictedSecondFrameMap fan nonempty regular basis rays σ τ c) ⊤ (1 : Γ(fan.affineToricChart (σ ⊓ τ), ⊤)) =
      (diagonalRightSheaf fan nonempty regular basis rays c).presheaf.map
        (eqToHom (overlap).image_top_eq_opensRange).op
        ((diagonalRightSheaf fan nonempty regular basis rays c).presheaf.map
          (homOfLE (diagonalOverlapOpen_le_second fan σ τ)).op
          ((invariantCartierSheafChartTrivialization fan nonempty regular
            (diagonalRightCoefficients fan basis rays c) τ).hom.val.app
            (op (Over.mk (𝟙 (fan.affineToricChartι τ).opensRange)))
            (1 : Γ(fan.algebraicRealization, (fan.affineToricChartι τ).opensRange)))) := by
  letI := toricSchemeIntegral fan nonempty
  rw [diagonalRestrictedSecondFrameMap_image, overFrame_one_restrict]
  simp only [← ConcreteCategory.comp_apply, ← Functor.map_comp, ← op_comp]
  rfl

end ToricPower

end
