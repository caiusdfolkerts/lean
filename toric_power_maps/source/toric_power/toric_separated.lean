module

public import ToricPower.GeometricCore
public import TauCeti.Geometry.Toric.Algebraic.DualSemigroup.Separation
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.RingTheory.TensorProduct.Maps

/-!
# The actual fan scheme is separated

For arbitrary cones of a finite rational fan, the proved integral dual-cone
separation theorem decomposes each overlap character as a sum of characters
on the two charts. Consequently the literal tensor-product restriction map
is surjective. The genuine overlap pullback and affine product open cover
then make the actual diagonal a closed immersion.

No completeness, full-dimensionality, smoothness, or a separatedness premise
is used. This adapts the explicit geometric argument from the recovered
BondalThomsen `Toric/Scheme/{OverlapAlgebra,Separated}` sources to the current
TauCeti fan scheme, whose charts are already constructed for arbitrary cones.

Candidate source: every declaration still requires the pinned compiler.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000

open AlgebraicGeometry CategoryTheory Limits Multiplicative
open scoped TensorProduct

namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [AddCommGroup Ambient] [Module ℝ Ambient]
    {embedding : Lattice →+ Ambient}

noncomputable def overlapTensorMap (fan : Fan embedding) (first second : fan.cones) :
    affineCoordinateRing fan.lattice first.val ⊗[ℂ] affineCoordinateRing fan.lattice second.val →ₐ[ℂ]
      affineCoordinateRing fan.lattice (first.val ⊓ second.val) :=
  Algebra.TensorProduct.productMap
    (faceAffineCoordinateRingMap fan.lattice (fan.inf_isFaceOf_left first.property second.property))
    (faceAffineCoordinateRingMap fan.lattice (fan.inf_isFaceOf_right first.property second.property))

theorem overlap_character_decomposition (fan : Fan embedding) (first second : fan.cones)
    (character : dualSemigroup fan.lattice (first.val ⊓ second.val)) :
    ∃ first_character : dualSemigroup fan.lattice first.val,
      ∃ second_character : dualSemigroup fan.lattice second.val,
        (first_character : Lattice →+ ℤ) + second_character = character := by
  have member : (character : Lattice →+ ℤ) ∈
      dualSemigroup fan.lattice first.val ⊔ dualSemigroup fan.lattice second.val := by
    rw [← fan.dualSemigroup_inf_eq_sup first.property second.property]
    exact character.property
  rw [AddSubmonoid.mem_sup] at member
  obtain ⟨first_character, first_member, second_character, second_member, same⟩ := member
  exact ⟨⟨first_character, first_member⟩, ⟨second_character, second_member⟩, same⟩

theorem overlap_monomial_mem_tensor_range (fan : Fan embedding) (first second : fan.cones)
    (character : dualSemigroup fan.lattice (first.val ⊓ second.val)) :
    MonoidAlgebra.single (ofAdd character) (1 : ℂ) ∈ (fan.overlapTensorMap first second).range := by
  obtain ⟨first_character, second_character, same⟩ :=
    fan.overlap_character_decomposition first second character
  refine ⟨MonoidAlgebra.single (ofAdd first_character) 1 ⊗ₜ[ℂ]
    MonoidAlgebra.single (ofAdd second_character) 1, ?_⟩
  change (fan.overlapTensorMap first second)
    (MonoidAlgebra.single (ofAdd first_character) 1 ⊗ₜ[ℂ]
      MonoidAlgebra.single (ofAdd second_character) 1) = _
  rw [overlapTensorMap, Algebra.TensorProduct.productMap_apply_tmul,
    faceAffineCoordinateRingMap_single, faceAffineCoordinateRingMap_single,
    MonoidAlgebra.single_mul_single]
  congr 1
  · apply congrArg ofAdd
    exact Subtype.ext same
  · simp

theorem overlapTensorMap_surjective (fan : Fan embedding) (first second : fan.cones) :
    Function.Surjective (fan.overlapTensorMap first second) := by
  apply (AlgHom.range_eq_top _).mp
  apply top_unique
  intro polynomial
  change True → polynomial ∈ (fan.overlapTensorMap first second).range
  rw [true_implies]
  induction polynomial using MonoidAlgebra.induction_on with
  | of character =>
    change MonoidAlgebra.single character 1 ∈ _
    exact fan.overlap_monomial_mem_tensor_range first second (toAdd character)
  | add first_polynomial second_polynomial first_member second_member =>
    exact (fan.overlapTensorMap first second).range.add_mem first_member second_member
  | smul coefficient polynomial member =>
    exact (fan.overlapTensorMap first second).range.smul_mem member coefficient

end TauCeti.Toric.Fan


namespace TauCeti.Toric.Fan

variable {Lattice : Type} {Ambient : Type*} [AddCommGroup Lattice]
    [AddCommGroup Ambient] [Module ℝ Ambient]
    {embedding : Lattice →+ Ambient}

theorem affineToricOverlap_isPullback (fan : Fan embedding)
    (first second : fan.cones) :
    IsPullback (fan.affineToricOverlapLeft first second)
      (fan.affineToricOverlapRight first second)
      (fan.affineToricChartι first) (fan.affineToricChartι second) := by
  letI := fan.isOpenImmersion_affineToricOverlapLeft first second
  apply IsPullback.flip
  apply IsOpenImmersion.isPullback
  · exact fan.affineToricOverlap_comp_affineToricChartι first second
  · ext point
    change fan.affineToricChartι first point ∈
        Set.range (fan.affineToricChartι second) ↔
      point ∈ Set.range (fan.affineToricOverlapLeft first second)
    constructor
    · rintro ⟨second_point, same⟩
      obtain ⟨overlap_point, left_eq, _⟩ :=
        (fan.affineToricChartι_eq_affineToricChartι_iff point second_point).mp
          same.symm
      exact ⟨overlap_point, left_eq⟩
    · rintro ⟨overlap_point, rfl⟩
      refine ⟨fan.affineToricOverlapRight first second overlap_point, ?_⟩
      have same := congrArg (fun morphism : fan.affineToricOverlap first second ⟶
        fan.algebraicRealization => morphism overlap_point)
        (fan.affineToricOverlap_comp_affineToricChartι first second)
      simpa only [Scheme.Hom.comp_apply] using same.symm

noncomputable def chartTensorProductIso (fan : Fan embedding) (first second : fan.cones) :
    Spec (CommRingCat.of (affineCoordinateRing fan.lattice first.val ⊗[ℂ]
      affineCoordinateRing fan.lattice second.val)) ≅
      pullback
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ (affineCoordinateRing fan.lattice first.val))))
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ (affineCoordinateRing fan.lattice second.val)))) :=
  (isPullback_SpecMap_of_isPushout _ _ _ _
    (CommRingCat.isPushout_tensorProduct ℂ (affineCoordinateRing fan.lattice first.val)
      (affineCoordinateRing fan.lattice second.val))).isoPullback

noncomputable def overlapToChartProduct (fan : Fan embedding) (first second : fan.cones) :
    fan.affineToricOverlap first second ⟶
      pullback
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ (affineCoordinateRing fan.lattice first.val))))
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ (affineCoordinateRing fan.lattice second.val)))) :=
  Spec.map (CommRingCat.ofHom (fan.overlapTensorMap first second).toRingHom) ≫
    (fan.chartTensorProductIso first second).hom

theorem overlapToChartProduct_fst (fan : Fan embedding) (first second : fan.cones) :
    fan.overlapToChartProduct first second ≫ pullback.fst _ _ =
      fan.affineToricOverlapLeft first second := by
  rw [overlapToChartProduct, chartTensorProductIso, Category.assoc,
    IsPullback.isoPullback_hom_fst, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    (((fan.overlapTensorMap first second).comp Algebra.TensorProduct.includeLeft).toRingHom)) = _
  rw [overlapTensorMap, Algebra.TensorProduct.productMap_left]
  rw [affineToricOverlapLeft_def, faceAffineToricSchemeMap_def]

theorem overlapToChartProduct_snd (fan : Fan embedding) (first second : fan.cones) :
    fan.overlapToChartProduct first second ≫ pullback.snd _ _ =
      fan.affineToricOverlapRight first second := by
  rw [overlapToChartProduct, chartTensorProductIso, Category.assoc,
    IsPullback.isoPullback_hom_snd, ← Spec.map_comp]
  change Spec.map (CommRingCat.ofHom
    (((fan.overlapTensorMap first second).comp Algebra.TensorProduct.includeRight).toRingHom)) = _
  rw [overlapTensorMap, Algebra.TensorProduct.productMap_right]
  rw [affineToricOverlapRight_def, faceAffineToricSchemeMap_def]

theorem overlapToChartProduct_isClosedImmersion (fan : Fan embedding) (first second : fan.cones) :
    IsClosedImmersion (fan.overlapToChartProduct first second) := by
  letI := IsClosedImmersion.spec_of_surjective
    (CommRingCat.ofHom (fan.overlapTensorMap first second).toRingHom)
    (fan.overlapTensorMap_surjective first second)
  unfold overlapToChartProduct
  infer_instance

theorem chartIntersectionComparison_isClosedImmersion (fan : Fan embedding)
    (first second : fan.cones) :
    IsClosedImmersion (pullback.map
      (fan.affineToricChartι first) (fan.affineToricChartι second)
      (fan.affineToricChartι first ≫ fan.algebraicRealizationStructureMap)
      (fan.affineToricChartι second ≫ fan.algebraicRealizationStructureMap)
      (𝟙 _) (𝟙 _) (fan.algebraicRealizationStructureMap) (by simp) (by simp)) := by
  let intersection_iso := (fan.affineToricOverlap_isPullback first second).isoPullback
  let product_iso := pullback.congrHom
    (fan.affineToricChartι_comp_algebraicRealizationStructureMap first)
    (fan.affineToricChartι_comp_algebraicRealizationStructureMap second)
  let comparison := pullback.map
      (fan.affineToricChartι first) (fan.affineToricChartι second)
      (fan.affineToricChartι first ≫ fan.algebraicRealizationStructureMap)
      (fan.affineToricChartι second ≫ fan.algebraicRealizationStructureMap)
      (𝟙 _) (𝟙 _) (fan.algebraicRealizationStructureMap) (by simp) (by simp)
  have same : intersection_iso.hom ≫ comparison ≫ product_iso.hom =
      fan.overlapToChartProduct first second := by
    apply pullback.hom_ext
    · simp [intersection_iso, product_iso, comparison,
        fan.overlapToChartProduct_fst first second]
    · simp [intersection_iso, product_iso, comparison,
        fan.overlapToChartProduct_snd first second]
  have closed : IsClosedImmersion (intersection_iso.hom ≫ comparison ≫ product_iso.hom) := by
    rw [same]
    exact fan.overlapToChartProduct_isClosedImmersion first second
  rw [MorphismProperty.cancel_left_of_respectsIso @IsClosedImmersion,
    MorphismProperty.cancel_right_of_respectsIso @IsClosedImmersion] at closed
  exact closed

theorem algebraicRealizationStructureMap_isSeparated (fan : Fan embedding) :
    IsSeparated (fan.algebraicRealizationStructureMap) := by
  constructor
  let cover := Scheme.Pullback.openCoverOfLeftRight
    (fan.affineToricOpenCover) (fan.affineToricOpenCover)
    (fan.algebraicRealizationStructureMap) (fan.algebraicRealizationStructureMap)
  apply IsZariskiLocalAtTarget.of_openCover (P := @IsClosedImmersion) cover
  intro pair
  let square := pullback_map_diagonal_isPullback
    (fan.affineToricChartι pair.1) (fan.affineToricChartι pair.2)
    (fan.algebraicRealizationStructureMap)
  letI := fan.chartIntersectionComparison_isClosedImmersion pair.1 pair.2
  have closed : IsClosedImmersion (square.isoPullback.inv ≫
      pullback.map (fan.affineToricChartι pair.1) (fan.affineToricChartι pair.2)
        (fan.affineToricChartι pair.1 ≫ fan.algebraicRealizationStructureMap)
        (fan.affineToricChartι pair.2 ≫ fan.algebraicRealizationStructureMap)
        (𝟙 _) (𝟙 _) (fan.algebraicRealizationStructureMap) (by simp) (by simp)) := by
    infer_instance
  rw [IsPullback.isoPullback_inv_snd] at closed
  exact closed

theorem algebraicRealization_isSeparated (fan : Fan embedding) :
    (fan.algebraicRealization).IsSeparated := by
  letI := fan.algebraicRealizationStructureMap_isSeparated
  letI : (Spec (CommRingCat.of ℂ)).IsSeparated := inferInstance
  constructor
  have same : fan.algebraicRealizationStructureMap ≫ terminal.from (Spec (CommRingCat.of ℂ)) =
      terminal.from (fan.algebraicRealization) := terminalIsTerminal.hom_ext _ _
  rw [← same]
  infer_instance

end TauCeti.Toric.Fan
