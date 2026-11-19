module

public import ToricPower.DiagonalToricAugmentation
public import ToricPower.ToricSeparated
public import Mathlib.RingTheory.TensorProduct.MonoidAlgebra

/-!
# The cellular augmentation is the actual affine diagonal map

The product semigroup algebra used in the cellular calculation is explicitly
identified with the tensor product of the two actual chart coordinate rings.
Under this algebra isomorphism the augmentation ring map is the actual
restriction from the product chart to its intersection chart. Applying `Spec`
identifies it with the pullback of the genuine scheme diagonal.

This is a comparison of the explicitly constructed maps, not a choice of an
unrelated isomorphic module. All cones and all ambient lattice directions
are retained. Candidate source pending the pinned compiler.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric
open ToricPower.IntegralArrangement
open scoped TensorProduct Classical

namespace ToricPower

/-- Monomials in a product monoid are pure tensors in the stated order. -/
def monoidAlgebraProductTensorEquiv (M Q : Type*) [CommMonoid M] [CommMonoid Q] :
    MonoidAlgebra ℂ (M × Q) ≃ₐ[ℂ]
      MonoidAlgebra ℂ M ⊗[ℂ] MonoidAlgebra ℂ Q :=
  ((MonoidAlgebra.domCongr ℂ ℂ (MulEquiv.prodComm : M × Q ≃* Q × M)).trans
    (MonoidAlgebra.curryAlgEquiv ℂ)).trans
      ((MonoidAlgebra.scalarTensorEquiv ℂ (MonoidAlgebra ℂ M) (M := Q)).symm.restrictScalars ℂ)

@[simp]
theorem monoidAlgebraProductTensorEquiv_single
    (M Q : Type*) [CommMonoid M] [CommMonoid Q] (m : M) (q : Q) (r : ℂ) :
    monoidAlgebraProductTensorEquiv M Q (MonoidAlgebra.single (m,q) r) =
      MonoidAlgebra.single m r ⊗ₜ[ℂ] MonoidAlgebra.single q 1 := by
  simp [monoidAlgebraProductTensorEquiv]

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {latticeMap : N →+ V}
  (fan : Fan latticeMap) {n s : ℕ}
  (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  (σ τ : fan.cones)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "S" => fanConeRaySet fan rays σ
local notation "T" => fanConeRaySet fan rays τ
local notation "R" => DiagonalChartRing ℂ A S T
local notation "Rσ" => affineCoordinateRing fan.lattice σ.val
local notation "Rτ" => affineCoordinateRing fan.lattice τ.val

def diagonalProductMonoidEquiv :
    Multiplicative (rayCharacterMonoid A S × rayCharacterMonoid A T) ≃*
      Multiplicative (dualSemigroup fan.lattice σ.val) ×
        Multiplicative (dualSemigroup fan.lattice τ.val) where
  toFun p :=
    (Multiplicative.ofAdd ((fanRayCharacterMonoidEquiv fan basis rays σ) p.toAdd.1),
      Multiplicative.ofAdd ((fanRayCharacterMonoidEquiv fan basis rays τ) p.toAdd.2))
  invFun p := Multiplicative.ofAdd
    (((fanRayCharacterMonoidEquiv fan basis rays σ).symm p.1.toAdd),
      ((fanRayCharacterMonoidEquiv fan basis rays τ).symm p.2.toAdd))
  left_inv p := by simp
  right_inv p := by simp
  map_mul' p q := by
    apply Prod.ext
    · exact congrArg Multiplicative.ofAdd
        ((fanRayCharacterMonoidEquiv fan basis rays σ).map_add p.toAdd.1 q.toAdd.1)
    · exact congrArg Multiplicative.ofAdd
        ((fanRayCharacterMonoidEquiv fan basis rays τ).map_add p.toAdd.2 q.toAdd.2)

/-- The literal cellular chart ring is the coordinate ring of the
affine product chart, with both factor coordinates specified. -/
def diagonalProductCoordinateEquiv : R ≃ₐ[ℂ] Rσ ⊗[ℂ] Rτ :=
  ((AddMonoidAlgebra.toMultiplicativeAlgEquiv ℂ ℂ _).trans
    (MonoidAlgebra.domCongr ℂ ℂ
      (diagonalProductMonoidEquiv fan basis rays σ τ))).trans
        (monoidAlgebraProductTensorEquiv _ _)

@[simp]
theorem diagonalProductCoordinateEquiv_single
    (p : rayCharacterMonoid A S × rayCharacterMonoid A T) (r : ℂ) :
    diagonalProductCoordinateEquiv fan basis rays σ τ (AddMonoidAlgebra.single p r) =
      MonoidAlgebra.single
          (Multiplicative.ofAdd ((fanRayCharacterMonoidEquiv fan basis rays σ) p.1)) r ⊗ₜ[ℂ]
        MonoidAlgebra.single
          (Multiplicative.ofAdd ((fanRayCharacterMonoidEquiv fan basis rays τ) p.2)) 1 := by
  simp [diagonalProductCoordinateEquiv,diagonalProductMonoidEquiv]

/-- The cellular scalar map is exactly the actual overlap tensor map. -/
theorem diagonalProductCoordinateEquiv_comp_overlap :
    (fan.overlapTensorMap σ τ).toRingHom.comp
        (diagonalProductCoordinateEquiv fan basis rays σ τ).toRingHom =
      diagonalChartToIntersection fan basis rays σ τ := by
  apply RingHom.ext
  intro f
  induction f using AddMonoidAlgebra.induction with
  | zero => simp
  | single_add p r f _ _ ih =>
      simp only [map_add,ih]
      congr 1
      change (fan.overlapTensorMap σ τ)
          (diagonalProductCoordinateEquiv fan basis rays σ τ
            (AddMonoidAlgebra.single p r)) =
        diagonalChartToIntersection fan basis rays σ τ (AddMonoidAlgebra.single p r)
      rw [diagonalProductCoordinateEquiv_single,
        TauCeti.Toric.Fan.overlapTensorMap,
        Algebra.TensorProduct.productMap_apply_tmul,
        faceAffineCoordinateRingMap_single,faceAffineCoordinateRingMap_single,
        MonoidAlgebra.single_mul_single,diagonalChartToIntersection_single,mul_one]
      congr 1
      apply congrArg Multiplicative.ofAdd
      apply Subtype.ext
      exact (basis.equivFun.symm.map_add p.1.val p.2.val).symm

theorem diagonalChartToIntersection_comp_inverse :
    (diagonalChartToIntersection fan basis rays σ τ).comp
        (diagonalProductCoordinateEquiv fan basis rays σ τ).symm.toRingHom =
      (fan.overlapTensorMap σ τ).toRingHom := by
  rw [← diagonalProductCoordinateEquiv_comp_overlap]
  apply RingHom.ext
  intro f
  exact congrArg (fan.overlapTensorMap σ τ)
    ((diagonalProductCoordinateEquiv fan basis rays σ τ).apply_symm_apply f)

/-- The actual affine product chart, expressed in the cellular ring. -/
def diagonalProductChartIso :
    Spec (.of R) ≅
      pullback (Spec.map (CommRingCat.ofHom (algebraMap ℂ Rσ)))
        (Spec.map (CommRingCat.ofHom (algebraMap ℂ Rτ))) :=
  Scheme.Spec.mapIso
      (diagonalProductCoordinateEquiv fan basis rays σ τ).symm.toRingEquiv.toCommRingCatIso.op ≪≫
    fan.chartTensorProductIso σ τ

/-- The augmentation is the actual overlap-to-product morphism under
the displayed affine coordinate isomorphism. -/
@[reassoc]
theorem diagonalChartToIntersection_Spec :
    Spec.map (CommRingCat.ofHom (diagonalChartToIntersection fan basis rays σ τ)) ≫
        (diagonalProductChartIso fan basis rays σ τ).hom =
      fan.overlapToChartProduct σ τ := by
  change Spec.map (CommRingCat.ofHom (diagonalChartToIntersection fan basis rays σ τ)) ≫
      Spec.map (CommRingCat.ofHom (diagonalProductCoordinateEquiv fan basis rays σ τ).symm.toRingHom) ≫
      (fan.chartTensorProductIso σ τ).hom = _
  rw [← Spec.map_comp_assoc]
  change Spec.map (CommRingCat.ofHom
      ((diagonalChartToIntersection fan basis rays σ τ).comp
        (diagonalProductCoordinateEquiv fan basis rays σ τ).symm.toRingHom)) ≫ _ = _
  rw [diagonalChartToIntersection_comp_inverse]
  rfl

/-- The standard product cover of the actual toric self-product. -/
def diagonalAffineProductCover : (toricDiagonalProduct fan).OpenCover :=
  Scheme.Pullback.openCoverOfLeftRight fan.affineToricOpenCover fan.affineToricOpenCover
    fan.algebraicRealizationStructureMap fan.algebraicRealizationStructureMap

/-- Coordinate identification with the canonical pullback chart. Keeping
the target explicit avoids reduction through the cover's chosen objects. -/
def diagonalProductCanonicalIso : Spec (.of R) ≅
    pullback (fan.affineToricChartι σ ≫ fan.algebraicRealizationStructureMap)
      (fan.affineToricChartι τ ≫ fan.algebraicRealizationStructureMap) :=
  diagonalProductChartIso fan basis rays σ τ ≪≫
    (pullback.congrHom
      (fan.affineToricChartι_comp_algebraicRealizationStructureMap σ)
      (fan.affineToricChartι_comp_algebraicRealizationStructureMap τ)).symm

/-- The canonical chart is the corresponding actual product-cover member. -/
abbrev diagonalProductCoverIso : Spec (.of R) ≅
    (diagonalAffineProductCover fan).X (σ,τ) :=
  diagonalProductCanonicalIso fan basis rays σ τ

def diagonalProductChartι : Spec (.of R) ⟶ toricDiagonalProduct fan :=
  (diagonalProductCoverIso fan basis rays σ τ).hom ≫
    (diagonalAffineProductCover fan).f (σ,τ)

instance diagonalProductChartι_isOpenImmersion :
    IsOpenImmersion (diagonalProductChartι fan basis rays σ τ) := by
  unfold diagonalProductChartι
  infer_instance

/-- The same genuine affine product cover, with every member expressed
in the literal semigroup coordinates used by the cellular complex. -/
def diagonalCoordinateOpenCover : (toricDiagonalProduct fan).OpenCover :=
  (diagonalAffineProductCover fan).copy
    (fan.cones × fan.cones)
    (fun p => Spec (.of (DiagonalChartRing ℂ (fanArrangementMatrix fan basis rays)
      (fanConeRaySet fan rays p.1) (fanConeRaySet fan rays p.2))))
    (fun p => diagonalProductChartι fan basis rays p.1 p.2)
    (Equiv.refl _) (fun p => diagonalProductCoverIso fan basis rays p.1 p.2)
    (fun _ => rfl)

/-- The first factor's actual coordinate embedding in the cellular ring. -/
def diagonalProductFirstCoordinate : Rσ →ₐ[ℂ] R :=
  (diagonalProductCoordinateEquiv fan basis rays σ τ).symm.toAlgHom.comp
    Algebra.TensorProduct.includeLeft

/-- The second factor's actual coordinate embedding in the cellular ring. -/
def diagonalProductSecondCoordinate : Rτ →ₐ[ℂ] R :=
  (diagonalProductCoordinateEquiv fan basis rays σ τ).symm.toAlgHom.comp
    Algebra.TensorProduct.includeRight

@[reassoc]
theorem diagonalProductChartIso_first :
    (diagonalProductChartIso fan basis rays σ τ).hom ≫ pullback.fst _ _ =
      Spec.map (CommRingCat.ofHom (diagonalProductFirstCoordinate fan basis rays σ τ).toRingHom) := by
  change Spec.map (CommRingCat.ofHom
      (diagonalProductCoordinateEquiv fan basis rays σ τ).symm.toRingHom) ≫
      (fan.chartTensorProductIso σ τ).hom ≫ pullback.fst _ _ = _
  rw [TauCeti.Toric.Fan.chartTensorProductIso,
    IsPullback.isoPullback_hom_fst,← Spec.map_comp]
  rfl

@[reassoc]
theorem diagonalProductChartIso_second :
    (diagonalProductChartIso fan basis rays σ τ).hom ≫ pullback.snd _ _ =
      Spec.map (CommRingCat.ofHom (diagonalProductSecondCoordinate fan basis rays σ τ).toRingHom) := by
  change Spec.map (CommRingCat.ofHom
      (diagonalProductCoordinateEquiv fan basis rays σ τ).symm.toRingHom) ≫
      (fan.chartTensorProductIso σ τ).hom ≫ pullback.snd _ _ = _
  rw [TauCeti.Toric.Fan.chartTensorProductIso,
    IsPullback.isoPullback_hom_snd,← Spec.map_comp]
  rfl

/-- The first projection on the product affine chart is the actual
first factor-coordinate ring embedding followed by its chart inclusion. -/
@[reassoc]
theorem diagonalProductChartι_first :
    diagonalProductChartι fan basis rays σ τ ≫ toricDiagonalFirst fan =
      Spec.map (CommRingCat.ofHom (diagonalProductFirstCoordinate fan basis rays σ τ).toRingHom) ≫
        fan.affineToricChartι σ := by
  rw [← diagonalProductChartIso_first_assoc]
  simp [diagonalProductChartι,diagonalProductCoverIso,diagonalProductCanonicalIso,
    diagonalAffineProductCover,toricDiagonalFirst,Category.assoc,Fan.affineToricOpenCover_f]
  simp only [Category.assoc, pullback.map, pullback.lift_fst, pullback.lift_fst_assoc,
    Category.id_comp, Category.comp_id]
  erw [pullback.lift_fst_assoc]

/-- The second projection on the product affine chart is the actual
second factor-coordinate ring embedding followed by its chart inclusion. -/
@[reassoc]
theorem diagonalProductChartι_second :
    diagonalProductChartι fan basis rays σ τ ≫ toricDiagonalSecond fan =
      Spec.map (CommRingCat.ofHom (diagonalProductSecondCoordinate fan basis rays σ τ).toRingHom) ≫
        fan.affineToricChartι τ := by
  rw [← diagonalProductChartIso_second_assoc]
  simp [diagonalProductChartι,diagonalProductCoverIso,diagonalProductCanonicalIso,
    diagonalAffineProductCover,toricDiagonalSecond,Category.assoc,Fan.affineToricOpenCover_f]
  simp only [Category.assoc, pullback.map, pullback.lift_snd, pullback.lift_snd_assoc,
    Category.id_comp, Category.comp_id]
  erw [pullback.lift_snd_assoc]

/-- The coordinate chart is an actual morphism over the coefficient
field. This supplies the base-field linearity used when the global
incidence coefficients are pulled back to the chart. -/
instance diagonalProductChartι_isOver :
    (diagonalProductChartι fan basis rays σ τ).IsOver (Spec (.of ℂ)) := by
  rw [Scheme.Hom.isOver_iff]
  change diagonalProductChartι fan basis rays σ τ ≫
      (toricDiagonalFirst fan ≫ fan.algebraicRealizationStructureMap) =
    Spec.map (CommRingCat.ofHom (algebraMap ℂ R))
  rw [← Category.assoc,diagonalProductChartι_first,Category.assoc,
    fan.affineToricChartι_comp_algebraicRealizationStructureMap]
  rw [← Spec.map_comp,← CommRingCat.ofHom_comp]
  congr 2
  exact (diagonalProductFirstCoordinate fan basis rays σ τ).comp_algebraMap

/-- The actual diagonal pulls back to the actual augmentation ring map.
This is the scheme-level identification needed to sheafify the local
cellular exactness calculation. -/
theorem diagonalProductChart_isPullback_overlap :
    IsPullback (fan.affineToricOverlapLeft σ τ ≫ fan.affineToricChartι σ)
      (Spec.map (CommRingCat.ofHom (diagonalChartToIntersection fan basis rays σ τ)))
      (pullback.diagonal fan.algebraicRealizationStructureMap)
      (diagonalProductChartι fan basis rays σ τ) := by
  let h := pullback_map_diagonal_isPullback
    (fan.affineToricChartι σ) (fan.affineToricChartι τ)
    fan.algebraicRealizationStructureMap
  let ei := (fan.affineToricOverlap_isPullback σ τ).isoPullback
  let ec := diagonalProductCanonicalIso fan basis rays σ τ
  apply h.of_iso' ei (Iso.refl _) ec (Iso.refl _)
  · simp only [ei,Iso.refl_hom,Category.comp_id,Category.assoc,
      IsPullback.isoPullback_hom_fst_assoc]
  · apply (cancel_mono
        (pullback.congrHom
          (fan.affineToricChartι_comp_algebraicRealizationStructureMap σ)
          (fan.affineToricChartι_comp_algebraicRealizationStructureMap τ)).hom).mp
    simp only [Category.assoc,ec,diagonalProductCanonicalIso,Iso.trans_hom,
      Iso.symm_hom,Iso.inv_hom_id,Category.comp_id]
    rw [diagonalChartToIntersection_Spec]
    apply pullback.hom_ext <;>
      simp [ei,fan.overlapToChartProduct_fst,fan.overlapToChartProduct_snd]
  · simp
  · rfl

/-- The actual diagonal pulls back to the actual augmentation ring map,
with its source written as the intersection-cone chart. -/
theorem diagonalProductChart_isPullback :
    IsPullback (fan.affineToricChartι (σ ⊓ τ))
      (Spec.map (CommRingCat.ofHom (diagonalChartToIntersection fan basis rays σ τ)))
      (pullback.diagonal fan.algebraicRealizationStructureMap)
      (diagonalProductChartι fan basis rays σ τ) := by
  simpa only [Fan.affineToricOverlapLeft_comp_affineToricChartι] using
    diagonalProductChart_isPullback_overlap fan basis rays σ τ

end ToricPower
