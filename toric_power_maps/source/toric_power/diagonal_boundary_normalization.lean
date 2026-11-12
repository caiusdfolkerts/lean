module

public import ToricPower.DiagonalInverseCellTopChart
public import ToricPower.DiagonalTopCellUnitCoefficient
public import ToricPower.AffineClosedImmersionGenerator

/-!
# The actual diagonal top line is the literal boundary Cartier line

Every original top-cell map becomes invertible on the diagonal: its
actual affine coefficient is a unit in the overlap ring. This proves
invertibility of the specified global map from the boundary Cartier
line to the actual diagonal top homology line. The resulting augmented
dual diagonal retains its original differential and its original map.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open TauCeti.Toric ToricPower.IntegralArrangement
open scoped Classical

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "δ" => toricDiagonal fan
local notation "J" => dualDiagonalLineSheaf fan nonempty regular basis rays

local instance boundaryNormalizationTopCellsFintype : Fintype (NormalizedCell A n) := Fintype.ofFinite _

/-- Scalar extension of the original chart generator is an
isomorphism, because its original quotient coefficient is a unit. -/
theorem diagonalTopGeneratorPullback_isIso (σ : fan.cones) (c : NormalizedCell A n) :
    IsIso ((Scheme.Modules.pullback
      (Spec.map (CommRingCat.ofHom (diagonalChartToIntersection fan basis rays σ σ)))).map
        (tilde.map (toricDiagonalTopGeneratorMap fan regular basis rays σ σ c))) := by
  apply affineClosedImmersion_generator_isIso _
    (diagonalChartToIntersection_surjective fan basis rays σ σ)
  change @IsUnit (affineCoordinateRing fan.lattice (σ.val ⊓ σ.val)) _
    ((toricDualDiagonalBoundaryFrameIso fan regular basis rays σ σ).hom
      ((diagonalFramedDualTopQuotient ℂ A
        (fanConeRaySet fan rays σ) (fanConeRaySet fan rays σ)
        (toricDiagonalCellFrames fan regular basis rays σ σ))
        ((diagonalFramedDualCoordinates ℂ A
          (fanConeRaySet fan rays σ) (fanConeRaySet fan rays σ)
          (toricDiagonalCellFrames fan regular basis rays σ σ) n).symm
            (Finsupp.single c 1))))
  exact toricDiagonalTopCellQuotient_isUnit fan basis rays regular σ c

/-- The actual inverse-cell map becomes an isomorphism after ordinary
pullback to the diagonal. No exactness of that pullback is asserted. -/
theorem diagonalInverseCellPulledTopQuotient_isIso (c : NormalizedCell A n) :
    IsIso ((Scheme.Modules.pullback δ).map
      (diagonalInverseCellTopQuotient fan nonempty regular basis rays c)) := by
  apply (Scheme.Modules.isIso_iff_pullback_openCover fan.affineToricOpenCover _).mpr
  change ∀ σ : fan.cones,
    IsIso ((Scheme.Modules.pullback (fan.affineToricChartι σ)).map
      ((Scheme.Modules.pullback δ).map
        (diagonalInverseCellTopQuotient fan nonempty regular basis rays c)))
  intro σ
  let φ := diagonalChartToIntersection fan basis rays σ σ
  let g := Spec.map (CommRingCat.ofHom φ)
  let F := Scheme.Modules.pullback g
  let P := Scheme.Modules.pullback (diagonalProductChartι fan basis rays σ σ)
  let f := diagonalInverseCellTopQuotient fan nonempty regular basis rays c
  let e := diagonalInverseCellPullbackFrame fan nonempty regular basis rays σ σ n c
  let h := dualDiagonalTopChartFrame fan nonempty regular basis rays σ σ
  haveI := diagonalTopGeneratorPullback_isIso fan regular basis rays σ c
  haveI : IsIso (F.map (e.hom ≫ P.map f ≫ h.hom)) := by
    rw [diagonalInverseCellTopChartFrame]
    rw [F.map_comp]
    infer_instance
  haveI : IsIso (F.map e.hom ≫ F.map (P.map f) ≫ F.map h.hom) := by
    simpa only [F.map_comp, Category.assoc] using
      (inferInstance : IsIso (F.map (e.hom ≫ P.map f ≫ h.hom)))
  haveI : IsIso (F.map (P.map f) ≫ F.map h.hom) :=
    IsIso.of_isIso_comp_left (F.map e.hom) _
  haveI : IsIso (F.map (P.map f)) := IsIso.of_isIso_comp_right _ (F.map h.hom)
  have localIso : IsIso ((Scheme.Modules.pullback (fan.affineToricChartι (σ ⊓ σ))).map
      ((Scheme.Modules.pullback δ).map f)) :=
    (NatIso.isIso_map_iff
      (pullbackSquareIso δ g (fan.affineToricChartι (σ ⊓ σ))
        (diagonalProductChartι fan basis rays σ σ)
        (diagonalProductChart_isPullback fan basis rays σ σ).w) f).mp (by
          change IsIso (F.map (P.map f))
          infer_instance)
  change IsIso ((Scheme.Modules.pullback (fan.affineToricChartι σ)).map
    ((Scheme.Modules.pullback δ).map f))
  exact Eq.mp (congrArg (fun κ : fan.cones =>
    IsIso ((Scheme.Modules.pullback (fan.affineToricChartι κ)).map
      ((Scheme.Modules.pullback δ).map f))) (inf_idem σ)) localIso

/-- The specified boundary-labelled morphism is itself invertible. -/
theorem diagonalBoundaryToTopLine_isIso (c : NormalizedCell A n) :
    IsIso (diagonalBoundaryToTopLine fan nonempty regular basis rays c) := by
  letI := diagonalInverseCellPulledTopQuotient_isIso fan nonempty regular basis rays c
  unfold diagonalBoundaryToTopLine
  infer_instance

/-- One actual top cell fixes a global normalization of the actual top
line by the boundary Cartier line. -/
def dualDiagonalBoundaryLineIso : diagonalBoundaryLine fan nonempty regular ≅ J := by
  let c := Classical.choice (exists_normalizedTopCell A)
  letI := diagonalBoundaryToTopLine_isIso fan nonempty regular basis rays c
  exact asIso (diagonalBoundaryToTopLine fan nonempty regular basis rays c)

/-- The actual global dual diagonal resolves the actual diagonal
pushforward of the literal boundary Cartier line, in degree `n`. -/
def dualDiagonalBoundaryAugmentation :
    diagonalGlobalInternalDualComplex fan nonempty regular basis rays ⟶
      (HomologicalComplex.single (toricDiagonalProduct fan).Modules (.up ℕ) n).obj
        ((Scheme.Modules.pushforward δ).obj (diagonalBoundaryLine fan nonempty regular)) :=
  dualDiagonalLineAugmentation fan nonempty regular basis rays ≫
    (HomologicalComplex.single (toricDiagonalProduct fan).Modules (.up ℕ) n).map
      ((Scheme.Modules.pushforward δ).map
        (dualDiagonalBoundaryLineIso fan nonempty regular basis rays).inv)

theorem dualDiagonalBoundaryAugmentation_quasiIso :
    QuasiIso (dualDiagonalBoundaryAugmentation fan nonempty regular basis rays) := by
  letI := dualDiagonalLineAugmentation_quasiIso fan nonempty regular basis rays
  unfold dualDiagonalBoundaryAugmentation
  infer_instance

end ToricPower

end
