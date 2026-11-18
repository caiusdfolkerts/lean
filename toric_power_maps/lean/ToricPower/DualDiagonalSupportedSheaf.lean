module

public import ToricPower.DiagonalInternalDualHomology
public import ToricPower.DiagonalTargetRestriction
public import ToricPower.AffineClosedImmersionUnit
public import ToricPower.OpenBaseChangeUnit
public import ToricPower.InvertibleChartFrames

/-!
# The actual dual diagonal homology is an invertible diagonal sheaf

Let `H` be the actual top homology sheaf of the global internal-dual
diagonal complex, and let `J` be its actual pullback to the diagonal.
On every genuine product chart the independently computed boundary
module is a scalar restriction of the coordinate ring of the overlap.
The canonical adjunction unit `H → δ_* J` is therefore an isomorphism.
The same local computation and the canonical quotient-ring counit give
rank-one frames for `J` on the ordinary toric affine cover.

No overlap transition scalar, global boundary identification, or
reconstruction equivalence is assumed here.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric
open ToricPower.IntegralArrangement
open scoped Classical

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {latticeMap : N →+ V}
  (fan : Fan latticeMap) (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "Y" => toricDiagonalProduct fan
local notation "δ" => toricDiagonal fan
local notation "K" => diagonalGlobalInternalDualComplex fan nonempty regular basis rays

/-- The actual global top homology, before choosing any geometric model. -/
def dualDiagonalTopSheaf : (Y).Modules := (K).homology n

/-- The actual pullback of top homology to the diagonal. -/
def dualDiagonalLineSheaf : fan.algebraicRealization.Modules :=
  (Scheme.Modules.pullback δ).obj (dualDiagonalTopSheaf fan nonempty regular basis rays)

variable (σ τ : fan.cones)

local notation "chart" => diagonalProductChartι fan basis rays σ τ
local notation "overlap" => fan.affineToricChartι (σ ⊓ τ)
local notation "φ" => diagonalChartToIntersection fan basis rays σ τ
local notation "g" => Spec.map (CommRingCat.ofHom φ)
local notation "H" => dualDiagonalTopSheaf fan nonempty regular basis rays
local notation "J" => dualDiagonalLineSheaf fan nonempty regular basis rays

/-- Surjectivity follows from the genuine overlap tensor map, under the
explicit coordinate-ring isomorphism already used for the product chart. -/
theorem diagonalChartToIntersection_surjective : Function.Surjective φ := by
  rw [← diagonalProductCoordinateEquiv_comp_overlap]
  exact (fan.overlapTensorMap_surjective σ τ).comp
    (diagonalProductCoordinateEquiv fan basis rays σ τ).surjective

/-- The actual top homology in a genuine product chart has a rank-one
module frame over the quotient coordinate ring of the overlap. -/
def dualDiagonalTopChartFrame :
    (Scheme.Modules.pullback chart).obj H ≅
      tilde (diagonalIntersectionModule fan basis rays σ τ) :=
  diagonalGlobalInternalDualTopChartIso fan nonempty regular basis rays σ τ ≪≫
    (tilde.functor _).mapIso (toricDualDiagonalBoundaryFrameIso fan regular basis rays σ τ)

/-- The actual local unit on top homology is invertible. -/
theorem dualDiagonalTopChartUnit_isIso :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
      ((Scheme.Modules.pullback chart).obj H)) := by
  rw [NatTrans.isIso_app_iff_of_iso
    (Scheme.Modules.pullbackPushforwardAdjunction g).unit
    (dualDiagonalTopChartFrame fan nonempty regular basis rays σ τ)]
  exact affineClosedImmersionUnit_onTilde_isIso
    (CommRingCat.ofHom φ) (diagonalChartToIntersection_surjective fan basis rays σ τ) _

/-- The canonical global unit realizes the actual top homology sheaf as
the diagonal pushforward of its own pullback. -/
theorem dualDiagonalTopUnit_isIso :
    IsIso ((Scheme.Modules.pullbackPushforwardAdjunction δ).unit.app H) := by
  apply (Scheme.Modules.isIso_iff_pullback_openCover
    (diagonalCoordinateOpenCover fan basis rays) _).mpr
  rintro ⟨σ, τ⟩
  letI := dualDiagonalTopChartUnit_isIso fan nonempty regular basis rays σ τ
  exact pullbackUnit_isIso_of_openBaseChange δ
    (Spec.map (CommRingCat.ofHom (diagonalChartToIntersection fan basis rays σ τ)))
    (fan.affineToricChartι (σ ⊓ τ)) (diagonalProductChartι fan basis rays σ τ)
    (diagonalProductChart_isPullback fan basis rays σ τ).w
    (diagonalChart_preimage_opensRange fan basis rays σ τ).le H

/-- This isomorphism's forward map is precisely the original adjunction unit. -/
def dualDiagonalTopPushforwardIso :
    H ≅ (Scheme.Modules.pushforward δ).obj J := by
  letI := dualDiagonalTopUnit_isIso fan nonempty regular basis rays
  exact asIso ((Scheme.Modules.pullbackPushforwardAdjunction δ).unit.app H)

/-- Pulling back the quotient-ring frame and using the original counit
trivializes the actual diagonal pullback on every overlap chart. -/
def dualDiagonalLineOverlapFrame :
    (J).restrict overlap ≅
      SheafOfModules.unit (fan.affineToricChart (σ ⊓ τ)).ringCatSheaf := by
  let U := fan.affineToricChart (σ ⊓ τ)
  let unitObject : QCoh U := ⟨SheafOfModules.unit U.ringCatSheaf, inferInstance⟩
  letI := affineClosedImmersionCounit_isIso
    (CommRingCat.ofHom φ) (diagonalChartToIntersection_surjective fan basis rays σ τ)
    unitObject
  exact (Scheme.Modules.restrictFunctorIsoPullback overlap).app J ≪≫
    ((pullbackSquareIso δ g overlap chart
      (diagonalProductChart_isPullback fan basis rays σ τ).w).app H).symm ≪≫
    (Scheme.Modules.pullback g).mapIso
      (dualDiagonalTopChartFrame fan nonempty regular basis rays σ τ ≪≫
        toricDiagonalChartTargetIso fan basis rays σ τ) ≪≫
    asIso ((Scheme.Modules.pullbackPushforwardAdjunction g).counit.app
      (SheafOfModules.unit U.ringCatSheaf))

/-- The pullback of the top homology is an actual invertible sheaf, on
every smooth finite toric fan, with no completeness hypothesis. -/
theorem dualDiagonalLineSheaf_isInvertible :
    TauCeti.AlgebraicGeometry.SheafOfModules.isInvertible
      fan.algebraicRealization J := by
  apply isInvertible_of_openCover_frames fan.affineToricOpenCover J
  change ∀ σ : fan.cones,
    SheafOfModules.unit (fan.affineToricChart σ).ringCatSheaf ≅
      (J).restrict (fan.affineToricChartι σ)
  intro σ
  have frame := (dualDiagonalLineOverlapFrame fan nonempty regular basis rays σ σ).symm
  exact Eq.mp (congrArg (fun κ : fan.cones =>
    SheafOfModules.unit (fan.affineToricChart κ).ringCatSheaf ≅
      (J).restrict (fan.affineToricChartι κ)) (inf_idem σ)) frame

/-- The original internal-dual complex has a genuine augmentation to
the diagonal pushforward of its invertible top line, in ambient degree. -/
def dualDiagonalLineAugmentation :
    K ⟶ (HomologicalComplex.single (Y).Modules (.up ℕ) n).obj
      ((Scheme.Modules.pushforward δ).obj J) :=
  diagonalGlobalInternalDualTopAugmentation fan nonempty regular basis rays ≫
    (HomologicalComplex.single (Y).Modules (.up ℕ) n).map
      (dualDiagonalTopPushforwardIso fan nonempty regular basis rays).hom

theorem dualDiagonalLineAugmentation_quasiIso :
    QuasiIso (dualDiagonalLineAugmentation fan nonempty regular basis rays) := by
  letI := diagonalGlobalInternalDualTopAugmentation_quasiIso
    fan nonempty regular basis rays
  unfold dualDiagonalLineAugmentation
  infer_instance

end ToricPower
