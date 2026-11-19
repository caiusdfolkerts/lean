module

public import ToricPower.DiagonalInternalDual
public import ToricPower.DiagonalExteriorDualLabels
public import ToricPower.AffineFreeDualFrameGenerators
public import ToricPower.InternalDualPullbackFrames

/-!
# Actual inverse-cell generators in the dual diagonal chart

Each inverse exterior label is trivialized by the canonical internal
dual of its original Cartier frame. The original finite-sum inclusion,
the original pullback comparison, and the original affine dual frame
then carry its unit to exactly the same-index free-dual generator.
The comparison is valid in every degree before taking homology.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TauCeti.Toric ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)
  (σ τ : fan.cones)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "R" => DiagonalChartRing ℂ A (fanConeRaySet fan rays σ) (fanConeRaySet fan rays τ)
local notation "U" => Spec (CommRingCat.of R)
local notation "Y" => toricDiagonalProduct fan
local notation "P" => Scheme.Modules.pullback (diagonalProductChartι fan basis rays σ τ)
local notation "L" => diagonalProductSheaf fan nonempty regular basis rays
local notation "M" => diagonalInverseProductSheaf fan nonempty regular basis rays

local instance diagonalInverseFrameYBiproducts : HasFiniteBiproducts (Y).Modules := HasFiniteBiproducts.of_hasFiniteProducts
local instance diagonalInverseFrameUBiproducts : HasFiniteBiproducts (U).Modules := HasFiniteBiproducts.of_hasFiniteProducts
local instance diagonalInverseFrameCellsFintype (q : ℕ) : Fintype (NormalizedCell A q) := Fintype.ofFinite _
local instance diagonalInverseFramePullbackMonoidal : (P).Monoidal := Functor.Monoidal.ofOplaxMonoidal P

local instance diagonalInverseFrameSumHasLeftDual (q : ℕ) :
    HasLeftDual (⨁ (fun c : NormalizedCell A q => L c)) :=
  diagonalGlobalSheafTerm_hasLeftDual fan nonempty regular basis rays q

/-- The inverse exterior inclusion is exactly the internal dual of the
original summand projection, with its original inverse-pairing map. -/
@[reassoc]
theorem diagonalExteriorDualTermIso_inclusion (q : ℕ) (c : NormalizedCell A q) :
    biproduct.ι (fun d : NormalizedCell A q => M d) c ≫
      (diagonalExteriorDualTermIso fan nonempty regular basis rays q).hom =
    (diagonalProductInternalDualIso fan nonempty regular basis rays c).hom ≫
      (internalDual (Y).Modules).map
        (biproduct.π (fun d : NormalizedCell A q => L d) c).op := by
  simp only [diagonalExteriorDualTermIso, Iso.trans_hom, Iso.symm_hom,
    biproduct.mapIso_hom, biproduct.ι_map_assoc, internalDualBiproductIso_ι_inv]

/-- The specified inverse-cell affine frame is obtained by dualizing
the specified original Cartier frame, through actual pullback. -/
def diagonalInverseCellPullbackFrame (q : ℕ) (c : NormalizedCell A q) :
    SheafOfModules.unit (U).ringCatSheaf ≅ (P).obj (M c) :=
  (inverseCellPullbackFrame P
    (fun d : NormalizedCell A q => L d) (fun d : NormalizedCell A q => M d)
    (fun d => diagonalProductInternalDualIso fan nonempty regular basis rays d)
    (fun d => diagonalProductCartierFrame fan nonempty regular basis rays σ τ d) c).symm

/-- The actual total unit frame is the same free-module frame used in
the original global diagonal comparison. -/
def diagonalTotalUnitFrame (q : ℕ) :
    (⨁ (fun _ : NormalizedCell A q => SheafOfModules.unit (U).ringCatSheaf)) ≅
      (P).obj (diagonalGlobalSheafTerm fan nonempty regular basis rays q) :=
  (tildeFiniteFreeBiproductIso (CommRingCat.of R) (NormalizedCell A q)).symm ≪≫
    diagonalGlobalTermChartIso fan nonempty regular basis rays σ τ q

/-- The original chart isomorphism and the canonical dual unit frame
are the same actual map. -/
theorem diagonalGlobalInternalDualChartIso_unitFrame (q : ℕ) :
    (diagonalGlobalInternalDualChartIso fan nonempty regular basis rays σ τ).hom.f q ≫
        (affineInternalDualCoordinates (CommRingCat.of R) (NormalizedCell A q)).hom =
      (totalInternalDualPullbackFrame P (fun d : NormalizedCell A q => L d)
        (diagonalTotalUnitFrame fan nonempty regular basis rays σ τ q)).hom := by
  letI := diagonalGlobalSheafTerm_hasLeftDual fan nonempty regular basis rays q
  change (internalDualComparison P).app
      (op (diagonalGlobalSheafTerm fan nonempty regular basis rays q)) ≫
      (internalDual (U).Modules).map
        (diagonalGlobalTermChartIso fan nonempty regular basis rays σ τ q).hom.op ≫
        (affineInternalDualCoordinates (CommRingCat.of R) (NormalizedCell A q)).hom = _
  simp only [totalInternalDualPullbackFrame, diagonalTotalUnitFrame,
    affineInternalDualCoordinates, internalDualInUnitFrames, Iso.trans_hom,
    asIso_hom, Functor.mapIso_hom, Iso.op_hom, Iso.symm_hom,
    op_comp, Functor.map_comp, Category.assoc]
  rfl

/-- Every genuine inverse-cell generator becomes the same-index
original dual basis vector in the complete affine complex. -/
theorem diagonalInverseCellPullbackFrame_generator (q : ℕ) (c : NormalizedCell A q) :
    (diagonalInverseCellPullbackFrame fan nonempty regular basis rays σ τ q c).hom ≫
      (P).map (biproduct.ι (fun d : NormalizedCell A q => M d) c ≫
        (diagonalExteriorDualTermIso fan nonempty regular basis rays q).hom) ≫
      (diagonalGlobalInternalDualChartIso fan nonempty regular basis rays σ τ).hom.f q ≫
        (affineInternalDualCoordinates (CommRingCat.of R) (NormalizedCell A q)).hom =
      biproduct.ι (fun _ : NormalizedCell A q => SheafOfModules.unit (U).ringCatSheaf) c := by
  letI := diagonalGlobalSheafTerm_hasLeftDual fan nonempty regular basis rays q
  rw [diagonalGlobalInternalDualChartIso_unitFrame,
    diagonalExteriorDualTermIso_inclusion]
  apply inverseCellPullbackFrame_generator P
    (fun d : NormalizedCell A q => L d) (fun d : NormalizedCell A q => M d)
    (fun d => diagonalProductInternalDualIso fan nonempty regular basis rays d)
    (fun d => diagonalProductCartierFrame fan nonempty regular basis rays σ τ d)
    (diagonalTotalUnitFrame fan nonempty regular basis rays σ τ q) c
  intro d
  unfold diagonalTotalUnitFrame diagonalGlobalTermChartIso
  rw [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    affineFreeFrameComparison_projection, Iso.inv_hom_id_assoc]
  rfl

end ToricPower

end
