module

public import PaperVerification.ToricAffineDifferentialWedges
public import PaperVerification.ToricOpenModuleFrames
public import PaperVerification.ToricDifferentialOverlaps
public import PaperVerification.ToricRationalFrameComparison

@[expose] public section

/-!
# The intrinsic canonical sheaf of the actual fan scheme

The left-hand side below is the ordinary top exterior power of the
intrinsic Kähler sheaf. Its actual polynomial-chart frames map to the
previously computed genuine generic differential volumes. This proves
the global sheaf comparison, and only then identifies the canonical
Cartier coefficients with minus one on every ray.
-/

noncomputable section

universe u

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace KaehlerDifferential
open PaperVerification.ToricCharacters PaperVerification.ToricSchemes
open scoped Classical BaseSections

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

variable {n : ℕ} («Σ» : SmoothCompleteFan n) (k : Type u) [Field k]

attribute [local instance] fanFunctionFieldAlgebra torusFunctionFieldAlgebra
  chartFunctionFieldAlgebra torusFunctionField_isFractionRing

local notation "X" => «Σ».fanScheme k
local notation "M" => topDifferentialSheaf k X n

def fullChartIntrinsicTopFrame (s : «Σ».fullCones) :
    topDifferentialSheaf k (coneChart k s.val) n≅
      SheafOfModules.unit (coneChart k s.val).ringCatSheaf :=
  affineTopDifferentialSheafIso k (monoidChartAlgebra k (dualConeMonoid s.val))
      («Σ».actualFullChartDifferentialBasis k s) ≪≫
    «Σ».fullChartTopDifferentialFrame k s

def intrinsicTopChartFrame (s : «Σ».fullCones) :
    (M).restrict («Σ».fanChartMap k («Σ».fullConeIndex s))≅
      SheafOfModules.unit (coneChart k s.val).ringCatSheaf :=
  topDifferentialSheafRestrictIso («Σ».fanChartMap k («Σ».fullConeIndex s)) n k ≪≫
    «Σ».fullChartIntrinsicTopFrame k s

/-- Actual local freeness on the actual image open. -/
def intrinsicTopOpenFrame (s : «Σ».fullCones) : ModuleFrame M («Σ».fullChartOpen k s) :=
  ModuleFrame.ofOpenImmersionIso («Σ».fanChartMap k («Σ».fullConeIndex s))
    («Σ».intrinsicTopChartFrame k s)

set_option maxHeartbeats 2000000 in
theorem fullChartIntrinsicTopFrame_wedge (s : «Σ».fullCones) :
    («Σ».fullChartIntrinsicTopFrame k s).hom.app ⊤
      (differentialWedgeSection (coneChart k s.val) k ⊤
        (fun i=>(Scheme.ΓSpecIso (CommRingCat.of
          (monoidChartAlgebra k (dualConeMonoid s.val)))).inv
            («Σ».fullChartCoordinate k s i)))=(1 : Γ(coneChart k s.val,⊤)) := by
  let R := CommRingCat.of (monoidChartAlgebra k (dualConeMonoid s.val))
  let b := «Σ».actualFullChartDifferentialBasis k s
  have hw := affineTopDifferentialSheafIso_differentialWedge_top k R b
    («Σ».fullChartCoordinate k s)
  have hb : (fun i : Fin n => D k R («Σ».fullChartCoordinate k s i))=b := by
    funext i
    exact («Σ».actualFullChartDifferentialBasis_apply k s i).symm
  have hw' := hw.trans (congrArg
    (fun v : Fin n → KaehlerDifferential k R =>
      tilde.toOpen (R := R) (ModuleCat.of R (⋀[R]^n (KaehlerDifferential k R))) ⊤
        (exteriorPower.ιMulti R n v)) hb)
  have hc : tildeTopBasisCoordinates R (ModuleCat.of R (KaehlerDifferential k R)) b ⊤
      (tilde.toOpen (ModuleCat.of R (⋀[R]^n (KaehlerDifferential k R))) ⊤
        (exteriorPower.ιMulti R n b))=(1 : Γ(Spec R,⊤)) :=
    (tildeTopBasisCoordinates_toOpen R (ModuleCat.of R (KaehlerDifferential k R)) b ⊤
      (exteriorPower.ιMulti R n b)).trans (by
        rw [basisTopExteriorEquiv_basis,map_one])
  exact (congrArg ((«Σ».fullChartTopDifferentialFrame k s).hom.app ⊤) hw').trans hc

/-- The chart coordinate, now as an actual regular function on the
actual image open of the chart. -/
def fullChartGlobalCoordinate (s : «Σ».fullCones) (i : Fin n) :
    Γ(X,«Σ».fullChartOpen k s) :=
  let j := «Σ».fanChartMap k («Σ».fullConeIndex s)
  (X).presheaf.map (eqToHom (j.image_top_eq_opensRange).symm).op
    ((j.appIso ⊤).inv ((Scheme.ΓSpecIso (CommRingCat.of
      (monoidChartAlgebra k (dualConeMonoid s.val)))).inv
        («Σ».fullChartCoordinate k s i)))

theorem intrinsicTopChartFrame_inv_one (s : «Σ».fullCones) :
    («Σ».intrinsicTopChartFrame k s).inv.app ⊤ (1 : Γ(coneChart k s.val,⊤)) =
      ((M).restrictAppIso («Σ».fanChartMap k («Σ».fullConeIndex s)) ⊤).inv
        (differentialWedgeSection X k
          ((«Σ».fanChartMap k («Σ».fullConeIndex s)) ''ᵁ ⊤)
          (fun i=>((«Σ».fanChartMap k («Σ».fullConeIndex s)).appIso ⊤).inv
            ((Scheme.ΓSpecIso (CommRingCat.of
              (monoidChartAlgebra k (dualConeMonoid s.val)))).inv
                («Σ».fullChartCoordinate k s i)))) := by
  letI : IsIso ((«Σ».intrinsicTopChartFrame k s).hom.app ⊤) :=
    Scheme.Modules.Hom.isIso_iff_isIso_app.mp
      (inferInstance : IsIso («Σ».intrinsicTopChartFrame k s).hom) ⊤
  apply (ConcreteCategory.bijective_of_isIso
    ((«Σ».intrinsicTopChartFrame k s).hom.app ⊤)).injective
  have hc := congrArg (fun f=>f.app ⊤ (1 : Γ(coneChart k s.val,⊤)))
    («Σ».intrinsicTopChartFrame k s).inv_hom_id
  rw [show («Σ».intrinsicTopChartFrame k s).hom.app ⊤
      ((«Σ».intrinsicTopChartFrame k s).inv.app ⊤ (1 : Γ(coneChart k s.val,⊤)))=(1 : Γ(coneChart k s.val,⊤)) from by
        simpa only [Scheme.Modules.Hom.comp_app,Scheme.Modules.Hom.id_app,
          ConcreteCategory.comp_apply,ConcreteCategory.id_apply] using hc]
  simp only [intrinsicTopChartFrame,Iso.trans_hom,Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply,differentialWedgeSection_openRestriction,
    Iso.inv_hom_id_apply]
  exact («Σ».fullChartIntrinsicTopFrame_wedge k s).symm

/-- The local basis of the intrinsic top sheaf is the actual wedge of
the actual affine coordinate differentials. -/
theorem intrinsicTopOpenFrame_generator (s : «Σ».fullCones) :
    («Σ».intrinsicTopOpenFrame k s).generator («Σ».fullChartOpen k s) le_rfl=
      differentialWedgeSection X k («Σ».fullChartOpen k s)
        («Σ».fullChartGlobalCoordinate k s) := by
  let j := «Σ».fanChartMap k («Σ».fullConeIndex s)
  let e : (M).restrict j ≅
      SheafOfModules.unit (coneChart k («Σ».fullConeIndex s).val).ringCatSheaf :=
    «Σ».intrinsicTopChartFrame k s
  let a : Fin n → Γ(X,j ''ᵁ (⊤ : (coneChart k («Σ».fullConeIndex s).val).Opens)) :=
    fun i => (j.appIso ⊤).inv
      ((Scheme.ΓSpecIso (CommRingCat.of
        (monoidChartAlgebra k (dualConeMonoid s.val)))).inv
          («Σ».fullChartCoordinate k s i))
  let ω := differentialWedgeSection X k (j ''ᵁ ⊤) a
  have he : e.inv.app ⊤
      (1 : Γ(coneChart k («Σ».fullConeIndex s).val,⊤)) =
      ((M).restrictAppIso j ⊤).inv ω :=
    «Σ».intrinsicTopChartFrame_inv_one k s
  have hv : ((M).restrictAppIso j ⊤).hom
      (e.inv.app ⊤ (1 : Γ(coneChart k («Σ».fullConeIndex s).val,⊤))) = ω :=
    (congrArg ((M).restrictAppIso j ⊤).hom he).trans
      (((M).restrictAppIso j ⊤).inv_hom_id_apply ω)
  have himage : ModuleFrame.imageFrameGenerator j e =
      (M).presheaf.map (eqToHom j.image_top_eq_opensRange.symm).op ω :=
    congrArg (fun v : Γ(M,j ''ᵁ (⊤ : (coneChart k («Σ».fullConeIndex s).val).Opens)) =>
      (M).presheaf.map (eqToHom j.image_top_eq_opensRange.symm).op v) hv
  have hres : (M).presheaf.map (eqToHom j.image_top_eq_opensRange.symm).op ω =
      differentialWedgeSection X k j.opensRange
        (fun i => (X).presheaf.map (eqToHom j.image_top_eq_opensRange.symm).op (a i)) :=
    differentialWedgeSection_restrict X k j.image_top_eq_opensRange.symm.le a
  exact (ModuleFrame.ofOpenImmersionIso_generator j e).trans (himage.trans hres)

theorem fullChartGlobalCoordinate_germ (s : «Σ».fullCones)
    [Nonempty («Σ».fullChartOpen k s)] (i : Fin n) :
    (X).germToFunctionField («Σ».fullChartOpen k s) («Σ».fullChartGlobalCoordinate k s i)=
      «Σ».chartRationalMap k («Σ».fullConeIndex s) («Σ».fullChartCoordinate k s i) := by
  let R := CommRingCat.of
    (monoidChartAlgebra k (dualConeMonoid («Σ».fullConeIndex s).val))
  let j : coneChart k («Σ».fullConeIndex s).val ⟶ X :=
    «Σ».fanChartMap k («Σ».fullConeIndex s)
  letI : IsIntegral (coneChart k («Σ».fullConeIndex s).val) :=
    «Σ».coneChart_isIntegral k («Σ».fullConeIndex s)
  letI : IsOpenImmersion j :=
    «Σ».fanChartMap_isOpenImmersion k («Σ».fullConeIndex s)
  let a : Γ(coneChart k («Σ».fullConeIndex s).val,⊤) :=
    (Scheme.ΓSpecIso R).inv («Σ».fullChartCoordinate k s i)
  let U : (X).Opens := j ''ᵁ (⊤ : (coneChart k («Σ».fullConeIndex s).val).Opens)
  letI : Nonempty U := by
    rw [show U=«Σ».fullChartOpen k s from j.image_top_eq_opensRange]
    infer_instance
  let b : Γ(X,U) := (j.appIso ⊤).inv a
  let f : «Σ».fullChartOpen k s ⟶ U :=
    eqToHom (j.image_top_eq_opensRange).symm
  change (X).germToFunctionField («Σ».fullChartOpen k s)
    ((X).presheaf.map f.op b) = _
  calc
    _ = (X).germToFunctionField U b :=
      germToFunctionField_restrict X f b
    _ = openImmersionRegularToFunctionField j ⊤ a :=
      (openImmersionRegularToFunctionField_eq_germ_image j ⊤ a).symm
    _ = _ := rfl


/-- The generic coefficient of the intrinsic local basis is exactly
the coefficient already obtained from actual chart Kähler modules. -/
theorem intrinsicTopOpenFrame_value
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) (s : «Σ».fullCones)
    [Nonempty («Σ».fullChartOpen k s)] :
    rationalValue X («Σ».fullChartOpen k s)
      ((topDifferentialRationalMap X k («Σ».genericLogDifferentialBasis k b₀)).app
        («Σ».fullChartOpen k s)
          ((«Σ».intrinsicTopOpenFrame k s).generator («Σ».fullChartOpen k s) le_rfl))=
      («Σ».differentialVolumeUnit k b₀ s : (X).functionField) := by
  rw [«Σ».intrinsicTopOpenFrame_generator,
    topDifferentialRationalMap_differentialWedge]
  simp_rw [«Σ».fullChartGlobalCoordinate_germ]
  change _=«Σ».actualChartTopCoefficient k b₀ s
    (exteriorPower.ιMulti (monoidChartAlgebra k (dualConeMonoid s.val)) n
      («Σ».actualFullChartDifferentialBasis k s))
  unfold actualChartTopCoefficient
  rw [LinearMap.comp_apply,exteriorScalarExtensionMap_wedge]
  change basisTopExteriorEquiv («Σ».genericLogDifferentialBasis k b₀) _ =
    basisTopExteriorEquiv («Σ».genericLogDifferentialBasis k b₀) _
  apply congrArg (fun ω :
    ⋀[(«Σ».fanScheme k).functionField]^n
      (KaehlerDifferential k («Σ».fanScheme k).functionField) =>
        basisTopExteriorEquiv («Σ».genericLogDifferentialBasis k b₀) ω)
  apply congrArg (fun v : Fin n → KaehlerDifferential k («Σ».fanScheme k).functionField =>
    exteriorPower.ιMulti («Σ».fanScheme k).functionField n v)
  funext i
  rw [«Σ».actualFullChartDifferentialBasis_apply,KaehlerDifferential.map_D]
  exact congrArg (D k («Σ».fanScheme k).functionField)
    («Σ».chartRationalMap_eq_torusRationalMap k («Σ».fullConeIndex s)
      («Σ».fullChartCoordinate k s i))

theorem intrinsicTopFrameValues (hpure : «Σ».IsPure)
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) :
    («Σ».differentialVolumeCocycle k hpure b₀).FrameValues M
      (topDifferentialRationalMap X k («Σ».genericLogDifferentialBasis k b₀))
      (fun s=>«Σ».intrinsicTopOpenFrame k s.down) := by
  intro s h
  letI : Nonempty («Σ».fullChartOpen k s.down) := h
  exact «Σ».intrinsicTopOpenFrame_value k b₀ s.down

/-- The genuine intrinsic canonical sheaf is the fractional sheaf
obtained from its genuine generic differential volume. -/
def intrinsicTopDifferentialVolumeIso (hpure : «Σ».IsPure)
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) :
    topDifferentialSheaf k («Σ».fanScheme k) n≅
      («Σ».differentialVolumeData k hpure b₀).sheaf :=
  («Σ».differentialVolumeCocycle k hpure b₀).sheafIsoOfFrames M
    (topDifferentialRationalMap X k («Σ».genericLogDifferentialBasis k b₀))
    (fun s=>«Σ».intrinsicTopOpenFrame k s.down)
    («Σ».intrinsicTopFrameValues k hpure b₀)

/-- The minus-one ray coefficients are a consequence of the actual
Kähler/top-exterior computation, not the definition of the canonical sheaf. -/
def intrinsicCanonicalFanIso (hpure : «Σ».IsPure)
    (b₀ : Module.Basis (Fin n) ℤ (Lattice n)) :
    topDifferentialSheaf k («Σ».fanScheme k) n≅
      («Σ».fanCartierData k hpure (fun _=>-1)).sheaf :=
  «Σ».intrinsicTopDifferentialVolumeIso k hpure b₀ ≪≫
    («Σ».differentialVolumeData_equivalent_canonical k hpure b₀).choose

theorem intrinsicTopDifferential_isInvertible (hpure : «Σ».IsPure) :
    IsInvertibleModule (topDifferentialSheaf k («Σ».fanScheme k) n) := by
  intro x
  obtain ⟨s,hs⟩ := «Σ».fullChartOpen_cover k hpure x
  exact ⟨«Σ».fullChartOpen k s,hs,⟨«Σ».intrinsicTopOpenFrame k s⟩⟩

end PaperVerification.ToricGeometry.SmoothCompleteFan

#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.intrinsicTopDifferentialVolumeIso
#print axioms PaperVerification.ToricGeometry.SmoothCompleteFan.intrinsicCanonicalFanIso
