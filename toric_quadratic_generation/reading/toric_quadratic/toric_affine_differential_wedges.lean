module

public import PaperVerification.ToricAffineExteriorSheaf
public import PaperVerification.ToricGenericTopDifferentials

@[expose] public section

/-! # The affine comparison preserves actual wedges of differentials -/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite
open scoped BaseSections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

variable {X : Scheme.{u}} {M N : X.Modules} (e : M≅N) (n : ℕ)

theorem sheafExteriorPowerIso_wedge (U : X.Opens) (ω : Fin n→Γ(M,U)) :
    (sheafExteriorPowerIso X e n).hom.app U
      (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        (presheafExteriorPower X.presheaf M.val n)).app (op U)
          (exteriorPower.ιMulti Γ(X,U) n ω)) =
      ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
        (presheafExteriorPower X.presheaf N.val n)).app (op U)
          (exteriorPower.ιMulti Γ(X,U) n (fun i=>e.hom.app U (ω i))) := by
  have h := congrArg
    (fun f=>f.app (op U) (exteriorPower.ιMulti Γ(X,U) n ω))
    ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.naturality
      (presheafExteriorPowerHom X.presheaf n e.hom.val))
  change
    ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      (presheafExteriorPower X.presheaf N.val n)).app (op U)
        (ModuleCat.exteriorPower.map (R := Γ(X,U)) (e.hom.val.app (op U)) n
          (exteriorPower.ιMulti Γ(X,U) n ω)) =
      (sheafExteriorPowerIso X e n).hom.app U
        (((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
          (presheafExteriorPower X.presheaf M.val n)).app (op U)
            (exteriorPower.ιMulti Γ(X,U) n ω)) at h
  have hmap :
      ModuleCat.exteriorPower.map (R := Γ(X,U)) (e.hom.val.app (op U)) n
        (exteriorPower.ιMulti Γ(X,U) n ω) =
      exteriorPower.ιMulti Γ(X,U) n (fun i=>e.hom.app U (ω i)) :=
    ModuleCat.exteriorPower.map_mk (R := Γ(X,U)) (e.hom.val.app (op U)) ω
  exact h.symm.trans (congrArg
    (fun x=>((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      (presheafExteriorPower X.presheaf N.val n)).app (op U) x) hmap)

variable (k R : Type u) [CommRing k] [CommRing R] [Algebra k R] {n : ℕ}
    (b : Module.Basis (Fin n) R (KaehlerDifferential k R))

local instance affineWedgeCoordinateAlgebra (U : (Spec (CommRingCat.of R)).Opens) :
    Algebra R Γ(Spec (CommRingCat.of R),U) :=
  inferInstanceAs (Algebra R
    ((Spec.structureSheaf (CommRingCat.of R)).presheaf.obj (op U)))

theorem affineTopDifferentialSheafIso_differentialWedge (f : R) (a : Fin n→R) :
    (affineTopDifferentialSheafIso k R b).hom.app (PrimeSpectrum.basicOpen f)
      (differentialWedgeSection (Spec (CommRingCat.of R)) k
        (PrimeSpectrum.basicOpen f)
        (fun i=>algebraMap R Γ(Spec (CommRingCat.of R),PrimeSpectrum.basicOpen f) (a i))) =
      tilde.toOpen (R := CommRingCat.of R) (ModuleCat.of R (⋀[R]^n (KaehlerDifferential k R)))
        (PrimeSpectrum.basicOpen f)
          (exteriorPower.ιMulti R n (fun i=>KaehlerDifferential.D k R (a i))) := by
  let U : (Spec (CommRingCat.of R)).Opens := PrimeSpectrum.basicOpen f
  let ω : Fin n→Γ(differentialSheaf k (Spec (CommRingCat.of R)),U) :=
    fun i=>(differentialSheafDerivation k (Spec (CommRingCat.of R))).d
      («X» := op U) (algebraMap R Γ(Spec (CommRingCat.of R),U) (a i))
  have hw := sheafExteriorPowerIso_wedge (affineDifferentialSheafIso k R) n U ω
  have hv : (fun i=>(affineDifferentialSheafIso k R).hom.app U (ω i)) =
      (fun i=>tilde.toOpen (R := CommRingCat.of R)
        (ModuleCat.of R (KaehlerDifferential k R)) U
          (KaehlerDifferential.D k R (a i))) := by
    funext i
    exact affineDifferentialSheafIso_D k R f (a i)
  have hη := congrArg
    (fun v=>((PresheafOfModules.sheafificationAdjunction
      (𝟙 (Spec (CommRingCat.of R)).ringCatSheaf.obj)).unit.app
        (presheafExteriorPower (Spec (CommRingCat.of R)).presheaf
          (tilde (R := CommRingCat.of R) (ModuleCat.of R (KaehlerDifferential k R))).val n)).app
            (op U) (exteriorPower.ιMulti Γ(Spec (CommRingCat.of R),U) n v)) hv
  exact (congrArg
    (fun z=>(affineTopExteriorSheafIso (CommRingCat.of R)
      (ModuleCat.of R (KaehlerDifferential k R)) b).hom.app U z)
      (hw.trans hη)).trans
    (affineTopExteriorSheafIso_wedge (CommRingCat.of R)
      (ModuleCat.of R (KaehlerDifferential k R)) b f
        (fun i=>KaehlerDifferential.D k R (a i)))

theorem affineTopDifferentialSheafIso_differentialWedge_top (a : Fin n→R) :
    (affineTopDifferentialSheafIso k R b).hom.app ⊤
      (differentialWedgeSection (Spec (CommRingCat.of R)) k ⊤
        (fun i=>(Scheme.ΓSpecIso (CommRingCat.of R)).inv (a i))) =
      tilde.toOpen (R := CommRingCat.of R) (ModuleCat.of R (⋀[R]^n (KaehlerDifferential k R))) ⊤
        (exteriorPower.ιMulti R n (fun i=>KaehlerDifferential.D k R (a i))) := by
  have h := affineTopDifferentialSheafIso_differentialWedge k R b 1 a
  have hU : (PrimeSpectrum.basicOpen (1 : R) : (Spec (CommRingCat.of R)).Opens)=⊤ :=
    PrimeSpectrum.basicOpen_one
  erw [hU] at h
  have htop (r : R) : algebraMap R Γ(Spec (CommRingCat.of R),⊤) r =
      (Scheme.ΓSpecIso (CommRingCat.of R)).inv r := by
    change (Spec (CommRingCat.of R)).presheaf.map (𝟙 (op ⊤))
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) = _
    exact congrArg (fun φ=>φ ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r))
      ((Spec (CommRingCat.of R)).presheaf.map_id (op ⊤))
  simpa only [htop] using h

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.affineTopDifferentialSheafIso_differentialWedge_top
