module

public import PaperVerification.ToricAffineDifferentialSheaf
public import PaperVerification.ToricLogarithmicVolume

@[expose] public section

/-!
# Actual top exterior powers of free affine module sheaves

The comparison is proved for every finite free module of the stated
rank, including rank zero. The top exterior coefficient on each
principal open is computed in the genuinely localized basis. These
coefficients commute with actual restriction and therefore give the
ordinary tilde/exterior comparison after sheafification. In the toric
application the input basis is the already computed Kähler basis of a
genuine polynomial chart.
-/

noncomputable section

universe u

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open PaperVerification.ToricCharacters
open scoped Classical

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

variable (R : CommRingCat.{u}) (M : ModuleCat.{u} R) {n : ℕ}
    (b : Module.Basis (Fin n) R M)

local notation "X" => Spec R
local notation "Q" => tilde M
local notation "W" => ModuleCat.of R (⋀[R]^n M)
local notation "P" => presheafExteriorPower
  (PresheafedSpace.presheaf (SheafedSpace.toPresheafedSpace
    (LocallyRingedSpace.toSheafedSpace (Scheme.toLocallyRingedSpace (Spec R)))))
  (SheafOfModules.val (tilde M)) n

local instance tildeToOpen_isLocalized (f : R) :
    IsLocalizedModule (.powers f)
      (show M →ₗ[R] Γ(Q,PrimeSpectrum.basicOpen f) from
        (tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom) :=
  inferInstanceAs (IsLocalizedModule.Away f
    (tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom)

def tildeLocalizedBasis (f : R) :
    Module.Basis (Fin n) Γ(X,PrimeSpectrum.basicOpen f) Γ(Q,PrimeSpectrum.basicOpen f) :=
  b.ofIsLocalizedModule Γ(X,PrimeSpectrum.basicOpen f) (.powers f)
    (show M →ₗ[R] Γ(Q,PrimeSpectrum.basicOpen f) from
      (tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom)

@[simp] theorem tildeLocalizedBasis_apply (f : R) (i : Fin n) :
    tildeLocalizedBasis R M b f i=tilde.toOpen M (PrimeSpectrum.basicOpen f) (b i) :=
  Module.Basis.ofIsLocalizedModule_apply _ _ _ _ _

theorem tildeLocalizedBasis_restrict (f g : R)
    (h : PrimeSpectrum.basicOpen g≤PrimeSpectrum.basicOpen f) (i : Fin n) :
    (Q).presheaf.map (homOfLE h).op (tildeLocalizedBasis R M b f i)=
      tildeLocalizedBasis R M b g i := by
  rw [tildeLocalizedBasis_apply,tildeLocalizedBasis_apply]
  exact congrArg (fun φ=>φ (b i))
    (tilde.toOpen_res M (PrimeSpectrum.basicOpen f) (PrimeSpectrum.basicOpen g) (homOfLE h))

/-- The actual global frame of the tilde top module coming from the
ordinary determinant coefficient of the given basis. -/
def tildeTopBasisFrame : tilde W≅SheafOfModules.unit (X).ringCatSheaf :=
  (tilde.functor R).mapIso (basisTopExteriorEquiv b).toModuleIso ≪≫ tildeSelf

def tildeTopBasisCoordinates (U : (X).Opens) : Γ(tilde W,U)≃ₗ[Γ(X,U)] Γ(X,U) :=
  ((PresheafOfModules.evaluation (X).ringCatSheaf.obj (op U)).mapIso
    ((SheafOfModules.forget _).mapIso (tildeTopBasisFrame R M b))).toLinearEquiv

theorem tildeTopBasisCoordinates_restrict {U V : (X).Opens} (h : V≤U)
    (s : Γ(tilde W,U)) :
    tildeTopBasisCoordinates R M b V ((tilde W).presheaf.map (homOfLE h).op s)=
      (X).presheaf.map (homOfLE h).op (tildeTopBasisCoordinates R M b U s) :=
  PresheafOfModules.naturality_apply (tildeTopBasisFrame R M b).hom.val
    (homOfLE h).op s

theorem tildeTopBasisCoordinates_toOpen (U : (X).Opens) (ω : ⋀[R]^n M) :
    tildeTopBasisCoordinates R M b U (tilde.toOpen W U ω)=
      algebraMap R Γ(X,U) (basisTopExteriorEquiv b ω) := by
  calc
    _ = tilde.toOpen (ModuleCat.of R R) U (basisTopExteriorEquiv b ω) := by
      exact congrArg (fun φ=>φ ω)
        (tilde.toOpen_map_app (basisTopExteriorEquiv b).toModuleIso.hom U)
    _ = _ := rfl

/-- The coefficient comparison is an equivalence over the actual
principal-open structure ring. -/
def affineTopExteriorBasicEquiv (f : R) :
    (P).obj (op (PrimeSpectrum.basicOpen f))≃ₗ[Γ(X,PrimeSpectrum.basicOpen f)]
      Γ(tilde W,PrimeSpectrum.basicOpen f) :=
  (basisTopExteriorEquiv (tildeLocalizedBasis R M b f)).trans
    (tildeTopBasisCoordinates R M b (PrimeSpectrum.basicOpen f)).symm

theorem localizedTopCoefficient_restrict (f g : R)
    (h : PrimeSpectrum.basicOpen g≤PrimeSpectrum.basicOpen f)
    (ω : (P).obj (op (PrimeSpectrum.basicOpen f))) :
    basisTopExteriorEquiv (tildeLocalizedBasis R M b g) ((P).map (homOfLE h).op ω)=
      (X).presheaf.map (homOfLE h).op
        (basisTopExteriorEquiv (tildeLocalizedBasis R M b f) ω) := by
  let c := basisTopExteriorEquiv (tildeLocalizedBasis R M b f) ω
  have hω : ω=c • exteriorPower.ιMulti Γ(X,PrimeSpectrum.basicOpen f) n
      (tildeLocalizedBasis R M b f) :=
    topExterior_eq_smul_basis (tildeLocalizedBasis R M b f) ω
  calc
    basisTopExteriorEquiv (tildeLocalizedBasis R M b g) ((P).map (homOfLE h).op ω)=
        basisTopExteriorEquiv (tildeLocalizedBasis R M b g)
          ((P).map (homOfLE h).op
            (c • exteriorPower.ιMulti Γ(X,PrimeSpectrum.basicOpen f) n
              (tildeLocalizedBasis R M b f))) := congrArg _ (congrArg _ hω)
    _ = basisTopExteriorEquiv (tildeLocalizedBasis R M b g)
        ((X).presheaf.map (homOfLE h).op c •
          (P).map (homOfLE h).op
            (exteriorPower.ιMulti Γ(X,PrimeSpectrum.basicOpen f) n
              (tildeLocalizedBasis R M b f))) :=
      congrArg (fun z : (P).obj (op (PrimeSpectrum.basicOpen g)) =>
        basisTopExteriorEquiv (tildeLocalizedBasis R M b g) z)
        ((P).map_smul (homOfLE h).op c
          (exteriorPower.ιMulti Γ(X,PrimeSpectrum.basicOpen f) n
            (tildeLocalizedBasis R M b f)))
    _ = basisTopExteriorEquiv (tildeLocalizedBasis R M b g)
        ((X).presheaf.map (homOfLE h).op c •
          exteriorPower.ιMulti Γ(X,PrimeSpectrum.basicOpen g) n
            (tildeLocalizedBasis R M b g)) := by
      have hw : (P).map (homOfLE h).op
          (exteriorPower.ιMulti Γ(X,PrimeSpectrum.basicOpen f) n
            (tildeLocalizedBasis R M b f)) =
          exteriorPower.ιMulti Γ(X,PrimeSpectrum.basicOpen g) n
            (tildeLocalizedBasis R M b g) := by
        calc
          _ = exteriorPower.ιMulti Γ(X,PrimeSpectrum.basicOpen g) n
              (fun i : Fin n => (Q).val.map (homOfLE h).op
                (tildeLocalizedBasis R M b f i)) :=
            presheafExteriorPower_map_wedge (X).presheaf (Q).val n
              (homOfLE h).op (tildeLocalizedBasis R M b f)
          _ = _ := congrArg
            (fun v : Fin n → Γ(Q,PrimeSpectrum.basicOpen g) =>
              exteriorPower.ιMulti Γ(X,PrimeSpectrum.basicOpen g) n v)
            (funext (fun i => tildeLocalizedBasis_restrict R M b f g h i))
      exact congrArg (fun z : (P).obj (op (PrimeSpectrum.basicOpen g)) =>
        basisTopExteriorEquiv (tildeLocalizedBasis R M b g)
          ((X).presheaf.map (homOfLE h).op c • z)) hw
    _ = (X).presheaf.map (homOfLE h).op c *
        basisTopExteriorEquiv (tildeLocalizedBasis R M b g)
          (exteriorPower.ιMulti Γ(X,PrimeSpectrum.basicOpen g) n
            (tildeLocalizedBasis R M b g)) :=
      (basisTopExteriorEquiv (tildeLocalizedBasis R M b g)).map_smul _ _
    _ = (X).presheaf.map (homOfLE h).op c * 1 :=
      congrArg (fun r : Γ(X,PrimeSpectrum.basicOpen g) =>
        (X).presheaf.map (homOfLE h).op c * r)
        (basisTopExteriorEquiv_basis (tildeLocalizedBasis R M b g))
    _ = (X).presheaf.map (homOfLE h).op c := mul_one _

theorem affineTopExteriorBasicEquiv_natural (f g : R)
    (h : PrimeSpectrum.basicOpen g≤PrimeSpectrum.basicOpen f)
    (ω : (P).obj (op (PrimeSpectrum.basicOpen f))) :
    affineTopExteriorBasicEquiv R M b g ((P).map (homOfLE h).op ω)=
      (tilde W).presheaf.map (homOfLE h).op (affineTopExteriorBasicEquiv R M b f ω) := by
  apply (tildeTopBasisCoordinates R M b (PrimeSpectrum.basicOpen g)).injective
  rw [tildeTopBasisCoordinates_restrict]
  simp only [affineTopExteriorBasicEquiv,LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  exact localizedTopCoefficient_restrict R M b f g h ω

theorem tildeLocalizedBasis_det (f : R) (v : Fin n→M) :
    (tildeLocalizedBasis R M b f).det
        (fun i=>tilde.toOpen M (PrimeSpectrum.basicOpen f) (v i))=
      algebraMap R Γ(X,PrimeSpectrum.basicOpen f) (b.det v) := by
  have hm : (tildeLocalizedBasis R M b f).toMatrix
      (fun i=>tilde.toOpen M (PrimeSpectrum.basicOpen f) (v i))=
        (algebraMap R Γ(X,PrimeSpectrum.basicOpen f)).mapMatrix (b.toMatrix v) := by
    funext i j
    exact b.ofIsLocalizedModule_repr_apply
      Γ(X,PrimeSpectrum.basicOpen f) (.powers f)
      (show M →ₗ[R] Γ(Q,PrimeSpectrum.basicOpen f) from
        (tilde.toOpen M (PrimeSpectrum.basicOpen f)).hom) (v j) i
  rw [Module.Basis.det_apply,hm,← RingHom.map_det,← Module.Basis.det_apply]

/-- The comparison is the ordinary wedge map on actual restricted
sections; the coefficient construction has not changed the exterior map. -/
theorem affineTopExteriorBasicEquiv_wedge (f : R) (v : Fin n→M) :
    affineTopExteriorBasicEquiv R M b f
      (exteriorPower.ιMulti Γ(X,PrimeSpectrum.basicOpen f) n
        (fun i=>tilde.toOpen M (PrimeSpectrum.basicOpen f) (v i)))=
      tilde.toOpen W (PrimeSpectrum.basicOpen f) (exteriorPower.ιMulti R n v) := by
  apply (tildeTopBasisCoordinates R M b (PrimeSpectrum.basicOpen f)).injective
  rw [tildeTopBasisCoordinates_toOpen]
  simp only [affineTopExteriorBasicEquiv,LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply]
  exact (basisTopExteriorEquiv_wedge (tildeLocalizedBasis R M b f)
    (fun i => tilde.toOpen M (PrimeSpectrum.basicOpen f) (v i))).trans
      ((tildeLocalizedBasis_det R M b f v).trans
        (congrArg (algebraMap R Γ(X,PrimeSpectrum.basicOpen f))
          (basisTopExteriorEquiv_wedge b v)).symm)

/-- Actual top exterior power commutes with the actual affine tilde
construction. The source is the sheafification definition of the
ordinary exterior module of the actual section modules. -/
def affineTopExteriorSheafIso :
    sheafExteriorPower X (tilde M) n≅tilde W :=
  basisModuleSheafificationIso (fun f : R=>PrimeSpectrum.basicOpen f)
    PrimeSpectrum.isBasis_basic_opens P (tilde W)
    (fun f=>(affineTopExteriorBasicEquiv R M b f).toLinearMap)
    (affineTopExteriorBasicEquiv_natural R M b)
    (fun f=>(affineTopExteriorBasicEquiv R M b f).bijective)

theorem affineTopExteriorSheafIso_basic (f : R)
    (ω : (P).obj (op (PrimeSpectrum.basicOpen f))) :
    (affineTopExteriorSheafIso R M b).hom.app (PrimeSpectrum.basicOpen f)
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 (X).ringCatSheaf.obj)).unit.app P).app (op (PrimeSpectrum.basicOpen f)) ω)=
        affineTopExteriorBasicEquiv R M b f ω := by
  have h := basisModuleSheafificationIso_unit
    (fun f : R=>PrimeSpectrum.basicOpen f) PrimeSpectrum.isBasis_basic_opens P (tilde W)
    (fun f=>(affineTopExteriorBasicEquiv R M b f).toLinearMap)
    (affineTopExteriorBasicEquiv_natural R M b)
    (fun f=>(affineTopExteriorBasicEquiv R M b f).bijective)
  exact (congrArg (fun φ=>φ.app (op (PrimeSpectrum.basicOpen f)) ω) h).trans
    (basisModuleComparison_app _ _ _ _ _ _ f ω)

theorem affineTopExteriorSheafIso_wedge (f : R) (v : Fin n→M) :
    (affineTopExteriorSheafIso R M b).hom.app (PrimeSpectrum.basicOpen f)
      (((PresheafOfModules.sheafificationAdjunction
        (𝟙 (X).ringCatSheaf.obj)).unit.app P).app (op (PrimeSpectrum.basicOpen f))
          (exteriorPower.ιMulti Γ(X,PrimeSpectrum.basicOpen f) n
            (fun i=>tilde.toOpen M (PrimeSpectrum.basicOpen f) (v i))))=
        tilde.toOpen W (PrimeSpectrum.basicOpen f) (exteriorPower.ιMulti R n v) := by
  rw [affineTopExteriorSheafIso_basic,affineTopExteriorBasicEquiv_wedge]

end PaperVerification.ToricSchemes

namespace PaperVerification.ToricSchemes

open AlgebraicGeometry CategoryTheory

variable (k R : Type u) [CommRing k] [CommRing R] [Algebra k R] {n : ℕ}
    (b : Module.Basis (Fin n) R (KaehlerDifferential k R))

/-- The ordinary intrinsic top differential sheaf on the affine chart
is the tilde of the ordinary top algebraic Kähler module. -/
def affineTopDifferentialSheafIso :
    topDifferentialSheaf k (Spec (CommRingCat.of R)) n≅
      tilde (R := CommRingCat.of R) (ModuleCat.of R (⋀[R]^n (KaehlerDifferential k R))) :=
  sheafExteriorPowerIso (Spec (CommRingCat.of R))
    (affineDifferentialSheafIso k R) n ≪≫
      affineTopExteriorSheafIso (CommRingCat.of R)
        (ModuleCat.of R (KaehlerDifferential k R)) b

end PaperVerification.ToricSchemes
