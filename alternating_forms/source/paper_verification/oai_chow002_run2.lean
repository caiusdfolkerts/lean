module

public import paper_verification.oai_chow001_run2
import all paper_verification.oai_chow001_run2
public import Mathlib.RingTheory.Ideal.Quotient.Operations
import all Mathlib.RingTheory.Ideal.Quotient.Operations
public import paper_verification.oai_chow000_run4
import all paper_verification.oai_chow000_run4
public import Mathlib.RingTheory.Localization.Ideal
import all Mathlib.RingTheory.Localization.Ideal
public import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import all Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import all Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.AlgebraicGeometry.Properties
import all Mathlib.AlgebraicGeometry.Properties
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import all Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Noetherian
import all Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
import all Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
import all Mathlib.AlgebraicGeometry.AlgebraicCycle.Basic
public import Mathlib.Data.Finsupp.Basic
import all Mathlib.Data.Finsupp.Basic
public import Mathlib.LinearAlgebra.Finsupp.Supported
import all Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.LinearAlgebra.Finsupp.VectorSpace
import all Mathlib.LinearAlgebra.Finsupp.VectorSpace
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import all Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
import Lean.Util.CollectAxioms
import Lean.Util.FoldConsts
import Lean.PrettyPrinter

set_option Elab.async false

@[expose] public section ComponentSource_0
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.DivisorRestriction -/

/-! # Divisor Restriction -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.DivisorRestriction.BundleCycles

noncomputable section

/-!
# LineBundleCycles: restriction of effective Cartier divisor coefficients

Local quotient length is invariant under the actual stalk isomorphism of
an open immersion. Consequently the finite divisor of a nonzero global
function restricts coefficientwise to the divisor of its restriction.
This supplies the locality of the multiplicities used in specialization.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.Order

universe u v

/-- Ring isomorphisms preserve the length defining the order of a regular function. -/
theorem ringOrder_equiv {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (e : R ≃+* S) (a : R) : Ring.ord S (e a) = Ring.ord R a := by
  let : Algebra R S := e.toRingHom.toAlgebra
  let eA : R ≃ₐ[R] S := { e with commutes' := fun _ => rfl }
  have hI : Ideal.span {e a} = (Ideal.span {a}).map e.toRingHom := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  let eQ := Ideal.quotientEquivAlg (Ideal.span {a}) (Ideal.span {e a}) eA hI
  exact (Module.length_eq_of_surjective (R := S) (M := S ⧸ Ideal.span {e a})
    e.surjective).symm.trans eQ.toLinearEquiv.length_eq.symm

variable {X Y : Scheme.{u}} [IsIntegral X] [IsIntegral Y]
variable (f : X ⟶ Y) [IsOpenImmersion f]

/-- A nonzero global section remains nonzero on a nonempty integral open subscheme. -/
theorem openImmersion_appTop_ne_zero (a : Γ(Y, ⊤)) (ha : a ≠ 0) : f.appTop a ≠ 0 := by
  intro h
  let x : X := genericPoint X
  have hg : Y.presheaf.germ ⊤ (f x) (by trivial) a ≠ 0 :=
    (map_ne_zero_iff _ (germ_injective_of_isIntegral Y (f x) (by trivial))).mpr ha
  apply hg
  apply (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv.injective
  change f.stalkMap x (Y.presheaf.germ ⊤ (f x) (by trivial) a) = f.stalkMap x 0
  have he := f.germ_stalkMap_apply ⊤ x (by trivial) a
  change f.stalkMap x (Y.presheaf.germ ⊤ (f x) (by trivial) a) =
    X.presheaf.germ ⊤ x (by trivial) (f.appTop a) at he
  exact he.trans ((congrArg (X.presheaf.germ ⊤ x (by trivial)) h).trans
    ((map_zero (X.presheaf.germ ⊤ x (by trivial)).hom).trans
      (map_zero (f.stalkMap x).hom).symm))

variable [AlgebraicGeometry.IsNoetherian X] [AlgebraicGeometry.IsNoetherian Y]

/-- The actual local-length divisor coefficients commute with open restriction. -/
theorem regularFunctionDivisor_openImmersion (a : Γ(Y, ⊤)) (ha : a ≠ 0) (x : X) :
    RegularDivisor.BundleCycles.regularFunctionDivisor X (f.appTop a) x = RegularDivisor.BundleCycles.regularFunctionDivisor Y a (f x) := by
  have hc : coheight (f x) = coheight x := coheight_eq_of_isOpenImmersion f
  by_cases hx : coheight x = 1
  · rw [RegularDivisor.BundleCycles.regularFunctionDivisor_coeff_length X _ (openImmersion_appTop_ne_zero f a ha) x hx,
      RegularDivisor.BundleCycles.regularFunctionDivisor_coeff_length Y a ha (f x) (hc.trans hx)]
    let e := (asIso (f.stalkMap x)).commRingCatIsoToRingEquiv
    have he : e (Y.presheaf.germ ⊤ (f x) (by trivial) a) =
        X.presheaf.germ ⊤ x (by trivial) (f.appTop a) :=
      f.germ_stalkMap_apply ⊤ x (by trivial) a
    have hl := ringOrder_equiv e (Y.presheaf.germ ⊤ (f x) (by trivial) a)
    rw [he] at hl
    exact congrArg (fun n : ℕ∞ => (n.toNat : ℤ)) hl
  · change X.ord (RegularDivisor.BundleCycles.globalFunctionFieldElement X (f.appTop a)) x =
      Y.ord (RegularDivisor.BundleCycles.globalFunctionFieldElement Y a) (f x)
    rw [Scheme.ord_eq_zero_of_coheight_neq_one hx,
      Scheme.ord_eq_zero_of_coheight_neq_one (fun h => hx (hc.symm.trans h))]

/-- The finite divisor on the open subscheme is exactly coefficient restriction,
with no change to multiplicities. -/
theorem regularFunctionDivisor_comap (a : Γ(Y, ⊤)) (ha : a ≠ 0) :
    Finsupp.comapDomain f (RegularDivisor.BundleCycles.regularFunctionDivisor Y a) f.isOpenEmbedding.injective.injOn =
      RegularDivisor.BundleCycles.regularFunctionDivisor X (f.appTop a) := by
  ext x
  exact (regularFunctionDivisor_openImmersion f a ha x).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.DivisorRestriction.BundleCycles
end ComponentSource_0

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.DivisorRestriction"

@[expose] public section ComponentSource_1
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Global.Specialization -/

/-! # Specialization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Global.Specialization.BundleCycles

noncomputable section

/-!
# LineBundleCycles: global specialization of an integral scheme

The actual global parameter gives a finite effective divisor on the integral
Noetherian deformation. Its entire support lies on the scheme-theoretic zero
fiber, so that divisor defines a finite cycle on the glued normal cone.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.Order
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

universe u

/-- The coordinate section on the parameter line. -/
def parameterLineSection : Γ(Deformation.Parameter.BundleCycles.deformationParameterLine.{u}, ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of (Polynomial (ULift.{u} ℤ)))).inv Polynomial.X

/-- Parameter zero is exactly the vanishing locus of the coordinate section. -/
theorem parameterZeroInclusion_range :
    Set.range QuotientFiber.BundleCycles.parameterZeroInclusion.{u} =
      (Deformation.Parameter.BundleCycles.deformationParameterLine.basicOpen parameterLineSection : Set Deformation.Parameter.BundleCycles.deformationParameterLine)ᶜ := by
  let A : CommRingCat := .of (Polynomial (ULift.{u} ℤ))
  let B : CommRingCat := .of (Polynomial (ULift.{u} ℤ) ⧸ QuotientFiber.BundleCycles.parameterZeroIdeal)
  let g : A ⟶ B := CommRingCat.ofHom (Ideal.Quotient.mk QuotientFiber.BundleCycles.parameterZeroIdeal)
  have hsurj : Function.Surjective g := Ideal.Quotient.mk_surjective
  have hker : RingHom.ker g.hom = QuotientFiber.BundleCycles.parameterZeroIdeal := Ideal.mk_ker
  change Set.range (PrimeSpectrum.comap g.hom) = _
  rw [range_comap_of_surjective _ _ hsurj, hker]
  change PrimeSpectrum.zeroLocus QuotientFiber.BundleCycles.parameterZeroIdeal =
    ((Spec A).basicOpen ((Scheme.ΓSpecIso A).inv Polynomial.X) : Set (Spec A))ᶜ
  rw [basicOpen_eq_of_affine]
  ext x
  simp only [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
  change Ideal.span {Polynomial.X} ≤ x.asIdeal ↔ ¬Polynomial.X ∉ x.asIdeal
  exact (Ideal.span_singleton_le_iff_mem (I := x.asIdeal)).trans not_not.symm

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The actual global regular parameter section. -/
def globalDeformationParameterSection : Γ(Deformation.BundleCycles.globalDeformation I, ⊤) :=
  (Deformation.Parameter.BundleCycles.globalDeformationParameter I).appTop parameterLineSection

/-- Restricting the global section gives the original affine Laurent parameter. -/
theorem globalDeformationParameterSection_on_chart (U : X.AffineZariskiSite) :
    ((Deformation.BundleCycles.globalDeformationCover I).f U).appTop (globalDeformationParameterSection I) =
      Affine.Specialization.BundleCycles.affineDeformationParameterSection (I.ideal U) := by
  let a : CommRingCat.of (Polynomial (ULift.{u} ℤ)) ⟶
      CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra (I.ideal U)) :=
    CommRingCat.ofHom (Deformation.Parameter.BundleCycles.deformationParameterRingMap (I.ideal U))
  have h := congrArg (fun k => k.appTop parameterLineSection)
    (Deformation.Parameter.BundleCycles.globalDeformationParameter_on_chart I U)
  have he := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality a) Polynomial.X
  change (Scheme.ΓSpecIso (CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra (I.ideal U)))).inv
      (Deformation.Parameter.BundleCycles.deformationParameterRingMap (I.ideal U) Polynomial.X) =
    (Spec.map a).appTop parameterLineSection at he
  rw [Deformation.Parameter.BundleCycles.deformationParameterRingMap_X] at he
  exact h.trans he.symm

/-- The global closed-fiber embedding has exactly the vanishing locus of t as its range. -/
theorem globalSpecialFiberMap_range :
    Set.range (SpecialFiber.BundleCycles.globalSpecialFiberMap I) =
      ((Deformation.BundleCycles.globalDeformation I).basicOpen (globalDeformationParameterSection I) :
        Set (Deformation.BundleCycles.globalDeformation I))ᶜ := by
  have h := Scheme.image_preimage_eq_of_isPullback (QuotientFiber.BundleCycles.globalSpecialFiber_isPullback I).flip Set.univ
  simp only [Set.preimage_univ, Set.image_univ] at h
  change Set.range (SpecialFiber.BundleCycles.globalSpecialFiberMap I) =
    Deformation.Parameter.BundleCycles.globalDeformationParameter I ⁻¹' Set.range QuotientFiber.BundleCycles.parameterZeroInclusion at h
  rw [parameterZeroInclusion_range, Set.preimage_compl] at h
  have hb := Scheme.preimage_basicOpen_top (Deformation.Parameter.BundleCycles.globalDeformationParameter I) parameterLineSection
  exact h.trans (congrArg (fun U : (Deformation.BundleCycles.globalDeformation I).Opens => (U : Set (Deformation.BundleCycles.globalDeformation I))ᶜ) hb)

/-- The canonical affine normal-cone chart as a morphism into the global cone. -/
def globalNormalConeChartMap (U : X.AffineZariskiSite) :
    Normal.Cone.BundleCycles.affineNormalCone (I.ideal U) ⟶ SpecialFiber.BundleCycles.globalSpecialFiber I :=
  (SpecialFiber.BundleCycles.globalSpecialFiberNormalConeChart I U).hom ≫ (SpecialFiber.BundleCycles.globalSpecialFiberCover I).f U

theorem globalNormalConeChartMap_toDeformation (U : X.AffineZariskiSite) :
    globalNormalConeChartMap I U ≫ SpecialFiber.BundleCycles.globalSpecialFiberMap I =
      Affine.Specialization.BundleCycles.normalConeFiberInclusion (I.ideal U) ≫ (Deformation.BundleCycles.globalDeformationCover I).f U := by
  let a : CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra (I.ideal U)) ⟶
      CommRingCat.of (SpecialFiber.BundleCycles.DeformationSpecialRing (I.ideal U)) :=
    CommRingCat.ofHom (Ideal.Quotient.mk (Deformation.Iff.BundleCycles.deformationSpecialIdeal (I.ideal U)))
  let b : CommRingCat.of (SpecialFiber.BundleCycles.DeformationSpecialRing (I.ideal U)) ⟶
      CommRingCat.of (Normal.Cone.BundleCycles.NormalConeRing (I.ideal U)) :=
    CommRingCat.ofHom (SpecialFiber.BundleCycles.normalConeSpecialFiberEquiv (I.ideal U)).symm.toRingHom
  have h : (SpecialFiber.BundleCycles.globalSpecialFiberNormalConeChart I U).hom ≫ Spec.map a =
      Affine.Specialization.BundleCycles.normalConeFiberInclusion (I.ideal U) := (Spec.map_comp a b).symm
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun k => (SpecialFiber.BundleCycles.globalSpecialFiberNormalConeChart I U).hom ≫ k)
      (SpecialFiber.BundleCycles.globalSpecialFiberMap_on_chart I U)).trans
    ((Category.assoc _ _ _).symm.trans
      (congrArg (fun k => k ≫ (Deformation.BundleCycles.globalDeformationCover I).f U) h)))

variable [IsIntegral X]

/-- The global parameter is nonzero, as can be checked on any nonempty affine chart. -/
theorem globalDeformationParameterSection_ne_zero : globalDeformationParameterSection I ≠ 0 := by
  let x : X := Classical.choice inferInstance
  let U : X.AffineZariskiSite := (directedCover X).idx x
  obtain ⟨y, _⟩ := (directedCover X).covers x
  have : Nonempty U.1 := ⟨y⟩
  have : IsDomain Γ(X, U.1) := inferInstance
  intro hz
  have h := congrArg ((Deformation.BundleCycles.globalDeformationCover I).f U).appTop hz
  rw [globalDeformationParameterSection_on_chart I U] at h
  exact Affine.Specialization.BundleCycles.affineDeformationParameterSection_ne_zero (I.ideal U)
    (h.trans (map_zero ((Deformation.BundleCycles.globalDeformationCover I).f U).appTop.hom))

variable [AlgebraicGeometry.IsNoetherian X]

/-- The finite effective divisor of t on the actual global deformation. -/
def globalDeformationParameterDivisor : Deformation.BundleCycles.globalDeformation I →₀ ℤ :=
  RegularDivisor.BundleCycles.regularFunctionDivisor (Deformation.BundleCycles.globalDeformation I) (globalDeformationParameterSection I)

theorem globalDeformationParameterDivisor_nonnegative (x : Deformation.BundleCycles.globalDeformation I) :
    0 ≤ globalDeformationParameterDivisor I x :=
  RegularDivisor.BundleCycles.regularFunctionDivisor_nonnegative _ _ (globalDeformationParameterSection_ne_zero I) x

theorem globalDeformationParameterDivisor_support :
    ((globalDeformationParameterDivisor I).support : Set (Deformation.BundleCycles.globalDeformation I)) ⊆
      Set.range (SpecialFiber.BundleCycles.globalSpecialFiberMap I) := by
  rw [globalSpecialFiberMap_range]
  exact RegularDivisor.BundleCycles.regularFunctionDivisor_support_subset _ _

/-- The point embedding of the globally glued normal cone. -/
def globalSpecialFiberPointEmbedding : SpecialFiber.BundleCycles.globalSpecialFiber I ↪ Deformation.BundleCycles.globalDeformation I :=
  ⟨SpecialFiber.BundleCycles.globalSpecialFiberMap I, (SpecialFiber.BundleCycles.globalSpecialFiberMap I).isClosedEmbedding.injective⟩

/-- The entire parameter divisor, transported to the actual global normal cone. -/
def globalSpecializationCycle : SpecialFiber.BundleCycles.globalSpecialFiber I →₀ ℤ :=
  Finsupp.comapDomain (globalSpecialFiberPointEmbedding I) (globalDeformationParameterDivisor I)
    (globalSpecialFiberPointEmbedding I).injective.injOn

@[simp]
theorem globalSpecializationCycle_apply (x : SpecialFiber.BundleCycles.globalSpecialFiber I) :
    globalSpecializationCycle I x = globalDeformationParameterDivisor I (SpecialFiber.BundleCycles.globalSpecialFiberMap I x) := rfl

/-- Pushing the specialization cycle back recovers every coefficient of the divisor of t. -/
theorem globalSpecializationCycle_push :
    Finsupp.embDomain (globalSpecialFiberPointEmbedding I) (globalSpecializationCycle I) =
      globalDeformationParameterDivisor I :=
  Finsupp.embDomain_comapDomain (globalDeformationParameterDivisor_support I)

theorem globalSpecializationCycle_nonnegative (x : SpecialFiber.BundleCycles.globalSpecialFiber I) :
    0 ≤ globalSpecializationCycle I x := globalDeformationParameterDivisor_nonnegative I _

/-- The global multiplicity is the actual length of the local quotient by t. -/
theorem globalSpecializationCycle_coeff_length (x : SpecialFiber.BundleCycles.globalSpecialFiber I)
    (hx : coheight (SpecialFiber.BundleCycles.globalSpecialFiberMap I x) = 1) :
    globalSpecializationCycle I x =
      ((Module.length ((Deformation.BundleCycles.globalDeformation I).presheaf.stalk (SpecialFiber.BundleCycles.globalSpecialFiberMap I x))
        (((Deformation.BundleCycles.globalDeformation I).presheaf.stalk (SpecialFiber.BundleCycles.globalSpecialFiberMap I x)) ⧸
          Ideal.span (Set.singleton ((Deformation.BundleCycles.globalDeformation I).presheaf.germ ⊤ (SpecialFiber.BundleCycles.globalSpecialFiberMap I x)
            (by trivial) (globalDeformationParameterSection I))))).toNat : ℤ) :=
  RegularDivisor.BundleCycles.regularFunctionDivisor_coeff_length _ _ (globalDeformationParameterSection_ne_zero I) _ hx

/-- The global parameter divisor restricts to the affine divisor with the same local lengths. -/
theorem globalDeformationParameterDivisor_on_chart (U : X.AffineZariskiSite) [Nonempty U.1]
    (x : (Deformation.BundleCycles.globalDeformationCover I).X U) :
    globalDeformationParameterDivisor I ((Deformation.BundleCycles.globalDeformationCover I).f U x) =
      Affine.Specialization.BundleCycles.affineDeformationParameterDivisor (I.ideal U) x := by
  have : IsDomain Γ(X, U.1) := inferInstance
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have : IsIntegral ((Deformation.BundleCycles.globalDeformationCover I).X U) :=
    inferInstanceAs (IsIntegral (Spec (CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra (I.ideal U)))))
  have : AlgebraicGeometry.IsNoetherian ((Deformation.BundleCycles.globalDeformationCover I).X U) :=
    inferInstanceAs (AlgebraicGeometry.IsNoetherian
      (Spec (CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra (I.ideal U)))))
  have h := DivisorRestriction.BundleCycles.regularFunctionDivisor_openImmersion ((Deformation.BundleCycles.globalDeformationCover I).f U)
    (globalDeformationParameterSection I) (globalDeformationParameterSection_ne_zero I) x
  rw [globalDeformationParameterSection_on_chart I U] at h
  exact h.symm

/-- The global specialization agrees with every actual affine normal-cone specialization. -/
theorem globalSpecializationCycle_on_chart (U : X.AffineZariskiSite) [Nonempty U.1]
    (x : Normal.Cone.BundleCycles.affineNormalCone (I.ideal U)) :
    globalSpecializationCycle I (globalNormalConeChartMap I U x) =
      Affine.Specialization.BundleCycles.affineSpecializationCycle (I.ideal U) x := by
  have : IsDomain Γ(X, U.1) := inferInstance
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have h := congrArg (fun k => k x) (globalNormalConeChartMap_toDeformation I U)
  change SpecialFiber.BundleCycles.globalSpecialFiberMap I (globalNormalConeChartMap I U x) =
    (Deformation.BundleCycles.globalDeformationCover I).f U (Affine.Specialization.BundleCycles.normalConeFiberInclusion (I.ideal U) x) at h
  rw [globalSpecializationCycle_apply, h]
  exact globalDeformationParameterDivisor_on_chart I U (Affine.Specialization.BundleCycles.normalConeFiberInclusion (I.ideal U) x)

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Global.Specialization.BundleCycles
end ComponentSource_1

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Global.Specialization"

@[expose] public section ComponentSource_2
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Closure -/

/-! # Closure -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Closure.BundleCycles

noncomputable section

/-!
# LineBundleCycles: saturation of a deformed closed support

The coefficientwise support ideal is saturated with respect to t. Thus
localizing its defining ideal at t and contracting it recovers exactly
the same closed deformation, without adding components on the special fiber.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

universe u
variable {R : Type u} [CommRing R]

theorem closedSupportDeformationRingMap_parameter (I P : Ideal R) :
    ClosedSupport.BundleCycles.closedSupportDeformationRingMap I P (Iff.BundleCycles.deformationParameter I) =
      Iff.BundleCycles.deformationParameter (I.map (Ideal.Quotient.mk P)) :=
  Maps.BundleCycles.deformationMap_parameter I _ (Ideal.Quotient.mk P) _

/-- Multiplication by any power of t does not change membership in the
actual defining ideal of the deformed closed support. -/
theorem closedSupportDeformationKernel_saturated (I P : Ideal R)
    (p : Iff.BundleCycles.deformationAlgebra I) (n : ℕ) :
    Iff.BundleCycles.deformationParameter I ^ n * p ∈ RingHom.ker (ClosedSupport.BundleCycles.closedSupportDeformationRingMap I P) ↔
      p ∈ RingHom.ker (ClosedSupport.BundleCycles.closedSupportDeformationRingMap I P) := by
  simp only [RingHom.mem_ker, map_mul, map_pow, closedSupportDeformationRingMap_parameter]
  constructor
  · exact mem_nonZeroDivisors_iff_left.mp
      (pow_mem (Iff.BundleCycles.deformationParameter_regular (I.map (Ideal.Quotient.mk P))) n) _
  · intro h
    rw [h, mul_zero]

/-- Contracting the defining ideal from the punctured deformation gives
exactly the original ideal: this is the affine schematic-closure condition. -/
theorem closedSupportDeformationKernel_localize_contract (I P : Ideal R) :
    ((RingHom.ker (ClosedSupport.BundleCycles.closedSupportDeformationRingMap I P)).map
      (algebraMap (Iff.BundleCycles.deformationAlgebra I) (LaurentPolynomial R))).comap
        (algebraMap (Iff.BundleCycles.deformationAlgebra I) (LaurentPolynomial R)) =
      RingHom.ker (ClosedSupport.BundleCycles.closedSupportDeformationRingMap I P) := by
  ext p
  rw [Ideal.mem_comap, IsLocalization.algebraMap_mem_map_algebraMap_iff
    (Submonoid.powers (Iff.BundleCycles.deformationParameter I))]
  constructor
  · rintro ⟨m, ⟨n, rfl⟩, hm⟩
    exact (closedSupportDeformationKernel_saturated I P p n).mp hm
  · intro hp
    exact ⟨1, Submonoid.one_mem _, by simpa only [one_mul] using hp⟩

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Closure.BundleCycles
end ComponentSource_2

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Deformation.Closure"

@[expose] public section ComponentSource_3
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Support.Specialization -/

/-! # Specialization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Support.Specialization.BundleCycles

noncomputable section

/-!
# LineBundleCycles: specialization of a global integral closed support

The actual integral support deformation has a nonzero global parameter.
Its finite effective divisor lies on the pullback of the ambient normal
cone. Pushing this entire divisor along that closed fiber gives a finite
cycle on the ambient global cone.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.Order
open _root_.AlgebraicGeometry.Scheme.AffineZariskiSite

universe u
variable {X : Scheme.{u}} (I P : X.IdealSheafData)

/-- The regular parameter on the support deformation is pulled from the ambient deformation. -/
def globalSupportParameterSection : Γ(Global.SupportDeformation.BundleCycles.globalSupportDeformation I P, ⊤) :=
  (Global.SupportDeformation.BundleCycles.globalSupportDeformationMap I P).appTop (Global.Specialization.BundleCycles.globalDeformationParameterSection I)

theorem closedSupportDeformationParameterSection {R : Type u} [CommRing R] (J Q : Ideal R) :
    (Deformation.ClosedSupport.BundleCycles.closedSupportDeformationInclusion J Q).appTop (Affine.Specialization.BundleCycles.affineDeformationParameterSection J) =
      Affine.Specialization.BundleCycles.affineDeformationParameterSection (J.map (Ideal.Quotient.mk Q)) := by
  let f : CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra J) ⟶
      CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra (J.map (Ideal.Quotient.mk Q))) :=
    CommRingCat.ofHom (Deformation.ClosedSupport.BundleCycles.closedSupportDeformationRingMap J Q)
  have h := ConcreteCategory.congr_hom (Scheme.ΓSpecIso_inv_naturality f) (Deformation.Iff.BundleCycles.deformationParameter J)
  change (Scheme.ΓSpecIso (CommRingCat.of (Deformation.Iff.BundleCycles.deformationAlgebra (J.map (Ideal.Quotient.mk Q))))).inv
      (Deformation.ClosedSupport.BundleCycles.closedSupportDeformationRingMap J Q (Deformation.Iff.BundleCycles.deformationParameter J)) =
    (Deformation.ClosedSupport.BundleCycles.closedSupportDeformationInclusion J Q).appTop (Affine.Specialization.BundleCycles.affineDeformationParameterSection J) at h
  rw [Deformation.Closure.BundleCycles.closedSupportDeformationRingMap_parameter] at h
  exact h.symm

/-- Every support chart carries exactly its original Laurent parameter section. -/
theorem globalSupportParameterSection_on_chart (U : X.AffineZariskiSite) :
    ((Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).f U).appTop (globalSupportParameterSection I P) =
      Affine.Specialization.BundleCycles.affineDeformationParameterSection (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U) := by
  have h := congrArg (fun k => k.appTop (Global.Specialization.BundleCycles.globalDeformationParameterSection I))
    (Global.SupportDeformation.BundleCycles.globalSupportDeformationMap_on_chart I P U)
  change ((Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).f U).appTop (globalSupportParameterSection I P) =
    (Deformation.ClosedSupport.BundleCycles.closedSupportDeformationInclusion (I.ideal U) (P.ideal U)).appTop
      (((Global.Deformation.BundleCycles.globalDeformationCover I).f U).appTop (Global.Specialization.BundleCycles.globalDeformationParameterSection I)) at h
  rw [Global.Specialization.BundleCycles.globalDeformationParameterSection_on_chart I U] at h
  exact h.trans (closedSupportDeformationParameterSection (I.ideal U) (P.ideal U))

/-- The actual zero fiber of the closed support deformation inside the ambient cone. -/
def globalSupportSpecialFiber : Scheme :=
  pullback (Global.SupportDeformation.BundleCycles.globalSupportDeformationMap I P) (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap I)

def globalSupportSpecialFiberInclusion : globalSupportSpecialFiber I P ⟶ Global.SupportDeformation.BundleCycles.globalSupportDeformation I P :=
  pullback.fst _ _

def globalSupportSpecialFiberMap : globalSupportSpecialFiber I P ⟶ Global.SpecialFiber.BundleCycles.globalSpecialFiber I :=
  pullback.snd _ _

instance globalSupportSpecialFiberInclusion_isClosedImmersion :
    IsClosedImmersion (globalSupportSpecialFiberInclusion I P) :=
  inferInstanceAs (IsClosedImmersion
    (pullback.fst (Global.SupportDeformation.BundleCycles.globalSupportDeformationMap I P) (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap I)))

instance globalSupportSpecialFiberMap_isClosedImmersion :
    IsClosedImmersion (globalSupportSpecialFiberMap I P) :=
  inferInstanceAs (IsClosedImmersion
    (pullback.snd (Global.SupportDeformation.BundleCycles.globalSupportDeformationMap I P) (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap I)))

/-- The pullback cone contains exactly the vanishing locus of the support's parameter. -/
theorem globalSupportSpecialFiberInclusion_range :
    Set.range (globalSupportSpecialFiberInclusion I P) =
      ((Global.SupportDeformation.BundleCycles.globalSupportDeformation I P).basicOpen (globalSupportParameterSection I P) :
        Set (Global.SupportDeformation.BundleCycles.globalSupportDeformation I P))ᶜ := by
  have h := Scheme.image_preimage_eq_of_isPullback
    (IsPullback.of_hasPullback (Global.SupportDeformation.BundleCycles.globalSupportDeformationMap I P) (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap I)).flip Set.univ
  simp only [Set.preimage_univ, Set.image_univ] at h
  change Set.range (globalSupportSpecialFiberInclusion I P) =
    Global.SupportDeformation.BundleCycles.globalSupportDeformationMap I P ⁻¹' Set.range (Global.SpecialFiber.BundleCycles.globalSpecialFiberMap I) at h
  rw [Global.Specialization.BundleCycles.globalSpecialFiberMap_range I, Set.preimage_compl] at h
  have hb := Scheme.preimage_basicOpen_top (Global.SupportDeformation.BundleCycles.globalSupportDeformationMap I P)
    (Global.Specialization.BundleCycles.globalDeformationParameterSection I)
  exact h.trans (congrArg
    (fun U : (Global.SupportDeformation.BundleCycles.globalSupportDeformation I P).Opens => (U : Set (Global.SupportDeformation.BundleCycles.globalSupportDeformation I P))ᶜ) hb)

variable [IsIntegral P.subscheme]

theorem globalSupportParameterSection_ne_zero : globalSupportParameterSection I P ≠ 0 := by
  let x : P.subscheme := Classical.choice inferInstance
  obtain ⟨U, y, _⟩ := P.subschemeCover.openCover.exists_eq x
  have : Nonempty (Spec ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U))) := ⟨y⟩
  have : IsDomain ((CoefficientDiagram.BundleCycles.supportCoefficientDiagram P).obj (.op U)) := Integrality.BundleCycles.supportCoefficientRing_isDomain P U
  intro hz
  have h := congrArg ((Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).f U).appTop hz
  rw [globalSupportParameterSection_on_chart I P U] at h
  exact Affine.Specialization.BundleCycles.affineDeformationParameterSection_ne_zero (CoefficientDiagram.BundleCycles.supportCenterIdeal P I U)
    (h.trans (map_zero ((Global.SupportDeformation.BundleCycles.globalSupportDeformationCover I P).f U).appTop.hom))

variable [AlgebraicGeometry.IsNoetherian X]

/-- The finite divisor of t on the global integral closed-support deformation. -/
def globalSupportParameterDivisor : Global.SupportDeformation.BundleCycles.globalSupportDeformation I P →₀ ℤ :=
  RegularDivisor.BundleCycles.regularFunctionDivisor (Global.SupportDeformation.BundleCycles.globalSupportDeformation I P) (globalSupportParameterSection I P)

theorem globalSupportParameterDivisor_support :
    ((globalSupportParameterDivisor I P).support : Set (Global.SupportDeformation.BundleCycles.globalSupportDeformation I P)) ⊆
      Set.range (globalSupportSpecialFiberInclusion I P) := by
  rw [globalSupportSpecialFiberInclusion_range]
  exact RegularDivisor.BundleCycles.regularFunctionDivisor_support_subset _ _

def globalSupportFiberPointEmbedding : globalSupportSpecialFiber I P ↪ Global.SupportDeformation.BundleCycles.globalSupportDeformation I P :=
  ⟨globalSupportSpecialFiberInclusion I P, (globalSupportSpecialFiberInclusion I P).isClosedEmbedding.injective⟩

/-- The complete divisor of t transported onto its closed fiber. -/
def globalSupportFiberCycle : globalSupportSpecialFiber I P →₀ ℤ :=
  Finsupp.comapDomain (globalSupportFiberPointEmbedding I P) (globalSupportParameterDivisor I P)
    (globalSupportFiberPointEmbedding I P).injective.injOn

theorem globalSupportFiberCycle_push :
    Finsupp.embDomain (globalSupportFiberPointEmbedding I P) (globalSupportFiberCycle I P) =
      globalSupportParameterDivisor I P :=
  Finsupp.embDomain_comapDomain (globalSupportParameterDivisor_support I P)

def globalSupportConePointEmbedding : globalSupportSpecialFiber I P ↪ Global.SpecialFiber.BundleCycles.globalSpecialFiber I :=
  ⟨globalSupportSpecialFiberMap I P, (globalSupportSpecialFiberMap I P).isClosedEmbedding.injective⟩

/-- Specialization of an actual integral closed support as a finite cycle on the ambient cone. -/
def globalClosedSupportSpecialization : Global.SpecialFiber.BundleCycles.globalSpecialFiber I →₀ ℤ :=
  Finsupp.embDomain (globalSupportConePointEmbedding I P) (globalSupportFiberCycle I P)

theorem globalClosedSupportSpecialization_at_support (x : globalSupportSpecialFiber I P) :
    globalClosedSupportSpecialization I P (globalSupportSpecialFiberMap I P x) =
      globalSupportParameterDivisor I P (globalSupportSpecialFiberInclusion I P x) :=
  Finsupp.embDomain_apply_self _ _ _

theorem globalClosedSupportSpecialization_nonnegative (x : Global.SpecialFiber.BundleCycles.globalSpecialFiber I) :
    0 ≤ globalClosedSupportSpecialization I P x := by
  classical
  by_cases hx : x ∈ Set.range (globalSupportSpecialFiberMap I P)
  · obtain ⟨y, rfl⟩ := hx
    rw [globalClosedSupportSpecialization_at_support]
    exact RegularDivisor.BundleCycles.regularFunctionDivisor_nonnegative _ _ (globalSupportParameterSection_ne_zero I P) _
  · have hz : globalClosedSupportSpecialization I P x = 0 :=
      Finsupp.embDomain_of_notMem_range _ _ _ hx
    exact hz.symm ▸ le_refl 0

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Support.Specialization.BundleCycles
end ComponentSource_3

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Support.Specialization"

@[expose] public section ComponentSource_4
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Global.CycleSpecialization -/

/-! # Cycle Specialization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Global.CycleSpecialization.BundleCycles

noncomputable section

/-!
# LineBundleCycles: global specialization on finite rational cycles

Each point indexes its actual reduced integral closed subscheme. Its
specialization is the divisor of t on the constructed support deformation,
pushed into the global cone. Linear extension gives specialization of
finite rational cycles. Grading and rational-equivalence descent are
separate assertions and are not assumed here.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

universe u
variable {X : Scheme.{u}} (I : X.IdealSheafData)

instance specializationSupport_isIntegral (W : IrreducibleCloseds X) :
    IsIntegral (CycleClass.Geometric.GenericPoint.reducedSupportIdeal W).subscheme := CycleClass.Geometric.GenericPoint.reducedSupportScheme_isIntegral W

variable [AlgebraicGeometry.IsNoetherian X]

/-- The specialization cycle of an actual reduced integral closed support. -/
def globalIntegralSupportSpecialization (W : IrreducibleCloseds X) : SpecialFiber.BundleCycles.globalSpecialFiber I →₀ ℤ :=
  Support.Specialization.BundleCycles.globalClosedSupportSpecialization I (CycleClass.Geometric.GenericPoint.reducedSupportIdeal W)

/-- The specialization cycle indexed by the generic point of its integral support. -/
def globalPrimeSpecialization (x : X) : SpecialFiber.BundleCycles.globalSpecialFiber I →₀ ℤ :=
  globalIntegralSupportSpecialization I (irreducibleSetEquivPoints.symm x)

theorem globalPrimeSpecialization_genericPoint (W : IrreducibleCloseds X) :
    globalPrimeSpecialization I (irreducibleSetEquivPoints W) = globalIntegralSupportSpecialization I W := by
  unfold globalPrimeSpecialization
  exact congrArg (globalIntegralSupportSpecialization I) (irreducibleSetEquivPoints.symm_apply_apply W)

theorem globalPrimeSpecialization_nonnegative (x : X) (y : SpecialFiber.BundleCycles.globalSpecialFiber I) :
    0 ≤ globalPrimeSpecialization I x y :=
  Support.Specialization.BundleCycles.globalClosedSupportSpecialization_nonnegative I
    (CycleClass.Geometric.GenericPoint.reducedSupportIdeal (irreducibleSetEquivPoints.symm x)) y

/-- Rational coefficients on the same finite geometric specialization cycle. -/
def globalPrimeSpecializationQ (x : X) : SpecialFiber.BundleCycles.globalSpecialFiber I →₀ ℚ :=
  (globalPrimeSpecialization I x).mapRange (fun n : ℤ => (n : ℚ)) Int.cast_zero

/-- Global specialization of finite rational cycles, before passage to Chow groups. -/
def globalCycleSpecialization : (X →₀ ℚ) →ₗ[ℚ] (SpecialFiber.BundleCycles.globalSpecialFiber I →₀ ℚ) :=
  Finsupp.linearCombination ℚ (globalPrimeSpecializationQ I)

@[simp]
theorem globalCycleSpecialization_single (x : X) (q : ℚ) :
    globalCycleSpecialization I (Finsupp.single x q) = q • globalPrimeSpecializationQ I x :=
  Finsupp.linearCombination_single ℚ q x

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Global.CycleSpecialization.BundleCycles
end ComponentSource_4

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Global.CycleSpecialization"

@[expose] public section ComponentSource_5
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.GlobalSpecializationGrading -/

/-! # Global Specialization Grading -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.GlobalSpecializationGrading.BundleCycles

noncomputable section

section

/-!
# LineBundleCycles: global specialization preserves support dimension

The divisor of the nonzero parameter lies in codimension one on the
integral support deformation. The dimension increase of that deformation
and dimension preservation under its two actual closed-fiber embeddings
show that every nonzero global specialization coefficient has the original
support dimension.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.CategoryTheory.Limits _root_.TopologicalSpace _root_.Order

variable {X : Scheme} (I P : X.IdealSheafData)

/-- Both maps from the support fiber induce the same actual morphism to the base. -/
theorem globalSupportSpecialFiber_toBase :
    Support.Specialization.BundleCycles.globalSupportSpecialFiberInclusion I P ≫
        (Support.Projection.BundleCycles.globalSupportDeformationToSupport I P ≫ P.subschemeι) =
      Support.Specialization.BundleCycles.globalSupportSpecialFiberMap I P ≫ Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection I := by
  have hl : Support.Projection.BundleCycles.globalSupportDeformationToSupport I P ≫ P.subschemeι =
      Global.SupportDeformation.BundleCycles.globalSupportDeformationMap I P ≫ Global.Deformation.BundleCycles.globalDeformationProjection I :=
    (Support.Projection.BundleCycles.globalSupportDeformationToSupport_toBase I P).trans (Global.SupportDeformation.BundleCycles.globalSupportDeformationMap_toBase I P).symm
  have hp : Support.Specialization.BundleCycles.globalSupportSpecialFiberInclusion I P ≫ Global.SupportDeformation.BundleCycles.globalSupportDeformationMap I P =
      Support.Specialization.BundleCycles.globalSupportSpecialFiberMap I P ≫ Global.SpecialFiber.BundleCycles.globalSpecialFiberMap I := pullback.condition
  rw [hl, ← Category.assoc, hp, Category.assoc, Global.SpecialFiber.BundleCycles.globalSpecialFiberMap_toBase]

variable [AlgebraicGeometry.IsNoetherian X] [IsIntegral P.subscheme]

/-- A nonzero parameter-divisor coefficient has exactly the original support dimension. -/
theorem globalSupportParameterDivisor_dimension
    (f : P.subscheme ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (x : Global.SupportDeformation.BundleCycles.globalSupportDeformation I P) (hx : Support.Specialization.BundleCycles.globalSupportParameterDivisor I P x ≠ 0) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x)
        (Support.Projection.BundleCycles.globalSupportDeformationToSupport I P ≫ f) = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f := by
  have hc : coheight x = 1 := by
    by_contra h
    apply hx
    exact Scheme.ord_eq_zero_of_coheight_neq_one h _
  have hg : LocallyOfFiniteType (Support.Projection.BundleCycles.globalSupportDeformationToSupport I P) :=
    Global.DeformationFiniteType.BundleCycles.globalSupportDeformationToSupport_locallyOfFiniteType I P
  have hd := DivisorClass.Chern.SupportCodimension.Construction.pointClosure_dimension_add_one
    (Support.Projection.BundleCycles.globalSupportDeformationToSupport I P ≫ f) x hc
  have he := Deformation.Dimension.BundleCycles.globalSupportDeformation_dimension I P f
  omega

/-- Every nonzero coefficient on the global cone retains the integral support's dimension. -/
theorem globalClosedSupportSpecialization_dimension
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (x : Global.SpecialFiber.BundleCycles.globalSpecialFiber I) (hx : Support.Specialization.BundleCycles.globalClosedSupportSpecialization I P x ≠ 0) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x)
        (Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection I ≫ f) = Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (P.subschemeι ≫ f) := by
  have hr : x ∈ Set.range (Support.Specialization.BundleCycles.globalSupportSpecialFiberMap I P) := by
    by_contra h
    exact hx (Finsupp.embDomain_of_notMem_range _ _ _ h)
  obtain ⟨y, rfl⟩ := hr
  have hy : Support.Specialization.BundleCycles.globalSupportParameterDivisor I P (Support.Specialization.BundleCycles.globalSupportSpecialFiberInclusion I P y) ≠ 0 :=
    fun h => hx ((Support.Specialization.BundleCycles.globalClosedSupportSpecialization_at_support I P y).trans h)
  have hd := globalSupportParameterDivisor_dimension I P (P.subschemeι ≫ f)
    (Support.Specialization.BundleCycles.globalSupportSpecialFiberInclusion I P y) hy
  have ha := Point.SupportDimension.BundleCycles.pointClosure_dimension_closedImmersion (Support.Specialization.BundleCycles.globalSupportSpecialFiberInclusion I P)
    (Support.Projection.BundleCycles.globalSupportDeformationToSupport I P ≫ (P.subschemeι ≫ f)) y
  have hb := Point.SupportDimension.BundleCycles.pointClosure_dimension_closedImmersion (Support.Specialization.BundleCycles.globalSupportSpecialFiberMap I P)
    (Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection I ≫ f) y
  have hs : Support.Specialization.BundleCycles.globalSupportSpecialFiberInclusion I P ≫
      (Support.Projection.BundleCycles.globalSupportDeformationToSupport I P ≫ (P.subschemeι ≫ f)) =
      Support.Specialization.BundleCycles.globalSupportSpecialFiberMap I P ≫ (Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection I ≫ f) := by
    rw [← Category.assoc (Support.Projection.BundleCycles.globalSupportDeformationToSupport I P), ← Category.assoc,
      globalSupportSpecialFiber_toBase, Category.assoc]
  exact hb.trans ((congrArg
    (fun g => Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm y) g) hs.symm).trans
    (ha.symm.trans hd))

omit [IsIntegral P.subscheme] in
/-- The global prime specialization preserves the dimension of the actual reduced point closure. -/
theorem globalPrimeSpecialization_dimension
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (x : X) (y : Global.SpecialFiber.BundleCycles.globalSpecialFiber I) (hy : Global.CycleSpecialization.BundleCycles.globalPrimeSpecialization I x y ≠ 0) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm y)
        (Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection I ≫ f) =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f :=
  globalClosedSupportSpecialization_dimension I
    (CycleClass.Geometric.GenericPoint.reducedSupportIdeal (irreducibleSetEquivPoints.symm x)) f y hy

omit [IsIntegral P.subscheme] in
theorem globalPrimeSpecializationQ_dimension
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (x : X) (y : Global.SpecialFiber.BundleCycles.globalSpecialFiber I) (hy : Global.CycleSpecialization.BundleCycles.globalPrimeSpecializationQ I x y ≠ 0) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm y)
        (Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection I ≫ f) =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f := by
  apply globalPrimeSpecialization_dimension I f x y
  intro h
  apply hy
  change (Global.CycleSpecialization.BundleCycles.globalPrimeSpecialization I x y : ℚ) = 0
  exact (congrArg (fun z : ℤ => (z : ℚ)) h).trans Int.cast_zero

end

/-! Nonzero specialization coefficients lie over specializations of
the original generic support point in the ambient scheme. -/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X : Scheme.{0}} [AlgebraicGeometry.IsNoetherian X] (I : X.IdealSheafData)

theorem globalClosedSupportSpecialization_support_base (P : X.IdealSheafData) [IsIntegral P.subscheme]
    (y : Global.SpecialFiber.BundleCycles.globalSpecialFiber I) (hy : Support.Specialization.BundleCycles.globalClosedSupportSpecialization I P y ≠ 0) :
    Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection I y ∈ Set.range P.subschemeι := by
  have hr : y ∈ Set.range (Support.Specialization.BundleCycles.globalSupportSpecialFiberMap I P) := by
    by_contra hn
    exact hy (Finsupp.embDomain_of_notMem_range _ _ _ hn)
  obtain ⟨v, rfl⟩ := hr
  refine ⟨Support.Projection.BundleCycles.globalSupportDeformationToSupport I P (Support.Specialization.BundleCycles.globalSupportSpecialFiberInclusion I P v), ?_⟩
  exact congrArg (fun a : Support.Specialization.BundleCycles.globalSupportSpecialFiber I P ⟶ X => a v) (globalSupportSpecialFiber_toBase I P)

theorem globalPrimeSpecialization_specializes (x : X) (y : Global.SpecialFiber.BundleCycles.globalSpecialFiber I)
    (hy : Global.CycleSpecialization.BundleCycles.globalPrimeSpecialization I x y ≠ 0) : x ⤳ Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection I y := by
  have H := globalClosedSupportSpecialization_support_base I
    (CycleClass.Geometric.GenericPoint.reducedSupportIdeal (irreducibleSetEquivPoints.symm x)) y hy
  change Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection I y ∈ Set.range (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x)) at H
  rw [CycleClass.Geometric.GenericPoint.range_reducedSupportι] at H
  exact specializes_iff_mem_closure.mpr H

theorem globalPrimeSpecializationQ_specializes (x : X) (y : Global.SpecialFiber.BundleCycles.globalSpecialFiber I)
    (hy : Global.CycleSpecialization.BundleCycles.globalPrimeSpecializationQ I x y ≠ 0) : x ⤳ Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection I y := by
  apply globalPrimeSpecialization_specializes I x y
  intro hz
  apply hy
  change (Global.CycleSpecialization.BundleCycles.globalPrimeSpecialization I x y : ℚ) = 0
  rw [hz, Int.cast_zero]

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.GlobalSpecializationGrading.BundleCycles
end ComponentSource_5

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.GlobalSpecializationGrading"

@[expose] public section ComponentSource_6
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.GlobalSpecialization -/

/-! # Global Specialization -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.GlobalSpecialization.BundleCycles

noncomputable section

section

/-!
# LineBundleCycles: specialization on genuine dimension-graded global cycles

The proved support-dimension theorem puts every coefficient of the global
specialization into the required grade. The resulting linear map recovers
the complete ungraded specialization when the grading is forgotten.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X : Scheme}

/-- Scheme points whose actual reduced closures have the prescribed dimension. -/
def SchemeDimensionCyclePoint (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (d : ℕ) :=
  {x : X // Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f = d}

def schemeDimensionPointEmbedding (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (d : ℕ) :
    SchemeDimensionCyclePoint f d ↪ X := ⟨Subtype.val, Subtype.val_injective⟩

/-- Forget the grading of a finite rational cycle without altering its coefficients. -/
def schemeDimensionCycleInclusion (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (d : ℕ) :
    (SchemeDimensionCyclePoint f d →₀ ℚ) →ₗ[ℚ] (X →₀ ℚ) :=
  Finsupp.lmapDomain ℚ ℚ (schemeDimensionPointEmbedding f d)

variable [AlgebraicGeometry.IsNoetherian X] (I : X.IdealSheafData)
    (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)

/-- The actual global prime specialization, regarded in its proved dimension grade. -/
def globalGradedPrimeSpecialization (d : ℕ) (x : SchemeDimensionCyclePoint f d) :
    SchemeDimensionCyclePoint (Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection I ≫ f) d →₀ ℚ :=
  Finsupp.comapDomain (schemeDimensionPointEmbedding (Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection I ≫ f) d)
    (Global.CycleSpecialization.BundleCycles.globalPrimeSpecializationQ I x.1)
    (schemeDimensionPointEmbedding (Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection I ≫ f) d).injective.injOn

/-- The grading retains every nonzero specialization coefficient. -/
theorem globalGradedPrimeSpecialization_push [LocallyOfFiniteType f]
    (d : ℕ) (x : SchemeDimensionCyclePoint f d) :
    schemeDimensionCycleInclusion (Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection I ≫ f) d
        (globalGradedPrimeSpecialization I f d x) = Global.CycleSpecialization.BundleCycles.globalPrimeSpecializationQ I x.1 := by
  have hs : ((Global.CycleSpecialization.BundleCycles.globalPrimeSpecializationQ I x.1).support : Set (Global.SpecialFiber.BundleCycles.globalSpecialFiber I)) ⊆
      Set.range (schemeDimensionPointEmbedding (Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection I ≫ f) d) := by
    intro y hy
    refine ⟨⟨y, ?_⟩, rfl⟩
    exact (GlobalSpecializationGrading.BundleCycles.globalPrimeSpecializationQ_dimension I f x.1 y (Finsupp.mem_support_iff.mp hy)).trans x.2
  exact (Finsupp.embDomain_eq_mapDomain
    (schemeDimensionPointEmbedding (Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection I ≫ f) d)
    (globalGradedPrimeSpecialization I f d x)).symm.trans (Finsupp.embDomain_comapDomain hs)

/-- Global specialization as a linear map on finite cycles of a fixed dimension. -/
def globalGradedCycleSpecialization (d : ℕ) :
    (SchemeDimensionCyclePoint f d →₀ ℚ) →ₗ[ℚ]
      (SchemeDimensionCyclePoint (Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection I ≫ f) d →₀ ℚ) :=
  Finsupp.linearCombination ℚ (globalGradedPrimeSpecialization I f d)

@[simp]
theorem globalGradedCycleSpecialization_single (d : ℕ) (x : SchemeDimensionCyclePoint f d) (q : ℚ) :
    globalGradedCycleSpecialization I f d (Finsupp.single x q) =
      q • globalGradedPrimeSpecialization I f d x :=
  Finsupp.linearCombination_single ℚ q x

/-- Forgetting the dimension grading commutes with specialization on every finite rational cycle. -/
theorem globalGradedCycleSpecialization_push [LocallyOfFiniteType f] (d : ℕ) :
    (schemeDimensionCycleInclusion (Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection I ≫ f) d).comp
        (globalGradedCycleSpecialization I f d) =
      (Global.CycleSpecialization.BundleCycles.globalCycleSpecialization I).comp (schemeDimensionCycleInclusion f d) :=
  (Finsupp.lmapDomain_linearCombination ℚ (schemeDimensionPointEmbedding f d)
    (schemeDimensionCycleInclusion (Global.SpecialFiber.BundleCycles.globalSpecialFiberProjection I ≫ f) d)
    (globalGradedPrimeSpecialization_push I f d)).symm

end

/-!
# LineBundleCycles: graded principal divisors on general finite-type schemes

The deformation and its cone need not be smooth or projective. Their
rational-equivalence relations use the same local-ring orders on actual
reduced integral supports. The dimension proof ensures that grading a
principal divisor discards no coefficient.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace _root_.Order

variable {X : Scheme} [AlgebraicGeometry.IsNoetherian X]

/-- The complete principal divisor pushed from an actual integral support. -/
def schemePrincipalPointDivisor (W : IrreducibleCloseds X)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) : X →₀ ℚ :=
  Finsupp.embDomain ⟨CycleClass.Geometric.GenericPoint.reducedSupportι W, (CycleClass.Geometric.GenericPoint.reducedSupportι W).isClosedEmbedding.injective⟩
    ((Ord.BundleCycles.principalDivisor (CycleClass.Geometric.GenericPoint.reducedSupportScheme W) g).mapRange (fun n : ℤ => (n : ℚ)) Int.cast_zero)

@[simp]
theorem schemePrincipalPointDivisor_at_support (W : IrreducibleCloseds X)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) (x : CycleClass.Geometric.GenericPoint.reducedSupportScheme W) :
    schemePrincipalPointDivisor W g (CycleClass.Geometric.GenericPoint.reducedSupportι W x) =
      ((CycleClass.Geometric.GenericPoint.reducedSupportScheme W).ord g x : ℚ) := Finsupp.embDomain_apply_self _ _ _

/-- Every nonzero principal-divisor coefficient has support dimension one lower. -/
theorem schemePrincipalPointDivisor_dimension (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) [LocallyOfFiniteType f]
    (W : IrreducibleCloseds X) (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField)
    (x : X) (hx : schemePrincipalPointDivisor W g x ≠ 0) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f + 1 =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f := by
  have hr : x ∈ Set.range (CycleClass.Geometric.GenericPoint.reducedSupportι W) := by
    by_contra h
    exact hx (Finsupp.embDomain_of_notMem_range _ _ _ h)
  obtain ⟨y, rfl⟩ := hr
  have hy : coheight y = 1 := by
    by_contra h
    apply hx
    exact (schemePrincipalPointDivisor_at_support W g y).trans
      ((congrArg (fun n : ℤ => (n : ℚ)) (Scheme.ord_eq_zero_of_coheight_neq_one h g)).trans Int.cast_zero)
  have hd := DivisorClass.Chern.SupportCodimension.Construction.pointClosure_dimension_add_one (CycleClass.Geometric.SupportFiniteType.supportStructureMap W f) y hy
  exact (congrArg (fun n => n + 1)
    (Point.SupportDimension.BundleCycles.pointClosure_dimension_closedImmersion (CycleClass.Geometric.GenericPoint.reducedSupportι W) f y)).trans hd

variable (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)

/-- The finite principal divisor indexed in the requested dimension grade. -/
def schemeGradedPrincipalDivisor (d : ℕ) (W : IrreducibleCloseds X)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) : SchemeDimensionCyclePoint f d →₀ ℚ :=
  Finsupp.comapDomain (schemeDimensionPointEmbedding f d) (schemePrincipalPointDivisor W g)
    (schemeDimensionPointEmbedding f d).injective.injOn

/-- With the actual support dimension, grading retains the full principal divisor. -/
theorem schemeGradedPrincipalDivisor_push [LocallyOfFiniteType f] (d : ℕ)
    (W : IrreducibleCloseds X) (hW : Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f = d + 1)
    (g : (CycleClass.Geometric.GenericPoint.reducedSupportScheme W).functionField) :
    schemeDimensionCycleInclusion f d (schemeGradedPrincipalDivisor f d W g) =
      schemePrincipalPointDivisor W g := by
  have hs : ((schemePrincipalPointDivisor W g).support : Set X) ⊆
      Set.range (schemeDimensionPointEmbedding f d) := by
    intro x hx
    refine ⟨⟨x, ?_⟩, rfl⟩
    have hd := schemePrincipalPointDivisor_dimension f W g x (Finsupp.mem_support_iff.mp hx)
    omega
  exact (Finsupp.embDomain_eq_mapDomain (schemeDimensionPointEmbedding f d)
    (schemeGradedPrincipalDivisor f d W g)).symm.trans (Finsupp.embDomain_comapDomain hs)

omit [AlgebraicGeometry.IsNoetherian X] in
/-- Forgetting the grade is injective on finite cycles. -/
theorem schemeDimensionCycleInclusion_injective (d : ℕ) :
    Function.Injective (schemeDimensionCycleInclusion f d) :=
  Finsupp.mapDomain_injective (schemeDimensionPointEmbedding f d).injective

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.GlobalSpecialization.BundleCycles
end ComponentSource_6

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Graded.GlobalSpecialization"

@[expose] public section ComponentSource_7
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.SingularLocus -/

/-! # Singular Locus -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.SingularLocus

noncomputable section

/-!
# Algebraic singular loci of cycle supports

This file uses the actual smooth locus of a morphism of schemes. Over a perfect
field, a reduced finite-presentation scheme is generically smooth. Consequently
its nonsmooth locus is closed with empty interior; in the integral case all its
points have positive intrinsic codimension.

These are algebraic inputs to a future fundamental-class construction. They do
not identify a complex analytic singular locus, assert a triangulation, or
postulate a fundamental class.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

universe u

variable {X Y : Scheme.{u}}

/-- The nonsmooth locus, defined from the formal smoothness of actual stalk maps. -/
def singularLocus (f : X ⟶ Y) [LocallyOfFinitePresentation f] : Set X :=
  (f.smoothLocus : Set X)ᶜ

@[simp]
theorem mem_singularLocus_iff (f : X ⟶ Y) [LocallyOfFinitePresentation f] (x : X) :
    x ∈ singularLocus f ↔ ¬ (f.stalkMap x).hom.FormallySmooth := Iff.rfl

theorem isClosed_singularLocus (f : X ⟶ Y) [LocallyOfFinitePresentation f] :
    IsClosed (singularLocus f) := f.smoothLocus.isOpen.isClosed_compl

@[simp]
theorem singularLocus_eq_empty_of_smooth (f : X ⟶ Y) [Smooth f] :
    singularLocus f = ∅ := by
  simp only [singularLocus, f.smoothLocus_eq_top, Opens.coe_top, Set.compl_univ]

variable {K : Type u} [Field K] [PerfectField K]

/-- Generic smoothness makes the singular locus nowhere dense as a closed set. -/
theorem interior_singularLocus_eq_empty [IsReduced X]
    (f : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation f] :
    interior (singularLocus f) = ∅ :=
  f.dense_smoothLocus_of_perfectField.interior_compl

theorem interior_closure_singularLocus_eq_empty [IsReduced X]
    (f : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation f] :
    interior (closure (singularLocus f)) = ∅ := by
  rw [(isClosed_singularLocus f).closure_eq, interior_singularLocus_eq_empty]

theorem genericPoint_not_mem_singularLocus [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation f] :
    genericPoint X ∉ singularLocus f := by
  intro hsing
  change ¬ (f.stalkMap (genericPoint X)).hom.FormallySmooth at hsing
  have hsm := f.genericPoint_mem_smoothLocus_of_perfectField
  change (f.stalkMap (genericPoint X)).hom.FormallySmooth at hsm
  exact hsing hsm

/-- A nonsmooth point on an integral finite-presentation scheme over a perfect
field has positive codimension in that scheme. -/
theorem coheight_pos_of_mem_singularLocus [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation f]
    (x : X) (hx : x ∈ singularLocus f) : 0 < Order.coheight x := by
  apply Order.coheight_pos.mpr
  intro hmax
  have hgen : genericPoint X ⤳ x := genericPoint_specializes x
  have hback : x ⤳ genericPoint X := hmax hgen
  have heq : x = genericPoint X := (hback.antisymm hgen).eq
  apply genericPoint_not_mem_singularLocus f
  simpa only [heq] using hx

/-- The reduced integral closed subscheme attached to an irreducible cycle
support has a dense smooth locus whenever its structure morphism is of finite
presentation locally. -/
theorem reducedSupport_dense_smoothLocus (Z : IrreducibleCloseds X)
    (f : GenericPoint.reducedSupportScheme Z ⟶ Spec (.of K)) [LocallyOfFinitePresentation f] :
    Dense (f.smoothLocus : Set (GenericPoint.reducedSupportScheme Z)) :=
  f.dense_smoothLocus_of_perfectField

/-- In particular the singular part of an actual cycle support has positive
intrinsic codimension at every point. -/
theorem reducedSupport_singular_coheight_pos (Z : IrreducibleCloseds X)
    (f : GenericPoint.reducedSupportScheme Z ⟶ Spec (.of K)) [LocallyOfFinitePresentation f]
    (x : GenericPoint.reducedSupportScheme Z) (hx : x ∈ singularLocus f) :
    0 < Order.coheight x :=
  coheight_pos_of_mem_singularLocus f x hx

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.SingularLocus
end ComponentSource_7

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.SingularLocus"

@[expose] public section ComponentSource_8
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.SingularCodimension -/

/-! # Singular Codimension -/

namespace OAI.AlgebraicGeometry

noncomputable section

/-!
# Ambient codimension of singular points on cycle supports

The generic point of a codimension-p integral support has ambient coheight p.
Every other point is a strict specialization, so its ambient coheight is at
least p+1. Generic smoothness over a perfect field therefore gives this bound
for the singular locus of the actual support structure morphism.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

universe u

variable {X : Scheme.{u}}

/-- Every nongeneric point of a codimension-p support has ambient codimension
at least p+1. This uses specialization, not a dimension subtraction formula. -/
theorem CycleClass.Geometric.SingularCodimension.reducedSupport_ambient_coheight_of_ne_generic (p : ℕ)
    (Z : Foundations.Scheme.CycleSupports.IrreducibleCycleSupport X p) (x : CycleClass.Geometric.GenericPoint.reducedSupportScheme Z.1)
    (hx : x ≠ genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z.1)) :
    ((p + 1 : ℕ) : ℕ∞) ≤ Order.coheight ((CycleClass.Geometric.GenericPoint.reducedSupportι Z.1) x) := by
  have hforward :
      (CycleClass.Geometric.GenericPoint.reducedSupportι Z.1) (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z.1)) ⤳
        (CycleClass.Geometric.GenericPoint.reducedSupportι Z.1) x :=
    (genericPoint_specializes x).map (CycleClass.Geometric.GenericPoint.reducedSupportι Z.1).continuous
  have hlt : (CycleClass.Geometric.GenericPoint.reducedSupportι Z.1) x <
      (CycleClass.Geometric.GenericPoint.reducedSupportι Z.1) (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z.1)) := by
    rw [lt_iff_le_not_ge]
    refine ⟨Scheme.le_iff_specializes.mpr hforward, ?_⟩
    intro hback
    have hreverse := Scheme.le_iff_specializes.mp hback
    have heq : (CycleClass.Geometric.GenericPoint.reducedSupportι Z.1) x =
        (CycleClass.Geometric.GenericPoint.reducedSupportι Z.1) (genericPoint (CycleClass.Geometric.GenericPoint.reducedSupportScheme Z.1)) :=
      (hreverse.antisymm hforward).eq
    exact hx ((CycleClass.Geometric.GenericPoint.reducedSupportι Z.1).isClosedEmbedding.injective heq)
  have hbound := Order.coheight_add_one_le hlt
  rw [CycleClass.Geometric.GenericPoint.reducedSupport_genericPoint_codimension p Z] at hbound
  simpa only [Nat.cast_add, Nat.cast_one] using hbound

variable {K : Type u} [Field K] [PerfectField K]

/-- A singular point of an integral codimension-p support over a perfect field
has ambient codimension at least p+1. -/
theorem CycleClass.Geometric.SingularCodimension.reducedSupport_singular_ambient_coheight (p : ℕ)
    (Z : Foundations.Scheme.CycleSupports.IrreducibleCycleSupport X p)
    (f : CycleClass.Geometric.GenericPoint.reducedSupportScheme Z.1 ⟶ Spec (.of K)) [LocallyOfFinitePresentation f]
    (x : CycleClass.Geometric.GenericPoint.reducedSupportScheme Z.1) (hx : x ∈ CycleClass.Geometric.SingularLocus.singularLocus f) :
    ((p + 1 : ℕ) : ℕ∞) ≤ Order.coheight ((CycleClass.Geometric.GenericPoint.reducedSupportι Z.1) x) := by
  apply CycleClass.Geometric.SingularCodimension.reducedSupport_ambient_coheight_of_ne_generic p Z x
  intro heq
  apply CycleClass.Geometric.SingularLocus.genericPoint_not_mem_singularLocus f
  simpa only [heq] using hx

/-- The singular-codimension bound applies to the actual induced structure
map, whose local finite presentation follows from finite type over the field. -/
theorem CycleClass.Geometric.SingularCodimension.supportStructureMap_singular_ambient_coheight (p : ℕ)
    (Z : Foundations.Scheme.CycleSupports.IrreducibleCycleSupport X p) (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] (x : CycleClass.Geometric.GenericPoint.reducedSupportScheme Z.1)
    (hx : x ∈ CycleClass.Geometric.SingularLocus.singularLocus (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z.1 f)) :
    ((p + 1 : ℕ) : ℕ∞) ≤ Order.coheight ((CycleClass.Geometric.GenericPoint.reducedSupportι Z.1) x) :=
  CycleClass.Geometric.SingularCodimension.reducedSupport_singular_ambient_coheight p Z (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z.1 f) x hx

/-- In particular this controls the singular part of every actual cycle
support in a smooth projective complex presentation. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.cycleSupport_singular_ambient_coheight
    (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (Z : Foundations.Scheme.CycleSupports.IrreducibleCycleSupport P.carrier p) (x : CycleClass.Geometric.GenericPoint.reducedSupportScheme Z.1)
    (hx : x ∈ CycleClass.Geometric.SingularLocus.singularLocus (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z.1 P.structureMap)) :
    ((p + 1 : ℕ) : ℕ∞) ≤ Order.coheight ((CycleClass.Geometric.GenericPoint.reducedSupportι Z.1) x) :=
  CycleClass.Geometric.SingularCodimension.supportStructureMap_singular_ambient_coheight p Z P.structureMap x hx

end

end OAI.AlgebraicGeometry
end ComponentSource_8

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.SingularCodimension"

@[expose] public section ComponentSource_9
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.SmoothStratum -/

/-! # Smooth Stratum -/

namespace OAI.AlgebraicGeometry

noncomputable section

/-!
# The actual smooth stratum of an algebraic cycle support

The smooth stratum is the open subscheme cut out by the smooth locus of the
actual structure morphism. Its smoothness is proved from restriction of the
smooth locus. For an integral cycle support over a perfect field it is dense,
and its complement has strictly larger ambient codimension.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

universe u

variable {X Y : Scheme.{u}}

/-- The open subscheme consisting of smooth points of an actual morphism. -/
def CycleClass.Geometric.SmoothStratum.smoothStratum (f : X ⟶ Y) [LocallyOfFinitePresentation f] : Scheme.{u} :=
  f.smoothLocus.toScheme

/-- The actual open immersion from the smooth stratum to its source scheme. -/
def CycleClass.Geometric.SmoothStratum.smoothStratumι (f : X ⟶ Y) [LocallyOfFinitePresentation f] :
    CycleClass.Geometric.SmoothStratum.smoothStratum f ⟶ X :=
  f.smoothLocus.ι

/-- The restriction of the structure morphism to its smooth stratum. -/
def CycleClass.Geometric.SmoothStratum.smoothStratumToBase (f : X ⟶ Y) [LocallyOfFinitePresentation f] :
    CycleClass.Geometric.SmoothStratum.smoothStratum f ⟶ Y :=
  CycleClass.Geometric.SmoothStratum.smoothStratumι f ≫ f

instance CycleClass.Geometric.SmoothStratum.smoothStratumι_isOpenImmersion (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] : IsOpenImmersion (CycleClass.Geometric.SmoothStratum.smoothStratumι f) :=
  inferInstanceAs (IsOpenImmersion f.smoothLocus.ι)

/-- Smoothness is proved, not included as an assumed field of a stratum. -/
instance CycleClass.Geometric.SmoothStratum.smoothStratumToBase_isSmooth (f : X ⟶ Y)
    [LocallyOfFinitePresentation f] : Smooth (CycleClass.Geometric.SmoothStratum.smoothStratumToBase f) := by
  change Smooth (f.smoothLocus.ι ≫ f)
  apply Scheme.Hom.smoothLocus_eq_top_iff.mp
  rw [← Scheme.Hom.preimage_smoothLocus_eq]
  exact Scheme.Opens.ι_preimage_self _

@[simp]
theorem CycleClass.Geometric.SmoothStratum.range_smoothStratumι (f : X ⟶ Y) [LocallyOfFinitePresentation f] :
    Set.range (CycleClass.Geometric.SmoothStratum.smoothStratumι f) = (f.smoothLocus : Set X) :=
  Scheme.Opens.range_ι _

/-- The omitted points are exactly the previously defined singular locus. -/
theorem CycleClass.Geometric.SmoothStratum.smoothStratum_complement (f : X ⟶ Y) [LocallyOfFinitePresentation f] :
    (Set.range (CycleClass.Geometric.SmoothStratum.smoothStratumι f))ᶜ = CycleClass.Geometric.SingularLocus.singularLocus f := by
  rw [CycleClass.Geometric.SmoothStratum.range_smoothStratumι]
  rfl

/-- The smooth open stratum of a reduced support is a locally closed subscheme
of the original ambient scheme. -/
def CycleClass.Geometric.SmoothStratum.reducedSupportSmoothStratumι (Z : IrreducibleCloseds X)
    (f : CycleClass.Geometric.GenericPoint.reducedSupportScheme Z ⟶ Y) [LocallyOfFinitePresentation f] :
    CycleClass.Geometric.SmoothStratum.smoothStratum f ⟶ X :=
  CycleClass.Geometric.SmoothStratum.smoothStratumι f ≫ CycleClass.Geometric.GenericPoint.reducedSupportι Z

instance CycleClass.Geometric.SmoothStratum.reducedSupportSmoothStratumι_isImmersion (Z : IrreducibleCloseds X)
    (f : CycleClass.Geometric.GenericPoint.reducedSupportScheme Z ⟶ Y) [LocallyOfFinitePresentation f] :
    IsImmersion (CycleClass.Geometric.SmoothStratum.reducedSupportSmoothStratumι Z f) := by
  unfold CycleClass.Geometric.SmoothStratum.reducedSupportSmoothStratumι
  infer_instance

variable {K : Type u} [Field K] [PerfectField K]

/-- Generic smoothness gives a dense range in every reduced source over a
perfect field. -/
theorem CycleClass.Geometric.SmoothStratum.smoothStratum_denseRange [IsReduced X]
    (f : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation f] :
    DenseRange (CycleClass.Geometric.SmoothStratum.smoothStratumι f) := by
  change Dense (Set.range (CycleClass.Geometric.SmoothStratum.smoothStratumι f))
  rw [CycleClass.Geometric.SmoothStratum.range_smoothStratumι]
  exact f.dense_smoothLocus_of_perfectField

instance CycleClass.Geometric.SmoothStratum.smoothStratum_nonempty [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation f] :
    Nonempty (CycleClass.Geometric.SmoothStratum.smoothStratum f) :=
  (CycleClass.Geometric.SmoothStratum.smoothStratum_denseRange f).nonempty

instance CycleClass.Geometric.SmoothStratum.smoothStratum_isIntegral [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [LocallyOfFinitePresentation f] :
    IsIntegral (CycleClass.Geometric.SmoothStratum.smoothStratum f) :=
  AlgebraicGeometry.isIntegral_of_isOpenImmersion (CycleClass.Geometric.SmoothStratum.smoothStratumι f)

/-- The closure of the smooth stratum in the ambient scheme is exactly the
irreducible cycle support from which it was constructed. -/
theorem CycleClass.Geometric.SmoothStratum.reducedSupportSmoothStratum_closure_range (Z : IrreducibleCloseds X)
    (f : CycleClass.Geometric.GenericPoint.reducedSupportScheme Z ⟶ Spec (.of K)) [LocallyOfFinitePresentation f] :
    closure (Set.range (CycleClass.Geometric.SmoothStratum.reducedSupportSmoothStratumι Z f)) = (Z : Set X) := by
  change closure (Set.range ((CycleClass.Geometric.GenericPoint.reducedSupportι Z) ∘ (CycleClass.Geometric.SmoothStratum.smoothStratumι f))) = (Z : Set X)
  rw [Set.range_comp, (CycleClass.Geometric.GenericPoint.reducedSupportι Z).isClosedEmbedding.closure_image_eq,
    (CycleClass.Geometric.SmoothStratum.smoothStratum_denseRange f).closure_range, Set.image_univ, CycleClass.Geometric.GenericPoint.range_reducedSupportι]

/-- A point of the support omitted by its actual smooth stratum has ambient
codimension at least p+1. -/
theorem CycleClass.Geometric.SmoothStratum.reducedSupportSmoothStratum_complement_coheight (p : ℕ)
    (Z : Foundations.Scheme.CycleSupports.IrreducibleCycleSupport X p)
    (f : CycleClass.Geometric.GenericPoint.reducedSupportScheme Z.1 ⟶ Spec (.of K)) [LocallyOfFinitePresentation f]
    (y : X) (hy : y ∈ (Z.1 : Set X))
    (homit : y ∉ Set.range (CycleClass.Geometric.SmoothStratum.reducedSupportSmoothStratumι Z.1 f)) :
    ((p + 1 : ℕ) : ℕ∞) ≤ Order.coheight y := by
  have hyrange : y ∈ Set.range (CycleClass.Geometric.GenericPoint.reducedSupportι Z.1) := by
    simpa only [CycleClass.Geometric.GenericPoint.range_reducedSupportι] using hy
  obtain ⟨x, rfl⟩ := hyrange
  apply CycleClass.Geometric.SingularCodimension.reducedSupport_singular_ambient_coheight p Z f x
  change x ∉ f.smoothLocus
  intro hx
  apply homit
  exact ⟨⟨x, hx⟩, rfl⟩

/-- The smooth stratum of an actual cycle support in the given complex variety. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.cycleSupportSmoothStratum (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (Z : Foundations.Scheme.CycleSupports.IrreducibleCycleSupport P.carrier p) : Scheme :=
  CycleClass.Geometric.SmoothStratum.smoothStratum (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z.1 P.structureMap)

/-- Its actual complex structure morphism. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.cycleSupportSmoothStratumToBase (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (Z : Foundations.Scheme.CycleSupports.IrreducibleCycleSupport P.carrier p) :
    P.cycleSupportSmoothStratum p Z ⟶ Foundations.Scheme.ProjectiveSpace.complexBase :=
  CycleClass.Geometric.SmoothStratum.smoothStratumToBase (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z.1 P.structureMap)

instance Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.cycleSupportSmoothStratumToBase_isSmooth (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (p : ℕ) (Z : Foundations.Scheme.CycleSupports.IrreducibleCycleSupport P.carrier p) :
    Smooth (P.cycleSupportSmoothStratumToBase p Z) :=
  inferInstanceAs (Smooth (CycleClass.Geometric.SmoothStratum.smoothStratumToBase (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z.1 P.structureMap)))

/-- The smooth locally closed stratum is dense in the actual cycle support. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.cycleSupportSmoothStratum_closure_range (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (p : ℕ) (Z : Foundations.Scheme.CycleSupports.IrreducibleCycleSupport P.carrier p) :
    closure (Set.range (CycleClass.Geometric.SmoothStratum.reducedSupportSmoothStratumι Z.1
      (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z.1 P.structureMap))) = (Z.1 : Set P.carrier) :=
  CycleClass.Geometric.SmoothStratum.reducedSupportSmoothStratum_closure_range Z.1 (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z.1 P.structureMap)

/-- The omitted part of an actual cycle support has larger ambient codimension. -/
theorem Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.cycleSupportSmoothStratum_complement_coheight (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation)
    (p : ℕ) (Z : Foundations.Scheme.CycleSupports.IrreducibleCycleSupport P.carrier p)
    (y : P.carrier) (hy : y ∈ (Z.1 : Set P.carrier))
    (homit : y ∉ Set.range (CycleClass.Geometric.SmoothStratum.reducedSupportSmoothStratumι Z.1
      (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z.1 P.structureMap))) :
    ((p + 1 : ℕ) : ℕ∞) ≤ Order.coheight y :=
  CycleClass.Geometric.SmoothStratum.reducedSupportSmoothStratum_complement_coheight p Z
    (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z.1 P.structureMap) y hy homit

end

end OAI.AlgebraicGeometry
end ComponentSource_9

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.SmoothStratum"

@[expose] public section ComponentSource_10
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.ReducedClosed -/

/-! # Reduced Closed -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.ReducedClosed

noncomputable section

/-!
# Reduced induced schemes on arbitrary closed subsets

This is the reduced induced scheme construction without an irreducibility
hypothesis. The vanishing ideal is genuinely radical on affine opens, and the
resulting closed immersion has precisely the requested underlying image.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

universe u

variable {X : Scheme.{u}}

/-- The radical ideal sheaf vanishing on the specified closed subset. -/
def reducedClosedIdeal (Z : Closeds X) : X.IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal Z

/-- The reduced induced scheme on an arbitrary closed subset. -/
def reducedClosedScheme (Z : Closeds X) : Scheme.{u} :=
  (reducedClosedIdeal Z).subscheme

/-- The canonical inclusion of the reduced closed subscheme. -/
def reducedClosedι (Z : Closeds X) : reducedClosedScheme Z ⟶ X :=
  (reducedClosedIdeal Z).subschemeι

instance reducedClosedι_isClosedImmersion (Z : Closeds X) :
    IsClosedImmersion (reducedClosedι Z) :=
  inferInstanceAs (IsClosedImmersion (reducedClosedIdeal Z).subschemeι)

@[simp]
theorem range_reducedClosedι (Z : Closeds X) :
    Set.range (reducedClosedι Z) = (Z : Set X) := by
  change Set.range (reducedClosedIdeal Z).subschemeι = (Z : Set X)
  rw [Scheme.IdealSheafData.range_subschemeι]
  simp [reducedClosedIdeal]

/-- The canonical inclusion is a genuine topological closed embedding. -/
theorem reducedClosedι_isClosedEmbedding (Z : Closeds X) :
    Topology.IsClosedEmbedding (reducedClosedι Z) :=
  (reducedClosedι Z).isClosedEmbedding

instance reducedClosedScheme_isReduced (Z : Closeds X) :
    AlgebraicGeometry.IsReduced (reducedClosedScheme Z) := by
  let I := reducedClosedIdeal Z
  change AlgebraicGeometry.IsReduced I.subscheme
  apply (AlgebraicGeometry.IsReduced.iff_of_openCover I.subscheme I.subschemeCover.openCover).2
  intro U
  change X.affineOpens at U
  change AlgebraicGeometry.IsReduced (Spec (.of (Γ(X, U) ⧸ I.ideal U)))
  apply (AlgebraicGeometry.affine_isReduced_iff _).2
  apply (Ideal.isRadical_iff_quotient_reduced _).1
  change (PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹' (Z : Set X))).IsRadical
  exact PrimeSpectrum.isRadical_vanishingIdeal _

/-- Nonemptiness of the prescribed closed set gives a point of its induced scheme. -/
theorem reducedClosedScheme_nonempty (Z : Closeds X) (hZ : (Z : Set X).Nonempty) :
    Nonempty (reducedClosedScheme Z) := by
  obtain ⟨x, hx⟩ := hZ
  have h : x ∈ Set.range (reducedClosedι Z) := by
    rw [range_reducedClosedι]
    exact hx
  obtain ⟨y, _⟩ := h
  exact ⟨y⟩

/-- The induced structure morphism is the original one composed with inclusion. -/
def reducedClosedStructureMap (Z : Closeds X) {S : Scheme.{u}} (f : X ⟶ S) :
    reducedClosedScheme Z ⟶ S :=
  reducedClosedι Z ≫ f

@[simp]
theorem reducedClosedStructureMap_eq (Z : Closeds X) {S : Scheme.{u}} (f : X ⟶ S) :
    reducedClosedStructureMap Z f = reducedClosedι Z ≫ f := rfl

instance reducedClosedStructureMap_locallyOfFiniteType (Z : Closeds X)
    {S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] :
    LocallyOfFiniteType (reducedClosedStructureMap Z f) := by
  dsimp [reducedClosedStructureMap]
  infer_instance

instance reducedClosedStructureMap_locallyOfFinitePresentation (Z : Closeds X)
    {S : Scheme.{u}} [IsLocallyNoetherian S] (f : X ⟶ S) [LocallyOfFiniteType f] :
    LocallyOfFinitePresentation (reducedClosedStructureMap Z f) :=
  inferInstance

instance reducedClosedScheme_isLocallyNoetherian [IsLocallyNoetherian X] (Z : Closeds X) :
    IsLocallyNoetherian (reducedClosedScheme Z) :=
  LocallyOfFiniteType.isLocallyNoetherian (reducedClosedι Z)

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.ReducedClosed
end ComponentSource_10

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.ReducedClosed"

@[expose] public section ComponentSource_11
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.SmoothStratification -/

/-! # Smooth Stratification -/

namespace OAI.AlgebraicGeometry

noncomputable section

/-!
# Finite geometric smooth stratifications

A stratum below is an actual scheme with an immersion into the ambient scheme
and a proved smooth structure morphism. A stratification is a finite list of
such strata with disjoint underlying images covering the specified set.
The construction uses Noetherian induction on closed subsets. No Whitney or
analytic regularity condition is asserted.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

universe u

variable {X Y : Scheme.{u}}

/-- A genuine smooth locally closed geometric piece over the given base. -/
structure CycleClass.Geometric.SmoothStratification.SmoothGeometricPiece (f : X ⟶ Y) where
  carrier : Scheme.{u}
  inclusion : carrier ⟶ X
  immersion : IsImmersion inclusion
  smooth : Smooth (inclusion ≫ f)

namespace CycleClass.Geometric.SmoothStratification.SmoothGeometricPiece

variable {f : X ⟶ Y}

instance inclusion_isImmersion (P : SmoothGeometricPiece f) :
    IsImmersion P.inclusion := P.immersion
instance structureMap_isSmooth (P : SmoothGeometricPiece f) :
    Smooth (P.inclusion ≫ f) := P.smooth

/-- The underlying set occupied by this actual geometric piece. -/
def support (P : SmoothGeometricPiece f) : Set X := Set.range P.inclusion

/-- Each stratum has locally closed image, as required for an algebraic stratum. -/
theorem isLocallyClosed_support (P : SmoothGeometricPiece f) :
    IsLocallyClosed P.support :=
  P.inclusion.isLocallyClosed_range

end CycleClass.Geometric.SmoothStratification.SmoothGeometricPiece

/-- The underlying union of a finite list of actual strata. -/
def CycleClass.Geometric.SmoothStratification.smoothPiecesSupport {f : X ⟶ Y} : List (CycleClass.Geometric.SmoothStratification.SmoothGeometricPiece f) → Set X
  | [] => ∅
  | P :: Ps => P.support ∪ smoothPiecesSupport Ps

theorem CycleClass.Geometric.SmoothStratification.support_subset_smoothPiecesSupport {f : X ⟶ Y}
    {P : CycleClass.Geometric.SmoothStratification.SmoothGeometricPiece f} {Ps : List (CycleClass.Geometric.SmoothStratification.SmoothGeometricPiece f)} (hP : P ∈ Ps) :
    P.support ⊆ CycleClass.Geometric.SmoothStratification.smoothPiecesSupport Ps := by
  induction Ps with
  | nil => simp at hP
  | cons Q Qs ih =>
      rcases List.mem_cons.mp hP with h | h
      · subst P
        exact Set.subset_union_left
      · exact Set.Subset.trans (ih h) Set.subset_union_right

/-- Each stratum is dense in the remaining closed tail of the ordered list.
Its closure minus itself is therefore a union of later strata. -/
def CycleClass.Geometric.SmoothStratification.smoothPiecesFrontier {f : X ⟶ Y} : List (CycleClass.Geometric.SmoothStratification.SmoothGeometricPiece f) → Prop
  | [] => True
  | P :: Ps => closure P.support = P.support ∪ CycleClass.Geometric.SmoothStratification.smoothPiecesSupport Ps ∧
      smoothPiecesFrontier Ps

/-- Finite smooth locally closed strata with disjoint images, the frontier
condition, and an exact cover of the specified set. -/
structure CycleClass.Geometric.SmoothStratification.SmoothGeometricStratification (f : X ⟶ Y) (S : Set X) where
  pieces : List (CycleClass.Geometric.SmoothStratification.SmoothGeometricPiece f)
  disjoint : pieces.Pairwise (fun P Q => Disjoint P.support Q.support)
  cover : CycleClass.Geometric.SmoothStratification.smoothPiecesSupport pieces = S
  frontier : CycleClass.Geometric.SmoothStratification.smoothPiecesFrontier pieces

namespace CycleClass.Geometric.SmoothStratification.SmoothGeometricStratification

variable {f : X ⟶ Y}

/-- The empty finite stratification. -/
def empty : SmoothGeometricStratification f ∅ where
  pieces := []
  disjoint := List.Pairwise.nil
  cover := rfl
  frontier := True.intro

/-- Adjoin one smooth geometric stratum disjoint from the already stratified set. -/
def cons {S T : Set X} (P : SmoothGeometricPiece f)
    (Q : SmoothGeometricStratification f T) (hd : Disjoint P.support T)
    (hc : P.support ∪ T = S) (hcl : closure P.support = S) :
    SmoothGeometricStratification f S where
  pieces := P :: Q.pieces
  disjoint := List.pairwise_cons.mpr ⟨fun R hR => hd.mono_right (by
    rw [← Q.cover]
    exact support_subset_smoothPiecesSupport hR), Q.disjoint⟩
  cover := by
    change P.support ∪ SmoothStratification.smoothPiecesSupport Q.pieces = S
    rw [Q.cover]
    exact hc
  frontier := ⟨by simpa only [Q.cover, hc] using hcl, Q.frontier⟩

end CycleClass.Geometric.SmoothStratification.SmoothGeometricStratification

variable {K : Type u} [Field K]

/-- The first stratum of a closed set is the smooth open locus of its reduced
induced scheme, included back into the original ambient scheme. -/
def CycleClass.Geometric.SmoothStratification.closedSmoothPiece (Z : Closeds X) (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] : CycleClass.Geometric.SmoothStratification.SmoothGeometricPiece f where
  carrier := CycleClass.Geometric.SmoothStratum.smoothStratum (CycleClass.Geometric.ReducedClosed.reducedClosedStructureMap Z f)
  inclusion := CycleClass.Geometric.SmoothStratum.smoothStratumι (CycleClass.Geometric.ReducedClosed.reducedClosedStructureMap Z f) ≫ CycleClass.Geometric.ReducedClosed.reducedClosedι Z
  immersion := by infer_instance
  smooth := by
    rw [Category.assoc]
    exact CycleClass.Geometric.SmoothStratum.smoothStratumToBase_isSmooth (CycleClass.Geometric.ReducedClosed.reducedClosedStructureMap Z f)

/-- The singular remainder, as a closed subset of the original ambient scheme. -/
def CycleClass.Geometric.SmoothStratification.closedSingularRemainder (Z : Closeds X) (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] : Closeds X :=
  ⟨(CycleClass.Geometric.ReducedClosed.reducedClosedι Z) '' CycleClass.Geometric.SingularLocus.singularLocus (CycleClass.Geometric.ReducedClosed.reducedClosedStructureMap Z f),
    (CycleClass.Geometric.ReducedClosed.reducedClosedι Z).isClosedEmbedding.isClosedMap _
      (CycleClass.Geometric.SingularLocus.isClosed_singularLocus (CycleClass.Geometric.ReducedClosed.reducedClosedStructureMap Z f))⟩

@[simp]
theorem CycleClass.Geometric.SmoothStratification.closedSmoothPiece_support (Z : Closeds X) (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] :
    (CycleClass.Geometric.SmoothStratification.closedSmoothPiece Z f).support =
      (CycleClass.Geometric.ReducedClosed.reducedClosedι Z) '' ((CycleClass.Geometric.ReducedClosed.reducedClosedStructureMap Z f).smoothLocus :
        Set (CycleClass.Geometric.ReducedClosed.reducedClosedScheme Z)) := by
  change Set.range ((CycleClass.Geometric.ReducedClosed.reducedClosedι Z) ∘
    (CycleClass.Geometric.SmoothStratum.smoothStratumι (CycleClass.Geometric.ReducedClosed.reducedClosedStructureMap Z f))) = _
  rw [Set.range_comp, CycleClass.Geometric.SmoothStratum.range_smoothStratumι]

/-- The smooth first stratum and singular remainder form an exact partition. -/
theorem CycleClass.Geometric.SmoothStratification.closedSmoothPiece_union_remainder (Z : Closeds X) (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] :
    (CycleClass.Geometric.SmoothStratification.closedSmoothPiece Z f).support ∪ (CycleClass.Geometric.SmoothStratification.closedSingularRemainder Z f : Set X) = Z := by
  rw [CycleClass.Geometric.SmoothStratification.closedSmoothPiece_support]
  change (CycleClass.Geometric.ReducedClosed.reducedClosedι Z) '' ((CycleClass.Geometric.ReducedClosed.reducedClosedStructureMap Z f).smoothLocus : Set _) ∪
    (CycleClass.Geometric.ReducedClosed.reducedClosedι Z) '' ((CycleClass.Geometric.ReducedClosed.reducedClosedStructureMap Z f).smoothLocus : Set _)ᶜ = _
  rw [Set.image_union_image_compl_eq_range, CycleClass.Geometric.ReducedClosed.range_reducedClosedι]

theorem CycleClass.Geometric.SmoothStratification.closedSmoothPiece_disjoint_remainder (Z : Closeds X) (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] :
    Disjoint (CycleClass.Geometric.SmoothStratification.closedSmoothPiece Z f).support (CycleClass.Geometric.SmoothStratification.closedSingularRemainder Z f : Set X) := by
  rw [CycleClass.Geometric.SmoothStratification.closedSmoothPiece_support]
  change Disjoint ((CycleClass.Geometric.ReducedClosed.reducedClosedι Z) ''
    ((CycleClass.Geometric.ReducedClosed.reducedClosedStructureMap Z f).smoothLocus : Set _))
    ((CycleClass.Geometric.ReducedClosed.reducedClosedι Z) '' ((CycleClass.Geometric.ReducedClosed.reducedClosedStructureMap Z f).smoothLocus : Set _)ᶜ)
  apply (Set.disjoint_image_iff (CycleClass.Geometric.ReducedClosed.reducedClosedι Z).isClosedEmbedding.injective).mpr
  exact disjoint_compl_right

theorem CycleClass.Geometric.SmoothStratification.closedSingularRemainder_le (Z : Closeds X) (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] : CycleClass.Geometric.SmoothStratification.closedSingularRemainder Z f ≤ Z := by
  intro x hx
  have hmem : x ∈ (CycleClass.Geometric.SmoothStratification.closedSmoothPiece Z f).support ∪
      (CycleClass.Geometric.SmoothStratification.closedSingularRemainder Z f : Set X) := Or.inr hx
  rw [CycleClass.Geometric.SmoothStratification.closedSmoothPiece_union_remainder] at hmem
  exact hmem

variable [PerfectField K]

/-- The first stratum is dense in this closed set, giving the frontier condition. -/
theorem CycleClass.Geometric.SmoothStratification.closure_closedSmoothPiece_support (Z : Closeds X) (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] : closure (CycleClass.Geometric.SmoothStratification.closedSmoothPiece Z f).support = (Z : Set X) := by
  rw [CycleClass.Geometric.SmoothStratification.closedSmoothPiece_support, (CycleClass.Geometric.ReducedClosed.reducedClosedι Z).isClosedEmbedding.closure_image_eq,
    (CycleClass.Geometric.ReducedClosed.reducedClosedStructureMap Z f).dense_smoothLocus_of_perfectField.closure_eq,
    Set.image_univ, CycleClass.Geometric.ReducedClosed.range_reducedClosedι]

/-- Unless the closed set is empty, generic smoothness makes the singular
remainder strictly smaller. This is the decreasing measure in Noetherian induction. -/
theorem CycleClass.Geometric.SmoothStratification.closedSingularRemainder_lt (Z : Closeds X) (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] (hZ : Z ≠ ⊥) : CycleClass.Geometric.SmoothStratification.closedSingularRemainder Z f < Z := by
  apply lt_of_le_not_ge (CycleClass.Geometric.SmoothStratification.closedSingularRemainder_le Z f)
  intro hge
  let : Nonempty (CycleClass.Geometric.ReducedClosed.reducedClosedScheme Z) :=
    CycleClass.Geometric.ReducedClosed.reducedClosedScheme_nonempty Z (Closeds.coe_nonempty.mpr hZ)
  have hnonempty : Nonempty (CycleClass.Geometric.SmoothStratum.smoothStratum (CycleClass.Geometric.ReducedClosed.reducedClosedStructureMap Z f)) :=
    (CycleClass.Geometric.SmoothStratum.smoothStratum_denseRange (CycleClass.Geometric.ReducedClosed.reducedClosedStructureMap Z f)).nonempty
  obtain ⟨a⟩ := hnonempty
  have ha : (CycleClass.Geometric.SmoothStratification.closedSmoothPiece Z f).inclusion a ∈ (CycleClass.Geometric.SmoothStratification.closedSmoothPiece Z f).support :=
    Set.mem_range_self a
  have haZ : (CycleClass.Geometric.SmoothStratification.closedSmoothPiece Z f).inclusion a ∈ (Z : Set X) :=
    (CycleClass.Geometric.SmoothStratification.closedSmoothPiece_union_remainder Z f) ▸ Or.inl ha
  exact (Set.disjoint_left.mp (CycleClass.Geometric.SmoothStratification.closedSmoothPiece_disjoint_remainder Z f)) ha (hge haZ)

/-- Noetherian induction produces finitely many actual smooth locally closed
strata, with disjoint images and the frontier condition, for every closed subset. -/
theorem CycleClass.Geometric.SmoothStratification.nonempty_smoothGeometricStratification_closed [NoetherianSpace X]
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] (Z : Closeds X) :
    Nonempty (CycleClass.Geometric.SmoothStratification.SmoothGeometricStratification f (Z : Set X)) := by
  apply wellFounded_lt.induction Z
  clear Z
  intro Z ih
  by_cases hZ : Z = ⊥
  · subst Z
    exact ⟨CycleClass.Geometric.SmoothStratification.SmoothGeometricStratification.empty⟩
  · obtain ⟨Q⟩ := ih (CycleClass.Geometric.SmoothStratification.closedSingularRemainder Z f) (CycleClass.Geometric.SmoothStratification.closedSingularRemainder_lt Z f hZ)
    exact ⟨CycleClass.Geometric.SmoothStratification.SmoothGeometricStratification.cons (CycleClass.Geometric.SmoothStratification.closedSmoothPiece Z f) Q
      (CycleClass.Geometric.SmoothStratification.closedSmoothPiece_disjoint_remainder Z f)
      (CycleClass.Geometric.SmoothStratification.closedSmoothPiece_union_remainder Z f) (CycleClass.Geometric.SmoothStratification.closure_closedSmoothPiece_support Z f)⟩

/-- A finite-type scheme over a perfect field admits a finite smooth geometric
stratification of its underlying space. -/
theorem CycleClass.Geometric.SmoothStratification.nonempty_smoothGeometricStratification_of_finiteType
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] [QuasiCompact f] :
    Nonempty (CycleClass.Geometric.SmoothStratification.SmoothGeometricStratification f Set.univ) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  let : IsNoetherian X := ⟨⟩
  exact CycleClass.Geometric.SmoothStratification.nonempty_smoothGeometricStratification_closed f ⊤

/-- A chosen finite stratification, extracted from the proved existence theorem. -/
def CycleClass.Geometric.SmoothStratification.smoothGeometricStratification_of_finiteType
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] [QuasiCompact f] :
    CycleClass.Geometric.SmoothStratification.SmoothGeometricStratification f Set.univ :=
  Classical.choice (CycleClass.Geometric.SmoothStratification.nonempty_smoothGeometricStratification_of_finiteType f)

/-- The construction applies in particular to the actual smooth projective
complex domains in this development. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.smoothGeometricStratification
    (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) :
    CycleClass.Geometric.SmoothStratification.SmoothGeometricStratification P.structureMap Set.univ :=
  CycleClass.Geometric.SmoothStratification.smoothGeometricStratification_of_finiteType P.structureMap

/-- Every actual integral cycle support has a finite smooth stratification. -/
def Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation.cycleSupportSmoothGeometricStratification
    (P : Foundations.Scheme.SmoothProjective.SmoothProjectivePresentation) (p : ℕ)
    (Z : Foundations.Scheme.CycleSupports.IrreducibleCycleSupport P.carrier p) :
    CycleClass.Geometric.SmoothStratification.SmoothGeometricStratification (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z.1 P.structureMap) Set.univ :=
  CycleClass.Geometric.SmoothStratification.smoothGeometricStratification_of_finiteType (CycleClass.Geometric.SupportFiniteType.supportStructureMap Z.1 P.structureMap)

end

end OAI.AlgebraicGeometry
end ComponentSource_11

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.SmoothStratification"

@[expose] public section ComponentSource_12
/- Original module: OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveTransport -/

/-! # Projective Transport -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme

noncomputable section

/-!
# Transport of actual projective presentations

The constructions here precompose genuine scheme morphisms with scheme
isomorphisms. The resulting presentations have the transported complex
structure map, and define isomorphic objects over `Spec ℂ`.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- Precomposing by a scheme isomorphism preserves and reflects smoothness. -/
theorem ProjectiveTransport.smooth_precompose_iso_iff {X Y S : Scheme}
    (e : Y ≅ X) (f : X ⟶ S) : Smooth (e.hom ≫ f) ↔ Smooth f := by
  constructor
  · intro h
    let : Smooth (e.hom ≫ f) := h
    have h' : Smooth (e.inv ≫ (e.hom ≫ f)) := inferInstance
    simpa using h'
  · intro h
    let : Smooth f := h
    infer_instance

/-- Precomposing by a scheme isomorphism preserves and reflects closed immersions. -/
theorem ProjectiveTransport.closedImmersion_precompose_iso_iff {X Y S : Scheme}
    (e : Y ≅ X) (f : X ⟶ S) :
    IsClosedImmersion (e.hom ≫ f) ↔ IsClosedImmersion f := by
  constructor
  · intro h
    let : IsClosedImmersion (e.hom ≫ f) := h
    have h' : IsClosedImmersion (e.inv ≫ (e.hom ≫ f)) := inferInstance
    simpa using h'
  · intro h
    let : IsClosedImmersion f := h
    infer_instance

section

variable {X Y : Scheme} {f : X ⟶ ProjectiveSpace.complexBase}

/-- Transport a chosen closed projective embedding to an isomorphic scheme. -/
def SmoothProjective.ProjectivePresentation.transportIso (P : SmoothProjective.ProjectivePresentation X f) (e : Y ≅ X) :
    SmoothProjective.ProjectivePresentation Y (e.hom ≫ f) where
  ambientDimension := P.ambientDimension
  embedding := e.hom ≫ P.embedding
  closedImmersion := inferInstance
  over_base := by simp only [Category.assoc, P.over_base]

@[simp]
theorem SmoothProjective.ProjectivePresentation.transportIso_ambientDimension (P : SmoothProjective.ProjectivePresentation X f) (e : Y ≅ X) :
    (P.transportIso e).ambientDimension = P.ambientDimension := rfl

@[simp]
theorem SmoothProjective.ProjectivePresentation.transportIso_embedding (P : SmoothProjective.ProjectivePresentation X f) (e : Y ≅ X) :
    (P.transportIso e).embedding = e.hom ≫ P.embedding := rfl

/-- Existence of a projective presentation is invariant under a scheme
isomorphism, with its induced complex structure map. -/
theorem SmoothProjective.ProjectivePresentation.nonempty_transportIso_iff (e : Y ≅ X) :
    Nonempty (SmoothProjective.ProjectivePresentation Y (e.hom ≫ f)) ↔
      Nonempty (SmoothProjective.ProjectivePresentation X f) := by
  constructor
  · rintro ⟨P⟩
    have h : Nonempty (SmoothProjective.ProjectivePresentation X (e.inv ≫ (e.hom ≫ f))) :=
      ⟨P.transportIso e.symm⟩
    simpa using h
  · rintro ⟨P⟩
    exact ⟨P.transportIso e⟩

/-- The same invariance for explicitly specified maps to `Spec ℂ`. -/
theorem SmoothProjective.ProjectivePresentation.nonempty_iff_of_iso {g : Y ⟶ ProjectiveSpace.complexBase}
    (e : Y ≅ X) (h : e.hom ≫ f = g) :
    Nonempty (SmoothProjective.ProjectivePresentation Y g) ↔
      Nonempty (SmoothProjective.ProjectivePresentation X f) := by
  subst g
  exact SmoothProjective.ProjectivePresentation.nonempty_transportIso_iff e

end

/-- Transport a smooth projective complex scheme and its presentation along
an isomorphism of its underlying scheme. -/
def SmoothProjective.SmoothProjectivePresentation.transportIso (P : SmoothProjective.SmoothProjectivePresentation) {Y : Scheme}
    (e : Y ≅ P.carrier) : SmoothProjective.SmoothProjectivePresentation where
  carrier := Y
  structureMap := e.hom ≫ P.structureMap
  projective := P.projective.transportIso e
  smooth := inferInstance

@[simp]
theorem SmoothProjective.SmoothProjectivePresentation.transportIso_structureMap (P : SmoothProjective.SmoothProjectivePresentation) {Y : Scheme}
    (e : Y ≅ P.carrier) :
    (P.transportIso e).structureMap = e.hom ≫ P.structureMap := rfl

@[simp]
theorem SmoothProjective.SmoothProjectivePresentation.transportIso_embedding (P : SmoothProjective.SmoothProjectivePresentation) {Y : Scheme}
    (e : Y ≅ P.carrier) :
    (P.transportIso e).embedding = e.hom ≫ P.embedding := rfl

/-- Transport changes the presentation but preserves the complex scheme up to
an actual isomorphism over the base. -/
def SmoothProjective.SmoothProjectivePresentation.transportIso_overIso (P : SmoothProjective.SmoothProjectivePresentation) {Y : Scheme}
    (e : Y ≅ P.carrier) : (P.transportIso e).toOver ≅ P.toOver :=
  Over.isoMk e rfl

end

end OAI.AlgebraicGeometry.Foundations.Scheme
end ComponentSource_12

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Foundations.Scheme.ProjectiveTransport"

@[expose] public section ComponentSource_13
/- Original module: OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective -/

/-! # Integral Projective -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective

noncomputable section

/-!
# Integral smooth projective complex varieties

This file restricts actual smooth projective presentations to carriers satisfying
mathlib's `IsIntegral`. It therefore makes the usual irreducibility and
nonemptiness convention for a variety explicit, rather than identifying the
raw possibly disconnected presentation type with that convention.
-/

open _root_.CategoryTheory _root_.AlgebraicGeometry

/-- A smooth projective complex presentation whose actual scheme is integral. -/
abbrev IntegralProjectiveVariety :=
  {P : SmoothProjective.SmoothProjectivePresentation // IsIntegral P.carrier}

namespace IntegralProjectiveVariety

/-- Forget only the integral-carrier condition. -/
abbrev presentation (V : IntegralProjectiveVariety) : SmoothProjective.SmoothProjectivePresentation := V.val

/-- The underlying actual scheme. -/
abbrev carrier (V : IntegralProjectiveVariety) : Scheme := V.presentation.carrier

/-- The actual morphism specifying the complex base. -/
abbrev structureMap (V : IntegralProjectiveVariety) : V.carrier ⟶ ProjectiveSpace.complexBase :=
  V.presentation.structureMap

/-- The ambient dimension of the chosen projective embedding. -/
abbrev ambientDimension (V : IntegralProjectiveVariety) : ℕ :=
  V.presentation.ambientDimension

/-- The actual closed projective embedding. -/
abbrev embedding (V : IntegralProjectiveVariety) :
    V.carrier ⟶ ProjectiveSpace.projectiveSpace V.ambientDimension := V.presentation.embedding

instance (V : IntegralProjectiveVariety) : IsIntegral V.carrier := V.property

instance (V : IntegralProjectiveVariety) : Smooth V.structureMap := V.presentation.smooth

instance (V : IntegralProjectiveVariety) : IsClosedImmersion V.embedding :=
  V.presentation.projective.closedImmersion

/-- Integral varieties are nonempty in mathlib's actual scheme topology. -/
theorem carrier_nonempty (V : IntegralProjectiveVariety) : Nonempty V.carrier :=
  inferInstance

/-- Irreducibility follows from the native integral-scheme condition. -/
theorem carrier_irreducible (V : IntegralProjectiveVariety) :
    IrreducibleSpace V.carrier := inferInstance

/-- Reducedness follows from the native integral-scheme condition. -/
theorem carrier_reduced (V : IntegralProjectiveVariety) :
    IsReduced V.carrier := inferInstance

/-- The associated complex scheme as an object over the base. -/
abbrev toOver (V : IntegralProjectiveVariety) : Over ProjectiveSpace.complexBase := V.presentation.toOver

/-- The chosen embedding is over the specified complex base. -/
@[reassoc]
theorem embedding_over (V : IntegralProjectiveVariety) :
    V.embedding ≫ ProjectiveSpace.projectiveSpaceToBase V.ambientDimension = V.structureMap :=
  V.presentation.embedding_over

/-- Every bundled variety has an actual closed projective embedding. -/
theorem exists_closedImmersion (V : IntegralProjectiveVariety) :
    ∃ (n : ℕ) (i : V.carrier ⟶ ProjectiveSpace.projectiveSpace n),
      IsClosedImmersion i ∧ i ≫ ProjectiveSpace.projectiveSpaceToBase n = V.structureMap :=
  SmoothProjective.ProjectivePresentation.nonempty_iff.mp ⟨V.presentation.projective⟩

/-- Construct the bundle from exactly the standard algebraic conditions. -/
def ofClosedImmersion {X : Scheme} (f : X ⟶ ProjectiveSpace.complexBase)
    (n : ℕ) (i : X ⟶ ProjectiveSpace.projectiveSpace n) (hi : IsClosedImmersion i)
    (hif : i ≫ ProjectiveSpace.projectiveSpaceToBase n = f) (hf : Smooth f) (hX : IsIntegral X) :
    IntegralProjectiveVariety :=
  ⟨{ carrier := X
     structureMap := f
     projective := ⟨n, i, hi, hif⟩
     smooth := hf }, hX⟩

@[simp]
theorem ofClosedImmersion_carrier {X : Scheme} (f : X ⟶ ProjectiveSpace.complexBase)
    (n : ℕ) (i : X ⟶ ProjectiveSpace.projectiveSpace n) (hi : IsClosedImmersion i)
    (hif : i ≫ ProjectiveSpace.projectiveSpaceToBase n = f) (hf : Smooth f) (hX : IsIntegral X) :
    (ofClosedImmersion f n i hi hif hf hX).carrier = X := rfl

@[simp]
theorem ofClosedImmersion_structureMap {X : Scheme} (f : X ⟶ ProjectiveSpace.complexBase)
    (n : ℕ) (i : X ⟶ ProjectiveSpace.projectiveSpace n) (hi : IsClosedImmersion i)
    (hif : i ≫ ProjectiveSpace.projectiveSpaceToBase n = f) (hf : Smooth f) (hX : IsIntegral X) :
    (ofClosedImmersion f n i hi hif hf hX).structureMap = f := rfl

/-- Integrality as well as the chosen smooth projective presentation transports
along an actual scheme isomorphism. -/
def transportIso (V : IntegralProjectiveVariety) {Y : Scheme}
    (e : Y ≅ V.carrier) : IntegralProjectiveVariety :=
  ⟨V.presentation.transportIso e, by
    change IsIntegral Y
    exact IsIntegral.of_isIso e.inv⟩

@[simp]
theorem transportIso_structureMap (V : IntegralProjectiveVariety) {Y : Scheme}
    (e : Y ≅ V.carrier) :
    (V.transportIso e).structureMap = e.hom ≫ V.structureMap := rfl

/-- The transported object is genuinely isomorphic over `Spec ℂ`. -/
def transportIso_overIso (V : IntegralProjectiveVariety) {Y : Scheme}
    (e : Y ≅ V.carrier) : (V.transportIso e).toOver ≅ V.toOver :=
  V.presentation.transportIso_overIso e

/-- Exact coverage, up to isomorphism over the complex base, by the integral
smooth projective presentation type. No disconnected presentation is identified
with an irreducible variety in this statement. -/
theorem exists_overIso_iff (X : Scheme) (f : X ⟶ ProjectiveSpace.complexBase) :
    (∃ (V : IntegralProjectiveVariety) (e : X ≅ V.carrier),
      e.hom ≫ V.structureMap = f) ↔
    IsIntegral X ∧ Smooth f ∧
      ∃ (n : ℕ) (i : X ⟶ ProjectiveSpace.projectiveSpace n),
        IsClosedImmersion i ∧ i ≫ ProjectiveSpace.projectiveSpaceToBase n = f := by
  constructor
  · rintro ⟨V, e, he⟩
    have hX : IsIntegral X := IsIntegral.of_isIso e.inv
    have hf' : Smooth (e.hom ≫ V.structureMap) := inferInstance
    have hf : Smooth f := he ▸ hf'
    refine ⟨hX, hf, V.ambientDimension, e.hom ≫ V.embedding, inferInstance, ?_⟩
    rw [Category.assoc, V.embedding_over, he]
  · rintro ⟨hX, hf, n, i, hi, hif⟩
    let V := ofClosedImmersion f n i hi hif hf hX
    refine ⟨V, Iso.refl X, ?_⟩
    change (𝟙 X) ≫ f = f
    simp

end IntegralProjectiveVariety

end

end OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective
end ComponentSource_13

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Foundations.Scheme.IntegralProjective"

@[expose] public section ComponentSource_14
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.FiniteSupport -/

/-! # Finite Support -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.FiniteSupport.Cycles

/-!
# Finite support of algebraic cycles on quasi-compact schemes

Mathlib's algebraic cycles are functions on scheme points with locally finite
support. Compactness alone makes that support finite: no Hausdorff or T1
assumption is needed. The conversions below retain every coefficient.
-/

open _root_.AlgebraicGeometry

universe u v

/-- A locally finitely supported function on a compact space has finite support,
without any separation assumption on that space. -/
theorem finiteSupport_locallyFinsupp {T : Type u} [TopologicalSpace T]
    [CompactSpace T] {R : Type v} [Zero R] (c : Function.locallyFinsupp T R) :
    (Function.support c).Finite := by
  simpa only [Set.univ_inter, Function.locallyFinsuppWithin.toFun_eq_coe] using
    c.locallyFiniteSupport.finite_inter_support_of_isCompact isCompact_univ

/-- Quasi-compactness of the scheme suffices to turn mathlib's locally finite
algebraic cycles into finitely supported cycles. -/
theorem algebraicCycle_finiteSupport {X : Scheme.{u}} [CompactSpace X]
    {R : Type v} [Zero R] (c : AlgebraicCycle X R) :
    (Function.support c).Finite :=
  finiteSupport_locallyFinsupp c

/-- Every finite cycle defines a mathlib algebraic cycle, on any scheme. -/
def finsuppToAlgebraicCycle {X : Scheme.{u}} {R : Type v} [Zero R]
    (c : X →₀ R) : AlgebraicCycle X R where
  toFun := c
  supportWithinDomain' := Set.subset_univ _
  supportLocallyFiniteWithinDomain' _ _ :=
    ⟨Set.univ, Filter.univ_mem, by
      simpa only [Set.univ_inter, Function.HasFiniteSupport] using c.hasFiniteSupport⟩

@[simp]
theorem finsuppToAlgebraicCycle_apply {X : Scheme.{u}} {R : Type v} [Zero R]
    (c : X →₀ R) (x : X) : finsuppToAlgebraicCycle c x = c x := rfl

/-- On a quasi-compact scheme, an algebraic cycle is a finite coefficient list. -/
noncomputable def algebraicCycleToFinsupp {X : Scheme.{u}} [CompactSpace X]
    {R : Type v} [Zero R] (c : AlgebraicCycle X R) : X →₀ R :=
  Finsupp.ofSupportFinite c (algebraicCycle_finiteSupport c)

@[simp]
theorem algebraicCycleToFinsupp_apply {X : Scheme.{u}} [CompactSpace X]
    {R : Type v} [Zero R] (c : AlgebraicCycle X R) (x : X) :
    algebraicCycleToFinsupp c x = c x := rfl

/-- This equivalence identifies coefficients, rather than selecting an arbitrary
bijection between the two notions of cycles. -/
noncomputable def algebraicCycleFinsuppEquiv (X : Scheme.{u}) [CompactSpace X]
    (R : Type v) [Zero R] : AlgebraicCycle X R ≃ (X →₀ R) where
  toFun := algebraicCycleToFinsupp
  invFun := finsuppToAlgebraicCycle
  left_inv _ := DFunLike.ext _ _ fun _ => rfl
  right_inv _ := Finsupp.ext fun _ => rfl

@[simp]
theorem algebraicCycleToFinsupp_finsuppToAlgebraicCycle {X : Scheme.{u}}
    [CompactSpace X] {R : Type v} [Zero R] (c : X →₀ R) :
    algebraicCycleToFinsupp (finsuppToAlgebraicCycle c) = c :=
  (algebraicCycleFinsuppEquiv X R).apply_symm_apply c

@[simp]
theorem finsuppToAlgebraicCycle_algebraicCycleToFinsupp {X : Scheme.{u}}
    [CompactSpace X] {R : Type v} [Zero R] (c : AlgebraicCycle X R) :
    finsuppToAlgebraicCycle (algebraicCycleToFinsupp c) = c :=
  (algebraicCycleFinsuppEquiv X R).symm_apply_apply c

/-- The equivalence also preserves addition of cycle coefficients. -/
noncomputable def algebraicCycleFinsuppAddEquiv (X : Scheme.{u}) [CompactSpace X]
    (R : Type v) [AddMonoid R] : AlgebraicCycle X R ≃+ (X →₀ R) where
  toEquiv := algebraicCycleFinsuppEquiv X R
  map_add' _ _ := Finsupp.ext fun _ => rfl

end OAI.AlgebraicGeometry.CycleClass.Geometric.FiniteSupport.Cycles
end ComponentSource_14

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.FiniteSupport"

@[expose] public section ComponentSource_15
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles -/

/-! # Dimension Cycles -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles

noncomputable section

/-!
# Algebraic cycles graded by actual function-field dimension

This module is separate from the earlier specialization-coheight cycle API.
Its grading uses the transcendence degrees of the actual function fields of
an integral projective variety and of the reduced integral closed subscheme
on each irreducible support. It accepts no arbitrary dimension function.

The support is allowed to be singular. These are genuine finite algebraic
cycles, not Betti classes; no cycle-class map or Hodge assertion is assumed.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace
open scoped BigOperators

universe v

/-- Codimension by the difference of actual function-field dimensions. -/
def dimensionCodimension (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (Z : IrreducibleCloseds V.carrier) : ℕ :=
  Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension V.structureMap -
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z V.structureMap

/-- Actual support dimension and codimension add to the ambient dimension.
The support-dimension inequality removes any truncated-subtraction ambiguity. -/
theorem supportDimension_add_dimensionCodimension (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety)
    (Z : IrreducibleCloseds V.carrier) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z V.structureMap + dimensionCodimension V Z =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension V.structureMap := by
  exact Nat.add_sub_of_le (Foundations.Scheme.SupportDimension.supportTranscendenceDimension_le Z V.structureMap)

/-- The actual irreducible closed supports in the indicated dimension grading. -/
def DimensionCycleSupport (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) :=
  {Z : IrreducibleCloseds V.carrier // dimensionCodimension V Z = p}

namespace DimensionCycleSupport

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}

/-- The reduced integral closed scheme on the cycle support. -/
abbrev scheme (Z : DimensionCycleSupport V p) : Scheme := GenericPoint.reducedSupportScheme Z.1

/-- Its actual closed immersion into the projective ambient variety. -/
abbrev inclusion (Z : DimensionCycleSupport V p) : Z.scheme ⟶ V.carrier :=
  GenericPoint.reducedSupportι Z.1

/-- Its induced complex structure morphism. -/
abbrev structureMap (Z : DimensionCycleSupport V p) : Z.scheme ⟶ Foundations.Scheme.ProjectiveSpace.complexBase :=
  SupportFiniteType.supportStructureMap Z.1 V.structureMap

instance scheme_isIntegral (Z : DimensionCycleSupport V p) : IsIntegral Z.scheme :=
  GenericPoint.reducedSupportScheme_isIntegral Z.1

instance inclusion_isClosedImmersion (Z : DimensionCycleSupport V p) :
    IsClosedImmersion Z.inclusion := GenericPoint.reducedSupportι_isClosedImmersion Z.1

/-- Every support inherits a genuine projective embedding. Smoothness of that
support is neither assumed nor required. -/
def projectivePresentation (Z : DimensionCycleSupport V p) :
    Foundations.Scheme.SmoothProjective.ProjectivePresentation Z.scheme Z.structureMap :=
  V.presentation.projective.reducedSupport Z.1

instance structureMap_isProper (Z : DimensionCycleSupport V p) : IsProper Z.structureMap :=
  Z.projectivePresentation.isProper

instance structureMap_locallyOfFiniteType (Z : DimensionCycleSupport V p) :
    LocallyOfFiniteType Z.structureMap := by infer_instance

/-- The indexing condition is literally the difference of the two function-field dimensions. -/
theorem dimension_difference (Z : DimensionCycleSupport V p) :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension V.structureMap -
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z.1 V.structureMap = p := Z.2

/-- A degree-`p` support has dimension exactly ambient dimension minus `p`. -/
theorem dimension_add_codimension (Z : DimensionCycleSupport V p) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z.1 V.structureMap + p =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension V.structureMap := by
  simpa only [Z.2] using supportDimension_add_dimensionCodimension V Z.1

/-- The dimension-based codimension never exceeds the ambient dimension. -/
theorem codimension_le_ambient (Z : DimensionCycleSupport V p) :
    p ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension V.structureMap := by
  rw [← Z.dimension_difference]
  exact Nat.sub_le _ _

/-- There are no supports in degrees greater than the dimension of the variety. -/
theorem isEmpty_of_ambient_lt (h : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension V.structureMap < p) :
    IsEmpty (DimensionCycleSupport V p) :=
  ⟨fun Z => (Nat.not_le_of_lt h) Z.codimension_le_ambient⟩

/-- The unique actual scheme point generic in the irreducible support. -/
def genericPoint (Z : DimensionCycleSupport V p) : V.carrier :=
  irreducibleSetEquivPoints Z.1

/-- The support label really is the closure of the indicated generic point. -/
theorem genericPoint_spec (Z : DimensionCycleSupport V p) :
    IsGenericPoint Z.genericPoint (Z.1 : Set V.carrier) :=
  Z.1.isIrreducible.isGenericPoint_genericPoint Z.1.isClosed

/-- Distinct irreducible supports have distinct generic points. -/
theorem genericPoint_injective :
    Function.Injective (DimensionCycleSupport.genericPoint : DimensionCycleSupport V p → V.carrier) := by
  intro Z W h
  apply Subtype.ext
  exact irreducibleSetEquivPoints.injective h

/-- The coefficient-preserving embedding into the point index used by mathlib. -/
def genericPointEmbedding (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) :
    DimensionCycleSupport V p ↪ V.carrier :=
  ⟨DimensionCycleSupport.genericPoint, genericPoint_injective⟩

/-- The constructed integral support maps its own generic point to this label. -/
theorem inclusion_genericPoint (Z : DimensionCycleSupport V p) :
    Z.inclusion (_root_.genericPoint Z.scheme) = Z.genericPoint :=
  GenericPoint.reducedSupport_genericPoint_eq Z.1

end DimensionCycleSupport

/-- Finite algebraic cycles with the genuine function-field dimension grading. -/
abbrev DimensionCycle (R : Type v) [Zero R] (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) :=
  DimensionCycleSupport V p →₀ R

abbrev IntegralDimensionCycle (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) :=
  DimensionCycle ℤ V p

abbrev RationalDimensionCycle (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) :=
  DimensionCycle ℚ V p

namespace DimensionCycle

variable {R : Type v} {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}

/-- A dimension-graded algebraic cycle above the ambient dimension vanishes. -/
theorem eq_zero_of_ambient_lt [Zero R] (z : DimensionCycle R V p)
    (h : Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension V.structureMap < p) : z = 0 := by
  let := DimensionCycleSupport.isEmpty_of_ambient_lt h
  exact Finsupp.ext fun Z => isEmptyElim Z

/-- Forgetting the dimension grade retains every irreducible-support coefficient. -/
def toSupportFinsupp [Zero R] (z : DimensionCycle R V p) :
    IrreducibleCloseds V.carrier →₀ R :=
  Finsupp.embDomain (Function.Embedding.subtype fun Z => dimensionCodimension V Z = p) z

@[simp]
theorem toSupportFinsupp_apply [Zero R] (z : DimensionCycle R V p)
    (Z : DimensionCycleSupport V p) : z.toSupportFinsupp Z.1 = z Z :=
  Finsupp.embDomain_apply_self _ _ _

/-- Extension by zero away from the actual dimension grade. -/
theorem toSupportFinsupp_apply_of_codimension_ne [Zero R] (z : DimensionCycle R V p)
    (Z : IrreducibleCloseds V.carrier) (hZ : dimensionCodimension V Z ≠ p) :
    z.toSupportFinsupp Z = 0 := by
  apply Finsupp.embDomain_of_notMem_range
  rintro ⟨W, rfl⟩
  exact hZ W.2

theorem toSupportFinsupp_injective [Zero R] :
    Function.Injective (DimensionCycle.toSupportFinsupp : DimensionCycle R V p →
      IrreducibleCloseds V.carrier →₀ R) :=
  Finsupp.embDomain_injective _

/-- The same cycle in the generic-point index used by mathlib's algebraic cycles. -/
def toPointFinsupp [Zero R] (z : DimensionCycle R V p) : V.carrier →₀ R :=
  Finsupp.embDomain (DimensionCycleSupport.genericPointEmbedding V p) z

@[simp]
theorem toPointFinsupp_apply [Zero R] (z : DimensionCycle R V p)
    (Z : DimensionCycleSupport V p) : z.toPointFinsupp Z.genericPoint = z Z :=
  Finsupp.embDomain_apply_self _ _ _

theorem toPointFinsupp_injective [Zero R] :
    Function.Injective (DimensionCycle.toPointFinsupp : DimensionCycle R V p → V.carrier →₀ R) :=
  Finsupp.embDomain_injective _

/-- These finite cycles determine actual mathlib algebraic cycles with the same
coefficients on the unique generic points of their supports. -/
def toAlgebraicCycle [Zero R] (z : DimensionCycle R V p) : AlgebraicCycle V.carrier R :=
  FiniteSupport.Cycles.finsuppToAlgebraicCycle z.toPointFinsupp

@[simp]
theorem toAlgebraicCycle_apply [Zero R] (z : DimensionCycle R V p)
    (Z : DimensionCycleSupport V p) : z.toAlgebraicCycle Z.genericPoint = z Z :=
  toPointFinsupp_apply z Z

theorem toAlgebraicCycle_injective [Zero R] :
    Function.Injective (DimensionCycle.toAlgebraicCycle : DimensionCycle R V p → AlgebraicCycle V.carrier R) := by
  intro z w h
  apply Finsupp.ext
  intro Z
  have he := congrArg (fun c : AlgebraicCycle V.carrier R => c Z.genericPoint) h
  simpa only [toAlgebraicCycle_apply] using he

/-- Actual irreducible closed supports form the free basis of these cycles. -/
def basis (R : Type v) [Semiring R] (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) :
    Module.Basis (DimensionCycleSupport V p) R (DimensionCycle R V p) :=
  Finsupp.basisSingleOne

@[simp]
theorem basis_apply [Semiring R] (Z : DimensionCycleSupport V p) :
    basis R V p Z = Finsupp.single Z (1 : R) := rfl

/-- Every cycle is its finite linear combination of actual irreducible supports. -/
theorem eq_sum_support [Semiring R] (z : DimensionCycle R V p) :
    z = ∑ Z ∈ z.support, z Z • Finsupp.single Z (1 : R) := by
  classical
  simpa only [Finsupp.sum, Finsupp.smul_single_one] using (Finsupp.sum_single z).symm

/-- The dimension grade is a concrete supported submodule, using the fixed
function-field dimensions above rather than an arbitrary weight function. -/
def supportedSubmodule (R : Type v) [Semiring R] (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) :
    Submodule R (IrreducibleCloseds V.carrier →₀ R) :=
  Finsupp.supported R R {Z | dimensionCodimension V Z = p}

/-- Finite support labels and the concrete supported submodule are equivalent. -/
def equivSupported (R : Type v) [Semiring R] (V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety) (p : ℕ) :
    DimensionCycle R V p ≃ₗ[R] supportedSubmodule R V p :=
  (Finsupp.supportedEquivFinsupp (R := R) {Z | dimensionCodimension V Z = p}).symm

end DimensionCycle

end

end OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles
end ComponentSource_15

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.DimensionCycles"

@[expose] public section ComponentSource_16
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification -/

/-! # Integral Smooth Stratification -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric

noncomputable section

/-!
# Finite stratifications by actual integral smooth pieces

A nonempty Noetherian reduced scheme has a nonempty integral open subscheme:
choose an open subset contained in one irreducible component. Taking its
actual smooth locus over a perfect field produces an integral smooth open
piece. Noetherian induction on the closed complement gives a finite disjoint
cover by such pieces. The boundary of each piece is contained in later pieces;
its closure need not equal the entire remaining closed set.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

universe u

variable {X Y : Scheme.{u}}

/-- A smooth locally closed geometric piece whose actual carrier is integral. -/
structure IntegralSmoothStratification.IntegralSmoothGeometricPiece (f : X ⟶ Y) extends SmoothStratification.SmoothGeometricPiece f where
  integral : IsIntegral carrier

namespace IntegralSmoothStratification.IntegralSmoothGeometricPiece

variable {f : X ⟶ Y}

instance carrier_isIntegral (P : IntegralSmoothGeometricPiece f) : IsIntegral P.carrier :=
  P.integral

instance inclusion_isImmersion (P : IntegralSmoothGeometricPiece f) :
    IsImmersion P.inclusion := P.immersion

instance structureMap_isSmooth (P : IntegralSmoothGeometricPiece f) :
    Smooth (P.inclusion ≫ f) := P.smooth

/-- The actual locally closed image in the ambient scheme. -/
def support (P : IntegralSmoothGeometricPiece f) : Set X := Set.range P.inclusion

theorem isLocallyClosed_support (P : IntegralSmoothGeometricPiece f) :
    IsLocallyClosed P.support := P.inclusion.isLocallyClosed_range

theorem support_nonempty (P : IntegralSmoothGeometricPiece f) : P.support.Nonempty :=
  Set.range_nonempty _

theorem isIrreducible_support (P : IntegralSmoothGeometricPiece f) :
    IsIrreducible P.support := by
  simpa only [IntegralSmoothGeometricPiece.support, Set.image_univ] using
    (IrreducibleSpace.isIrreducible_univ P.carrier).image P.inclusion
      P.inclusion.continuous.continuousOn

end IntegralSmoothStratification.IntegralSmoothGeometricPiece

/-- Every nonempty Noetherian reduced scheme contains a nonempty integral open. -/
theorem IntegralSmoothStratification.exists_integral_open [NoetherianSpace X] [Nonempty X] [IsReduced X] :
    ∃ U : X.Opens, Nonempty U ∧ IsIntegral U.toScheme := by
  obtain ⟨x⟩ := ‹Nonempty X›
  obtain ⟨o, ho, hne, hsubset⟩ :=
    NoetherianSpace.exists_isOpen_nonempty_subset_irreducibleComponent
      (irreducibleComponent x) (irreducibleComponent_mem_irreducibleComponents x)
  let U : X.Opens := ⟨o, ho⟩
  have hU : IsIrreducible (U : Set X) :=
    ⟨hne, isIrreducible_irreducibleComponent.isPreirreducible.open_subset ho hsubset⟩
  let : IrreducibleSpace U.toScheme := Subtype.irreducibleSpace hU
  exact ⟨U, inferInstance, isIntegral_of_irreducibleSpace_of_isReduced U.toScheme⟩

variable {K : Type u} [Field K] [PerfectField K]

/-- The canonical function-field dimension of an integral smooth piece. -/
def IntegralSmoothStratification.IntegralSmoothGeometricPiece.dimension {f : X ⟶ Spec (.of K)}
    (P : IntegralSmoothStratification.IntegralSmoothGeometricPiece f) : ℕ :=
  Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (P.inclusion ≫ f)

/-- The actual smooth locus of an integral open in a reduced closed subset,
included into that reduced closed scheme. -/
def IntegralSmoothStratification.integralOpenSmoothImmersion (Z : Closeds X) (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] (U : (ReducedClosed.reducedClosedScheme Z).Opens)
    [IsIntegral U.toScheme] :
    SmoothStratum.smoothStratum (U.ι ≫ ReducedClosed.reducedClosedStructureMap Z f) ⟶ ReducedClosed.reducedClosedScheme Z :=
  SmoothStratum.smoothStratumι (U.ι ≫ ReducedClosed.reducedClosedStructureMap Z f) ≫ U.ι

instance IntegralSmoothStratification.integralOpenSmoothImmersion_isOpenImmersion (Z : Closeds X)
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (U : (ReducedClosed.reducedClosedScheme Z).Opens) [IsIntegral U.toScheme] :
    IsOpenImmersion (IntegralSmoothStratification.integralOpenSmoothImmersion Z f U) := by
  unfold IntegralSmoothStratification.integralOpenSmoothImmersion
  infer_instance

/-- The integral smooth open piece, viewed as an actual locally closed piece
of the original ambient scheme. -/
def IntegralSmoothStratification.integralOpenSmoothPiece (Z : Closeds X) (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] (U : (ReducedClosed.reducedClosedScheme Z).Opens)
    [IsIntegral U.toScheme] : IntegralSmoothStratification.IntegralSmoothGeometricPiece f where
  carrier := SmoothStratum.smoothStratum (U.ι ≫ ReducedClosed.reducedClosedStructureMap Z f)
  inclusion := IntegralSmoothStratification.integralOpenSmoothImmersion Z f U ≫ ReducedClosed.reducedClosedι Z
  immersion := by infer_instance
  smooth := by
    dsimp only [IntegralSmoothStratification.integralOpenSmoothImmersion]
    rw [Category.assoc, Category.assoc]
    exact SmoothStratum.smoothStratumToBase_isSmooth (U.ι ≫ ReducedClosed.reducedClosedStructureMap Z f)
  integral := inferInstance

/-- Removing this actual open image leaves a closed subset of the ambient scheme. -/
def IntegralSmoothStratification.integralOpenSmoothRemainder (Z : Closeds X) (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] (U : (ReducedClosed.reducedClosedScheme Z).Opens)
    [IsIntegral U.toScheme] : Closeds X :=
  ⟨(ReducedClosed.reducedClosedι Z) '' (Set.range (IntegralSmoothStratification.integralOpenSmoothImmersion Z f U))ᶜ,
    (ReducedClosed.reducedClosedι Z).isClosedEmbedding.isClosedMap _
      (IntegralSmoothStratification.integralOpenSmoothImmersion Z f U).isOpenEmbedding.isOpen_range.isClosed_compl⟩

@[simp]
theorem IntegralSmoothStratification.integralOpenSmoothPiece_support (Z : Closeds X) (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] (U : (ReducedClosed.reducedClosedScheme Z).Opens)
    [IsIntegral U.toScheme] :
    (IntegralSmoothStratification.integralOpenSmoothPiece Z f U).support =
      (ReducedClosed.reducedClosedι Z) '' Set.range (IntegralSmoothStratification.integralOpenSmoothImmersion Z f U) := by
  change Set.range ((ReducedClosed.reducedClosedι Z) ∘ (IntegralSmoothStratification.integralOpenSmoothImmersion Z f U)) = _
  exact Set.range_comp _ _

theorem IntegralSmoothStratification.integralOpenSmoothPiece_union_remainder (Z : Closeds X)
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (U : (ReducedClosed.reducedClosedScheme Z).Opens) [IsIntegral U.toScheme] :
    (IntegralSmoothStratification.integralOpenSmoothPiece Z f U).support ∪
      (IntegralSmoothStratification.integralOpenSmoothRemainder Z f U : Set X) = Z := by
  rw [IntegralSmoothStratification.integralOpenSmoothPiece_support]
  change (ReducedClosed.reducedClosedι Z) '' Set.range (IntegralSmoothStratification.integralOpenSmoothImmersion Z f U) ∪
    (ReducedClosed.reducedClosedι Z) '' (Set.range (IntegralSmoothStratification.integralOpenSmoothImmersion Z f U))ᶜ = _
  rw [Set.image_union_image_compl_eq_range, ReducedClosed.range_reducedClosedι]

theorem IntegralSmoothStratification.integralOpenSmoothPiece_disjoint_remainder (Z : Closeds X)
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (U : (ReducedClosed.reducedClosedScheme Z).Opens) [IsIntegral U.toScheme] :
    Disjoint (IntegralSmoothStratification.integralOpenSmoothPiece Z f U).support
      (IntegralSmoothStratification.integralOpenSmoothRemainder Z f U : Set X) := by
  rw [IntegralSmoothStratification.integralOpenSmoothPiece_support]
  apply (Set.disjoint_image_iff (ReducedClosed.reducedClosedι Z).isClosedEmbedding.injective).mpr
  exact disjoint_compl_right

theorem IntegralSmoothStratification.integralOpenSmoothRemainder_lt (Z : Closeds X)
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (U : (ReducedClosed.reducedClosedScheme Z).Opens) [IsIntegral U.toScheme] :
    IntegralSmoothStratification.integralOpenSmoothRemainder Z f U < Z := by
  have hcover := IntegralSmoothStratification.integralOpenSmoothPiece_union_remainder Z f U
  apply lt_of_le_not_ge
  · intro x hx
    change x ∈ (Z : Set X)
    rw [← hcover]
    exact Or.inr hx
  · intro hge
    obtain ⟨x, hx⟩ := (IntegralSmoothStratification.integralOpenSmoothPiece Z f U).support_nonempty
    have hxZ : x ∈ (Z : Set X) := hcover ▸ Or.inl hx
    exact (Set.disjoint_left.mp (IntegralSmoothStratification.integralOpenSmoothPiece_disjoint_remainder Z f U))
      hx (hge hxZ)

/-- Taking the smooth locus of this integral open preserves its actual
function-field dimension. -/
theorem IntegralSmoothStratification.integralOpenSmoothPiece_dimension (Z : Closeds X)
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (U : (ReducedClosed.reducedClosedScheme Z).Opens) [IsIntegral U.toScheme] :
    (IntegralSmoothStratification.integralOpenSmoothPiece Z f U).dimension =
      Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (U.ι ≫ ReducedClosed.reducedClosedStructureMap Z f) := by
  change Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension
    (((SmoothStratum.smoothStratumι (U.ι ≫ ReducedClosed.reducedClosedStructureMap Z f) ≫ U.ι) ≫
      ReducedClosed.reducedClosedι Z) ≫ f) = _
  simpa only [Category.assoc, ReducedClosed.reducedClosedStructureMap] using
    Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion
      (SmoothStratum.smoothStratumι (U.ι ≫ ReducedClosed.reducedClosedStructureMap Z f))
      (U.ι ≫ ReducedClosed.reducedClosedStructureMap Z f)

/-- The underlying union of a finite list of integral smooth pieces. -/
def IntegralSmoothStratification.integralSmoothPiecesSupport {f : X ⟶ Y} :
    List (IntegralSmoothStratification.IntegralSmoothGeometricPiece f) → Set X
  | [] => ∅
  | P :: Ps => P.support ∪ integralSmoothPiecesSupport Ps

theorem IntegralSmoothStratification.support_subset_integralSmoothPiecesSupport {f : X ⟶ Y}
    {P : IntegralSmoothStratification.IntegralSmoothGeometricPiece f} {Ps : List (IntegralSmoothStratification.IntegralSmoothGeometricPiece f)}
    (hP : P ∈ Ps) : P.support ⊆ IntegralSmoothStratification.integralSmoothPiecesSupport Ps := by
  induction Ps with
  | nil => simp at hP
  | cons Q Qs ih =>
      rcases List.mem_cons.mp hP with h | h
      · subst P
        exact Set.subset_union_left
      · exact Set.Subset.trans (ih h) Set.subset_union_right

/-- The boundary of each piece is contained in the union of the later pieces. -/
def IntegralSmoothStratification.integralSmoothPiecesFrontier {f : X ⟶ Y} :
    List (IntegralSmoothStratification.IntegralSmoothGeometricPiece f) → Prop
  | [] => True
  | P :: Ps => closure P.support \ P.support ⊆ IntegralSmoothStratification.integralSmoothPiecesSupport Ps ∧
      integralSmoothPiecesFrontier Ps

/-- A finite disjoint cover by actual integral smooth locally closed schemes,
ordered so that each piece's boundary is contained in the remaining pieces. -/
structure IntegralSmoothStratification.IntegralSmoothGeometricStratification (f : X ⟶ Y) (S : Set X) where
  pieces : List (IntegralSmoothStratification.IntegralSmoothGeometricPiece f)
  disjoint : pieces.Pairwise (fun P Q => Disjoint P.support Q.support)
  cover : IntegralSmoothStratification.integralSmoothPiecesSupport pieces = S
  frontier : IntegralSmoothStratification.integralSmoothPiecesFrontier pieces

namespace IntegralSmoothStratification.IntegralSmoothGeometricStratification

variable {f : X ⟶ Y}

/-- The empty closed subset has its empty stratification. -/
def empty : IntegralSmoothGeometricStratification f ∅ where
  pieces := []
  disjoint := List.Pairwise.nil
  cover := rfl
  frontier := True.intro

/-- Adjoin an integral smooth piece to a stratified closed remainder. -/
def cons {S T : Set X} (P : IntegralSmoothGeometricPiece f)
    (Q : IntegralSmoothGeometricStratification f T) (hd : Disjoint P.support T)
    (hc : P.support ∪ T = S) (hcl : closure P.support ⊆ S) :
    IntegralSmoothGeometricStratification f S where
  pieces := P :: Q.pieces
  disjoint := List.pairwise_cons.mpr ⟨fun R hR => hd.mono_right (by
    rw [← Q.cover]
    exact support_subset_integralSmoothPiecesSupport hR), Q.disjoint⟩
  cover := by
    change P.support ∪ IntegralSmoothStratification.integralSmoothPiecesSupport Q.pieces = S
    rw [Q.cover]
    exact hc
  frontier := ⟨by
    rw [Q.cover]
    intro x hx
    have hxS := hcl hx.1
    rw [← hc] at hxS
    exact hxS.resolve_left hx.2, Q.frontier⟩

/-- Every chosen piece lies in the prescribed underlying set. -/
theorem piece_support_subset {S : Set X} (Q : IntegralSmoothGeometricStratification f S)
    {P : IntegralSmoothGeometricPiece f} (hP : P ∈ Q.pieces) : P.support ⊆ S := by
  rw [← Q.cover]
  exact support_subset_integralSmoothPiecesSupport hP

end IntegralSmoothStratification.IntegralSmoothGeometricStratification

/-- Every closed subset of a Noetherian finite-type scheme over a perfect field
admits a finite disjoint stratification by actual integral smooth schemes. -/
theorem IntegralSmoothStratification.nonempty_integralSmoothGeometricStratification_closed [NoetherianSpace X]
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] (Z : Closeds X) :
    Nonempty (IntegralSmoothStratification.IntegralSmoothGeometricStratification f (Z : Set X)) := by
  apply wellFounded_lt.induction Z
  clear Z
  intro Z ih
  by_cases hZ : Z = ⊥
  · subst Z
    exact ⟨IntegralSmoothStratification.IntegralSmoothGeometricStratification.empty⟩
  · let : NoetherianSpace (ReducedClosed.reducedClosedScheme Z) :=
      (ReducedClosed.reducedClosedι Z).isClosedEmbedding.isEmbedding.isInducing.noetherianSpace
    let : Nonempty (ReducedClosed.reducedClosedScheme Z) :=
      ReducedClosed.reducedClosedScheme_nonempty Z (Closeds.coe_nonempty.mpr hZ)
    obtain ⟨U, _, hU⟩ := IntegralSmoothStratification.exists_integral_open (X := ReducedClosed.reducedClosedScheme Z)
    let : IsIntegral U.toScheme := hU
    obtain ⟨Q⟩ := ih (IntegralSmoothStratification.integralOpenSmoothRemainder Z f U)
      (IntegralSmoothStratification.integralOpenSmoothRemainder_lt Z f U)
    have hc := IntegralSmoothStratification.integralOpenSmoothPiece_union_remainder Z f U
    refine ⟨IntegralSmoothStratification.IntegralSmoothGeometricStratification.cons (IntegralSmoothStratification.integralOpenSmoothPiece Z f U) Q
      (IntegralSmoothStratification.integralOpenSmoothPiece_disjoint_remainder Z f U) hc ?_⟩
    apply closure_minimal _ Z.isClosed
    intro x hx
    rw [← hc]
    exact Or.inl hx

/-- The finite-type hypotheses imply the required topological Noetherianity. -/
theorem IntegralSmoothStratification.nonempty_integralSmoothGeometricStratification_of_finiteType
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] [QuasiCompact f] :
    Nonempty (IntegralSmoothStratification.IntegralSmoothGeometricStratification f Set.univ) := by
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  let : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  let : IsNoetherian X := ⟨⟩
  exact IntegralSmoothStratification.nonempty_integralSmoothGeometricStratification_closed f ⊤

/-- Choose only after proving existence of the actual finite stratification. -/
def IntegralSmoothStratification.integralSmoothGeometricStratification_of_finiteType
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] [QuasiCompact f] :
    IntegralSmoothStratification.IntegralSmoothGeometricStratification f Set.univ :=
  Classical.choice (IntegralSmoothStratification.nonempty_integralSmoothGeometricStratification_of_finiteType f)

/-- Genuine dimension-graded cycle supports, including singular supports, admit
a finite stratification by integral smooth locally closed schemes. -/
def DimensionCycles.DimensionCycleSupport.integralSmoothGeometricStratification
    {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ} (Z : DimensionCycles.DimensionCycleSupport V p) :
    IntegralSmoothStratification.IntegralSmoothGeometricStratification Z.structureMap Set.univ :=
  IntegralSmoothStratification.integralSmoothGeometricStratification_of_finiteType Z.structureMap

end

end OAI.AlgebraicGeometry.CycleClass.Geometric
end ComponentSource_16

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.IntegralSmoothStratification"

@[expose] public section ComponentSource_17
/- Original module: OAI.AlgebraicGeometry.Foundations.Scheme.StrictTranscendenceDrop -/

/-! # Strict Transcendence Drop -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.StrictTranscendenceDrop

noncomputable section

/-!
# Strict transcendence-degree drop under a proper prime quotient

A surjective homomorphism between domains of finite transcendence degree cannot
preserve transcendence degree while having a nonzero kernel. The proof lifts a
transcendence basis and uses the fact that an algebraic domain extension cannot
acquire a kernel when the map on its base remains injective.
-/

open Function _root_.Algebra Cardinal

universe u v w

variable {k : Type v} [Field k]
variable {A B : Type u} [CommRing A] [IsDomain A] [CommRing B]
variable [Algebra k A] [Algebra k B]

/-- If an algebra homomorphism preserves algebraic independence of a
transcendence basis of its domain, the homomorphism is injective. -/
theorem injective_of_transcendenceBasis_image_independent
    {ι : Type w} {x : ι → A} (f : A →ₐ[k] B)
    (hx : IsTranscendenceBasis k x)
    (hfx : AlgebraicIndependent k (f ∘ x)) : Function.Injective f := by
  let S := Algebra.adjoin k (Set.range x)
  let : Algebra A B := f.toRingHom.toAlgebra
  let : Algebra.IsAlgebraic S A := hx.isAlgebraic
  have heval : MvPolynomial.aeval (f ∘ x) = f.comp (MvPolynomial.aeval x) := by
    ext i
    simp
  have hinj : Function.Injective (algebraMap S B) := by
    intro a b hab
    obtain ⟨p, rfl⟩ := hx.1.aevalEquiv.surjective a
    obtain ⟨q, rfl⟩ := hx.1.aevalEquiv.surjective b
    have hpq : p = q := by
      apply hfx
      rw [heval]
      change f (MvPolynomial.aeval x p) = f (MvPolynomial.aeval x q)
      exact hab
    exact congrArg hx.1.aevalEquiv hpq
  change Function.Injective (algebraMap A B)
  exact Algebra.IsAlgebraic.injective_tower_top (R := S) A hinj

variable [IsDomain B]

/-- With finite transcendence degree, a surjective noninjective homomorphism of
domains strictly decreases transcendence degree. -/
theorem trdeg_lt_of_surjective_not_injective
    (f : A →ₐ[k] B) (hf : Function.Surjective f) (hni : ¬ Function.Injective f)
    (hfin : Algebra.trdeg k A < ℵ₀) : Algebra.trdeg k B < Algebra.trdeg k A := by
  apply lt_of_not_ge
  intro hge
  obtain ⟨s, hs⟩ := exists_isTranscendenceBasis k B
  choose x hx using (fun b : s => hf b.val)
  have hcomp : f ∘ x = (Subtype.val : s → B) := funext hx
  have hfx : AlgebraicIndependent k (f ∘ x) := by
    rw [hcomp]
    exact hs.1
  have hxind : AlgebraicIndependent k x := hfx.of_comp f
  have hxbasis : IsTranscendenceBasis k x :=
    hxind.isTranscendenceBasis_of_trdeg_le hfin
      (hge.trans_eq hs.cardinalMk_eq_trdeg.symm)
  exact hni (injective_of_transcendenceBasis_image_independent f hxbasis hfx)

/-- The finite-type version requires no separate transcendence-degree bound. -/
theorem trdeg_lt_of_surjective_not_injective_of_finiteType
    [Algebra.FiniteType k A] (f : A →ₐ[k] B)
    (hf : Function.Surjective f) (hni : ¬ Function.Injective f) :
    Algebra.trdeg k B < Algebra.trdeg k A :=
  trdeg_lt_of_surjective_not_injective f hf hni trdeg_lt_aleph0_of_finiteType

/-- A nonzero prime quotient of a finite-type domain has strictly smaller
transcendence degree over the coefficient field. -/
theorem trdeg_quotient_lt_of_prime_ne_bot [Algebra.FiniteType k A]
    (p : Ideal A) [p.IsPrime] (hp : p ≠ ⊥) :
    Algebra.trdeg k (A ⧸ p) < Algebra.trdeg k A := by
  apply trdeg_lt_of_surjective_not_injective_of_finiteType (Ideal.Quotient.mkₐ k p)
    Ideal.Quotient.mk_surjective
  intro hinj
  apply hp
  simpa using (RingHom.injective_iff_ker_eq_bot (Ideal.Quotient.mk p)).mp hinj

/-- The strict drop also holds for the transcendence degrees of the function
fields of the two domains. -/
theorem fractionRing_trdeg_quotient_lt_of_prime_ne_bot [Algebra.FiniteType k A]
    (p : Ideal A) [p.IsPrime] (hp : p ≠ ⊥) :
    Algebra.trdeg k (FractionRing (A ⧸ p)) < Algebra.trdeg k (FractionRing A) := by
  rw [← TranscendenceDegreeTransfer.trdeg_eq_fractionRing k (A ⧸ p), ← TranscendenceDegreeTransfer.trdeg_eq_fractionRing k A]
  exact trdeg_quotient_lt_of_prime_ne_bot p hp

/-- The natural-number version of strict transcendence-degree drop. Finiteness
comes from the finite-type hypothesis, so `Cardinal.toNat` loses no information. -/
theorem trdeg_toNat_quotient_lt_of_prime_ne_bot [Algebra.FiniteType k A]
    (p : Ideal A) [p.IsPrime] (hp : p ≠ ⊥) :
    (Algebra.trdeg k (A ⧸ p)).toNat < (Algebra.trdeg k A).toNat :=
  Cardinal.toNat_lt_toNat (trdeg_quotient_lt_of_prime_ne_bot p hp)
    trdeg_lt_aleph0_of_finiteType

/-- Strict inclusion of prime ideals reverses the transcendence degrees of
their quotient domains. The ambient finite-type ring need not be a domain. -/
theorem trdeg_quotient_lt_of_prime_lt
    {R : Type u} [CommRing R] [Algebra k R] [Algebra.FiniteType k R]
    {p q : Ideal R} [p.IsPrime] [q.IsPrime] (hpq : p < q) :
    Algebra.trdeg k (R ⧸ q) < Algebra.trdeg k (R ⧸ p) := by
  apply trdeg_lt_of_surjective_not_injective_of_finiteType
    (Ideal.Quotient.factorₐ k hpq.le) (Ideal.Quotient.factor_surjective hpq.le)
  intro hinj
  apply not_le_of_gt hpq
  intro a ha
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  apply hinj
  simpa only [Ideal.Quotient.factorₐ_apply_mk, map_zero] using
    (Ideal.Quotient.eq_zero_iff_mem.mpr ha : Ideal.Quotient.mk q a = 0)

/-- The natural-number dimension function obtained from transcendence degree
strictly decreases along strict inclusion of prime ideals. -/
theorem trdeg_toNat_quotient_lt_of_prime_lt
    {R : Type u} [CommRing R] [Algebra k R] [Algebra.FiniteType k R]
    {p q : Ideal R} [p.IsPrime] [q.IsPrime] (hpq : p < q) :
    (Algebra.trdeg k (R ⧸ q)).toNat < (Algebra.trdeg k (R ⧸ p)).toNat :=
  Cardinal.toNat_lt_toNat (trdeg_quotient_lt_of_prime_lt hpq)
    trdeg_lt_aleph0_of_finiteType

end

end OAI.AlgebraicGeometry.Foundations.Scheme.StrictTranscendenceDrop
end ComponentSource_17

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Foundations.Scheme.StrictTranscendenceDrop"

@[expose] public section ComponentSource_18
/- Original module: OAI.AlgebraicGeometry.Foundations.Scheme.SupportDimensionDrop -/

/-! # Support Dimension Drop -/

namespace OAI.AlgebraicGeometry.Foundations.Scheme.SupportDimensionDrop

noncomputable section

/-!
# Strict dimension drop for irreducible closed supports

The dimension of a support is computed in its actual function field. On an
ambient affine open this is the transcendence degree of the quotient by its
vanishing ideal. Strict inclusion of these prime ideals therefore gives strict
dimension drop, without substituting order-theoretic codimension for dimension.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

universe u

variable {K : Type u} [Field K] {X : Scheme.{u}}

/-- Strict inclusion of the actual prime ideals on a common nonempty affine
chart gives strict inequality of the dimensions of the two supports. -/
theorem supportTranscendenceDimension_lt_of_affineIdeal_lt
    (Z W : IrreducibleCloseds X) (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (U : X.affineOpens) [Nonempty (SupportAffineQuotient.supportAffineOpen Z U)]
    [Nonempty (SupportAffineQuotient.supportAffineOpen W U)]
    (h : (CycleClass.Geometric.GenericPoint.reducedSupportIdeal W).ideal U < (CycleClass.Geometric.GenericPoint.reducedSupportIdeal Z).ideal U) :
    SupportDimension.supportTranscendenceDimension Z f < SupportDimension.supportTranscendenceDimension W f := by
  let := SpecScalarTransport.specSectionScalarAlgebra f U
  let := AffineSectionFiniteType.specSectionScalarAlgebra_finiteType f U U.2
  let := SupportAffineQuotient.supportAffineIdeal_isPrime Z U
  let := SupportAffineQuotient.supportAffineIdeal_isPrime W U
  rw [SupportDimension.supportTranscendenceDimension_eq_affineQuotient Z f U,
    SupportDimension.supportTranscendenceDimension_eq_affineQuotient W f U]
  exact StrictTranscendenceDrop.trdeg_toNat_quotient_lt_of_prime_lt (k := K) h

/-- A proper irreducible closed subset of an irreducible closed support has
strictly smaller dimension over the base field. -/
theorem supportTranscendenceDimension_lt_of_lt
    (Z W : IrreducibleCloseds X) (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (hZW : Z < W) :
    SupportDimension.supportTranscendenceDimension Z f < SupportDimension.supportTranscendenceDimension W f := by
  obtain ⟨U, hZU, hWU⟩ := SupportAffineInclusion.exists_common_supportAffineOpen Z W hZW.le
  let := hZU
  let := hWU
  exact supportTranscendenceDimension_lt_of_affineIdeal_lt Z W f U
    (SupportAffineInclusion.supportAffineIdeal_lt Z W hZW U)

/-- Dimension is strictly increasing on irreducible closed supports ordered
by inclusion. -/
theorem supportTranscendenceDimension_strictMono
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] :
    StrictMono (fun Z : IrreducibleCloseds X => SupportDimension.supportTranscendenceDimension Z f) := by
  intro Z W hZW
  exact supportTranscendenceDimension_lt_of_lt Z W f hZW

end

end OAI.AlgebraicGeometry.Foundations.Scheme.SupportDimensionDrop
end ComponentSource_18

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Foundations.Scheme.SupportDimensionDrop"

@[expose] public section ComponentSource_19
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.StratumDimension -/

/-! # Stratum Dimension -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric

noncomputable section

/-!
# Native dimensions of smooth strata and singular boundaries

The bounds below concern the canonical transcendence dimensions of actual
function fields. A locally closed immersion is factored through its genuine
coborder open subscheme, where it is a closed immersion. The closed-immersion
inequality and the open-immersion equality give the bound for every integral
smooth stratum. Generic smoothness and strict dimension drop for proper
irreducible closed supports give the strict singular-boundary bound.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

universe u

variable {K : Type u} [Field K] {X Y : Scheme.{u}}

/-- The native natural-number dimension cannot increase under an actual
closed immersion of integral schemes locally of finite type over the field. -/
theorem StratumDimension.schemeTranscendenceDimension_closedImmersion_le [IsIntegral X] [IsIntegral Y]
    (i : Y ⟶ X) [IsClosedImmersion i] (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (i ≫ f) ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f := by
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra f
  let := Foundations.Scheme.FunctionFieldScalar.functionFieldScalarAlgebra (i ≫ f)
  apply (Nat.cast_le (α := Cardinal)).mp
  rw [Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_cast (i ≫ f), Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension_cast f]
  exact Foundations.Scheme.ClosedImmersionDimension.closedImmersion_functionField_trdeg_le i f

/-- An actual locally closed immersion between integral schemes cannot
increase native dimension. The factorization and both dimension comparisons
are constructed from the given immersion. -/
theorem StratumDimension.schemeTranscendenceDimension_immersion_le [IsIntegral X] [IsIntegral Y]
    (i : Y ⟶ X) [IsImmersion i] (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (i ≫ f) ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f := by
  let : Nonempty i.coborderRange := ⟨i.liftCoborder (genericPoint Y)⟩
  let : IsIntegral i.coborderRange.toScheme :=
    isIntegral_of_isOpenImmersion i.coborderRange.ι
  have h := StratumDimension.schemeTranscendenceDimension_closedImmersion_le i.liftCoborder
    (i.coborderRange.ι ≫ f)
  have he := Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion i.coborderRange.ι f
  simpa only [← Category.assoc, Scheme.Hom.liftCoborder_ι] using h.trans_eq he

/-- Every actual integral smooth stratum has dimension at most the dimension
of its integral ambient scheme. No dimension bound is stored in the piece. -/
theorem IntegralSmoothStratification.IntegralSmoothGeometricPiece.dimension_le [IsIntegral X]
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (P : IntegralSmoothStratification.IntegralSmoothGeometricPiece f) :
    P.dimension ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f :=
  StratumDimension.schemeTranscendenceDimension_immersion_le P.inclusion f

/-- The actual nonsmooth part of an integral support, viewed in the original
ambient scheme through its canonical closed immersion. -/
def StratumDimension.supportSingularBoundary (Z : IrreducibleCloseds X)
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] : Set X :=
  (GenericPoint.reducedSupportι Z) '' SingularLocus.singularLocus (SupportFiniteType.supportStructureMap Z f)

theorem StratumDimension.isClosed_supportSingularBoundary (Z : IrreducibleCloseds X)
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] :
    IsClosed (StratumDimension.supportSingularBoundary Z f) :=
  (GenericPoint.reducedSupportι Z).isClosedEmbedding.isClosedMap _
    (SingularLocus.isClosed_singularLocus (SupportFiniteType.supportStructureMap Z f))

theorem StratumDimension.supportSingularBoundary_subset (Z : IrreducibleCloseds X)
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] :
    StratumDimension.supportSingularBoundary Z f ⊆ (Z : Set X) := by
  intro x hx
  rw [← GenericPoint.range_reducedSupportι Z]
  obtain ⟨y, _, rfl⟩ := hx
  exact Set.mem_range_self y

variable [PerfectField K]

/-- Generic smoothness excludes the actual generic point of the support from
its singular boundary in the ambient scheme. -/
theorem StratumDimension.genericPoint_not_mem_supportSingularBoundary (Z : IrreducibleCloseds X)
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] :
    irreducibleSetEquivPoints Z ∉ StratumDimension.supportSingularBoundary Z f := by
  rw [← GenericPoint.reducedSupport_genericPoint_eq Z]
  rintro ⟨x, hx, he⟩
  have hxgen := (GenericPoint.reducedSupportι Z).isClosedEmbedding.injective he
  apply SingularLocus.genericPoint_not_mem_singularLocus (SupportFiniteType.supportStructureMap Z f)
  simpa only [hxgen] using hx

/-- Every irreducible closed support contained in the singular boundary is
properly contained in the original support. -/
theorem StratumDimension.lt_of_subset_supportSingularBoundary (W Z : IrreducibleCloseds X)
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (hW : (W : Set X) ⊆ StratumDimension.supportSingularBoundary Z f) : W < Z := by
  apply lt_of_le_not_ge (hW.trans (StratumDimension.supportSingularBoundary_subset Z f))
  intro hZW
  apply StratumDimension.genericPoint_not_mem_supportSingularBoundary Z f
  exact hW (hZW (Z.isIrreducible.isGenericPoint_genericPoint Z.isClosed).mem)

/-- A closed irreducible support lying in the actual singular boundary has
strictly smaller native dimension. -/
theorem StratumDimension.supportTranscendenceDimension_lt_of_subset_singularBoundary
    (W Z : IrreducibleCloseds X) (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f]
    (hW : (W : Set X) ⊆ StratumDimension.supportSingularBoundary Z f) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension W f < Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z f :=
  Foundations.Scheme.SupportDimensionDrop.supportTranscendenceDimension_lt_of_lt W Z f
    (StratumDimension.lt_of_subset_supportSingularBoundary W Z f hW)

/-- The genuine dense smooth stratum of an integral support has exactly the
dimension of that support, through the actual generic-stalk isomorphism. -/
theorem StratumDimension.smoothStratum_dimension_eq_support (Z : IrreducibleCloseds X)
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (SmoothStratum.smoothStratumToBase (SupportFiniteType.supportStructureMap Z f)) =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z f :=
  Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion
    (SmoothStratum.smoothStratumι (SupportFiniteType.supportStructureMap Z f)) (SupportFiniteType.supportStructureMap Z f)

variable {V : Foundations.Scheme.IntegralProjective.IntegralProjectiveVariety} {p : ℕ}

/-- Any integral smooth locally closed stratum of the actual support has
native dimension bounded by the support's own dimension. -/
theorem DimensionCycles.DimensionCycleSupport.stratum_dimension_le (Z : DimensionCycles.DimensionCycleSupport V p)
    (P : IntegralSmoothStratification.IntegralSmoothGeometricPiece Z.structureMap) :
    P.dimension ≤ Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z.1 V.structureMap :=
  P.dimension_le Z.structureMap

/-- The ambient codimension of the support converts the preceding bound to
the exact ambient dimension grading used for algebraic cycles. -/
theorem DimensionCycles.DimensionCycleSupport.stratum_dimension_add_codimension_le (Z : DimensionCycles.DimensionCycleSupport V p)
    (P : IntegralSmoothStratification.IntegralSmoothGeometricPiece Z.structureMap) :
    P.dimension + p ≤ Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension V.structureMap := by
  rw [← Z.dimension_add_codimension]
  exact Nat.add_le_add_right (Z.stratum_dimension_le P) p

/-- Singular-boundary supports have strictly greater ambient codimension than
the support whose singularities they lie in. -/
theorem DimensionCycles.DimensionCycleSupport.codimension_lt_of_subset_singularBoundary (Z : DimensionCycles.DimensionCycleSupport V p)
    (W : IrreducibleCloseds V.carrier)
    (hW : (W : Set V.carrier) ⊆ StratumDimension.supportSingularBoundary Z.1 V.structureMap) :
    p < DimensionCycles.dimensionCodimension V W := by
  have hlt := StratumDimension.supportTranscendenceDimension_lt_of_subset_singularBoundary
    W Z.1 V.structureMap hW
  have hZ := Z.dimension_add_codimension
  have hWdim := DimensionCycles.supportDimension_add_dimensionCodimension V W
  omega

end

end OAI.AlgebraicGeometry.CycleClass.Geometric
end ComponentSource_19

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.StratumDimension"

@[expose] public section ComponentSource_20
/- Original module: OAI.AlgebraicGeometry.CycleClass.Geometric.StratumClosure -/

/-! # Stratum Closure -/

namespace OAI.AlgebraicGeometry.CycleClass.Geometric

noncomputable section

/-!
# Reduced closures of integral locally closed strata

The scheme-theoretic image of a quasi-compact morphism from a reduced scheme
has radical ideal sheaf. For an integral source this identifies that image
with the actual reduced irreducible closure of its range. An immersion is
therefore a genuine open immersion into its reduced closure. This supplies
equality of their native dimensions and strict dimension bounds for strata
contained in singular loci.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

universe u

variable {X Y : Scheme.{u}}

/-- The kernel ideal sheaf of a quasi-compact map from a reduced scheme is
radical, because its affine section ideals are kernels into reduced rings. -/
theorem StratumClosure.kernel_radical_of_reduced [IsReduced Y] (i : Y ⟶ X) [QuasiCompact i] :
    i.ker.radical = i.ker := by
  ext U : 2
  simp only [Scheme.IdealSheafData.radical_ideal, Scheme.Hom.ker_apply]
  exact (Ideal.isRadical_bot.comap (i.app U).hom).radical

/-- The actual irreducible closed subset obtained by closing the image of an
integral scheme. -/
def StratumClosure.integralImageClosure [IsIntegral Y] (i : Y ⟶ X) : IrreducibleCloseds X :=
  ⟨closure (Set.range i), (by
    have hi : IsIrreducible (Set.range i) := by
      simpa only [Set.image_univ] using
        (IrreducibleSpace.isIrreducible_univ Y).image i i.continuous.continuousOn
    exact hi.closure), isClosed_closure⟩

@[simp]
theorem StratumClosure.integralImageClosure_coe [IsIntegral Y] (i : Y ⟶ X) :
    (StratumClosure.integralImageClosure i : Set X) = closure (Set.range i) := rfl

/-- The image ideal is precisely the vanishing ideal of the actual closure,
not merely an ideal with the same topological support. -/
theorem StratumClosure.kernel_eq_reducedImageClosureIdeal [IsIntegral Y] (i : Y ⟶ X)
    [QuasiCompact i] : i.ker = GenericPoint.reducedSupportIdeal (StratumClosure.integralImageClosure i) := by
  change i.ker = Scheme.IdealSheafData.vanishingIdeal
    ⟨closure (Set.range i), isClosed_closure⟩
  have hs : (⟨closure (Set.range i), isClosed_closure⟩ : Closeds X) = i.ker.support := by
    apply SetLike.coe_injective
    exact i.support_ker.symm
  rw [hs, Scheme.IdealSheafData.vanishingIdeal_support, StratumClosure.kernel_radical_of_reduced i]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- The actual scheme-theoretic image is canonically the reduced induced
scheme on the irreducible closure. -/
def StratumClosure.reducedImageClosureIso [IsIntegral Y] (i : Y ⟶ X) [QuasiCompact i] :
    i.image ≅ GenericPoint.reducedSupportScheme (StratumClosure.integralImageClosure i) where
  hom := Scheme.IdealSheafData.inclusion (StratumClosure.kernel_eq_reducedImageClosureIdeal i).ge
  inv := Scheme.IdealSheafData.inclusion (StratumClosure.kernel_eq_reducedImageClosureIdeal i).le
  hom_inv_id := by
    rw [Scheme.IdealSheafData.inclusion_comp]
    exact Scheme.IdealSheafData.inclusion_id _
  inv_hom_id := by
    rw [Scheme.IdealSheafData.inclusion_comp]
    exact Scheme.IdealSheafData.inclusion_id _

@[reassoc]
theorem StratumClosure.reducedImageClosureIso_hom_inclusion [IsIntegral Y] (i : Y ⟶ X)
    [QuasiCompact i] :
    (StratumClosure.reducedImageClosureIso i).hom ≫ GenericPoint.reducedSupportι (StratumClosure.integralImageClosure i) =
      i.imageι :=
  Scheme.IdealSheafData.inclusion_subschemeι _

/-- Factorization of the given map through its genuine reduced closure. -/
def StratumClosure.toReducedImageClosure [IsIntegral Y] (i : Y ⟶ X) [QuasiCompact i] :
    Y ⟶ GenericPoint.reducedSupportScheme (StratumClosure.integralImageClosure i) :=
  i.toImage ≫ (StratumClosure.reducedImageClosureIso i).hom

@[reassoc]
theorem StratumClosure.toReducedImageClosure_inclusion [IsIntegral Y] (i : Y ⟶ X)
    [QuasiCompact i] :
    StratumClosure.toReducedImageClosure i ≫ GenericPoint.reducedSupportι (StratumClosure.integralImageClosure i) = i := by
  rw [StratumClosure.toReducedImageClosure, Category.assoc, StratumClosure.reducedImageClosureIso_hom_inclusion,
    Scheme.Hom.toImage_imageι]

/-- A quasi-compact integral immersion is open in its actual reduced closure. -/
instance StratumClosure.toReducedImageClosure_isOpenImmersion [IsIntegral Y] (i : Y ⟶ X)
    [QuasiCompact i] [IsImmersion i] : IsOpenImmersion (StratumClosure.toReducedImageClosure i) := by
  unfold StratumClosure.toReducedImageClosure
  infer_instance

/-- This open factor has dense range in its irreducible reduced closure. -/
theorem StratumClosure.toReducedImageClosure_denseRange [IsIntegral Y] (i : Y ⟶ X)
    [QuasiCompact i] [IsImmersion i] : DenseRange (StratumClosure.toReducedImageClosure i) :=
  IsOpenMap.denseRange_of_isPreirreducibleSpace _
    (StratumClosure.toReducedImageClosure i).isOpenEmbedding.isOpenMap

variable {K : Type u} [Field K]

/-- The native dimension of an integral locally closed immersion equals that
of its genuine irreducible closed support. -/
theorem StratumClosure.schemeTranscendenceDimension_eq_imageClosure [IsIntegral Y] (i : Y ⟶ X)
    [QuasiCompact i] [IsImmersion i] (f : X ⟶ Spec (.of K)) :
    Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension (i ≫ f) =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (StratumClosure.integralImageClosure i) f := by
  have h := Foundations.Scheme.OpenFunctionField.schemeTranscendenceDimension_openImmersion
    (StratumClosure.toReducedImageClosure i) (SupportFiniteType.supportStructureMap (StratumClosure.integralImageClosure i) f)
  simpa only [SupportFiniteType.supportStructureMap, Foundations.Scheme.SupportDimension.supportTranscendenceDimension, ← Category.assoc,
    StratumClosure.toReducedImageClosure_inclusion] using h

section

variable {S : Scheme.{u}} {f : X ⟶ S}

/-- A stratum in a Noetherian ambient space is itself Noetherian. -/
instance IntegralSmoothStratification.IntegralSmoothGeometricPiece.carrier_noetherianSpace [NoetherianSpace X]
    (P : IntegralSmoothStratification.IntegralSmoothGeometricPiece f) : NoetherianSpace P.carrier :=
  P.inclusion.isEmbedding.isInducing.noetherianSpace

/-- The actual irreducible closure of a stratum's image. -/
def IntegralSmoothStratification.IntegralSmoothGeometricPiece.closureSupport (P : IntegralSmoothStratification.IntegralSmoothGeometricPiece f) : IrreducibleCloseds X :=
  StratumClosure.integralImageClosure P.inclusion

@[simp]
theorem IntegralSmoothStratification.IntegralSmoothGeometricPiece.closureSupport_coe (P : IntegralSmoothStratification.IntegralSmoothGeometricPiece f) :
    (P.closureSupport : Set X) = closure P.support := rfl

/-- The stratum as an actual open subscheme of its reduced irreducible closure. -/
def IntegralSmoothStratification.IntegralSmoothGeometricPiece.toReducedClosure [NoetherianSpace X] (P : IntegralSmoothStratification.IntegralSmoothGeometricPiece f) :
    P.carrier ⟶ GenericPoint.reducedSupportScheme P.closureSupport :=
  StratumClosure.toReducedImageClosure P.inclusion

instance IntegralSmoothStratification.IntegralSmoothGeometricPiece.toReducedClosure_isOpenImmersion [NoetherianSpace X]
    (P : IntegralSmoothStratification.IntegralSmoothGeometricPiece f) : IsOpenImmersion P.toReducedClosure :=
  inferInstanceAs (IsOpenImmersion (StratumClosure.toReducedImageClosure P.inclusion))

@[reassoc]
theorem IntegralSmoothStratification.IntegralSmoothGeometricPiece.toReducedClosure_inclusion [NoetherianSpace X]
    (P : IntegralSmoothStratification.IntegralSmoothGeometricPiece f) :
    P.toReducedClosure ≫ GenericPoint.reducedSupportι P.closureSupport = P.inclusion :=
  StratumClosure.toReducedImageClosure_inclusion P.inclusion

/-- The generic-stalk comparison preserves the actual base-field scalar map. -/
theorem IntegralSmoothStratification.IntegralSmoothGeometricPiece.dimension_eq_closure [NoetherianSpace X] {f : X ⟶ Spec (.of K)}
    (P : IntegralSmoothStratification.IntegralSmoothGeometricPiece f) :
    P.dimension = Foundations.Scheme.SupportDimension.supportTranscendenceDimension P.closureSupport f :=
  StratumClosure.schemeTranscendenceDimension_eq_imageClosure P.inclusion f

/-- A stratum contained in a closed irreducible support has its entire
irreducible closure in that support. -/
theorem IntegralSmoothStratification.IntegralSmoothGeometricPiece.closureSupport_le_of_support_subset {f : X ⟶ Spec (.of K)}
    (P : IntegralSmoothStratification.IntegralSmoothGeometricPiece f) (Z : IrreducibleCloseds X)
    (hP : P.support ⊆ (Z : Set X)) : P.closureSupport ≤ Z :=
  closure_minimal hP Z.isClosed

/-- The actual native dimension is bounded by any irreducible closed support
containing the stratum. -/
theorem IntegralSmoothStratification.IntegralSmoothGeometricPiece.dimension_le_of_support_subset [NoetherianSpace X]
    {f : X ⟶ Spec (.of K)} [LocallyOfFiniteType f]
    (P : IntegralSmoothStratification.IntegralSmoothGeometricPiece f) (Z : IrreducibleCloseds X)
    (hP : P.support ⊆ (Z : Set X)) :
    P.dimension ≤ Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z f := by
  rw [P.dimension_eq_closure]
  exact (Foundations.Scheme.SupportDimensionDrop.supportTranscendenceDimension_strictMono f).monotone
    (P.closureSupport_le_of_support_subset Z hP)

/-- Closing a stratum inside the closed singular boundary and using strict
dimension drop gives the bound for the actual locally closed carrier. -/
theorem IntegralSmoothStratification.IntegralSmoothGeometricPiece.dimension_lt_of_support_subset_singularBoundary [NoetherianSpace X]
    [PerfectField K] {f : X ⟶ Spec (.of K)} [LocallyOfFiniteType f]
    (P : IntegralSmoothStratification.IntegralSmoothGeometricPiece f) (Z : IrreducibleCloseds X)
    (hP : P.support ⊆ StratumDimension.supportSingularBoundary Z f) :
    P.dimension < Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z f := by
  rw [P.dimension_eq_closure]
  apply StratumDimension.supportTranscendenceDimension_lt_of_subset_singularBoundary P.closureSupport Z f
  exact closure_minimal hP (StratumDimension.isClosed_supportSingularBoundary Z f)

end

/-- A genuine irreducible closed subset of the singular locus has strictly
smaller native dimension than the integral ambient scheme itself. -/
theorem StratumClosure.supportTranscendenceDimension_lt_of_subset_singularLocus [IsIntegral X]
    [PerfectField K] (Z : IrreducibleCloseds X) (f : X ⟶ Spec (.of K))
    [LocallyOfFiniteType f] (hZ : (Z : Set X) ⊆ SingularLocus.singularLocus f) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z f < Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f := by
  let T : IrreducibleCloseds X :=
    ⟨Set.univ, IrreducibleSpace.isIrreducible_univ X, isClosed_univ⟩
  have hZT : Z < T := by
    apply lt_of_le_not_ge (Set.subset_univ _)
    intro hTZ
    exact SingularLocus.genericPoint_not_mem_singularLocus f (hZ (hTZ (Set.mem_univ _)))
  exact (Foundations.Scheme.SupportDimensionDrop.supportTranscendenceDimension_lt_of_lt Z T f hZT).trans_le
    (Foundations.Scheme.SupportDimension.supportTranscendenceDimension_le T f)

/-- Every actual integral locally closed smooth stratum contained in the
singular locus has strictly smaller native dimension. -/
theorem IntegralSmoothStratification.IntegralSmoothGeometricPiece.dimension_lt_of_support_subset_singularLocus
    [IsIntegral X] [NoetherianSpace X] [PerfectField K]
    {f : X ⟶ Spec (.of K)} [LocallyOfFiniteType f]
    (P : IntegralSmoothStratification.IntegralSmoothGeometricPiece f) (hP : P.support ⊆ SingularLocus.singularLocus f) :
    P.dimension < Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension f := by
  rw [P.dimension_eq_closure]
  apply StratumClosure.supportTranscendenceDimension_lt_of_subset_singularLocus P.closureSupport f
  exact closure_minimal hP (SingularLocus.isClosed_singularLocus f)

end

end OAI.AlgebraicGeometry.CycleClass.Geometric
end ComponentSource_20

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.CycleClass.Geometric.StratumClosure"

@[expose] public section ComponentSource_21
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.SupportImage -/

/-! # Support Image -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.SupportImage.BundleCycles

noncomputable section

/-!
# LineBundleCycles: actual support images under closed immersion

The image of a reduced integral support under a closed immersion is its
actual reduced image scheme. The induced morphism is an isomorphism, so
both the scheme structure and the support dimension are preserved.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X Y : Scheme} (i : X ⟶ Y) [IsClosedImmersion i]

/-- The actual reduced irreducible image of a support. -/
def closedImageSupport (W : IrreducibleCloseds X) : IrreducibleCloseds Y :=
  CycleClass.Geometric.StratumClosure.integralImageClosure (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ i)

theorem closedImageSupport_coe (W : IrreducibleCloseds X) :
    (closedImageSupport i W : Set Y) = i '' (W : Set X) := by
  change closure (Set.range (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ i)) = _
  have hr : Set.range (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ i) = i '' (W : Set X) := by
    change Set.range (i ∘ CycleClass.Geometric.GenericPoint.reducedSupportι W) = _
    rw [Set.range_comp, CycleClass.Geometric.GenericPoint.range_reducedSupportι]
  exact (congrArg closure hr).trans (i.isClosedEmbedding.isClosedMap _ W.isClosed).closure_eq

/-- The support itself is isomorphic to its reduced closed image. -/
def closedSupportImageIso (W : IrreducibleCloseds X) :
    CycleClass.Geometric.GenericPoint.reducedSupportScheme W ≅ CycleClass.Geometric.GenericPoint.reducedSupportScheme (closedImageSupport i W) := by
  let j := CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ i
  have he : IsIso (CycleClass.Geometric.StratumClosure.toReducedImageClosure j) := by
    change IsIso (j.toImage ≫ (CycleClass.Geometric.StratumClosure.reducedImageClosureIso j).hom)
    infer_instance
  exact @asIso _ _ _ _ (CycleClass.Geometric.StratumClosure.toReducedImageClosure j) he

theorem closedSupportImageIso_inclusion (W : IrreducibleCloseds X) :
    (closedSupportImageIso i W).hom ≫ CycleClass.Geometric.GenericPoint.reducedSupportι (closedImageSupport i W) =
      CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ i :=
  CycleClass.Geometric.StratumClosure.toReducedImageClosure_inclusion (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ i)

/-- The image is exactly the closure of the image of the original generic point. -/
theorem closedImageSupport_eq_pointClosure (W : IrreducibleCloseds X) :
    closedImageSupport i W = irreducibleSetEquivPoints.symm (i (irreducibleSetEquivPoints W)) := by
  apply IrreducibleCloseds.ext
  have h := (W.isIrreducible.isGenericPoint_genericPoint W.isClosed).image i.continuous
  have hc := h.def
  change closure {i (irreducibleSetEquivPoints W)} = closure (i '' (W : Set X)) at hc
  exact (closedImageSupport_coe i W).trans
    ((i.isClosedEmbedding.isClosedMap _ W.isClosed).closure_eq.symm.trans hc.symm)

theorem closedImageSupport_genericPoint (W : IrreducibleCloseds X) :
    irreducibleSetEquivPoints (closedImageSupport i W) = i (irreducibleSetEquivPoints W) :=
  (congrArg irreducibleSetEquivPoints (closedImageSupport_eq_pointClosure i W)).trans
    (irreducibleSetEquivPoints.apply_symm_apply _)

/-- Closed support images preserve the actual base-field dimension. -/
theorem closedImageSupport_dimension (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (W : IrreducibleCloseds X) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (closedImageSupport i W) f =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension W (i ≫ f) := by
  have h := CycleClass.Geometric.StratumClosure.schemeTranscendenceDimension_eq_imageClosure (CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ i) f
  change Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension ((CycleClass.Geometric.GenericPoint.reducedSupportι W ≫ i) ≫ f) =
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (closedImageSupport i W) f at h
  exact h.symm.trans
    (congrArg (fun g => Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension g) (Category.assoc _ _ _))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.SupportImage.BundleCycles
end ComponentSource_21

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.SupportImage"

@[expose] public section ComponentSource_22
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.CyclePushforward -/

/-! # Cycle Pushforward -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.CyclePushforward.BundleCycles

noncomputable section

/-!
# LineBundleCycles: closed-immersion pushforward on dimension-graded cycles

Each generic point maps to its actual image point. Closed immersions
preserve its reduced-support dimension and residue field, so the
pushforward keeps the original rational coefficient.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory

variable {X Y : Scheme} (i : X ⟶ Y) [IsClosedImmersion i]
    (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)

/-- The actual closed-immersion map on points in one dimension grade. -/
def closedDimensionPointMap (d : ℕ) : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (i ≫ f) d →
    Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d :=
  fun x => ⟨i x.1, (Point.SupportDimension.BundleCycles.pointClosure_dimension_closedImmersion i f x.1).trans x.2⟩

theorem closedDimensionPointMap_injective (d : ℕ) :
    Function.Injective (closedDimensionPointMap i f d) := by
  intro x y h
  exact Subtype.ext (i.isClosedEmbedding.injective (congrArg Subtype.val h))

/-- Pushforward of finite graded cycles along the actual closed immersion. -/
def closedDimensionCyclePushforward (d : ℕ) :
    (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (i ≫ f) d →₀ ℚ) →ₗ[ℚ] (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :=
  Finsupp.lmapDomain ℚ ℚ (closedDimensionPointMap i f d)

@[simp]
theorem closedDimensionCyclePushforward_single (d : ℕ)
    (x : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (i ≫ f) d) (q : ℚ) :
    closedDimensionCyclePushforward i f d (Finsupp.single x q) =
      Finsupp.single (closedDimensionPointMap i f d x) q :=
  Finsupp.mapDomain_single

/-- Forgetting the grading gives the full pushforward on all point coefficients. -/
theorem closedDimensionCyclePushforward_forget (d : ℕ)
    (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (i ≫ f) d →₀ ℚ) :
    Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d (closedDimensionCyclePushforward i f d z) =
      Finsupp.mapDomain i (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion (i ≫ f) d z) := by
  change Finsupp.mapDomain _ (Finsupp.mapDomain _ z) = Finsupp.mapDomain _ (Finsupp.mapDomain _ z)
  rw [← Finsupp.mapDomain_comp, ← Finsupp.mapDomain_comp]
  rfl

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.CyclePushforward.BundleCycles
end ComponentSource_22

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Closed.CyclePushforward"

@[expose] public section ComponentSource_23
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.ImmersionDimension -/

/-! # Immersion Dimension -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.ImmersionDimension.BundleCycles

noncomputable section

/-!
# LineBundleCycles: support dimension under locally closed immersion

The source support is open in its actual reduced image closure. The
generic-point image identifies that closure and the existing genuine
function-field comparison proves equality of dimensions.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X Y : Scheme} [AlgebraicGeometry.IsNoetherian X]
    (i : X ⟶ Y) [IsImmersion i]

omit [AlgebraicGeometry.IsNoetherian X] [IsImmersion i] in
/-- The reduced image closure of a point support is the closure of its actual image point. -/
theorem pointSupport_imageClosure (x : X) :
    CycleClass.Geometric.StratumClosure.integralImageClosure (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x) ≫ i) =
      irreducibleSetEquivPoints.symm (i x) := by
  apply IrreducibleCloseds.ext
  change closure (Set.range (i ∘ CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x))) = closure {i x}
  rw [Set.range_comp, CycleClass.Geometric.GenericPoint.range_reducedSupportι]
  change closure (i '' closure {x}) = closure {i x}
  rw [closure_image_closure i.continuous, Set.image_singleton]

/-- Locally closed immersion preserves the actual dimension of every reduced point closure. -/
theorem pointClosure_dimension_immersion (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (x : X) :
    Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm (i x)) f =
      Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) (i ≫ f) := by
  have h := CycleClass.Geometric.StratumClosure.schemeTranscendenceDimension_eq_imageClosure
    (CycleClass.Geometric.GenericPoint.reducedSupportι (irreducibleSetEquivPoints.symm x) ≫ i) f
  have himage := congrArg (fun Z => Foundations.Scheme.SupportDimension.supportTranscendenceDimension Z f) (pointSupport_imageClosure i x)
  exact himage.symm.trans (h.symm.trans
    (congrArg (fun g => Foundations.Scheme.TranscendenceDimension.schemeTranscendenceDimension g) (Category.assoc _ _ _)))

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.ImmersionDimension.BundleCycles
end ComponentSource_23

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.ImmersionDimension"

@[expose] public section ComponentSource_24
/- Original module: OAI.AlgebraicGeometry.Divisors.LineBundles.Open.CycleRestriction -/

/-! # Cycle Restriction -/

namespace OAI.AlgebraicGeometry.Divisors.LineBundles.Open.CycleRestriction.BundleCycles

noncomputable section

/-!
# LineBundleCycles: restriction of graded finite cycles to an open subscheme

The actual open immersion embeds the generic points without changing
support dimension. Restriction retains exactly the coefficients whose
generic points lie in the open. Extending finite cycles by zero gives a
section of this cycle-level restriction map.
-/

open _root_.AlgebraicGeometry _root_.CategoryTheory _root_.TopologicalSpace

variable {X Y : Scheme}

theorem schemeDimensionCycleInclusion_apply (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (d : ℕ)
    (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) (x : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d) :
    Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d z x.1 = z x :=
  Finsupp.mapDomain_apply_of_injective (Graded.GlobalSpecialization.BundleCycles.schemeDimensionPointEmbedding f d).injective z x

theorem schemeDimensionCycleInclusion_of_dimension_ne (f : X ⟶ Foundations.Scheme.ProjectiveSpace.complexBase) (d : ℕ)
    (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) (x : X)
    (hx : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) f ≠ d) :
    Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d z x = 0 := by
  apply Finsupp.mapDomain_of_notMem_range z x
  rintro ⟨y, hy⟩
  exact hx ((congrArg (fun q => Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm q) f)
    hy.symm).trans y.2)

variable [AlgebraicGeometry.IsNoetherian X] (i : X ⟶ Y) [IsOpenImmersion i]
    (f : Y ⟶ Foundations.Scheme.ProjectiveSpace.complexBase)

/-- The actual embedding of the dimension-graded generic points. -/
def openDimensionPointEmbedding (d : ℕ) :
    Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (i ≫ f) d ↪ Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d where
  toFun x := ⟨i x.1, (ImmersionDimension.BundleCycles.pointClosure_dimension_immersion i f x.1).trans x.2⟩
  inj' := fun _ _ h => Subtype.ext (i.isOpenEmbedding.injective (congrArg Subtype.val h))

/-- Coefficient restriction along the actual open immersion. -/
def openDimensionCycleRestriction (d : ℕ) :
    (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) →ₗ[ℚ] (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (i ≫ f) d →₀ ℚ) :=
  Finsupp.lcomapDomain (openDimensionPointEmbedding i f d) (openDimensionPointEmbedding i f d).injective

/-- Extension of a finite cycle by closing its generic points in the ambient scheme. -/
def openDimensionCycleExtension (d : ℕ) :
    (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (i ≫ f) d →₀ ℚ) →ₗ[ℚ] (Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :=
  Finsupp.lmapDomain ℚ ℚ (openDimensionPointEmbedding i f d)

theorem openDimensionCycleRestriction_extension (d : ℕ)
    (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (i ≫ f) d →₀ ℚ) :
    openDimensionCycleRestriction i f d (openDimensionCycleExtension i f d z) = z :=
  Finsupp.leftInverse_lcomapDomain_mapDomain (openDimensionPointEmbedding i f d)
    (openDimensionPointEmbedding i f d).injective z

theorem openDimensionCycleRestriction_surjective (d : ℕ) :
    Function.Surjective (openDimensionCycleRestriction i f d) :=
  fun z => ⟨openDimensionCycleExtension i f d z, openDimensionCycleRestriction_extension i f d z⟩

/-- Forgetting the grade recovers restriction of all actual point coefficients. -/
theorem openDimensionCycleRestriction_forget (d : ℕ) (z : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint f d →₀ ℚ) :
    Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion (i ≫ f) d (openDimensionCycleRestriction i f d z) =
      Finsupp.comapDomain i (Graded.GlobalSpecialization.BundleCycles.schemeDimensionCycleInclusion f d z) i.isOpenEmbedding.injective.injOn := by
  ext x
  by_cases hx : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm x) (i ≫ f) = d
  · let q : Graded.GlobalSpecialization.BundleCycles.SchemeDimensionCyclePoint (i ≫ f) d := ⟨x, hx⟩
    have h := schemeDimensionCycleInclusion_apply (i ≫ f) d (openDimensionCycleRestriction i f d z) q
    have hy := schemeDimensionCycleInclusion_apply f d z (openDimensionPointEmbedding i f d q)
    exact h.trans hy.symm
  · have hi : Foundations.Scheme.SupportDimension.supportTranscendenceDimension (irreducibleSetEquivPoints.symm (i x)) f ≠ d :=
      fun h => hx ((ImmersionDimension.BundleCycles.pointClosure_dimension_immersion i f x).symm.trans h)
    exact (schemeDimensionCycleInclusion_of_dimension_ne (i ≫ f) d _ x hx).trans
      (schemeDimensionCycleInclusion_of_dimension_ne f d z (i x) hi).symm

end

end OAI.AlgebraicGeometry.Divisors.LineBundles.Open.CycleRestriction.BundleCycles
end ComponentSource_24

run_cmd Lean.logInfo "COMPONENT_SOURCE_END: OAI.AlgebraicGeometry.Divisors.LineBundles.Open.CycleRestriction"


set_option pp.explicit false
set_option pp.proofs false
set_option pp.deepTerms false
set_option maxHeartbeats 0

open Lean Elab Command in
run_cmd do
  let env := (← getEnv).setExporting false
  let opts ← getOptions
  if true && env.header.trustLevel != 0 then
    throwError "The final environment has nonzero kernel trust level"
  if Lean.debug.skipKernelTC.get opts then
    throwError "The final environment disabled kernel type checking"
  if Lean.Elab.inServer.get opts then
    throwError "The final environment unexpectedly uses server mode"
  let required : Array (Name × String) := #[
    (`OAI.AlgebraicGeometry.Divisors.LineBundles.Open.CycleRestriction.BundleCycles.openDimensionCycleRestriction_forget, "theorem")
  ]
  let localNames := env.checked.get.constants.foldStage2 (fun acc name _ => acc.push name) (#[] : Array Name)
  if localNames.isEmpty then throwError "Empty authored declaration audit"
  let mut names := localNames
  for (name, _) in required do
    unless names.contains name do names := names.push name
  let mut rows : Array Json := #[]
  for name in names do
    let some info := env.checked.get.find? name | throwError "Missing checked declaration {name}"
    let kind := match info with
      | .thmInfo _ => "theorem"
      | .defnInfo _ => "definition"
      | .opaqueInfo _ => "opaque"
      | .axiomInfo _ => "axiom"
      | .inductInfo _ => "inductive"
      | .ctorInfo _ => "constructor"
      | .recInfo _ => "recursor"
      | .quotInfo _ => "quotient primitive"
    if kind == "axiom" then throwError "Authored axiom {name}"
    let value := info.value? (allowOpaque := true)
    if kind == "theorem" || kind == "definition" || kind == "opaque" then
      unless value.isSome do throwError "No actual body {name}"
    for (requiredName, expectedKind) in required do
      if name == requiredName && kind != expectedKind then
        throwError "Endpoint kind mismatch {name}: expected {expectedKind}, got {kind}"
    let axioms ← collectAxioms name
    for ax in axioms do
      if ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound then
        throwError "Unapproved transitive axiom {name}: {ax}"
    let mut fields := [("name", toJson name.toString), ("kind", toJson kind),
      ("actual_body_available", toJson value.isSome),
      ("universe_parameters", toJson (info.levelParams.map Name.toString)),
      ("type_dependencies", toJson (info.type.getUsedConstants.map Name.toString)),
      ("body_dependencies", toJson ((value.map Expr.getUsedConstants).getD #[] |>.map Name.toString)),
      ("transitive_axioms", toJson (axioms.map Name.toString))]
    if required.any (fun e => e.1 == name) then
      let typeText ← liftTermElabM <| return (← Meta.ppExpr info.type).pretty
      fields := fields ++ [("readable_type", toJson typeText)]
    rows := rows.push (Json.mkObj fields)
  IO.FS.createDirAll ".lake/reports"
  let path := ".lake/reports/" ++ (← getEnv).mainModule.toString ++ ".json"
  IO.FS.writeFile path (Json.mkObj [("accepted", toJson true),
    ("nonce", toJson "99732b8ebd468a569d345c0afc6dd79b"), ("declaration_count", toJson localNames.size),
    ("kernel_trust_level", toJson env.header.trustLevel.toNat),
    ("kernel_type_checking_enabled", toJson (!Lean.debug.skipKernelTC.get opts)),
    ("server_mode", toJson (Lean.Elab.inServer.get opts)),
    ("required_endpoint_count", toJson required.size),
    ("all_new_declarations_read_from_checked_environment", toJson true),
    ("declarations", toJson rows)]).pretty
  logInfo "LITERAL_COMPONENT_KERNEL_AUDIT_COMPLETE:99732b8ebd468a569d345c0afc6dd79b"
