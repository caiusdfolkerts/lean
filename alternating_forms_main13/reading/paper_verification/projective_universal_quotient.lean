module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.LocalTriviality
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import PaperVerification.SheafUnitPivotKernel
public import PaperVerification.SheafFiniteCoordinates

/-!
# The universal quotient on an actual projective spectrum

Degree-one homogeneous elements give genuine sections of the original
twisting sheaf. If their basic opens cover the projective spectrum, the
associated map from a free module sheaf onto `O(1)` is an epimorphism.
The proof uses local chart generators and sheaf separation. In particular,
it constructs the universal quotient on polynomial projective space over
any commutative ring, with every rank allowed.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace PaperVerification.ProjectiveUniversalQuotient

variable {A σ I : Type} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  {𝒜 : ℕ → σ} [GradedRing 𝒜]

/-- The compatible family of sections represented by `a/1`. -/
def homogeneousSection (a : 𝒜 1) : (Proj.twistingSheaf 𝒜 (1 : ℤ)).sections :=
  PresheafOfModules.sectionsMk
    (fun U => Proj.toTwistingSheaf 𝒜 (n := (1 : ℤ)) rfl U.unop a)
    (fun _ _ _ => rfl)

/-- Evaluation of degree-one homogeneous generators, as a morphism of
actual sheaves of modules on `Proj`. -/
def quotientMap (a : I → 𝒜 1) :
    SheafOfModules.free (R := (Proj 𝒜).ringCatSheaf) I ⟶
      Proj.twistingSheaf 𝒜 (1 : ℤ) :=
  (SheafOfModules.freeHomEquiv _).symm (fun i => homogeneousSection (a i))

lemma quotientMap_freeSection (a : I → 𝒜 1) (i : I) (U : (Proj 𝒜).Opens) :
    Scheme.Modules.Hom.app (X := Proj 𝒜) (quotientMap a) U
        ((SheafOfModules.freeSection (R := (Proj 𝒜).ringCatSheaf) i).val (op U)) =
      Proj.toTwistingSheaf 𝒜 (n := (1 : ℤ)) rfl U (a i) := by
  exact congrArg (fun s : (Proj.twistingSheaf 𝒜 (1 : ℤ)).sections => s.val (op U))
    (SheafOfModules.sectionsMap_freeHomEquiv_symm_freeSection
      (fun i => homogeneousSection (a i)) i)

lemma homogeneousSection_eq_chartGenerator (a : 𝒜 1)
    (U : (Proj 𝒜).Opens) (hU : U ≤ Proj.basicOpen 𝒜 (a : A)) :
    Proj.toTwistingSheaf 𝒜 (n := (1 : ℤ)) rfl U a =
      Proj.twistingSheaf.chartGenerator 1 (a : A) a.property U hU := by
  apply Proj.twistingSheaf.ext
  intro x
  simp only [Proj.toTwistingSheaf_apply_apply, Proj.twistingSheaf.chartGenerator_apply]
  congr 1 <;> first | rfl | (apply Subtype.ext; simp) | simp

/-- A covering family of degree-one coordinates generates the actual
twisting sheaf in degree one. -/
theorem quotientMap_epi (a : I → 𝒜 1)
    (hcover : (⨆ i, Proj.basicOpen 𝒜 (a i : A)) = ⊤) : Epi (quotientMap a) := by
  constructor
  intro N f g hfg
  apply Scheme.Modules.hom_ext
  intro U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  let F : TopCat.Sheaf AddCommGrpCat (Proj 𝒜) := ⟨N.val.presheaf, N.isSheaf⟩
  let W : I → (Proj 𝒜).Opens := fun i => U ⊓ Proj.basicOpen 𝒜 (a i : A)
  refine F.eq_of_locally_eq' W U (fun i => homOfLE inf_le_left) ?_ _ _ ?_
  · change U ≤ ⨆ i, U ⊓ Proj.basicOpen 𝒜 (a i : A)
    rw [← inf_iSup_eq, hcover, inf_top_eq]
  · intro i
    let j : W i ⟶ U := homOfLE inf_le_left
    have hi : (Scheme.Modules.Hom.app (X := Proj 𝒜) f (W i)) (Proj.toTwistingSheaf 𝒜 rfl (W i) (a i)) =
        (Scheme.Modules.Hom.app (X := Proj 𝒜) g (W i)) (Proj.toTwistingSheaf 𝒜 rfl (W i) (a i)) := by
      have h := congrArg (fun q => Scheme.Modules.Hom.app (X := Proj 𝒜) q (W i)
        ((SheafOfModules.freeSection (R := (Proj 𝒜).ringCatSheaf) i).val (op (W i)))) hfg
      change Scheme.Modules.Hom.app (X := Proj 𝒜) f (W i)
          (Scheme.Modules.Hom.app (X := Proj 𝒜) (quotientMap a) (W i)
            ((SheafOfModules.freeSection (R := (Proj 𝒜).ringCatSheaf) i).val (op (W i)))) =
        Scheme.Modules.Hom.app (X := Proj 𝒜) g (W i)
          (Scheme.Modules.Hom.app (X := Proj 𝒜) (quotientMap a) (W i)
            ((SheafOfModules.freeSection (R := (Proj 𝒜).ringCatSheaf) i).val (op (W i)))) at h
      erw [quotientMap_freeSection] at h
      exact h
    erw [homogeneousSection_eq_chartGenerator (a i) (W i) inf_le_right] at hi
    obtain ⟨r, hr⟩ :=
      (Proj.twistingSheaf.chartSectionsLinearEquiv 1 (a i : A) (a i).property
        (W i) inf_le_right).surjective
          ((Proj.twistingSheaf 𝒜 (1 : ℤ)).presheaf.map j.op s)
    change N.val.presheaf.map j.op (Scheme.Modules.Hom.app (X := Proj 𝒜) f U s) = N.val.presheaf.map j.op (Scheme.Modules.Hom.app (X := Proj 𝒜) g U s)
    erw [← ConcreteCategory.congr_hom ((Scheme.Modules.Hom.mapPresheaf (X := Proj 𝒜) f).naturality j.op) s,
      ← ConcreteCategory.congr_hom ((Scheme.Modules.Hom.mapPresheaf (X := Proj 𝒜) g).naturality j.op) s]
    change Scheme.Modules.Hom.app (X := Proj 𝒜) f (W i) ((Proj.twistingSheaf 𝒜 (1 : ℤ)).presheaf.map j.op s) =
      Scheme.Modules.Hom.app (X := Proj 𝒜) g (W i) ((Proj.twistingSheaf 𝒜 (1 : ℤ)).presheaf.map j.op s)
    erw [← hr, Proj.twistingSheaf.chartSectionsLinearEquiv_apply,
      Scheme.Modules.Hom.app_smul, Scheme.Modules.Hom.app_smul, hi]

section FiniteCoordinates

variable [Fintype I]

/-- The same universal quotient, expressed on the actual finite product
`O^I` used by the kernel and local-frame APIs. -/
def powerQuotient (a : I → 𝒜 1) :
    SheafModulePowers.structurePower (Proj 𝒜) I ⟶ Proj.twistingSheaf 𝒜 (1 : ℤ) :=
  SheafCoordinateMorphisms.fromSections _ (fun i => homogeneousSection (a i))

theorem powerQuotient_epi (a : I → 𝒜 1)
    (hcover : (⨆ i, Proj.basicOpen 𝒜 (a i : A)) = ⊤) : Epi (powerQuotient a) := by
  haveI := quotientMap_epi a hcover
  haveI : Epi (SheafFiniteCoordinates.freeToPower ≫ powerQuotient a) := by
    rw [powerQuotient, SheafFiniteCoordinates.freeToPower_fromSections]
    exact inferInstanceAs (Epi (quotientMap a))
  exact epi_of_epi SheafFiniteCoordinates.freeToPower (powerQuotient a)

/-- The original universal quotient has a free kernel on each coordinate
chart. Its inverse frame restores the omitted coordinate by the usual
negative weighted sum; the forward frame is actual coordinate projection. -/
def kernelFrameIso (a : Option I → 𝒜 1) :
    (kernel (powerQuotient a)).over (Proj.basicOpen 𝒜 (a none : A)) ≅
      (SheafModulePowers.structurePower (Proj 𝒜) I).over
        (Proj.basicOpen 𝒜 (a none : A)) :=
  SheafUnitPivotKernel.frameIso (Proj.twistingSheaf 𝒜 (1 : ℤ))
    (fun i => homogeneousSection (a i)) (Proj.basicOpen 𝒜 (a none : A))
    (fun V hV => Proj.twistingSheaf.chartSectionsLinearEquiv 1
      (a none : A) (a none).property V hV)
    (by
      intro V hV
      change Proj.twistingSheaf.chartSectionsLinearEquiv 1
        (a none : A) (a none).property V hV 1 =
          Proj.toTwistingSheaf 𝒜 rfl V (a none)
      rw [Proj.twistingSheaf.chartSectionsLinearEquiv_apply, one_smul]
      exact (homogeneousSection_eq_chartGenerator (a none) V hV).symm)

end FiniteCoordinates

section Polynomial

variable (R : Type) [CommRing R] (J : Type) [Fintype J] [DecidableEq J]

attribute [local instance] MvPolynomial.gradedAlgebra

/-- The coordinate generators of the ordinary polynomial projective
space, as degree-one homogeneous elements. -/
def polynomialCoordinates (j : J) : MvPolynomial.homogeneousSubmodule J R 1 :=
  ⟨MvPolynomial.X j, MvPolynomial.isHomogeneous_X R j⟩

theorem polynomialCoordinates_cover :
    (⨆ j, Proj.basicOpen (MvPolynomial.homogeneousSubmodule J R)
      (polynomialCoordinates R J j : MvPolynomial J R)) = ⊤ := by
  apply Proj.iSup_basicOpen_eq_top
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro n hn p hp
  rw [← Set.image_univ]
  apply MvPolynomial.mem_ideal_span_X_image.mpr
  intro d hd
  have hdeg : d.degree = n := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using
      hp (MvPolynomial.mem_support_iff.mp hd)
  by_contra! h
  have hzero : d = 0 := by
    ext j
    exact h j (Set.mem_univ j)
  rw [hzero, map_zero] at hdeg
  omega

/-- The genuine universal line quotient `O^J → O(1)` on polynomial
projective space, over every commutative coefficient ring. -/
theorem polynomialQuotient_epi : Epi (quotientMap (polynomialCoordinates R J)) :=
  quotientMap_epi _ (polynomialCoordinates_cover R J)

end Polynomial

end PaperVerification.ProjectiveUniversalQuotient
