module

public import PaperVerification.SymmetricBasisDegree
public import PaperVerification.GradedProjScalarMap
public import OAI.AlgebraicGeometry.Divisors.LineBundles.SymmetricProjective.Scheme

/-!
# Free symmetric projective spectra are ordinary projective spaces

A basis gives the actual polynomial equivalence in every homogeneous degree.
The induced `Proj` isomorphism and its inverse preserve the original scalar
structure. No twisting sheaf, Chow group or cohomology comparison is required.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.SymmetricFreeProjectiveIso

open AlgebraicGeometry CategoryTheory Module
open OAI.AlgebraicGeometry.Divisors.LineBundles

variable {R M I : Type} [CommRing R] [AddCommGroup M] [Module R M]
attribute [local instance] MvPolynomial.gradedAlgebra

/-- The actual graded map determined by the chosen basis. -/
def toPolynomial (b : Basis I R M) :
    Symmetric.Grading.BundleCycles.symmetricGrading R M →+*ᵍ
      MvPolynomial.homogeneousSubmodule I R where
  __ := (SymmetricAlgebra.equivMvPolynomial b).toRingHom
  map_mem {n} {x} hx :=
    (SymmetricAlgebra.equivMvPolynomial_isHomogeneous_iff R M b n x).mpr hx

/-- Its inverse preserves the same homogeneous degree. -/
def fromPolynomial (b : Basis I R M) :
    MvPolynomial.homogeneousSubmodule I R →+*ᵍ
      Symmetric.Grading.BundleCycles.symmetricGrading R M where
  __ := (SymmetricAlgebra.equivMvPolynomial b).symm.toRingHom
  map_mem {n} {x} hx := by
    apply (SymmetricAlgebra.equivMvPolynomial_isHomogeneous_iff R M b n _).mp
    change ((SymmetricAlgebra.equivMvPolynomial b)
      ((SymmetricAlgebra.equivMvPolynomial b).symm x)).IsHomogeneous n
    rw [AlgEquiv.apply_symm_apply]
    exact hx

@[simp] theorem fromPolynomial_toPolynomial (b : Basis I R M) :
    (fromPolynomial b).comp (toPolynomial b) = GradedRingHom.id _ := by
  apply GradedRingHom.coe_ringHom_injective
  apply RingHom.ext
  intro x
  exact (SymmetricAlgebra.equivMvPolynomial b).symm_apply_apply x

@[simp] theorem toPolynomial_fromPolynomial (b : Basis I R M) :
    (toPolynomial b).comp (fromPolynomial b) = GradedRingHom.id _ := by
  apply GradedRingHom.coe_ringHom_injective
  apply RingHom.ext
  intro x
  exact (SymmetricAlgebra.equivMvPolynomial b).apply_symm_apply x

/-- The original projective schemes, identified through their genuine
homogeneous coordinate rings. -/
def projectiveIso (b : Basis I R M) :
    Proj (MvPolynomial.homogeneousSubmodule I R) ≅
      SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveScheme R M :=
  projIsoOfGradedAlgEquiv (SymmetricAlgebra.equivMvPolynomial b)
    (fun n x hx => (toPolynomial b).map_mem hx)
    (fun n x hx => (fromPolynomial b).map_mem hx)

theorem projectiveIso_hom_over (b : Basis I R M) :
    (projectiveIso b).hom ≫
      SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R M =
        gradedProjStructureMap (MvPolynomial.homogeneousSubmodule I R) :=
  projIsoOfGradedAlgEquiv_hom_over (SymmetricAlgebra.equivMvPolynomial b)
    (fun n x hx => (toPolynomial b).map_mem hx)
    (fun n x hx => (fromPolynomial b).map_mem hx)

theorem projectiveIso_inv_over (b : Basis I R M) :
    (projectiveIso b).inv ≫ gradedProjStructureMap (MvPolynomial.homogeneousSubmodule I R) =
      SymmetricProjective.Scheme.BundleCycles.symmetricProjectiveToBase R M := by
  rw [← projectiveIso_hom_over b, Iso.inv_hom_id_assoc]

end PaperVerification.SymmetricFreeProjectiveIso
