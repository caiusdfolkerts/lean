module

public import PaperVerification.ModuleCatRingEquivTor
public import Mathlib.RingTheory.Ideal.Quotient.Basic

/-! # Concrete scalar and tensor formulas with opaque coefficient rings

These elementary identities avoid expanding a large algebra equivalence when
specializing actual projective resolutions. All maps are the existing scalar
restriction and balanced tensor maps, and every displayed formula is on the
original underlying elements.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped TensorProduct

namespace PaperVerification.ModuleCatRingEquivTor

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory

universe u

/-- The native ground-ring action agrees with restriction of scalars. -/
def nativeScalarsEquiv {R T : Type u} [CommRing R] [CommRing T] [Algebra R T]
    (B : Type u) [AddCommGroup B] [Module T B] [Module R B] [IsScalarTower R T B] :
    ((ModuleCat.restrictScalars (algebraMap R T)).obj (ModuleCat.of T B)) ≃ₗ[R] B :=
  (show B ≃ₗ[R] ((ModuleCat.restrictScalars (algebraMap R T)).obj (ModuleCat.of T B)) from
    { toFun x := x
      invFun x := x
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' c x := by
        change c • x=(algebraMap R T c) • x
        exact (IsScalarTower.algebraMap_smul T c x).symm }).symm

/-- Tensoring with a specified vector, using the actual balanced product. -/
def tensorWithVector {R : Type u} [CommRing R]
    (U V : ModuleCat.{u} R) (x : U) : V ⟶ U ⊗ V :=
  ModuleCat.ofHom (TensorProduct.mk R U V x)

/-- Actual homology of a complex whose differentials are proved zero. -/
def homologyIsoOfZeroDifferentials {R : Type u} [CommRing R]
    (C : ChainComplex (ModuleCat.{u} R) ℕ) (hd : ∀ i j, C.d i j=0) (r : ℕ) :
    C.homology r ≅ C.X r :=
  (ShortComplex.HomologyData.ofZeros (C.sc r) (hd _ _) (hd _ _)).left.homologyIso

variable {A D : Type u} [CommRing A] [CommRing D] (e : A ≃+* D)

/-- The changed coefficient-residue action is the original quotient product. -/
theorem scalarChange_quotient_smul (J : Ideal A) (d : D) (q : A ⧸ J) :
    d • (show (scalarChange e).obj (ModuleCat.of A (A ⧸ J)) from q) =
      (show (scalarChange e).obj (ModuleCat.of A (A ⧸ J)) from
        Ideal.Quotient.mk J (e.symm d)*q) := rfl

/-- Vanishing of actual tensor differentials is preserved by the explicit
balanced-tensor comparison of the changed projective resolution. -/
theorem resolutionTensor_d_eq_zero (X Y : ModuleCat.{u} A) (P : ProjectiveResolution Y)
    (hd : ∀ i j, ((((tensoringLeft (ModuleCat A)).obj X).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj P.complex).d i j=0) (i j : ℕ) :
    ((((tensoringLeft (ModuleCat D)).obj ((scalarChange e).obj X)).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj (resolution e P).complex).d i j=0 := by
  change (((tensoringLeft (ModuleCat D)).obj ((scalarChange e).obj X)).map
    ((scalarChange e).map (P.complex.d i j)))=0
  apply (cancel_mono (tensorIso e X (P.complex.X j)).hom).mp
  rw [zero_comp,tensorIso_naturality]
  change (tensorIso e X (P.complex.X i)).hom ≫
    (scalarChange e).map
      (((((tensoringLeft (ModuleCat A)).obj X).mapHomologicalComplex
        (ComplexShape.down ℕ)).obj P.complex).d i j)=0
  rw [hd, (scalarChange e).map_zero, comp_zero]

/-- The scalar associativity needed for the original exterior Koszul degree. -/
theorem associate_integer_smul {R M : Type*} [Monoid R] [AddCommGroup M]
    [DistribMulAction R M] (a b : R) (n : ℤ) (x : M) :
    a • b • (n • x)=n • ((a*b) • x) := by
  rw [←mul_smul,smul_comm]

end PaperVerification.ModuleCatRingEquivTor
