module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.RingTheory.FiniteType

/-! # Literal projective structural maps

The structural map of a finite polynomial Proj is proper over its scalar
field. A graded morphism commutes with the degree-zero structural maps.
These facts keep the later toric embedding over the original base field.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u

namespace Unimodular.Projectivity
open AlgebraicGeometry CategoryTheory HomogeneousLocalization HomogeneousIdeal
open scoped Classical

section Graded
variable {A B σ τ : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  [CommRing B] [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (f : 𝒜 →+*ᵍ ℬ)

def gradeZeroMap : 𝒜 0 →+* ℬ 0 where
  toFun x := ⟨f x.val, f.map_mem x.property⟩
  map_one' := Subtype.ext (map_one f)
  map_mul' x y := Subtype.ext (map_mul f x.val y.val)
  map_zero' := Subtype.ext (map_zero f)
  map_add' x y := Subtype.ext (map_add f x.val y.val)

lemma awayMap_fromZero (s : A) (x : 𝒜 0) :
    Away.map f s (fromZeroRingHom 𝒜 (Submonoid.powers s) x) =
      fromZeroRingHom ℬ (Submonoid.powers (f s)) (gradeZeroMap f x) := by
  apply HomogeneousLocalization.val_injective
  simp [Away.map, fromZeroRingHom, HomogeneousLocalization.map_mk,
    HomogeneousLocalization.val_mk, gradeZeroMap, map_one]

/-- Actual morphism compatibility, not only compatibility on points. -/
theorem projMap_toSpecZero (hf : ℬ₊ ≤ 𝒜₊.map f) :
    Proj.map f hf ≫ Proj.toSpecZero 𝒜 =
      Proj.toSpecZero ℬ ≫ Spec.map (CommRingCat.ofHom (gradeZeroMap f)) := by
  apply (Proj.mapAffineOpenCover f hf).openCover.hom_ext
  intro s
  simp only [Scheme.AffineOpenCover.openCover_f, Proj.mapAffineOpenCover_f]
  rw [← Category.assoc, Proj.awayι_comp_map f hf s.1.2 _ s.2.2, Category.assoc,
    Proj.awayι_toSpecZero, ← Category.assoc, Proj.awayι_toSpecZero,
    ← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro x
  exact awayMap_fromZero f s.2 x
end Graded

section Polynomial
variable (k : Type u) [CommRing k] (ι : Type u)
attribute [local instance] MvPolynomial.gradedAlgebra

def polynomialGradeZeroScalarMap :
    k →+* MvPolynomial.homogeneousSubmodule ι k 0 where
  toFun a := ⟨MvPolynomial.C a, MvPolynomial.isHomogeneous_C ι a⟩
  map_one' := Subtype.ext MvPolynomial.C.map_one
  map_mul' a b := Subtype.ext (MvPolynomial.C.map_mul a b)
  map_zero' := Subtype.ext MvPolynomial.C.map_zero
  map_add' a b := Subtype.ext (MvPolynomial.C.map_add a b)

/-- The actual polynomial projective structural morphism over `k`. -/
def polynomialProjectiveToSpec :
    Proj (MvPolynomial.homogeneousSubmodule ι k) ⟶ Spec (CommRingCat.of k) :=
  Proj.toSpecZero (MvPolynomial.homogeneousSubmodule ι k) ≫
    Spec.map (CommRingCat.ofHom (polynomialGradeZeroScalarMap k ι))

theorem polynomialGradeZeroScalarMap_bijective :
    Function.Bijective (polynomialGradeZeroScalarMap k ι) := by
  constructor
  · intro x y h
    exact MvPolynomial.C_injective ι k (congrArg Subtype.val h)
  · intro x
    have hx : ∃ r : k, algebraMap k (MvPolynomial ι k) r = x.val := by
      simpa only [MvPolynomial.homogeneousSubmodule_zero, Submodule.mem_one] using x.property
    obtain ⟨r, hr⟩ := hx
    exact ⟨r, Subtype.ext hr⟩

instance polynomialGradeZeroScalarMap_isIso :
    IsIso (CommRingCat.ofHom (polynomialGradeZeroScalarMap k ι)) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (polynomialGradeZeroScalarMap_bijective k ι)

/-- Finite polynomial Proj is genuinely proper over the original field
(or, more generally, over any scalar ring). -/
instance polynomialProjectiveToSpec_isProper [Finite ι] :
    IsProper (polynomialProjectiveToSpec k ι) := by
  letI : Algebra k (MvPolynomial.homogeneousSubmodule ι k 0) := {
    toSMul := inferInstance
    algebraMap := polynomialGradeZeroScalarMap k ι
    commutes' := fun r x => mul_comm _ _
    smul_def' := by
      intro r x
      apply Subtype.ext
      exact Algebra.smul_def r x.val }
  letI : IsScalarTower k (MvPolynomial.homogeneousSubmodule ι k 0) (MvPolynomial ι k) := {
    smul_assoc := fun r x y => by
      rw [Algebra.smul_def (r • x) y, Algebra.smul_def x y,
        SetLike.GradeZero.algebraMap_apply, SetLike.GradeZero.algebraMap_apply,
        Submodule.coe_smul, smul_mul_assoc] }
  letI : Algebra.FiniteType (MvPolynomial.homogeneousSubmodule ι k 0) (MvPolynomial ι k) :=
    Algebra.FiniteType.of_restrictScalars_finiteType k _ _
  unfold polynomialProjectiveToSpec
  infer_instance

#print axioms projMap_toSpecZero
#print axioms polynomialProjectiveToSpec_isProper
end Polynomial
end Unimodular.Projectivity
