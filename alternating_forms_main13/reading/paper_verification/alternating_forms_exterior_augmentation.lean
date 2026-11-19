module

public import PaperVerification.AlternatingFormsExteriorFullBasis
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# The actual augmentation and original grading of an exterior quotient

The augmentation is induced by the exterior algebra's scalar projection.
The grading is the image of each genuine exterior power in the literal
ring quotient by the two quadratic relations. All comparison maps below
are constructed independently of any Hilbert function or Koszul property.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace PaperVerification.AlternatingForms.ExteriorAugmented

universe u
variable {K M : Type u} [CommRing K] [AddCommGroup M] [Module K M]

/-- The scalar projection kills every positive homogeneous exterior power. -/
theorem augmentation_homogeneous_zero {d : ℕ} (hd : 0<d)
    (x : ExteriorAlgebra K M) (hx : x∈⋀[K]^d M) :
    ExteriorAlgebra.algebraMapInv x=0 := by
  have h1 : (LinearMap.range (ExteriorAlgebra.ι K : M →ₗ[K] ExteriorAlgebra K M)).map
      (ExteriorAlgebra.algebraMapInv : ExteriorAlgebra K M →ₐ[K] K).toLinearMap=⊥ := by
    rw [←LinearMap.range_comp]
    change LinearMap.range ((ExteriorAlgebra.lift K
      ⟨(0 : M →ₗ[K] K),fun _ => by simp⟩).toLinearMap.comp (ExteriorAlgebra.ι K))=⊥
    rw [ExteriorAlgebra.ι_comp_lift,LinearMap.range_zero]
  have hm : ExteriorAlgebra.algebraMapInv x∈
      (⋀[K]^d M).map (ExteriorAlgebra.algebraMapInv : ExteriorAlgebra K M →ₐ[K] K).toLinearMap :=
    ⟨x,hx,rfl⟩
  rw [ExteriorAlgebra.exteriorPower,Submodule.map_pow,h1,
    Submodule.bot_pow (Nat.ne_of_gt hd)] at hm
  exact (Submodule.mem_bot K).mp hm

variable (f g : ⋀[K]^2 M)

abbrev Quotient := ExteriorAlgebra K M ⧸ exteriorRelationIdeal f g

/-- The actual coefficient-field augmentation of the full exterior quotient. -/
def augmentation : Quotient f g →ₐ[K] K :=
  Ideal.Quotient.liftₐ (exteriorRelationIdeal f g) ExteriorAlgebra.algebraMapInv (by
    change exteriorRelationIdeal f g≤
      RingHom.ker (ExteriorAlgebra.algebraMapInv : ExteriorAlgebra K M →ₐ[K] K).toRingHom
    apply Ideal.span_le.mpr
    rintro x (rfl | rfl)
    · exact augmentation_homogeneous_zero (by decide : 0<2) f.val f.property
    · exact augmentation_homogeneous_zero (by decide : 0<2) g.val g.property)

@[simp] theorem augmentation_mk (x : ExteriorAlgebra K M) :
    augmentation f g (Ideal.Quotient.mk (exteriorRelationIdeal f g) x)=
      ExteriorAlgebra.algebraMapInv x := rfl

/-- The original homogeneous grading on the actual ring quotient. -/
def grading : TauCeti.InternalGrading K (Quotient f g) ℕ :=
  (exteriorFullQuotientGrading f g).map
    (Submodule.Quotient.restrictScalarsEquiv K (exteriorRelationIdeal f g))

theorem grading_piece (d : ℕ) :
    (grading f g).piece d=(⋀[K]^d M).map
      (Ideal.Quotient.mkₐ K (exteriorRelationIdeal f g)).toLinearMap := by
  rw [grading,TauCeti.InternalGrading.map_piece,exteriorFullQuotientGrading_piece]
  ext x
  constructor
  · rintro ⟨y,⟨z,rfl⟩,rfl⟩
    exact ⟨z,z.property,rfl⟩
  · rintro ⟨z,hz,rfl⟩
    refine ⟨exteriorDegreeProjection f g d ⟨z,hz⟩,⟨⟨z,hz⟩,rfl⟩,?_⟩
    rfl

def degreeEquivPiece (d : ℕ) :
    ExteriorQuotientDegree f g d ≃ₗ[K] (grading f g).piece d := by
  rw [grading,TauCeti.InternalGrading.map_piece]
  exact (exteriorQuotientDegreeEquivFullPiece f g d).trans
    (Submodule.equivMapOfInjective
      (Submodule.Quotient.restrictScalarsEquiv K (exteriorRelationIdeal f g)).toLinearMap
      (Submodule.Quotient.restrictScalarsEquiv K (exteriorRelationIdeal f g)).injective
      ((exteriorFullQuotientGrading f g).piece d))

instance grading_piece_finite [Module.Finite K M] (d : ℕ) :
    Module.Finite K ((grading f g).piece d) :=
  Module.Finite.equiv (degreeEquivPiece f g d)

theorem grading_piece_finrank (d : ℕ) :
    Module.finrank K ((grading f g).piece d)=Module.finrank K (ExteriorQuotientDegree f g d) :=
  (degreeEquivPiece f g d).finrank_eq.symm

theorem grading_zero : (grading f g).piece 0=(1 : Submodule K (Quotient f g)) := by
  rw [grading_piece,ExteriorAlgebra.exteriorPower,pow_zero,Submodule.map_one]

theorem grading_mul (d e : ℕ) (x y : Quotient f g)
    (hx : x∈(grading f g).piece d) (hy : y∈(grading f g).piece e) :
    x*y∈(grading f g).piece (d+e) := by
  rw [grading_piece] at hx hy ⊢
  obtain ⟨a,ha,rfl⟩ := hx
  obtain ⟨b,hb,rfl⟩ := hy
  refine ⟨a*b,?_,map_mul (Ideal.Quotient.mkₐ K (exteriorRelationIdeal f g)) a b⟩
  exact SetLike.mul_mem_graded ha hb

theorem augmentation_piece_zero (d : ℕ) (hd : 0<d) (x : Quotient f g)
    (hx : x∈(grading f g).piece d) : augmentation f g x=0 := by
  rw [grading_piece] at hx
  obtain ⟨a,ha,rfl⟩ := hx
  exact augmentation_homogeneous_zero hd a ha

end PaperVerification.AlternatingForms.ExteriorAugmented
