module

public import PaperVerification.HomogeneousBasisProfile
public import Mathlib.LinearAlgebra.Contraction
public import Mathlib.LinearAlgebra.TensorProduct.Basis

/-!
# Actual homogeneous multiplication rows and the tensor annihilator

The degree-one and degree-two bases restrict a genuine homogeneous augmented
basis to its actual homogeneous pieces. Multiplication is independently
defined by the original ring product. Its coefficient rows span exactly
the annihilator of its kernel, with the canonical tensor evaluation pairing.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical BigOperators TensorProduct

namespace PaperVerification.HomogeneousMultiplicationRows

open AugmentedAlgebraBasis

universe u
variable {K A I : Type u} [Field K] [Ring A] [Algebra K A] [Fintype I]
  (G : TauCeti.InternalGrading K A ℕ)
  (B : Module.Basis (Option I) K A) (δ : I → ℕ)
  (hzero : G.piece 0=(1 : Submodule K A)) (hunit : B none=1)
  (hhom : ∀ i,B (some i)∈G.piece (δ i))

/-- Literal homogeneous vectors form a basis of the actual piece. -/
def homogeneousBasis (d : ℕ) (hd : 0<d) :
    Module.Basis {i : I // δ i=d} K (G.piece d) :=
  (Module.Basis.span (B.linearIndependent.comp
    (fun i : {i : I // δ i=d} => some i.val)
    (fun i j h => Subtype.ext (Option.some.inj h)))).map
      (LinearEquiv.ofEq _ _
        (HomogeneousBasisProfile.span_degree G B δ hzero hunit hhom d hd))

@[simp] theorem homogeneousBasis_val (d : ℕ) (hd : 0<d)
    (i : {i : I // δ i=d}) :
    (homogeneousBasis G B δ hzero hunit hhom d hd i : A)=B (some i.val) := by
  simp only [homogeneousBasis,Module.Basis.map_apply,LinearEquiv.coe_ofEq_apply,
    Module.Basis.coe_span_apply,Function.comp_apply]

/-- Restricted dual coordinates are the original coefficients. -/
theorem homogeneousBasis_dual_eval (d : ℕ) (hd : 0<d)
    (i : {i : I // δ i=d}) (x : G.piece d) :
    (homogeneousBasis G B δ hzero hunit hhom d hd).dualBasis i x=
      B.repr x.val (some i.val) := by
  have he : (homogeneousBasis G B δ hzero hunit hhom d hd).dualBasis i=
      (B.coord (some i.val)).comp (G.piece d).subtype := by
    apply (homogeneousBasis G B δ hzero hunit hhom d hd).ext
    intro j
    rw [Module.Basis.dualBasis_apply_self]
    simp only [LinearMap.comp_apply,Submodule.subtype_apply,homogeneousBasis_val,
      Module.Basis.coord_apply,Module.Basis.repr_self,Finsupp.single_apply,
      Option.some.injEq,Subtype.ext_iff]
  rw [he]
  rfl

/-- Original multiplication, restricted only in its domain. -/
def multiplicationAmbient : (G.piece 1 ⊗[K] G.piece 1) →ₗ[K] A :=
  TensorProduct.lift ((LinearMap.mul K A).compl₁₂
    (G.piece 1).subtype (G.piece 1).subtype)

@[simp] theorem multiplicationAmbient_tmul (x y : G.piece 1) :
    multiplicationAmbient G (x ⊗ₜ[K] y)=x.val*y.val := rfl

variable (hmul : ∀ d e (x y : A),x∈G.piece d → y∈G.piece e → x*y∈G.piece (d+e))

include hmul in
theorem multiplicationAmbient_mem (z : G.piece 1 ⊗[K] G.piece 1) :
    multiplicationAmbient G z∈G.piece 2 := by
  induction z using TensorProduct.induction_on with
  | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
  | tmul x y =>
      rw [multiplicationAmbient_tmul]
      exact hmul 1 1 x.val y.val x.property y.property
  | add z w hz hw =>
      rw [map_add]
      exact Submodule.add_mem _ hz hw

/-- Actual multiplication into the actual degree-two piece. -/
def multiplication : (G.piece 1 ⊗[K] G.piece 1) →ₗ[K] G.piece 2 :=
  (multiplicationAmbient G).codRestrict (G.piece 2) (multiplicationAmbient_mem G hmul)

@[simp] theorem multiplication_val (z : G.piece 1 ⊗[K] G.piece 1) :
    (multiplication G hmul z : A)=multiplicationAmbient G z := rfl

@[simp] theorem multiplication_tmul_val (x y : G.piece 1) :
    (multiplication G hmul (x ⊗ₜ[K] y) : A)=x.val*y.val := rfl

theorem multiplication_eq_zero_iff (z : G.piece 1 ⊗[K] G.piece 1) :
    multiplication G hmul z=0 ↔ multiplicationAmbient G z=0 := by
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

/-- An actual degree-two coordinate pulled back by multiplication. -/
def row (c : {i : I // δ i=2}) :
    Module.Dual K (G.piece 1 ⊗[K] G.piece 1) :=
  (multiplication G hmul).dualMap
    ((homogeneousBasis G B δ hzero hunit hhom 2 (by decide)).dualBasis c)

theorem row_tmul (c : {i : I // δ i=2}) (x y : G.piece 1) :
    row G B δ hzero hunit hhom hmul c (x ⊗ₜ[K] y)=
      B.repr (x.val*y.val) (some c.val) := by
  change (homogeneousBasis G B δ hzero hunit hhom 2 (by decide)).dualBasis c
    (multiplication G hmul (x ⊗ₜ[K] y))=_
  rw [homogeneousBasis_dual_eval,multiplication_tmul_val]

/-- The entries are literally productCoefficients of the original basis. -/
theorem row_tmul_basis (c : {i : I // δ i=2})
    (a b : {i : I // δ i=1}) :
    row G B δ hzero hunit hhom hmul c
      (homogeneousBasis G B δ hzero hunit hhom 1 (by decide) a ⊗ₜ[K]
       homogeneousBasis G B δ hzero hunit hhom 1 (by decide) b)=
      productCoefficients B a.val b.val c.val := by
  rw [row_tmul,homogeneousBasis_val,homogeneousBasis_val]
  rfl

/-- Linear duality for an abstract module map, before specializing to grading data. -/
theorem span_range_dualMap_basis {V W J : Type*}
    [AddCommMonoid V] [Module K V] [AddCommMonoid W] [Module K W] [Finite J] [DecidableEq J]
    (f : V →ₗ[K] W) (b : Module.Basis J K W) :
    Submodule.span K (Set.range (fun j => f.dualMap (b.dualBasis j)))=
      (LinearMap.ker f).dualAnnihilator := by
  letI : AddCommGroup V := Module.addCommMonoidToAddCommGroup K
  letI : AddCommGroup W := Module.addCommMonoidToAddCommGroup K
  calc
    Submodule.span K (Set.range (fun j => f.dualMap (b.dualBasis j)))=
        (Submodule.span K (Set.range b.dualBasis)).map f.dualMap := by
      rw [Submodule.map_span,←Set.range_comp]
      rfl
    _ = LinearMap.range f.dualMap := by
      rw [b.dualBasis.span_eq,Submodule.map_top]
    _ = (LinearMap.ker f).dualAnnihilator :=
      LinearMap.range_dualMap_eq_dualAnnihilator_ker f

set_option maxHeartbeats 800000 in
/-- No surjectivity or rank hypothesis on multiplication is used. -/
theorem row_span_eq_dualAnnihilator :
    Submodule.span K (Set.range (row G B δ hzero hunit hhom hmul))=
      (LinearMap.ker (multiplication G hmul)).dualAnnihilator := by
  have h := span_range_dualMap_basis (K := K)
    (V := G.piece 1 ⊗[K] G.piece 1) (W := G.piece 2)
    (J := {i : I // δ i=2}) (multiplication G hmul)
    (homogeneousBasis G B δ hzero hunit hhom 2 (by decide))
  have hr : row G B δ hzero hunit hhom hmul =
      (fun c : {i : I // δ i=2} => (multiplication G hmul).dualMap
        ((homogeneousBasis G B δ hzero hunit hhom 2 (by decide)).dualBasis c)) := by
    funext c
    rfl
  exact (congrArg (fun f : {i : I // δ i=2} →
    Module.Dual K (G.piece 1 ⊗[K] G.piece 1) => Submodule.span K (Set.range f)) hr).trans h

/-- A literal coefficient row in the actual degree-one dual tensor square. -/
def tensorRow (c : {i : I // δ i=2}) :
    Module.Dual K (G.piece 1) ⊗[K] Module.Dual K (G.piece 1) :=
  ∑ a : {i : I // δ i=1},∑ b : {i : I // δ i=1},
    productCoefficients B a.val b.val c.val •
      ((homogeneousBasis G B δ hzero hunit hhom 1 (by decide)).dualBasis a ⊗ₜ[K]
       (homogeneousBasis G B δ hzero hunit hhom 1 (by decide)).dualBasis b)

/-- Canonical tensor evaluation identifies the coefficient row. -/
theorem dualDistrib_tensorRow (c : {i : I // δ i=2}) :
    TensorProduct.dualDistrib K (G.piece 1) (G.piece 1)
        (tensorRow G B δ hzero hunit hhom c)=
      row G B δ hzero hunit hhom hmul c := by
  apply ((homogeneousBasis G B δ hzero hunit hhom 1 (by decide)).tensorProduct
    (homogeneousBasis G B δ hzero hunit hhom 1 (by decide))).ext
  rintro ⟨a,b⟩
  rw [Module.Basis.tensorProduct_apply,row_tmul_basis]
  simp [tensorRow,TensorProduct.dualDistrib_apply,
    Module.Basis.dualBasis_apply_self,Finsupp.single_apply,smul_eq_mul,mul_ite,ite_mul]

/-- Equality with the conventional annihilator in the actual dual tensor square. -/
theorem tensorRow_span_eq_actual_annihilator :
    Submodule.span K (Set.range (tensorRow G B δ hzero hunit hhom))=
      (LinearMap.ker (multiplication G hmul)).dualAnnihilator.comap
        (TensorProduct.dualDistrib K (G.piece 1) (G.piece 1)) := by
  letI : Module.Finite K (G.piece 1) :=
    Module.Finite.of_basis (homogeneousBasis G B δ hzero hunit hhom 1 (by decide))
  have hi : Function.Injective (TensorProduct.dualDistrib K (G.piece 1) (G.piece 1)) := by
    rw [←TensorProduct.toLinearMap_dualDistribEquiv]
    exact (TensorProduct.dualDistribEquiv K (G.piece 1) (G.piece 1)).injective
  have hs : Function.Surjective (TensorProduct.dualDistrib K (G.piece 1) (G.piece 1)) := by
    rw [←TensorProduct.toLinearMap_dualDistribEquiv]
    exact (TensorProduct.dualDistribEquiv K (G.piece 1) (G.piece 1)).surjective
  apply Submodule.map_injective_of_injective hi
  rw [Submodule.map_comap_eq_of_surjective hs,Submodule.map_span,←Set.range_comp]
  have he :
      (fun c : {i : I // δ i=2} =>
        TensorProduct.dualDistrib K (G.piece 1) (G.piece 1)
          (tensorRow G B δ hzero hunit hhom c))=
        row G B δ hzero hunit hhom hmul := by
    funext c
    exact dualDistrib_tensorRow G B δ hzero hunit hhom hmul c
  simp only [Function.comp_def]
  rw [he]
  exact row_span_eq_dualAnnihilator G B δ hzero hunit hhom hmul

end PaperVerification.HomogeneousMultiplicationRows
