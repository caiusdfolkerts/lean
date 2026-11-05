module

public import PaperVerification.PolynomialDivergence
public import PaperVerification.KoszulSyzygies
public import Mathlib.Algebra.LieRinehartAlgebra.Subalgebra
public import Mathlib.LinearAlgebra.Pi

/-!
# The actual first two divergence--Koszul maps

The field module is an actual Lie--Rinehart subalgebra of polynomial
derivations.  Its closed one-form is polynomial-linear, as in the paper.
The divergence contribution is defined by coordinate partial derivatives.
The commutator identity and the zero composite of the corrected second
map are conclusions.  Ordered pairs avoid a division by two.

This source is a dependency of the general comparison theorem, not a
completed formalization of its degreewise or equivariant conclusions.
It has not yet been compiled.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.DivergenceCocycle

open MvPolynomial PolynomialDivergence
open scoped BigOperators

variable {K ι : Type*} [CommRing K] [Fintype ι]
local notation "P" => MvPolynomial ι K
local notation "Der" => Derivation K P P

variable (L : LieRinehartSubalgebra P Der)

/-- The literal closedness condition for the polynomial-linear one-form. -/
def IsClosed (ω : L →ₗ[P] P) : Prop :=
  ∀ X Y : L, ω ⁅X,Y⁆ = (X : Der) (ω Y) - (Y : Der) (ω X)

/-- The first map on the actual vector-field module. -/
def functional (ω : L →ₗ[P] P) (t : K) : L →ₗ[K] P :=
  t • (divergence.comp (L.toSubmodule.subtype.restrictScalars K)) +
    (1-t) • ω.restrictScalars K

@[simp] theorem functional_apply (ω : L →ₗ[P] P) (t : K) (X : L) :
    functional L ω t X = t • divergence (X : Der) + (1-t) • ω X := rfl

theorem functional_polynomial_smul (ω : L →ₗ[P] P) (t : K) (a : P) (X : L) :
    functional L ω t (a • X) = a * functional L ω t X + t • (X : Der) a := by
  change t • divergence (a • (X : Der)) + (1-t) • ω (a • X) = _
  rw [divergence_polynomial_smul,map_smul,functional_apply]
  simp only [smul_eq_mul,Algebra.smul_def,MvPolynomial.algebraMap_eq]
  ring

theorem functional_commutator (ω : L →ₗ[P] P) (hω : IsClosed L ω)
    (t : K) (X Y : L) :
    functional L ω t ⁅X,Y⁆ =
      (X : Der) (functional L ω t Y) - (Y : Der) (functional L ω t X) := by
  rw [functional_apply,LieRinehartSubalgebra.coe_bracket,
    divergence_commutator,hω X Y]
  simp only [functional_apply,map_add,map_smul,smul_sub]
  abel

/-- The paper's operator for a fixed field. -/
def operator (ω : L →ₗ[P] P) (t : K) (X : L) : P →ₗ[K] P :=
  LinearMap.mulLeft K (functional L ω t X) + t • (X : Der).toLinearMap

@[simp] theorem operator_apply (ω : L →ₗ[P] P) (t : K) (X : L) (p : P) :
    operator L ω t X p = functional L ω t X * p + t • (X : Der) p := rfl

/-- The operator equals the first map evaluated on the actual multiple. -/
theorem operator_eq_functional (ω : L →ₗ[P] P) (t : K) (X : L) (p : P) :
    operator L ω t X p = functional L ω t (p • X) := by
  rw [operator_apply,functional_polynomial_smul,mul_comm p]

theorem operator_polynomial_smul (ω : L →ₗ[P] P) (t : K)
    (a : P) (X : L) (p : P) :
    operator L ω t (a • X) p = operator L ω t X (a*p) := by
  rw [operator_eq_functional,operator_eq_functional,smul_smul]
  congr 1
  exact mul_comm p a

/-- Closedness produces the actual deformed commutator identity. -/
theorem operator_commutator (ω : L →ₗ[P] P) (hω : IsClosed L ω)
    (t : K) (X Y : L) (p : P) :
    operator L ω t X (operator L ω t Y p) -
      operator L ω t Y (operator L ω t X p) =
        t • operator L ω t ⁅X,Y⁆ p := by
  simp only [operator_apply,map_add,map_smul,Derivation.leibniz,smul_eq_mul,
    LieRinehartSubalgebra.coe_bracket,Derivation.commutator_apply]
  rw [functional_commutator L ω hω t X Y]
  simp only [Algebra.smul_def,MvPolynomial.algebraMap_eq]
  ring

variable {r : ℕ} (b : Module.Basis (Fin r) P L)

/-- The first map in basis coordinates, retaining its true differential
operator action on each coefficient. -/
def first (ω : L →ₗ[P] P) (t : K) : (Fin r → P) →ₗ[K] P where
  toFun v := ∑ i, operator L ω t (b i) (v i)
  map_add' v w := by simp only [Pi.add_apply,map_add,Finset.sum_add_distrib]
  map_smul' a v := by
    simp only [Pi.smul_apply,map_smul,Finset.smul_sum,RingHom.id_apply]

@[simp] theorem first_apply (ω : L →ₗ[P] P) (t : K) (v : Fin r → P) :
    first L b ω t v = ∑ i, operator L ω t (b i) (v i) := rfl

theorem first_eq_functional (ω : L →ₗ[P] P) (t : K) (v : Fin r → P) :
    first L b ω t v = functional L ω t (∑ i, v i • b i) := by
  simp only [first_apply,map_sum,operator_eq_functional]

/-- Basis independence is equality of the actual joint image with the
range of the actual first map on the whole vector-field module. -/
theorem range_first_eq (ω : L →ₗ[P] P) (t : K) :
    (first L b ω t).range = (functional L ω t).range := by
  ext p
  constructor
  · rintro ⟨v,rfl⟩
    exact ⟨∑ i, v i • b i,(first_eq_functional L b ω t v).symm⟩
  · rintro ⟨X,rfl⟩
    refine ⟨b.equivFun X,?_⟩
    rw [first_eq_functional,b.sum_equivFun]

/-- One corrected relation, valued in the actual vector-field module. -/
def elementarySecond (ω : L →ₗ[P] P) (t : K) (i j : Fin r) : P →ₗ[K] L where
  toFun p := operator L ω t (b j) p • b i -
    operator L ω t (b i) p • b j - t • (p • ⁅b i,b j⁆)
  map_add' p q := by
    simp only [map_add,add_smul,smul_add]
    abel
  map_smul' a p := by
    simp only [map_smul,smul_sub,smul_assoc,smul_comm a t]

@[simp] theorem elementarySecond_apply (ω : L →ₗ[P] P) (t : K)
    (i j : Fin r) (p : P) :
    elementarySecond L b ω t i j p = operator L ω t (b j) p • b i -
      operator L ω t (b i) p • b j - t • (p • ⁅b i,b j⁆) := rfl

theorem functional_elementarySecond (ω : L →ₗ[P] P) (hω : IsClosed L ω)
    (t : K) (i j : Fin r) (p : P) :
    functional L ω t (elementarySecond L b ω t i j p) = 0 := by
  rw [elementarySecond_apply,map_sub,map_sub,map_smul,
    ←operator_eq_functional,←operator_eq_functional,←operator_eq_functional,
    operator_commutator L ω hω,sub_self]

/-- Ordered pairs span the second Koszul term's image without a choice
of orientation and without dividing by two. -/
def second (ω : L →ₗ[P] P) (t : K) : (Fin r → Fin r → P) →ₗ[K] L where
  toFun A := ∑ i, ∑ j, elementarySecond L b ω t i j (A j i)
  map_add' A B := by simp only [Pi.add_apply,map_add,Finset.sum_add_distrib]
  map_smul' a A := by
    simp only [Pi.smul_apply,map_smul,Finset.smul_sum,RingHom.id_apply]

/-- The genuine first and second maps form a complex at every parameter. -/
theorem functional_comp_second (ω : L →ₗ[P] P) (hω : IsClosed L ω) (t : K) :
    (functional L ω t).comp (second L b ω t) = 0 := by
  ext A
  simp only [LinearMap.comp_apply,second,LinearMap.coe_mk,AddHom.coe_mk,
    map_sum,functional_elementarySecond L b ω hω,Finset.sum_const_zero,
    LinearMap.zero_apply]

/-- The undeformed first map is the actual Koszul coefficient map. -/
theorem functional_zero (ω : L →ₗ[P] P) (X : L) :
    functional L ω 0 X =
      KoszulSyzygies.coefficient (fun i => ω (b i)) (b.equivFun X) := by
  simp only [functional_apply,zero_smul,sub_zero,one_smul,zero_add,
    KoszulSyzygies.coefficient_apply]
  calc
    ω X = ω (∑ i, b.equivFun X i • b i) := congrArg ω (b.sum_equivFun X).symm
    _ = _ := by simp only [map_sum,map_smul,smul_eq_mul]

/-- In basis coordinates the undeformed second image is the literal
matrix form of the second Koszul differential. -/
theorem second_zero_coordinates (ω : L →ₗ[P] P) (A : Fin r → Fin r → P) :
    b.equivFun (second L b ω 0 A) =
      KoszulSyzygies.boundary (fun i => ω (b i)) A := by
  classical
  ext l
  simp only [second,LinearMap.coe_mk,AddHom.coe_mk,elementarySecond_apply,
    operator_apply,functional_apply,zero_smul,sub_zero,one_smul,zero_add,add_zero,
    map_sum,map_sub,map_smul,Finset.sum_apply,Pi.sub_apply,Pi.smul_apply,
    smul_eq_mul,Module.Basis.equivFun_self,Finset.sum_sub_distrib,
    KoszulSyzygies.boundary_apply,mul_sub]
  have hfirst : (∑ i, ∑ j, (ω (b j) * A j i) * (if i=l then 1 else 0)) =
      ∑ j, ω (b j) * A j l := by
    rw [Finset.sum_comm]
    simp
  have hsecond : (∑ i, ∑ j, (ω (b i) * A j i) * (if j=l then 1 else 0)) =
      ∑ i, ω (b i) * A l i := by simp
  simpa only [Finset.sum_sub_distrib] using congrArg₂ (·-·) hfirst hsecond

/-- Exactness at the undeformed point is derived from regularity of the
actual sequence of one-form values, through the checked Koszul library. -/
theorem zero_parameter_exact (ω : L →ₗ[P] P)
    (hregular : RingTheory.Sequence.IsWeaklyRegular P
      (List.ofFn fun i : Fin r => ω (b i))) :
    (second L b ω 0).range = (functional L ω 0).ker := by
  have he := KoszulSyzygies.kernel_eq_boundary_range
    (fun i : Fin r => ω (b i)) hregular
  ext X
  constructor
  · rintro ⟨A,rfl⟩
    apply LinearMap.mem_ker.mpr
    rw [functional_zero,second_zero_coordinates]
    exact KoszulSyzygies.coefficient_boundary _ A
  · intro hX
    have hz : b.equivFun X ∈ (KoszulSyzygies.coefficient (fun i => ω (b i))).ker := by
      apply LinearMap.mem_ker.mpr
      rw [←functional_zero]
      exact LinearMap.mem_ker.mp hX
    rw [he] at hz
    obtain ⟨A,hA⟩ := hz
    refine ⟨A,b.equivFun.injective ?_⟩
    rw [second_zero_coordinates]
    exact hA

end PaperVerification.DivergenceCocycle
