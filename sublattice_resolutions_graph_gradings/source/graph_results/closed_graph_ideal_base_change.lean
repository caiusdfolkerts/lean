module
public import graph_results.closed_graph_integral_model
public import graph_foundation.part012
public import Mathlib.RingTheory.TensorProduct.MvPolynomial

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.ClosedGraphIdealBaseChange -/
section

/-! # The actual ideal after arbitrary coefficient base change

Monic normal form gives a coefficient-linear retraction from the polynomial
ring onto the ideal. Tensoring this explicit retraction proves injectivity
without flatness. The image is the actual mapped polynomial ideal, because
it is closed under multiplication by every polynomial in the new ring.
The graph specialization therefore includes the noninjective map z ↦ 0.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 200000
set_option synthInstance.maxHeartbeats 5000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency true
noncomputable section

namespace FourPapers.Sublattice

open Classical MvPolynomial
open scoped TensorProduct

section GeneralIdeal
variable {R V : Type*} [CommRing R]
  (I : Ideal (MvPolynomial V R))
  (A : Type*) [CommRing A] [Algebra R A]

/-- Multiplication by an actual source polynomial, retaining the ideal. -/
def idealCoefficientMultiply (p : MvPolynomial V R) : I →ₗ[R] I where
  toFun f := p • f
  map_add' f g := smul_add p f g
  map_smul' r f := smul_comm p r f

@[simp] theorem idealCoefficientMultiply_val (p : MvPolynomial V R) (f : I) :
    (idealCoefficientMultiply I p f).val = p * f.val := rfl

/-- The literal polynomial inclusion, with the native ideal coefficient
module related explicitly to its scalar-restricted presentation. -/
def idealCoefficientInclusion : I →ₗ[R] MvPolynomial V R :=
  (I.restrictScalars R).subtype.comp (idealScalarRestrictionEquiv I).toLinearMap

@[simp] theorem idealCoefficientInclusion_apply (f : I) :
    idealCoefficientInclusion I f = f.val := rfl

/-- The canonical polynomial-valued map on a base-changed ideal. -/
def idealBaseChangePolynomialMap :
    (A ⊗[R] I) →ₗ[A] MvPolynomial V A :=
  (MvPolynomial.algebraTensorAlgEquiv R A).toLinearEquiv.toLinearMap.comp
    ((idealCoefficientInclusion I).baseChange A)

@[simp] theorem idealBaseChangePolynomialMap_tmul (a : A) (f : I) :
    idealBaseChangePolynomialMap I A (a ⊗ₜ[R] f) =
      a • MvPolynomial.map (algebraMap R A) f.val := by
  change MvPolynomial.algebraTensorAlgEquiv R A
    ((idealCoefficientInclusion I).baseChange A (a ⊗ₜ[R] f)) = _
  rw [LinearMap.baseChange_tmul]
  exact MvPolynomial.algebraTensorAlgEquiv_tmul R A a f.val

/-- Polynomial multiplication on the original ideal commutes with its
actual coefficient base-change map. -/
theorem idealBaseChangePolynomialMap_multiply (p : MvPolynomial V R)
    (x : A ⊗[R] I) :
    idealBaseChangePolynomialMap I A ((idealCoefficientMultiply I p).baseChange A x) =
      MvPolynomial.map (algebraMap R A) p * idealBaseChangePolynomialMap I A x := by
  have he : (idealBaseChangePolynomialMap I A).comp
      ((idealCoefficientMultiply I p).baseChange A) =
    (LinearMap.mulLeft A (MvPolynomial.map (algebraMap R A) p)).comp
      (idealBaseChangePolynomialMap I A) := by
    apply TensorProduct.AlgebraTensorModule.ext
    intro a f
    simp only [LinearMap.comp_apply, LinearMap.baseChange_tmul,
      idealBaseChangePolynomialMap_tmul, idealCoefficientMultiply_val,
      map_mul, LinearMap.mulLeft_apply, mul_smul_comm]
  exact LinearMap.congr_fun he x

theorem idealBaseChangePolynomialMap_mem (x : A ⊗[R] I) :
    idealBaseChangePolynomialMap I A x ∈ I.map (MvPolynomial.map (algebraMap R A)) := by
  induction x using TensorProduct.induction_on with
  | zero =>
      rw [map_zero]
      exact Ideal.zero_mem _
  | tmul a f =>
      rw [idealBaseChangePolynomialMap_tmul]
      exact ((I.map (MvPolynomial.map (algebraMap R A))).restrictScalars A).smul_mem a
        (Ideal.mem_map_of_mem _ f.property)
  | add x y hx hy =>
      rw [map_add]
      exact Ideal.add_mem _ hx hy

/-- The image is closed under every new polynomial multiplier. It is not
necessary for that polynomial, or its coefficients, to come from R. -/
theorem idealBaseChangePolynomialMap_range_mul (p : MvPolynomial V A)
    (x : MvPolynomial V A) (hx : x ∈ LinearMap.range (idealBaseChangePolynomialMap I A)) :
    p * x ∈ LinearMap.range (idealBaseChangePolynomialMap I A) := by
  obtain ⟨y, rfl⟩ := hx
  change (LinearMap.mulRight A (idealBaseChangePolynomialMap I A y)) p ∈
    LinearMap.range (idealBaseChangePolynomialMap I A)
  apply polynomialLinearMap_mem
  intro a _
  refine ⟨(idealCoefficientMultiply I (monomial a 1)).baseChange A y, ?_⟩
  rw [idealBaseChangePolynomialMap_multiply, MvPolynomial.map_monomial, map_one]
  rfl

def idealBaseChangeRange : Ideal (MvPolynomial V A) where
  carrier := LinearMap.range (idealBaseChangePolynomialMap I A)
  zero_mem' := (LinearMap.range (idealBaseChangePolynomialMap I A)).zero_mem
  add_mem' := (LinearMap.range (idealBaseChangePolynomialMap I A)).add_mem
  smul_mem' p x hx := idealBaseChangePolynomialMap_range_mul I A p x hx

theorem idealBaseChangeRange_eq :
    idealBaseChangeRange I A = I.map (MvPolynomial.map (algebraMap R A)) := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    exact idealBaseChangePolynomialMap_mem I A y
  · apply Ideal.map_le_iff_le_comap.mpr
    intro f hf
    change MvPolynomial.map (algebraMap R A) f ∈
      LinearMap.range (idealBaseChangePolynomialMap I A)
    refine ⟨1 ⊗ₜ[R] (⟨f,hf⟩ : I), ?_⟩
    rw [idealBaseChangePolynomialMap_tmul, one_smul]

/-- The canonical map has its literal mapped ideal as codomain. -/
def idealCoefficientBaseChangeMap :
    (A ⊗[R] I) →ₗ[A] I.map (MvPolynomial.map (algebraMap R A)) :=
  (idealScalarRestrictionEquiv (I.map (MvPolynomial.map (algebraMap R A)))).symm.toLinearMap.comp
    ((idealBaseChangePolynomialMap I A).codRestrict
      ((I.map (MvPolynomial.map (algebraMap R A))).restrictScalars A)
      (idealBaseChangePolynomialMap_mem I A))

@[simp] theorem idealCoefficientBaseChangeMap_val (x : A ⊗[R] I) :
    (idealCoefficientBaseChangeMap I A x).val = idealBaseChangePolynomialMap I A x := rfl

theorem idealCoefficientBaseChangeMap_surjective :
    Function.Surjective (idealCoefficientBaseChangeMap I A) := by
  intro f
  have hf : f.val ∈ idealBaseChangeRange I A := by
    rw [idealBaseChangeRange_eq]
    exact f.property
  obtain ⟨x,hx⟩ := hf
  exact ⟨x, Subtype.ext hx⟩

end GeneralIdeal

section MonicIdeal
variable {R V : Type*} [CommRing R] [Nontrivial R]
  (m : MonomialOrder V) (I : Ideal (MvPolynomial V R))
  (B : Set (MvPolynomial V R)) (hB : m.IsGroebnerBasis B I)
  (hu : ∀ f ∈ B, f ≠ 0 → IsUnit (m.leadingCoeff f))

/-- Monic normal form supplies an actual coefficient-linear splitting of
ideal inclusion. No projectivity theorem for an arbitrary ideal is invoked. -/
def groebnerIdealRetraction : MvPolynomial V R →ₗ[R] I :=
  (idealScalarRestrictionEquiv I).symm.toLinearMap.comp
    ((LinearMap.id - hB.normalForm hu).codRestrict (I.restrictScalars R)
      (hB.sub_normalForm_mem hu))

theorem groebnerIdealRetraction_inclusion :
    (groebnerIdealRetraction m I B hB hu).comp (idealCoefficientInclusion I) =
      LinearMap.id := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  change f.val - hB.normalForm hu f.val = f.val
  rw [(hB.normalForm_eq_zero_iff hu).mpr f.property, sub_zero]

variable (A : Type*) [CommRing A] [Algebra R A]

include hB hu in
theorem idealBaseChangePolynomialMap_injective :
    Function.Injective (idealBaseChangePolynomialMap I A) := by
  have hi : Function.Injective ((idealCoefficientInclusion I).baseChange A) := by
    have hr : ((groebnerIdealRetraction m I B hB hu).baseChange A).comp
        ((idealCoefficientInclusion I).baseChange A) = LinearMap.id := by
      rw [← LinearMap.baseChange_comp, groebnerIdealRetraction_inclusion,
        LinearMap.baseChange_id]
    have hf : Function.LeftInverse ((groebnerIdealRetraction m I B hB hu).baseChange A)
        ((idealCoefficientInclusion I).baseChange A) := fun x => LinearMap.congr_fun hr x
    exact hf.injective
  exact (MvPolynomial.algebraTensorAlgEquiv R A).injective.comp hi

include hB hu in
theorem idealCoefficientBaseChangeMap_injective :
    Function.Injective (idealCoefficientBaseChangeMap I A) := by
  intro x y h
  apply idealBaseChangePolynomialMap_injective m I B hB hu A
  exact congrArg Subtype.val h

/-- Arbitrary base change identifies the original ideal with the actual
extended ideal. In particular A may have torsion or may kill the parameter. -/
def groebnerIdealBaseChangeEquiv :
    (A ⊗[R] I) ≃ₗ[A] I.map (MvPolynomial.map (algebraMap R A)) :=
  LinearEquiv.ofBijective (idealCoefficientBaseChangeMap I A)
    ⟨idealCoefficientBaseChangeMap_injective m I B hB hu A,
      idealCoefficientBaseChangeMap_surjective I A⟩

@[simp] theorem groebnerIdealBaseChangeEquiv_tmul_val (a : A) (f : I) :
    (groebnerIdealBaseChangeEquiv m I B hB hu A (a ⊗ₜ[R] f)).val =
      a • MvPolynomial.map (algebraMap R A) f.val :=
  idealBaseChangePolynomialMap_tmul I A a f

theorem groebnerIdealBaseChangeEquiv_multiply (p : MvPolynomial V R)
    (x : A ⊗[R] I) :
    (groebnerIdealBaseChangeEquiv m I B hB hu A
      ((idealCoefficientMultiply I p).baseChange A x)).val =
        MvPolynomial.map (algebraMap R A) p *
          (groebnerIdealBaseChangeEquiv m I B hB hu A x).val :=
  idealBaseChangePolynomialMap_multiply I A p x

end MonicIdeal

section GraphSpecialization
variable {N : ℕ} {G : SimpleGraph (Fin N)} (hG : IntervalLabeling G) (s : ℕ)
  (A : Type*) [CommRing A] [Algebra GraphIntegralCoefficientRing A]

/-- Written in the original finite variable set, allowing the new
coefficient algebra to live in any universe. -/
def graphSpecializedParameterBinomial (t : A) (i j : Fin N) :
    MvPolynomial (GraphIntegralVariables N) A :=
  monomial (graphPairExponent i j) 1 -
    monomial (graphPairExponent j i) (t ^ (j.val-i.val))

def graphSpecializedParameterGenerators (t : A) (G : SimpleGraph (Fin N)) :
    Set (MvPolynomial (GraphIntegralVariables N) A) :=
  {f | ∃ i j, i < j ∧ G.Adj i j ∧ f = graphSpecializedParameterBinomial A t i j}

def graphSpecializedParameterIdeal (t : A) (G : SimpleGraph (Fin N)) :
    Ideal (MvPolynomial (GraphIntegralVariables N) A) :=
  Ideal.span (graphSpecializedParameterGenerators A t G)

/-- This is the displayed specialized ideal power, not a definition by
base change. The equality below proves the connection to the original family. -/
abbrev IntegralGraphSpecializedModule :=
  (graphSpecializedParameterIdeal A
    (algebraMap GraphIntegralCoefficientRing A Polynomial.X) G)^s

lemma graphIntegralGenerators_map :
    MvPolynomial.map (algebraMap GraphIntegralCoefficientRing A) ''
      graphParameterGenerators (Polynomial.X : Polynomial ℤ) G =
    graphSpecializedParameterGenerators A
      (algebraMap GraphIntegralCoefficientRing A Polynomial.X) G := by
  ext f
  constructor
  · rintro ⟨g, ⟨i,j,hij,hijG,rfl⟩,rfl⟩
    refine ⟨i,j,hij,hijG,?_⟩
    simp only [graphParameterBinomial, graphSpecializedParameterBinomial,
      map_sub, MvPolynomial.map_monomial, map_one, map_pow]
  · rintro ⟨i,j,hij,hijG,rfl⟩
    refine ⟨graphParameterBinomial Polynomial.X i j,
      ⟨i,j,hij,hijG,rfl⟩, ?_⟩
    simp only [graphParameterBinomial, graphSpecializedParameterBinomial,
      map_sub, MvPolynomial.map_monomial, map_one, map_pow]

theorem integralGraphIdeal_map :
    (integralGraphParameterData hG s).ideal.map
      (MvPolynomial.map (algebraMap GraphIntegralCoefficientRing A)) =
        IntegralGraphSpecializedModule (G := G) s A := by
  change ((graphParameterIdeal (Polynomial.X : Polynomial ℤ) G)^s).map _ =
    (graphSpecializedParameterIdeal A
      (algebraMap GraphIntegralCoefficientRing A Polynomial.X) G)^s
  simp only [Ideal.map_pow, graphParameterIdeal, Ideal.map_span,
    graphIntegralGenerators_map, graphSpecializedParameterIdeal]

/-- Every coefficient specialization preserves the literal ideal module,
including z=0, without assuming the coefficient algebra is flat. -/
def integralGraphIdealBaseChangeEquiv :
    (A ⊗[GraphIntegralCoefficientRing] IntegralGraphModule hG s) ≃ₗ[A]
      IntegralGraphSpecializedModule (G := G) s A :=
  (groebnerIdealBaseChangeEquiv (integralGraphParameterData hG s).order
    (integralGraphParameterData hG s).ideal (integralGraphParameterData hG s).generators
    (integralGraphParameterData hG s).groebner (integralGraphParameterData hG s).unitLeading A).trans
      ((LinearEquiv.ofEq _ _ (integralGraphIdeal_map hG s A)).restrictScalars A)

@[simp] theorem integralGraphIdealBaseChangeEquiv_tmul_val (a : A)
    (f : IntegralGraphModule hG s) :
    (integralGraphIdealBaseChangeEquiv hG s A (a ⊗ₜ[GraphIntegralCoefficientRing] f)).val =
      a • MvPolynomial.map (algebraMap GraphIntegralCoefficientRing A) f.val := by
  change (groebnerIdealBaseChangeEquiv (integralGraphParameterData hG s).order
    (integralGraphParameterData hG s).ideal (integralGraphParameterData hG s).generators
    (integralGraphParameterData hG s).groebner (integralGraphParameterData hG s).unitLeading A
      (a ⊗ₜ[GraphIntegralCoefficientRing] f)).val = _
  exact groebnerIdealBaseChangeEquiv_tmul_val _ _ _ _ _ A a f

/-- At parameter zero the displayed generators are exactly the edge
monomials, over every coefficient algebra. -/
theorem graphSpecializedParameterBinomial_zero {i j : Fin N} (hij : i < j) :
    graphSpecializedParameterBinomial A 0 i j = monomial (graphPairExponent i j) 1 := by
  have hpos : 0 < j.val-i.val := Nat.sub_pos_of_lt hij
  simp only [graphSpecializedParameterBinomial, zero_pow (ne_of_gt hpos),
    map_zero, sub_zero]

@[simp] theorem graphSpecializedParameterBinomial_one (i j : Fin N) :
    graphSpecializedParameterBinomial A 1 i j =
      monomial (graphPairExponent i j) 1 - monomial (graphPairExponent j i) 1 := by
  simp only [graphSpecializedParameterBinomial, one_pow]

theorem graphSpecializedParameterIdeal_zero :
    graphSpecializedParameterIdeal A 0 G =
      Ideal.span {f : MvPolynomial (GraphIntegralVariables N) A |
        ∃ i j, i < j ∧ G.Adj i j ∧ f = monomial (graphPairExponent i j) 1} := by
  unfold graphSpecializedParameterIdeal
  apply congrArg Ideal.span
  ext f
  constructor
  · rintro ⟨i,j,hij,hijG,rfl⟩
    exact ⟨i,j,hij,hijG,graphSpecializedParameterBinomial_zero A hij⟩
  · rintro ⟨i,j,hij,hijG,rfl⟩
    exact ⟨i,j,hij,hijG,(graphSpecializedParameterBinomial_zero A hij).symm⟩

theorem graphSpecializedParameterIdeal_one :
    graphSpecializedParameterIdeal A 1 G =
      Ideal.span {f : MvPolynomial (GraphIntegralVariables N) A |
        ∃ i j, i < j ∧ G.Adj i j ∧
          f = monomial (graphPairExponent i j) 1 - monomial (graphPairExponent j i) 1} := by
  simp only [graphSpecializedParameterIdeal, graphSpecializedParameterGenerators,
    graphSpecializedParameterBinomial_one]

/-- The base-changed augmentation now targets the actual specialized
ideal power through the proved canonical equivalence. -/
def integralGraphSpecializedAugmentation (hs : 0 < s) :
    (A ⊗[GraphIntegralCoefficientRing] IntegralGraphFreeModel hG s) →ₗ[A]
      IntegralGraphSpecializedModule (G := G) s A :=
  (integralGraphIdealBaseChangeEquiv hG s A).toLinearMap.comp
    (integralGraphSplitBaseChange hG s hs A).projection

theorem integralGraphSpecializedAugmentation_surjective (hs : 0 < s) :
    Function.Surjective (integralGraphSpecializedAugmentation hG s A hs) := by
  intro f
  refine ⟨(integralGraphSplitBaseChange hG s hs A).inclusion
    ((integralGraphIdealBaseChangeEquiv hG s A).symm f), ?_⟩
  have he := (integralGraphSplitBaseChange hG s hs A).projection_inclusion
    ((integralGraphIdealBaseChangeEquiv hG s A).symm f)
  exact (congrArg (integralGraphIdealBaseChangeEquiv hG s A) he).trans
    ((integralGraphIdealBaseChangeEquiv hG s A).apply_symm_apply f)

/-- Every coefficient specialization retains exactness at the actual
module, with a boundary supplied by the tensor of the constructed homotopy. -/
theorem integralGraphSpecialized_cycle_boundary (hs : 0 < s)
    (x : A ⊗[GraphIntegralCoefficientRing] IntegralGraphFreeModel hG s)
    (hx : (integralGraphSplitBaseChange hG s hs A).sourceD x = 0)
    (hε : integralGraphSpecializedAugmentation hG s A hs x = 0) :
    ∃ y, (integralGraphSplitBaseChange hG s hs A).sourceD y = x := by
  let C := integralGraphSplitBaseChange hG s hs A
  have hp : C.projection x = 0 := by
    apply (integralGraphIdealBaseChangeEquiv hG s A).map_eq_zero_iff.mp
    exact hε
  refine ⟨C.homotopy x, ?_⟩
  simpa only [hp, map_zero, zero_add] using (C.cycle_decomposition x hx).symm

end GraphSpecialization
end FourPapers.Sublattice

end
end
end


end
