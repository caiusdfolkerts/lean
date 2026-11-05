module

public import PaperVerification.ToricCharacterMultiplication
public import Mathlib.RingTheory.Coalgebra.MonoidAlgebra
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Algebra.Module.Submodule.Equiv

@[expose] public section

/-!
# Character bases of algebraic torus subrepresentations

Stability here is under the actual coalgebra comultiplication, with values
in the tensor product containing the submodule. It is not stability under
the action of rational points. Thus the argument works over finite fields
as well. Taking one coefficient in the first tensor factor isolates one
character in the second; this proves the character basis assertion.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open AddMonoidAlgebra
open scoped TensorProduct

variable (k : Type*) [Field k]
variable {M : Type*} [AddCommGroup M]

/-- Extract the coefficient of one character from the first tensor
factor, retaining the actual second module. -/
def characterCoefficient {V : Type*} [AddCommGroup V] [Module k V] (m : M) :
    AddMonoidAlgebra k M ⊗[k] V →ₗ[k] V :=
  (TensorProduct.lid k V).toLinearMap.comp
    (((AddMonoidAlgebra.basis M k).coord m).rTensor V)

@[simp] theorem characterCoefficient_tmul {V : Type*}
    [AddCommGroup V] [Module k V]
    (m : M) (f : AddMonoidAlgebra k M) (v : V) :
    characterCoefficient k m (f ⊗ₜ[k] v) = f.coeff m • v := by
  simp only [characterCoefficient, LinearMap.comp_apply, LinearMap.rTensor_tmul,
    LinearEquiv.coe_coe, TensorProduct.lid_tmul]
  rfl

/-- Comultiplication followed by one coefficient projection is exactly
the corresponding individual character term. -/
theorem characterCoefficient_comul (m : M) (f : AddMonoidAlgebra k M) :
    characterCoefficient k m (Coalgebra.comul (R := k) f) = single m (f.coeff m) := by
  have h : (characterCoefficient k m).comp
        (Coalgebra.comul (R := k) (A := AddMonoidAlgebra k M)) =
      (AddMonoidAlgebra.lsingle (R := k) m).comp
        ((AddMonoidAlgebra.basis M k).coord m) := by
    apply (AddMonoidAlgebra.basis M k).ext
    intro i
    change characterCoefficient k m
        (Coalgebra.comul (R := k) (AddMonoidAlgebra.single i (1 : k))) =
      AddMonoidAlgebra.single m ((AddMonoidAlgebra.single i (1 : k)).coeff m)
    by_cases hi : i = m
    · subst i
      simp [AddMonoidAlgebra.comul_single]
    · simp [AddMonoidAlgebra.comul_single, hi, Ne.symm hi]
  exact congrArg (fun g => g f) h

/-- Algebraic stability of a Laurent-polynomial submodule under the
split torus: the genuine coaction factors through `k[M] ⊗ S`. -/
def IsCharacterStable (S : Submodule k (AddMonoidAlgebra k M)) : Prop :=
  ∀ f ∈ S, Coalgebra.comul (R := k) f ∈ LinearMap.range
    (TensorProduct.map (LinearMap.id : AddMonoidAlgebra k M →ₗ[k] _)
      S.subtype)

theorem characterCoefficient_map_subtype
    (S : Submodule k (AddMonoidAlgebra k M)) (m : M)
    (z : AddMonoidAlgebra k M ⊗[k] S) :
    characterCoefficient k m
      (TensorProduct.map (LinearMap.id : AddMonoidAlgebra k M →ₗ[k] _)
        S.subtype z) ∈ S := by
  induction z using TensorProduct.induction_on with
  | zero => simp
  | tmul f g =>
      simpa only [TensorProduct.map_tmul, LinearMap.id_apply,
        Submodule.subtype_apply, characterCoefficient_tmul] using
        S.smul_mem (f.coeff m) g.property
  | add z w hz hw => simpa only [map_add] using S.add_mem hz hw

/-- Algebraic coaction stability is equivalent to closure under the
literal Laurent character components. The reverse implication builds
the required tensor preimage from the finite support of the element. -/
theorem isCharacterStable_iff_components
    (S : Submodule k (AddMonoidAlgebra k M)) :
    IsCharacterStable k S ↔
      ∀ f∈S,∀ m : M,single m (f.coeff m)∈S := by
  constructor
  · intro hS f hf m
    obtain ⟨z,hz⟩ := hS f hf
    have h := characterCoefficient_map_subtype k S m z
    rw [hz,characterCoefficient_comul] at h
    exact h
  · intro hS f hf
    classical
    let z : AddMonoidAlgebra k M ⊗[k] S :=
      ∑ m∈f.coeff.support,
        (single m 1) ⊗ₜ[k] (⟨single m (f.coeff m),hS f hf m⟩ : S)
    refine ⟨z,?_⟩
    have hsum : (∑ m∈f.coeff.support,single m (f.coeff m))=f :=
      AddMonoidAlgebra.sum_coeff_single f
    conv_rhs => rw [← hsum]
    simp only [z,map_sum,TensorProduct.map_tmul,LinearMap.id_apply,
      Submodule.subtype_apply,AddMonoidAlgebra.comul_single,
      CommSemiring.comul_apply,AddMonoidAlgebra.lsingle_apply]

/-- Each nonzero coefficient of a stable element supplies its entire
one-dimensional character line in the same submodule. -/
theorem single_mem_of_stable (S : Submodule k (AddMonoidAlgebra k M))
    (hS : IsCharacterStable k S) (f : AddMonoidAlgebra k M) (hf : f ∈ S)
    (m : M) (hm : f.coeff m ≠ 0) : single m (1 : k) ∈ S := by
  obtain ⟨z, hz⟩ := hS f hf
  have hterm := characterCoefficient_map_subtype k S m z
  rw [hz, characterCoefficient_comul] at hterm
  have hmul := S.smul_mem (f.coeff m)⁻¹ hterm
  simpa only [smul_single, smul_eq_mul, inv_mul_cancel₀ hm] using hmul

/-- The exponent set of the characters actually contained in the
submodule, without a chosen spanning family or a weight decomposition. -/
def characterExponents (S : Submodule k (AddMonoidAlgebra k M)) : Set M :=
  {m | single m (1 : k) ∈ S}

/-- A subrepresentation of the regular representation of a split torus
has precisely its contained characters as a basis. This equality first
states the spanning assertion at the level of actual submodules. -/
theorem stable_eq_characterModule (S : Submodule k (AddMonoidAlgebra k M))
    (hS : IsCharacterStable k S) :
    S = characterModule k (characterExponents k S) := by
  apply le_antisymm
  · intro f hf
    rw [mem_characterModule_iff]
    intro m hm
    exact single_mem_of_stable k S hS f hf m
      (Finsupp.mem_support_iff.mp hm)
  · rw [characterModule_eq_span]
    apply Submodule.span_le.mpr
    rintro _ ⟨m, hm, rfl⟩
    exact hm

/-- The actual coordinate equivalence of a stable module with finitely
supported functions on its character exponents. -/
def stableCharacterCoordinates (S : Submodule k (AddMonoidAlgebra k M))
    (hS : IsCharacterStable k S) : S ≃ₗ[k] characterExponents k S →₀ k :=
  (LinearEquiv.ofEq S (characterModule k (characterExponents k S))
    (stable_eq_characterModule k S hS)).trans
      (AddMonoidAlgebra.supportedEquivFinsupp (R := k) (S := k)
        (characterExponents k S))

def stableCharacterBasis (S : Submodule k (AddMonoidAlgebra k M))
    (hS : IsCharacterStable k S) :
    Module.Basis (characterExponents k S) k S where
  repr := stableCharacterCoordinates k S hS

/-- Finite-dimensionality supplies a finite exponent set, with no
assumption on the cardinality or characteristic of the ground field. -/
theorem finite_characterExponents
    (S : Submodule k (AddMonoidAlgebra k M)) [FiniteDimensional k S]
    (hS : IsCharacterStable k S) : (characterExponents k S).Finite := by
  letI := FiniteDimensional.fintypeBasisIndex (stableCharacterBasis k S hS)
  exact Set.toFinite _

end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.stable_eq_characterModule
#print axioms PaperVerification.ToricCharacters.finite_characterExponents
