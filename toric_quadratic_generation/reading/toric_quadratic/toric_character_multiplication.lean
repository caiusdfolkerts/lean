module

public import Mathlib.Algebra.Algebra.Bilinear
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MonoidAlgebra.Module
public import Mathlib.LinearAlgebra.TensorProduct.Map

@[expose] public section

/-!
# Multiplication of genuine Laurent-character submodules

For an arbitrary exponent set S, the module V(S) consists of the elements
of the actual additive monoid algebra whose finite support is contained
in S. The tensor-product multiplication map has image exactly V(S+T).
This algebraic statement imposes no finiteness on the exponent sets and
does not assume an identification with global sections of a line bundle.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open Set AddMonoidAlgebra
open scoped Pointwise TensorProduct

variable (k : Type*) [CommSemiring k]
variable {M : Type*} [AddCommMonoid M]

/-- The ordinary submodule of the monoid algebra with support in S. -/
abbrev characterModule (S : Set M) : Submodule k (AddMonoidAlgebra k M) :=
  AddMonoidAlgebra.supported k k S

theorem mem_characterModule_iff (S : Set M) (f : AddMonoidAlgebra k M) :
    f ∈ characterModule k S ↔ (f.coeff.support : Set M) ⊆ S :=
  AddMonoidAlgebra.mem_supported

theorem characterModule_eq_span (S : Set M) :
    characterModule k S = Submodule.span k ((fun m : M => single m (1 : k)) '' S) :=
  AddMonoidAlgebra.supported_eq_span_single k S

theorem characterModule_mono {S T : Set M} (h : S ⊆ T) :
    characterModule k S ≤ characterModule k T :=
  AddMonoidAlgebra.supported_mono h

theorem single_mem_characterModule [Nontrivial k] (S : Set M) (m : M) :
    single m (1 : k) ∈ characterModule k S ↔ m ∈ S := by
  rw [characterModule_eq_span]
  exact AddMonoidAlgebra.single_mem_span_single

/-- Multiplication on the actual monoid algebra, restricted on its two
tensor factors but initially retaining the full algebra as codomain. -/
def characterMultiplicationAmbient (S T : Set M) :
    characterModule k S ⊗[k] characterModule k T →ₗ[k] AddMonoidAlgebra k M :=
  (LinearMap.mul' k (AddMonoidAlgebra k M)).comp
    (TensorProduct.mapIncl (characterModule k S) (characterModule k T))

@[simp] theorem characterMultiplicationAmbient_tmul (S T : Set M)
    (f : characterModule k S) (g : characterModule k T) :
    characterMultiplicationAmbient k S T (f ⊗ₜ[k] g) =
      (f : AddMonoidAlgebra k M) * (g : AddMonoidAlgebra k M) := rfl

theorem character_product_set (S T : Set M) :
    Set.image2 (fun f g : AddMonoidAlgebra k M => f * g)
      ((fun m : M => single m (1 : k)) '' S)
      ((fun m : M => single m (1 : k)) '' T) =
        (fun m : M => single m (1 : k)) '' (S + T) := by
  ext f
  constructor
  · rintro ⟨a, ⟨x, hx, rfl⟩, b, ⟨y, hy, rfl⟩, rfl⟩
    exact ⟨x + y, Set.add_mem_add hx hy, by simp⟩
  · rintro ⟨z, ⟨x, hx, y, hy, rfl⟩, rfl⟩
    exact ⟨single x 1, ⟨x, hx, rfl⟩,
      single y 1, ⟨y, hy, rfl⟩, by simp⟩

/-- The image is exactly the span of all products of the original
characters; cancellation of coefficients introduces no new exponents. -/
theorem range_characterMultiplicationAmbient (S T : Set M) :
    LinearMap.range (characterMultiplicationAmbient k S T) =
      characterModule k (S + T) := by
  change LinearMap.range (TensorProduct.lift (LinearMap.mul k (AddMonoidAlgebra k M)) ∘ₗ
    TensorProduct.mapIncl (characterModule k S) (characterModule k T)) = _
  rw [← TensorProduct.map₂_eq_range_lift_comp_mapIncl]
  rw [characterModule_eq_span, characterModule_eq_span,
    Submodule.map₂_span_span, characterModule_eq_span]
  congr 1
  exact character_product_set k S T

/-- Multiplication with codomain restricted to any genuine support
module containing the pointwise sum of the two exponent sets. -/
def characterMultiplication (S T U : Set M) (hST : S + T ⊆ U) :
    characterModule k S ⊗[k] characterModule k T →ₗ[k] characterModule k U :=
  (characterMultiplicationAmbient k S T).codRestrict (characterModule k U) (by
    intro x
    apply characterModule_mono k hST
    rw [← range_characterMultiplicationAmbient k S T]
    exact ⟨x, rfl⟩)

@[simp] theorem characterMultiplication_coe (S T U : Set M) (hST : S + T ⊆ U)
    (x : characterModule k S ⊗[k] characterModule k T) :
    ((characterMultiplication k S T U hST x : characterModule k U) :
      AddMonoidAlgebra k M) = characterMultiplicationAmbient k S T x := rfl

@[simp] theorem characterMultiplication_tmul (S T U : Set M) (hST : S + T ⊆ U)
    (f : characterModule k S) (g : characterModule k T) :
    ((characterMultiplication k S T U hST (f ⊗ₜ[k] g) : characterModule k U) :
      AddMonoidAlgebra k M) = (f : AddMonoidAlgebra k M) * g := rfl

theorem range_characterMultiplication (S T U : Set M) (hST : S + T ⊆ U) :
    LinearMap.range (characterMultiplication k S T U hST) =
      (characterModule k (S + T)).comap (characterModule k U).subtype := by
  rw [characterMultiplication, LinearMap.range_codRestrict,
    range_characterMultiplicationAmbient]

/-- Surjectivity is exactly the full lattice-point sum assertion. The
nonzero coefficient hypothesis is necessary to recover an exponent from
its character; it holds over every field, in every characteristic. -/
theorem characterMultiplication_surjective_iff [Nontrivial k]
    (S T U : Set M) (hST : S + T ⊆ U) :
    Function.Surjective (characterMultiplication k S T U hST) ↔ U = S + T := by
  constructor
  · intro hsurj
    apply Set.Subset.antisymm _ hST
    intro m hm
    let χ : characterModule k U :=
      ⟨single m (1 : k), (single_mem_characterModule k U m).mpr hm⟩
    obtain ⟨x, hx⟩ := hsurj χ
    have hχ : single m (1 : k) ∈ LinearMap.range
        (characterMultiplicationAmbient k S T) := by
      refine ⟨x, ?_⟩
      exact congrArg (fun y : characterModule k U => (y : AddMonoidAlgebra k M)) hx
    rw [range_characterMultiplicationAmbient] at hχ
    exact (single_mem_characterModule k (S + T) m).mp hχ
  · intro hU f
    have hf : (f : AddMonoidAlgebra k M) ∈ characterModule k (S + T) := by
      rw [← hU]
      exact f.property
    rw [← range_characterMultiplicationAmbient k S T] at hf
    obtain ⟨x, hx⟩ := hf
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact hx

end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.range_characterMultiplicationAmbient
#print axioms PaperVerification.ToricCharacters.characterMultiplication_surjective_iff
