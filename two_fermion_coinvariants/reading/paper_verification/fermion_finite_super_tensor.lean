module

public import PaperVerification.FermionGradedTensor

/-!
# Finite genuine super tensor products

The factors carry their actual total exterior-degree grading. Tensor products
use Mathlib's signed graded tensor multiplication, with its newly constructed
natural grading. In particular this is not the ordinary tensor product ring.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped TensorProduct

namespace PaperVerification.Fermion

universe u
variable (F : Type u) [Field F]

structure NGradedAlgebra where
  Carrier : Type u
  [ring : Ring Carrier]
  [algebra : Algebra F Carrier]
  part : ℕ → Submodule F Carrier
  [graded : GradedAlgebra part]

attribute [instance] NGradedAlgebra.ring NGradedAlgebra.algebra NGradedAlgebra.graded

namespace NGradedAlgebra

def scalar : NGradedAlgebra F where
  Carrier := F
  ring := inferInstance
  algebra := inferInstance
  part := basisDegreePart (Module.Basis.singleton Unit F) (fun _ ↦ 0)
  graded := basisDegreeGradedAlgebra (Module.Basis.singleton Unit F) (fun _ ↦ 0)
    (by
      apply Submodule.subset_span
      refine ⟨(),rfl,?_⟩
      simp)
    (by
      intro i j
      apply Submodule.subset_span
      refine ⟨(),rfl,?_⟩
      simp)

def tensor (A B : NGradedAlgebra F) : NGradedAlgebra F where
  Carrier := A.part ᵍ⊗[F] B.part
  ring := inferInstance
  algebra := inferInstance
  part := naturalGradedTensorPart A.part B.part
  graded := naturalGradedTensorAlgebra A.part B.part

def tensorList : List (NGradedAlgebra F) → NGradedAlgebra F
  | [] => scalar F
  | A::As => tensor F A (tensorList As)

/-- A fixed finite ordering gives an iterated genuine graded tensor product.
The local factor isomorphism is noncanonical already because its ramified
coordinates involve choices of roots, so this harmless ordering choice
does not strengthen its mathematical hypotheses. -/
def tensorFamily {ι : Type u} [Fintype ι] (A : ι → NGradedAlgebra F) :
    NGradedAlgebra F :=
  tensorList F (List.ofFn (fun i : Fin (Fintype.card ι) ↦ A ((Fintype.equivFin ι).symm i)))

end NGradedAlgebra
end PaperVerification.Fermion
