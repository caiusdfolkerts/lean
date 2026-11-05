module

public import PaperVerification.ToricMainTheorems
public import PaperVerification.ToricCharacterMultiplication

@[expose] public section

/-!
# Adjoint multiplication in the actual Laurent character algebra

This composes the unrestricted lattice-point equality with the proved
image of tensor-product multiplication. Identification of these character
modules with scheme-theoretic global sections is a separate sheaf theorem;
it is not built into the definitions used here.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.LatticePolytope

open Set PaperVerification.ToricCharacters
open scoped Pointwise TensorProduct

variable {n : ℕ} (P Q : LatticePolytope n)

def latticePointSet : Set (Lattice n) :=
  {m | embed n m ∈ P.carrier}

def interiorLatticePointSet : Set (Lattice n) :=
  {m | embed n m ∈ interior P.carrier}

def sumInteriorLatticePointSet : Set (Lattice n) :=
  {m | embed n m ∈ interior (P.minkowskiSum Q)}

theorem latticePoint_add_interior_subset :
    P.latticePointSet + Q.interiorLatticePointSet ⊆ P.sumInteriorLatticePointSet Q := by
  rintro m ⟨a, ha, b, hb, rfl⟩
  exact P.add_mem_interior_minkowskiSum Q a b ha hb

/-- The actual multiplication of Laurent polynomials with the indicated
support restrictions, on the tensor product over the ground field. -/
def adjointCharacterMultiplication (k : Type*) [Field k] :
    characterModule k P.latticePointSet ⊗[k] characterModule k Q.interiorLatticePointSet →ₗ[k]
      characterModule k (P.sumInteriorLatticePointSet Q) :=
  characterMultiplication k P.latticePointSet Q.interiorLatticePointSet
    (P.sumInteriorLatticePointSet Q) (P.latticePoint_add_interior_subset Q)

/-- The mixed theorem gives surjectivity of the genuine multiplication
map over every field, in every characteristic. -/
theorem adjointCharacterMultiplication_surjective (k : Type*) [Field k]
    (hP : P.Smooth) (hQ : Q.Smooth) (hfan : P.SameNormalFan Q)
    (hboundP : P.EdgesAtLeast (n + 1)) (hboundQ : Q.EdgesAtLeast (n + 1)) :
    Function.Surjective (P.adjointCharacterMultiplication Q k) := by
  apply (characterMultiplication_surjective_iff k _ _ _ _).mpr
  exact (toric_theorem_1_3_polytope_sets n P Q hP hQ hfan hboundP hboundQ).symm

end PaperVerification.ToricGeometry.LatticePolytope

#print axioms PaperVerification.ToricGeometry.LatticePolytope.adjointCharacterMultiplication_surjective
