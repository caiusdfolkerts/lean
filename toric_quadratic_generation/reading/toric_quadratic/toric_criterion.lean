module
public import PaperVerification.ToricIdeal
public import PaperVerification.ToricConvexity
@[expose] public section
/-!
# The complete exchange criterion with explicit geometric inputs

This is the algebraic reduction underlying Proposition 2.1. The face map
and its parity/adjoint properties are explicit inputs: they are not constructed from
smoothness or an edge-length bound in this file.
-/

namespace PaperVerification.ToricExchange

variable {M V : Type*} [AddCommGroup M] [AddCommGroup V] [Module ℝ V]
variable (embedding : M →+ V) (P : Set V)
variable (R : Type*) [CommRing R]

/-- Convexity, full IDP, face parity, and proper-face adjoint decomposition yield
quadratic generation in the conventional ring `R[X_a] → R[M][t]`.
All natural degrees and every commutative coefficient ring are included. -/
theorem quadratic_generation_of_convex_face_data (hP : Convex ℝ P)
    (hidp : IntegerDecompositionProperty embedding P)
    {F : Type*} [SemilatticeSup F] [OrderTop F]
    (face : latticePoints embedding P → F)
    (parity : ∀ a b c : latticePoints embedding P, face c ≤ face a ⊔ face b →
      ∃ p q : latticePoints embedding P,
        (a : M) + b = (p : M) + q ∧ SameParity (p : M) c)
    (adjoint : ∀ a b : latticePoints embedding P, face a ⊔ face b ≠ ⊤ →
      ∃ u v : latticePoints embedding P, (a : M) + b = (u : M) + v ∧
        face u = face a ⊔ face b ∧ face v ≤ face a ⊔ face b) :
    RingHom.ker (paperToricMap (latticePoints embedding P) R) =
      polynomialQuadraticIdeal (latticePoints embedding P) R :=
  paper_kernel_eq_quadrics (latticePoints embedding P) R
    (midpointDecomposition_of_convex_idp embedding P hP hidp)
    (tripleReduction_of_convex_face_data embedding P hP face parity adjoint)

end PaperVerification.ToricExchange
