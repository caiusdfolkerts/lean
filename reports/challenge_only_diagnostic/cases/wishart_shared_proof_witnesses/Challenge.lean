module
public import Mathlib
/-! Shared proposition witnesses for proof-reference differences measured in
Wishart raw audit44473421580 and canonical class-type probe44481534659.
These declarations supply only proofs of fully literal canonical propositions;
no norm, scalar action, order, measure, functional calculus value or data record
is chosen by an unrestricted definition. All proof bodies are genuine. -/
@[expose] public section
noncomputable section
open scoped MatrixOrder Matrix.Norms.L2Operator
namespace WishartSharedProof
universe u
/-- The source's exact natural-zero interpretation of the nonzero dimension two. -/
@[instance 2000] theorem natTwoNeZero :
    @NeZero ℕ (@Zero.ofOfNat0 ℕ (instOfNatNat (nat_lit 0))) (1+1 : ℕ) := by norm_num
/-- Dimension two satisfies the canonical lower-bound class used by `PiLp` numerals. -/
@[instance 2000] theorem natTwoAtLeastTwo : Nat.AtLeastTwo (1+1) := by infer_instance
/-- Real scalar multiplication commutes with matrix conjugate transpose. -/
@[instance 2000] theorem realMatrixStarModule (n : Type u) :
    StarModule ℝ (Matrix n n ℝ) := by infer_instance
/-- The topology of the real scalar semiring is compatible with its operations. -/
@[instance 2000] theorem realTopologicalSemiring : IsTopologicalSemiring ℝ := by infer_instance
/-- The real scalar/matrix actions commute. -/
@[instance 2000] theorem realMatrixScalarComm (n : Type u) [Fintype n] [DecidableEq n] :
    SMulCommClass ℝ (Matrix n n ℝ) (Matrix n n ℝ) := by infer_instance
/-- The real scalar/matrix actions satisfy the scalar tower law. -/
@[instance 2000] theorem realMatrixScalarTower (n : Type u) [Fintype n] [DecidableEq n] :
    IsScalarTower ℝ (Matrix n n ℝ) (Matrix n n ℝ) := by infer_instance
/-- The matrix star order used by the source's total functional calculus. -/
@[instance 2000] theorem realMatrixStarOrdered (n : Type u) [Fintype n] :
    StarOrderedRing (Matrix n n ℝ) := by infer_instance
/-- The exact real-matrix continuous-functional-calculus proposition. -/
@[instance 2000] theorem realMatrixCFC (n : Type u) [Fintype n] [DecidableEq n] :
    NonUnitalContinuousFunctionalCalculus ℝ (Matrix n n ℝ) IsSelfAdjoint := by infer_instance
/-- Nonnegative real-matrix order has nonnegative real spectrum. -/
@[instance 2000] theorem realMatrixNonnegSpectrum (n : Type u) [Fintype n] :
    NonnegSpectrumClass ℝ (Matrix n n ℝ) := by infer_instance
/-- The real scalar action commutes with multiplication on complex matrices. -/
@[instance 2000] theorem complexMatrixScalarComm (n : Type u) [Fintype n] [DecidableEq n] :
    SMulCommClass ℝ (Matrix n n ℂ) (Matrix n n ℂ) := by infer_instance
/-- The real scalar action and complex-matrix multiplication form a tower. -/
@[instance 2000] theorem complexMatrixScalarTower (n : Type u) [Fintype n] [DecidableEq n] :
    IsScalarTower ℝ (Matrix n n ℂ) (Matrix n n ℂ) := by infer_instance
/-- The canonical complex-matrix star-order proposition. -/
@[instance 2000] theorem complexMatrixStarOrdered (n : Type u) [Fintype n] :
    StarOrderedRing (Matrix n n ℂ) := by infer_instance
/-- The exact complex-matrix real continuous-functional-calculus proposition. -/
@[instance 2000] theorem complexMatrixCFC (n : Type u) [Fintype n] [DecidableEq n] :
    NonUnitalContinuousFunctionalCalculus ℝ (Matrix n n ℂ) IsSelfAdjoint := by infer_instance
/-- Nonnegative complex-matrix order has nonnegative real spectrum. -/
@[instance 2000] theorem complexMatrixNonnegSpectrum (n : Type u) [Fintype n] :
    NonnegSpectrumClass ℝ (Matrix n n ℂ) := by infer_instance
end WishartSharedProof
