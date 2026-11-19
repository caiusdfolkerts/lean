module
public import Mathlib
/-! Shared proposition witnesses for proof-reference differences measured in
Wishart raw audit44473421580 and canonical class-type probe44481534659.
These declarations supply only proofs of fully literal canonical propositions;
no norm, scalar action, order, measure, functional calculus value or data record
is chosen by an unrestricted definition. All proof bodies are genuine. -/
@[expose] public section
noncomputable section
namespace WishartSharedProof
open scoped MatrixOrder Matrix.Norms.L2Operator
universe u
/-- The source's exact natural-zero interpretation of the nonzero dimension two. -/
@[instance 2000] theorem natTwoNeZero :
    @NeZero ℕ (@Zero.ofOfNat0 ℕ (instOfNatNat (nat_lit 0))) (1+1 : ℕ) := ⟨by decide⟩
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
/-- The identity real scalar homomorphisms are mutually inverse. -/
@[instance 2000] theorem realIdentityInvPair :
    RingHomInvPair (RingHom.id ℝ) (RingHom.id ℝ) := by infer_instance
/-- Addition is continuous on the literal Gaussian row space. -/
@[instance 2000] theorem rowContinuousAdd (F : Type u) [NormedRing F] (m : ℕ) :
    ContinuousAdd (PiLp 2 (fun _ : Fin m => F)) := by infer_instance
/-- The two real scalar actions on the literal row space commute. -/
@[instance 2000] theorem rowScalarComm (F : Type u) [NormedRing F] [InnerProductSpace ℝ F] (m : ℕ) :
    SMulCommClass ℝ ℝ (PiLp 2 (fun _ : Fin m => F)) := by infer_instance
/-- Constant real scaling is continuous on the literal row space. -/
@[instance 2000] theorem rowContinuousConstSMul (F : Type u) [NormedRing F] [InnerProductSpace ℝ F] (m : ℕ) :
    ContinuousConstSMul ℝ (PiLp 2 (fun _ : Fin m => F)) := by infer_instance
/-- The literal row space is a topological additive group. -/
@[instance 2000] theorem rowTopologicalAddGroup (F : Type u) [NormedRing F] (m : ℕ) :
    IsTopologicalAddGroup (PiLp 2 (fun _ : Fin m => F)) := by infer_instance
/-- Joint real scaling is continuous on the literal row space. -/
@[instance 2000] theorem rowContinuousSMul (F : Type u) [NormedRing F] [InnerProductSpace ℝ F] (m : ℕ) :
    ContinuousSMul ℝ (PiLp 2 (fun _ : Fin m => F)) := by infer_instance
/-- The literal row space is Hausdorff. -/
@[instance 2000] theorem rowT2Space (F : Type u) [NormedRing F] (m : ℕ) :
    T2Space (PiLp 2 (fun _ : Fin m => F)) := by infer_instance
/-- Finitely many finite-dimensional coordinates form a finite real module. -/
@[instance 2000] theorem rowFinite (F : Type u) [NormedRing F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (m : ℕ) :
    Module.Finite ℝ (PiLp 2 (fun _ : Fin m => F)) := by infer_instance
/-- The measured alternative complex normed-ring hierarchy paths have the same whole record. -/
theorem complexNormedCommRing_path_eq :
    @CommCStarAlgebra.toNormedCommRing ℂ instCommCStarAlgebraComplex =
      @NormedField.toNormedCommRing ℂ Complex.instNormedField := by rfl
/-- Changing only a proposition witness cannot change the resulting mathematical value. -/
theorem propositionWitness_value_eq {P : Prop} {α : Sort u} (f : P → α) (h₁ h₂ : P) :
    f h₁ = f h₂ := by rfl
end WishartSharedProof
