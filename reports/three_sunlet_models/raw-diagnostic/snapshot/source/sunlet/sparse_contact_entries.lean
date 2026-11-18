module

public import sunlet.contact_development

/-!
# Computable entries of the actual sparse contact matrices

These entry formulas avoid reducing the general basis representation inside
`LinearMap.toMatrix'`. Their equality to the original matrices is proved
before they are used by the ordinary kernel-reduced finite certificates.
-/

@[expose] public section

namespace Sunlet.SparseContactEntries

open NormalizedVariations ToricDifferential

variable {ι Ω : Type*} [Fintype ι] [Fintype Ω] [DecidableEq ι] [DecidableEq Ω]

def coefficientEntry (o : Ω) (j : Index ι Ω o) (a : ι) : ℚ :=
  match j with
  | .inl c => if a = c then 1 else 0
  | .inr _ => 0

def torusEntry (o : Ω) (j : Index ι Ω o) (x : Ω) : ℚ :=
  match j with
  | .inl _ => 0
  | .inr y => if x = y.val then 1 else 0

/-- Explicit rational entries, with no matrix-of-a-linear-map conversion
or rational scalar-extension operation in the computation. -/
def tangentEntries (π : ι → Equiv.Perm Ω) (o : Ω) (A B : Set ι)
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] :
    Matrix (ι × Ω) (Bool × Index ι Ω o) ℚ :=
  fun ax bj =>
    (if bj.1 then (if ax.2 = o then 1 else 2) /
      (if π ax.1 ax.2 = o then 1 else 2) else 1) *
    (coefficientEntry o bj.2 ax.1 +
      (if bj.1 then (if ax.1 ∈ B then 1 else 0) else (if ax.1 ∈ A then 1 else 0)) *
      (torusEntry o bj.2 ax.2 - torusEntry o bj.2 (π ax.1 ax.2)))

/-- Explicit entries of the first sparse Hessian. The fixed test direction
and variable direction retain the original ordering. -/
def hessianEntries (π : ι → Equiv.Perm Ω) (o : Ω) (A : Set ι)
    [DecidablePred (· ∈ A)] (w : Index ι Ω o) :
    Matrix (ι × Ω) (Index ι Ω o) ℚ :=
  fun ax j =>
    coefficientEntry o w ax.1 *
      (torusEntry o j ax.2 - torusEntry o j (π ax.1 ax.2)) +
    coefficientEntry o j ax.1 *
      (torusEntry o w ax.2 - torusEntry o w (π ax.1 ax.2)) +
    (if ax.1 ∈ A then 1 else 0) *
      (torusEntry o j ax.2 - torusEntry o j (π ax.1 ax.2)) *
      (torusEntry o w ax.2 - torusEntry o w (π ax.1 ax.2))

theorem tangentMatrix_eq_entries (π : ι → Equiv.Perm Ω) (o : Ω) (A B : Set ι)
    [DecidablePred (· ∈ A)] [DecidablePred (· ∈ B)] :
    SparseContactCertificate.tangentMatrix (K := ℚ) π o A B = tangentEntries π o A B := by
  ext ax bj
  rcases ax with ⟨a, x⟩
  rcases bj with ⟨b, j⟩
  rw [SparseContactCertificate.tangentMatrix, LinearMap.toMatrix'_apply,
    ← ToricPairAlgebra.sparse_fieldPairDifferential (k := ℚ) o π A B,
    ToricPairAlgebra.fieldPairDifferential_single]
  rw [differential_apply, ToricPairAlgebra.asVariation_single_coefficient,
    ToricPairAlgebra.asVariation_single_torus, ToricPairAlgebra.asVariation_single_torus]
  cases b <;>
    simp [tangentEntries, ToricPairAlgebra.sparseCoefficient, ToricPairAlgebra.sparseTorus,
      sparseCoefficients, sparseScale, ratio, TwoRatioRigidity.scale,
      coefficientEntry, torusEntry, ToricPairAlgebra.basisCoefficient, ToricPairAlgebra.basisTorus]
  all_goals cases j <;> simp

theorem hessianMatrix_eq_entries (π : ι → Equiv.Perm Ω) (o : Ω) (A : Set ι)
    [DecidablePred (· ∈ A)] (w : Index ι Ω o) :
    SparseContactCertificate.hessianMatrix (K := ℚ) π o A w = hessianEntries π o A w := by
  ext ax j
  rcases ax with ⟨a, x⟩
  rw [SparseContactCertificate.hessianMatrix, LinearMap.toMatrix'_apply]
  change hessian π (sparseCoefficients (E := ℚ) A) (fun _ => 1)
    (asVariation o (Pi.single j 1)) (asVariation o (Pi.single w 1)) (a, x) = _
  simp only [hessian, ratio, div_self (one_ne_zero : (1 : ℚ) ≠ 0), one_mul,
    ToricPairAlgebra.asVariation_single_coefficient, ToricPairAlgebra.asVariation_single_torus]
  rfl

end Sunlet.SparseContactEntries
