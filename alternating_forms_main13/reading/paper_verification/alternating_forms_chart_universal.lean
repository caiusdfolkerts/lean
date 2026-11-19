module

public import PaperVerification.AlternatingFormsChartConverse
public import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Universal points of the actual common-isotropic affine charts

For every commutative algebra, including nonreduced algebras, homomorphisms
out of the displayed chart ring are naturally the row-reduced matrices
whose rows satisfy the original alternating-form restrictions.  The pivot
columns give an explicit splitting of the row embedding.  Thus the chart
describes rank-s direct summands, rather than merely a set of vectors or
field-valued isotropic planes.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.AlternatingForms

open MvPolynomial Matrix
open scoped BigOperators

variable {K : Type*} [Field K] {s n t m : ℕ}

theorem alternatingRowPair_map
    {R S : Type*} [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (φ : R →ₐ[K] S) (f : StrictPairs n → K)
    (A : Matrix (Fin (t+2)) (Fin n) R) (i j : Fin (t+2)) :
    alternatingRowPair f (A.map φ) i j = φ (alternatingRowPair f A i j) := by
  simp only [alternatingRowPair,map_sum,map_smul,map_sub,map_mul,
    Matrix.map_apply]

/-- The literal row-reduced, common-isotropic matrices over an arbitrary
commutative coefficient algebra. -/
structure IsotropicChartPoint
    (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K)
    (R : Type*) [CommRing R] [Algebra K R] where
  matrix : Matrix (Fin (t+2)) (Fin n) R
  pivot : matrix.submatrix id p.val = 1
  isotropic : ∀ l i j, alternatingRowPair (forms l) matrix i j = 0

abbrev IsotropicChartRing (p : PluckerIndex (t+2) n)
    (forms : Fin m → StrictPairs n → K) :=
  MvPolynomial (PluckerChartVariable p) K ⧸ isotropicChartIdeal p forms

def chartEntryEvaluation {R : Type*} [CommRing R] [Algebra K R]
    (p : PluckerIndex s n) (A : Matrix (Fin s) (Fin n) R) :
    MvPolynomial (PluckerChartVariable p) K →ₐ[K] R :=
  aeval (fun a ↦ A a.1 a.2.val)

theorem chartEntryEvaluation_matrix {R : Type*} [CommRing R] [Algebra K R]
    (p : PluckerIndex s n) (A : Matrix (Fin s) (Fin n) R)
    (hp : A.submatrix id p.val=1) :
    (pluckerChartMatrix (K := K) p).map (chartEntryEvaluation (K := K) p A) = A := by
  classical
  apply Matrix.ext
  intro i j
  change chartEntryEvaluation (K := K) p A (pluckerChartMatrix (K := K) p i j)=A i j
  by_cases hj : j ∈ Set.range p.val
  · obtain ⟨r,rfl⟩ := hj
    have h₁ := congrFun (congrFun (pluckerChartMatrix_pivot (K := K) p) i) r
    simp only [Matrix.of_apply] at h₁
    have h₂ := congrFun (congrFun hp i) r
    change A i (p.val r)=(1 : Matrix (Fin s) (Fin s) R) i r at h₂
    rw [h₁,h₂]
    simp only [Matrix.one_apply,apply_ite,map_one,map_zero] <;> split_ifs <;> rfl
  · rw [pluckerChartMatrix_nonpivot p i ⟨j,hj⟩]
    simp only [chartEntryEvaluation,aeval_X]

theorem chartEntryEvaluation_kills_isotropy
    {R : Type*} [CommRing R] [Algebra K R]
    (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K)
    (A : IsotropicChartPoint p forms R) :
    isotropicChartIdeal p forms ≤ RingHom.ker (chartEntryEvaluation (K := K) p A.matrix).toRingHom := by
  apply Ideal.span_le.mpr
  rintro f ⟨⟨l,ij⟩,rfl⟩
  change chartEntryEvaluation (K := K) p A.matrix
    (alternatingRowPair (forms l) (pluckerChartMatrix (K := K) p) ij.val.1 ij.val.2)=0
  rw [←alternatingRowPair_map,chartEntryEvaluation_matrix p A.matrix A.pivot]
  exact A.isotropic l ij.val.1 ij.val.2

def IsotropicChartPoint.toAlgHom
    {R : Type*} [CommRing R] [Algebra K R]
    {p : PluckerIndex (t+2) n} {forms : Fin m → StrictPairs n → K}
    (A : IsotropicChartPoint p forms R) : IsotropicChartRing p forms →ₐ[K] R :=
  Ideal.Quotient.liftₐ _ (chartEntryEvaluation (K := K) p A.matrix)
    (fun f hf ↦ chartEntryEvaluation_kills_isotropy p forms A hf)

theorem IsotropicChartPoint.toAlgHom_entry
    {R : Type*} [CommRing R] [Algebra K R]
    {p : PluckerIndex (t+2) n} {forms : Fin m → StrictPairs n → K}
    (A : IsotropicChartPoint p forms R) (i : Fin (t+2)) (j : Fin n) :
    A.toAlgHom (Ideal.Quotient.mk (isotropicChartIdeal p forms)
      (pluckerChartMatrix (K := K) p i j)) = A.matrix i j := by
  change chartEntryEvaluation (K := K) p A.matrix (pluckerChartMatrix (K := K) p i j)=A.matrix i j
  exact congrFun (congrFun (chartEntryEvaluation_matrix p A.matrix A.pivot) i) j

def chartPointOfAlgHom
    {R : Type*} [CommRing R] [Algebra K R]
    (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K)
    (φ : IsotropicChartRing p forms →ₐ[K] R) : IsotropicChartPoint p forms R where
  matrix := (pluckerChartMatrix (K := K) p).map
    (φ.comp (Ideal.Quotient.mkₐ K (isotropicChartIdeal p forms)))
  pivot := by
    apply Matrix.ext
    intro i j
    change φ (Ideal.Quotient.mk _ (pluckerChartMatrix (K := K) p i (p.val j))) =
      (1 : Matrix (Fin (t+2)) (Fin (t+2)) R) i j
    rw [show pluckerChartMatrix (K := K) p i (p.val j)=
      (1 : Matrix (Fin (t+2)) (Fin (t+2)) (MvPolynomial (PluckerChartVariable p) K)) i j from
      congrFun (congrFun (pluckerChartMatrix_pivot p) i) j]
    simp only [Matrix.one_apply,apply_ite,map_one,map_zero] <;> split_ifs <;> rfl
  isotropic := by
    intro l i j
    rw [alternatingRowPair_map]
    change φ (Ideal.Quotient.mk _
      (alternatingRowPair (forms l) (pluckerChartMatrix (K := K) p) i j))=0
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr
      (alternatingRowPair_mem_chartIdeal p forms l i j),map_zero]

theorem chartPointOfAlgHom_toAlgHom
    {R : Type*} [CommRing R] [Algebra K R]
    (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K)
    (φ : IsotropicChartRing p forms →ₐ[K] R) :
    (chartPointOfAlgHom p forms φ).toAlgHom=φ := by
  apply Ideal.Quotient.algHom_ext
  apply MvPolynomial.algHom_ext
  intro a
  change chartEntryEvaluation (K := K) p (chartPointOfAlgHom p forms φ).matrix (X a)=
    φ (Ideal.Quotient.mk _ (X a))
  rw [chartEntryEvaluation,aeval_X]
  change φ (Ideal.Quotient.mk _ (pluckerChartMatrix (K := K) p a.1 a.2.val))=_
  rw [pluckerChartMatrix_nonpivot]

theorem IsotropicChartPoint.ext_matrix
    {R : Type*} [CommRing R] [Algebra K R]
    {p : PluckerIndex (t+2) n} {forms : Fin m → StrictPairs n → K}
    (A B : IsotropicChartPoint p forms R) (h : A.matrix=B.matrix) : A=B := by
  cases A
  cases B
  cases h
  rfl

theorem IsotropicChartPoint.ofAlgHom_toAlgHom
    {R : Type*} [CommRing R] [Algebra K R]
    {p : PluckerIndex (t+2) n} {forms : Fin m → StrictPairs n → K}
    (A : IsotropicChartPoint p forms R) : chartPointOfAlgHom p forms A.toAlgHom=A := by
  apply IsotropicChartPoint.ext_matrix
  apply Matrix.ext
  intro i j
  exact IsotropicChartPoint.toAlgHom_entry A i j

/-- The actual chart ring represents isotropic, pivot-normalized matrices
over every commutative K-algebra, with no reducedness or field assumption. -/
def isotropicChartPointEquiv
    {R : Type*} [CommRing R] [Algebra K R]
    (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K) :
    (IsotropicChartRing p forms →ₐ[K] R) ≃ IsotropicChartPoint p forms R where
  toFun := chartPointOfAlgHom p forms
  invFun := IsotropicChartPoint.toAlgHom
  left_inv := chartPointOfAlgHom_toAlgHom p forms
  right_inv := IsotropicChartPoint.ofAlgHom_toAlgHom

theorem chartPointOfAlgHom_natural
    {R S : Type*} [CommRing R] [CommRing S] [Algebra K R] [Algebra K S]
    (p : PluckerIndex (t+2) n) (forms : Fin m → StrictPairs n → K)
    (φ : IsotropicChartRing p forms →ₐ[K] R) (ψ : R →ₐ[K] S) :
    (chartPointOfAlgHom p forms (ψ.comp φ)).matrix=
      ((chartPointOfAlgHom p forms φ).matrix).map ψ := by
  apply Matrix.ext
  intro i j
  rfl

/-- The pivot projection is a literal left inverse to the row embedding.
Its image is therefore a free rank-s direct summand over the arbitrary ring. -/
theorem normalized_rows_split
    {R : Type*} [CommRing R]
    (p : PluckerIndex s n) (A : Matrix (Fin s) (Fin n) R)
    (hp : A.submatrix id p.val=1) (v : Fin s → R) :
    (fun j ↦ (v ᵥ* A) (p.val j))=v := by
  classical
  have h : (fun j ↦ (v ᵥ* A) (p.val j))=v ᵥ* (A.submatrix id p.val) := rfl
  rw [h,hp,Matrix.vecMul_one]

theorem normalized_rows_injective
    {R : Type*} [CommRing R]
    (p : PluckerIndex s n) (A : Matrix (Fin s) (Fin n) R)
    (hp : A.submatrix id p.val=1) : Function.Injective (fun v ↦ v ᵥ* A) := by
  intro u v huv
  have h := congrArg (fun w : Fin n → R ↦ fun j ↦ w (p.val j)) huv
  simpa only [normalized_rows_split p A hp] using h

end PaperVerification.AlternatingForms
