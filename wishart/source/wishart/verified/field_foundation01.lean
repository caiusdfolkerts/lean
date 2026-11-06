module

public import tau_ceti.algebra.quaternion.complex_matrix
public import Mathlib.Analysis.Matrix.PosDef
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Matrix.Order
public import Mathlib.Analysis.Matrix.MeasurableSpace
public import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
public import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Measurable

/- Generated ordinary proof stage. See audit/staged_field/FieldFoundation01/manifest.json. -/

@[expose] public section

section CanonicalSource0
/- Source: Wishart/QuaternionMatrix.lean -/



/-!
# The complex representation of arbitrary quaternion matrices

The scalar representation is lifted entrywise and then flattened.  In particular,
matrix multiplication is preserved in its original order; no commutativity of
quaternion entries is used.  The real trace, rather than the quaternion-valued
trace, is the cyclic quantity used in the density of Section 7.

This file is a proof-development source until its complete dependency closure
has been checked by the pinned compiler.
-/

noncomputable section
open scoped Matrix Quaternion BigOperators Classical ComplexOrder

namespace Wishart.QuaternionMatrix

/-- Real scalar multiplication commutes with quaternion conjugation. -/
instance quaternionRealStarModule : StarModule ℝ ℍ[ℝ] where
  star_smul r q := by
    simpa only [star_trivial] using Quaternion.star_smul r q

/-- The ordinary Borel measurable structure on the real quaternion space. -/
instance quaternionMeasurableSpace : MeasurableSpace ℍ[ℝ] := borel _

instance quaternionBorelSpace : BorelSpace ℍ[ℝ] := ⟨rfl⟩

abbrev Hermitian (p : ℕ) := selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℍ[ℝ])

variable {m n k : Type*}

/-- The standard real-algebra representation, with each quaternion replaced by
its two-by-two complex matrix.  This also applies to rectangular matrices. -/
def complexRepresentation (A : Matrix m n ℍ[ℝ]) :
    Matrix (m × Fin 2) (n × Fin 2) ℂ :=
  Matrix.comp m n (Fin 2) (Fin 2) ℂ (A.map Quaternion.toComplexMatrix)

@[simp] theorem complexRepresentation_apply (A : Matrix m n ℍ[ℝ])
    (i : m) (j : n) (a b : Fin 2) :
    complexRepresentation A (i, a) (j, b) = Quaternion.toComplexMatrix (A i j) a b := rfl

theorem complexRepresentation_injective :
    Function.Injective (complexRepresentation : Matrix m n ℍ[ℝ] → _) := by
  intro A B h
  apply Matrix.map_injective Quaternion.toComplexMatrix_injective
  exact (Matrix.comp m n (Fin 2) (Fin 2) ℂ).injective h

@[simp] theorem complexRepresentation_zero :
    complexRepresentation (0 : Matrix m n ℍ[ℝ]) = 0 := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [complexRepresentation_apply, Matrix.zero_apply, map_zero]

@[simp] theorem complexRepresentation_add (A B : Matrix m n ℍ[ℝ]) :
    complexRepresentation (A + B) = complexRepresentation A + complexRepresentation B := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [complexRepresentation_apply, Matrix.add_apply, map_add]

@[simp] theorem complexRepresentation_sub (A B : Matrix m n ℍ[ℝ]) :
    complexRepresentation (A - B) = complexRepresentation A - complexRepresentation B := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [complexRepresentation_apply, Matrix.sub_apply, map_sub]

@[simp] theorem complexRepresentation_smul (r : ℝ) (A : Matrix m n ℍ[ℝ]) :
    complexRepresentation (r • A) = r • complexRepresentation A := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [complexRepresentation_apply, Matrix.smul_apply, map_smul]

/-- A real linear map, used for continuity, measurability, and real Jacobians. -/
def complexRepresentationLinearMap :
    Matrix m n ℍ[ℝ] →ₗ[ℝ] Matrix (m × Fin 2) (n × Fin 2) ℂ where
  toFun := complexRepresentation
  map_add' := complexRepresentation_add
  map_smul' := complexRepresentation_smul

theorem continuous_complexRepresentation [Fintype m] [Fintype n] :
    Continuous (complexRepresentation : Matrix m n ℍ[ℝ] → _) :=
  complexRepresentationLinearMap.continuous_of_finiteDimensional

theorem complexRepresentation_mul [Fintype n]
    (A : Matrix m n ℍ[ℝ]) (B : Matrix n k ℍ[ℝ]) :
    complexRepresentation (A * B) = complexRepresentation A * complexRepresentation B := by
  ext ⟨i, a⟩ ⟨j, b⟩
  simp only [complexRepresentation_apply, Matrix.mul_apply, map_sum, map_mul,
    Matrix.sum_apply, Fintype.sum_prod_type]

@[simp] theorem complexRepresentation_one [DecidableEq n] :
    complexRepresentation (1 : Matrix n n ℍ[ℝ]) = 1 := by
  rw [complexRepresentation, Matrix.map_one _ (map_zero _) (map_one _), Matrix.comp_one]

@[simp] theorem complexRepresentation_conjTranspose (A : Matrix m n ℍ[ℝ]) :
    complexRepresentation Aᴴ = (complexRepresentation A)ᴴ := by
  ext ⟨j, b⟩ ⟨i, a⟩
  simp only [complexRepresentation_apply, Matrix.conjTranspose_apply, map_star,
    Matrix.star_apply]

/-- The square-matrix representation is an injective homomorphism of real
algebras with adjoints. -/
def complexRepresentationStarAlgHom [Fintype n] [DecidableEq n] :
    Matrix n n ℍ[ℝ] →⋆ₐ[ℝ] Matrix (n × Fin 2) (n × Fin 2) ℂ where
  toFun := complexRepresentation
  map_zero' := complexRepresentation_zero
  map_one' := complexRepresentation_one
  map_add' := complexRepresentation_add
  map_mul' := complexRepresentation_mul
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, complexRepresentation_smul,
      complexRepresentation_one, Algebra.algebraMap_eq_smul_one]
  map_star' := complexRepresentation_conjTranspose

theorem isHermitian_complexRepresentation_iff (A : Matrix n n ℍ[ℝ]) :
    (complexRepresentation A).IsHermitian ↔ A.IsHermitian := by
  change (complexRepresentation A)ᴴ = complexRepresentation A ↔ Aᴴ = A
  rw [← complexRepresentation_conjTranspose, complexRepresentation_injective.eq_iff]

theorem complexRepresentation_gram [Fintype m] (A : Matrix m n ℍ[ℝ]) :
    complexRepresentation (Aᴴ * A) = (complexRepresentation A)ᴴ * complexRepresentation A := by
  rw [complexRepresentation_mul, complexRepresentation_conjTranspose]

theorem posSemidef_complexRepresentation_gram [Fintype m] [Fintype n]
    (A : Matrix m n ℍ[ℝ]) : (complexRepresentation (Aᴴ * A)).PosSemidef := by
  rw [complexRepresentation_gram]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- Quaternion positive semidefiniteness is evaluated by its faithful complex
representation.  The subsequent spectral theorem identifies this cone with
nonnegative quaternion Hermitian eigenvalues. -/
def PosSemidef [Fintype n] (A : Matrix n n ℍ[ℝ]) : Prop :=
  (complexRepresentation A).PosSemidef

/-- Positive definiteness on the quaternion Hermitian space. -/
def PosDef [Fintype n] (A : Matrix n n ℍ[ℝ]) : Prop :=
  (complexRepresentation A).PosDef

theorem PosSemidef.isHermitian [Fintype n] {A : Matrix n n ℍ[ℝ]}
    (hA : PosSemidef A) : A.IsHermitian :=
  (isHermitian_complexRepresentation_iff A).mp (Matrix.PosSemidef.isHermitian hA)

theorem PosDef.isHermitian [Fintype n] {A : Matrix n n ℍ[ℝ]}
    (hA : PosDef A) : A.IsHermitian :=
  (isHermitian_complexRepresentation_iff A).mp (Matrix.PosDef.isHermitian hA)

theorem PosDef.posSemidef [Fintype n] {A : Matrix n n ℍ[ℝ]}
    (hA : PosDef A) : PosSemidef A := Matrix.PosDef.posSemidef hA

theorem PosSemidef.congruence [Fintype m] [Fintype n]
    {A : Matrix m m ℍ[ℝ]} (hA : PosSemidef A) (B : Matrix m n ℍ[ℝ]) :
    PosSemidef (Bᴴ * A * B) := by
  unfold PosSemidef
  rw [complexRepresentation_mul, complexRepresentation_mul,
    complexRepresentation_conjTranspose]
  exact hA.conjTranspose_mul_mul_same _

@[simp] theorem toComplexMatrix_real (r : ℝ) :
    Quaternion.toComplexMatrix (r : ℍ[ℝ]) = (r : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [Quaternion.toComplexMatrix_apply]
  ext a b
  fin_cases a <;> fin_cases b <;> simp

theorem complexRepresentation_diagonal [DecidableEq n] (d : n → ℝ) :
    complexRepresentation (Matrix.diagonal (fun i => (d i : ℍ[ℝ]))) =
      Matrix.diagonal (fun i : n × Fin 2 => (d i.1 : ℂ)) := by
  ext ⟨i, a⟩ ⟨j, b⟩
  by_cases hij : i = j
  · subst j
    by_cases hab : a = b
    · subst b
      simp [complexRepresentation_apply, toComplexMatrix_real]
    · simp [complexRepresentation_apply, toComplexMatrix_real, hab]
  · simp [complexRepresentation_apply, hij]

/-- Twice the real quaternion trace is the complex trace of the representation. -/
theorem trace_complexRepresentation [Fintype n] (A : Matrix n n ℍ[ℝ]) :
    (complexRepresentation A).trace = ((2 * (A.trace).re : ℝ) : ℂ) := by
  have hre : (∑ i, A i i).re = ∑ i, (A i i).re := by
    change (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)) (∑ i, A i i) =
      ∑ i, (QuaternionAlgebra.reₗ (-1 : ℝ) 0 (-1)) (A i i)
    exact map_sum _ _ _
  calc
    (complexRepresentation A).trace = ∑ i, (Quaternion.toComplexMatrix (A i i)).trace := by
      simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type,
        complexRepresentation_apply]
    _ = ∑ i, ((2 * (A i i).re : ℝ) : ℂ) := by
      simp only [Quaternion.trace_toComplexMatrix]
    _ = ((∑ i, 2 * (A i i).re : ℝ) : ℂ) := by
      exact (map_sum (algebraMap ℝ ℂ) _ _).symm
    _ = ((2 * (A.trace).re : ℝ) : ℂ) := by
      rw [← Finset.mul_sum, ← hre]
      rfl

theorem real_trace_mul_comm [Fintype m] [Fintype n]
    (A : Matrix m n ℍ[ℝ]) (B : Matrix n m ℍ[ℝ]) :
    (A * B).trace.re = (B * A).trace.re := by
  have h := Matrix.trace_mul_comm (complexRepresentation A) (complexRepresentation B)
  rw [← complexRepresentation_mul, ← complexRepresentation_mul,
    trace_complexRepresentation, trace_complexRepresentation] at h
  have hr := congrArg Complex.re h
  norm_num only [Complex.ofReal_re] at hr
  linarith

theorem complexRepresentation_congruence [Fintype m]
    (A : Matrix m m ℍ[ℝ]) (B : Matrix m n ℍ[ℝ]) :
    complexRepresentation (Bᴴ * A * B) =
      (complexRepresentation B)ᴴ * complexRepresentation A * complexRepresentation B := by
  rw [complexRepresentation_mul, complexRepresentation_mul,
    complexRepresentation_conjTranspose]

theorem complexRepresentation_unitary [Fintype n] [DecidableEq n]
    {U : Matrix n n ℍ[ℝ]} (hU : U ∈ unitary (Matrix n n ℍ[ℝ])) :
    complexRepresentation U ∈ unitary (Matrix (n × Fin 2) (n × Fin 2) ℂ) :=
  Unitary.map_mem complexRepresentationStarAlgHom hU

end Wishart.QuaternionMatrix
end
end CanonicalSource0

section CanonicalSource1
/- Source: Wishart/QuaternionColumns.lean -/



/-!
# Quaternion columns and complex eigenvectors

The first columns of the two-by-two scalar representations form a real-linear
bijection from quaternion columns to complex columns of twice the dimension.
Consequently a complex eigenvector of the representation, with a real
eigenvalue, gives an actual quaternion eigenvector.  This is the first step of
the quaternion Hermitian spectral theorem, before unitary completion.
-/

noncomputable section
open scoped Classical Matrix Quaternion BigOperators

namespace Wishart.QuaternionMatrix

variable {n m : Type*}

def columnRepresentation (v : n → ℍ[ℝ]) : n × Fin 2 → ℂ :=
  fun ia => Quaternion.toComplexMatrix (v ia.1) ia.2 0

def columnRepresentationInv (z : n × Fin 2 → ℂ) : n → ℍ[ℝ] :=
  fun i => ⟨(z (i, 0)).re, (z (i, 0)).im, -(z (i, 1)).re, (z (i, 1)).im⟩

theorem columnRepresentationInv_representation (v : n → ℍ[ℝ]) :
    columnRepresentationInv (columnRepresentation v) = v := by
  funext i
  ext <;> simp [columnRepresentationInv, columnRepresentation,
    Quaternion.toComplexMatrix_apply]

theorem columnRepresentation_representationInv (z : n × Fin 2 → ℂ) :
    columnRepresentation (columnRepresentationInv z) = z := by
  funext ⟨i, a⟩
  fin_cases a <;> apply Complex.ext <;>
    simp [columnRepresentationInv, columnRepresentation, Quaternion.toComplexMatrix_apply]

def columnRepresentationLinearEquiv : (n → ℍ[ℝ]) ≃ₗ[ℝ] (n × Fin 2 → ℂ) where
  toFun := columnRepresentation
  invFun := columnRepresentationInv
  left_inv := columnRepresentationInv_representation
  right_inv := columnRepresentation_representationInv
  map_add' v w := by
    funext ⟨i, a⟩
    simp only [columnRepresentation, Pi.add_apply, map_add, Matrix.add_apply]
  map_smul' r v := by
    funext ⟨i, a⟩
    simp only [columnRepresentation, Pi.smul_apply, map_smul, Matrix.smul_apply, RingHom.id_apply]

@[simp] theorem columnRepresentationLinearEquiv_apply (v : n → ℍ[ℝ]) :
    columnRepresentationLinearEquiv v = columnRepresentation v := rfl

@[simp] theorem columnRepresentation_zero :
    columnRepresentation (0 : n → ℍ[ℝ]) = 0 := by
  funext ⟨i, a⟩
  change Quaternion.toComplexMatrix (0 : ℍ[ℝ]) a 0 = 0
  simp only [map_zero, Matrix.zero_apply]

theorem columnRepresentation_injective :
    Function.Injective (columnRepresentation : (n → ℍ[ℝ]) → _) :=
  columnRepresentationLinearEquiv.injective

theorem columnRepresentation_mulVec [Fintype n]
    (A : Matrix m n ℍ[ℝ]) (v : n → ℍ[ℝ]) :
    columnRepresentation (A *ᵥ v) = complexRepresentation A *ᵥ columnRepresentation v := by
  funext ⟨i, a⟩
  simp only [columnRepresentation, Matrix.mulVec, dotProduct, map_sum, map_mul,
    Matrix.sum_apply, Matrix.mul_apply, Fintype.sum_prod_type, complexRepresentation_apply]

theorem columnRepresentation_smul (r : ℝ) (v : n → ℍ[ℝ]) :
    columnRepresentation (r • v) = r • columnRepresentation v :=
  columnRepresentationLinearEquiv.map_smul r v

theorem columnRepresentation_normSq_sum [Fintype n] (v : n → ℍ[ℝ]) :
    (∑ i, Quaternion.normSq (v i)) =
      ∑ ia : n × Fin 2, Complex.normSq (columnRepresentation v ia) := by
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Fin.sum_univ_two, columnRepresentation, Quaternion.toComplexMatrix_apply]
  simp [Quaternion.normSq_def', Complex.normSq_apply]
  ring

theorem star_dotProduct_eq_normSq_sum [Fintype n] (v : n → ℍ[ℝ]) :
    star v ⬝ᵥ v = ((∑ i, Quaternion.normSq (v i) : ℝ) : ℍ[ℝ]) := by
  simp only [dotProduct, Pi.star_apply, Quaternion.star_mul_self]
  exact (map_sum (algebraMap ℝ ℍ[ℝ]) _ _).symm

theorem exists_unit_eigenvector {p : ℕ}
    {A : Matrix (Fin (p + 1)) (Fin (p + 1)) ℍ[ℝ]} (hA : A.IsHermitian) :
    ∃ (lam : ℝ) (v : Fin (p + 1) → ℍ[ℝ]),
      star v ⬝ᵥ v = 1 ∧ A *ᵥ v = lam • v := by
  let hC := (isHermitian_complexRepresentation_iff A).mpr hA
  let i : Fin (p + 1) × Fin 2 := (0, 0)
  let z := hC.eigenvectorBasis i
  let v := columnRepresentationInv (z : (Fin (p + 1) × Fin 2) → ℂ)
  have hv : columnRepresentation v = (z : (Fin (p + 1) × Fin 2) → ℂ) :=
    columnRepresentation_representationInv _
  refine ⟨hC.eigenvalues i, v, ?_, ?_⟩
  · rw [star_dotProduct_eq_normSq_sum]
    have hnorm : (∑ j, Quaternion.normSq (v j)) = 1 := by
      rw [columnRepresentation_normSq_sum, hv]
      have hz : ‖z‖ = 1 := hC.eigenvectorBasis.orthonormal.1 i
      calc
        (∑ j, Complex.normSq (z j)) = ‖z‖ ^ 2 := by
          rw [PiLp.norm_sq_eq_of_L2]
          apply Finset.sum_congr rfl
          intro j hj
          exact Complex.normSq_eq_norm_sq _
        _ = 1 := by rw [hz]; norm_num
    rw [hnorm]
    norm_cast
  · apply columnRepresentation_injective
    rw [columnRepresentation_mulVec, columnRepresentation_smul, hv]
    exact hC.mulVec_eigenvectorBasis i

/-- Positivity in the representation agrees with the ordinary quaternion
quadratic form on every quaternion column. -/
theorem complexQuadratic_column [Fintype n] (A : Matrix n n ℍ[ℝ])
    (v : n → ℍ[ℝ]) :
    star (columnRepresentation v) ⬝ᵥ
        (complexRepresentation A *ᵥ columnRepresentation v) =
      Quaternion.toComplexMatrix (star v ⬝ᵥ (A *ᵥ v)) 0 0 := by
  rw [← columnRepresentation_mulVec]
  simp only [dotProduct, columnRepresentation, map_sum, Matrix.sum_apply,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Pi.star_apply, map_mul, map_star, Matrix.star_apply,
    Matrix.mul_apply, Fin.sum_univ_two, columnRepresentation]

end Wishart.QuaternionMatrix
end
end CanonicalSource1

section CanonicalSource2
/- Source: Wishart/QuaternionHouseholder.lean -/



/-!
# Quaternion unit vectors extend to unitary matrices

This is a constructive Householder argument over the real quaternions.  Its
rank-one reflector has a real scalar coefficient; therefore the proof does not
commute arbitrary quaternion factors.  It supplies the unitary completion used
in the induction proving the quaternion Hermitian spectral theorem.
-/

noncomputable section
open Matrix
open scoped Classical Quaternion BigOperators

namespace Wishart.QuaternionMatrix

theorem exists_unit_phase (q : ℍ[ℝ]) :
    ∃ u : unitary ℍ[ℝ], u.val * (‖q‖ : ℍ[ℝ]) = q := by
  by_cases hq : q = 0
  · exact ⟨1, by simp [hq]⟩
  have hn : 0 < ‖q‖ := norm_pos_iff.mpr hq
  let a : ℍ[ℝ] := ‖q‖⁻¹ • q
  have ha : ‖a‖ = 1 := by
    dsimp only [a]
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn),
      inv_mul_cancel₀ hn.ne']
  have hau : a ∈ unitary ℍ[ℝ] := by
    apply Unitary.mem_iff.mpr
    constructor
    · rw [Quaternion.star_mul_self, Quaternion.normSq_eq_norm_mul_self, ha,
        one_mul, Quaternion.coe_one]
    · rw [Quaternion.self_mul_star, Quaternion.normSq_eq_norm_mul_self, ha,
        one_mul, Quaternion.coe_one]
  refine ⟨⟨a, hau⟩, ?_⟩
  change a * (‖q‖ : ℍ[ℝ]) = q
  rw [Quaternion.mul_coe_eq_smul]
  dsimp only [a]
  rw [smul_smul, mul_inv_cancel₀ hn.ne', one_smul]

variable {n : Type*} [Fintype n] [DecidableEq n]

def quaternionOuter (v : n → ℍ[ℝ]) : Matrix n n ℍ[ℝ] :=
  Matrix.vecMulVec v (star v)

theorem quaternionOuter_conjTranspose (v : n → ℍ[ℝ]) :
    (quaternionOuter v)ᴴ = quaternionOuter v := by
  simp only [quaternionOuter, Matrix.conjTranspose_vecMulVec, star_star]

theorem quaternionOuter_sq (v : n → ℍ[ℝ]) {d : ℝ}
    (hv : star v ⬝ᵥ v = (d : ℍ[ℝ])) :
    quaternionOuter v * quaternionOuter v = d • quaternionOuter v := by
  rw [quaternionOuter, Matrix.vecMulVec_mul_vecMulVec, hv]
  apply Matrix.ext
  intro i j
  change v i * ((d : ℍ[ℝ]) * star (v j)) = d • (v i * star (v j))
  rw [Quaternion.coe_mul_eq_smul, mul_smul_comm]

theorem quaternionOuter_mulVec (v x : n → ℍ[ℝ]) {d : ℝ}
    (hvx : star v ⬝ᵥ x = (d : ℍ[ℝ])) :
    quaternionOuter v *ᵥ x = d • v := by
  rw [quaternionOuter, Matrix.vecMulVec_mulVec, hvx]
  funext i
  exact Quaternion.mul_coe_eq_smul d (v i)

def householder (v : n → ℍ[ℝ]) (d : ℝ) : Matrix n n ℍ[ℝ] :=
  1 - d⁻¹ • quaternionOuter v

theorem householder_conjTranspose (v : n → ℍ[ℝ]) (d : ℝ) :
    (householder v d)ᴴ = householder v d := by
  simp only [householder, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    Matrix.conjTranspose_smul, star_trivial, quaternionOuter_conjTranspose]

theorem householder_sq (v : n → ℍ[ℝ]) {d : ℝ} (hd : d ≠ 0)
    (hv : star v ⬝ᵥ v = ((2 * d : ℝ) : ℍ[ℝ])) :
    householder v d * householder v d = 1 := by
  simp only [householder, Matrix.sub_mul, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
    Matrix.smul_mul, Matrix.mul_smul, quaternionOuter_sq v hv, smul_sub, smul_smul]
  have hc : d⁻¹ * (d⁻¹ * (2 * d)) = 2 * d⁻¹ := by field_simp [hd]
  rw [hc]
  rw [two_mul, add_smul]
  abel

theorem householder_mem_unitary (v : n → ℍ[ℝ]) {d : ℝ} (hd : d ≠ 0)
    (hv : star v ⬝ᵥ v = ((2 * d : ℝ) : ℍ[ℝ])) :
    householder v d ∈ unitary (Matrix n n ℍ[ℝ]) := by
  change (householder v d)ᴴ * householder v d = 1 ∧
    householder v d * (householder v d)ᴴ = 1
  rw [householder_conjTranspose, householder_sq v hd hv]
  exact ⟨rfl, rfl⟩

theorem householder_mulVec (v x : n → ℍ[ℝ]) {d : ℝ} (hd : d ≠ 0)
    (hvx : star v ⬝ᵥ x = (d : ℍ[ℝ])) :
    householder v d *ᵥ x = x - v := by
  rw [householder, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.smul_mulVec,
    quaternionOuter_mulVec v x hvx, smul_smul, inv_mul_cancel₀ hd, one_smul]

theorem star_dotProduct_single (x : n → ℍ[ℝ]) (i : n) (u : ℍ[ℝ]) :
    star x ⬝ᵥ Pi.single i u = star (x i) * u := by
  simp [dotProduct, Pi.single_apply]

theorem star_single_dotProduct (x : n → ℍ[ℝ]) (i : n) (u : ℍ[ℝ]) :
    star (Pi.single i u) ⬝ᵥ x = star u * x i := by
  simp [dotProduct, Pi.single_apply, apply_ite]

/-- Every unit quaternion column is the first column of an actual quaternion
unitary matrix, in all dimensions. -/
theorem exists_unitary_firstColumn {p : ℕ} (x : Fin (p + 1) → ℍ[ℝ])
    (hx : star x ⬝ᵥ x = 1) :
    ∃ U : unitary (Matrix (Fin (p + 1)) (Fin (p + 1)) ℍ[ℝ]),
      ∀ i, U.val i 0 = x i := by
  obtain ⟨u, hu⟩ := exists_unit_phase (x 0)
  let e : Fin (p + 1) → ℍ[ℝ] := Pi.single 0 u.val
  let v := x + e
  let d : ℝ := 1 + ‖x 0‖
  have hd : 0 < d := by dsimp [d]; positivity
  have hux : star u.val * x 0 = (‖x 0‖ : ℍ[ℝ]) := by
    nth_rewrite 1 [← hu]
    rw [← mul_assoc, Unitary.coe_star_mul_self, one_mul]
  have hxu : star (x 0) * u.val = (‖x 0‖ : ℍ[ℝ]) := by
    have h := congrArg star hux
    simpa only [star_mul, star_star, Quaternion.star_coe] using h
  have hex : star e ⬝ᵥ x = (‖x 0‖ : ℍ[ℝ]) := by
    dsimp only [e]
    rw [star_single_dotProduct, hux]
  have hxe : star x ⬝ᵥ e = (‖x 0‖ : ℍ[ℝ]) := by
    dsimp only [e]
    rw [star_dotProduct_single, hxu]
  have hee : star e ⬝ᵥ e = 1 := by
    dsimp only [e]
    rw [star_single_dotProduct]
    simpa using Unitary.coe_star_mul_self u
  have hvx : star v ⬝ᵥ x = (d : ℍ[ℝ]) := by
    dsimp only [v]
    rw [star_add, add_dotProduct, hx, hex]
    simp [d]
  have hvv : star v ⬝ᵥ v = ((2 * d : ℝ) : ℍ[ℝ]) := by
    dsimp only [v]
    rw [star_add, add_dotProduct, dotProduct_add, dotProduct_add,
      hx, hxe, hex, hee]
    dsimp [d]
    simp only [Quaternion.coe_mul, Quaternion.coe_add, Quaternion.coe_one,
      show ((2 : ℝ) : ℍ[ℝ]) = 2 from Quaternion.coe_natCast 2]
    noncomm_ring
  let H : unitary (Matrix (Fin (p + 1)) (Fin (p + 1)) ℍ[ℝ]) :=
    ⟨householder v d, householder_mem_unitary v hd.ne' hvv⟩
  let diag : Fin (p + 1) → ℍ[ℝ] := fun i => if i = 0 then -star u.val else 1
  have hdiag : Matrix.diagonal diag ∈ unitary (Matrix (Fin (p + 1)) (Fin (p + 1)) ℍ[ℝ]) := by
    change (Matrix.diagonal diag)ᴴ * Matrix.diagonal diag = 1 ∧
      Matrix.diagonal diag * (Matrix.diagonal diag)ᴴ = 1
    constructor <;> rw [Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal]
    · apply Matrix.diagonal_eq_one.mpr
      funext i
      by_cases hi : i = 0 <;>
        simp [diag, hi, Unitary.coe_mul_star_self, Unitary.coe_star_mul_self]
    · apply Matrix.diagonal_eq_one.mpr
      funext i
      by_cases hi : i = 0 <;>
        simp [diag, hi, Unitary.coe_mul_star_self, Unitary.coe_star_mul_self]
  let D : unitary (Matrix (Fin (p + 1)) (Fin (p + 1)) ℍ[ℝ]) := ⟨Matrix.diagonal diag, hdiag⟩
  let M := D * H
  have hMx : M.val *ᵥ x = Pi.single 0 1 := by
    change (Matrix.diagonal diag * householder v d) *ᵥ x = Pi.single 0 1
    rw [← Matrix.mulVec_mulVec, householder_mulVec v x hd.ne' hvx]
    have hxv : x - v = -e := by dsimp [v]; abel
    rw [hxv]
    funext i
    by_cases hi : i = 0
    · subst i
      simp [Matrix.mulVec_diagonal, diag, e, Unitary.coe_star_mul_self]
    · simp [Matrix.mulVec_diagonal, diag, e, hi]
  refine ⟨star M, ?_⟩
  have hback : (star M.val) *ᵥ Pi.single 0 1 = x := by
    rw [← hMx, Matrix.mulVec_mulVec, Unitary.coe_star_mul_self, Matrix.one_mulVec]
  intro i
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using congrFun hback i

end Wishart.QuaternionMatrix
end
end CanonicalSource2

section CanonicalSource3
/- Source: Wishart/QuaternionDeterminant.lean -/



/-!
# Positive quaternion determinants and the rank-one determinant identity

On the positive cone the Moore determinant is the positive square root of the
complex determinant of the faithful representation.  The identification with
the product of quaternion eigenvalues is established in the spectral layer;
the name `positiveDeterminant` keeps that separate obligation explicit here.

The rank-one formula is derived from the ordinary complex rank-two determinant
lemma.  Inverses are the genuine two-sided ring inverses of quaternion matrices.
-/

noncomputable section
open scoped Matrix Quaternion ComplexOrder BigOperators Classical Ring

namespace Wishart.QuaternionMatrix

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem isUnit_of_complexRepresentation_isUnit {A : Matrix n n ℍ[ℝ]}
    (hA : IsUnit (complexRepresentation A)) : IsUnit A := by
  apply IsArtinianRing.isUnit_iff_isRightRegular.mpr
  intro B C h
  apply complexRepresentation_injective
  apply hA.isRegular.2
  simpa only [← complexRepresentation_mul] using congrArg complexRepresentation h

theorem PosDef.isUnit {A : Matrix n n ℍ[ℝ]} (hA : PosDef A) : IsUnit A :=
  isUnit_of_complexRepresentation_isUnit (Matrix.PosDef.isUnit hA)

theorem complexRepresentation_ringInverse {A : Matrix n n ℍ[ℝ]} (hA : IsUnit A) :
    complexRepresentation A⁻¹ʳ = (complexRepresentation A)⁻¹ := by
  apply Eq.symm
  apply Matrix.inv_eq_left_inv
  rw [← complexRepresentation_mul, Ring.inverse_mul_cancel A hA,
    complexRepresentation_one]

theorem PosDef.ringInverse {A : Matrix n n ℍ[ℝ]} (hA : PosDef A) :
    PosDef A⁻¹ʳ := by
  unfold PosDef
  rw [complexRepresentation_ringInverse hA.isUnit]
  exact Matrix.PosDef.inv hA

/-- The positive square root of the complex determinant.  All uses as a
quaternion determinant carry an explicit positive-semidefinite hypothesis. -/
def positiveDeterminant (A : Matrix n n ℍ[ℝ]) : ℝ :=
  Real.sqrt (complexRepresentation A).det.re

theorem positiveDeterminant_nonneg (A : Matrix n n ℍ[ℝ]) :
    0 ≤ positiveDeterminant A := Real.sqrt_nonneg _

theorem PosSemidef.det_re_nonneg {A : Matrix n n ℍ[ℝ]} (hA : PosSemidef A) :
    0 ≤ (complexRepresentation A).det.re :=
  (RCLike.nonneg_iff.mp (Matrix.PosSemidef.det_nonneg hA)).1

theorem PosSemidef.positiveDeterminant_sq {A : Matrix n n ℍ[ℝ]}
    (hA : PosSemidef A) : positiveDeterminant A ^ 2 = (complexRepresentation A).det.re :=
  Real.sq_sqrt hA.det_re_nonneg

theorem PosDef.positiveDeterminant_pos {A : Matrix n n ℍ[ℝ]} (hA : PosDef A) :
    0 < positiveDeterminant A := by
  apply Real.sqrt_pos.mpr
  exact (RCLike.pos_iff.mp (Matrix.PosDef.det_pos hA)).1

theorem positiveDeterminant_diagonal (d : n → ℝ) (hd : ∀ i, 0 ≤ d i) :
    positiveDeterminant (Matrix.diagonal (fun i => (d i : ℍ[ℝ]))) = ∏ i, d i := by
  rw [positiveDeterminant, complexRepresentation_diagonal, Matrix.det_diagonal]
  simp only [Fintype.prod_prod_type, Fin.prod_univ_two]
  have hprod : (∏ i, (d i : ℂ) * d i) = ((∏ i, d i : ℝ) : ℂ) ^ 2 := by
    rw [Finset.prod_mul_distrib, ← Complex.ofReal_prod]
    ring
  rw [hprod]
  simp only [← Complex.ofReal_pow, Complex.ofReal_re]
  exact Real.sqrt_sq (Finset.prod_nonneg fun i _ => hd i)

theorem PosSemidef.diag_re_nonneg {A : Matrix n n ℍ[ℝ]}
    (hA : PosSemidef A) (i : n) : 0 ≤ (A i i).re := by
  have hreal : A i i = ((A i i).re : ℍ[ℝ]) :=
    Quaternion.star_eq_self.mp (hA.isHermitian.apply i i)
  have h := Matrix.PosSemidef.diag_nonneg
    (show (complexRepresentation A).PosSemidef from hA) (i := (i, (0 : Fin 2)))
  rw [complexRepresentation_apply, hreal, toComplexMatrix_real] at h
  simpa using (Complex.nonneg_iff.mp h).1

/-- The scalar in the quaternion rank-one determinant lemma is an actual
nonnegative real quadratic form, not an assumed scalar identity. -/
def rowQuadratic (Q : Matrix n n ℍ[ℝ]) (w : Matrix Unit n ℍ[ℝ]) : ℝ :=
  (w * Q⁻¹ʳ * wᴴ) () () |>.re

theorem rowQuadratic_nonneg {Q : Matrix n n ℍ[ℝ]} (hQ : PosDef Q)
    (w : Matrix Unit n ℍ[ℝ]) : 0 ≤ rowQuadratic Q w := by
  have h := hQ.ringInverse.posSemidef.congruence wᴴ
  simp only [Matrix.conjTranspose_conjTranspose] at h
  exact h.diag_re_nonneg ()

theorem rowQuadratic_matrix {Q : Matrix n n ℍ[ℝ]} (hQ : PosDef Q)
    (w : Matrix Unit n ℍ[ℝ]) :
    w * Q⁻¹ʳ * wᴴ = Matrix.diagonal (fun _ : Unit => (rowQuadratic Q w : ℍ[ℝ])) := by
  have h := hQ.ringInverse.posSemidef.congruence wᴴ
  simp only [Matrix.conjTranspose_conjTranspose] at h
  apply Matrix.ext
  intro a b
  cases a
  cases b
  simpa only [Matrix.diagonal_apply_eq, rowQuadratic] using
    (Quaternion.star_eq_self.mp (h.isHermitian.apply () ()))

theorem complex_det_rankOne {Q : Matrix n n ℍ[ℝ]} (hQ : PosDef Q)
    (w : Matrix Unit n ℍ[ℝ]) :
    (complexRepresentation (Q + wᴴ * w)).det =
      (complexRepresentation Q).det * ((1 + rowQuadratic Q w : ℝ) : ℂ) ^ 2 := by
  rw [complexRepresentation_add, complexRepresentation_gram]
  rw [Matrix.det_add_mul _ _
    ((Matrix.isUnit_iff_isUnit_det _).mp (Matrix.PosDef.isUnit hQ))]
  have hsmall :
      complexRepresentation w * (complexRepresentation Q)⁻¹ *
          (complexRepresentation w)ᴴ =
        Matrix.diagonal (fun _ : Unit × Fin 2 => (rowQuadratic Q w : ℂ)) := by
    rw [← complexRepresentation_ringInverse hQ.isUnit,
      ← complexRepresentation_conjTranspose, ← complexRepresentation_mul,
      ← complexRepresentation_mul, rowQuadratic_matrix hQ,
      complexRepresentation_diagonal]
  rw [hsmall, ← Matrix.diagonal_one, Matrix.diagonal_add, Matrix.det_diagonal]
  simp [Fintype.prod_prod_type, Fin.prod_univ_two, pow_two]

/-- Equation (20) for every positive-definite quaternion Hermitian background.
Its proof takes the positive square root of the complex rank-two identity. -/
theorem positiveDeterminant_rankOne {Q : Matrix n n ℍ[ℝ]} (hQ : PosDef Q)
    (w : Matrix Unit n ℍ[ℝ]) :
    positiveDeterminant (Q + wᴴ * w) =
      positiveDeterminant Q * (1 + rowQuadratic Q w) := by
  have hc : 0 ≤ 1 + rowQuadratic Q w := by
    have := rowQuadratic_nonneg hQ w
    linarith
  have hdet := congrArg Complex.re (complex_det_rankOne hQ w)
  simp only [← Complex.ofReal_pow, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero] at hdet
  rw [positiveDeterminant, hdet, Real.sqrt_mul hQ.posSemidef.det_re_nonneg,
    Real.sqrt_sq hc]
  rfl

theorem positiveDeterminant_congruence {Q : Matrix n n ℍ[ℝ]}
    (hQ : PosSemidef Q) (R : Matrix n n ℍ[ℝ]) :
    positiveDeterminant (Rᴴ * Q * R) =
      positiveDeterminant (Rᴴ * R) * positiveDeterminant Q := by
  have hR : PosSemidef (Rᴴ * R) := posSemidef_complexRepresentation_gram R
  have hRQ := hQ.congruence R
  have hQim : (complexRepresentation Q).det.im = 0 :=
    (RCLike.nonneg_iff.mp (Matrix.PosSemidef.det_nonneg hQ)).2
  have hsq : positiveDeterminant (Rᴴ * Q * R) ^ 2 =
      (positiveDeterminant (Rᴴ * R) * positiveDeterminant Q) ^ 2 := by
    rw [hRQ.positiveDeterminant_sq, mul_pow, hR.positiveDeterminant_sq,
      hQ.positiveDeterminant_sq, complexRepresentation_congruence,
      complexRepresentation_gram]
    simp only [Matrix.det_mul, Matrix.det_conjTranspose, Complex.star_def,
      Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im, hQim]
    ring
  have hleft := positiveDeterminant_nonneg (Rᴴ * Q * R)
  have hright := mul_nonneg (positiveDeterminant_nonneg (Rᴴ * R))
    (positiveDeterminant_nonneg Q)
  nlinarith

end Wishart.QuaternionMatrix
end
end CanonicalSource3

section CanonicalSource4
/- Source: Wishart/QuaternionSpectral.lean -/



/-!
# The quaternion Hermitian spectral theorem

The proof is by dimension induction.  A real eigenvalue and quaternion unit
eigenvector come from the faithful complex representation; the explicit
Householder construction completes that vector to a quaternion unitary frame.
The orthogonal complement is another quaternion Hermitian matrix.  In
particular, no quaternion spectral theorem is introduced as an assumption.
-/

noncomputable section
open Matrix Polynomial
open scoped Classical Matrix Quaternion BigOperators ComplexOrder

namespace Wishart.QuaternionMatrix

def blockSucc {R : Type*} [Zero R] {p : ℕ} (c : R)
    (A : Matrix (Fin p) (Fin p) R) : Matrix (Fin (p + 1)) (Fin (p + 1)) R :=
  Matrix.of fun i j => Fin.cases (Fin.cases c (fun _ => 0) j)
    (fun i => Fin.cases 0 (fun j => A i j) j) i

@[simp] theorem blockSucc_zero_zero {R : Type*} [Zero R] {p : ℕ}
    (c : R) (A : Matrix (Fin p) (Fin p) R) : blockSucc c A 0 0 = c := rfl
@[simp] theorem blockSucc_zero_succ {R : Type*} [Zero R] {p : ℕ}
    (c : R) (A : Matrix (Fin p) (Fin p) R) (j : Fin p) : blockSucc c A 0 j.succ = 0 := rfl
@[simp] theorem blockSucc_succ_zero {R : Type*} [Zero R] {p : ℕ}
    (c : R) (A : Matrix (Fin p) (Fin p) R) (i : Fin p) : blockSucc c A i.succ 0 = 0 := rfl
@[simp] theorem blockSucc_succ_succ {R : Type*} [Zero R] {p : ℕ}
    (c : R) (A : Matrix (Fin p) (Fin p) R) (i j : Fin p) :
    blockSucc c A i.succ j.succ = A i j := rfl

theorem blockSucc_mul {R : Type*} [NonUnitalNonAssocSemiring R] {p : ℕ}
    (c d : R) (A B : Matrix (Fin p) (Fin p) R) :
    blockSucc c A * blockSucc d B = blockSucc (c * d) (A * B) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ]

theorem blockSucc_one {R : Type*} [Zero R] [One R] {p : ℕ} :
    blockSucc (1 : R) (1 : Matrix (Fin p) (Fin p) R) = 1 := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j <;> simp [Matrix.one_apply, eq_comm]

theorem blockSucc_conjTranspose {R : Type*} [AddMonoid R] [StarAddMonoid R] {p : ℕ}
    (c : R) (A : Matrix (Fin p) (Fin p) R) :
    (blockSucc c A)ᴴ = blockSucc (star c) Aᴴ := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j <;> simp [Matrix.conjTranspose_apply]

theorem blockSucc_diagonal {R : Type*} [Zero R] {p : ℕ}
    (c : R) (d : Fin p → R) :
    blockSucc c (Matrix.diagonal d) = Matrix.diagonal (Fin.cons c d) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;>
    refine Fin.cases ?_ (fun j => ?_) j <;> simp [Matrix.diagonal_apply, eq_comm]

def blockSuccUnitary {p : ℕ} (U : unitary (Matrix (Fin p) (Fin p) ℍ[ℝ])) :
    unitary (Matrix (Fin (p + 1)) (Fin (p + 1)) ℍ[ℝ]) := by
  refine ⟨blockSucc 1 U.val, ?_⟩
  have hU1 : U.valᴴ * U.val = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using U.property.1
  have hU2 : U.val * U.valᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using U.property.2
  change (blockSucc 1 U.val)ᴴ * blockSucc 1 U.val = 1 ∧
    blockSucc 1 U.val * (blockSucc 1 U.val)ᴴ = 1
  rw [blockSucc_conjTranspose, star_one, blockSucc_mul, blockSucc_mul,
    one_mul, hU1, hU2, blockSucc_one]
  exact ⟨rfl, rfl⟩

theorem exists_unitary_diagonalization : ∀ p : ℕ,
    ∀ A : Matrix (Fin p) (Fin p) ℍ[ℝ], A.IsHermitian →
      ∃ (U : unitary (Matrix (Fin p) (Fin p) ℍ[ℝ])) (lam : Fin p → ℝ),
        U.valᴴ * A * U.val =
          Matrix.diagonal (fun i => (lam i : ℍ[ℝ])) := by
  intro p
  induction p with
  | zero =>
      intro A hA
      exact ⟨1, fun i => Fin.elim0 i, Subsingleton.elim _ _⟩
  | succ p ih =>
      intro A hA
      obtain ⟨lam, v, hv, hAv⟩ := exists_unit_eigenvector hA
      obtain ⟨U, hUcol⟩ := exists_unitary_firstColumn v hv
      let B : Matrix (Fin (p + 1)) (Fin (p + 1)) ℍ[ℝ] :=
        U.valᴴ * A * U.val
      have hB : B.IsHermitian := Matrix.isHermitian_conjTranspose_mul_mul U.val hA
      have hUe : U.val *ᵥ Pi.single 0 1 = v := by
        funext i
        simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using hUcol i
      have hU1 : U.valᴴ * U.val = 1 := by
        simpa only [Matrix.star_eq_conjTranspose] using U.property.1
      have hUstarv : U.valᴴ *ᵥ v = Pi.single 0 1 := by
        rw [← hUe, Matrix.mulVec_mulVec, hU1, Matrix.one_mulVec]
      have hBe : B *ᵥ Pi.single 0 1 = lam • Pi.single 0 1 := by
        dsimp only [B]
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hUe, hAv,
          Matrix.mulVec_smul, hUstarv]
      have hBcol (i : Fin (p + 1)) :
          B i 0 = (lam • (Pi.single 0 (1 : ℍ[ℝ]) : Fin (p + 1) → ℍ[ℝ])) i := by
        simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using congrFun hBe i
      let T := B.submatrix Fin.succ Fin.succ
      have hT : T.IsHermitian := hB.submatrix Fin.succ
      obtain ⟨V, mu, hV⟩ := ih T hT
      have hBblock : B = blockSucc (lam : ℍ[ℝ]) T := by
        apply Matrix.ext
        intro i j
        refine Fin.cases ?_ (fun i => ?_) i
        · refine Fin.cases ?_ (fun j => ?_) j
          · simpa [← Algebra.algebraMap_eq_smul_one] using hBcol 0
          · have hrow := hB.apply 0 j.succ
            rw [hBcol] at hrow
            simpa using hrow.symm
        · refine Fin.cases ?_ (fun j => ?_) j
          · simpa using hBcol i.succ
          · rfl
      refine ⟨U * blockSuccUnitary V, Fin.cons lam mu, ?_⟩
      change (U.val *
          blockSucc 1 V.val)ᴴ * A *
          (U.val * blockSucc 1 V.val) = _
      simp only [Matrix.conjTranspose_mul, blockSucc_conjTranspose, star_one]
      have heq :
          (blockSucc 1 V.valᴴ) * B * blockSucc 1 V.val =
            Matrix.diagonal (fun i => ((Fin.cons lam mu : Fin (p + 1) → ℝ) i : ℍ[ℝ])) := by
        rw [hBblock, blockSucc_mul, blockSucc_mul, one_mul, mul_one, hV,
          blockSucc_diagonal]
        congr 1
        funext i
        exact Fin.cases rfl (fun _ => rfl) i
      simpa only [B, Matrix.mul_assoc] using heq

/-- A selected quaternion eigenframe and its real eigenvalue list.  The
decomposition is proved above; this structure does not postulate it. -/
structure EigenDecomposition {p : ℕ} (A : Matrix (Fin p) (Fin p) ℍ[ℝ]) where
  frame : unitary (Matrix (Fin p) (Fin p) ℍ[ℝ])
  values : Fin p → ℝ
  diagonalization : frame.valᴴ * A * frame.val =
    Matrix.diagonal (fun i => (values i : ℍ[ℝ]))

def eigenDecomposition {p : ℕ} (A : Matrix (Fin p) (Fin p) ℍ[ℝ])
    (hA : A.IsHermitian) : EigenDecomposition A :=
  let h := exists_unitary_diagonalization p A hA
  ⟨h.choose, h.choose_spec.choose, h.choose_spec.choose_spec⟩

theorem EigenDecomposition.reconstruct {p : ℕ}
    {A : Matrix (Fin p) (Fin p) ℍ[ℝ]} (D : EigenDecomposition A) :
    D.frame.val *
        Matrix.diagonal (fun i => (D.values i : ℍ[ℝ])) * D.frame.valᴴ = A := by
  have hU : D.frame.val * D.frame.valᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using D.frame.property.2
  rw [← D.diagonalization]
  simp only [← Matrix.mul_assoc, hU, Matrix.one_mul]
  rw [Matrix.mul_assoc, hU, Matrix.mul_one]

theorem EigenDecomposition.values_nonneg {p : ℕ}
    {A : Matrix (Fin p) (Fin p) ℍ[ℝ]} (D : EigenDecomposition A)
    (hA : PosSemidef A) (i : Fin p) : 0 ≤ D.values i := by
  have h := hA.congruence D.frame.val
  rw [D.diagonalization] at h
  simpa using h.diag_re_nonneg i

/-- The square-root definition agrees with the product of the real quaternion
eigenvalues on the entire positive cone, including singular matrices. -/
theorem EigenDecomposition.positiveDeterminant_eq_prod {p : ℕ}
    {A : Matrix (Fin p) (Fin p) ℍ[ℝ]} (D : EigenDecomposition A)
    (hA : PosSemidef A) : positiveDeterminant A = ∏ i, D.values i := by
  have hU : D.frame.valᴴ * D.frame.val = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using D.frame.property.1
  have h := positiveDeterminant_congruence hA D.frame.val
  rw [D.diagonalization, positiveDeterminant_diagonal D.values (D.values_nonneg hA),
    hU] at h
  have hone : positiveDeterminant (1 : Matrix (Fin p) (Fin p) ℍ[ℝ]) = 1 := by
    simp [positiveDeterminant, complexRepresentation_one]
  rw [hone, one_mul] at h
  exact h.symm

/-- Every quaternion Hermitian eigenvalue occurs twice in the complex
characteristic polynomial of the representation. -/
theorem EigenDecomposition.complex_charpoly {p : ℕ}
    {A : Matrix (Fin p) (Fin p) ℍ[ℝ]} (D : EigenDecomposition A) :
    (complexRepresentation A).charpoly =
      ∏ i, (X - C (D.values i : ℂ)) ^ 2 := by
  have hU := complexRepresentation_unitary D.frame.property
  have hU2 : complexRepresentation D.frame.val * (complexRepresentation D.frame.val)ᴴ = 1 := by
    simpa only [Matrix.star_eq_conjTranspose] using hU.2
  have hdiag := congrArg (fun M : Matrix (Fin p) (Fin p) ℍ[ℝ] => complexRepresentation M) D.diagonalization
  rw [complexRepresentation_congruence, complexRepresentation_diagonal] at hdiag
  have hchar : (complexRepresentation A).charpoly =
      (Matrix.diagonal (fun ia : Fin p × Fin 2 => (D.values ia.1 : ℂ))).charpoly := by
    rw [← hdiag, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, hU2, Matrix.one_mul]
  rw [hchar, Matrix.charpoly_diagonal, Fintype.prod_prod_type]
  simp [Fin.prod_univ_two, pow_two]

end Wishart.QuaternionMatrix
end
end CanonicalSource4

section CanonicalSource5
/- Source: Wishart/QuaternionCone.lean -/



/-!
# The ordinary quaternion positive cone and its square root

The faithful complex representation is compared with the quaternion quadratic
form, and the square root is obtained by the actual complex functional
calculus.  The quaternion spectral decomposition proves that its value lies in
the representation's image.  Thus measurability of the square root does not
require a measurable choice of an eigenframe.
-/

noncomputable section
open Matrix MeasureTheory
open scoped Classical Quaternion Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator Ring

namespace Wishart.QuaternionMatrix

variable {n : Type*} [Fintype n] [DecidableEq n]

theorem quadratic_eq_real {A : Matrix n n ℍ[ℝ]} (hA : A.IsHermitian)
    (v : n → ℍ[ℝ]) :
    star v ⬝ᵥ (A *ᵥ v) = ((star v ⬝ᵥ (A *ᵥ v)).re : ℍ[ℝ]) :=
  Quaternion.star_eq_self.mp (hA.star_dotProduct_mulVec_comm v v)

theorem complexQuadratic_column_eq_real {A : Matrix n n ℍ[ℝ]}
    (hA : A.IsHermitian) (v : n → ℍ[ℝ]) :
    star (columnRepresentation v) ⬝ᵥ
        (complexRepresentation A *ᵥ columnRepresentation v) =
      ((star v ⬝ᵥ (A *ᵥ v)).re : ℂ) := by
  rw [complexQuadratic_column, quadratic_eq_real hA v, toComplexMatrix_real]
  simp

/-- The cone used by the formalization is exactly positivity of every ordinary
quaternion Hermitian quadratic form. -/
theorem posSemidef_iff_quadratic (A : Matrix n n ℍ[ℝ]) :
    PosSemidef A ↔ A.IsHermitian ∧
      ∀ v : n → ℍ[ℝ], 0 ≤ (star v ⬝ᵥ (A *ᵥ v)).re := by
  constructor
  · intro hA
    refine ⟨hA.isHermitian, fun v => ?_⟩
    have h := Matrix.PosSemidef.dotProduct_mulVec_nonneg hA (columnRepresentation v)
    rw [complexQuadratic_column_eq_real hA.isHermitian v] at h
    exact (RCLike.nonneg_iff.mp h).1
  · rintro ⟨hA, hq⟩
    apply Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    refine ⟨(isHermitian_complexRepresentation_iff A).mpr hA, ?_⟩
    intro z
    obtain ⟨v, rfl⟩ := columnRepresentationLinearEquiv.surjective z
    rw [columnRepresentationLinearEquiv_apply, complexQuadratic_column_eq_real hA v]
    exact RCLike.nonneg_iff.mpr ⟨hq v, by simp⟩

theorem posDef_iff_quadratic (A : Matrix n n ℍ[ℝ]) :
    PosDef A ↔ A.IsHermitian ∧
      ∀ v : n → ℍ[ℝ], v ≠ 0 → 0 < (star v ⬝ᵥ (A *ᵥ v)).re := by
  constructor
  · intro hA
    refine ⟨hA.isHermitian, fun v hv => ?_⟩
    have hv' : columnRepresentation v ≠ 0 := by
      intro hz
      apply hv
      apply columnRepresentationLinearEquiv.injective
      change columnRepresentation v = columnRepresentation 0
      calc
        columnRepresentation v = 0 := hz
        _ = columnRepresentation 0 := columnRepresentation_zero.symm
    have h := Matrix.PosDef.dotProduct_mulVec_pos hA hv'
    rw [complexQuadratic_column_eq_real hA.isHermitian v] at h
    exact (RCLike.pos_iff.mp h).1
  · rintro ⟨hA, hq⟩
    apply Matrix.posDef_iff_dotProduct_mulVec.mpr
    refine ⟨(isHermitian_complexRepresentation_iff A).mpr hA, ?_⟩
    intro z hz
    obtain ⟨v, rfl⟩ := columnRepresentationLinearEquiv.surjective z
    have hv : v ≠ 0 := by
      intro hv
      apply hz
      simpa [hv] using columnRepresentationLinearEquiv.map_zero
    rw [columnRepresentationLinearEquiv_apply, complexQuadratic_column_eq_real hA v]
    exact RCLike.pos_iff.mpr ⟨hq v hv, by simp⟩

/-- A continuous linear left inverse of the faithful representation, defined
on the entire complex ambient space. -/
def representationLeftInverse :
    Matrix (n × Fin 2) (n × Fin 2) ℂ →ₗ[ℝ] Matrix n n ℍ[ℝ] where
  toFun A := Matrix.of fun i j =>
    ⟨(A (i,0) (j,0)).re, (A (i,0) (j,0)).im,
      -(A (i,1) (j,0)).re, (A (i,1) (j,0)).im⟩
  map_add' A B := by ext i j <;> simp [add_comm]
  map_smul' r A := by ext i j <;> simp [QuaternionAlgebra.smul_mk]

@[simp] theorem representationLeftInverse_representation (A : Matrix n n ℍ[ℝ]) :
    representationLeftInverse (complexRepresentation A) = A := by
  ext i j <;> simp [representationLeftInverse, complexRepresentation_apply,
    Quaternion.toComplexMatrix_apply]

def sqrt (A : Matrix n n ℍ[ℝ]) : Matrix n n ℍ[ℝ] :=
  representationLeftInverse (CFC.sqrt (complexRepresentation A))

theorem measurable_sqrt : Measurable (sqrt : Matrix n n ℍ[ℝ] → _) :=
  representationLeftInverse.continuous_of_finiteDimensional.measurable.comp
    (CFC.measurable_sqrt.comp continuous_complexRepresentation.measurable)

theorem exists_posSemidef_square_root {p : ℕ}
    {A : Matrix (Fin p) (Fin p) ℍ[ℝ]} (hA : PosSemidef A) :
    ∃ R : Matrix (Fin p) (Fin p) ℍ[ℝ], PosSemidef R ∧ R * R = A := by
  let D := eigenDecomposition A hA.isHermitian
  let E : Matrix (Fin p) (Fin p) ℍ[ℝ] :=
    Matrix.diagonal (fun i => (Real.sqrt (D.values i) : ℍ[ℝ]))
  let R := D.frame.val * E * star D.frame.val
  have hE : PosSemidef E := by
    unfold PosSemidef E
    rw [complexRepresentation_diagonal]
    exact Matrix.PosSemidef.diagonal fun _ =>
      RCLike.nonneg_iff.mpr ⟨Real.sqrt_nonneg _, by simp⟩
  refine ⟨R, ?_, ?_⟩
  · simpa only [R, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]
      using hE.congruence (star D.frame.val)
  · have hE2 : E * E = Matrix.diagonal (fun i => (D.values i : ℍ[ℝ])) := by
      dsimp only [E]
      rw [Matrix.diagonal_mul_diagonal]
      congr 1
      funext i
      rw [← Quaternion.coe_mul, ← pow_two, Real.sq_sqrt (D.values_nonneg hA i)]
    calc
      R * R = D.frame.val * (E * E) * star D.frame.val := by
        simp only [R, Matrix.mul_assoc, ← Matrix.mul_assoc (star D.frame.val) D.frame.val,
          D.frame.property.1, Matrix.one_mul]
      _ = A := by rw [hE2]; exact D.reconstruct

theorem complexRepresentation_sqrt {p : ℕ}
    {A : Matrix (Fin p) (Fin p) ℍ[ℝ]} (hA : PosSemidef A) :
    complexRepresentation (sqrt A) = CFC.sqrt (complexRepresentation A) := by
  obtain ⟨R, hR, hR2⟩ := exists_posSemidef_square_root hA
  have h := CFC.sqrt_unique
    (show complexRepresentation R * complexRepresentation R = complexRepresentation A by
      rw [← complexRepresentation_mul, hR2]) (Matrix.PosSemidef.nonneg hR)
  rw [sqrt, h, representationLeftInverse_representation]

theorem PosSemidef.sqrt {p : ℕ} {A : Matrix (Fin p) (Fin p) ℍ[ℝ]}
    (hA : PosSemidef A) : PosSemidef (sqrt A) := by
  unfold PosSemidef
  rw [complexRepresentation_sqrt hA]
  exact Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg _)

theorem sqrt_mul_self {p : ℕ} {A : Matrix (Fin p) (Fin p) ℍ[ℝ]}
    (hA : PosSemidef A) : sqrt A * sqrt A = A := by
  apply complexRepresentation_injective
  rw [complexRepresentation_mul, complexRepresentation_sqrt hA]
  exact CFC.sqrt_mul_sqrt_self _ (Matrix.PosSemidef.nonneg hA)

theorem PosDef.sqrt {p : ℕ} {A : Matrix (Fin p) (Fin p) ℍ[ℝ]}
    (hA : PosDef A) : PosDef (sqrt A) := by
  unfold PosDef
  rw [complexRepresentation_sqrt hA.posSemidef]
  exact Matrix.isStrictlyPositive_iff_posDef.mp
    (Matrix.isStrictlyPositive_iff_posDef.mpr hA).sqrt

end Wishart.QuaternionMatrix
end
end CanonicalSource5
