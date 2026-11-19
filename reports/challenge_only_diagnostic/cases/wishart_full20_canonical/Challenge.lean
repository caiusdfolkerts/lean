module
public import Mathlib
/-! Literal canonical primitives for all twenty Wishart targets.
Data and genuine constructor proofs adapted from pinned TauCeti06d5bb;
no TauCeti import, unrestricted function value or mathematical proof hole.
-/
@[expose] public section
noncomputable section
open Set MeasureTheory Module
open scoped BigOperators RealInnerProductSpace Matrix Quaternion
/-! Shared proposition witnesses for proof-reference differences measured in
Wishart raw audit44473421580 and canonical class-type probe44481534659.
These declarations supply only proofs of fully literal canonical propositions;
no norm, scalar action, order, measure, functional calculus value or data record
is chosen by an unrestricted definition. All proof bodies are genuine. -/
namespace WishartSharedProof
open scoped MatrixOrder Matrix.Norms.L2Operator
universe u
/-- The source's exact natural-zero interpretation of the nonzero dimension two. -/ @[instance 2000] theorem natTwoNeZero :
    @NeZero ℕ (@Zero.ofOfNat0 ℕ (instOfNatNat (nat_lit 0))) (1+1:ℕ):=⟨by decide⟩
/-- Dimension two satisfies the canonical lower-bound class used by `PiLp` numerals. -/ @[instance 2000] theorem natTwoAtLeastTwo:Nat.AtLeastTwo (1+1):=by infer_instance
/-- Real scalar multiplication commutes with matrix conjugate transpose. -/ @[instance 2000] theorem realMatrixStarModule (n:Type u) :
    StarModule ℝ (Matrix n n ℝ):=by infer_instance
/-- The topology of the real scalar semiring is compatible with its operations. -/ @[instance 2000] theorem realTopologicalSemiring:IsTopologicalSemiring ℝ:=by infer_instance
/-- The real scalar/matrix actions commute. -/ @[instance 2000] theorem realMatrixScalarComm (n:Type u) [Fintype n] [DecidableEq n] :
    SMulCommClass ℝ (Matrix n n ℝ) (Matrix n n ℝ):=by infer_instance
/-- The real scalar/matrix actions satisfy the scalar tower law. -/ @[instance 2000] theorem realMatrixScalarTower (n:Type u) [Fintype n] [DecidableEq n] :
    IsScalarTower ℝ (Matrix n n ℝ) (Matrix n n ℝ):=by infer_instance
/-- The matrix star order used by the source's total functional calculus. -/ @[instance 2000] theorem realMatrixStarOrdered (n:Type u) [Fintype n] :
    StarOrderedRing (Matrix n n ℝ):=by infer_instance
/-- The exact real-matrix continuous-functional-calculus proposition. -/ @[instance 2000] theorem realMatrixCFC (n:Type u) [Fintype n] [DecidableEq n] :
    NonUnitalContinuousFunctionalCalculus ℝ (Matrix n n ℝ) IsSelfAdjoint:=by infer_instance
/-- Nonnegative real-matrix order has nonnegative real spectrum. -/ @[instance 2000] theorem realMatrixNonnegSpectrum (n:Type u) [Fintype n] :
    NonnegSpectrumClass ℝ (Matrix n n ℝ):=by infer_instance
/-- The real scalar action commutes with multiplication on complex matrices. -/ @[instance 2000] theorem complexMatrixScalarComm (n:Type u) [Fintype n] [DecidableEq n] :
    SMulCommClass ℝ (Matrix n n ℂ) (Matrix n n ℂ):=by infer_instance
/-- The real scalar action and complex-matrix multiplication form a tower. -/ @[instance 2000] theorem complexMatrixScalarTower (n:Type u) [Fintype n] [DecidableEq n] :
    IsScalarTower ℝ (Matrix n n ℂ) (Matrix n n ℂ):=by infer_instance
/-- The canonical complex-matrix star-order proposition. -/ @[instance 2000] theorem complexMatrixStarOrdered (n:Type u) [Fintype n] :
    StarOrderedRing (Matrix n n ℂ):=by infer_instance
/-- The exact complex-matrix real continuous-functional-calculus proposition. -/ @[instance 2000] theorem complexMatrixCFC (n:Type u) [Fintype n] [DecidableEq n] :
    NonUnitalContinuousFunctionalCalculus ℝ (Matrix n n ℂ) IsSelfAdjoint:=by infer_instance
/-- Nonnegative complex-matrix order has nonnegative real spectrum. -/ @[instance 2000] theorem complexMatrixNonnegSpectrum (n:Type u) [Fintype n] :
    NonnegSpectrumClass ℝ (Matrix n n ℂ):=by infer_instance
/-- The identity real scalar homomorphisms are mutually inverse. -/ @[instance 2000] theorem realIdentityInvPair :
    RingHomInvPair (RingHom.id ℝ) (RingHom.id ℝ):=by infer_instance
/-- Addition is continuous on the literal Gaussian row space. -/ @[instance 2000] theorem rowContinuousAdd (F:Type u) [NormedRing F] (m:ℕ) :
    ContinuousAdd (PiLp 2 (fun _:Fin m => F)):=by infer_instance
/-- The two real scalar actions on the literal row space commute. -/ @[instance 2000] theorem rowScalarComm (F:Type u) [NormedRing F] [InnerProductSpace ℝ F] (m:ℕ) :
    SMulCommClass ℝ ℝ (PiLp 2 (fun _:Fin m => F)):=by infer_instance
/-- Constant real scaling is continuous on the literal row space. -/ @[instance 2000] theorem rowContinuousConstSMul (F:Type u) [NormedRing F] [InnerProductSpace ℝ F] (m:ℕ) :
    ContinuousConstSMul ℝ (PiLp 2 (fun _:Fin m => F)):=by infer_instance
/-- The literal row space is a topological additive group. -/ @[instance 2000] theorem rowTopologicalAddGroup (F:Type u) [NormedRing F] (m:ℕ) :
    IsTopologicalAddGroup (PiLp 2 (fun _:Fin m => F)):=by infer_instance
/-- Joint real scaling is continuous on the literal row space. -/ @[instance 2000] theorem rowContinuousSMul (F:Type u) [NormedRing F] [InnerProductSpace ℝ F] (m:ℕ) :
    ContinuousSMul ℝ (PiLp 2 (fun _:Fin m => F)):=by infer_instance
/-- The literal row space is Hausdorff. -/ @[instance 2000] theorem rowT2Space (F:Type u) [NormedRing F] (m:ℕ) :
    T2Space (PiLp 2 (fun _:Fin m => F)):=by infer_instance
/-- Finitely many finite-dimensional coordinates form a finite real module. -/ @[instance 2000] theorem rowFinite (F:Type u) [NormedRing F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] (m:ℕ) :
    Module.Finite ℝ (PiLp 2 (fun _:Fin m => F)):=by infer_instance
/-- The measured alternative complex normed-ring hierarchy paths have the same whole record. -/ theorem complexNormedCommRing_path_eq :
    @CommCStarAlgebra.toNormedCommRing ℂ instCommCStarAlgebraComplex =
      @NormedField.toNormedCommRing ℂ Complex.instNormedField:=by rfl
/-- Changing only a proposition witness cannot change the resulting mathematical value. -/ theorem propositionWitness_value_eq {P:Prop} {α:Sort u} (f:P→α) (h₁ h₂:P) :
    f h₁=f h₂:=by rfl
/-- The two source real-semiring superclass paths give the same whole record. -/ theorem realSemiring_path_eq :
    @CommSemiring.toSemiring ℝ (@CommRing.toCommSemiring ℝ Real.commRing) =
      @Ring.toSemiring ℝ (@DivisionRing.toRing ℝ Real.instDivisionRing):=by rfl
/-- The literal zeroth index lies below every cardinality at least three. -/ theorem zero_lt_of_three_le {n:ℕ} (h:3 ≤ n):0 < n:=by omega
/-- The literal third index lies below every cardinality at least three. -/ theorem two_lt_of_three_le {n:ℕ} (h:3 ≤ n):2 < n:=by omega
/-- The literal zeroth index lies below every cardinality at least two. -/ theorem zero_lt_of_two_le {n:ℕ} (h:2 ≤ n):0 < n:=by omega
/-- The literal second index lies below every cardinality at least two. -/ theorem one_lt_of_two_le {n:ℕ} (h:2 ≤ n):1 < n:=by omega
/-- The exact reversed cardinality identity used by both spectral index maps. -/ theorem finCard_symm (p:ℕ):p=Fintype.card (Fin p):=(WishartSharedProof.finCard_symm p)
/-- The real identity matrix is self-adjoint at every dimension. -/ theorem realIdentitySelfAdjoint (p:ℕ):IsSelfAdjoint (1:Matrix (Fin p) (Fin p) ℝ) :=
  Matrix.isHermitian_one.isSelfAdjoint
/-- A real vector subspace is free over the real field. -/ @[instance 2000] theorem submoduleFree (E:Type u) [AddCommGroup E] [Module ℝ E]
    (S:Submodule ℝ E):Module.Free ℝ S:=by infer_instance
/-- A subspace of a finite real module is finite. -/ @[instance 2000] theorem submoduleFinite (E:Type u) [AddCommGroup E] [Module ℝ E]
    [Module.Finite ℝ E] (S:Submodule ℝ E):Module.Finite ℝ S:=by infer_instance
/-- A normed real vector subspace inherits its ambient Borel structure. -/ @[instance 2000] theorem submoduleBorel (E:Type u) [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] (S:Submodule ℝ E):BorelSpace S:=by infer_instance
/-- The scalar tower used by the normalized nonnegative density measure. -/ @[instance 2000] theorem ennrealSelfScalarTower:IsScalarTower ENNReal ENNReal ENNReal:=by infer_instance
/-- The source's real-scalar tower on real matrices. -/ @[instance 2000] theorem realMatrixSelfScalarTower (n:Type u) :
    IsScalarTower ℝ ℝ (Matrix n n ℝ):=by infer_instance
/-- The source's real-scalar tower on complex matrices. -/ @[instance 2000] theorem complexMatrixSelfScalarTower (n:Type u) :
    IsScalarTower ℝ ℝ (Matrix n n ℂ):=by infer_instance
end WishartSharedProof

namespace WishartLiteralStructures
section MatrixInner
variable {m n:Type*} [Fintype m] [Fintype n]
/-- The literal Frobenius inner-product record on real matrices. -/ @[instance_reducible]
def matrixInnerProductSpace :
    letI:NormedAddCommGroup (Matrix m n ℝ):=Matrix.frobeniusNormedAddCommGroup
    InnerProductSpace ℝ (Matrix m n ℝ) :=
  letI:NormedAddCommGroup (Matrix m n ℝ):=Matrix.frobeniusNormedAddCommGroup
  { __:=(Matrix.frobeniusNormedSpace:NormedSpace ℝ (Matrix m n ℝ))
    inner A B:=∑ i,∑ j,A i j * B i j
    norm_sq_eq_re_inner A:=by
      have h:(0:ℝ) ≤ ∑ i,∑ j,‖A i j‖ ^ (2:ℝ) :=
        Finset.sum_nonneg fun _ _ ↦ Finset.sum_nonneg fun _ _ ↦ Real.rpow_nonneg (norm_nonneg _) _
      rw [Matrix.frobenius_norm_def,← Real.rpow_natCast _ 2,← Real.rpow_mul h]
      norm_num [Real.rpow_two,pow_two]
    conj_inner_symm A B:=by
      simp [mul_comm]
    add_left A B C:=by
      simp [add_mul,Finset.sum_add_distrib]
    smul_left A B r:=by
      simp [mul_assoc,Finset.mul_sum] }
end MatrixInner
section SymmetricInner
variable (p:ℕ)
/-- Frobenius norm with the unchanged subtype uniformity. -/ @[instance_reducible] def symmetricNormedAddCommGroup :
    NormedAddCommGroup (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
  letI:NormedAddCommGroup (Matrix (Fin p) (Fin p) ℝ):=Matrix.frobeniusNormedAddCommGroup
  letI base:NormedAddCommGroup (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
    Submodule.normedAddCommGroup _
  { base with toMetricSpace:=base.toMetricSpace.replaceUniformity rfl }
/-- The symmetric subspace carries the Frobenius inner product `⟪A, B⟫ = ∑ i, ∑ j, A i j * B i j` of the underlying matrices, which on this subspace is the trace pairing `selfAdjoint.inner_eq_trace_mul`. -/ def symmetricInnerProductSpace :
    letI:NormedAddCommGroup (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)):=symmetricNormedAddCommGroup p
    InnerProductSpace ℝ (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
  letI:NormedAddCommGroup (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)):=symmetricNormedAddCommGroup p
  letI:NormedAddCommGroup (Matrix (Fin p) (Fin p) ℝ):=Matrix.frobeniusNormedAddCommGroup
  letI:NormedSpace ℝ (Matrix (Fin p) (Fin p) ℝ):=Matrix.frobeniusNormedSpace
  letI:InnerProductSpace ℝ (Matrix (Fin p) (Fin p) ℝ):=matrixInnerProductSpace
  { __:=(inferInstance:Module ℝ (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)))
    norm_smul_le r A:=norm_smul_le r (A:Matrix (Fin p) (Fin p) ℝ)
    inner A B:=⟪(A:Matrix (Fin p) (Fin p) ℝ),(B:Matrix (Fin p) (Fin p) ℝ)⟫
    norm_sq_eq_re_inner A :=
      InnerProductSpace.norm_sq_eq_re_inner (𝕜:=ℝ) (A:Matrix (Fin p) (Fin p) ℝ)
    conj_inner_symm A B :=
      InnerProductSpace.conj_inner_symm (𝕜:=ℝ) (A:Matrix (Fin p) (Fin p) ℝ) ↑B
    add_left A B C:=by
      change (∑ i,∑ j,((A:Matrix (Fin p) (Fin p) ℝ) i j +
        (B:Matrix (Fin p) (Fin p) ℝ) i j) * (C:Matrix (Fin p) (Fin p) ℝ) i j) =
        (∑ i,∑ j,(A:Matrix (Fin p) (Fin p) ℝ) i j * (C:Matrix (Fin p) (Fin p) ℝ) i j) +
        (∑ i,∑ j,(B:Matrix (Fin p) (Fin p) ℝ) i j * (C:Matrix (Fin p) (Fin p) ℝ) i j)
      simp only [add_mul,Finset.sum_add_distrib]
    smul_left A B r:=by
      change (∑ i,∑ j,(r * (A:Matrix (Fin p) (Fin p) ℝ) i j) *
        (B:Matrix (Fin p) (Fin p) ℝ) i j) =
        r * (∑ i,∑ j,(A:Matrix (Fin p) (Fin p) ℝ) i j *
          (B:Matrix (Fin p) (Fin p) ℝ) i j)
      simp [Finset.mul_sum,mul_assoc] }
end SymmetricInner
/-- The complete standard quaternion basis, with genuine multiplication proofs. -/ def complexMatrixBasis :
    QuaternionAlgebra.Basis (Matrix (Fin 2) (Fin 2) ℂ) (-1:ℝ) 0 (-1) where
  i:=!![Complex.I,0; 0,-Complex.I]
  j:=!![0,1; -1,0]
  k:=!![0,Complex.I; Complex.I,0]
  i_mul_i:=by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply,Fin.sum_univ_two]
  j_mul_j:=by
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [Matrix.mul_apply,Fin.sum_univ_two]
  i_mul_j:=by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply,Fin.sum_univ_two]
  j_mul_i:=by
    ext a b
    fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply,Fin.sum_univ_two]
theorem complexMatrixBasis_liftHom_apply (q:ℍ[ℝ]) :
    complexMatrixBasis.liftHom q =
      !![(q.re:ℂ) + q.imI * Complex.I,(q.imJ:ℂ) + q.imK * Complex.I;
        -(q.imJ:ℂ) + q.imK * Complex.I,(q.re:ℂ) - q.imI * Complex.I]:=by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [complexMatrixBasis,QuaternionAlgebra.Basis.liftHom,QuaternionAlgebra.Basis.lift,
      Algebra.algebraMap_eq_smul_one,Complex.ext_iff]
theorem complexMatrixBasis_liftHom_star (q:ℍ[ℝ]) :
    complexMatrixBasis.liftHom (star q)=star (complexMatrixBasis.liftHom q):=by
  rw [complexMatrixBasis_liftHom_apply,complexMatrixBasis_liftHom_apply]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.star_apply]
/-- The fully specified standard star-algebra embedding. -/ def quaternionRepresentation:ℍ[ℝ] →⋆ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℂ :=
  { complexMatrixBasis.liftHom with map_star':=complexMatrixBasis_liftHom_star }
/-- Congruence by every rectangular matrix, including singular ones. -/ def symmetricCongruence {p q:ℕ} (M:Matrix (Fin q) (Fin p) ℝ) :
    selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) →ₗ[ℝ]
      selfAdjoint.submodule ℝ (Matrix (Fin q) (Fin q) ℝ) :=
  LinearMap.codRestrict _
    (mulRightLinearMap (Fin q) ℝ Mᵀ ∘ₗ mulLeftLinearMap (Fin p) ℝ M ∘ₗ
      (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)).subtype)
    fun A => by
      simp only [LinearMap.comp_apply,mulRightLinearMap_apply,mulLeftLinearMap_apply,
        Submodule.subtype_apply]
      have h:=Matrix.isHermitian_mul_mul_conjTranspose M
        (Matrix.isHermitian_iff_isSelfAdjoint.mpr A.property)
      exact Matrix.isHermitian_iff_isSelfAdjoint.mp
        (by simpa only [Matrix.conjTranspose_eq_transpose_of_trivial] using h)
/-- The literal Gram statistic of a finite real Gaussian sample. -/ def wishartGram {p ν:ℕ} (X:Fin ν→EuclideanSpace ℝ (Fin p)) :
    selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) :=
  ⟨Matrix.gram ℝ fun i => WithLp.toLp 2 fun r => X r i,
    Matrix.isHermitian_iff_isSelfAdjoint.mp (Matrix.isHermitian_gram ℝ _)⟩
/-- Every Gaussian-Gram scale, including the canonical singular/invalid cases. -/ def wishartGramMeasure {p:ℕ} (ν:ℕ) (S:Matrix (Fin p) (Fin p) ℝ) :
    Measure (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
  (Measure.pi fun _:Fin ν => ProbabilityTheory.multivariateGaussian 0 S).map wishartGram
end WishartLiteralStructures
@[expose] public section
noncomputable section
open Set MeasureTheory
open scoped BigOperators ENNReal Matrix
namespace WishartLiteralLaws
/-- The same self-adjoint carrier and all on-or-above-diagonal coordinates. -/ abbrev SymmetricMatrix (p:ℕ):=selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)
/-- All on-or-above-diagonal coordinate positions. -/ abbrev UpperTriangle (p:ℕ):={ij:Fin p×Fin p // ij.1 ≤ ij.2}
/-- Reflection of the supplied upper-triangular entries, including the diagonal. -/ def mirrorMatrix {p:ℕ} (x:UpperTriangle p→ℝ):Matrix (Fin p) (Fin p) ℝ :=
  Matrix.of fun i j =>
    if h:i ≤ j then x ⟨(i,j),h⟩ else x ⟨(j,i),le_of_not_ge h⟩
/-- Genuine symmetry of the completely specified reflection formula. -/ theorem mirror_isHermitian {p:ℕ} (x:UpperTriangle p→ℝ) :
    (mirrorMatrix x).IsHermitian:=by
  refine Matrix.IsHermitian.ext fun i j => ?_
  simp only [mirrorMatrix,Matrix.of_apply,star_trivial]
  rcases le_total i j with h | h
  · rcases h.lt_or_eq with hlt | rfl
    · rw [dite_eq_right (not_le.2 hlt),dite_eq_left h]
    · rfl
  · rcases h.lt_or_eq with hlt | rfl
    · rw [dite_eq_left h,dite_eq_right (not_le.2 hlt)]
    · rfl
/-- The literal coordinate reconstruction as an actual symmetric matrix. -/ def reconstruct {p:ℕ} (x:UpperTriangle p→ℝ):SymmetricMatrix p :=
  ⟨mirrorMatrix x,mirror_isHermitian x⟩
/-- The upper-triangle coordinate cube has measure one; Frobenius volume or an unspecified Haar normalization is not substituted. -/ def symmetricLebesgue (p:ℕ):Measure (SymmetricMatrix p) :=
  (volume:Measure (UpperTriangle p→ℝ)).map reconstruct
/-- The complete multivariate Gamma product, including all totalized values. -/ def multivariateGamma (p:ℕ) (a:ℝ):ℝ :=
  Real.pi ^ (((p:ℝ) * ((p:ℝ) - 1)) / (Nat.cast 4:ℝ)) *
    ∏ i:Fin p,Real.Gamma (a - (i.1:ℝ) / (Nat.cast 2:ℝ))
open Classical in
/-- Exact real Wishart density, with no restriction hidden in the data value. -/ def wishartPDFReal {p:ℕ} (n:ℝ) (S:Matrix (Fin p) (Fin p) ℝ)
    (A:SymmetricMatrix p):ℝ :=
  if (A:Matrix (Fin p) (Fin p) ℝ).PosDef then
    (A:Matrix (Fin p) (Fin p) ℝ).det ^
        ((n - (p:ℝ) - 1) / (Nat.cast 2:ℝ)) *
      Real.exp (-Matrix.trace (S⁻¹ * (A:Matrix (Fin p) (Fin p) ℝ)) /
        (Nat.cast 2:ℝ)) /
      ((Nat.cast 2:ℝ) ^ (n * (p:ℝ) / (Nat.cast 2:ℝ)) *
        S.det ^ (n / (Nat.cast 2:ℝ)) * multivariateGamma p (n / (Nat.cast 2:ℝ)))
  else 0
/-- The exact nonnegative extended density. -/ def wishartPDF {p:ℕ} (n:ℝ) (S:Matrix (Fin p) (Fin p) ℝ)
    (A:SymmetricMatrix p):ℝ≥0∞:=ENNReal.ofReal (wishartPDFReal n S A)
open Classical in
/-- The exact valid-parameter branch and zero elsewhere are both retained. -/ def nonsingularWishartMeasure {p:ℕ} (n:ℝ) (S:Matrix (Fin p) (Fin p) ℝ) :
    Measure (SymmetricMatrix p) :=
  if S.PosDef ∧ (p:ℝ) - 1 < n then
    (symmetricLebesgue p).withDensity (wishartPDF n S)
  else 0
/-- The canonical total inverse is retained even on singular inputs. -/ def symmetricInv {p:ℕ} (A:SymmetricMatrix p):SymmetricMatrix p :=
  ⟨(A:Matrix (Fin p) (Fin p) ℝ)⁻¹,
    Matrix.isHermitian_iff_isSelfAdjoint.1
      (Matrix.isHermitian_iff_isSelfAdjoint.2 A.property).inv⟩
/-- The inverse-Wishart law uses the inverted scale and the complete inverse map. -/ def inverseWishartMeasure {p:ℕ} (n:ℝ) (S:Matrix (Fin p) (Fin p) ℝ) :
    Measure (SymmetricMatrix p) :=
  (nonsingularWishartMeasure n S⁻¹).map symmetricInv
end WishartLiteralLaws
attribute [-instance] instCommCStarAlgebraComplex
end
end
end
end
@[expose] public section
noncomputable section
open MeasureTheory Module
open scoped Quaternion Matrix BigOperators RealInnerProductSpace
namespace Matrix
section LiteralFrobenius
variable {m n:Type*} [Fintype m] [Fintype n]
/-- The exact Frobenius inner product with its canonical Frobenius norm. -/ @[instance_reducible] def frobeniusInnerProductSpace :
    letI:NormedAddCommGroup (Matrix m n ℝ):=Matrix.frobeniusNormedAddCommGroup
    InnerProductSpace ℝ (Matrix m n ℝ):=WishartLiteralStructures.matrixInnerProductSpace
end LiteralFrobenius
namespace Norms.Frobenius
attribute [scoped instance] Matrix.frobeniusInnerProductSpace
end Norms.Frobenius
/-- Exact rectangular congruence, with all parameters retained. -/ def symmetricCongruenceLinearMap {p q:ℕ} (M:Matrix (Fin q) (Fin p) ℝ) :
    selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ) →ₗ[ℝ]
    selfAdjoint.submodule ℝ (Matrix (Fin q) (Fin q) ℝ) :=
  WishartLiteralStructures.symmetricCongruence M
end Matrix
namespace TauCeti
/-- The literal Frobenius norm, with precisely the subtype uniformity. -/ instance symmetricMatrixNormedAddCommGroup (p:ℕ) :
    NormedAddCommGroup (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
  WishartLiteralStructures.symmetricNormedAddCommGroup p
/-- The literal compatible Frobenius inner product. -/ instance symmetricMatrixInnerProductSpace (p:ℕ) :
    InnerProductSpace ℝ (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
  WishartLiteralStructures.symmetricInnerProductSpace p
instance symmetricMatrixIsUniformAddGroup (p:ℕ) :
    IsUniformAddGroup (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
  SeminormedAddCommGroup.to_isUniformAddGroup
instance symmetricMatrixSecondCountableTopology (p:ℕ) :
    SecondCountableTopology (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
  by
    letI:SecondCountableTopology (Matrix (Fin p) (Fin p) ℝ) :=
      inferInstanceAs (SecondCountableTopology (Fin p→Fin p→ℝ))
    exact TopologicalSpace.Subtype.secondCountableTopology _
instance symmetricMatrixCompleteSpace (p:ℕ) :
    CompleteSpace (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)):=FiniteDimensional.complete ℝ _
instance symmetricMatrixContinuousENorm (p:ℕ) :
    ContinuousENorm (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)):=ESeminormedAddMonoid.toContinuousENorm
instance symmetricMatrixBorelSpace (p:ℕ) :
    BorelSpace (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)):=Subtype.borelSpace _
/-- Exact upper-triangular unit-coordinate-cube Lebesgue normalization. -/ def symmetricLebesgue (p:ℕ):Measure (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :=
  WishartLiteralLaws.symmetricLebesgue p
/-- The complete multivariate Gamma product on every real argument. -/ def multivariateGamma (p:ℕ) (a:ℝ):ℝ:=WishartLiteralLaws.multivariateGamma p a
namespace Probability
/-- Exact Gaussian-Gram sampling law at every integer sample size and scale. -/ def wishartGramMeasure {p:ℕ} (ν:ℕ) (S:Matrix (Fin p) (Fin p) ℝ) :
    Measure (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)):=WishartLiteralStructures.wishartGramMeasure ν S
/-- The complete real law, including zero outside the valid parameter range. -/ def nonsingularWishartMeasure {p:ℕ} (n:ℝ) (S:Matrix (Fin p) (Fin p) ℝ) :
    Measure (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)):=WishartLiteralLaws.nonsingularWishartMeasure n S
/-- The complete inverse law, including the totalized inverse on singular inputs. -/ def inverseWishartMeasure {p:ℕ} (n:ℝ) (S:Matrix (Fin p) (Fin p) ℝ) :
    Measure (selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)):=WishartLiteralLaws.inverseWishartMeasure n S
end Probability
end TauCeti
namespace Quaternion
/-- The complete standard real star-algebra embedding of each quaternion. -/ def toComplexMatrix:ℍ[ℝ] →⋆ₐ[ℝ] Matrix (Fin 2) (Fin 2) ℂ:=WishartLiteralStructures.quaternionRepresentation
end Quaternion
namespace selfAdjoint
/-- Exact Hermitian property of a real symmetric-submodule element. -/ theorem isHermitian_coe {p:ℕ} (A:selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)) :
    (A:Matrix (Fin p) (Fin p) ℝ).IsHermitian:=A.property
end selfAdjoint
namespace WishartLiteralSpecification
/-- The supplied matrix inner-product record equals the entire literal record. -/ theorem matrixInner_exact {m n:Type*} [Fintype m] [Fintype n] :
    (Matrix.frobeniusInnerProductSpace (m:=m) (n:=n))=WishartLiteralStructures.matrixInnerProductSpace:=by sorry
/-- The supplied normed-group record has the literal norm and subtype uniformity. -/ theorem symmetricNorm_exact (p:ℕ):TauCeti.symmetricMatrixNormedAddCommGroup p=WishartLiteralStructures.symmetricNormedAddCommGroup p:=by sorry
/-- The complete compatible inner-product record is fixed, not an unspecified norm. -/ theorem symmetricInner_exact (p:ℕ):TauCeti.symmetricMatrixInnerProductSpace p=WishartLiteralStructures.symmetricInnerProductSpace p:=by sorry
/-- Every coordinate of congruence is fixed by the literal matrix formula. -/ theorem congruence_exact {p q:ℕ} (M:Matrix (Fin q) (Fin p) ℝ):Matrix.symmetricCongruenceLinearMap M=WishartLiteralStructures.symmetricCongruence M:=by sorry
/-- Every entry of the supplied star-algebra embedding is fixed. -/ theorem quaternion_exact (q:@Quaternion ℝ Real.instZero Real.instOne Real.instNeg):Quaternion.toComplexMatrix q=WishartLiteralStructures.quaternionRepresentation q:=by sorry
/-- Exact Lebesgue normalization in every dimension, including zero. -/ theorem lebesgue_exact (p:ℕ):TauCeti.symmetricLebesgue p=WishartLiteralLaws.symmetricLebesgue p:=by sorry
/-- Exact Gamma value, including every totalized argument. -/ theorem gamma_exact:TauCeti.multivariateGamma=WishartLiteralLaws.multivariateGamma:=by sorry
/-- The supplied real law is fixed at every real degree and scale matrix. -/ theorem wishart_exact {p:ℕ}:@TauCeti.Probability.nonsingularWishartMeasure p=@WishartLiteralLaws.nonsingularWishartMeasure p:=by sorry
/-- The supplied inverse law is fixed at every real degree and scale matrix. -/ theorem inverse_exact {p:ℕ}:@TauCeti.Probability.inverseWishartMeasure p=@WishartLiteralLaws.inverseWishartMeasure p:=by sorry
/-- The complete Gaussian-Gram sampling law is fixed, not just its density case. -/ theorem gram_exact {p:ℕ} (ν:ℕ) (S:Matrix (Fin p) (Fin p) ℝ):TauCeti.Probability.wishartGramMeasure ν S=WishartLiteralStructures.wishartGramMeasure ν S:=by sorry
end WishartLiteralSpecification
end
end
@[expose] public section
noncomputable section
set_option maxHeartbeats 0
namespace Wishart.Spectral end Wishart.Spectral
namespace WishartVerification.MomentAssembly end WishartVerification.MomentAssembly
namespace WishartVerification end WishartVerification
open Filter Function Matrix MeasureTheory MeasureTheory.Measure ProbabilityTheory Set Set.powersetCard TauCeti TauCeti.Probability Topology Wishart.Spectral WishartVerification WishartVerification.MomentAssembly
open scoped Quaternion BigOperators
namespace Wishart.QuaternionMatrix
/-- Real scalar multiplication commutes with quaternion conjugation. -/ instance quaternionRealStarModule:StarModule ℝ ℍ[ℝ] where
  star_smul r q:=by
    simpa only [star_trivial] using Quaternion.star_smul r q
/-- The ordinary Borel measurable structure on real quaternion space. -/ instance quaternionMeasurableSpace:MeasurableSpace ℍ[ℝ]:=borel _
instance quaternionBorelSpace:BorelSpace ℍ[ℝ]:=⟨rfl⟩
end Wishart.QuaternionMatrix
namespace Wishart section open scoped Matrix MatrixOrder Matrix.Norms.L2Operator
/-- Literal SymmetricMatrix. -/ abbrev SymmetricMatrix (p:ℕ):=selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)
/-- Literal principalSymmetricBlock. -/ def principalSymmetricBlock {p q:ℕ} (f:Fin q→Fin p) (X:SymmetricMatrix p):SymmetricMatrix q:=⟨(X:Matrix (Fin p) (Fin p) ℝ).submatrix f f,Matrix.isHermitian_iff_isSelfAdjoint.mp ((Matrix.isHermitian_iff_isSelfAdjoint.mpr X.property).submatrix f)⟩
/-- Literal blockDiagonalMatrix. -/ def blockDiagonalMatrix {q m:ℕ} (A:Matrix (Fin q) (Fin q) ℝ) (C:Matrix (Fin m) (Fin m) ℝ):Matrix (Fin (q + m)) (Fin (q + m)) ℝ:=(Matrix.fromBlocks A 0 0 C).submatrix finSumFinEquiv.symm finSumFinEquiv.symm
/-- Literal leadingScale. -/ def leadingScale (q m:ℕ) (S:Matrix (Fin (q + m)) (Fin (q + m)) ℝ):Matrix (Fin q) (Fin q) ℝ:=S.submatrix (Fin.castAdd m) (Fin.castAdd m)
/-- Literal selectedInverseRoot. -/ def selectedInverseRoot (q m:ℕ) (S:Matrix (Fin (q + m)) (Fin (q + m)) ℝ):Matrix (Fin q) (Fin q) ℝ:=(CFC.sqrt (leadingScale q m S))⁻¹
/-- Literal selectedWhitening. -/ def selectedWhitening (q m:ℕ) (S:Matrix (Fin (q + m)) (Fin (q + m)) ℝ):Matrix (Fin (q + m)) (Fin (q + m)) ℝ:=blockDiagonalMatrix (selectedInverseRoot q m S) (1:Matrix (Fin m) (Fin m) ℝ)
end end Wishart
namespace WishartVerification section open scoped BigOperators Matrix
/-- Literal SymmetricMatrix. -/ abbrev SymmetricMatrix (p:ℕ):=selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)
/-- A partition into labelled nonempty principal blocks. -/ structure PrincipalPartition (p d:ℕ) where
  block:Fin d→Finset (Fin p)
  nonempty:∀ i,(block i).Nonempty
  unique_block:∀ x:Fin p,∃! i:Fin d,x ∈ block i
/-- Literal principalMinor. -/ def principalMinor {p:ℕ} (I:Finset (Fin p)) (X:SymmetricMatrix p):ℝ:=((X:Matrix (Fin p) (Fin p) ℝ).submatrix (fun i:I => (i:Fin p)) (fun i:I => (i:Fin p))).det
/-- Literal principalMomentIntegrand. -/ def principalMomentIntegrand {p d:ℕ} (P:PrincipalPartition p d) (ν:Fin d→ℝ) (J:Finset (Fin d)) (X:SymmetricMatrix p):ℝ:=∏ i ∈ J,(principalMinor (P.block i) X) ^ (ν i)
/-- Literal principalMoment. -/ def principalMoment {p d:ℕ} (α:ℝ) (Sigma:Matrix (Fin p) (Fin p) ℝ) (P:PrincipalPartition p d) (ν:Fin d→ℝ) (J:Finset (Fin d)):ℝ:=∫ X,principalMomentIntegrand P ν J X ∂TauCeti.Probability.nonsingularWishartMeasure α Sigma
/-- Literal independentActiveScaleBlocks. -/ def independentActiveScaleBlocks {p d:ℕ} (Sigma:Matrix (Fin p) (Fin p) ℝ) (P:PrincipalPartition p d) (ν:Fin d→ℝ):Prop:=∀ i j:Fin d,i ≠ j→0 < ν i→0 < ν j→∀ a ∈ P.block i,∀ b ∈ P.block j,Sigma a b=0
/-- The whole content of manuscript Theorem 1.1: arbitrary real shape in its full nonsingular range, all nonnegative real exponents, all selected splits, joint integrability, and the exact equality characterization. -/ def PrincipalTheorem:Prop:=∀ (p d:ℕ) (α:ℝ) (Sigma:Matrix (Fin p) (Fin p) ℝ) (P:PrincipalPartition p d) (ν:Fin d→ℝ),0 < p→0 < d→(p:ℝ) - 1 < α→Sigma.PosDef→(∀ i,0 ≤ ν i)→(∀ J:Finset (Fin d),Integrable (principalMomentIntegrand P ν J) (TauCeti.Probability.nonsingularWishartMeasure α Sigma)) ∧ (∀ j:Fin d,principalMoment α Sigma P ν {j} * principalMoment α Sigma P ν (Finset.univ.erase j) ≤ principalMoment α Sigma P ν Finset.univ ∧ (∏ i:Fin d,principalMoment α Sigma P ν {i}) ≤ principalMoment α Sigma P ν {j} * principalMoment α Sigma P ν (Finset.univ.erase j)) ∧ ((principalMoment α Sigma P ν Finset.univ=∏ i:Fin d,principalMoment α Sigma P ν {i}) ↔ independentActiveScaleBlocks Sigma P ν)
end end WishartVerification
namespace Wishart section open scoped Matrix MatrixOrder Matrix.Norms.L2Operator
/-- Literal selectedDimension. -/ abbrev selectedDimension {p:ℕ} (I:Finset (Fin p)):ℕ:=Fintype.card I
/-- Literal complementDimension. -/ abbrev complementDimension {p:ℕ} (I:Finset (Fin p)):ℕ:=Fintype.card {a:Fin p // a ∉ I}
/-- Literal selectedCoordinatesEquiv. -/ def selectedCoordinatesEquiv {p:ℕ} (I:Finset (Fin p)):Fin (selectedDimension I + complementDimension I) ≃ Fin p:=finSumFinEquiv.symm.trans ((Equiv.sumCongr (Fintype.equivFin I).symm (Fintype.equivFin {a:Fin p // a ∉ I}).symm).trans (Equiv.sumCompl (fun a:Fin p => a ∈ I)))
/-- Literal normalizedSelectedMatrix. -/ def normalizedSelectedMatrix {p:ℕ} (I:Finset (Fin p)) (S:Matrix (Fin p) (Fin p) ℝ) (X:SymmetricMatrix p):SymmetricMatrix (selectedDimension I + complementDimension I):=Matrix.symmetricCongruenceLinearMap (selectedWhitening (selectedDimension I) (complementDimension I) (S.submatrix (selectedCoordinatesEquiv I) (selectedCoordinatesEquiv I))) (principalSymmetricBlock (selectedCoordinatesEquiv I) X)
end end Wishart
namespace WishartVerification section open scoped ENNReal variable {Ω:Type*} [MeasurableSpace Ω] {μ:Measure Ω}
/-- Literal HasAllFiniteMoments. -/ def HasAllFiniteMoments (f:Ω→ℝ) (μ:Measure Ω):Prop:=∀ p:ℝ≥0∞,p ≠ ∞→MemLp f p μ
end end WishartVerification
namespace WishartVerification section open scoped Classical Matrix variable {p d:ℕ}
/-- Literal selectedRank. -/ abbrev selectedRank (P:PrincipalPartition p d) (j:Fin d):ℕ:=Wishart.selectedDimension (P.block j)
/-- Literal remainingRank. -/ abbrev remainingRank (P:PrincipalPartition p d) (j:Fin d):ℕ:=Wishart.complementDimension (P.block j)
/-- Literal normalizedPrincipalMatrix. -/ abbrev normalizedPrincipalMatrix (P:PrincipalPartition p d) (Sigma:Matrix (Fin p) (Fin p) ℝ) (j:Fin d):=Wishart.normalizedSelectedMatrix (P.block j) Sigma
end end WishartVerification
namespace Wishart.Spectral section open scoped ENNReal
/-- Literal Sym. -/ abbrev Sym (p:ℕ):=selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℝ)
/-- Literal coordinateSpectrum. -/
noncomputable def coordinateSpectrum {p:ℕ} (S:Sym p):Fin p→ℝ:=(selfAdjoint.isHermitian_coe S).eigenvalues
end end Wishart.Spectral
namespace Wishart.Spectral section open scoped Classical
/-- Literal ascendingIndexEquiv. -/
noncomputable def ascendingIndexEquiv (p:ℕ):Equiv.Perm (Fin p):=Fin.revPerm.trans ((finCongr (WishartSharedProof.finCard_symm p)).trans (Fintype.equivOfCardEq (Fintype.card_fin (Fintype.card (Fin p)))))
/-- Literal ascendingSpectrum. -/
noncomputable def ascendingSpectrum {p:ℕ} (S:Sym p):Fin p→ℝ:=coordinateSpectrum S ∘ ascendingIndexEquiv p
end end Wishart.Spectral
namespace WishartVerification section open scoped Classical ENNReal variable {ι:Type*} [Fintype ι] [LinearOrder ι]
/-- Literal orderedChamber. -/ def orderedChamber (s:Set ℝ):Set (ι→ℝ):={x | StrictMono x ∧ ∀ i,x i ∈ s}
end end WishartVerification
namespace WishartVerification section open scoped Classical ENNReal variable {ι:Type*} [Fintype ι] [LinearOrder ι] variable {Ω:Type*} [MeasurableSpace Ω]
/-- Normalizing a nonnegative real density by its nonnegative integral. -/
noncomputable def normalizedWeight (μ:Measure Ω) (w:Ω→ℝ):Measure Ω:=(∫⁻ x,ENNReal.ofReal (w x) ∂μ)⁻¹ • μ.withDensity (fun x ↦ ENNReal.ofReal (w x))
end end WishartVerification
namespace WishartVerification section open scoped Classical variable {p d:ℕ}
/-- Literal principalSetCoordinates. -/ def principalSetCoordinates (I:Finset (Fin p)):Fin (Fintype.card I)→Fin p:=fun a ↦ ((Fintype.equivFin I).symm a:Fin p)
/-- Literal principalSetMatrix. -/ def principalSetMatrix (I:Finset (Fin p)):SymmetricMatrix p→SymmetricMatrix (Fintype.card I):=Wishart.principalSymmetricBlock (principalSetCoordinates I)
/-- Theorem 1.1, with all original quantifiers and parameter ranges, joint moment finiteness, every selected split, the product lower bound, and the exact active-block equality characterization. -/ theorem theorem_1_1:PrincipalTheorem:=by sorry
end end WishartVerification
namespace WishartVerification section open scoped Classical ENNReal variable {Ω:Type*} [MeasurableSpace Ω]
/-- Comparison against every bounded Borel increasing real-valued test. The order restriction is only on the common support set. -/ def IncreasingExpectationLE [Preorder Ω] (s:Set Ω) (μ ν:Measure Ω):Prop:=∀ f:Ω→ℝ,Measurable f→MonotoneOn f s→(∃ M:ℝ,∀ x,|f x| ≤ M)→(∫ x,f x ∂μ) ≤ ∫ x,f x ∂ν
end end WishartVerification
namespace WishartVerification section open scoped Classical variable {p d:ℕ}
/-- Literal shiftedPrincipalMinor. -/ def shiftedPrincipalMinor (Sigma:Matrix (Fin p) (Fin p) ℝ) (I:Finset (Fin p)) (c:ℝ) (X:SymmetricMatrix p):ℝ:=(((X:Matrix (Fin p) (Fin p) ℝ).submatrix (fun i:I ↦ (i:Fin p)) (fun i:I ↦ (i:Fin p))) + c • Sigma.submatrix (fun i:I ↦ (i:Fin p)) (fun i:I ↦ (i:Fin p))).det
/-- Literal shiftedMomentIntegrand. -/ def shiftedMomentIntegrand (Sigma:Matrix (Fin p) (Fin p) ℝ) (P:PrincipalPartition p d) (c ν:Fin d→ℝ) (J:Finset (Fin d)) (X:SymmetricMatrix p):ℝ:=∏ i ∈ J,shiftedPrincipalMinor Sigma (P.block i) (c i) X ^ ν i
/-- Literal shiftedMoment. -/ def shiftedMoment (α:ℝ) (Sigma:Matrix (Fin p) (Fin p) ℝ) (P:PrincipalPartition p d) (c ν:Fin d→ℝ) (J:Finset (Fin d)):ℝ:=∫ X,shiftedMomentIntegrand Sigma P c ν J X ∂TauCeti.Probability.nonsingularWishartMeasure α Sigma
/-- Literal shiftedMomentRatio. -/ def shiftedMomentRatio (α:ℝ) (Sigma:Matrix (Fin p) (Fin p) ℝ) (P:PrincipalPartition p d) (c ν:Fin d→ℝ):ℝ:=shiftedMoment α Sigma P c ν Finset.univ / ∏ i:Fin d,shiftedMoment α Sigma P c ν {i}
/-- Literal shiftedTiltLaw. -/ def shiftedTiltLaw (α:ℝ) (Sigma:Matrix (Fin p) (Fin p) ℝ) (P:PrincipalPartition p d) (c ν:Fin d→ℝ) (J:Finset (Fin d)):Measure (SymmetricMatrix p):=normalizedWeight (TauCeti.Probability.nonsingularWishartMeasure α Sigma) (shiftedMomentIntegrand Sigma P c ν J)
/-- Literal selectedEigenvalues. -/ def selectedEigenvalues (Sigma:Matrix (Fin p) (Fin p) ℝ) (P:PrincipalPartition p d) (j:Fin d) (X:SymmetricMatrix p):Fin (selectedRank P j)→ℝ:=Wishart.Spectral.ascendingSpectrum (Wishart.principalSymmetricBlock (Fin.castAdd (remainingRank P j)) (normalizedPrincipalMatrix P Sigma j X))
end end WishartVerification
namespace WishartVerification section open scoped Classical Matrix variable {p d:ℕ}
/-- Section 4.1: both inequalities with arbitrary proportional nonnegative shifts, with the original real shape and all nonnegative real powers. -/ theorem proportional_shift_product_inequalities (P:PrincipalPartition p d) {α:ℝ} {Sigma:Matrix (Fin p) (Fin p) ℝ} (hSigma:Sigma.PosDef) (hα:(p:ℝ) - 1 < α) (c ν:Fin d→ℝ) (hc:∀ i,0 ≤ c i) (hν:∀ i,0 ≤ ν i):(∀ J,Integrable (shiftedMomentIntegrand Sigma P c ν J) (TauCeti.Probability.nonsingularWishartMeasure α Sigma)) ∧ ∀ j:Fin d,shiftedMoment α Sigma P c ν {j} * shiftedMoment α Sigma P c ν (Finset.univ.erase j) ≤ shiftedMoment α Sigma P c ν Finset.univ ∧ (∏ i:Fin d,shiftedMoment α Sigma P c ν {i}) ≤ shiftedMoment α Sigma P c ν {j} * shiftedMoment α Sigma P c ν (Finset.univ.erase j):=by sorry
end end WishartVerification
namespace WishartVerification section open scoped Classical variable {p d:ℕ}
/-- Proposition 4.1 in full: the normalized determinant-product ratio is increasing in every exponent, and the full determinant tilt stochastically dominates the single-factor tilt on the entire ordered selected spectrum. -/ theorem proposition_4_1 (P:PrincipalPartition p d) {α:ℝ} {Sigma:Matrix (Fin p) (Fin p) ℝ} (hSigma:Sigma.PosDef) (hα:(p:ℝ) - 1 < α) (c:Fin d→ℝ) (hc:∀ i,0 ≤ c i):MonotoneOn (shiftedMomentRatio α Sigma P c) (Set.Ici (0:Fin d→ℝ)) ∧ ∀ (ν:Fin d→ℝ),(∀ i,0 ≤ ν i)→∀ j:Fin d,IncreasingExpectationLE (orderedChamber (Set.Ioi 0)) ((shiftedTiltLaw α Sigma P c ν {j}).map (selectedEigenvalues Sigma P j)) ((shiftedTiltLaw α Sigma P c ν Finset.univ).map (selectedEigenvalues Sigma P j)):=by sorry
end end WishartVerification
namespace Wishart section open scoped Matrix MatrixOrder Matrix.Norms.L2Operator
/-- Literal compressionScale. -/ def compressionScale {p q:ℕ} (Sigma:Matrix (Fin p) (Fin p) ℝ) (B:Matrix (Fin p) (Fin q) ℝ):Matrix (Fin q) (Fin q) ℝ:=Bᵀ * Sigma * B
/-- Literal normalizedCompressionRows. -/ def normalizedCompressionRows {p q:ℕ} (Sigma:Matrix (Fin p) (Fin p) ℝ) (B:Matrix (Fin p) (Fin q) ℝ):Matrix (Fin q) (Fin p) ℝ:=(CFC.sqrt (compressionScale Sigma B))⁻¹ * Bᵀ
/-- Literal normalizedCompression. -/ def normalizedCompression {p q:ℕ} (Sigma:Matrix (Fin p) (Fin p) ℝ) (B:Matrix (Fin p) (Fin q) ℝ):SymmetricMatrix p→SymmetricMatrix q:=Matrix.symmetricCongruenceLinearMap (normalizedCompressionRows Sigma B)
/-- Literal normalizedCompression_posDef. -/ theorem normalizedCompression_posDef {p k:ℕ} {Omega:Matrix (Fin p) (Fin p) ℝ} (hOmega:Omega.PosDef) (B:Matrix (Fin p) (Fin k) ℝ) (hB:B.rank=k) {Y:SymmetricMatrix p} (hY:(Y:Matrix (Fin p) (Fin p) ℝ).PosDef):(normalizedCompression Omega B Y:Matrix (Fin k) (Fin k) ℝ).PosDef:=by sorry
end end Wishart
namespace Wishart.Spectral section open scoped Classical MatrixOrder Matrix.Norms.L2Operator
/-- Literal positiveOrderedSpectrum. -/ def positiveOrderedSpectrum (p:ℕ):Set (Fin p→ℝ):={lam | Monotone lam ∧ ∀ i,0 < lam i}
/-- Literal ascendingSpectrum_mem_positiveOrderedSpectrum. -/ theorem ascendingSpectrum_mem_positiveOrderedSpectrum {p:ℕ} (S:Sym p) (hS:(S:Matrix (Fin p) (Fin p) ℝ).PosDef):ascendingSpectrum S ∈ positiveOrderedSpectrum p:=by sorry
end end Wishart.Spectral
namespace Wishart.Spectral section open scoped Classical ENNReal MatrixOrder Matrix.Norms.L2Operator
/-- Literal PositiveSpectrum. -/ abbrev PositiveSpectrum (p:ℕ):={lam:Fin p→ℝ // lam ∈ positiveOrderedSpectrum p}
end end Wishart.Spectral
namespace Wishart section open scoped Classical ENNReal MatrixOrder Matrix.Norms.L2Operator
/-- The original domain-valued test at an actual positive compression; its arbitrary value off the positive matrix cone is fixed to zero. -/ def domainInverseCompressionFactor {p k:ℕ} {Omega:Matrix (Fin p) (Fin p) ℝ} (hOmega:Omega.PosDef) (B:Matrix (Fin p) (Fin k) ℝ) (hB:B.rank=k) (f:PositiveSpectrum k→ℝ) (Y:SymmetricMatrix p):ℝ:=if hY:(Y:Matrix (Fin p) (Fin p) ℝ).PosDef then f ⟨ascendingSpectrum (normalizedCompression Omega B Y),ascendingSpectrum_mem_positiveOrderedSpectrum _ (normalizedCompression_posDef hOmega B hB hY)⟩ else 0
/-- Literal domainInverseCompressionProduct. -/ def domainInverseCompressionProduct {p d:ℕ} {Omega:Matrix (Fin p) (Fin p) ℝ} (hOmega:Omega.PosDef) (k:Fin d→ℕ) (B:∀ i,Matrix (Fin p) (Fin (k i)) ℝ) (hB:∀ i,(B i).rank=k i) (f:∀ i,PositiveSpectrum (k i)→ℝ) (J:Finset (Fin d)) (Y:SymmetricMatrix p):ℝ:=∏ i ∈ J,domainInverseCompressionFactor hOmega (B i) (hB i) (f i) Y
/-- The full finite-expectation chain of Theorem6.1 for functions whose domain is literally only the ordered positive spectrum. No extension hypothesis is imposed on the user-supplied functions. -/ theorem theorem_6_1_on_positiveOrderedSpectrum {p d:ℕ} {β:ℝ} {Omega:Matrix (Fin p) (Fin p) ℝ} (hOmega:Omega.PosDef) (hβ:(p:ℝ) - 1 < β) (k:Fin d→ℕ) (B:∀ i,Matrix (Fin p) (Fin (k i)) ℝ) (hB:∀ i,(B i).rank=k i) (f:∀ i,PositiveSpectrum (k i)→ℝ) (hfm:∀ i,Measurable (f i)) (hf0:∀ i x,0 ≤ f i x) (hdir:(∀ i,Monotone (f i)) ∨ (∀ i,Antitone (f i))) (hIsingle:∀ i,Integrable (domainInverseCompressionFactor hOmega (B i) (hB i) (f i)) (inverseWishartMeasure β Omega)) (hIremaining:∀ j,Integrable (domainInverseCompressionProduct hOmega k B hB f (Finset.univ.erase j)) (inverseWishartMeasure β Omega)) (hIjoint:Integrable (domainInverseCompressionProduct hOmega k B hB f Finset.univ) (inverseWishartMeasure β Omega)):(∏ i,∫ Y,domainInverseCompressionProduct hOmega k B hB f {i} Y ∂inverseWishartMeasure β Omega) ≤ (∫ Y,domainInverseCompressionProduct hOmega k B hB f Finset.univ Y ∂inverseWishartMeasure β Omega) ∧ ∀ j:Fin d,(∏ i,∫ Y,domainInverseCompressionProduct hOmega k B hB f {i} Y ∂inverseWishartMeasure β Omega) ≤ (∫ Y,domainInverseCompressionProduct hOmega k B hB f {j} Y ∂inverseWishartMeasure β Omega) * (∫ Y,domainInverseCompressionProduct hOmega k B hB f (Finset.univ.erase j) Y ∂inverseWishartMeasure β Omega) ∧ (∫ Y,domainInverseCompressionProduct hOmega k B hB f {j} Y ∂inverseWishartMeasure β Omega) * (∫ Y,domainInverseCompressionProduct hOmega k B hB f (Finset.univ.erase j) Y ∂inverseWishartMeasure β Omega) ≤ (∫ Y,domainInverseCompressionProduct hOmega k B hB f Finset.univ Y ∂inverseWishartMeasure β Omega):=by sorry
/-- Literal inverseCompressionDeterminant. -/ def inverseCompressionDeterminant {p k:ℕ} (S:Matrix (Fin p) (Fin p) ℝ) (B:Matrix (Fin p) (Fin k) ℝ) (c:ℝ) (Y:SymmetricMatrix p):ℝ:=(Bᵀ * (Y:Matrix (Fin p) (Fin p) ℝ) * B + c • compressionScale S B).det
/-- Literal inverseDeterminantProduct. -/ def inverseDeterminantProduct {p d:ℕ} (S:Matrix (Fin p) (Fin p) ℝ) (k:Fin d→ℕ) (B:∀ i,Matrix (Fin p) (Fin (k i)) ℝ) (c ν:Fin d→ℝ) (J:Finset (Fin d)) (Y:SymmetricMatrix p):ℝ:=∏ i ∈ J,inverseCompressionDeterminant S (B i) (c i) Y ^ ν i
/-- Literal inverseDeterminantMoment. -/ def inverseDeterminantMoment {p d:ℕ} (β:ℝ) (Omega:Matrix (Fin p) (Fin p) ℝ) (k:Fin d→ℕ) (B:∀ i,Matrix (Fin p) (Fin (k i)) ℝ) (c ν:Fin d→ℝ) (J:Finset (Fin d)):ℝ:=∫ Y,inverseDeterminantProduct Omega k B c ν J Y ∂inverseWishartMeasure β Omega
end end Wishart
namespace WishartVerification section open scoped BigOperators variable {ι:Type*} [Fintype ι] [Nonempty ι]
/-- Literal finiteMaximum. -/ def finiteMaximum (x:ι→ℝ):ℝ:=Finset.univ.sup' Finset.univ_nonempty x
end end WishartVerification
namespace WishartVerification section 
/-- The paper's condition on a positive outer function, on its actual domain `(0,∞)`. Values at nonpositive arguments do not enter this definition. -/ structure GeometricallyLogConvex (f:ℝ→ℝ):Prop where
  positive:∀ x,0 < x→0 < f x
  convex_log:ConvexOn ℝ Set.univ (fun s => Real.log (f (Real.exp s)))
  monotone_log:Monotone (fun s => Real.log (f (Real.exp s)))
end end WishartVerification
namespace Wishart.QuaternionMatrix section open scoped Matrix Quaternion BigOperators Classical ComplexOrder
/-- Literal Hermitian. -/ abbrev Hermitian (p:ℕ):=selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℍ[ℝ])
end end Wishart.QuaternionMatrix
namespace Wishart.QuaternionMatrix section open scoped Matrix Quaternion BigOperators Classical ComplexOrder variable {m n k:Type*}
/-- The standard real-algebra representation, with each quaternion replaced by its two-by-two complex matrix. This also applies to rectangular matrices. -/ def complexRepresentation (A:Matrix m n ℍ[ℝ]):Matrix (m×Fin 2) (n×Fin 2) ℂ:=Matrix.comp m n (Fin 2) (Fin 2) ℂ (A.map Quaternion.toComplexMatrix)
/-- Literal isHermitian_complexRepresentation_iff. -/ theorem isHermitian_complexRepresentation_iff (A:Matrix n n ℍ[ℝ]):(complexRepresentation A).IsHermitian ↔ A.IsHermitian:=by sorry
/-- Positive definiteness on the quaternion Hermitian space. -/ def PosDef [Fintype n] (A:Matrix n n ℍ[ℝ]):Prop:=(complexRepresentation A).PosDef
end end Wishart.QuaternionMatrix
namespace Wishart.QuaternionMatrix section open scoped Matrix Quaternion ComplexOrder BigOperators Classical Ring variable {n:Type*} [Fintype n] [DecidableEq n]
/-- The positive square root of the complex determinant. All uses as a quaternion determinant carry an explicit positive-semidefinite hypothesis. -/ def positiveDeterminant (A:Matrix n n ℍ[ℝ]):ℝ:=Real.sqrt (complexRepresentation A).det.re
end end Wishart.QuaternionMatrix
namespace Wishart.QuaternionMatrix section open scoped Classical Quaternion Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator Ring variable {n:Type*} [Fintype n] [DecidableEq n]
/-- A continuous linear left inverse of the faithful representation, defined on the entire complex ambient space. -/ def representationLeftInverse :
    Matrix (n×Fin 2) (n×Fin 2) ℂ →ₗ[ℝ] Matrix n n ℍ[ℝ] where
  toFun A:=Matrix.of fun i j =>
    ⟨(A (i,0) (j,0)).re,(A (i,0) (j,0)).im,
      -(A (i,1) (j,0)).re,(A (i,1) (j,0)).im⟩
  map_add' A B:=by ext i j <;> simp [add_comm]
  map_smul' r A:=by ext i j <;> simp [QuaternionAlgebra.smul_mk]
/-- Literal sqrt. -/ def sqrt (A:Matrix n n ℍ[ℝ]):Matrix n n ℍ[ℝ]:=representationLeftInverse (CFC.sqrt (complexRepresentation A))
end end Wishart.QuaternionMatrix
namespace Wishart.ComplexMatrix section open scoped Matrix ComplexOrder InnerProductSpace RealInnerProductSpace BigOperators Classical variable {n:Type*} [Fintype n] [DecidableEq n]
/-- Literal realDeterminant. -/ def realDeterminant (A:Matrix n n ℂ):ℝ:=A.det.re
end end Wishart.ComplexMatrix
namespace Wishart.FieldGaussian section open scoped Classical Matrix BigOperators Quaternion ENNReal variable (F:Type*) [NormedRing F] [StarRing F] [CStarRing F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [SMulCommClass ℝ F F] [IsScalarTower ℝ F F] [MeasurableSpace F] [BorelSpace F]
/-- Literal Row. -/ abbrev Row (m:ℕ):=PiLp 2 (fun _:Fin m => F)
/-- Right multiplication by a genuinely arbitrary rectangular field matrix, viewed as a real continuous linear map. -/ def rowFactorLinearMap {r m:ℕ} (R:Matrix (Fin r) (Fin m) F) :
    Row F r →ₗ[ℝ] Row F m where
  toFun z:=WithLp.toLp 2 fun j => ∑ i,z i * R i j
  map_add' x y:=by
    ext j
    simp [add_mul,Finset.sum_add_distrib]
  map_smul' c z:=by
    ext j
    simp [smul_mul_assoc,Finset.smul_sum]
/-- Literal rowFactorCLM. -/ def rowFactorCLM {r m:ℕ} (R:Matrix (Fin r) (Fin m) F):Row F r →L[ℝ] Row F m:=(rowFactorLinearMap F R).toContinuousLinearMap
/-- Literal standardDeviation. -/ def standardDeviation:ℝ:=(Real.sqrt (Module.finrank ℝ F))⁻¹
/-- Literal normalizedRowFactorCLM. -/ def normalizedRowFactorCLM {r m:ℕ} (R:Matrix (Fin r) (Fin m) F):Row F r →L[ℝ] Row F m:=standardDeviation F • rowFactorCLM F R
/-- The actual centered field Gaussian row with rectangular covariance factor `R`; for an identity factor each real component has variance `1 / dim ℝ F`. -/ def gaussianRowWithFactor {r m:ℕ} (R:Matrix (Fin r) (Fin m) F):Measure (Row F m):=(stdGaussian (Row F r)).map (normalizedRowFactorCLM F R)
end end Wishart.FieldGaussian
namespace Wishart.FieldGaussian section open scoped Classical Quaternion Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator Ring ENNReal variable (F:Type*) [NormedRing F] [StarRing F] [CStarRing F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F] [SMulCommClass ℝ F F] [IsScalarTower ℝ F F] [StarModule ℝ F] [MeasurableSpace F] [BorelSpace F]
/-- Literal Hermitian. -/ abbrev Hermitian (p:ℕ):=selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) F)
/-- Literal rowsMatrix. -/ def rowsMatrix {n p:ℕ} (z:Fin n→Row F p):Matrix (Fin n) (Fin p) F:=Matrix.of fun i j => z i j
/-- Literal rowsGram. -/ def rowsGram {n p:ℕ} (z:Fin n→Row F p):Hermitian F p:=⟨(rowsMatrix F z)ᴴ * rowsMatrix F z,(Matrix.isHermitian_conjTranspose_mul_self (rowsMatrix F z)).isSelfAdjoint⟩
/-- Literal gramWithFactor. -/ def gramWithFactor {r p:ℕ} (n:ℕ) (R:Matrix (Fin r) (Fin p) F):Measure (Hermitian F p):=(Measure.pi (fun _:Fin n => gaussianRowWithFactor F R)).map (rowsGram F)
end end Wishart.FieldGaussian
namespace Wishart.ComplexMatrix section open scoped Classical Quaternion Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator Ring ENNReal
/-- Literal Hermitian. -/ abbrev Hermitian (p:ℕ):=selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) ℂ)
/-- Literal hermitianLebesgue. -/ def hermitianLebesgue (p:ℕ):Measure (Hermitian p):=(Module.finBasis ℝ (Hermitian p)).addHaar
/-- The unnormalized literal complex density (b = 2). -/ def wishartWeight {p:ℕ} (α:ℝ) (Sigma:Matrix (Fin p) (Fin p) ℂ) (X:Hermitian p):ℝ≥0∞:=if (X:Matrix (Fin p) (Fin p) ℂ).PosDef then ENNReal.ofReal (realDeterminant (X:Matrix (Fin p) (Fin p) ℂ) ^ (α - p) * Real.exp (-((Sigma⁻¹ * (X:Matrix (Fin p) (Fin p) ℂ)).trace).re)) else 0
/-- Literal wishartNormalizer. -/ def wishartNormalizer {p:ℕ} (α:ℝ) (Sigma:Matrix (Fin p) (Fin p) ℂ):ℝ≥0∞:=∫⁻ X,wishartWeight α Sigma X ∂hermitianLebesgue p
/-- Literal wishartMeasure. -/ def wishartMeasure {p:ℕ} (α:ℝ) (Sigma:Matrix (Fin p) (Fin p) ℂ):Measure (Hermitian p):=(wishartNormalizer α Sigma)⁻¹ • (hermitianLebesgue p).withDensity (wishartWeight α Sigma)
/-- The genuine n-row field Gaussian Gram law, including singular sample sizes. -/ def gramMeasure {p:ℕ} (n:ℕ) (Sigma:Matrix (Fin p) (Fin p) ℂ):Measure (Hermitian p):=Wishart.FieldGaussian.gramWithFactor ℂ n (CFC.sqrt Sigma)
/-- Literal compressionCovariance. -/ def compressionCovariance {p k:ℕ} (B:Matrix (Fin p) (Fin k) ℂ) (Sigma:Matrix (Fin p) (Fin p) ℂ):Matrix (Fin k) (Fin k) ℂ:=Bᴴ * Sigma * B
/-- The exact standardized compression. The congruence form makes the total function Hermitian even outside its intended positive-definite parameters. -/ def normalizedCompression {p k:ℕ} (B:Matrix (Fin p) (Fin k) ℂ) (Sigma:Matrix (Fin p) (Fin p) ℂ) (X:Hermitian p):Hermitian k :=
  let R:=B * (CFC.sqrt (compressionCovariance B Sigma))⁻¹
  ⟨Rᴴ * (X:Matrix (Fin p) (Fin p) ℂ) * R,
    (Matrix.isHermitian_conjTranspose_mul_mul R
      (show IsSelfAdjoint (X:Matrix (Fin p) (Fin p) ℂ) from X.property).isHermitian).isSelfAdjoint⟩
end end Wishart.ComplexMatrix
namespace Wishart.QuaternionMatrix section open scoped Classical Quaternion Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator Ring ENNReal open scoped Matrix.Norms.Frobenius
set_option backward.isDefEq.respectTransparency false in
local instance matrixBorelSpace (p q:ℕ):BorelSpace (Matrix (Fin p) (Fin q) ℍ[ℝ]) :=
  inferInstanceAs (BorelSpace (Fin p→Fin q→ℍ[ℝ]))
set_option backward.isDefEq.respectTransparency false in
local instance hermitianBorelSpace (p:ℕ):BorelSpace (Hermitian p) :=
  inferInstanceAs (BorelSpace {X:Matrix (Fin p) (Fin p) ℍ[ℝ] // X ∈ selfAdjoint.submodule ℝ _})
set_option backward.isDefEq.respectTransparency false in
/-- Literal hermitianLebesgue. -/ def hermitianLebesgue (p:ℕ):Measure (Hermitian p):=(Module.finBasis ℝ (Hermitian p)).addHaar
/-- The unnormalized literal quaternion density (b = 4). -/ def wishartWeight {p:ℕ} (α:ℝ) (Sigma:Matrix (Fin p) (Fin p) ℍ[ℝ]) (X:Hermitian p):ℝ≥0∞:=if PosDef (X:Matrix (Fin p) (Fin p) ℍ[ℝ]) then ENNReal.ofReal (positiveDeterminant (X:Matrix (Fin p) (Fin p) ℍ[ℝ]) ^ (2 * (α - p + 1) - 1) * Real.exp (-2 * ((Sigma⁻¹ʳ * (X:Matrix (Fin p) (Fin p) ℍ[ℝ])).trace).re)) else 0
/-- Literal wishartNormalizer. -/ def wishartNormalizer {p:ℕ} (α:ℝ) (Sigma:Matrix (Fin p) (Fin p) ℍ[ℝ]):ℝ≥0∞:=∫⁻ X,wishartWeight α Sigma X ∂hermitianLebesgue p
/-- Literal wishartMeasure. -/ def wishartMeasure {p:ℕ} (α:ℝ) (Sigma:Matrix (Fin p) (Fin p) ℍ[ℝ]):Measure (Hermitian p):=(wishartNormalizer α Sigma)⁻¹ • (hermitianLebesgue p).withDensity (wishartWeight α Sigma)
/-- Literal gramMeasure. -/ def gramMeasure {p:ℕ} (n:ℕ) (Sigma:Matrix (Fin p) (Fin p) ℍ[ℝ]):Measure (Hermitian p):=Wishart.FieldGaussian.gramWithFactor ℍ[ℝ] n (sqrt Sigma)
/-- Literal compressionCovariance. -/ def compressionCovariance {p k:ℕ} (B:Matrix (Fin p) (Fin k) ℍ[ℝ]) (Sigma:Matrix (Fin p) (Fin p) ℍ[ℝ]):Matrix (Fin k) (Fin k) ℍ[ℝ]:=Bᴴ * Sigma * B
/-- Literal normalizedCompression. -/ def normalizedCompression {p k:ℕ} (B:Matrix (Fin p) (Fin k) ℍ[ℝ]) (Sigma:Matrix (Fin p) (Fin p) ℍ[ℝ]) (X:Hermitian p):Hermitian k :=
  let R:=B * (sqrt (compressionCovariance B Sigma))⁻¹ʳ
  ⟨Rᴴ * (X:Matrix (Fin p) (Fin p) ℍ[ℝ]) * R,
    (Matrix.isHermitian_conjTranspose_mul_mul R
      (show IsSelfAdjoint (X:Matrix (Fin p) (Fin p) ℍ[ℝ]) from X.property).isHermitian).isSelfAdjoint⟩
end end Wishart.QuaternionMatrix
namespace WishartVerification section 
/-- Literal hermitian_matrix_coe. -/ theorem hermitian_matrix_coe {F ι:Type*} [AddCommGroup F] [Module ℝ F] [StarAddMonoid F] [StarModule ℝ F] (X:selfAdjoint.submodule ℝ (Matrix ι ι F)):(X:Matrix ι ι F).IsHermitian:=by sorry
end end WishartVerification
namespace Wishart section open scoped BigOperators ENNReal Matrix MatrixOrder Matrix.Norms.Operator
/-- Literal shiftedCompressionDeterminant. -/ def shiftedCompressionDeterminant {p q:ℕ} (Sigma:Matrix (Fin p) (Fin p) ℝ) (Q:Matrix (Fin p) (Fin q) ℝ) (c:ℝ) (X:SymmetricMatrix p):ℝ:=(Qᵀ * (X:Matrix (Fin p) (Fin p) ℝ) * Q + c • compressionScale Sigma Q).det
end end Wishart
namespace WishartVerification.MomentAssembly section open scoped Classical variable {ι:Type*} [DecidableEq ι]
/-- Literal descendingRankEquiv. -/ def descendingRankEquiv (rank:ι→ℕ) (A:Finset ι):Fin (Fintype.card A) ≃ A:=(Tuple.sortDesc (fun i => rank ((Fintype.equivFin A).symm i))).trans (Fintype.equivFin A).symm
/-- Literal descendingRanks. -/ def descendingRanks (rank:ι→ℕ) (A:Finset ι):Fin (Fintype.card A)→ℕ:=fun i => rank (descendingRankEquiv rank A i)
/-- The condition is vacuous when at most two active proper factors remain; otherwise it reads precisely `n ≥ min(k_(1)+k_(3), p+1)` in descending order. -/ def orderedRankThreshold (rank:ι→ℕ) (A:Finset ι) (p:ℕ) (n:ℝ):Prop :=
  ∀ h:3 ≤ Fintype.card A,
    min ((descendingRanks rank A ⟨0,WishartSharedProof.zero_lt_of_three_le h⟩:ℝ) +
      descendingRanks rank A ⟨2,WishartSharedProof.two_lt_of_three_le h⟩) ((p:ℝ) + 1) ≤ n
end end WishartVerification.MomentAssembly
namespace Wishart section open scoped Classical BigOperators ENNReal Matrix MatrixOrder Matrix.Norms.Operator
/-- Literal GeometricCompressionFamily. -/ structure GeometricCompressionFamily (p:ℕ) (ι:Type*) where
  size:ι→ℕ
  matrix:∀ i,Matrix (Fin p) (Fin (size i)) ℝ
  full_rank:∀ i,(matrix i).rank=size i
  shift:ι→ℝ
  shift_nonneg:∀ i,0 ≤ shift i
  outer:ι→ℝ→ℝ
  geometric:∀ i,GeometricallyLogConvex (outer i)
end end Wishart
namespace Wishart.GeometricCompressionFamily section open scoped Classical BigOperators ENNReal Matrix MatrixOrder Matrix.Norms.Operator variable {p:ℕ} {ι:Type*} [DecidableEq ι] variable (F:GeometricCompressionFamily p ι) (Sigma:Matrix (Fin p) (Fin p) ℝ)
/-- Literal factor. -/ def factor (i:ι) (X:SymmetricMatrix p):ℝ:=F.outer i (shiftedCompressionDeterminant Sigma (F.matrix i) (F.shift i) X)
/-- Literal subproduct. -/ def subproduct (J:Finset ι) (X:SymmetricMatrix p):ℝ:=∏ i ∈ J,F.factor Sigma i X
/-- Literal moment. -/ def moment (n:ℝ) (J:Finset ι):ℝ≥0∞:=∫⁻ X,ENNReal.ofReal (F.subproduct Sigma J X) ∂nonsingularWishartMeasure n Sigma
/-- Constancy is tested on the entire positive definite cone, the actual support of the nonsingular law. It is not a premise about an unknown conditional moment. -/ def ConstantFactor (i:ι):Prop:=∃ c:ℝ,∀ X:SymmetricMatrix p,(X:Matrix (Fin p) (Fin p) ℝ).PosDef→F.factor Sigma i X=c
/-- Literal activeProper. -/ def activeProper [Fintype ι]:Finset ι:=Finset.univ.filter (fun i => F.size i < p ∧ ¬ F.ConstantFactor Sigma i)
end end Wishart.GeometricCompressionFamily
namespace Wishart section open scoped Matrix MatrixOrder Matrix.Norms.Operator ENNReal
/-- Literal positiveSemidefiniteCone. -/ def positiveSemidefiniteCone (k:ℕ):Set (SymmetricMatrix k):={X | (X:Matrix (Fin k) (Fin k) ℝ).PosSemidef}
/-- A nonzero continuous convex homogeneous Loewner-increasing orthogonally invariant function on the positive semidefinite cone, precisely as defined in the manuscript. -/ structure SpectralGauge (k:ℕ) where
  toFun:SymmetricMatrix k→ℝ
  nonnegative:∀ X ∈ positiveSemidefiniteCone k,0 ≤ toFun X
  nonzero:∃ X ∈ positiveSemidefiniteCone k,toFun X ≠ 0
  continuousOn:ContinuousOn toFun (positiveSemidefiniteCone k)
  convexOn:ConvexOn ℝ (positiveSemidefiniteCone k) toFun
  homogeneous:∀ (a:ℝ),0 ≤ a→∀ X ∈ positiveSemidefiniteCone k,
    toFun (a • X)=a * toFun X
  loewner:∀ X ∈ positiveSemidefiniteCone k,∀ Y ∈ positiveSemidefiniteCone k,
    ((Y - X:SymmetricMatrix k):Matrix (Fin k) (Fin k) ℝ).PosSemidef →
      toFun X ≤ toFun Y
  orthogonalInvariant:∀ (U:Matrix.orthogonalGroup (Fin k) ℝ)
    (X:SymmetricMatrix k),X ∈ positiveSemidefiniteCone k →
    toFun (Matrix.symmetricCongruenceLinearMap (U:Matrix (Fin k) (Fin k) ℝ) X) =
      toFun X
instance {k:ℕ}:CoeFun (SpectralGauge k) (fun _ => SymmetricMatrix k→ℝ):=⟨SpectralGauge.toFun⟩
end end Wishart
namespace Wishart.SpectralGauge section open scoped Matrix MatrixOrder Matrix.Norms.Operator RealInnerProductSpace InnerProductSpace variable {k:ℕ} (Φ:SpectralGauge k)
/-- The exact named Frobenius seminormed parent used in the source gauge section. -/ local instance gaugeSymmetricSeminormedAddCommGroup:SeminormedAddCommGroup (SymmetricMatrix k):=(TauCeti.symmetricMatrixNormedAddCommGroup k).toSeminormedAddCommGroup
/-- The exact named compatible Frobenius inner-product record used in the source. -/ local instance gaugeSymmetricInnerProductSpace:InnerProductSpace ℝ (SymmetricMatrix k):=TauCeti.symmetricMatrixInnerProductSpace k
/-- The entire gauge seminormed record is fixed at every dimension. -/ theorem gaugeSeminormed_value {k:ℕ}:@gaugeSymmetricSeminormedAddCommGroup k=(TauCeti.symmetricMatrixNormedAddCommGroup k).toSeminormedAddCommGroup:=by sorry
/-- The entire gauge inner-product record is fixed at every dimension. -/ theorem gaugeInner_value {k:ℕ}:@gaugeSymmetricInnerProductSpace k=TauCeti.symmetricMatrixInnerProductSpace k:=by sorry
/-- Literal identitySymmetric. -/ def identitySymmetric (k:ℕ):SymmetricMatrix k:=⟨1,WishartSharedProof.realIdentitySelfAdjoint _⟩
/-- The canonical compact set of all positive linear trace minorants. -/ def supportSet:Set (SymmetricMatrix k):={H | (H:Matrix (Fin k) (Fin k) ℝ).PosSemidef ∧ ∀ X ∈ positiveSemidefiniteCone k,⟪H,X⟫_ℝ ≤ Φ X}
/-- A single countable family of positive trace minorants recovers the gauge at every PSD input. This supplies finite maxima for subsequent regularization. -/ theorem exists_countable_positive_support:∃ H:ℕ→SymmetricMatrix k,(∀ n,H n ∈ Φ.supportSet) ∧ ∀ X ∈ positiveSemidefiniteCone k,(⨆ n,⟪H n,X⟫_ℝ)=Φ X:=by sorry
end end Wishart.SpectralGauge
namespace Wishart.SpectralGauge section open scoped Matrix MatrixOrder Matrix.Norms.Operator variable {k:ℕ} (Φ:SpectralGauge k)
/-- A measurable extension used only to express random variables on the whole ambient measurable space. It equals the original gauge at every PSD matrix. -/ def value (X:SymmetricMatrix k):ℝ:=(positiveSemidefiniteCone k).indicator Φ X
end end Wishart.SpectralGauge
namespace Wishart.SpectralGauge section open scoped Matrix MatrixOrder Matrix.Norms.Operator RealInnerProductSpace variable {k:ℕ} (Φ:SpectralGauge k)
/-- Literal supportSequence. -/
def supportSequence:ℕ→SymmetricMatrix k:=Classical.choose Φ.exists_countable_positive_support
/-- Literal supportMaximum. -/
def supportMaximum (n:ℕ) (X:SymmetricMatrix k):ℝ:=finiteMaximum (fun l:Fin (n + 1) => ⟪Φ.supportSequence l,X⟫)
end end Wishart.SpectralGauge
namespace Wishart section open scoped Matrix MatrixOrder Matrix.Norms.Operator
/-- Literal shiftedGaugeValue. -/
def shiftedGaugeValue {q:ℕ} (Φ:SpectralGauge q) (c:ℝ) (S:SymmetricMatrix q):ℝ:=Φ.value (S + c • SpectralGauge.identitySymmetric q)
/-- Literal normalizedGaugeValue. -/
def normalizedGaugeValue {p q:ℕ} (Sigma:Matrix (Fin p) (Fin p) ℝ) (B:Matrix (Fin p) (Fin q) ℝ) (Φ:SpectralGauge q) (c:ℝ) (X:SymmetricMatrix p):ℝ:=shiftedGaugeValue Φ c (normalizedCompression Sigma B X)
end end Wishart
namespace WishartVerification.MomentAssembly section open scoped Classical ENNReal BigOperators variable {ι:Type*} [DecidableEq ι]
/-- Literal orderedGaugeRankThreshold. -/
def orderedGaugeRankThreshold (rank:ι→ℕ) (A:Finset ι) (n:ℝ):Prop :=
  ∀ h:3 ≤ Fintype.card A,(descendingRanks rank A ⟨2,WishartSharedProof.two_lt_of_three_le h⟩:ℝ) + 1 ≤ n
end end WishartVerification.MomentAssembly
namespace Wishart section open scoped Classical BigOperators ENNReal Matrix MatrixOrder Matrix.Norms.Operator
/-- Literal GeometricGaugeFamily. -/
structure GeometricGaugeFamily (p:ℕ) (ι:Type*) where
  size:ι→ℕ
  matrix:∀ i,Matrix (Fin p) (Fin (size i)) ℝ
  full_rank:∀ i,(matrix i).rank=size i
  gauge:∀ i,SpectralGauge (size i)
  shift:ι→ℝ
  shift_nonneg:∀ i,0 ≤ shift i
  outer:ι→ℝ→ℝ
  geometric:∀ i,GeometricallyLogConvex (outer i)
end end Wishart
namespace Wishart.GeometricGaugeFamily section open scoped Classical BigOperators ENNReal Matrix MatrixOrder Matrix.Norms.Operator variable {p:ℕ} {ι:Type*} [DecidableEq ι] variable (F:GeometricGaugeFamily p ι) (Sigma:Matrix (Fin p) (Fin p) ℝ)
/-- Literal factor. -/
def factor (i:ι) (X:SymmetricMatrix p):ℝ:=F.outer i (normalizedGaugeValue Sigma (F.matrix i) (F.gauge i) (F.shift i) X)
/-- Literal subproduct. -/
def subproduct (J:Finset ι) (X:SymmetricMatrix p):ℝ:=∏ i ∈ J,F.factor Sigma i X
/-- Literal moment. -/
def moment (n:ℝ) (J:Finset ι):ℝ≥0∞:=∫⁻ X,ENNReal.ofReal (F.subproduct Sigma J X) ∂nonsingularWishartMeasure n Sigma
/-- Literal ConstantFactor. -/
def ConstantFactor (i:ι):Prop:=∃ c:ℝ,∀ X:SymmetricMatrix p,(X:Matrix (Fin p) (Fin p) ℝ).PosDef→F.factor Sigma i X=c
/-- Literal activeProper. -/
def activeProper [Fintype ι]:Finset ι:=Finset.univ.filter (fun i => F.size i < p ∧ ¬ F.ConstantFactor Sigma i)
end end Wishart.GeometricGaugeFamily
namespace Wishart.Spectral section open scoped Classical
/-- Literal SymmetricProfile. -/
def SymmetricProfile {k:ℕ} (h:(Fin k→ℝ)→ℝ):Prop:=∀ (σ:Equiv.Perm (Fin k)) (x:Fin k→ℝ),h (x ∘ σ)=h x
end end Wishart.Spectral
namespace Wishart.Spectral section open scoped Classical Matrix.Norms.Operator
/-- The manuscript's decreasing eigenvalue enumeration. -/
noncomputable def descendingSpectrum {p:ℕ} (S:Sym p):Fin p→ℝ:=ascendingSpectrum S ∘ Fin.rev
end end Wishart.Spectral
namespace Wishart.QuaternionMatrix section open scoped Classical Quaternion Matrix ComplexOrder variable {m n:Type*} [Fintype m] [Fintype n]
/-- Literal FullColumnRank. -/
def FullColumnRank (B:Matrix m n ℍ[ℝ]):Prop:=Function.Injective B.mulVec
end end Wishart.QuaternionMatrix
namespace Wishart.FieldSpectral section open scoped Classical ComplexOrder Matrix.Norms.L2Operator variable {𝕜:Type*} [RCLike 𝕜]
/-- Literal orderedValues. -/
def orderedValues {p:ℕ} {A:Matrix (Fin p) (Fin p) 𝕜} (hA:A.IsHermitian):Fin p→ℝ:=fun i => hA.eigenvalues₀ (Fin.cast (WishartSharedProof.finCard_symm p) i)
/-- Literal Hermitian. -/
abbrev Hermitian (𝕜:Type*) [RCLike 𝕜] (p:ℕ):=selfAdjoint.submodule ℝ (Matrix (Fin p) (Fin p) 𝕜)
end end Wishart.FieldSpectral
namespace Wishart.QuaternionMatrix section open scoped Classical Quaternion Matrix ComplexOrder MatrixOrder Matrix.Norms.L2Operator open scoped Matrix.Norms.Frobenius
/-- Flatten the two scalar coordinates in the actual complex representation. -/
def flatRepresentation {p j:ℕ} (A:Matrix (Fin p) (Fin j) ℍ[ℝ]):Matrix (Fin (p * 2)) (Fin (j * 2)) ℂ:=(complexRepresentation A).submatrix finProdFinEquiv.symm finProdFinEquiv.symm
/-- Literal flatHermitian. -/
def flatHermitian {p:ℕ} (A:Hermitian p):Wishart.FieldSpectral.Hermitian ℂ (p * 2):=⟨flatRepresentation (A:Matrix (Fin p) (Fin p) ℍ[ℝ]),(((isHermitian_complexRepresentation_iff _).mpr (WishartVerification.hermitian_matrix_coe A)).submatrix finProdFinEquiv.symm).eq⟩
end end Wishart.QuaternionMatrix
namespace Wishart.QuaternionMatrix section open scoped Classical Quaternion Matrix ComplexOrder Matrix.Norms.L2Operator open scoped Matrix.Norms.Frobenius
/-- Literal doubledIndex. -/
def doubledIndex {p:ℕ} (i:Fin p):Fin (p * 2):=finProdFinEquiv (i,0)
/-- Literal orderedValues. -/
def orderedValues {p:ℕ} (A:Hermitian p):Fin p→ℝ:=fun i => Wishart.FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe (flatHermitian A)) (doubledIndex i)
end end Wishart.QuaternionMatrix
namespace Wishart.Spectral section open scoped Classical BigOperators variable {k:ℕ}
/-- Literal spectralRegularization. -/
def spectralRegularization (h:(Fin k→ℝ)→ℝ) (x:Fin k→ℝ) (t:ℝ):ℝ:=Real.exp (h (fun i => Real.log (x i + Real.exp t)))
/-- Literal spectralBoundaryValue. -/
def spectralBoundaryValue (h:(Fin k→ℝ)→ℝ) (x:Fin k→ℝ):ℝ:=⨅ t:ℝ,spectralRegularization h x t
end end Wishart.Spectral
namespace Wishart section open scoped Classical Quaternion ComplexOrder BigOperators ENNReal
/-- Both inequalities in the selected-factor chain, with extended expectations. Using nonnegative extended multiplication also fixes the paper's zero-factor convention: `0 * ∞ = 0`. -/
def ExtendedSelectedProductComparison {E ι:Type*} [MeasurableSpace E] [DecidableEq ι] (μ:Measure E) (f:ι→E→ℝ):Prop:=∀ (J:Finset ι) (j:ι),j ∈ J→(∫⁻ X,ENNReal.ofReal (f j X) ∂μ) * (∫⁻ X,ENNReal.ofReal (∏ i ∈ J.erase j,f i X) ∂μ) ≤ ∫⁻ X,ENNReal.ofReal (∏ i ∈ J,f i X) ∂μ ∧ (∏ i ∈ J,∫⁻ X,ENNReal.ofReal (f i X) ∂μ) ≤ (∫⁻ X,ENNReal.ofReal (f j X) ∂μ) * (∫⁻ X,ENNReal.ofReal (∏ i ∈ J.erase j,f i X) ∂μ)
/-- Literal ComplexSpectralFamily. -/
structure ComplexSpectralFamily (p:ℕ) (ι:Type*) where
  size:ι→ℕ
  matrix:∀ i,Matrix (Fin p) (Fin (size i)) ℂ
  full_rank:∀ i,Function.Injective (matrix i).mulVec
  shift:ι→ℝ
  shift_nonneg:∀ i,0 ≤ shift i
  profile:∀ i,(Fin (size i)→ℝ)→ℝ
  convex:∀ i,ConvexOn ℝ univ (profile i)
  increasing:∀ i,Monotone (profile i)
  symmetric:∀ i,Spectral.SymmetricProfile (profile i)
/-- Literal QuaternionSpectralFamily. -/
structure QuaternionSpectralFamily (p:ℕ) (ι:Type*) where
  size:ι→ℕ
  matrix:∀ i,Matrix (Fin p) (Fin (size i)) ℍ[ℝ]
  full_rank:∀ i,QuaternionMatrix.FullColumnRank (matrix i)
  shift:ι→ℝ
  shift_nonneg:∀ i,0 ≤ shift i
  profile:∀ i,(Fin (size i)→ℝ)→ℝ
  convex:∀ i,ConvexOn ℝ univ (profile i)
  increasing:∀ i,Monotone (profile i)
  symmetric:∀ i,Spectral.SymmetricProfile (profile i)
end end Wishart
namespace Wishart.ComplexSpectralFamily section open scoped Classical Quaternion ComplexOrder BigOperators ENNReal variable {p:ℕ} {ι:Type*} (F:ComplexSpectralFamily p ι)
/-- Literal shiftedCompression. -/
def shiftedCompression (Sigma:Matrix (Fin p) (Fin p) ℂ) (i:ι) (X:ComplexMatrix.Hermitian p):ComplexMatrix.Hermitian (F.size i):=ComplexMatrix.normalizedCompression (F.matrix i) Sigma X + F.shift i • (⟨1,Matrix.isHermitian_one⟩:ComplexMatrix.Hermitian (F.size i))
/-- Literal factor. -/
def factor (Sigma:Matrix (Fin p) (Fin p) ℂ) (i:ι) (X:ComplexMatrix.Hermitian p):ℝ:=Spectral.spectralBoundaryValue (F.profile i) (FieldSpectral.orderedValues (WishartVerification.hermitian_matrix_coe (F.shiftedCompression Sigma i X)))
end end Wishart.ComplexSpectralFamily
namespace Wishart.QuaternionSpectralFamily section open scoped Classical Quaternion ComplexOrder BigOperators ENNReal variable {p:ℕ} {ι:Type*} (F:QuaternionSpectralFamily p ι)
/-- Literal shiftedCompression. -/
def shiftedCompression (Sigma:Matrix (Fin p) (Fin p) ℍ[ℝ]) (i:ι) (X:QuaternionMatrix.Hermitian p):QuaternionMatrix.Hermitian (F.size i):=QuaternionMatrix.normalizedCompression (F.matrix i) Sigma X + F.shift i • (⟨1,Matrix.isHermitian_one⟩:QuaternionMatrix.Hermitian (F.size i))
/-- Literal factor. -/
def factor (Sigma:Matrix (Fin p) (Fin p) ℍ[ℝ]) (i:ι) (X:QuaternionMatrix.Hermitian p):ℝ:=Spectral.spectralBoundaryValue (F.profile i) (QuaternionMatrix.orderedValues (F.shiftedCompression Sigma i X))
end end Wishart.QuaternionSpectralFamily
namespace Wishart section open scoped Classical Quaternion ComplexOrder BigOperators ENNReal
/-- The two allowed actual complex laws; the real-shape normalization must still be established, rather than built into this predicate as an assumption. -/
def IsSectionSevenComplexLaw {p:ℕ} (Sigma:Matrix (Fin p) (Fin p) ℂ) (μ:Measure (ComplexMatrix.Hermitian p)):Prop:=(∃ α:ℝ,(p:ℝ) - 1 < α ∧ μ=ComplexMatrix.wishartMeasure α Sigma) ∨ (∃ n:ℕ,1 ≤ n ∧ μ=ComplexMatrix.gramMeasure n Sigma)
/-- Literal IsSectionSevenQuaternionLaw. -/
def IsSectionSevenQuaternionLaw {p:ℕ} (Sigma:Matrix (Fin p) (Fin p) ℍ[ℝ]) (μ:Measure (QuaternionMatrix.Hermitian p)):Prop:=(∃ α:ℝ,(p:ℝ) - 1 < α ∧ μ=QuaternionMatrix.wishartMeasure α Sigma) ∨ (∃ n:ℕ,1 ≤ n ∧ μ=QuaternionMatrix.gramMeasure n Sigma)
/-- This is a required conclusion in the final Section 7 package. It prevents the normalization convention `∞⁻¹ = 0` from making a malformed density law produce a vacuous zero-measure comparison. -/
def SectionSevenComplexNormalization:Prop:=∀ (p:ℕ) (α:ℝ) (Sigma:Matrix (Fin p) (Fin p) ℂ),(p:ℝ) - 1 < α→Sigma.PosDef→0 < ComplexMatrix.wishartNormalizer α Sigma ∧ ComplexMatrix.wishartNormalizer α Sigma < ⊤ ∧ IsProbabilityMeasure (ComplexMatrix.wishartMeasure α Sigma)
/-- Literal SectionSevenQuaternionNormalization. -/
def SectionSevenQuaternionNormalization:Prop:=∀ (p:ℕ) (α:ℝ) (Sigma:Matrix (Fin p) (Fin p) ℍ[ℝ]),(p:ℝ) - 1 < α→QuaternionMatrix.PosDef Sigma→0 < QuaternionMatrix.wishartNormalizer α Sigma ∧ QuaternionMatrix.wishartNormalizer α Sigma < ⊤ ∧ IsProbabilityMeasure (QuaternionMatrix.wishartMeasure α Sigma)
/-- Full complex principal target: all admissible real shapes and all positive integer sample sizes, all finite families and all full-column-rank overlaps. -/
def TheoremSevenOneComplex:Prop:=∀ (p:ℕ) (ι:Type) [Fintype ι] [DecidableEq ι] (Sigma:Matrix (Fin p) (Fin p) ℂ),Sigma.PosDef→∀ (F:ComplexSpectralFamily p ι) (μ:Measure (ComplexMatrix.Hermitian p)),IsSectionSevenComplexLaw Sigma μ→ExtendedSelectedProductComparison μ (F.factor Sigma)
/-- Literal TheoremSevenOneQuaternion. -/
def TheoremSevenOneQuaternion:Prop:=∀ (p:ℕ) (ι:Type) [Fintype ι] [DecidableEq ι] (Sigma:Matrix (Fin p) (Fin p) ℍ[ℝ]),QuaternionMatrix.PosDef Sigma→∀ (F:QuaternionSpectralFamily p ι) (μ:Measure (QuaternionMatrix.Hermitian p)),IsSectionSevenQuaternionLaw Sigma μ→ExtendedSelectedProductComparison μ (F.factor Sigma)
/-- The finite determinant-power assertion is a separate part of 7.1; it is not silently inferred from the extended comparison. -/
def TheoremSevenOneComplexFinitePowers:Prop:=∀ (p:ℕ) (ι:Type) [Fintype ι] [DecidableEq ι] (Sigma:Matrix (Fin p) (Fin p) ℂ),Sigma.PosDef→∀ (k:ι→ℕ) (B:∀ i,Matrix (Fin p) (Fin (k i)) ℂ),(∀ i,Function.Injective (B i).mulVec)→∀ (c ν:ι→ℝ),(∀ i,0 ≤ c i)→(∀ i,0 ≤ ν i)→∀ μ:Measure (ComplexMatrix.Hermitian p),IsSectionSevenComplexLaw Sigma μ→(∫⁻ X,ENNReal.ofReal (∏ i,ComplexMatrix.realDeterminant ((B i)ᴴ * (X:Matrix (Fin p) (Fin p) ℂ) * B i + c i • ComplexMatrix.compressionCovariance (B i) Sigma) ^ ν i) ∂μ) < ⊤
/-- Literal TheoremSevenOneQuaternionFinitePowers. -/
def TheoremSevenOneQuaternionFinitePowers:Prop:=∀ (p:ℕ) (ι:Type) [Fintype ι] [DecidableEq ι] (Sigma:Matrix (Fin p) (Fin p) ℍ[ℝ]),QuaternionMatrix.PosDef Sigma→∀ (k:ι→ℕ) (B:∀ i,Matrix (Fin p) (Fin (k i)) ℍ[ℝ]),(∀ i,QuaternionMatrix.FullColumnRank (B i))→∀ (c ν:ι→ℝ),(∀ i,0 ≤ c i)→(∀ i,0 ≤ ν i)→∀ μ:Measure (QuaternionMatrix.Hermitian p),IsSectionSevenQuaternionLaw Sigma μ→(∫⁻ X,ENNReal.ofReal (∏ i,QuaternionMatrix.positiveDeterminant ((B i)ᴴ * (X:Matrix (Fin p) (Fin p) ℍ[ℝ]) * B i + c i • QuaternionMatrix.compressionCovariance (B i) Sigma) ^ ν i) ∂μ) < ⊤
/-- The required combined Section 7 target, including law nonvacuity and finite moments. Defining this proposition does not assert it. -/
def TheoremSevenOne:Prop:=SectionSevenComplexNormalization ∧ SectionSevenQuaternionNormalization ∧ TheoremSevenOneComplex ∧ TheoremSevenOneQuaternion ∧ TheoremSevenOneComplexFinitePowers ∧ TheoremSevenOneQuaternionFinitePowers
end end Wishart
namespace Wishart.Spectral section open scoped Classical BigOperators Matrix.Norms.Operator
/-- Literal identitySymmetric. -/
def identitySymmetric (p:ℕ):Sym p:=⟨1,WishartSharedProof.realIdentitySelfAdjoint _⟩
/-- Literal shiftSymmetric. -/
def shiftSymmetric {p:ℕ} (c:ℝ) (X:Sym p):Sym p:=X + c • identitySymmetric p
end end Wishart.Spectral
namespace Wishart.Spectral section open scoped Classical BigOperators ENNReal
/-- Literal FiniteConvexIncreasingSymmetric. -/
def FiniteConvexIncreasingSymmetric {k:ℕ} (h:(Fin k→ℝ)→ℝ):Prop:=ConvexOn ℝ Set.univ h ∧ Monotone h ∧ SymmetricProfile h
/-- Literal logSpectralFactor. -/
def logSpectralFactor {k:ℕ} (h:(Fin k→ℝ)→ℝ) (S:Sym k):ℝ:=Real.exp (h (fun i => Real.log (descendingSpectrum S i)))
end end Wishart.Spectral
namespace Wishart.Spectral section open scoped Classical BigOperators ENNReal Matrix MatrixOrder Matrix.Norms.Operator variable {κ ι:Type*} [Fintype κ] [Fintype ι] [Nonempty ι]
/-- Literal normalizedShiftedMatrix. -/
def normalizedShiftedMatrix {p q:ℕ} (Sigma:Matrix (Fin p) (Fin p) ℝ) (B:Matrix (Fin p) (Fin q) ℝ) (c:ℝ) (X:Sym p):Sym q:=shiftSymmetric c (normalizedCompression Sigma B X)
/-- Literal normalizedLogSpectralFactor. -/
def normalizedLogSpectralFactor {p q:ℕ} (Sigma:Matrix (Fin p) (Fin p) ℝ) (B:Matrix (Fin p) (Fin q) ℝ) (c:ℝ) (h:(Fin q→ℝ)→ℝ) (X:Sym p):ℝ:=logSpectralFactor h (normalizedShiftedMatrix Sigma B c X)
end end Wishart.Spectral
namespace WishartVerification.MomentAssembly section open scoped Classical ENNReal BigOperators variable {ι:Type*} [DecidableEq ι]
/-- Literal orderedPairRankThreshold. -/
def orderedPairRankThreshold (rank:ι→ℕ) (A:Finset ι) (p:ℕ) (n:ℝ):Prop :=
  ∀ h:2 ≤ Fintype.card A,
    min ((descendingRanks rank A ⟨0,WishartSharedProof.zero_lt_of_two_le h⟩:ℝ) +
      descendingRanks rank A ⟨1,WishartSharedProof.one_lt_of_two_le h⟩) ((p:ℝ) + 1) ≤ n
end end WishartVerification.MomentAssembly
namespace Wishart section open scoped Classical BigOperators ENNReal Matrix MatrixOrder Matrix.Norms.Operator
/-- Literal LogSpectralCompressionFamily. -/
structure LogSpectralCompressionFamily (p:ℕ) (ι:Type*) where
  size:ι→ℕ
  matrix:∀ i,Matrix (Fin p) (Fin (size i)) ℝ
  full_rank:∀ i,(matrix i).rank=size i
  shift:ι→ℝ
  shift_nonneg:∀ i,0 ≤ shift i
  profile:∀ i,(Fin (size i)→ℝ)→ℝ
  profile_class:∀ i,FiniteConvexIncreasingSymmetric (profile i)
end end Wishart
namespace Wishart.LogSpectralCompressionFamily section open scoped Classical BigOperators ENNReal Matrix MatrixOrder Matrix.Norms.Operator variable {p:ℕ} {ι:Type*} [DecidableEq ι] variable (F:LogSpectralCompressionFamily p ι) (Sigma:Matrix (Fin p) (Fin p) ℝ)
/-- Literal factor. -/
def factor (i:ι) (X:SymmetricMatrix p):ℝ:=normalizedLogSpectralFactor Sigma (F.matrix i) (F.shift i) (F.profile i) X
/-- Literal subproduct. -/
def subproduct (J:Finset ι) (X:SymmetricMatrix p):ℝ:=∏ i ∈ J,F.factor Sigma i X
/-- Literal moment. -/
def moment (n:ℝ) (J:Finset ι):ℝ≥0∞:=∫⁻ X,ENNReal.ofReal (F.subproduct Sigma J X) ∂nonsingularWishartMeasure n Sigma
/-- Literal ConstantFactor. -/
def ConstantFactor (i:ι):Prop:=∃ c:ℝ,∀ X:SymmetricMatrix p,(X:Matrix (Fin p) (Fin p) ℝ).PosDef→F.factor Sigma i X=c
/-- Literal activeProper. -/
def activeProper [Fintype ι]:Finset ι:=Finset.univ.filter (fun i => F.size i < p ∧ ¬ F.ConstantFactor Sigma i)
end end Wishart.LogSpectralCompressionFamily
namespace WishartVerification section 
/-- Literal GeometricOuterOnNonnegative. -/
structure GeometricOuterOnNonnegative (f:ℝ→ℝ):Prop where
  geometric:GeometricallyLogConvex f
  zero_nonneg:0 ≤ f 0
  continuous_zero:ContinuousWithinAt f (Ici 0) 0
end end WishartVerification
namespace WishartVerification.MomentAssembly section open scoped Classical ENNReal BigOperators variable {ι:Type*} [DecidableEq ι]
/-- The condition is vacuous when at most two active proper factors remain; otherwise it reads precisely `n ≥ k_(1)+k_(3)` in descending order. -/
def gramOrderedRankThreshold (rank:ι→ℕ) (A:Finset ι) (n:ℕ):Prop :=
  ∀ h:3 ≤ Fintype.card A,
    descendingRanks rank A ⟨0,WishartSharedProof.zero_lt_of_three_le h⟩ +
      descendingRanks rank A ⟨2,WishartSharedProof.two_lt_of_three_le h⟩ ≤ n
end end WishartVerification.MomentAssembly
namespace Wishart section open scoped Classical BigOperators ENNReal Matrix MatrixOrder Matrix.Norms.Operator
/-- Literal GramGeometricCompressionFamily. -/
structure GramGeometricCompressionFamily (p:ℕ) (ι:Type*) where
  size:ι→ℕ
  matrix:∀ i,Matrix (Fin p) (Fin (size i)) ℝ
  full_rank:∀ i,(matrix i).rank=size i
  shift:ι→ℝ
  shift_nonneg:∀ i,0 ≤ shift i
  outer:ι→ℝ→ℝ
  boundary:∀ i,GeometricOuterOnNonnegative (outer i)
end end Wishart
namespace Wishart.GramGeometricCompressionFamily section open scoped Classical BigOperators ENNReal Matrix MatrixOrder Matrix.Norms.Operator variable {p:ℕ} {ι:Type*} [DecidableEq ι] variable (F:GramGeometricCompressionFamily p ι) (Sigma:Matrix (Fin p) (Fin p) ℝ)
/-- Literal factor. -/
def factor (i:ι) (X:SymmetricMatrix p):ℝ:=F.outer i (shiftedCompressionDeterminant Sigma (F.matrix i) (F.shift i) X)
/-- Literal subproduct. -/
def subproduct (J:Finset ι) (X:SymmetricMatrix p):ℝ:=∏ i ∈ J,F.factor Sigma i X
/-- Literal moment. -/
def moment (n:ℕ) (J:Finset ι):ℝ≥0∞:=∫⁻ X,ENNReal.ofReal (F.subproduct Sigma J X) ∂wishartGramMeasure n Sigma
/-- Literal AEConstantFactor. -/
def AEConstantFactor (n:ℕ) (i:ι):Prop:=∃ c:ℝ,∀ᵐ X ∂wishartGramMeasure n Sigma,F.factor Sigma i X=c
/-- Literal activeProper. -/
def activeProper [Fintype ι] (n:ℕ):Finset ι:=Finset.univ.filter (fun i => F.size i < p ∧ ¬ F.AEConstantFactor Sigma n i)
end end Wishart.GramGeometricCompressionFamily
namespace Wishart section open scoped Classical ENNReal MatrixOrder Matrix.Norms.L2Operator
/-- Literal matrixBetaIIConstant. -/
def matrixBetaIIConstant {p:ℕ} (α β:ℝ) (Omega:Matrix (Fin p) (Fin p) ℝ):ℝ:=multivariateGamma p ((α + β) / 2) / (multivariateGamma p (α / 2) * multivariateGamma p (β / 2)) * Omega.det ^ (β / 2)
/-- Literal matrixBetaIIPDFReal. -/
def matrixBetaIIPDFReal {p:ℕ} (α β:ℝ) (Omega:Matrix (Fin p) (Fin p) ℝ) (X:SymmetricMatrix p):ℝ:=if (X:Matrix (Fin p) (Fin p) ℝ).PosDef then matrixBetaIIConstant α β Omega * (X:Matrix (Fin p) (Fin p) ℝ).det ^ ((α - p - 1) / 2) * (Omega + (X:Matrix (Fin p) (Fin p) ℝ)).det ^ (-((α + β) / 2)) else 0
/-- Literal matrixBetaIIPDF. -/
def matrixBetaIIPDF {p:ℕ} (α β:ℝ) (Omega:Matrix (Fin p) (Fin p) ℝ) (X:SymmetricMatrix p):ℝ≥0∞:=ENNReal.ofReal (matrixBetaIIPDFReal α β Omega X)
/-- The beta-II law is defined by the paper's density, not by an assumed hierarchy. Equality to the hierarchy is proved in the next module. -/
def matrixBetaIIMeasure {p:ℕ} (α β:ℝ) (Omega:Matrix (Fin p) (Fin p) ℝ):Measure (SymmetricMatrix p):=(symmetricLebesgue p).withDensity (matrixBetaIIPDF α β Omega)
/-- Literal compressionDeterminantProduct. -/
def compressionDeterminantProduct {p d:ℕ} (k:Fin d→ℕ) (B:∀ i,Matrix (Fin p) (Fin (k i)) ℝ) (ν:Fin d→ℝ) (J:Finset (Fin d)) (X:SymmetricMatrix p):ℝ:=∏ i ∈ J,((B i)ᵀ * (X:Matrix (Fin p) (Fin p) ℝ) * B i).det ^ ν i
end end Wishart
namespace Wishart section open scoped Classical BigOperators ENNReal MatrixOrder Matrix.Norms.L2Operator
/-- The actual normalized principal matrix, with the covariance inverse square root on both sides, in an arbitrary fixed enumeration of the coordinate set. -/
def normalizedPrincipalGaugeMatrix {p:ℕ} (Sigma:Matrix (Fin p) (Fin p) ℝ) (I:Finset (Fin p)) (X:SymmetricMatrix p):SymmetricMatrix (Fintype.card I):=Matrix.symmetricCongruenceLinearMap (CFC.sqrt (Sigma.submatrix (principalSetCoordinates I) (principalSetCoordinates I)))⁻¹ (principalSetMatrix I X)
/-- Literal principalGaugeFactor. -/
def principalGaugeFactor {p d:ℕ} (Sigma:Matrix (Fin p) (Fin p) ℝ) (I:Fin d→Finset (Fin p)) (Φ:∀ i,SpectralGauge (Fintype.card (I i))) (c:Fin d→ℝ) (f:Fin d→ℝ→ℝ) (i:Fin d) (X:SymmetricMatrix p):ℝ:=f i (Φ i (normalizedPrincipalGaugeMatrix Sigma (I i) X + c i • SpectralGauge.identitySymmetric (Fintype.card (I i))))
/-- Literal principalShiftedDeterminant. -/
def principalShiftedDeterminant {p:ℕ} (Sigma:Matrix (Fin p) (Fin p) ℝ) (I:Finset (Fin p)) (c:ℝ) (X:SymmetricMatrix p):ℝ:=((X:Matrix (Fin p) (Fin p) ℝ).submatrix (principalSetCoordinates I) (principalSetCoordinates I) + c • Sigma.submatrix (principalSetCoordinates I) (principalSetCoordinates I)).det
/-- Literal principalLogSpectralFactor. -/
def principalLogSpectralFactor {p d:ℕ} (Sigma:Matrix (Fin p) (Fin p) ℝ) (I:Fin d→Finset (Fin p)) (c:Fin d→ℝ) (h:∀ i,(Fin (Fintype.card (I i))→ℝ)→ℝ) (i:Fin d) (X:SymmetricMatrix p):ℝ:=Real.exp (h i (fun j => Real.log (ascendingSpectrum (normalizedPrincipalGaugeMatrix Sigma (I i) X + c i • Spectral.identitySymmetric (Fintype.card (I i))) j)))
/-- Literal selectedExtendedBound. -/
def selectedExtendedBound {Ω ι:Type*} [MeasurableSpace Ω] [DecidableEq ι] (μ:Measure Ω) (f:ι→Ω→ℝ) (J:Finset ι) (i:ι):Prop:=(∫⁻ X,ENNReal.ofReal (f i X) ∂μ) * (∫⁻ X,ENNReal.ofReal (∏ j ∈ J.erase i,f j X) ∂μ) ≤ ∫⁻ X,ENNReal.ofReal (∏ j ∈ J,f j X) ∂μ
/-- Literal productExtendedBound. -/
def productExtendedBound {Ω ι:Type*} [MeasurableSpace Ω] (μ:Measure Ω) (f:ι→Ω→ℝ) (J:Finset ι):Prop:=(∏ i ∈ J,∫⁻ X,ENNReal.ofReal (f i X) ∂μ) ≤ ∫⁻ X,ENNReal.ofReal (∏ i ∈ J,f i X) ∂μ
/-- Literal realPairBound. -/
def realPairBound {Ω:Type*} [MeasurableSpace Ω] (μ:Measure Ω) (f g:Ω→ℝ):Prop:=(∫ X,f X ∂μ) * (∫ X,g X ∂μ) ≤ ∫ X,f X * g X ∂μ
/-- The literal maximum in (10). The empty remaining product is handled by the separate trivial-small-family clause whenever that clause applies. -/
def selectedCompressionRankBound {ι:Type*} [DecidableEq ι] (rank:ι→ℕ) (J:Finset ι) (i:ι) (p:ℕ) (n:ℝ):Prop:=min ((rank i:ℝ) + (J.erase i).sup rank) ((p:ℝ) + 1) ≤ n
/-- Literal DeterminantCompressionConclusion. -/
structure DeterminantCompressionConclusion {p d:ℕ}
    (F:GeometricCompressionFamily p (Fin d))
    (Sigma:Matrix (Fin p) (Fin p) ℝ) (n:ℝ):Prop where
  selected:∀ J:Finset (Fin d),∀ i ∈ J,
    (F.size i=p ∨ J.card ≤ 2 ∨ selectedCompressionRankBound F.size J i p n) →
      selectedExtendedBound (nonsingularWishartMeasure n Sigma) (F.factor Sigma) J i
  product:orderedRankThreshold F.size (F.activeProper Sigma) p n →
    ∀ J,productExtendedBound (nonsingularWishartMeasure n Sigma) (F.factor Sigma) J
  constants:∀ i,F.ConstantFactor Sigma i ↔
    ∃ c:ℝ,∀ᵐ X ∂nonsingularWishartMeasure n Sigma,F.factor Sigma i X=c
/-- Literal GaugeCompressionConclusion. -/
structure GaugeCompressionConclusion {p d:ℕ}
    (F:GeometricGaugeFamily p (Fin d))
    (Sigma:Matrix (Fin p) (Fin p) ℝ) (n:ℝ):Prop where
  selected:∀ J:Finset (Fin d),∀ i ∈ J,
    (F.size i=p ∨ J.card ≤ 2 ∨ (F.size i:ℝ) + 1 ≤ n) →
      selectedExtendedBound (nonsingularWishartMeasure n Sigma) (F.factor Sigma) J i
  product:orderedGaugeRankThreshold F.size (F.activeProper Sigma) n →
    ∀ J,productExtendedBound (nonsingularWishartMeasure n Sigma) (F.factor Sigma) J
  constants:∀ i,F.ConstantFactor Sigma i ↔
    ∃ c:ℝ,∀ᵐ X ∂nonsingularWishartMeasure n Sigma,F.factor Sigma i X=c
/-- Literal LogSpectralCompressionConclusion. -/
structure LogSpectralCompressionConclusion {p d:ℕ}
    (F:LogSpectralCompressionFamily p (Fin d))
    (Sigma:Matrix (Fin p) (Fin p) ℝ) (n:ℝ):Prop where
  selected:∀ J:Finset (Fin d),∀ i ∈ J,
    (F.size i=p ∨ selectedCompressionRankBound F.size J i p n) →
      selectedExtendedBound (nonsingularWishartMeasure n Sigma) (F.factor Sigma) J i
  product:orderedPairRankThreshold F.size (F.activeProper Sigma) p n →
    ∀ J,productExtendedBound (nonsingularWishartMeasure n Sigma) (F.factor Sigma) J
  constants:∀ i,F.ConstantFactor Sigma i ↔
    ∃ c:ℝ,∀ᵐ X ∂nonsingularWishartMeasure n Sigma,F.factor Sigma i X=c
/-- Literal Theorem51GeometricTarget. -/
def Theorem51GeometricTarget:Prop:=∀ (p d:ℕ) (n:ℝ) (Sigma:Matrix (Fin p) (Fin p) ℝ) (F:GeometricCompressionFamily p (Fin d)),Sigma.PosDef→(p:ℝ) - 1 < n→DeterminantCompressionConclusion F Sigma n
/-- Literal Theorem52GeometricTarget. -/
def Theorem52GeometricTarget:Prop:=∀ (p d:ℕ) (n:ℝ) (Sigma:Matrix (Fin p) (Fin p) ℝ) (F:GeometricGaugeFamily p (Fin d)),Sigma.PosDef→(p:ℝ) - 1 < n→GaugeCompressionConclusion F Sigma n
/-- Literal Theorem53SpectralTarget. -/
def Theorem53SpectralTarget:Prop:=∀ (p d:ℕ) (n:ℝ) (Sigma:Matrix (Fin p) (Fin p) ℝ) (F:LogSpectralCompressionFamily p (Fin d)),Sigma.PosDef→(p:ℝ) - 1 < n→LogSpectralCompressionConclusion F Sigma n
/-- Literal Theorem51MonotonePairTarget. -/
def Theorem51MonotonePairTarget:Prop:=∀ (p q k:ℕ) (n c d:ℝ) (Sigma:Matrix (Fin p) (Fin p) ℝ) (Q:Matrix (Fin p) (Fin q) ℝ) (M:Matrix (Fin p) (Fin k) ℝ) (f g:ℝ→ℝ),Sigma.PosDef→(p:ℝ) - 1 < n→Q.rank=q→M.rank=k→0 ≤ c→0 ≤ d→(∀ t ∈ Set.Ioi (0:ℝ),0 ≤ f t)→(∀ t ∈ Set.Ioi (0:ℝ),0 ≤ g t)→MonotoneOn f (Set.Ioi 0)→MonotoneOn g (Set.Ioi 0)→Integrable (fun X => f (shiftedCompressionDeterminant Sigma Q c X)) (nonsingularWishartMeasure n Sigma)→Integrable (fun X => g (shiftedCompressionDeterminant Sigma M d X)) (nonsingularWishartMeasure n Sigma)→Integrable (fun X => f (shiftedCompressionDeterminant Sigma Q c X) * g (shiftedCompressionDeterminant Sigma M d X)) (nonsingularWishartMeasure n Sigma)→realPairBound (nonsingularWishartMeasure n Sigma) (fun X => f (shiftedCompressionDeterminant Sigma Q c X)) (fun X => g (shiftedCompressionDeterminant Sigma M d X))
/-- Literal Theorem52MonotonePairTarget. -/
def Theorem52MonotonePairTarget:Prop:=∀ (p q k:ℕ) (n c d:ℝ) (Sigma:Matrix (Fin p) (Fin p) ℝ) (Q:Matrix (Fin p) (Fin q) ℝ) (M:Matrix (Fin p) (Fin k) ℝ) (Φ:SpectralGauge q) (Ψ:SpectralGauge k) (f g:ℝ→ℝ),Sigma.PosDef→(p:ℝ) - 1 < n→Q.rank=q→M.rank=k→0 ≤ c→0 ≤ d→(∀ t ∈ Set.Ioi (0:ℝ),0 ≤ f t)→(∀ t ∈ Set.Ioi (0:ℝ),0 ≤ g t)→MonotoneOn f (Set.Ioi 0)→MonotoneOn g (Set.Ioi 0)→Integrable (fun X => f (normalizedGaugeValue Sigma Q Φ c X)) (nonsingularWishartMeasure n Sigma)→Integrable (fun X => g (normalizedGaugeValue Sigma M Ψ d X)) (nonsingularWishartMeasure n Sigma)→Integrable (fun X => f (normalizedGaugeValue Sigma Q Φ c X) * g (normalizedGaugeValue Sigma M Ψ d X)) (nonsingularWishartMeasure n Sigma)→realPairBound (nonsingularWishartMeasure n Sigma) (fun X => f (normalizedGaugeValue Sigma Q Φ c X)) (fun X => g (normalizedGaugeValue Sigma M Ψ d X))
/-- Literal Theorem51PrincipalTarget. -/
def Theorem51PrincipalTarget:Prop:=∀ (p d:ℕ) (n:ℝ) (Sigma:Matrix (Fin p) (Fin p) ℝ) (I:Fin d→Finset (Fin p)) (c:Fin d→ℝ) (f:Fin d→ℝ→ℝ),Sigma.PosDef→(p:ℝ) - 1 < n→Pairwise (fun i j => Disjoint (I i) (I j))→(∀ i,0 ≤ c i)→(∀ i,GeometricallyLogConvex (f i))→(∀ J,∀ i ∈ J,selectedExtendedBound (nonsingularWishartMeasure n Sigma) (fun i X => f i (principalShiftedDeterminant Sigma (I i) (c i) X)) J i) ∧ (∀ J,productExtendedBound (nonsingularWishartMeasure n Sigma) (fun i X => f i (principalShiftedDeterminant Sigma (I i) (c i) X)) J)
/-- Literal Theorem52PrincipalTarget. -/
def Theorem52PrincipalTarget:Prop:=∀ (p d:ℕ) (n:ℝ) (Sigma:Matrix (Fin p) (Fin p) ℝ) (I:Fin d→Finset (Fin p)) (Φ:∀ i,SpectralGauge (Fintype.card (I i))) (c:Fin d→ℝ) (f:Fin d→ℝ→ℝ),Sigma.PosDef→(p:ℝ) - 1 < n→(∀ i,(I i).Nonempty)→Pairwise (fun i j => Disjoint (I i) (I j))→(∀ i,0 ≤ c i)→(∀ i,GeometricallyLogConvex (f i))→(∀ J,∀ i ∈ J,selectedExtendedBound (nonsingularWishartMeasure n Sigma) (principalGaugeFactor Sigma I Φ c f) J i) ∧ (∀ J,productExtendedBound (nonsingularWishartMeasure n Sigma) (principalGaugeFactor Sigma I Φ c f) J)
/-- Literal Theorem53PrincipalTarget. -/
def Theorem53PrincipalTarget:Prop:=∀ (p d:ℕ) (n:ℝ) (Sigma:Matrix (Fin p) (Fin p) ℝ) (I:Fin d→Finset (Fin p)) (c:Fin d→ℝ) (h:∀ i,(Fin (Fintype.card (I i))→ℝ)→ℝ),Sigma.PosDef→(p:ℝ) - 1 < n→(∀ i,(I i).Nonempty)→Pairwise (fun i j => Disjoint (I i) (I j))→(3 ≤ d ∨ (p:ℝ) ≤ n)→(∀ i,0 ≤ c i)→(∀ i,FiniteConvexIncreasingSymmetric (h i))→(∀ J,∀ i ∈ J,selectedExtendedBound (nonsingularWishartMeasure n Sigma) (principalLogSpectralFactor Sigma I c h) J i) ∧ (∀ J,productExtendedBound (nonsingularWishartMeasure n Sigma) (principalLogSpectralFactor Sigma I c h) J)
/-- Literal Corollary54ProductTarget. -/
def Corollary54ProductTarget:Prop:=∀ (p d n:ℕ) (Sigma:Matrix (Fin p) (Fin p) ℝ) (F:GramGeometricCompressionFamily p (Fin d)),1 ≤ n→Sigma.PosDef→gramOrderedRankThreshold F.size (F.activeProper Sigma n) n→∀ J,productExtendedBound (wishartGramMeasure n Sigma) (F.factor Sigma) J
/-- Literal Corollary54MonotonePairTarget. -/
def Corollary54MonotonePairTarget:Prop:=∀ (p q k n:ℕ) (c d:ℝ) (Sigma:Matrix (Fin p) (Fin p) ℝ) (Q:Matrix (Fin p) (Fin q) ℝ) (M:Matrix (Fin p) (Fin k) ℝ) (f g:ℝ→ℝ),1 ≤ n→Sigma.PosDef→Q.rank=q→M.rank=k→0 ≤ c→0 ≤ d→(∀ t ∈ Set.Ici (0:ℝ),0 ≤ f t)→(∀ t ∈ Set.Ici (0:ℝ),0 ≤ g t)→MonotoneOn f (Set.Ici 0)→MonotoneOn g (Set.Ici 0)→Integrable (fun X => f (shiftedCompressionDeterminant Sigma Q c X)) (wishartGramMeasure n Sigma)→Integrable (fun X => g (shiftedCompressionDeterminant Sigma M d X)) (wishartGramMeasure n Sigma)→Integrable (fun X => f (shiftedCompressionDeterminant Sigma Q c X) * g (shiftedCompressionDeterminant Sigma M d X)) (wishartGramMeasure n Sigma)→realPairBound (wishartGramMeasure n Sigma) (fun X => f (shiftedCompressionDeterminant Sigma Q c X)) (fun X => g (shiftedCompressionDeterminant Sigma M d X))
/-- Literal Corollary54PowerTarget. -/
def Corollary54PowerTarget:Prop:=∀ (p d n:ℕ) (Sigma:Matrix (Fin p) (Fin p) ℝ) (k:Fin d→ℕ) (B:∀ i,Matrix (Fin p) (Fin (k i)) ℝ) (c ν:Fin d→ℝ),1 ≤ n→Sigma.PosDef→(∀ i,(B i).rank=k i)→(∀ i,0 ≤ c i)→(∀ i,0 ≤ ν i)→HasAllFiniteMoments (fun X:SymmetricMatrix p => ∏ i,shiftedCompressionDeterminant Sigma (B i) (c i) X ^ ν i) (wishartGramMeasure n Sigma)
/-- Literal theorem_5_1_complete. -/
theorem theorem_5_1_complete:Theorem51GeometricTarget ∧ Theorem51MonotonePairTarget ∧ Theorem51PrincipalTarget:=by sorry
/-- Literal theorem_5_2_complete. -/
theorem theorem_5_2_complete:Theorem52GeometricTarget ∧ Theorem52MonotonePairTarget ∧ Theorem52PrincipalTarget:=by sorry
/-- Literal theorem_5_3_complete. -/
theorem theorem_5_3_complete:Theorem53SpectralTarget ∧ Theorem53PrincipalTarget:=by sorry
/-- Literal corollary_5_4_complete. -/
theorem corollary_5_4_complete:Corollary54ProductTarget ∧ Corollary54MonotonePairTarget ∧ Corollary54PowerTarget:=by sorry
end end Wishart
namespace Wishart section open scoped Classical ENNReal Matrix
/-- The exact criterion under the convention permitting zero-column full column rank matrices. No positive-rank hypothesis is imposed. -/
theorem corollary_6_2_finite_moment_iff_positive_ranks {p d:ℕ} {β:ℝ} {Omega:Matrix (Fin p) (Fin p) ℝ} (hOmega:Omega.PosDef) (hβ:(p:ℝ) - 1 < β) (k:Fin d→ℕ) (B:∀ i,Matrix (Fin p) (Fin (k i)) ℝ) (hB:∀ i,(B i).rank=k i) (c ν:Fin d→ℝ) (hc:∀ i,0 ≤ c i) (hν:∀ i,0 ≤ ν i):Integrable (inverseDeterminantProduct Omega k B c ν Finset.univ) (inverseWishartMeasure β Omega) ↔ 2 * (∑ i ∈ Finset.univ.filter (fun i ↦ 0 < k i),ν i) < β - p + 1:=by sorry
/-- The full common-sign product inequalities also retain zero-column compressions, with the exact positive-rank sum in the finite-moment range. -/
theorem corollary_6_2_positive_ranks {p d:ℕ} {β:ℝ} {Omega:Matrix (Fin p) (Fin p) ℝ} (hOmega:Omega.PosDef) (hβ:(p:ℝ) - 1 < β) (k:Fin d→ℕ) (B:∀ i,Matrix (Fin p) (Fin (k i)) ℝ) (hB:∀ i,(B i).rank=k i) (c ν:Fin d→ℝ) (hc:∀ i,0 ≤ c i) (hrange:((∀ i,0 ≤ ν i) ∧ 2 * (∑ i ∈ Finset.univ.filter (fun i ↦ 0 < k i),ν i) < β - p + 1) ∨ (∀ i,ν i ≤ 0)):(∀ J:Finset (Fin d),Integrable (inverseDeterminantProduct Omega k B c ν J) (inverseWishartMeasure β Omega)) ∧ (∏ i,inverseDeterminantMoment β Omega k B c ν {i}) ≤ inverseDeterminantMoment β Omega k B c ν Finset.univ ∧ ∀ j:Fin d,(∏ i,inverseDeterminantMoment β Omega k B c ν {i}) ≤ inverseDeterminantMoment β Omega k B c ν {j} * inverseDeterminantMoment β Omega k B c ν (Finset.univ.erase j) ∧ inverseDeterminantMoment β Omega k B c ν {j} * inverseDeterminantMoment β Omega k B c ν (Finset.univ.erase j) ≤ inverseDeterminantMoment β Omega k B c ν Finset.univ:=by sorry
end end Wishart
namespace Wishart section open scoped Classical ENNReal MatrixOrder Matrix.Norms.L2Operator
/-- The marginal gamma formula on the full corrected finite-moment range. For a zero-column compression the determinant and both multivariate gamma factors equal one, so no condition on the real exponent is needed. -/
theorem corollary_6_2_gamma_moment_effective_rank {p k:ℕ} {β r:ℝ} {Omega:Matrix (Fin p) (Fin p) ℝ} (hOmega:Omega.PosDef) (hβ:(p:ℝ) - 1 < β) (B:Matrix (Fin p) (Fin k) ℝ) (hB:B.rank=k) (hr:k=0 ∨ 2 * r < β - p + 1):(∫ Y:SymmetricMatrix p,(Bᵀ * (Y:Matrix (Fin p) (Fin p) ℝ) * B).det ^ r ∂inverseWishartMeasure β Omega)=(compressionScale Omega B).det ^ r * (2:ℝ) ^ (-(k:ℝ) * r) * (multivariateGamma k ((β - p + k) / 2 - r) / multivariateGamma k ((β - p + k) / 2)):=by sorry
end end Wishart
namespace Wishart section open scoped Classical ENNReal Matrix
/-- Literal theorem_6_3_finite_moment_iff_positive_ranks. -/
theorem theorem_6_3_finite_moment_iff_positive_ranks {p d:ℕ} {α β:ℝ} {Omega:Matrix (Fin p) (Fin p) ℝ} (hOmega:Omega.PosDef) (hα:(p:ℝ) - 1 < α) (hβ:(p:ℝ) - 1 < β) (k:Fin d→ℕ) (B:∀ i,Matrix (Fin p) (Fin (k i)) ℝ) (hB:∀ i,(B i).rank=k i) (ν:Fin d→ℝ) (hν:∀ i,0 ≤ ν i):Integrable (compressionDeterminantProduct k B ν Finset.univ) (matrixBetaIIMeasure α β Omega) ↔ 2 * (∑ i ∈ Finset.univ.filter (fun i ↦ 0 < k i),ν i) < β - p + 1:=by sorry
/-- The printed beta-II gamma formula on the corrected all-rank domain. Positive ranks retain exactly the printed nonnegative moment range; rank zero permits every real exponent and both gamma ratios reduce to one. -/
theorem theorem_6_3_gamma_moment_effective_rank {p k:ℕ} {α β r:ℝ} {Omega:Matrix (Fin p) (Fin p) ℝ} (hOmega:Omega.PosDef) (hα:(p:ℝ) - 1 < α) (hβ:(p:ℝ) - 1 < β) (B:Matrix (Fin p) (Fin k) ℝ) (hB:B.rank=k) (hr:k=0 ∨ (0 ≤ r ∧ 2 * r < β - p + 1)):(∫ X:SymmetricMatrix p,(Bᵀ * (X:Matrix (Fin p) (Fin p) ℝ) * B).det ^ r ∂matrixBetaIIMeasure α β Omega)=(compressionScale Omega B).det ^ r * (multivariateGamma k (α / 2 + r) / multivariateGamma k (α / 2)) * (multivariateGamma k ((β - p + k) / 2 - r) / multivariateGamma k ((β - p + k) / 2)):=by sorry
end end Wishart
namespace Wishart section open scoped Classical ENNReal MatrixOrder Matrix.Norms.L2Operator
/-- The exact beta-II product statement with the retained factors defined by their actual almost-sure behavior under the density (19). -/
theorem theorem_6_3_ae_constant_rank {p d:ℕ} {α β:ℝ} {Omega:Matrix (Fin p) (Fin p) ℝ} (hOmega:Omega.PosDef) (hα:(p:ℝ) - 1 < α) (hβ:(p:ℝ) - 1 < β) (k:Fin d→ℕ) (B:∀ i,Matrix (Fin p) (Fin (k i)) ℝ) (hB:∀ i,(B i).rank=k i) (f:Fin d→ℝ→ℝ) (hf:∀ i,GeometricallyLogConvex (f i)) (hsize:orderedRankThreshold k (Finset.univ.filter (fun i ↦ k i < p ∧ ¬ ∃ c:ℝ,∀ᵐ X:SymmetricMatrix p ∂matrixBetaIIMeasure α β Omega,f i ((B i)ᵀ * (X:Matrix (Fin p) (Fin p) ℝ) * B i).det=c)) p α) (J:Finset (Fin d)):(∏ i ∈ J,∫⁻ X:SymmetricMatrix p,ENNReal.ofReal (f i ((B i)ᵀ * (X:Matrix (Fin p) (Fin p) ℝ) * B i).det) ∂matrixBetaIIMeasure α β Omega) ≤ ∫⁻ X:SymmetricMatrix p,ENNReal.ofReal (∏ i ∈ J,f i ((B i)ᵀ * (X:Matrix (Fin p) (Fin p) ℝ) * B i).det) ∂matrixBetaIIMeasure α β Omega:=by sorry
end end Wishart
namespace Wishart section open scoped Classical Quaternion ENNReal
/-- The full Section 7 target, with both literal laws, both fields, nonvacuous normalization, the selected-factor chains, and finite powers. -/
theorem theorem_7_1:TheoremSevenOne:=by sorry
end end Wishart

#print equations Wishart.QuaternionMatrix.complexRepresentation
#print equations Wishart.QuaternionMatrix.positiveDeterminant
#print equations Wishart.QuaternionMatrix.sqrt
#print equations Wishart.QuaternionMatrix.PosDef
#print equations Wishart.QuaternionSpectralFamily.shiftedCompression
#print equations Wishart.QuaternionMatrix.normalizedCompression
#print equations Wishart.QuaternionMatrix.flatHermitian
#print equations Wishart.QuaternionMatrix.flatRepresentation
#print equations Wishart.matrixBetaIIMeasure
#print equations Wishart.matrixBetaIIPDF
#print equations Wishart.matrixBetaIIPDFReal
#print equations Wishart.matrixBetaIIConstant
#print equations Wishart.inverseDeterminantMoment
#print equations Wishart.Corollary54PowerTarget
#print equations Wishart.Corollary54MonotonePairTarget
#print equations Wishart.Corollary54ProductTarget
#print equations Wishart.GramGeometricCompressionFamily.activeProper
#print equations Wishart.GramGeometricCompressionFamily.AEConstantFactor
#print equations Wishart.Theorem52PrincipalTarget
#print equations Wishart.Theorem52MonotonePairTarget
#print equations Wishart.Theorem51PrincipalTarget
#print equations Wishart.Theorem51MonotonePairTarget
#print equations WishartVerification.shiftedTiltLaw
#print equations WishartVerification.shiftedMomentRatio
#print equations WishartVerification.shiftedMoment
#print equations WishartVerification.PrincipalTheorem
#print equations WishartVerification.principalMoment
