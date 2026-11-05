module
public import graph_foundation.part009
public import shared_results.part004
public import paper_results.part005

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.IntegralFamily -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false

/-!
# The polynomial-parameter integral comparison

The degree of a matrix index is the cardinality of its actual exterior face.
The matrix construction below restricts to these homogeneous submodules only
after proving that the differential lowers degree and both comparison maps
preserve degree. Matrix invertibility alone is not used as a substitute for
these degreewise chain identities.
-/

noncomputable section
namespace FourPapers.Sublattice
open Classical CategoryTheory CommAlg CommAlg.Koszul CommAlg.Polymatroid Polynomial

section MatrixComplexes
variable {R I M : Type*} [CommRing R] [Fintype I] [DecidableEq I]
  [AddCommGroup M] [Module R M]

lemma basisDegreePiece_preserved (b : Module.Basis I R M) (degree : I → ℕ)
    (f : M →ₗ[R] M)
    (hf : ∀ i j, degree j ≠ degree i → b.repr (f (b i)) j = 0)
    (p : ℕ) {x : M} (hx : x ∈ basisDegreePiece b degree p) :
    f x ∈ basisDegreePiece b degree p := by
  have hle : basisDegreePiece b degree p ≤ (basisDegreePiece b degree p).comap f := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, hi, rfl⟩
    change f (b i) ∈ basisDegreePiece b degree p
    rw [← b.linearCombination_repr (f (b i)), Finsupp.linearCombination_apply, Finsupp.sum]
    apply Submodule.sum_mem
    intro j hj
    apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨j, ?_, rfl⟩
    change degree i = p at hi
    change degree j = p
    by_contra hn
    exact (Finsupp.mem_support_iff.mp hj) (hf i j (by simpa [hi] using hn))
  exact hle hx

/-- A square-zero matrix gives the actual chain complex on the specified
homogeneous basis pieces, once its degree support has been checked. -/
def matrixComplexData (degree : I → ℕ) (D : Matrix I I R) (hDD : D * D = 0)
    (hdegree : ∀ i j, degree j + 1 ≠ degree i → D j i = 0) :
    FourPapers.SubmoduleComplexData R (I → R) where
  piece := basisDegreePiece (Pi.basisFun R I) degree
  d := D.toLin'
  square_zero := by
    apply LinearMap.ext
    intro x
    change Matrix.mulVec D (Matrix.mulVec D x) = 0
    rw [Matrix.mulVec_mulVec, hDD, Matrix.zero_mulVec]
  lowers p x hx := by
    apply basisDegreePiece_differential_lowers (Pi.basisFun R I) degree D.toLin' _ p hx
    intro i j hij
    simpa only [Pi.basisFun_repr, Pi.basisFun_apply, Matrix.toLin'_apply,
      Matrix.mulVec_single_one, Matrix.col_apply] using hdegree i j hij

lemma matrixUnit_equiv_exists (A : Matrix I I R) (hA : IsUnit A) :
    ∃ e : (I → R) ≃ₗ[R] (I → R), e.toLinearMap = A.toLin' := by
  rcases hA with ⟨a, rfl⟩
  exact ⟨Matrix.toLin'OfInv (M := (↑a⁻¹ : Matrix I I R)) (M' := ↑a)
    (by simp) (by simp), rfl⟩

/-- An invertible unitriangular matrix that respects exterior degree gives an
isomorphism of the genuine degreewise complexes, with the inverse checked on
every homogeneous submodule. -/
def unitriangularMatrixComplexIso (degree weight : I → ℕ)
    (D E F : Matrix I I R) (hDD : D * D = 0) (hEE : E * E = 0)
    (hDdegree : ∀ i j, degree j + 1 ≠ degree i → D j i = 0)
    (hEdegree : ∀ i j, degree j + 1 ≠ degree i → E j i = 0)
    (hFdegree : ∀ i j, degree j ≠ degree i → F j i = 0)
    (hFtriangular : ∀ i j, weight i ≤ weight j → F j i = if j = i then 1 else 0)
    (hFunit : IsUnit F) (hchain : D * F = F * E) :
    (matrixComplexData degree E hEE hEdegree).complex ≅
      (matrixComplexData degree D hDD hDdegree).complex := by
  let hex := matrixUnit_equiv_exists F hFunit
  let e := Classical.choose hex
  have he : e.toLinearMap = F.toLin' := Classical.choose_spec hex
  have hp : ∀ p x, x ∈ basisDegreePiece (Pi.basisFun R I) degree p →
      e x ∈ basisDegreePiece (Pi.basisFun R I) degree p := by
    intro p x hx
    change e.toLinearMap x ∈ _
    rw [he]
    apply basisDegreePiece_preserved (Pi.basisFun R I) degree F.toLin' _ p hx
    intro i j hij
    simpa only [Pi.basisFun_repr, Pi.basisFun_apply, Matrix.toLin'_apply,
      Matrix.mulVec_single_one, Matrix.col_apply] using hFdegree i j hij
  have hi : ∀ p x, x ∈ basisDegreePiece (Pi.basisFun R I) degree p →
      e.symm x ∈ basisDegreePiece (Pi.basisFun R I) degree p := by
    intro p x hx
    apply triangularInverse_preserves_span (Pi.basisFun R I) weight e
    · intro i
      change (Pi.basisFun R I).repr (e.toLinearMap _) i = 1
      rw [he]
      simpa only [Pi.basisFun_repr, Pi.basisFun_apply, Matrix.toLin'_apply,
        Matrix.mulVec_single_one, Matrix.col_apply, ↓reduceIte]
        using hFtriangular i i le_rfl
    · intro i j hij hw
      change (Pi.basisFun R I).repr (e.toLinearMap _) j = 0
      rw [he]
      simpa only [Pi.basisFun_repr, Pi.basisFun_apply, Matrix.toLin'_apply,
        Matrix.mulVec_single_one, Matrix.col_apply, if_neg (Ne.symm hij)]
        using hFtriangular i j hw
    · exact hp p
    · exact hx
  apply FourPapers.SubmoduleComplexData.isoOfTotal _ _ e hp hi
  change D.toLin'.comp e.toLinearMap = e.toLinearMap.comp E.toLin'
  rw [he, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul, hchain]

end MatrixComplexes

universe u
variable {k : Type u} [CommRing k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}
variable (m : ℕ) (α : Exponent (FiniteVariable.{u} n))

def chainMatrixDegree (a : ChainFaceIndex n E m α) : ℕ := a.2.val.card

lemma chainOrdinaryMatrix_square_zero (hE : finiteLatticeClosed n E) :
    chainOrdinaryMatrix (k := k) m α hE * chainOrdinaryMatrix m α hE = 0 := by
  unfold chainOrdinaryMatrix
  rw [← LinearMap.toMatrix_mul, chainTotalOrdinaryDifferential_square_zero, map_zero]

lemma chainSpecialMatrix_square_zero :
    chainSpecialMatrix (E := E) (k := k) m α * chainSpecialMatrix m α = 0 := by
  unfold chainSpecialMatrix
  rw [← LinearMap.toMatrix_mul, chainTotalSpecialDifferential_square_zero, map_zero]

lemma chainOrdinaryMatrix_degreeSupport (hE : finiteLatticeClosed n E)
    (i j : ChainFaceIndex n E m α)
    (h : chainMatrixDegree m α j + 1 ≠ chainMatrixDegree m α i) :
    chainOrdinaryMatrix (k := k) m α hE j i = 0 := by
  rw [chainOrdinaryMatrix, LinearMap.toMatrix_apply]
  exact chainTotalOrdinaryDifferential_degreeSupport hE m α k i j h

lemma chainChangeMatrix_degreeSupport (hE : finiteLatticeClosed n E)
    (i j : ChainFaceIndex n E m α)
    (h : chainMatrixDegree m α j ≠ chainMatrixDegree m α i) :
    chainChangeMatrix (k := k) m α hE j i = 0 := by
  rw [chainChangeMatrix, LinearMap.toMatrix_apply]
  apply repr_zero_of_mem_basis_span (chainTotalBasis n E m α k)
    {a | a.2.val.card = i.2.val.card}
  · apply allPowerChange_preserves_degree hE i.2.val.card
    exact Submodule.subset_span ⟨i, rfl, rfl⟩
  · exact h

lemma chainSpecialMatrix_degreeSupport (i j : ChainFaceIndex n E m α)
    (h : chainMatrixDegree m α j + 1 ≠ chainMatrixDegree m α i) :
    chainSpecialMatrix (k := k) m α j i = 0 := by
  rw [chainSpecialMatrix, LinearMap.toMatrix_apply]
  rw [chainTotalSpecialDifferential_basis, map_sum, Finsupp.finset_sum_apply]
  apply Finset.sum_eq_zero
  intro x _
  split_ifs with hq
  · have hne : (⟨i.1, i.2.val.erase x.val, hq⟩ : ChainFaceIndex n E m α) ≠ j := by
      intro he
      have hcard := congrArg (fun a : ChainFaceIndex n E m α => a.2.val.card) he
      apply h
      dsimp [chainMatrixDegree] at hcard ⊢
      rw [← hcard, Finset.card_erase_add_one x.property]
    rw [map_zsmul_unit, Module.Basis.repr_self]
    simp [Finsupp.single_apply, hne]
  · simp

lemma weightedChainDifferential_square_zero (hE : finiteLatticeClosed n E) :
    weightedChainDifferential (k := k) m α hE * weightedChainDifferential m α hE = 0 :=
  WeightedMatrix.homogenize_square_zero _ _
    (chainOrdinaryMatrix_nonIncreasing m α hE) (chainOrdinaryMatrix_square_zero m α hE)

lemma constantChainDifferential_square_zero :
    (chainSpecialMatrix (E := E) (k := k) m α).map C *
      (chainSpecialMatrix m α).map C = 0 := by
  rw [← Matrix.map_mul, chainSpecialMatrix_square_zero, Matrix.map_zero]
  simp

lemma weightedChainDifferential_degreeSupport (hE : finiteLatticeClosed n E)
    (i j : ChainFaceIndex n E m α)
    (h : chainMatrixDegree m α j + 1 ≠ chainMatrixDegree m α i) :
    weightedChainDifferential (k := k) m α hE j i = 0 := by
  simp only [weightedChainDifferential, WeightedMatrix.homogenize,
    chainOrdinaryMatrix_degreeSupport m α hE i j h, map_zero, zero_mul]

lemma constantChainDifferential_degreeSupport (i j : ChainFaceIndex n E m α)
    (h : chainMatrixDegree m α j + 1 ≠ chainMatrixDegree m α i) :
    (chainSpecialMatrix (k := k) m α).map C j i = 0 := by
  simp only [Matrix.map_apply, chainSpecialMatrix_degreeSupport m α i j h, map_zero]

/-- The fixed fine/auxiliary component of the literal weight-homogenized
ordinary Koszul matrix, with actual exterior cardinality as chain degree. -/
def weightedChainComplexData (hE : finiteLatticeClosed n E) :
    FourPapers.SubmoduleComplexData k[X] (ChainFaceIndex n E m α → k[X]) :=
  matrixComplexData (chainMatrixDegree m α) (weightedChainDifferential m α hE)
    (weightedChainDifferential_square_zero m α hE)
    (weightedChainDifferential_degreeSupport m α hE)

/-- The constant polynomial extension of the integral special-fiber matrix. -/
def constantChainComplexData :
    FourPapers.SubmoduleComplexData k[X] (ChainFaceIndex n E m α → k[X]) :=
  matrixComplexData (chainMatrixDegree m α) ((chainSpecialMatrix (k := k) m α).map C)
    (constantChainDifferential_square_zero m α)
    (constantChainDifferential_degreeSupport m α)

/-- The comparison over the polynomial parameter is an actual degreewise
chain isomorphism over every coefficient ring. -/
def weightedChainComplexIso (hE : finiteLatticeClosed n E) (hm : 0 < m) :
    (constantChainComplexData (E := E) (k := k) m α).complex ≅
      (weightedChainComplexData (k := k) m α hE).complex := by
  apply unitriangularMatrixComplexIso (chainMatrixDegree m α) (chainMatrixWeight m α)
    (weightedChainDifferential m α hE) ((chainSpecialMatrix m α).map C)
    (weightedChainComparison m α hE)
    (weightedChainDifferential_square_zero m α hE)
    (constantChainDifferential_square_zero m α)
    (weightedChainDifferential_degreeSupport m α hE)
    (constantChainDifferential_degreeSupport m α)
  · intro i j hij
    simp only [weightedChainComparison, WeightedMatrix.homogenize,
      chainChangeMatrix_degreeSupport m α hE i j hij, map_zero, zero_mul]
  · intro i j hij
    simp only [weightedChainComparison, WeightedMatrix.homogenize,
      chainChangeMatrix_unitriangular m α hE hm j i hij,
      Nat.sub_eq_zero_of_le hij, pow_zero, mul_one]
    split_ifs <;> simp
  · exact weightedChainComparison_isUnit m α hE hm
  · exact weightedChainComparison_chain m α hE hm

def weightedChainHomotopyEquiv (hE : finiteLatticeClosed n E) (hm : 0 < m) :
    HomotopyEquiv (constantChainComplexData (E := E) (k := k) m α).complex
      (weightedChainComplexData (k := k) m α hE).complex :=
  HomotopyEquiv.ofIso (weightedChainComplexIso m α hE hm)

/-- The actual parameter-zero differential is the special-fiber matrix used
in the constant complex. This follows from the chain relation and the identity
reduction of the comparison, without a field or torsion-freeness assumption. -/
theorem weightedChainDifferential_at_zero (hE : finiteLatticeClosed n E) (hm : 0 < m) :
    (weightedChainDifferential (k := k) m α hE).map (Polynomial.evalRingHom 0) =
      chainSpecialMatrix m α := by
  have h := congrArg (fun A : Matrix (ChainFaceIndex n E m α)
      (ChainFaceIndex n E m α) k[X] => A.map (Polynomial.evalRingHom 0))
    (weightedChainComparison_chain (k := k) m α hE hm)
  have hF : (weightedChainComparison (k := k) m α hE).map
      (Polynomial.evalRingHom 0) = 1 := by
    ext i j
    exact weightedChainComparison_at_zero m α hE hm i j
  have hE0 : ((chainSpecialMatrix (E := E) (k := k) m α).map C).map
      (Polynomial.evalRingHom 0) = chainSpecialMatrix m α := by
    ext i j
    simp
  simpa only [Matrix.map_mul, hF, hE0, Matrix.mul_one, Matrix.one_mul] using h

lemma finiteChainFactorWeight_zero (w : FiniteMultichain n E 0) :
    finiteChainFactorWeight.{u} w = 0 := by
  rw [finiteChainFactorWeight_sum]
  simp

lemma chainOrdinaryMatrix_zero_power (hE : finiteLatticeClosed n E) :
    chainOrdinaryMatrix (k := k) 0 α hE = chainSpecialMatrix 0 α := by
  ext i j
  have h := chainTotalDifferential_strictLower hE 0 α k j i (by
    rw [finiteChainFactorWeight_zero, finiteChainFactorWeight_zero])
  rw [LinearMap.sub_apply, map_sub, Finsupp.sub_apply] at h
  simpa only [chainOrdinaryMatrix, chainSpecialMatrix, LinearMap.toMatrix_apply] using
    sub_eq_zero.mp h

lemma weightedChainDifferential_zero_power (hE : finiteLatticeClosed n E) :
    weightedChainDifferential (k := k) 0 α hE = (chainSpecialMatrix 0 α).map C := by
  rw [weightedChainDifferential, WeightedMatrix.homogenize_weight_preserving,
    chainOrdinaryMatrix_zero_power α hE]
  intro i j hij
  exact (hij (by simp [chainMatrixWeight, finiteChainFactorWeight_zero])).elim

/-- The family comparison also includes auxiliary degree zero. -/
def weightedChainComplexIsoAll (hE : finiteLatticeClosed n E) :
    (constantChainComplexData (E := E) (k := k) m α).complex ≅
      (weightedChainComplexData (k := k) m α hE).complex := by
  cases m with
  | zero =>
      have h : weightedChainComplexData (k := k) 0 α hE =
          constantChainComplexData (E := E) (k := k) 0 α := by
        unfold weightedChainComplexData constantChainComplexData
        congr 1
        exact weightedChainDifferential_zero_power α hE
      exact (eqToIso (congrArg FourPapers.SubmoduleComplexData.complex h)).symm
  | succ m => exact weightedChainComplexIso (m + 1) α hE (Nat.succ_pos m)

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.weightedChainComplexIso
#print axioms FourPapers.Sublattice.weightedChainHomotopyEquiv
#print axioms FourPapers.Sublattice.weightedChainComplexIsoAll

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.AdmissibleMatrixFamily -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace FourPapers.Sublattice
open Classical CategoryTheory CommAlg CommAlg.Koszul CommAlg.Polymatroid Polynomial
universe u
variable {k : Type u} [CommRing k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}
variable (ω : FiniteReesVariable.{u} E → ℕ) (m : ℕ) (α : Exponent (FiniteVariable.{u} n))

def admissibleChainMatrixWeight (a : ChainFaceIndex n E m α) : ℕ :=
  admissibleChainWeight ω α a.1.val

lemma chainSpecialMatrix_admissible_preserving (i j : ChainFaceIndex n E m α)
    (h : admissibleChainMatrixWeight ω m α i ≠ admissibleChainMatrixWeight ω m α j) :
    chainSpecialMatrix (k := k) m α i j = 0 := by
  rw [chainSpecialMatrix, LinearMap.toMatrix_apply]
  exact blockMap_basis_weight_ne
    (fun w : AdmissibleChain n E m α => totalFaceBasis (k := k)
      (quotientKoszulFaces (finiteChainCoefficientFamily n w.val) (α - finiteChainShift n w.val)))
    (fun w => admissibleChainWeight ω α w.val)
    (fun w => quotientTotalDifferential (k := k) (finiteChainCoefficientFamily n w.val)
      (α - finiteChainShift n w.val)) j i (Ne.symm h)

lemma chainSpecialMatrix_admissible_nonIncreasing :
    WeightedMatrix.NonIncreasing (admissibleChainMatrixWeight ω m α)
      (chainSpecialMatrix (E := E) (k := k) m α) := by
  intro i j hij
  exact chainSpecialMatrix_admissible_preserving ω m α i j (ne_of_gt hij)

lemma chainOrdinaryMatrix_admissible_nonIncreasing (hE : finiteLatticeClosed n E)
    (hω : FiniteReesWeightAdmissible hE ω) :
    WeightedMatrix.NonIncreasing (admissibleChainMatrixWeight ω m α)
      (chainOrdinaryMatrix (k := k) m α hE) := by
  intro i j hij
  have h := chainTotalDifferential_admissible_strictLower hE ω hω m α k j i hij.le
  rw [LinearMap.sub_apply, map_sub, Finsupp.sub_apply] at h
  rw [chainOrdinaryMatrix, LinearMap.toMatrix_apply]
  have hz := chainSpecialMatrix_admissible_preserving (k := k) ω m α i j (ne_of_gt hij)
  rw [chainSpecialMatrix, LinearMap.toMatrix_apply] at hz
  rwa [hz, sub_zero] at h

lemma chainChangeMatrix_admissible_unitriangular (hE : finiteLatticeClosed n E)
    (hω : FiniteReesWeightAdmissible hE ω) (hm : 0 < m)
    (i j : ChainFaceIndex n E m α)
    (h : admissibleChainMatrixWeight ω m α j ≤ admissibleChainMatrixWeight ω m α i) :
    chainChangeMatrix (k := k) m α hE i j = if i = j then 1 else 0 := by
  rw [chainChangeMatrix, LinearMap.toMatrix_apply]
  have hh := allPowerChange_admissible_lower (k := k) ω hE hω hm j i h
  rw [map_sub, Finsupp.sub_apply, Module.Basis.repr_self, Finsupp.single_apply] at hh
  convert sub_eq_zero.mp hh using 1 <;> simp only [eq_comm]

def admissibleChainDifferential (hE : finiteLatticeClosed n E) :
    Matrix (ChainFaceIndex n E m α) (ChainFaceIndex n E m α) k[X] :=
  WeightedMatrix.homogenize (admissibleChainMatrixWeight ω m α)
    (chainOrdinaryMatrix (k := k) m α hE)

def admissibleChainComparison (hE : finiteLatticeClosed n E) :
    Matrix (ChainFaceIndex n E m α) (ChainFaceIndex n E m α) k[X] :=
  WeightedMatrix.homogenize (admissibleChainMatrixWeight ω m α)
    (chainChangeMatrix (k := k) m α hE)

theorem admissibleChainComparison_isUnit (hE : finiteLatticeClosed n E)
    (hω : FiniteReesWeightAdmissible hE ω) (hm : 0 < m) :
    IsUnit (admissibleChainComparison (k := k) ω m α hE) :=
  WeightedMatrix.homogenize_isUnit _ _
    (chainChangeMatrix_admissible_unitriangular ω m α hE hω hm)

theorem admissibleChainComparison_chain (hE : finiteLatticeClosed n E)
    (hω : FiniteReesWeightAdmissible hE ω) (hm : 0 < m) :
    admissibleChainDifferential (k := k) ω m α hE * admissibleChainComparison ω m α hE =
      admissibleChainComparison ω m α hE * (chainSpecialMatrix m α).map C := by
  have h := (WeightedMatrix.homogenized_chain_isomorphism
    (admissibleChainMatrixWeight ω m α)
    (chainOrdinaryMatrix (k := k) m α hE) (chainSpecialMatrix m α)
    (chainChangeMatrix m α hE)
    (chainOrdinaryMatrix_admissible_nonIncreasing ω m α hE hω)
    (chainSpecialMatrix_admissible_nonIncreasing ω m α)
    (chainChangeMatrix_admissible_unitriangular ω m α hE hω hm)
    (chainMatrix_relation m α hE)).2
  rw [WeightedMatrix.homogenize_weight_preserving _ _
    (chainSpecialMatrix_admissible_preserving ω m α)] at h
  exact h

theorem admissibleChainComparison_at_zero (hE : finiteLatticeClosed n E)
    (hω : FiniteReesWeightAdmissible hE ω) (hm : 0 < m)
    (i j : ChainFaceIndex n E m α) :
    (admissibleChainComparison (k := k) ω m α hE i j).eval 0 =
      (1 : Matrix _ _ k) i j :=
  WeightedMatrix.homogenize_unitriangular_at_zero _ _
    (chainChangeMatrix_admissible_unitriangular ω m α hE hω hm) i j

lemma admissibleChainDifferential_square_zero (hE : finiteLatticeClosed n E)
    (hω : FiniteReesWeightAdmissible hE ω) :
    admissibleChainDifferential (k := k) ω m α hE * admissibleChainDifferential ω m α hE = 0 :=
  WeightedMatrix.homogenize_square_zero _ _
    (chainOrdinaryMatrix_admissible_nonIncreasing ω m α hE hω)
    (chainOrdinaryMatrix_square_zero m α hE)

lemma admissibleChainDifferential_degreeSupport (hE : finiteLatticeClosed n E)
    (i j : ChainFaceIndex n E m α)
    (h : chainMatrixDegree m α j + 1 ≠ chainMatrixDegree m α i) :
    admissibleChainDifferential (k := k) ω m α hE j i = 0 := by
  simp only [admissibleChainDifferential, WeightedMatrix.homogenize,
    chainOrdinaryMatrix_degreeSupport m α hE i j h, map_zero, zero_mul]

def admissibleChainComplexData (hE : finiteLatticeClosed n E)
    (hω : FiniteReesWeightAdmissible hE ω) :
    FourPapers.SubmoduleComplexData k[X] (ChainFaceIndex n E m α → k[X]) :=
  matrixComplexData (chainMatrixDegree m α) (admissibleChainDifferential ω m α hE)
    (admissibleChainDifferential_square_zero ω m α hE hω)
    (admissibleChainDifferential_degreeSupport ω m α hE)

/-- Full matrix comparison for every admissible monic Gröbner weight. Its
triangularity is derived from actual reductions and the existing block lifts. -/
def admissibleChainComplexIso (hE : finiteLatticeClosed n E)
    (hω : FiniteReesWeightAdmissible hE ω) (hm : 0 < m) :
    (constantChainComplexData (E := E) (k := k) m α).complex ≅
      (admissibleChainComplexData (k := k) ω m α hE hω).complex := by
  apply unitriangularMatrixComplexIso (chainMatrixDegree m α)
    (admissibleChainMatrixWeight ω m α)
    (admissibleChainDifferential ω m α hE) ((chainSpecialMatrix m α).map C)
    (admissibleChainComparison ω m α hE)
    (admissibleChainDifferential_square_zero ω m α hE hω)
    (constantChainDifferential_square_zero m α)
    (admissibleChainDifferential_degreeSupport ω m α hE)
    (constantChainDifferential_degreeSupport m α)
  · intro i j hij
    simp only [admissibleChainComparison, WeightedMatrix.homogenize,
      chainChangeMatrix_degreeSupport m α hE i j hij, map_zero, zero_mul]
  · intro i j hij
    simp only [admissibleChainComparison, WeightedMatrix.homogenize,
      chainChangeMatrix_admissible_unitriangular ω m α hE hω hm j i hij,
      Nat.sub_eq_zero_of_le hij, pow_zero, mul_one]
    split_ifs <;> simp
  · exact admissibleChainComparison_isUnit ω m α hE hω hm
  · exact admissibleChainComparison_chain ω m α hE hω hm

theorem admissibleChainDifferential_at_zero (hE : finiteLatticeClosed n E)
    (hω : FiniteReesWeightAdmissible hE ω) (hm : 0 < m) :
    (admissibleChainDifferential (k := k) ω m α hE).map (Polynomial.evalRingHom 0) =
      chainSpecialMatrix m α := by
  have h := congrArg (fun A : Matrix (ChainFaceIndex n E m α)
      (ChainFaceIndex n E m α) k[X] => A.map (Polynomial.evalRingHom 0))
    (admissibleChainComparison_chain (k := k) ω m α hE hω hm)
  have hF : (admissibleChainComparison (k := k) ω m α hE).map
      (Polynomial.evalRingHom 0) = 1 := by
    apply Matrix.ext
    intro i j
    exact admissibleChainComparison_at_zero ω m α hE hω hm i j
  have hE0 : ((chainSpecialMatrix (E := E) (k := k) m α).map C).map
      (Polynomial.evalRingHom 0) = chainSpecialMatrix m α := by
    apply Matrix.ext
    intro i j
    simp
  simpa only [Matrix.map_mul, hF, hE0, Matrix.mul_one, Matrix.one_mul] using h

lemma admissibleChainWeight_zero_power (w : FiniteMultichain n E 0) :
    admissibleChainWeight ω α w = Finsupp.weight (fun v => ω (Sum.inl v)) α := by
  rw [admissibleChainWeight_eq]
  simp [finiteChainShift]

lemma admissibleChainDifferential_zero_power (hE : finiteLatticeClosed n E) :
    admissibleChainDifferential (k := k) ω 0 α hE = (chainSpecialMatrix 0 α).map C := by
  rw [admissibleChainDifferential, WeightedMatrix.homogenize_weight_preserving,
    chainOrdinaryMatrix_zero_power α hE]
  intro i j hij
  exact (hij (by simp [admissibleChainMatrixWeight, admissibleChainWeight_zero_power])).elim

/-- Auxiliary degree zero is included; its weight is constant on the whole
fine strand, and the family differential is already constant. -/
def admissibleChainComplexIsoAll (hE : finiteLatticeClosed n E)
    (hω : FiniteReesWeightAdmissible hE ω) :
    (constantChainComplexData (E := E) (k := k) m α).complex ≅
      (admissibleChainComplexData (k := k) ω m α hE hω).complex := by
  cases m with
  | zero =>
    have h : admissibleChainComplexData (k := k) ω 0 α hE hω =
        constantChainComplexData (E := E) (k := k) 0 α := by
      unfold admissibleChainComplexData constantChainComplexData
      congr 1
      exact admissibleChainDifferential_zero_power ω α hE
    exact (eqToIso (congrArg FourPapers.SubmoduleComplexData.complex h)).symm
  | succ m => exact admissibleChainComplexIso ω (m + 1) α hE hω (Nat.succ_pos m)

end FourPapers.Sublattice
end

#print axioms FourPapers.Sublattice.admissibleChainComplexIso
#print axioms FourPapers.Sublattice.admissibleChainDifferential_at_zero
#print axioms FourPapers.Sublattice.admissibleChainComplexIsoAll

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.IntegralFamilyAlgebra -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

/-!
# Identification with the actual integral Rees family

`finiteReesFamily` is the already constructed subalgebra of the monoid algebra
over `k[τ]`, with basis `τ^(standardWeight a) x^a`.  The differential here is
defined independently as multiplication by its actual base variables tensored
with exterior contraction.  Its coefficients are then identified with the
weight-homogenized matrices, rather than postulated to be those matrices.
-/

noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid Polynomial
open scoped TensorProduct
universe u
variable {k : Type u} [CommRing k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

def familyPresentedIndex (c : FiniteReesVariable.{u} E →₀ ℕ) :
    finiteReesExponentMonoid.{u} E := ⟨finiteReesExponentMap E c, ⟨c, rfl⟩⟩

lemma familyPresentedIndex_embedding (c : FiniteReesVariable.{u} E →₀ ℕ) :
    finiteReesMonoidEmbedding E (familyPresentedIndex c) =
      presentedExponent (finiteTupleImage E) (c.embDomain (finiteReesVariableEmbedding E)) := by
  apply Subtype.ext
  exact finiteReesExponentMap_embedding E c

lemma finiteStandardWeight_presented (hE : finiteLatticeClosed n E)
    (c : FiniteReesVariable.{u} E →₀ ℕ) (hc : FiniteReesStandard c) :
    finiteStandardWeight hE (familyPresentedIndex c) = finitePresentationWeight c := by
  unfold finiteStandardWeight standardWeight
  rw [familyPresentedIndex_embedding, canonicalExponent_presented,
    reesNormalForm_of_standard _ hc]
  rfl

def familyBaseIndex (v : FiniteVariable.{u} n) : finiteReesExponentMonoid.{u} E :=
  familyPresentedIndex (Finsupp.single (Sum.inl v) 1)

lemma familyBaseIndex_val (v : FiniteVariable.{u} n) :
    (familyBaseIndex (E := E) v).val = Finsupp.single (some v) 1 := by
  simp [familyBaseIndex, familyPresentedIndex, finiteReesExponentMap,
    Finsupp.weight_single, finiteReesVariableExponent]

lemma familyBaseIndex_standard (hE : finiteLatticeClosed n E)
    (v : FiniteVariable.{u} n) :
    FiniteReesStandard (Finsupp.single (Sum.inl v) 1 : FiniteReesVariable.{u} E →₀ ℕ) := by
  rw [finiteReesStandard_iff_colons hE]
  have hf : finiteFactorPart
      (Finsupp.single (Sum.inl v) 1 : FiniteReesVariable.{u} E →₀ ℕ) = 0 := by
    ext a
    simp [finiteFactorPart, Finsupp.comapDomain_apply]
  simp only [hf, Finsupp.zero_apply, ne_eq, not_true_eq_false, false_implies, implies_true,
    and_self]

lemma finiteStandardWeight_base (hE : finiteLatticeClosed n E)
    (v : FiniteVariable.{u} n) :
    finiteStandardWeight hE (familyBaseIndex (E := E) v) = 1 := by
  rw [familyBaseIndex, finiteStandardWeight_presented hE _ (familyBaseIndex_standard hE v)]
  simpa [finitePresentationWeight] using finitePresentationWeight_add_row (E := E) 0 v

def familyChainIndex {m : ℕ} (a : FiniteChainStandardIndex.{u} n E m) :
    finiteReesExponentMonoid.{u} E :=
  familyPresentedIndex (finiteChainPresentation a.1 a.2.val)

lemma familyChainIndex_val {m : ℕ} (a : FiniteChainStandardIndex.{u} n E m) :
    (familyChainIndex a).val = finiteTargetExponent (finiteChainIndexExponent a) m :=
  finiteChainPresentation_image a.1 a.2.val

lemma finiteStandardWeight_chain (hE : finiteLatticeClosed n E) {m : ℕ}
    (a : FiniteChainStandardIndex.{u} n E m) :
    finiteStandardWeight hE (familyChainIndex a) = chainIndexWeight a :=
  finiteStandardWeight_presented hE _
    ((finiteChainPresentation_standard_iff hE _ _).mpr a.2.property)

lemma familyBase_add_chain (hE : finiteLatticeClosed n E) {m : ℕ}
    (v : FiniteVariable.{u} n) (a : FiniteChainStandardIndex.{u} n E m) :
    familyBaseIndex (E := E) v + familyChainIndex a =
      familyChainIndex (chainIndexMultiply hE a v) := by
  apply Subtype.ext
  change (familyBaseIndex (E := E) v).val + (familyChainIndex a).val = _
  rw [familyBaseIndex_val, familyChainIndex_val, familyChainIndex_val,
    chainIndexMultiply_image, finiteTargetExponent_add_row, add_comm]

def familyBaseVariable (hE : finiteLatticeClosed n E) (v : FiniteVariable.{u} n) :
    finiteReesFamily k hE := finiteReesFamilyBasis k hE (familyBaseIndex (E := E) v)

/-- Literal multiplication in the constructed polynomial-parameter algebra.
The exponent is the exact drop of multichain weight. -/
lemma familyBaseVariable_mul_chain (hE : finiteLatticeClosed n E) {m : ℕ}
    (v : FiniteVariable.{u} n) (a : FiniteChainStandardIndex.{u} n E m) :
    familyBaseVariable (k := k) hE v * finiteReesFamilyBasis k hE (familyChainIndex a) =
      (X ^ (finiteChainFactorWeight.{u} a.1 -
        finiteChainFactorWeight.{u} (chainIndexMultiply hE a v).1) : k[X]) •
        finiteReesFamilyBasis k hE (familyChainIndex (chainIndexMultiply hE a v)) := by
  change weightedMonoidBasis (k := k) (finiteStandardWeight hE)
      (finiteStandardWeight_zero hE) (finiteStandardWeight_subadd hE)
      (familyBaseIndex v) *
      weightedMonoidBasis (k := k) (finiteStandardWeight hE)
        (finiteStandardWeight_zero hE) (finiteStandardWeight_subadd hE)
        (familyChainIndex a) =
    (X ^ (finiteChainFactorWeight.{u} a.1 -
      finiteChainFactorWeight.{u} (chainIndexMultiply hE a v).1) : k[X]) •
      weightedMonoidBasis (k := k) (finiteStandardWeight hE)
        (finiteStandardWeight_zero hE) (finiteStandardWeight_subadd hE)
        (familyChainIndex (chainIndexMultiply hE a v))
  rw [weightedMonoidBasis_mul]
  rw [familyBase_add_chain hE, finiteStandardWeight_base hE,
    finiteStandardWeight_chain hE, finiteStandardWeight_chain hE]
  congr 2
  rw [chainIndexWeight_eq, chainIndexWeight_eq, chainIndexMultiply_coefficient_degree]
  omega

/-- The ordinary tensor exterior algebra with coefficients in the genuine
integral family; the scalar ring is `k[τ]`. -/
abbrev FamilyKoszulTensorAlgebra (hE : finiteLatticeClosed n E) :=
  finiteReesFamily k hE ⊗[k[X]] Simplicial.Ambient (FiniteVariable.{u} n) k[X]

abbrev FamilyTensorIndex := finiteReesExponentMonoid.{u} E × Finset (FiniteVariable.{u} n)

def familyTensorBasis (hE : finiteLatticeClosed n E) :
    Module.Basis (FamilyTensorIndex (E := E)) k[X] (FamilyKoszulTensorAlgebra (k := k) hE) :=
  (finiteReesFamilyBasis k hE).tensorProduct
    (Simplicial.basis (V := FiniteVariable.{u} n) (k := k[X]))

/-- The actual relative Koszul differential in the family. -/
def familyKoszulDifferential (hE : finiteLatticeClosed n E) :
    Module.End k[X] (FamilyKoszulTensorAlgebra (k := k) hE) :=
  ∑ v : FiniteVariable.{u} n,
    TensorProduct.map (LinearMap.mulLeft k[X] (familyBaseVariable hE v))
      (Simplicial.contraction v)

lemma familyKoszulDifferential_tmul (hE : finiteLatticeClosed n E)
    (r : finiteReesFamily k hE) (x : Simplicial.Ambient (FiniteVariable.{u} n) k[X]) :
    familyKoszulDifferential hE (r ⊗ₜ[k[X]] x) =
      ∑ v : FiniteVariable.{u} n,
        (familyBaseVariable hE v * r) ⊗ₜ[k[X]] Simplicial.contraction v x := by
  simp only [familyKoszulDifferential, LinearMap.sum_apply,
    TensorProduct.map_tmul, LinearMap.mulLeft_apply]

variable (m : ℕ) (α : Exponent (FiniteVariable.{u} n))

def familyFaceEmbedding (hE : finiteLatticeClosed n E) :
    ChainFaceIndex n E m α ↪ FamilyTensorIndex (E := E) where
  toFun a := (familyChainIndex (chainFaceStandardIndex a), a.2.val)
  inj' a b hab := by
    apply chainFaceToActual_injective hE α
    apply Subtype.ext
    exact congrArg Prod.snd hab

def familyChainVector (hE : finiteLatticeClosed n E) (a : ChainFaceIndex n E m α) :
    FamilyKoszulTensorAlgebra (k := k) hE :=
  familyTensorBasis hE (familyFaceEmbedding m α hE a)

lemma familyChainVector_eq (hE : finiteLatticeClosed n E) (a : ChainFaceIndex n E m α) :
    familyChainVector (k := k) m α hE a =
      finiteReesFamilyBasis k hE (familyChainIndex (chainFaceStandardIndex a)) ⊗ₜ[k[X]]
        Simplicial.basis a.2.val :=
  Module.Basis.tensorProduct_apply _ _ _ _

lemma familyChainVector_linearIndependent (hE : finiteLatticeClosed n E) :
    LinearIndependent k[X] (familyChainVector (k := k) m α hE) :=
  (familyTensorBasis hE).linearIndependent.comp (familyFaceEmbedding m α hE)
    (familyFaceEmbedding m α hE).injective

/-- This differential identity is computed from multiplication in
`finiteReesFamily` and exterior contraction, before any matrix comparison. -/
theorem familyKoszulDifferential_chainVector (hE : finiteLatticeClosed n E)
    (a : ChainFaceIndex n E m α) :
    familyKoszulDifferential hE (familyChainVector (k := k) m α hE a) =
      ∑ v : {v // v ∈ a.2.val},
        TauCeti.ExteriorAlgebra.basisEraseSign v.val a.2.val •
          ((X ^ (chainMatrixWeight m α a -
            chainMatrixWeight m α (chainFaceErase hE a v.val)) : k[X]) •
            familyChainVector m α hE (chainFaceErase hE a v.val)) := by
  rw [familyChainVector_eq, familyKoszulDifferential_tmul]
  calc
    _ = ∑ v ∈ a.2.val,
        (familyBaseVariable hE v *
          finiteReesFamilyBasis k hE (familyChainIndex (chainFaceStandardIndex a))) ⊗ₜ[k[X]]
            Simplicial.contraction v (Simplicial.basis a.2.val) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro v _ hv
      simp only [Simplicial.contraction_basis, if_neg hv, TensorProduct.tmul_zero]
    _ = ∑ v : {v // v ∈ a.2.val},
        (familyBaseVariable hE v.val *
          finiteReesFamilyBasis k hE (familyChainIndex (chainFaceStandardIndex a))) ⊗ₜ[k[X]]
            Simplicial.contraction v.val (Simplicial.basis a.2.val) :=
      Finset.sum_subtype a.2.val (fun _ => Iff.rfl) _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v _
      rw [Simplicial.contraction_basis, if_pos v.property,
        familyBaseVariable_mul_chain hE, ← chainFaceErase_standard hE a v.val v.property,
        familyChainVector_eq, chainFaceErase_val]
      simp only [TensorProduct.tmul_smul, ← TensorProduct.smul_tmul']
      congr 3
      exact congrArg (Simplicial.basis (k := k[X])) (by
        ext x
        simp only [Finset.mem_erase])

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.familyKoszulDifferential_chainVector

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.AdmissibleFamilyAlgebra -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

/-!
The same normal-form basis identification as `IntegralFamilyAlgebra`, now for
arbitrary presentation weights. Index and exponent equivalences are reused;
the multiplication coefficients are recalculated for the new actual subalgebra.
-/

noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid Polynomial
open scoped TensorProduct
universe u
variable {k : Type u} [CommRing k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}
variable (ω : FiniteReesVariable.{u} E → ℕ)

lemma admissibleStandardWeight_presented (hE : finiteLatticeClosed n E)
    (c : FiniteReesVariable.{u} E →₀ ℕ) (hc : FiniteReesStandard c) :
    admissibleStandardWeight hE ω (familyPresentedIndex c) = Finsupp.weight ω c := by
  have he : finiteCanonicalExponent hE (familyPresentedIndex c) = c := by
    apply finiteReesStandard_image_injective hE
      (finiteCanonicalExponent_standard hE _) hc
    exact finiteCanonicalExponent_image hE _
  rw [admissibleStandardWeight, he]

lemma admissibleStandardWeight_base (hE : finiteLatticeClosed n E)
    (v : FiniteVariable.{u} n) :
    admissibleStandardWeight hE ω (familyBaseIndex (E := E) v) = ω (Sum.inl v) := by
  rw [familyBaseIndex, admissibleStandardWeight_presented ω hE _ (familyBaseIndex_standard hE v),
    Finsupp.weight_single, one_nsmul]

lemma admissibleStandardWeight_chain (hE : finiteLatticeClosed n E) {m : ℕ}
    (a : FiniteChainStandardIndex.{u} n E m) :
    admissibleStandardWeight hE ω (familyChainIndex a) = admissibleIndexWeight ω a :=
  admissibleStandardWeight_presented ω hE _
    ((finiteChainPresentation_standard_iff hE _ _).mpr a.2.property)

def admissibleFamilyBaseVariable (hE : finiteLatticeClosed n E)
    (hω : FiniteReesWeightAdmissible hE ω) (v : FiniteVariable.{u} n) :
    admissibleReesFamily k hE ω hω :=
  admissibleReesFamilyBasis k hE ω hω (familyBaseIndex (E := E) v)

lemma admissibleFamilyBaseVariable_mul_chain (hE : finiteLatticeClosed n E)
    (hω : FiniteReesWeightAdmissible hE ω) {m : ℕ}
    (v : FiniteVariable.{u} n) (a : FiniteChainStandardIndex.{u} n E m) :
    admissibleFamilyBaseVariable (k := k) ω hE hω v *
        admissibleReesFamilyBasis k hE ω hω (familyChainIndex a) =
      (X ^ (ω (Sum.inl v) + admissibleIndexWeight ω a -
        admissibleIndexWeight ω (chainIndexMultiply hE a v)) : k[X]) •
          admissibleReesFamilyBasis k hE ω hω (familyChainIndex (chainIndexMultiply hE a v)) := by
  calc
    _ = (X ^ (admissibleStandardWeight hE ω (familyBaseIndex v) +
        admissibleStandardWeight hE ω (familyChainIndex a) -
        admissibleStandardWeight hE ω (familyBaseIndex v + familyChainIndex a)) : k[X]) •
          admissibleReesFamilyBasis k hE ω hω (familyBaseIndex v + familyChainIndex a) :=
      weightedMonoidBasis_mul (admissibleStandardWeight hE ω)
        (admissibleStandardWeight_zero hE ω) (admissibleStandardWeight_subadd hE ω hω) _ _
    _ = _ := by
      rw [familyBase_add_chain hE, admissibleStandardWeight_base ω hE,
        admissibleStandardWeight_chain ω hE, admissibleStandardWeight_chain ω hE]

abbrev AdmissibleFamilyKoszulTensorAlgebra (hE : finiteLatticeClosed n E)
    (hω : FiniteReesWeightAdmissible hE ω) :=
  admissibleReesFamily k hE ω hω ⊗[k[X]] Simplicial.Ambient (FiniteVariable.{u} n) k[X]

def admissibleFamilyTensorBasis (hE : finiteLatticeClosed n E)
    (hω : FiniteReesWeightAdmissible hE ω) :
    Module.Basis (FamilyTensorIndex (E := E)) k[X]
      (AdmissibleFamilyKoszulTensorAlgebra (k := k) ω hE hω) :=
  (admissibleReesFamilyBasis k hE ω hω).tensorProduct
    (Simplicial.basis (V := FiniteVariable.{u} n) (k := k[X]))

/-- Relative Koszul differential defined from multiplication by the actual
base-variable elements of the arbitrary-weight family. -/
def admissibleFamilyKoszulDifferential (hE : finiteLatticeClosed n E)
    (hω : FiniteReesWeightAdmissible hE ω) :
    Module.End k[X] (AdmissibleFamilyKoszulTensorAlgebra (k := k) ω hE hω) :=
  ∑ v : FiniteVariable.{u} n,
    TensorProduct.map (LinearMap.mulLeft k[X] (admissibleFamilyBaseVariable ω hE hω v))
      (Simplicial.contraction v)

lemma admissibleFamilyKoszulDifferential_tmul (hE : finiteLatticeClosed n E)
    (hω : FiniteReesWeightAdmissible hE ω) (r : admissibleReesFamily k hE ω hω)
    (x : Simplicial.Ambient (FiniteVariable.{u} n) k[X]) :
    admissibleFamilyKoszulDifferential ω hE hω (r ⊗ₜ[k[X]] x) =
      ∑ v : FiniteVariable.{u} n,
        (admissibleFamilyBaseVariable ω hE hω v * r) ⊗ₜ[k[X]] Simplicial.contraction v x := by
  simp only [admissibleFamilyKoszulDifferential, LinearMap.sum_apply,
    TensorProduct.map_tmul, LinearMap.mulLeft_apply]

variable (m : ℕ) (α : Exponent (FiniteVariable.{u} n))

def admissibleFamilyChainVector (hE : finiteLatticeClosed n E)
    (hω : FiniteReesWeightAdmissible hE ω) (a : ChainFaceIndex n E m α) :
    AdmissibleFamilyKoszulTensorAlgebra (k := k) ω hE hω :=
  admissibleFamilyTensorBasis ω hE hω (familyFaceEmbedding m α hE a)

lemma admissibleFamilyChainVector_eq (hE : finiteLatticeClosed n E)
    (hω : FiniteReesWeightAdmissible hE ω) (a : ChainFaceIndex n E m α) :
    admissibleFamilyChainVector (k := k) ω m α hE hω a =
      admissibleReesFamilyBasis k hE ω hω (familyChainIndex (chainFaceStandardIndex a)) ⊗ₜ[k[X]]
        Simplicial.basis a.2.val :=
  Module.Basis.tensorProduct_apply _ _ _ _

lemma admissibleFamilyChainVector_linearIndependent (hE : finiteLatticeClosed n E)
    (hω : FiniteReesWeightAdmissible hE ω) :
    LinearIndependent k[X] (admissibleFamilyChainVector (k := k) ω m α hE hω) :=
  (admissibleFamilyTensorBasis ω hE hω).linearIndependent.comp (familyFaceEmbedding m α hE)
    (familyFaceEmbedding m α hE).injective

lemma admissibleFace_weight_drop (hE : finiteLatticeClosed n E)
    (a : ChainFaceIndex n E m α) (v : FiniteVariable.{u} n) (hv : v ∈ a.2.val) :
    ω (Sum.inl v) + admissibleIndexWeight ω (chainFaceStandardIndex a) -
        admissibleIndexWeight ω (chainFaceStandardIndex (chainFaceErase hE a v)) =
      admissibleChainMatrixWeight ω m α a -
        admissibleChainMatrixWeight ω m α (chainFaceErase hE a v) := by
  have hs := admissibleChainWeight_face ω a
  have ht := admissibleChainWeight_face ω (chainFaceErase hE a v)
  have hf := faceWeight_erase_add (fun x => ω (Sum.inl x)) a.2.val v hv
  rw [chainFaceErase_val] at ht
  unfold admissibleChainMatrixWeight
  omega

theorem admissibleFamilyKoszulDifferential_chainVector (hE : finiteLatticeClosed n E)
    (hω : FiniteReesWeightAdmissible hE ω) (a : ChainFaceIndex n E m α) :
    admissibleFamilyKoszulDifferential ω hE hω
      (admissibleFamilyChainVector (k := k) ω m α hE hω a) =
      ∑ v : {v // v ∈ a.2.val},
        TauCeti.ExteriorAlgebra.basisEraseSign v.val a.2.val •
          ((X ^ (admissibleChainMatrixWeight ω m α a -
            admissibleChainMatrixWeight ω m α (chainFaceErase hE a v.val)) : k[X]) •
            admissibleFamilyChainVector ω m α hE hω (chainFaceErase hE a v.val)) := by
  rw [admissibleFamilyChainVector_eq, admissibleFamilyKoszulDifferential_tmul]
  calc
    _ = ∑ v ∈ a.2.val,
        (admissibleFamilyBaseVariable ω hE hω v *
          admissibleReesFamilyBasis k hE ω hω (familyChainIndex (chainFaceStandardIndex a))) ⊗ₜ[k[X]]
            Simplicial.contraction v (Simplicial.basis a.2.val) := by
      symm
      apply Finset.sum_subset (Finset.subset_univ _)
      intro v hv hnot
      simp only [Simplicial.contraction_basis, if_neg hnot, TensorProduct.tmul_zero]
    _ = ∑ v : {v // v ∈ a.2.val},
        (admissibleFamilyBaseVariable ω hE hω v.val *
          admissibleReesFamilyBasis k hE ω hω (familyChainIndex (chainFaceStandardIndex a))) ⊗ₜ[k[X]]
            Simplicial.contraction v.val (Simplicial.basis a.2.val) :=
      Finset.sum_subtype a.2.val (fun _ => Iff.rfl) _
    _ = _ := by
      apply Finset.sum_congr rfl
      intro v hv
      rw [Simplicial.contraction_basis, if_pos v.property,
        admissibleFamilyBaseVariable_mul_chain ω hE hω,
        ← chainFaceErase_standard hE a v.val v.property,
        admissibleFace_weight_drop ω m α hE a v.val v.property,
        admissibleFamilyChainVector_eq, chainFaceErase_val]
      simp only [TensorProduct.tmul_smul, ← TensorProduct.smul_tmul']
      congr 3
      exact congrArg (Simplicial.basis (k := k[X])) (by
        ext x
        simp only [Finset.mem_erase])

end FourPapers.Sublattice
end

#print axioms FourPapers.Sublattice.admissibleFamilyKoszulDifferential_chainVector

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.IntegralFamilyStrands -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false

/-!
# Actual fine strands of the integral family

The coefficient-exterior basis is restricted by its genuine fine and auxiliary
degrees.  A proved bijection identifies this whole basis with the multichain
normal-form basis.  The comparison with the matrix complex is justified both on
the homogeneous terms and on the literal variable-multiplication differential.
-/

noncomputable section
namespace FourPapers.Sublattice
open Classical CategoryTheory CommAlg CommAlg.Koszul CommAlg.Polymatroid Polynomial
universe u
variable {k : Type u} [CommRing k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}
variable (m : ℕ) (α : Exponent (FiniteVariable.{u} n))

def familyFineExponent (a : finiteReesExponentMonoid.{u} E) :
    Exponent (FiniteVariable.{u} n) :=
  a.val.comapDomain some (Option.some_injective _).injOn

lemma familyTarget_reconstruct (a : finiteReesExponentMonoid.{u} E) :
    finiteTargetExponent (familyFineExponent a) (a.val none) = a.val := by
  ext x
  cases x with
  | none => simp
  | some x => simp [familyFineExponent]

/-- Actual fine/auxiliary degree on the tensor basis, including the exterior
generator's contribution to the fine degree. -/
def familyStrandPredicate (a : FamilyTensorIndex (E := E)) : Prop :=
  a.1.val none = m ∧ familyFineExponent a.1 + faceExponent a.2 = α

lemma familyFaceEmbedding_mem (hE : finiteLatticeClosed n E)
    (a : ChainFaceIndex n E m α) :
    familyStrandPredicate m α (familyFaceEmbedding m α hE a) := by
  constructor
  · change (familyChainIndex (chainFaceStandardIndex a)).val none = m
    rw [familyChainIndex_val, finiteTargetExponent_none]
  · have h : familyFineExponent (familyChainIndex (chainFaceStandardIndex a)) =
        α - faceExponent a.2.val := by
      ext v
      simp only [familyFineExponent, Finsupp.comapDomain_apply,
        familyChainIndex_val, finiteTargetExponent_some, chainFaceStandardIndex_exponent]
    change familyFineExponent (familyChainIndex (chainFaceStandardIndex a)) +
      faceExponent a.2.val = α
    rw [h, tsub_add_cancel_of_le (chainFaceIndex_face_le a)]

/-- Every tensor-basis vector in the requested genuine fine/auxiliary degree
occurs, and no other tensor-basis vector occurs. -/
theorem familyFaceEmbedding_range (hE : finiteLatticeClosed n E) :
    Set.range (familyFaceEmbedding m α hE) = {a | familyStrandPredicate m α a} := by
  ext a
  constructor
  · rintro ⟨b, rfl⟩
    exact familyFaceEmbedding_mem m α hE b
  · rintro ⟨hm, hα⟩
    have hface : faceExponent a.2 ≤ α := by
      rw [← hα]
      exact le_add_of_nonneg_left zero_le
    have hexp : finiteTargetExponent (α - faceExponent a.2) m = a.1.val := by
      rw [← hα, add_tsub_cancel_right, ← hm, familyTarget_reconstruct]
    have hcoeff : Contains (exponentPowerFamily (finiteRowFamily n E) m)
        (α - faceExponent a.2) := by
      apply (finiteTarget_mem_rees_iff _ _).mp
      rw [hexp]
      exact a.1.property
    let b := (chainFaceEquiv hE α).symm ⟨a.2, hface, hcoeff⟩
    have hb : b.2.val = a.2 :=
      congrArg Subtype.val ((chainFaceEquiv hE α).apply_symm_apply ⟨a.2, hface, hcoeff⟩)
    refine ⟨b, ?_⟩
    apply Prod.ext
    · apply Subtype.ext
      change (familyChainIndex (chainFaceStandardIndex b)).val = a.1.val
      rw [familyChainIndex_val, chainFaceStandardIndex_exponent, hb, hexp]
    · exact hb

/-- The literal fine/auxiliary homogeneous submodule of the tensor algebra. -/
def familyStrandTotal (hE : finiteLatticeClosed n E) :
    Submodule k[X] (FamilyKoszulTensorAlgebra (k := k) hE) :=
  Submodule.span k[X] ((familyTensorBasis (k := k) hE) ''
    {a | familyStrandPredicate m α a})

instance familyStrandTotalAddCommGroup (hE : finiteLatticeClosed n E) :
    AddCommGroup (familyStrandTotal (k := k) m α hE) :=
  Module.addCommMonoidToAddCommGroup k[X]

lemma familyChainSpan_eq (hE : finiteLatticeClosed n E) :
    Submodule.span k[X] (Set.range (familyChainVector (k := k) m α hE)) =
      familyStrandTotal m α hE := by
  have hr : Set.range (familyChainVector (k := k) m α hE) =
      familyTensorBasis hE '' {a | familyStrandPredicate m α a} := by
    rw [← familyFaceEmbedding_range m α hE]
    exact Set.range_comp (familyTensorBasis hE) (familyFaceEmbedding m α hE)
  rw [hr]
  rfl

def familyStrandBasis (hE : finiteLatticeClosed n E) :
    Module.Basis (ChainFaceIndex n E m α) k[X] (familyStrandTotal (k := k) m α hE) :=
  (Module.Basis.span (familyChainVector_linearIndependent (k := k) m α hE)).map
    (LinearEquiv.ofEq _ _ (familyChainSpan_eq m α hE))

lemma familyStrandBasis_val (hE : finiteLatticeClosed n E)
    (a : ChainFaceIndex n E m α) :
    (familyStrandBasis (k := k) m α hE a).val = familyChainVector m α hE a := by
  change (Module.Basis.span (familyChainVector_linearIndependent (k := k) m α hE) a).val = _
  exact Module.Basis.coe_span_apply _ a

def familyStrandCoordinates (hE : finiteLatticeClosed n E) :
    (ChainFaceIndex n E m α → k[X]) ≃ₗ[k[X]] familyStrandTotal (k := k) m α hE :=
  (Pi.basisFun k[X] (ChainFaceIndex n E m α)).equiv (familyStrandBasis m α hE) (Equiv.refl _)

lemma familyStrandCoordinates_basis (hE : finiteLatticeClosed n E)
    (a : ChainFaceIndex n E m α) :
    familyStrandCoordinates (k := k) m α hE (Pi.basisFun k[X] _ a) =
      familyStrandBasis m α hE a :=
  Module.Basis.equiv_apply _ _ _ _

lemma weightedChainDifferential_basis (hE : finiteLatticeClosed n E)
    (a : ChainFaceIndex n E m α) :
    (weightedChainDifferential (k := k) m α hE).toLin' (Pi.basisFun k[X] _ a) =
      ∑ v : {v // v ∈ a.2.val},
        TauCeti.ExteriorAlgebra.basisEraseSign v.val a.2.val •
          ((X ^ (chainMatrixWeight m α a -
            chainMatrixWeight m α (chainFaceErase hE a v.val)) : k[X]) •
              Pi.basisFun k[X] _ (chainFaceErase hE a v.val)) := by
  apply _root_.funext
  intro b
  simp only [Pi.basisFun_apply, Matrix.toLin'_apply, Matrix.mulVec_single_one,
    Matrix.col_apply, weightedChainDifferential, WeightedMatrix.homogenize,
    chainOrdinaryMatrix, LinearMap.toMatrix_apply]
  rw [chainTotalOrdinaryDifferential_basis, map_sum, Finsupp.finset_sum_apply,
    map_sum, Finset.sum_mul]
  simp only [Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hb : chainFaceErase hE a v.val = b
  · subst b
    simp only [map_zsmul_unit, Finsupp.smul_apply, Module.Basis.repr_self,
      Finsupp.single_eq_same, Pi.single_eq_same, smul_eq_mul, mul_one]
    simp only [map_one, smul_mul_assoc, one_mul]
  · simp [map_zsmul_unit, Module.Basis.repr_self, hb, Ne.symm hb]

/-- The coordinate map intertwines the matrix differential with the actual
relative Koszul differential in the tensor algebra. -/
theorem familyStrandCoordinates_intertwines (hE : finiteLatticeClosed n E)
    (x : ChainFaceIndex n E m α → k[X]) :
    familyKoszulDifferential hE (familyStrandCoordinates (k := k) m α hE x).val =
      (familyStrandCoordinates m α hE ((weightedChainDifferential m α hE).toLin' x)).val := by
  let f := (familyStrandTotal (k := k) m α hE).subtype.comp
    (familyStrandCoordinates m α hE).toLinearMap
  have hf (a : ChainFaceIndex n E m α) :
      f (Pi.basisFun k[X] _ a) = familyChainVector m α hE a := by
    change (familyStrandCoordinates (k := k) m α hE (Pi.basisFun k[X] _ a)).val = _
    rw [familyStrandCoordinates_basis, familyStrandBasis_val]
  have h : (familyKoszulDifferential hE).comp f =
      f.comp (weightedChainDifferential m α hE).toLin' := by
    apply (Pi.basisFun k[X] (ChainFaceIndex n E m α)).ext
    intro a
    change familyKoszulDifferential hE (f (Pi.basisFun k[X] _ a)) =
      f ((weightedChainDifferential m α hE).toLin' (Pi.basisFun k[X] _ a))
    rw [hf, familyKoszulDifferential_chainVector, weightedChainDifferential_basis, map_sum]
    apply Finset.sum_congr rfl
    intro v _
    rw [LinearMap.map_smul_of_tower (R := ℤˣ) f, f.map_smul, hf]
  exact LinearMap.congr_fun h x

section Transport
universe v
variable {R : Type*} {A B : Type v} [CommRing R] [AddCommGroup A] [Module R A]
  [AddCommGroup B] [Module R B]

/-- Transport of a checked total differential and its explicit homogeneous
submodules along a linear equivalence. -/
def transportComplexData (C : FourPapers.SubmoduleComplexData R A) (e : A ≃ₗ[R] B) :
    FourPapers.SubmoduleComplexData R B where
  piece p := (C.piece p).map e.toLinearMap
  d := e.toLinearMap.comp (C.d.comp e.symm.toLinearMap)
  square_zero := by
    apply LinearMap.ext
    intro x
    change e (C.d (e.symm (e (C.d (e.symm x))))) = 0
    rw [e.symm_apply_apply]
    have h := LinearMap.congr_fun C.square_zero (e.symm x)
    change C.d (C.d (e.symm x)) = 0 at h
    rw [h, map_zero]
  lowers p x hx := by
    obtain ⟨y, hy, rfl⟩ := hx
    change e (C.d (e.symm (e y))) ∈ _
    rw [e.symm_apply_apply]
    exact ⟨C.d y, C.lowers p y hy, rfl⟩

def transportComplexIso (C : FourPapers.SubmoduleComplexData R A) (e : A ≃ₗ[R] B) :
    C.complex ≅ (transportComplexData C e).complex := by
  apply FourPapers.SubmoduleComplexData.isoOfTotal _ _ e
  · intro p x hx
    exact ⟨x, hx, rfl⟩
  · intro p x hx
    obtain ⟨y, hy, rfl⟩ := hx
    change e.symm (e y) ∈ C.piece p
    rwa [e.symm_apply_apply]
  · apply LinearMap.ext
    intro x
    change e (C.d (e.symm (e x))) = e (C.d x)
    rw [e.symm_apply_apply]

end Transport

/-- The actual family strand, with its fine-degree module and polynomial
coefficient action. The following two theorems identify its terms and
differential with the conventional relative Koszul construction. -/
def familyStrandComplexData (hE : finiteLatticeClosed n E) :
    FourPapers.SubmoduleComplexData k[X] (familyStrandTotal (k := k) m α hE) :=
  transportComplexData (weightedChainComplexData m α hE) (familyStrandCoordinates m α hE)

theorem familyStrandComplexData_piece (hE : finiteLatticeClosed n E) (p : ℕ) :
    (familyStrandComplexData (k := k) m α hE).piece p =
      basisDegreePiece (familyStrandBasis m α hE) (chainMatrixDegree m α) p := by
  change (Submodule.span k[X] (Pi.basisFun k[X] (ChainFaceIndex n E m α) ''
      {a | chainMatrixDegree m α a = p})).map
        (familyStrandCoordinates m α hE).toLinearMap = _
  rw [Submodule.map_span]
  congr 1
  rw [Set.image_image]
  apply Set.image_congr
  intro a _
  exact familyStrandCoordinates_basis m α hE a

theorem familyStrandComplexData_d (hE : finiteLatticeClosed n E)
    (x : familyStrandTotal (k := k) m α hE) :
    ((familyStrandComplexData m α hE).d x).val = familyKoszulDifferential hE x.val := by
  have h := familyStrandCoordinates_intertwines m α hE
    ((familyStrandCoordinates (k := k) m α hE).symm x)
  change (familyStrandCoordinates (k := k) m α hE
    ((weightedChainDifferential m α hE).toLin'
      ((familyStrandCoordinates m α hE).symm x))).val = _
  simpa only [LinearEquiv.apply_symm_apply] using h.symm

/-- The fixed fine/auxiliary strand of the actual Rees family's relative
Koszul complex is isomorphic to the constant special-fiber complex over `k[τ]`.
Both the source identification and the literal target differential are checked
above; this is the family assertion in Theorem 7.1. -/
def integralFamilyKoszulIso (hE : finiteLatticeClosed n E) (hm : 0 < m) :
    (constantChainComplexData (E := E) (k := k) m α).complex ≅
      (familyStrandComplexData (k := k) m α hE).complex :=
  weightedChainComplexIso m α hE hm ≪≫
    transportComplexIso (weightedChainComplexData m α hE) (familyStrandCoordinates m α hE)

def integralFamilyKoszulHomotopyEquiv (hE : finiteLatticeClosed n E) (hm : 0 < m) :
    HomotopyEquiv (constantChainComplexData (E := E) (k := k) m α).complex
      (familyStrandComplexData (k := k) m α hE).complex :=
  HomotopyEquiv.ofIso (integralFamilyKoszulIso m α hE hm)

/-- Every nonnegative auxiliary degree is included, including the polynomial
ring component in auxiliary degree zero. -/
def integralFamilyKoszulIsoAll (hE : finiteLatticeClosed n E) :
    (constantChainComplexData (E := E) (k := k) m α).complex ≅
      (familyStrandComplexData (k := k) m α hE).complex :=
  weightedChainComplexIsoAll m α hE ≪≫
    transportComplexIso (weightedChainComplexData m α hE) (familyStrandCoordinates m α hE)

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.familyFaceEmbedding_range
#print axioms FourPapers.Sublattice.familyStrandCoordinates_intertwines
#print axioms FourPapers.Sublattice.familyStrandComplexData_d
#print axioms FourPapers.Sublattice.integralFamilyKoszulIso
#print axioms FourPapers.Sublattice.integralFamilyKoszulHomotopyEquiv
#print axioms FourPapers.Sublattice.integralFamilyKoszulIsoAll

end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.AdmissibleFamilyStrands -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace FourPapers.Sublattice
open Classical CategoryTheory CommAlg CommAlg.Koszul CommAlg.Polymatroid Polynomial
universe u
variable {k : Type u} [CommRing k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}
variable (ω : FiniteReesVariable.{u} E → ℕ) (m : ℕ) (α : Exponent (FiniteVariable.{u} n))

def admissibleFamilyStrandTotal (hE : finiteLatticeClosed n E)
    (hω : FiniteReesWeightAdmissible hE ω) :
    Submodule k[X] (AdmissibleFamilyKoszulTensorAlgebra ω (k := k) hE hω) :=
  Submodule.span k[X] ((admissibleFamilyTensorBasis ω (k := k) hE hω) ''
    {a | familyStrandPredicate m α a})

instance admissibleFamilyStrandTotalAddCommGroup (hE : finiteLatticeClosed n E)
    (hω : FiniteReesWeightAdmissible hE ω) :
    AddCommGroup (admissibleFamilyStrandTotal ω (k := k) m α hE hω) :=
  Module.addCommMonoidToAddCommGroup k[X]

lemma admissibleFamilyChainSpan_eq (hE : finiteLatticeClosed n E)
    (hω : FiniteReesWeightAdmissible hE ω) :
    Submodule.span k[X] (Set.range (admissibleFamilyChainVector ω (k := k) m α hE hω)) =
      admissibleFamilyStrandTotal ω m α hE hω := by
  have hr : Set.range (admissibleFamilyChainVector ω (k := k) m α hE hω) =
      admissibleFamilyTensorBasis ω hE hω '' {a | familyStrandPredicate m α a} := by
    rw [← familyFaceEmbedding_range m α hE]
    exact Set.range_comp (admissibleFamilyTensorBasis ω hE hω) (familyFaceEmbedding m α hE)
  rw [hr]
  rfl

def admissibleFamilyStrandBasis (hE : finiteLatticeClosed n E)
    (hω : FiniteReesWeightAdmissible hE ω) :
    Module.Basis (ChainFaceIndex n E m α) k[X] (admissibleFamilyStrandTotal ω (k := k) m α hE hω) :=
  (Module.Basis.span (admissibleFamilyChainVector_linearIndependent ω (k := k) m α hE hω)).map
    (LinearEquiv.ofEq _ _ (admissibleFamilyChainSpan_eq ω m α hE hω))

lemma admissibleFamilyStrandBasis_val (hE : finiteLatticeClosed n E)
    (hω : FiniteReesWeightAdmissible hE ω)
    (a : ChainFaceIndex n E m α) :
    (admissibleFamilyStrandBasis ω (k := k) m α hE hω a).val = admissibleFamilyChainVector ω m α hE hω a := by
  change (Module.Basis.span (admissibleFamilyChainVector_linearIndependent ω (k := k) m α hE hω) a).val = _
  exact Module.Basis.coe_span_apply _ a

def admissibleFamilyStrandCoordinates (hE : finiteLatticeClosed n E)
    (hω : FiniteReesWeightAdmissible hE ω) :
    (ChainFaceIndex n E m α → k[X]) ≃ₗ[k[X]] admissibleFamilyStrandTotal ω (k := k) m α hE hω :=
  (Pi.basisFun k[X] (ChainFaceIndex n E m α)).equiv (admissibleFamilyStrandBasis ω m α hE hω) (Equiv.refl _)

lemma admissibleFamilyStrandCoordinates_basis (hE : finiteLatticeClosed n E)
    (hω : FiniteReesWeightAdmissible hE ω)
    (a : ChainFaceIndex n E m α) :
    admissibleFamilyStrandCoordinates ω (k := k) m α hE hω (Pi.basisFun k[X] _ a) =
      admissibleFamilyStrandBasis ω m α hE hω a :=
  Module.Basis.equiv_apply _ _ _ _

lemma admissibleChainDifferential_basis (hE : finiteLatticeClosed n E)
    (a : ChainFaceIndex n E m α) :
    (admissibleChainDifferential ω (k := k) m α hE).toLin' (Pi.basisFun k[X] _ a) =
      ∑ v : {v // v ∈ a.2.val},
        TauCeti.ExteriorAlgebra.basisEraseSign v.val a.2.val •
          ((X ^ (admissibleChainMatrixWeight ω m α a -
            admissibleChainMatrixWeight ω m α (chainFaceErase hE a v.val)) : k[X]) •
              Pi.basisFun k[X] _ (chainFaceErase hE a v.val)) := by
  apply _root_.funext
  intro b
  simp only [Pi.basisFun_apply, Matrix.toLin'_apply, Matrix.mulVec_single_one,
    Matrix.col_apply, admissibleChainDifferential, WeightedMatrix.homogenize,
    chainOrdinaryMatrix, LinearMap.toMatrix_apply]
  rw [chainTotalOrdinaryDifferential_basis, map_sum, Finsupp.finset_sum_apply,
    map_sum, Finset.sum_mul]
  simp only [Finset.sum_apply, Pi.smul_apply]
  apply Finset.sum_congr rfl
  intro v _
  by_cases hb : chainFaceErase hE a v.val = b
  · subst b
    simp only [map_zsmul_unit, Finsupp.smul_apply, Module.Basis.repr_self,
      Finsupp.single_eq_same, Pi.single_eq_same, smul_eq_mul, mul_one]
    simp only [map_one, smul_mul_assoc, one_mul]
  · simp [map_zsmul_unit, Module.Basis.repr_self, hb, Ne.symm hb]

/-- The coordinate map intertwines the matrix differential with the actual
relative Koszul differential in the tensor algebra. -/
theorem admissibleFamilyStrandCoordinates_intertwines (hE : finiteLatticeClosed n E)
    (hω : FiniteReesWeightAdmissible hE ω)
    (x : ChainFaceIndex n E m α → k[X]) :
    admissibleFamilyKoszulDifferential ω hE hω (admissibleFamilyStrandCoordinates ω (k := k) m α hE hω x).val =
      (admissibleFamilyStrandCoordinates ω m α hE hω ((admissibleChainDifferential ω m α hE).toLin' x)).val := by
  let f := (admissibleFamilyStrandTotal ω (k := k) m α hE hω).subtype.comp
    (admissibleFamilyStrandCoordinates ω m α hE hω).toLinearMap
  have hf (a : ChainFaceIndex n E m α) :
      f (Pi.basisFun k[X] _ a) = admissibleFamilyChainVector ω m α hE hω a := by
    change (admissibleFamilyStrandCoordinates ω (k := k) m α hE hω
      (Pi.basisFun k[X] _ a)).val = _
    rw [admissibleFamilyStrandCoordinates_basis, admissibleFamilyStrandBasis_val]
  have h : (admissibleFamilyKoszulDifferential ω hE hω).comp f =
      f.comp (admissibleChainDifferential ω m α hE).toLin' := by
    apply (Pi.basisFun k[X] (ChainFaceIndex n E m α)).ext
    intro a
    change admissibleFamilyKoszulDifferential ω hE hω (f (Pi.basisFun k[X] _ a)) =
      f ((admissibleChainDifferential ω m α hE).toLin' (Pi.basisFun k[X] _ a))
    rw [hf, admissibleFamilyKoszulDifferential_chainVector,
      admissibleChainDifferential_basis, map_sum]
    apply Finset.sum_congr rfl
    intro v _
    rw [LinearMap.map_smul_of_tower (R := ℤˣ) f, f.map_smul, hf]
  exact LinearMap.congr_fun h x

def admissibleFamilyStrandComplexData (hE : finiteLatticeClosed n E)
    (hω : FiniteReesWeightAdmissible hE ω) :
    FourPapers.SubmoduleComplexData k[X] (admissibleFamilyStrandTotal ω (k := k) m α hE hω) :=
  transportComplexData (admissibleChainComplexData ω m α hE hω) (admissibleFamilyStrandCoordinates ω m α hE hω)

theorem admissibleFamilyStrandComplexData_piece (hE : finiteLatticeClosed n E)
    (hω : FiniteReesWeightAdmissible hE ω) (p : ℕ) :
    (admissibleFamilyStrandComplexData ω (k := k) m α hE hω).piece p =
      basisDegreePiece (admissibleFamilyStrandBasis ω m α hE hω) (chainMatrixDegree m α) p := by
  change (Submodule.span k[X] (Pi.basisFun k[X] (ChainFaceIndex n E m α) ''
      {a | chainMatrixDegree m α a = p})).map
        (admissibleFamilyStrandCoordinates ω m α hE hω).toLinearMap = _
  rw [Submodule.map_span]
  congr 1
  rw [Set.image_image]
  apply Set.image_congr
  intro a _
  exact admissibleFamilyStrandCoordinates_basis ω m α hE hω a

theorem admissibleFamilyStrandComplexData_d (hE : finiteLatticeClosed n E)
    (hω : FiniteReesWeightAdmissible hE ω)
    (x : admissibleFamilyStrandTotal ω (k := k) m α hE hω) :
    ((admissibleFamilyStrandComplexData ω m α hE hω).d x).val = admissibleFamilyKoszulDifferential ω hE hω x.val := by
  have h := admissibleFamilyStrandCoordinates_intertwines ω m α hE hω
    ((admissibleFamilyStrandCoordinates ω (k := k) m α hE hω).symm x)
  change (admissibleFamilyStrandCoordinates ω (k := k) m α hE hω
    ((admissibleChainDifferential ω m α hE).toLin'
      ((admissibleFamilyStrandCoordinates ω m α hE hω).symm x))).val = _
  simpa only [LinearEquiv.apply_symm_apply] using h.symm

/-- The fixed fine/auxiliary strand of the actual Rees family's relative
Koszul complex is isomorphic to the constant special-fiber complex over `k[τ]`.
Both the source identification and the literal target differential are checked
above; this is the family assertion in Theorem 7.1. -/
def admissibleFamilyKoszulIso (hE : finiteLatticeClosed n E)
    (hω : FiniteReesWeightAdmissible hE ω) (hm : 0 < m) :
    (constantChainComplexData (E := E) (k := k) m α).complex ≅
      (admissibleFamilyStrandComplexData ω (k := k) m α hE hω).complex :=
  admissibleChainComplexIso ω m α hE hω hm ≪≫
    transportComplexIso (admissibleChainComplexData ω m α hE hω) (admissibleFamilyStrandCoordinates ω m α hE hω)

def admissibleFamilyKoszulHomotopyEquiv (hE : finiteLatticeClosed n E)
    (hω : FiniteReesWeightAdmissible hE ω) (hm : 0 < m) :
    HomotopyEquiv (constantChainComplexData (E := E) (k := k) m α).complex
      (admissibleFamilyStrandComplexData ω (k := k) m α hE hω).complex :=
  HomotopyEquiv.ofIso (admissibleFamilyKoszulIso ω m α hE hω hm)

def admissibleFamilyKoszulIsoAll (hE : finiteLatticeClosed n E)
    (hω : FiniteReesWeightAdmissible hE ω) :
    (constantChainComplexData (E := E) (k := k) m α).complex ≅
      (admissibleFamilyStrandComplexData ω (k := k) m α hE hω).complex :=
  admissibleChainComplexIsoAll ω m α hE hω ≪≫
    transportComplexIso (admissibleChainComplexData ω m α hE hω)
      (admissibleFamilyStrandCoordinates ω m α hE hω)


end FourPapers.Sublattice
end

#print axioms FourPapers.Sublattice.admissibleFamilyKoszulIso

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.SignedReesFamily -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace FourPapers.Sublattice
open Classical CategoryTheory CommAlg CommAlg.Koszul CommAlg.Polymatroid Polynomial
open scoped TensorProduct
universe u
variable {k : Type u} [CommRing k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

def signedStandardWeight (hE : finiteLatticeClosed n E)
    (ω : FiniteReesVariable.{u} E → ℤ) (a : finiteReesExponentMonoid.{u} E) : ℤ :=
  Finsupp.weight ω (finiteCanonicalExponent hE a)

@[simp] lemma signedStandardWeight_zero (hE : finiteLatticeClosed n E)
    (ω : FiniteReesVariable.{u} E → ℤ) : signedStandardWeight hE ω 0 = 0 := by
  simp [signedStandardWeight]

lemma positiveReesWeight_standard (hE : finiteLatticeClosed n E)
    (ω : FiniteReesVariable.{u} E → ℤ) (a : finiteReesExponentMonoid.{u} E) :
    (admissibleStandardWeight hE (positiveReesWeight ω) a : ℤ) =
      signedStandardWeight hE ω a + (positiveReesWeightShift ω : ℤ) * (a.val.degree : ℤ) := by
  unfold admissibleStandardWeight signedStandardWeight
  rw [positiveReesWeight_weight, finiteCanonicalExponent_image]

lemma positiveReesWeight_standard_defect (hE : finiteLatticeClosed n E)
    (ω : FiniteReesVariable.{u} E → ℤ) (a b : finiteReesExponentMonoid.{u} E) :
    (admissibleStandardWeight hE (positiveReesWeight ω) a : ℤ) +
        (admissibleStandardWeight hE (positiveReesWeight ω) b : ℤ) -
        (admissibleStandardWeight hE (positiveReesWeight ω) (a + b) : ℤ) =
      signedStandardWeight hE ω a + signedStandardWeight hE ω b -
        signedStandardWeight hE ω (a + b) := by
  rw [positiveReesWeight_standard, positiveReesWeight_standard, positiveReesWeight_standard]
  change _ = signedStandardWeight hE ω a + signedStandardWeight hE ω b -
    signedStandardWeight hE ω (a + b)
  simp only [AddSubmonoid.coe_add, map_add, Nat.cast_add]
  ring

lemma signedStandardWeight_subadd (hE : finiteLatticeClosed n E)
    (ω : FiniteReesVariable.{u} E → ℤ) (hω : SignedFiniteReesWeightAdmissible hE ω)
    (a b : finiteReesExponentMonoid.{u} E) :
    signedStandardWeight hE ω (a + b) ≤ signedStandardWeight hE ω a + signedStandardWeight hE ω b := by
  have h := admissibleStandardWeight_subadd hE (positiveReesWeight ω)
    (positiveReesWeight_admissible hE ω hω) a b
  have h' := positiveReesWeight_standard_defect hE ω a b
  omega

lemma positiveReesWeight_standard_defect_toNat (hE : finiteLatticeClosed n E)
    (ω : FiniteReesVariable.{u} E → ℤ) (a b : finiteReesExponentMonoid.{u} E) :
    admissibleStandardWeight hE (positiveReesWeight ω) a +
        admissibleStandardWeight hE (positiveReesWeight ω) b -
        admissibleStandardWeight hE (positiveReesWeight ω) (a + b) =
      (signedStandardWeight hE ω a + signedStandardWeight hE ω b -
        signedStandardWeight hE ω (a + b)).toNat := by
  rw [← positiveReesWeight_standard_defect hE ω a b, ← Nat.cast_add, Int.toNat_sub]

/-- The signed-weight degeneration inside a Laurent parameter algebra.
This is the original weight, before the positive homogeneous regrading. -/
def signedReesFamily (hE : finiteLatticeClosed n E)
    (ω : FiniteReesVariable.{u} E → ℤ) (hω : SignedFiniteReesWeightAdmissible hE ω) :
    Subalgebra k[X] (AddMonoidAlgebra (LaurentPolynomial k) (finiteReesExponentMonoid.{u} E)) :=
  signedWeightedMonoidAlgebra (signedStandardWeight hE ω)
    (signedStandardWeight_zero hE ω) (signedStandardWeight_subadd hE ω hω)

def signedReesFamilyBasis (hE : finiteLatticeClosed n E)
    (ω : FiniteReesVariable.{u} E → ℤ) (hω : SignedFiniteReesWeightAdmissible hE ω) :
    Module.Basis (finiteReesExponentMonoid.{u} E) k[X] (signedReesFamily (k := k) hE ω hω) :=
  signedWeightedMonoidBasis (signedStandardWeight hE ω)
    (signedStandardWeight_zero hE ω) (signedStandardWeight_subadd hE ω hω)

/-- The change of ambient monomial weights is an actual algebra isomorphism,
with equality of every multiplication coefficient. -/
def signedReesFamilyEquiv (hE : finiteLatticeClosed n E)
    (ω : FiniteReesVariable.{u} E → ℤ) (hω : SignedFiniteReesWeightAdmissible hE ω) :
    admissibleReesFamily k hE (positiveReesWeight ω) (positiveReesWeight_admissible hE ω hω) ≃ₐ[k[X]]
      signedReesFamily (k := k) hE ω hω :=
  signedWeightedAlgebraEquiv (admissibleStandardWeight hE (positiveReesWeight ω))
    (admissibleStandardWeight_zero hE _) (admissibleStandardWeight_subadd hE _
      (positiveReesWeight_admissible hE ω hω))
    (signedStandardWeight hE ω) (signedStandardWeight_zero hE ω)
    (signedStandardWeight_subadd hE ω hω) (positiveReesWeight_standard_defect_toNat hE ω)

@[simp] lemma signedReesFamilyEquiv_basis (hE : finiteLatticeClosed n E)
    (ω : FiniteReesVariable.{u} E → ℤ) (hω : SignedFiniteReesWeightAdmissible hE ω)
    (a : finiteReesExponentMonoid.{u} E) :
    signedReesFamilyEquiv (k := k) hE ω hω
      (admissibleReesFamilyBasis k hE (positiveReesWeight ω)
        (positiveReesWeight_admissible hE ω hω) a) = signedReesFamilyBasis hE ω hω a :=
  signedWeightedBasisEquiv_basis _ _ _ _ _ _ a

def signedFamilyBaseVariable (hE : finiteLatticeClosed n E)
    (ω : FiniteReesVariable.{u} E → ℤ) (hω : SignedFiniteReesWeightAdmissible hE ω)
    (v : FiniteVariable.{u} n) : signedReesFamily (k := k) hE ω hω :=
  signedReesFamilyBasis hE ω hω (familyBaseIndex (E := E) v)

abbrev SignedFamilyKoszulTensorAlgebra (hE : finiteLatticeClosed n E)
    (ω : FiniteReesVariable.{u} E → ℤ) (hω : SignedFiniteReesWeightAdmissible hE ω) :=
  signedReesFamily (k := k) hE ω hω ⊗[k[X]] Simplicial.Ambient (FiniteVariable.{u} n) k[X]

def signedFamilyTensorBasis (hE : finiteLatticeClosed n E)
    (ω : FiniteReesVariable.{u} E → ℤ) (hω : SignedFiniteReesWeightAdmissible hE ω) :
    Module.Basis (FamilyTensorIndex (E := E)) k[X] (SignedFamilyKoszulTensorAlgebra (k := k) hE ω hω) :=
  (signedReesFamilyBasis hE ω hω).tensorProduct (Simplicial.basis (k := k[X]))

def signedFamilyKoszulDifferential (hE : finiteLatticeClosed n E)
    (ω : FiniteReesVariable.{u} E → ℤ) (hω : SignedFiniteReesWeightAdmissible hE ω) :
    Module.End k[X] (SignedFamilyKoszulTensorAlgebra (k := k) hE ω hω) :=
  ∑ v : FiniteVariable.{u} n,
    TensorProduct.map (LinearMap.mulLeft k[X] (signedFamilyBaseVariable hE ω hω v))
      (Simplicial.contraction v)

def signedFamilyTensorEquiv (hE : finiteLatticeClosed n E)
    (ω : FiniteReesVariable.{u} E → ℤ) (hω : SignedFiniteReesWeightAdmissible hE ω) :
    AdmissibleFamilyKoszulTensorAlgebra (k := k) (positiveReesWeight ω) hE
        (positiveReesWeight_admissible hE ω hω) ≃ₗ[k[X]]
      SignedFamilyKoszulTensorAlgebra (k := k) hE ω hω :=
  TensorProduct.congr (signedReesFamilyEquiv hE ω hω).toLinearEquiv (LinearEquiv.refl _ _)

@[simp] lemma signedFamilyTensorEquiv_basis (hE : finiteLatticeClosed n E)
    (ω : FiniteReesVariable.{u} E → ℤ) (hω : SignedFiniteReesWeightAdmissible hE ω)
    (a : FamilyTensorIndex (E := E)) :
    signedFamilyTensorEquiv (k := k) hE ω hω
      (admissibleFamilyTensorBasis (positiveReesWeight ω) hE
        (positiveReesWeight_admissible hE ω hω) a) = signedFamilyTensorBasis hE ω hω a := by
  rcases a with ⟨a, F⟩
  simp [signedFamilyTensorEquiv, admissibleFamilyTensorBasis, signedFamilyTensorBasis,
    Module.Basis.tensorProduct_apply, signedReesFamilyEquiv_basis]

/-- Naturality is proved for the literal variable-multiplication Koszul
differentials, before any strand is transported. -/
theorem signedFamilyTensorEquiv_differential (hE : finiteLatticeClosed n E)
    (ω : FiniteReesVariable.{u} E → ℤ) (hω : SignedFiniteReesWeightAdmissible hE ω)
    (x : AdmissibleFamilyKoszulTensorAlgebra (k := k) (positiveReesWeight ω) hE
      (positiveReesWeight_admissible hE ω hω)) :
    signedFamilyTensorEquiv hE ω hω
      (admissibleFamilyKoszulDifferential (positiveReesWeight ω) hE
        (positiveReesWeight_admissible hE ω hω) x) =
      signedFamilyKoszulDifferential hE ω hω (signedFamilyTensorEquiv hE ω hω x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp only [
      (admissibleFamilyKoszulDifferential (positiveReesWeight ω) hE
        (positiveReesWeight_admissible hE ω hω)).map_zero,
      (signedFamilyTensorEquiv (k := k) hE ω hω).map_zero,
      (signedFamilyKoszulDifferential (k := k) hE ω hω).map_zero]
  | add x y hx hy =>
      simp only [
        (admissibleFamilyKoszulDifferential (positiveReesWeight ω) hE
          (positiveReesWeight_admissible hE ω hω)).map_add,
        (signedFamilyTensorEquiv (k := k) hE ω hω).map_add,
        (signedFamilyKoszulDifferential (k := k) hE ω hω).map_add, hx, hy]
  | tmul r x =>
      rw [admissibleFamilyKoszulDifferential_tmul]
      let g := fun v : FiniteVariable.{u} n =>
        (admissibleFamilyBaseVariable (positiveReesWeight ω) hE
          (positiveReesWeight_admissible hE ω hω) v * r) ⊗ₜ[k[X]] Simplicial.contraction v x
      have hs (s : Finset (FiniteVariable.{u} n)) :
          signedFamilyTensorEquiv hE ω hω (∑ v ∈ s, g v) =
            ∑ v ∈ s, signedFamilyTensorEquiv hE ω hω (g v) := by
        induction s using Finset.induction_on with
        | empty => simp only [Finset.sum_empty, (signedFamilyTensorEquiv (k := k) hE ω hω).map_zero]
        | @insert v s hv ih =>
            rw [Finset.sum_insert hv, (signedFamilyTensorEquiv (k := k) hE ω hω).map_add,
              ih, Finset.sum_insert hv]
      rw [hs Finset.univ]
      dsimp only [g]
      simp only [signedFamilyKoszulDifferential,
        LinearMap.sum_apply, TensorProduct.map_tmul, LinearMap.mulLeft_apply,
        signedFamilyTensorEquiv, TensorProduct.congr_tmul, LinearEquiv.refl_apply,
        AlgEquiv.toLinearEquiv_apply,
        (signedReesFamilyEquiv (k := k) hE ω hω).map_mul]
      apply Finset.sum_congr rfl
      intro v _
      apply congrArg (fun y : signedReesFamily (k := k) hE ω hω =>
        y ⊗ₜ[k[X]] Simplicial.contraction v x)
      calc
        _ = signedReesFamilyEquiv hE ω hω
              (admissibleFamilyBaseVariable (positiveReesWeight ω) hE
                (positiveReesWeight_admissible hE ω hω) v) *
            signedReesFamilyEquiv hE ω hω r :=
          (signedReesFamilyEquiv (k := k) hE ω hω).map_mul _ _
        _ = _ := by
          rw [admissibleFamilyBaseVariable, signedReesFamilyEquiv_basis]
          rfl

end FourPapers.Sublattice
end

#print axioms FourPapers.Sublattice.signedReesFamilyEquiv
#print axioms FourPapers.Sublattice.signedFamilyTensorEquiv_differential

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.SignedFamilyStrands -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false

noncomputable section
namespace FourPapers.Sublattice
open Classical CategoryTheory CommAlg CommAlg.Koszul CommAlg.Polymatroid Polynomial
universe u
variable {k : Type u} [CommRing k]
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}
variable (hE : finiteLatticeClosed n E) (ω : FiniteReesVariable.{u} E → ℤ)
variable (hω : SignedFiniteReesWeightAdmissible hE ω)
variable (m : ℕ) (α : Exponent (FiniteVariable.{u} n))

def signedFamilyStrandTotal :
    Submodule k[X] (SignedFamilyKoszulTensorAlgebra (k := k) hE ω hω) :=
  Submodule.span k[X] ((signedFamilyTensorBasis hE ω hω) ''
    {a | familyStrandPredicate m α a})

instance signedFamilyStrandTotalAddCommGroup :
    AddCommGroup (signedFamilyStrandTotal (k := k) hE ω hω m α) :=
  Module.addCommMonoidToAddCommGroup k[X]

lemma signedFamilyTensorEquiv_strand :
    (admissibleFamilyStrandTotal (positiveReesWeight ω) (k := k) m α hE
      (positiveReesWeight_admissible hE ω hω)).map (signedFamilyTensorEquiv hE ω hω).toLinearMap =
        signedFamilyStrandTotal (k := k) hE ω hω m α := by
  unfold admissibleFamilyStrandTotal signedFamilyStrandTotal
  rw [Submodule.map_span, Set.image_image]
  congr 1
  apply Set.image_congr
  intro a _
  exact signedFamilyTensorEquiv_basis hE ω hω a

def signedFamilyStrandEquiv :
    admissibleFamilyStrandTotal (positiveReesWeight ω) (k := k) m α hE
      (positiveReesWeight_admissible hE ω hω) ≃ₗ[k[X]]
        signedFamilyStrandTotal (k := k) hE ω hω m α :=
  (signedFamilyTensorEquiv hE ω hω).ofSubmodules _ _ (signedFamilyTensorEquiv_strand hE ω hω m α)

@[simp] lemma signedFamilyStrandEquiv_val
    (x : admissibleFamilyStrandTotal (positiveReesWeight ω) (k := k) m α hE
      (positiveReesWeight_admissible hE ω hω)) :
    (signedFamilyStrandEquiv hE ω hω m α x).val = signedFamilyTensorEquiv hE ω hω x.val := rfl

def signedFamilyStrandBasis :
    Module.Basis (ChainFaceIndex n E m α) k[X] (signedFamilyStrandTotal (k := k) hE ω hω m α) :=
  (admissibleFamilyStrandBasis (positiveReesWeight ω) m α hE
    (positiveReesWeight_admissible hE ω hω)).map (signedFamilyStrandEquiv hE ω hω m α)

lemma signedFamilyStrandBasis_val (a : ChainFaceIndex n E m α) :
    (signedFamilyStrandBasis (k := k) hE ω hω m α a).val =
      signedFamilyTensorBasis hE ω hω (familyFaceEmbedding m α hE a) := by
  rw [signedFamilyStrandBasis, Module.Basis.map_apply, signedFamilyStrandEquiv_val,
    admissibleFamilyStrandBasis_val]
  exact signedFamilyTensorEquiv_basis hE ω hω _

def signedFamilyStrandComplexData :
    FourPapers.SubmoduleComplexData k[X] (signedFamilyStrandTotal (k := k) hE ω hω m α) :=
  transportComplexData (admissibleFamilyStrandComplexData (positiveReesWeight ω) m α hE
    (positiveReesWeight_admissible hE ω hω)) (signedFamilyStrandEquiv hE ω hω m α)

/-- The transported terms are exactly the exterior-degree pieces of the
whole signed-weight fine/auxiliary strand. -/
theorem signedFamilyStrandComplexData_piece (p : ℕ) :
    (signedFamilyStrandComplexData (k := k) hE ω hω m α).piece p =
      basisDegreePiece (signedFamilyStrandBasis hE ω hω m α) (chainMatrixDegree m α) p := by
  change ((admissibleFamilyStrandComplexData (positiveReesWeight ω) m α hE
    (positiveReesWeight_admissible hE ω hω)).piece p).map
      (signedFamilyStrandEquiv hE ω hω m α).toLinearMap = _
  rw [admissibleFamilyStrandComplexData_piece]
  unfold basisDegreePiece
  rw [Submodule.map_span, Set.image_image]
  rfl

/-- The differential is the literal relative Koszul differential in the
Laurent-realized signed-weight family, not a newly stipulated differential. -/
theorem signedFamilyStrandComplexData_d
    (x : signedFamilyStrandTotal (k := k) hE ω hω m α) :
    ((signedFamilyStrandComplexData hE ω hω m α).d x).val =
      signedFamilyKoszulDifferential hE ω hω x.val := by
  change signedFamilyTensorEquiv hE ω hω
    ((admissibleFamilyStrandComplexData (positiveReesWeight ω) m α hE
      (positiveReesWeight_admissible hE ω hω)).d
      ((signedFamilyStrandEquiv hE ω hω m α).symm x)).val = _
  rw [admissibleFamilyStrandComplexData_d, signedFamilyTensorEquiv_differential]
  congr 1
  exact congrArg Subtype.val ((signedFamilyStrandEquiv hE ω hω m α).apply_symm_apply x)

/-- The family conclusion of Theorem 7.1 for every signed admissible weight,
with no positivity restriction and no restriction on the auxiliary degree. -/
def signedFamilyKoszulIsoAll :
    (constantChainComplexData (E := E) (k := k) m α).complex ≅
      (signedFamilyStrandComplexData (k := k) hE ω hω m α).complex :=
  admissibleFamilyKoszulIsoAll (positiveReesWeight ω) m α hE
      (positiveReesWeight_admissible hE ω hω) ≪≫
    transportComplexIso (admissibleFamilyStrandComplexData (positiveReesWeight ω) m α hE
      (positiveReesWeight_admissible hE ω hω)) (signedFamilyStrandEquiv hE ω hω m α)

def signedChainMatrixHomogenization (A : Matrix (ChainFaceIndex n E m α) (ChainFaceIndex n E m α) k) :
    Matrix (ChainFaceIndex n E m α) (ChainFaceIndex n E m α) k[X] :=
  fun i j => C (A i j) * X ^ (signedChainWeight ω α j.1.val - signedChainWeight ω α i.1.val).toNat

/-- Every matrix entry is unchanged by the positive homogeneous shift.
This covers both the ordinary differential and the comparison matrix. -/
theorem signedChainMatrixHomogenization_eq
    (A : Matrix (ChainFaceIndex n E m α) (ChainFaceIndex n E m α) k) :
    signedChainMatrixHomogenization ω m α A =
      WeightedMatrix.homogenize (admissibleChainMatrixWeight (positiveReesWeight ω) m α) A := by
  apply Matrix.ext
  intro i j
  unfold signedChainMatrixHomogenization WeightedMatrix.homogenize admissibleChainMatrixWeight
  rw [← positiveReesWeight_chainWeight_difference ω α j.1 i.1, Int.toNat_sub]

end FourPapers.Sublattice
end

#print axioms FourPapers.Sublattice.signedFamilyKoszulIsoAll
#print axioms FourPapers.Sublattice.signedFamilyStrandComplexData_d

end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.LiteralReesFamily -/
section

/-!
# The signed standard family is the literal Rees generator image

The additive map below is the original exponent map, with codomain
restricted to its image. The equality of subalgebras is proved from actual
canonical presentation monomials and their weight inequalities.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 800000
noncomputable section

namespace FourPapers.Sublattice
open Classical CommAlg.Polymatroid
open scoped Polynomial

universe u
variable {k : Type u} [CommRing k]
  {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

def finitePresentedHom (E : Finset (FiniteTuple n)) :
    (FiniteReesVariable.{u} E →₀ ℕ) →+ finiteReesExponentMonoid.{u} E where
  toFun := familyPresentedIndex
  map_zero' := Subtype.ext (map_zero (finiteReesExponentMap E))
  map_add' c e := Subtype.ext (map_add (finiteReesExponentMap E) c e)

theorem finitePresentedHom_canonical (hE : finiteLatticeClosed n E)
    (a : finiteReesExponentMonoid.{u} E) :
    finitePresentedHom E (finiteCanonicalExponent hE a) = a :=
  Subtype.ext (finiteCanonicalExponent_image hE a)

theorem finiteCanonicalExponent_presented_normal (hE : finiteLatticeClosed n E)
    (c : FiniteReesVariable.{u} E →₀ ℕ) :
    finiteCanonicalExponent hE (finitePresentedHom E c) = finiteReesNormalForm hE c := by
  apply finiteReesStandard_image_injective hE
    (finiteCanonicalExponent_standard hE _) (finiteReesNormalForm_standard hE c)
  rw [finiteCanonicalExponent_image, finiteReesNormalForm_image]
  rfl

/-- Normal reduction decreases every admissible signed weight. Positivity
is removed by the proved homogeneous shift, so no lower bound is assumed
on the original presentation weights. -/
theorem signedNormalWeight_le (hE : finiteLatticeClosed n E)
    (ω : FiniteReesVariable.{u} E → ℤ) (hω : SignedFiniteReesWeightAdmissible hE ω)
    (c : FiniteReesVariable.{u} E →₀ ℕ) :
    Finsupp.weight ω (finiteCanonicalExponent hE (finitePresentedHom E c)) ≤
      Finsupp.weight ω c := by
  rw [finiteCanonicalExponent_presented_normal]
  have h := finiteReesNormalForm_admissible_weight_le hE (positiveReesWeight ω)
    (positiveReesWeight_admissible hE ω hω) c
  have h' := positiveReesWeight_difference ω (finiteReesNormalForm hE c) c
    (finiteReesNormalForm_image hE c)
  omega

/-- The original presentation variables, with their assigned signed
parameter weights, generate exactly the subalgebra used by the integral
chain comparison. This is equality inside the common Laurent monoid
algebra, not merely an abstract module equivalence. -/
theorem literalReesFamily_eq_signedReesFamily (hE : finiteLatticeClosed n E)
    (ω : FiniteReesVariable.{u} E → ℤ) (hω : SignedFiniteReesWeightAdmissible hE ω) :
    LiteralWeightFamily.family (k := k) (finitePresentedHom E) ω =
      signedReesFamily (k := k) hE ω hω := by
  exact LiteralWeightFamily.family_eq_normalSpan (finitePresentedHom E) ω
    (finiteCanonicalExponent hE) (finitePresentedHom_canonical hE)
    (signedNormalWeight_le hE ω hω)
    (signedStandardWeight_zero hE ω) (signedStandardWeight_subadd hE ω hω)

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.literalReesFamily_eq_signedReesFamily


end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.FiniteReesInitialIdeal -/
section

/-!
# The displayed monomial special fiber forces admissible weights

The ideal below is generated by the sorting heads and the predecessor
heads of Proposition 2.2. Its standard monomials are proved to be exactly
the chain monomials with admissible coefficients. Each displayed relation
has a standard tail. Consequently equality with the signed-weight initial ideal of the Rees
presentation kernel forces the strict weight inequalities used by Theorem
7.1.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
noncomputable section

namespace FourPapers.Sublattice

open Classical MvPolynomial CommAlg.Polymatroid
universe u
variable {d : ℕ} {n : Fin d → ℕ} {E : Finset (FiniteTuple n)}

def finiteReesInitialHeads (E : Finset (FiniteTuple n)) :
    Set (FiniteReesVariable.{u} E →₀ ℕ) :=
  {c | (∃ a b : E, ¬a.val ≤ b.val ∧ ¬b.val ≤ a.val ∧
      c = finiteSortingHeadExponent a b) ∨
    (∃ b a : E, b.val ≤ a.val ∧ b.val ≠ a.val ∧
      c = finiteCoefficientHeadExponent b a)}

def finiteReesInitialIdeal (k : Type*) [CommRing k]
    (E : Finset (FiniteTuple n)) : Ideal (MvPolynomial (FiniteReesVariable.{u} E) k) :=
  Ideal.span ((fun c => MvPolynomial.monomial c (1 : k)) '' finiteReesInitialHeads E)

theorem finiteSortingHead_le_iff {a b : E} (hne : a ≠ b)
    (c : FiniteReesVariable.{u} E →₀ ℕ) :
    finiteSortingHeadExponent a b ≤ c ↔
      finiteFactorPart c a ≠ 0 ∧ finiteFactorPart c b ≠ 0 := by
  rw [← Finsupp.embDomain_le_embDomain_iff_le (finiteReesVariableEmbedding E),
    finiteSortingHeadExponent_embedding,
    sortingHeadExponent_le_iff ((finiteTupleImageEquiv E).injective.ne hne),
    finiteFactorPart_embedding_apply, finiteFactorPart_embedding_apply]

theorem finiteCoefficientHead_le_iff {b a : E} (hba : b.val ≤ a.val)
    (c : FiniteReesVariable.{u} E →₀ ℕ) :
    finiteCoefficientHeadExponent b a ≤ c ↔
      finiteFactorPart c a ≠ 0 ∧
        finiteRowExponent n b.val - finiteRowExponent n a.val ≤ finiteCoefficientPart c := by
  rw [← Finsupp.embDomain_le_embDomain_iff_le (finiteReesVariableEmbedding E),
    finiteCoefficientHeadExponent_embedding, coefficientHeadExponent_le_iff hba,
    finiteFactorPart_embedding_apply, finiteCoefficientPart_embedding]
  change (finiteFactorPart c a ≠ 0 ∧
      ∀ x ∈ ratio (finiteTupleToNat b.val) (finiteTupleToNat a.val),
        0 < (finiteCoefficientPart c).embDomain finiteVariableEmbedding x) ↔ _
  rw [← finiteRatio_divides_iff hba]

/-- Exact agreement with the literal displayed monomial generators. -/
theorem finiteReesStandard_iff_noInitialHead (c : FiniteReesVariable.{u} E →₀ ℕ) :
    FiniteReesStandard c ↔ ¬∃ g ∈ finiteReesInitialHeads E, g ≤ c := by
  rw [finiteReesStandard_iff]
  constructor
  · rintro ⟨hchain,hcoeff⟩ ⟨g,hg,hgc⟩
    rcases hg with ⟨a,b,hab,hba,rfl⟩ | ⟨b,a,hba,hne,rfl⟩
    · have hne : a ≠ b := fun h => hab (h ▸ le_rfl)
      obtain ⟨ha,hb⟩ := (finiteSortingHead_le_iff hne c).mp hgc
      exact (hchain a b ha hb).elim hab hba
    · obtain ⟨ha,hdiv⟩ := (finiteCoefficientHead_le_iff hba c).mp hgc
      apply hcoeff a ha
      exact ⟨finiteRowExponent n b.val - finiteRowExponent n a.val,
        Finset.mem_image.mpr ⟨b.val,Finset.mem_filter.mpr ⟨b.property,hba,hne⟩,rfl⟩,hdiv⟩
  · intro h
    constructor
    · intro a b ha hb
      by_contra hn
      push_neg at hn
      have hne : a ≠ b := fun he => hn.1 (by simpa only [he] using (le_refl b.val))
      exact h ⟨finiteSortingHeadExponent a b,Or.inl ⟨a,b,hn.1,hn.2,rfl⟩,
        (finiteSortingHead_le_iff hne c).mpr ⟨ha,hb⟩⟩
    · intro a ha ⟨g,hg,hgc⟩
      obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hg
      obtain ⟨hbE,hba,hne⟩ := Finset.mem_filter.mp hb
      exact h ⟨finiteCoefficientHeadExponent ⟨b,hbE⟩ a,
        Or.inr ⟨⟨b,hbE⟩,a,hba,hne,rfl⟩,
        (finiteCoefficientHead_le_iff hba c).mpr ⟨ha,hgc⟩⟩

theorem finiteReesInitialIdeal_monomial_iff {k : Type*} [CommRing k] [Nontrivial k]
    (c : FiniteReesVariable.{u} E →₀ ℕ) :
    MvPolynomial.monomial c (1 : k) ∈ finiteReesInitialIdeal k E ↔ ¬FiniteReesStandard c := by
  rw [finiteReesInitialIdeal, MvPolynomial.mem_ideal_span_monomial_image]
  simp only [MvPolynomial.support_monomial, one_ne_zero, if_false,
    Finset.mem_singleton, forall_eq]
  simpa only [not_not] using (not_congr (finiteReesStandard_iff_noInitialHead c)).symm

theorem finiteHighCoefficient_allowed (a : FiniteTuple n)
    (v : Exponent (FiniteVariable.{u} n))
    (hv : ∀ r j, j < a r → v ⟨r,ULift.up j⟩ = 0) :
    ¬Contains (finiteCoordinatePredecessorFamily E a) v := by
  rintro ⟨g,hg,hgv⟩
  obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hg
  obtain ⟨hbE,hba,hne⟩ := Finset.mem_filter.mp hb
  have hr : ∃ r, b r ≠ a r := by
    by_contra h
    push_neg at h
    exact hne (funext h)
  obtain ⟨r,hr⟩ := hr
  have hlt : b r < a r := lt_of_le_of_ne (hba r) hr
  have hratio : (finiteRowExponent n b - finiteRowExponent n a)
      ⟨r,ULift.up (b r)⟩ = 1 := by
    simp only [Finsupp.tsub_apply, finiteRowExponent_apply, if_pos rfl,
      if_neg hr.symm, Nat.sub_zero, if_true]
  have h := hgv ⟨r,ULift.up (b r)⟩
  rw [hratio, hv r (b r) hlt] at h
  exact Nat.not_succ_le_zero 0 h

lemma finiteFactorPart_sorting (a b t : E) :
    finiteFactorPart (finiteSortingHeadExponent.{u} a b) t =
      (if a = t then 1 else 0) + (if b = t then 1 else 0) := by
  simp [finiteFactorPart,finiteSortingHeadExponent,Finsupp.comapDomain_apply,
    Finsupp.single_apply]

lemma finiteCoefficientPart_sorting (a b : E) :
    finiteCoefficientPart (finiteSortingHeadExponent.{u} a b) = 0 := by
  ext x
  simp [finiteCoefficientPart,finiteSortingHeadExponent,Finsupp.comapDomain_apply,
    Finsupp.single_apply]

lemma finiteFactorPart_coefficient (b a : E) :
    finiteFactorPart (finiteCoefficientHeadExponent.{u} b a) = Finsupp.single a 1 := by
  ext t
  simp [finiteFactorPart,finiteCoefficientHeadExponent,Finsupp.comapDomain_apply,
    Finsupp.embDomain_inl,Finsupp.sumElim_apply,Finsupp.single_apply]

lemma finiteCoefficientPart_coefficient (b a : E) :
    finiteCoefficientPart (finiteCoefficientHeadExponent.{u} b a) =
      finiteRowExponent n b.val - finiteRowExponent n a.val := by
  ext x
  simp [finiteCoefficientPart,finiteCoefficientHeadExponent,Finsupp.comapDomain_apply,
    Finsupp.embDomain_inl,Finsupp.sumElim_apply,Finsupp.single_apply]

theorem finiteSortingHead_standard_of_le (a b : E) (hab : a.val ≤ b.val) :
    FiniteReesStandard (finiteSortingHeadExponent.{u} a b) := by
  rw [finiteReesStandard_iff]
  have hs (t : E) (ht : finiteFactorPart (finiteSortingHeadExponent.{u} a b) t ≠ 0) :
      t = a ∨ t = b := by
    by_contra h
    push_neg at h
    rw [finiteFactorPart_sorting] at ht
    simp only [Ne.symm h.1,Ne.symm h.2,if_false,zero_add,ne_eq,not_true_eq_false] at ht
  constructor
  · intro c e hc he
    rcases hs c hc with rfl | rfl <;> rcases hs e he with rfl | rfl
    · exact Or.inl le_rfl
    · exact Or.inl hab
    · exact Or.inr hab
    · exact Or.inl le_rfl
  · intro t ht
    rw [finiteCoefficientPart_sorting]
    exact finiteHighCoefficient_allowed t.val 0 (fun _ _ _ => rfl)

theorem finiteSortingTail_standard (hE : finiteLatticeClosed n E) (a b : E) :
    FiniteReesStandard (finiteSortingTailExponent.{u} hE a b) :=
  finiteSortingHead_standard_of_le
    ⟨a.val ⊓ b.val,hE.1 a.val a.property b.val b.property⟩
    ⟨a.val ⊔ b.val,hE.2 a.val a.property b.val b.property⟩
    (inf_le_left.trans le_sup_left)

theorem finiteCoefficientTail_standard {b a : E} (hba : b.val ≤ a.val) :
    FiniteReesStandard (finiteCoefficientHeadExponent.{u} a b) := by
  rw [finiteReesStandard_iff,finiteFactorPart_coefficient,
    finiteCoefficientPart_coefficient]
  have hs (t : E) (ht : Finsupp.single b 1 t ≠ (0 : ℕ)) : t = b := by
    by_contra h
    exact ht (Finsupp.single_eq_of_ne h)
  constructor
  · intro c e hc he
    rw [hs c hc,hs e he]
    exact Or.inl le_rfl
  · intro t ht
    rw [hs t ht]
    apply finiteHighCoefficient_allowed
    intro r j hj
    have hbj : b.val r ≠ j := ne_of_gt hj
    have haj : a.val r ≠ j := ne_of_gt (hj.trans_le (hba r))
    simp only [Finsupp.tsub_apply,finiteRowExponent_apply,if_neg hbj,if_neg haj,Nat.sub_self]

/-- The paper's literal signed-weight initial-ideal hypothesis on the
kernel of its polynomial Rees presentation implies admissibility. -/
theorem signedAdmissible_of_weightInitialIdeal
    (hE : finiteLatticeClosed n E) (ω : FiniteReesVariable.{u} E → ℤ)
    (hB : SignedWeightInitial.initialIdeal ω
      (RingHom.ker (finiteReesPresentationMap E ℤ).toRingHom) = finiteReesInitialIdeal ℤ E) :
    SignedFiniteReesWeightAdmissible hE ω := by
  have hrel (c e : FiniteReesVariable.{u} E →₀ ℕ)
      (hce : finiteReesExponentMap E c = finiteReesExponentMap E e) :
      MvPolynomial.monomial c (1 : ℤ) - MvPolynomial.monomial e 1 ∈
        RingHom.ker (finiteReesPresentationMap E ℤ).toRingHom := by
    change (finiteReesPresentationMap E ℤ).toRingHom
      (MvPolynomial.monomial c (1 : ℤ) - MvPolynomial.monomial e 1) = 0
    rw [(finiteReesPresentationMap E ℤ).toRingHom.map_sub]
    change AddMonoidAlgebra.mapDomain (finiteReesExponentMap E)
      (AddMonoidAlgebra.single c (1 : ℤ)) -
      AddMonoidAlgebra.mapDomain (finiteReesExponentMap E)
        (AddMonoidAlgebra.single e (1 : ℤ)) = 0
    rw [AddMonoidAlgebra.mapDomain_single, AddMonoidAlgebra.mapDomain_single,hce,sub_self]
  constructor
  · intro a b hab hba
    apply SignedWeightInitial.binomial_weight_strict ω _ _ hB
      (hrel _ _ (finiteSorting_exponent_images hE a b))
    · exact Ideal.subset_span ⟨finiteSortingHeadExponent a b,
        Or.inl ⟨a,b,hab,hba,rfl⟩,rfl⟩
    · rw [finiteReesInitialIdeal_monomial_iff]
      exact not_not.mpr (finiteSortingTail_standard hE a b)
  · intro b a hba hne
    apply SignedWeightInitial.binomial_weight_strict ω _ _ hB
      (hrel _ _ (finiteCoefficient_exponent_images b a))
    · exact Ideal.subset_span ⟨finiteCoefficientHeadExponent b a,
        Or.inr ⟨b,a,hba,hne,rfl⟩,rfl⟩
    · rw [finiteReesInitialIdeal_monomial_iff]
      exact not_not.mpr (finiteCoefficientTail_standard hba)

end FourPapers.Sublattice

#print axioms FourPapers.Sublattice.finiteReesStandard_iff_noInitialHead
#print axioms FourPapers.Sublattice.signedAdmissible_of_weightInitialIdeal


end
end
end

/- BEGIN EXACT BODY: FourPapers.Sublattice.SquarefreeAlexanderDuality -/
section

/-!
# Integral Alexander duality in the actual squarefree Koszul strand

The full positive fine Koszul strand has the explicit exterior-creation
contraction. Its ideal subcomplex and quotient complex therefore have
homology shifted by one. At the full squarefree degree the ideal faces
are exactly the Alexander dual of the Stanley--Reisner faces.

This constructs the relevant integral comparison directly on signed
chains. It does not replace integral cohomology by homology of the same
complex, and so retains the torsion placement in Lemma 10.1.

`AugmentedFaceHomology P p` uses faces with cardinality p. Its usual
reduced simplicial degree is p-1. Thus the final equivalence identifies
Koszul degree p+1 with reduced Alexander-dual homology degree p-1.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 900000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.Sublattice
open Classical CategoryTheory CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

/-- Equality of the actual quotient face predicates transports the whole
homogeneous complex, preserving each exterior degree. -/
def quotientHomogeneousIsoOfFaces (B C : Family V) (α β : Exponent V)
    (h : quotientKoszulFaces B α = quotientKoszulFaces C β) :
    quotientHomogeneousComplex (k := k) B α ≅ quotientHomogeneousComplex (k := k) C β := by
  let f : TotalFaceModule (k := k) (quotientKoszulFaces B α) ≃ₗ[k]
      TotalFaceModule (k := k) (quotientKoszulFaces C β) :=
    { toFun x := ⟨x.val,by simpa only [← h] using x.property⟩
      invFun x := ⟨x.val,by simpa only [h] using x.property⟩
      left_inv _ := rfl
      right_inv _ := rfl
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  let e := (quotientTotalData (k := k) B α).isoOfTotal (quotientTotalData C β) f
    (by
      intro i x hx
      change x.val ∈ Simplicial.Chains (quotientKoszulFaces B α) i at hx
      change x.val ∈ Simplicial.Chains (quotientKoszulFaces C β) i
      simpa only [h] using hx)
    (by
      intro i x hx
      change x.val ∈ Simplicial.Chains (quotientKoszulFaces C β) i at hx
      change x.val ∈ Simplicial.Chains (quotientKoszulFaces B α) i
      simpa only [h] using hx)
    (by
      apply LinearMap.ext
      intro x
      apply Subtype.ext
      change quotientFaceProjection C β (Simplicial.boundary x.val) =
        quotientFaceProjection B α (Simplicial.boundary x.val)
      simp only [quotientFaceProjection_eq_faceProjection,h])
  exact (quotientTotalKoszulIso B α).symm ≪≫ e ≪≫ quotientTotalKoszulIso C β

def quotientHomologyEquivOfContains (B C : Family V) (α : Exponent V)
    (h : ∀ v,Contains B v ↔ Contains C v) (p : ℕ) :
    (quotientHomogeneousComplex (k := k) B α).homology p ≃ₗ[k]
      (quotientHomogeneousComplex (k := k) C α).homology p :=
  ((HomologicalComplex.homologyFunctor (ModuleCat.{u} k) (ComplexShape.down ℕ) p).mapIso
    (quotientHomogeneousIsoOfFaces B C α α (quotientKoszulFaces_eq_of_contains h α))).toLinearEquiv

def augmentedFaceCycles (P : Finset V → Prop) (p : ℕ) :
    Submodule k (Simplicial.Ambient V k) :=
  Simplicial.Chains P p ⊓ LinearMap.ker Simplicial.boundary

def augmentedFaceBoundary (P : Finset V → Prop) (hP : Simplicial.Downward P) (p : ℕ) :
    Simplicial.Chains (k := k) P (p+1) →ₗ[k] augmentedFaceCycles (k := k) P p :=
  (Simplicial.boundary.domRestrict (Simplicial.Chains P (p+1))).codRestrict _
    (fun x => ⟨Simplicial.boundary_mem hP x.property,
      Simplicial.boundary_boundary x.val⟩)

abbrev AugmentedFaceHomology (P : Finset V → Prop) (hP : Simplicial.Downward P) (p : ℕ) : Type u :=
  augmentedFaceCycles (k := k) P p ⧸ LinearMap.range (augmentedFaceBoundary (k := k) P hP p)

/-- Equality of face predicates identifies the literal augmented cycle/boundary
quotients. The downward-closure proofs are equal by proof irrelevance. -/
def augmentedFaceHomologyEquivOfFaces (P Q : Finset V → Prop)
    (hP : Simplicial.Downward P) (hQ : Simplicial.Downward Q)
    (h : P = Q) (p : ℕ) :
    AugmentedFaceHomology (k := k) P hP p ≃ₗ[k]
      AugmentedFaceHomology (k := k) Q hQ p := by
  subst Q
  exact LinearEquiv.refl k _

/-- Take the unprojected boundary of an actual quotient cycle. -/
def quotientIdealConnectingCycle (B : Family V) (α : Exponent V) (p : ℕ) :
    ClosedGraphDegreeCycles (k := k) B α (p+1) →ₗ[k]
      augmentedFaceCycles (k := k) (koszulFaces B α) p where
  toFun z := ⟨Simplicial.boundary z.val.val, by
    have hzfull : z.val.val ∈ Simplicial.Chains (fullKoszulFaces α) (p+1) :=
      Simplicial.chains_mono (fun _ hs => hs.1) (p+1) z.property.2
    exact ⟨quotientFaceProjection_zero_mem_ideal_degree B α p
      (Simplicial.boundary_mem (fullKoszulFaces_downward α) hzfull)
      (congrArg Subtype.val z.property.1), Simplicial.boundary_boundary z.val.val⟩⟩
  map_add' x y := Subtype.ext (map_add Simplicial.boundary x.val.val y.val.val)
  map_smul' r x := Subtype.ext (map_smul Simplicial.boundary r x.val.val)

theorem quotientIdealConnectingCycle_boundary (B : Family V) (α : Exponent V) (p : ℕ)
    (y : totalFacePiece (k := k) (quotientKoszulFaces B α) (p+2)) :
    quotientIdealConnectingCycle B α p (closedGraphDegreeBoundary B α (p+1) y) ∈
      LinearMap.range (augmentedFaceBoundary (k := k) (koszulFaces B α) (koszulFaces_downward B α) p) := by
  have hyfull : y.val.val ∈ Simplicial.Chains (fullKoszulFaces α) (p+2) :=
    Simplicial.chains_mono (fun _ hs => hs.1) (p+2) y.property
  have hdy := Simplicial.boundary_mem (fullKoszulFaces_downward α) hyfull
  refine ⟨⟨quotientFaceProjection B α (Simplicial.boundary y.val.val) -
      Simplicial.boundary y.val.val,
    quotientFaceProjection_sub_mem_ideal_degree B α (p+1) hdy⟩, ?_⟩
  apply Subtype.ext
  change Simplicial.boundary (quotientFaceProjection B α (Simplicial.boundary y.val.val) -
      Simplicial.boundary y.val.val) =
    Simplicial.boundary (quotientFaceProjection B α (Simplicial.boundary y.val.val))
  rw [map_sub, Simplicial.boundary_boundary, sub_zero]

def quotientIdealConnectingHomology (B : Family V) (α : Exponent V) (p : ℕ) :
    ClosedGraphDegreeHomology (k := k) B α (p+1) →ₗ[k]
      AugmentedFaceHomology (k := k) (koszulFaces B α) (koszulFaces_downward B α) p :=
  (LinearMap.range (closedGraphDegreeBoundary B α (p+1))).liftQ
    (((LinearMap.range (augmentedFaceBoundary (k := k) (koszulFaces B α)
      (koszulFaces_downward B α) p)).mkQ).comp (quotientIdealConnectingCycle B α p)) (by
        rintro x ⟨y,rfl⟩
        exact (Submodule.Quotient.mk_eq_zero _).mpr
          (quotientIdealConnectingCycle_boundary B α p y))

theorem quotientIdealConnectingHomology_injective
    (B : Family V) (α : Exponent V) (e : V) (he : 0 < α e) (p : ℕ) :
    Function.Injective (quotientIdealConnectingHomology (k := k) B α p) := by
  apply (LinearMap.ker_eq_bot).mp
  apply (Submodule.eq_bot_iff _).mpr
  intro x hx
  obtain ⟨z,rfl⟩ := (LinearMap.range (closedGraphDegreeBoundary B α (p+1))).mkQ_surjective x
  obtain ⟨a,ha⟩ := (Submodule.Quotient.mk_eq_zero _).mp hx
  have had : Simplicial.boundary a.val = Simplicial.boundary z.val.val :=
    congrArg Subtype.val ha
  have hzfull : z.val.val ∈ Simplicial.Chains (fullKoszulFaces α) (p+1) :=
    Simplicial.chains_mono (fun _ hs => hs.1) (p+1) z.property.2
  have hafull : a.val ∈ Simplicial.Chains (fullKoszulFaces α) (p+1) :=
    Simplicial.chains_mono (fun _ hs => hs.1) (p+1) a.property
  have hw : z.val.val-a.val ∈ Simplicial.Chains (fullKoszulFaces α) (p+1) :=
    Submodule.sub_mem _ hzfull hafull
  have hdw : Simplicial.boundary (z.val.val-a.val) = 0 := by
    rw [map_sub,had,sub_self]
  have hc := creation_mem_chains e (fun _ hF => fullKoszulFaces_insert he hF) hw
  let y : TotalFaceModule (k := k) (quotientKoszulFaces B α) :=
    ⟨quotientFaceProjection B α (Simplicial.creation e (z.val.val-a.val)),
      relativeProjection_mem _ _ _ _⟩
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨⟨y,quotientFaceProjection_degree B α (p+2) hc⟩,?_⟩
  apply Subtype.ext
  apply Subtype.ext
  change quotientFaceProjection B α (Simplicial.boundary
      (quotientFaceProjection B α (Simplicial.creation e (z.val.val-a.val)))) = z.val.val
  rw [quotientFaceProjection_boundary B α (chains_mem_basisSpan hc),
    Simplicial.boundary_creation,hdw,map_zero,sub_zero,map_sub,
    quotientFaceProjection_zero_on_ideal B α (chains_mem_basisSpan a.property),sub_zero]
  exact relativeProjection_eq_self z.val.property

theorem quotientIdealConnectingHomology_surjective
    (B : Family V) (α : Exponent V) (e : V) (he : 0 < α e) (p : ℕ) :
    Function.Surjective (quotientIdealConnectingHomology (k := k) B α p) := by
  intro x
  obtain ⟨z,rfl⟩ := (LinearMap.range
    (augmentedFaceBoundary (k := k) (koszulFaces B α) (koszulFaces_downward B α) p)).mkQ_surjective x
  have hzfull : z.val ∈ Simplicial.Chains (fullKoszulFaces α) p :=
    Simplicial.chains_mono (fun _ hs => hs.1) p z.property.1
  let f := Simplicial.creation e z.val
  have hf : f ∈ Simplicial.Chains (fullKoszulFaces α) (p+1) :=
    creation_mem_chains e (fun _ hF => fullKoszulFaces_insert he hF) hzfull
  have hdf : Simplicial.boundary f = z.val := by
    dsimp only [f]
    rw [Simplicial.boundary_creation,z.property.2,map_zero,sub_zero]
  let q : TotalFaceModule (k := k) (quotientKoszulFaces B α) :=
    ⟨quotientFaceProjection B α f,relativeProjection_mem _ _ _ _⟩
  have hq : quotientTotalDifferential B α q = 0 := by
    apply Subtype.ext
    change quotientFaceProjection B α (Simplicial.boundary (quotientFaceProjection B α f)) = 0
    rw [quotientFaceProjection_boundary B α (chains_mem_basisSpan hf),hdf]
    exact quotientFaceProjection_zero_on_ideal B α (chains_mem_basisSpan z.property.1)
  let c : ClosedGraphDegreeCycles (k := k) B α (p+1) :=
    ⟨q,hq,quotientFaceProjection_degree B α (p+1) hf⟩
  refine ⟨Submodule.Quotient.mk c,?_⟩
  apply (Submodule.Quotient.eq _).mpr
  refine ⟨⟨quotientFaceProjection B α f-f,
    quotientFaceProjection_sub_mem_ideal_degree B α (p+1) hf⟩,?_⟩
  apply Subtype.ext
  change Simplicial.boundary (quotientFaceProjection B α f-f) =
    Simplicial.boundary (quotientFaceProjection B α f)-z.val
  rw [map_sub,hdf]

/-- The actual connecting isomorphism in every nonzero fine degree,
over an arbitrary commutative coefficient ring. -/
def quotientIdealConnectingEquiv
    (B : Family V) (α : Exponent V) (e : V) (he : 0 < α e) (p : ℕ) :
    ClosedGraphDegreeHomology (k := k) B α (p+1) ≃ₗ[k]
      AugmentedFaceHomology (k := k) (koszulFaces B α) (koszulFaces_downward B α) p :=
  LinearEquiv.ofBijective (quotientIdealConnectingHomology B α p)
    ⟨quotientIdealConnectingHomology_injective B α e he p,
      quotientIdealConnectingHomology_surjective B α e he p⟩

/-- The actual Stanley--Reisner faces on the full variable set. -/
def stanleyReisnerFaces (B : Family V) (F : Finset V) : Prop :=
  ¬Contains B (faceExponent F)

def alexanderDualFaces (B : Family V) (F : Finset V) : Prop :=
  ¬stanleyReisnerFaces B (Finset.univ \ F)

theorem faceExponent_le_faceExponent_iff (A B : Finset V) :
    faceExponent A ≤ faceExponent B ↔ A ⊆ B := by
  constructor
  · intro h v hv
    by_contra hb
    have hh := h v
    simp [faceExponent_apply,hv,hb] at hh
  · exact faceExponent_mono

theorem squarefree_sub_face (S F : Finset V) :
    faceExponent S - faceExponent F = faceExponent (S \ F) := by
  ext v
  by_cases hs : v ∈ S <;> by_cases hv : v ∈ F <;>
    simp [faceExponent_apply,hs,hv]

theorem fullSquarefree_sub_face (F : Finset V) :
    faceExponent (Finset.univ : Finset V) - faceExponent F =
      faceExponent (Finset.univ \ F) := by
  ext v
  by_cases hv : v ∈ F <;> simp [faceExponent_apply,hv]

/-- Alexander duality relative to the actual support S, so variables of
fine exponent zero are not silently added to the vertex set. -/
def supportedAlexanderDualFaces (B : Family V) (S F : Finset V) : Prop :=
  F ⊆ S ∧ ¬stanleyReisnerFaces B (S \ F)

theorem koszulFaces_squarefreeSupport (B : Family V) (S : Finset V) :
    koszulFaces B (faceExponent S) = supportedAlexanderDualFaces B S := by
  funext F
  apply propext
  simp only [koszulFaces,faceExponent_le_faceExponent_iff,squarefree_sub_face,
    supportedAlexanderDualFaces,stanleyReisnerFaces,not_not]

theorem supportedAlexanderDualFaces_downward (B : Family V) (S : Finset V) :
    Simplicial.Downward (supportedAlexanderDualFaces B S) := by
  rw [← koszulFaces_squarefreeSupport]
  exact koszulFaces_downward B _

def supportedSquarefreeAlexanderDuality (B : Family V) (S : Finset V)
    (e : V) (he : e ∈ S) (p : ℕ) :
    (quotientHomogeneousComplex (k := k) B (faceExponent S)).homology (p+1) ≃ₗ[k]
      AugmentedFaceHomology (k := k) (supportedAlexanderDualFaces B S)
        (supportedAlexanderDualFaces_downward B S) p := by
  have he' : 0 < faceExponent S e := by simp [faceExponent_apply,he]
  have E := (quotientCategoricalDegreeHomologyEquiv (k := k) B (faceExponent S) (p+1)).trans
    (quotientIdealConnectingEquiv (k := k) B (faceExponent S) e he' p)
  exact E.trans (augmentedFaceHomologyEquivOfFaces (k := k)
    (koszulFaces B (faceExponent S)) (supportedAlexanderDualFaces B S)
    (koszulFaces_downward B (faceExponent S)) (supportedAlexanderDualFaces_downward B S)
    (koszulFaces_squarefreeSupport B S) p)

theorem koszulFaces_fullSquarefree (B : Family V) :
    koszulFaces B (faceExponent (Finset.univ : Finset V)) = alexanderDualFaces B := by
  funext F
  apply propext
  have hF : faceExponent F ≤ faceExponent (Finset.univ : Finset V) :=
    faceExponent_mono (Finset.subset_univ F)
  simp only [koszulFaces,hF,true_and,fullSquarefree_sub_face,
    alexanderDualFaces,stanleyReisnerFaces,not_not]

theorem alexanderDualFaces_downward (B : Family V) : Simplicial.Downward (alexanderDualFaces B) := by
  rw [← koszulFaces_fullSquarefree]
  exact koszulFaces_downward B _

/-- Integral combinatorial Alexander duality in the exact convention
needed by Lemma 10.1. The right side is reduced degree p-1, while the
left side is genuine fine Koszul degree p+1. -/
def squarefreeAlexanderDuality (B : Family V) (e : V) (p : ℕ) :
    (quotientHomogeneousComplex (k := k) B (faceExponent (Finset.univ : Finset V))).homology (p+1) ≃ₗ[k]
      AugmentedFaceHomology (k := k) (alexanderDualFaces B) (alexanderDualFaces_downward B) p := by
  have he : 0 < faceExponent (Finset.univ : Finset V) e := by simp [faceExponent_apply]
  have E := (quotientCategoricalDegreeHomologyEquiv (k := k) B (faceExponent Finset.univ) (p+1)).trans
    (quotientIdealConnectingEquiv (k := k) B (faceExponent Finset.univ) e he p)
  exact E.trans (augmentedFaceHomologyEquivOfFaces (k := k)
    (koszulFaces B (faceExponent (Finset.univ : Finset V))) (alexanderDualFaces B)
    (koszulFaces_downward B (faceExponent Finset.univ)) (alexanderDualFaces_downward B)
    (koszulFaces_fullSquarefree B) p)

/-- Degree zero of the nonzero squarefree quotient strand vanishes; no
spurious reduced degree minus two group is inserted into the comparison. -/
theorem squarefreeQuotientHomology_zero (B : Family V) (e : V) :
    Subsingleton (ClosedGraphDegreeHomology (k := k) B (faceExponent Finset.univ) 0) := by
  constructor
  intro x y
  obtain ⟨z,rfl⟩ := (LinearMap.range (closedGraphDegreeBoundary B (faceExponent Finset.univ) 0)).mkQ_surjective x
  obtain ⟨w,rfl⟩ := (LinearMap.range (closedGraphDegreeBoundary B (faceExponent Finset.univ) 0)).mkQ_surjective y
  apply (Submodule.Quotient.eq _).mpr
  obtain ⟨a,ha,hda⟩ := quotientCycle_boundary_degree_zero B (faceExponent Finset.univ) e
    (by simp [faceExponent_apply]) (z.val-w.val) (Submodule.sub_mem _ z.property.2 w.property.2)
  exact ⟨⟨a,ha⟩,Subtype.ext hda⟩

end FourPapers.Sublattice
end

end
end


end
