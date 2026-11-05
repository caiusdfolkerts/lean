module

public import PaperVerification.AlternatingFormsOddIntegralBaseChange
public import PaperVerification.AlternatingFormsExteriorTransport
public import Mathlib.LinearAlgebra.Basis.SMul
public import Mathlib.Algebra.MonoidAlgebra.Basic

/-!
# Independent invertible coefficients on every edge of the odd path

Successive diagonal factors solve `dᵢ*dᵢ₊₁=cᵢ` in the unit group of an
arbitrary commutative ring.  The resulting actual exterior automorphism
identifies the unweighted and weighted generated ideals.  Rescaling each
transported basis vector by its explicitly computed unit leaves the
literal good exterior words as a basis.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators

namespace PaperVerification.AlternatingForms.IntegralOdd

variable (R : Type*) [CommRing R] {k s : ℕ}

def firstEdge (i : Fin k) : Fin (2*k) := ⟨2*i.val,by have := i.isLt; omega⟩
def secondEdge (i : Fin k) : Fin (2*k) := ⟨2*i.val+1,by have := i.isLt; omega⟩

def weightedFirstForm (c : Fin (2*k) → Rˣ) : ⋀[R]^2 (Fin (2*k+1) → R) :=
  ∑ i : Fin k, (c (firstEdge i) : R) • exteriorPower.ιMulti R 2
    ![Pi.basisFun R (Fin (2*k+1)) (oddPathFirstLeft i),
      Pi.basisFun R (Fin (2*k+1)) (oddPathMiddle i)]

def weightedSecondForm (c : Fin (2*k) → Rˣ) : ⋀[R]^2 (Fin (2*k+1) → R) :=
  ∑ i : Fin k, (c (secondEdge i) : R) • exteriorPower.ιMulti R 2
    ![Pi.basisFun R (Fin (2*k+1)) (oddPathMiddle i),
      Pi.basisFun R (Fin (2*k+1)) (oddPathSecondRight i)]

abbrev weightedQuotientDegree (c : Fin (2*k) → Rˣ) (s : ℕ) :=
  ExteriorQuotientDegree (weightedFirstForm R c) (weightedSecondForm R c) s

def pathEdgeExtension (c : Fin (2*k) → Rˣ) (j : ℕ) : Rˣ :=
  if h : j<2*k then c ⟨j,h⟩ else 1

def pathVertexUnitNat (c : Fin (2*k) → Rˣ) : ℕ → Rˣ
  | 0 => 1
  | j+1 => pathEdgeExtension R c j * (pathVertexUnitNat c j)⁻¹

def pathVertexUnits (c : Fin (2*k) → Rˣ) (j : Fin (2*k+1)) : Rˣ :=
  pathVertexUnitNat R c j.val

theorem pathVertexUnits_edge (c : Fin (2*k) → Rˣ) (j : Fin (2*k)) :
    pathVertexUnits R c j.castSucc * pathVertexUnits R c j.succ = c j := by
  simp only [pathVertexUnits, Fin.val_castSucc, Fin.val_succ, pathVertexUnitNat,
    pathEdgeExtension, dif_pos j.isLt]
  simp [mul_comm, mul_left_comm, mul_assoc]

theorem pathVertexUnits_first (c : Fin (2*k) → Rˣ) (i : Fin k) :
    pathVertexUnits R c (oddPathFirstLeft i) *
      pathVertexUnits R c (oddPathMiddle i) = c (firstEdge i) := by
  exact pathVertexUnits_edge R c (firstEdge i)

theorem pathVertexUnits_second (c : Fin (2*k) → Rˣ) (i : Fin k) :
    pathVertexUnits R c (oddPathMiddle i) *
      pathVertexUnits R c (oddPathSecondRight i) = c (secondEdge i) := by
  exact pathVertexUnits_edge R c (secondEdge i)

def pathDiagonalEquiv (c : Fin (2*k) → Rˣ) :
    (Fin (2*k+1) → R) ≃ₗ[R] (Fin (2*k+1) → R) :=
  (Pi.basisFun R (Fin (2*k+1))).equiv
    ((Pi.basisFun R (Fin (2*k+1))).unitsSMul (pathVertexUnits R c)) (Equiv.refl _)

@[simp] theorem pathDiagonalEquiv_basis (c : Fin (2*k) → Rˣ)
    (i : Fin (2*k+1)) :
    pathDiagonalEquiv R c (Pi.basisFun R (Fin (2*k+1)) i) =
      pathVertexUnits R c i • Pi.basisFun R (Fin (2*k+1)) i := by
  rw [pathDiagonalEquiv, Module.Basis.equiv_apply]
  exact Module.Basis.unitsSMul_apply i

def pathWordUnit (c : Fin (2*k) → Rˣ) (I : Fin s → Fin (2*k+1)) : Rˣ :=
  ∏ i, pathVertexUnits R c (I i)

theorem pathDiagonalEquiv_word (c : Fin (2*k) → Rˣ)
    (I : Fin s → Fin (2*k+1)) :
    exteriorPower.map s (pathDiagonalEquiv R c).toLinearMap
        (exteriorPower.ιMulti R s (fun i => Pi.basisFun R (Fin (2*k+1)) (I i))) =
      pathWordUnit R c I •
        exteriorPower.ιMulti R s (fun i => Pi.basisFun R (Fin (2*k+1)) (I i)) := by
  rw [exteriorPower.map_apply_ιMulti]
  simpa only [Function.comp_def, LinearEquiv.coe_coe, pathDiagonalEquiv_basis,
    Units.smul_def, pathWordUnit, Units.coe_prod] using
    (exteriorPower.ιMulti R s).map_smul_univ
      (fun i => (pathVertexUnits R c (I i) : R))
      (fun i => Pi.basisFun R (Fin (2*k+1)) (I i))

theorem pathDiagonalEquiv_pair (c : Fin (2*k) → Rˣ)
    (u v : Fin (2*k+1)) :
    exteriorPower.map 2 (pathDiagonalEquiv R c).toLinearMap
      (exteriorPower.ιMulti R 2 ![Pi.basisFun R (Fin (2*k+1)) u,
        Pi.basisFun R (Fin (2*k+1)) v]) =
      ((pathVertexUnits R c u * pathVertexUnits R c v : Rˣ) : R) •
        exteriorPower.ιMulti R 2 ![Pi.basisFun R (Fin (2*k+1)) u,
          Pi.basisFun R (Fin (2*k+1)) v] := by
  have h := pathDiagonalEquiv_word R c ![u,v]
  have he : (fun i : Fin 2 => Pi.basisFun R (Fin (2*k+1)) (![u,v] i)) =
      ![Pi.basisFun R (Fin (2*k+1)) u, Pi.basisFun R (Fin (2*k+1)) v] := by
    funext i
    fin_cases i <;> rfl
  rw [he] at h
  simpa only [Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
    pathWordUnit, Units.smul_def, Function.comp_def] using h

theorem pathDiagonalEquiv_firstForm (c : Fin (2*k) → Rˣ) :
    exteriorPower.map 2 (pathDiagonalEquiv R c).toLinearMap (firstForm R k) =
      weightedFirstForm R c := by
  simp only [firstForm, weightedFirstForm, map_sum, pathDiagonalEquiv_pair,
    pathVertexUnits_first]

theorem pathDiagonalEquiv_secondForm (c : Fin (2*k) → Rˣ) :
    exteriorPower.map 2 (pathDiagonalEquiv R c).toLinearMap (secondForm R k) =
      weightedSecondForm R c := by
  simp only [secondForm, weightedSecondForm, map_sum, pathDiagonalEquiv_pair,
    pathVertexUnits_second]

def weightedQuotientEquiv (c : Fin (2*k) → Rˣ) (s : ℕ) :
    quotientDegree R k s ≃ₗ[R] weightedQuotientDegree R c s :=
  exteriorQuotientDegreePencilEquiv (pathDiagonalEquiv R c)
    (firstForm R k) (secondForm R k)
    (weightedFirstForm R c) (weightedSecondForm R c)
    (by rw [pathDiagonalEquiv_firstForm, pathDiagonalEquiv_secondForm]) s

def weightedGoodWord (c : Fin (2*k) → Rˣ) (s : ℕ) (I : GoodOddIndex k s) :
    weightedQuotientDegree R c s :=
  Submodule.Quotient.mk (powerBasis R s (2*k+1) I.val)

theorem weightedQuotientEquiv_goodWord (c : Fin (2*k) → Rˣ)
    (I : GoodOddIndex k s) :
    weightedQuotientEquiv R c s (goodWord R k s I) =
      pathWordUnit R c I.val.val • weightedGoodWord R c s I := by
  rw [weightedQuotientEquiv, goodWord, exteriorQuotientDegreePencilEquiv_mk,
    powerBasis_apply, pathDiagonalEquiv_word]
  simp only [weightedGoodWord, powerBasis_apply, Units.smul_def,
    Submodule.Quotient.mk_smul]

def weightedBasisOfGoodBasis (c : Fin (2*k) → Rˣ) (s : ℕ)
    (b : Module.Basis (GoodOddIndex k s) R (quotientDegree R k s)) :
    Module.Basis (GoodOddIndex k s) R (weightedQuotientDegree R c s) :=
  (b.map (weightedQuotientEquiv R c s)).unitsSMul
    (fun I => (pathWordUnit R c I.val.val)⁻¹)

theorem weightedBasisOfGoodBasis_apply (c : Fin (2*k) → Rˣ) (s : ℕ)
    (b : Module.Basis (GoodOddIndex k s) R (quotientDegree R k s))
    (hb : ∀ I, b I=goodWord R k s I) (I : GoodOddIndex k s) :
    weightedBasisOfGoodBasis R c s b I = weightedGoodWord R c s I := by
  rw [weightedBasisOfGoodBasis, Module.Basis.unitsSMul_apply, Module.Basis.map_apply,
    hb, weightedQuotientEquiv_goodWord, inv_smul_smul]

/-- The exact multivariate Laurent coefficient ring in the paper: the
group algebra of the free abelian exponent group over `ℤ[1/M!]`. -/
def IntegralLaurentRing (k : ℕ) :=
  AddMonoidAlgebra (IntegralCoefficientRing k) (Fin (2*k) →₀ ℤ)

instance integralLaurentRing_commRing (k : ℕ) : CommRing (IntegralLaurentRing k) :=
  inferInstanceAs (CommRing (AddMonoidAlgebra (IntegralCoefficientRing k) (Fin (2*k) →₀ ℤ)))

instance integralLaurentRing_algebra (k : ℕ) :
    Algebra (IntegralCoefficientRing k) (IntegralLaurentRing k) := by
  unfold IntegralLaurentRing
  infer_instance

def integralLaurentEdge (k : ℕ) (i : Fin (2*k)) : (IntegralLaurentRing k)ˣ where
  val := AddMonoidAlgebra.single (Finsupp.single i 1) 1
  inv := AddMonoidAlgebra.single (-Finsupp.single i 1) 1
  val_inv := by
    change AddMonoidAlgebra.single (Finsupp.single i 1) (1 : IntegralCoefficientRing k) *
      AddMonoidAlgebra.single (-Finsupp.single i 1) 1 =
        (1 : AddMonoidAlgebra (IntegralCoefficientRing k) (Fin (2*k) →₀ ℤ))
    simp only [AddMonoidAlgebra.single_mul_single,add_neg_cancel,
      one_mul,←AddMonoidAlgebra.one_def]
  inv_val := by
    change AddMonoidAlgebra.single (-Finsupp.single i 1) (1 : IntegralCoefficientRing k) *
      AddMonoidAlgebra.single (Finsupp.single i 1) 1 =
        (1 : AddMonoidAlgebra (IntegralCoefficientRing k) (Fin (2*k) →₀ ℤ))
    simp only [AddMonoidAlgebra.single_mul_single,neg_add_cancel,
      one_mul,←AddMonoidAlgebra.one_def]

set_option maxHeartbeats 800000 in
/-- Every degree of the literal quotient with all independent Laurent
edge coefficients has the printed good monomials as a free basis. -/
def paper_integral_laurent_basis (k s : ℕ) :
    Module.Basis (GoodOddIndex k s) (IntegralLaurentRing k)
      (weightedQuotientDegree (IntegralLaurentRing k) (integralLaurentEdge k) s) :=
  weightedBasisOfGoodBasis (IntegralLaurentRing k) (integralLaurentEdge k) s
    (paper_integral_good_basis_after_base_change k s (IntegralLaurentRing k))

@[simp] theorem paper_integral_laurent_basis_apply (k s : ℕ)
    (I : GoodOddIndex k s) :
    paper_integral_laurent_basis k s I =
      weightedGoodWord (IntegralLaurentRing k) (integralLaurentEdge k) s I :=
  weightedBasisOfGoodBasis_apply _ _ _ _
    (paper_integral_good_basis_after_base_change_apply k s _) I

/-- Actual free good-word bases after every base change from the full
Laurent coefficient ring.  The target may be nonreduced or have torsion. -/
def paper_integral_laurent_basis_after_base_change (k s : ℕ)
    (T : Type*) [CommRing T] [Algebra (IntegralCoefficientRing k) T]
    [Algebra (IntegralLaurentRing k) T]
    [IsScalarTower (IntegralCoefficientRing k) (IntegralLaurentRing k) T] :
    Module.Basis (GoodOddIndex k s) T
      (weightedQuotientDegree T
        (fun i => Units.map (algebraMap (IntegralLaurentRing k) T).toMonoidHom
          (integralLaurentEdge k i)) s) :=
  weightedBasisOfGoodBasis T _ s
    (paper_integral_good_basis_after_base_change k s T)

@[simp] theorem paper_integral_laurent_basis_after_base_change_apply (k s : ℕ)
    (T : Type*) [CommRing T] [Algebra (IntegralCoefficientRing k) T]
    [Algebra (IntegralLaurentRing k) T]
    [IsScalarTower (IntegralCoefficientRing k) (IntegralLaurentRing k) T]
    (I : GoodOddIndex k s) :
    paper_integral_laurent_basis_after_base_change k s T I =
      weightedGoodWord T
        (fun i => Units.map (algebraMap (IntegralLaurentRing k) T).toMonoidHom
          (integralLaurentEdge k i)) s I :=
  weightedBasisOfGoodBasis_apply _ _ _ _
    (paper_integral_good_basis_after_base_change_apply k s T) I

end PaperVerification.AlternatingForms.IntegralOdd
