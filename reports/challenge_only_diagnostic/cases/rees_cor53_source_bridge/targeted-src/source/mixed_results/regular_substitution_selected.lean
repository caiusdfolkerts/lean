module
public import mixed_results.regular_substitution_tor_algebra
public import mixed_results.koszul_selected_elimination
public import mixed_results.tensor_koszul_selected_rename

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.RegularSubstitutionSelected -/
section

/-! # Regular substitution preserves each selected Rees degree

The coefficient projection is linear over the source polynomial ring.
Both maps in the double-Koszul comparison commute with its tensor
extensions. Projecting class lifts proves that generation by any
specified coefficient degree is preserved.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency true
noncomputable section
namespace FourPapers.PolynomialRegularSubstitution
open Classical CommAlg MvPolynomial
open scoped TensorProduct
universe u
variable {K Y V : Type u} [Field K] [Fintype V] [LinearOrder V]
  [Fintype Y] [LinearOrder Y]
local instance : LinearOrder (V ⊕ Y) :=
  LinearOrder.lift' (fun z : V ⊕ Y => (toLex z : Lex (V ⊕ Y))) (fun _ _ h => h)
local instance : LinearOrder (Y ⊕ V) :=
  LinearOrder.lift' (fun z : Y ⊕ V => (toLex z : Lex (Y ⊕ V))) (fun _ _ h => h)
local notation "S" => MvPolynomial V K
local notation "R" => MvPolynomial Y K
variable (f : V → (MvPolynomial Y K))
variable [Algebra (MvPolynomial V K) (MvPolynomial Y K)] [IsScalarTower K (MvPolynomial V K) (MvPolynomial Y K)]
variable (A : Type u) [CommRing A] [Algebra (MvPolynomial V K) A] [Algebra K A] [IsScalarTower K (MvPolynomial V K) A]

def doubleCoefficientProjection (P : A →ₗ[S] A) : (A ⊗[K] R) →ₗ[K] (A ⊗[K] R) :=
  (P.restrictScalars K).rTensor R

def baseCoefficientProjection (P : A →ₗ[S] A) : (A ⊗[S] R) →ₗ[K] (A ⊗[S] R) :=
  (P.rTensor R).restrictScalars K

variable {A}

theorem sourceProjection_mul (P : A →ₗ[S] A) (s : S) (a : A) :
    P (algebraMap S A s*a)=algebraMap S A s*P a := by
  simpa only [Algebra.smul_def] using P.map_smul s a

theorem doubleProjection_mul (P : A →ₗ[S] A) (s : S) (r : R) (z : A ⊗[K] R) :
    doubleCoefficientProjection A P ((algebraMap S A s ⊗ₜ[K] r)*z)=
      (algebraMap S A s ⊗ₜ[K] r)*doubleCoefficientProjection A P z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [mul_zero,map_zero]
  | add x y hx hy => simp only [mul_add,map_add,hx,hy]
  | tmul a q =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, doubleCoefficientProjection,
        LinearMap.rTensor_tmul, LinearMap.restrictScalars_apply]
      rw [sourceProjection_mul]

theorem doubleProjection_graph_mul (P : A →ₗ[S] A) (v : V) (z : A ⊗[K] R) :
    doubleCoefficientProjection A P (graphFamily f A v*z)=
      graphFamily f A v*doubleCoefficientProjection A P z := by
  rw [graphFamily,sub_mul,map_sub,sub_mul,doubleProjection_mul]
  congr 1
  simpa only [map_one] using doubleProjection_mul P (1 : S) (f v) z

theorem doubleProjection_variable_mul (P : A →ₗ[S] A) (y : Y) (z : A ⊗[K] R) :
    doubleCoefficientProjection A P
      (PolynomialCoefficientContraction.variables (K := K) (A := A) y*z)=
      PolynomialCoefficientContraction.variables (K := K) (A := A) y*
        doubleCoefficientProjection A P z := by
  simpa only [map_one,PolynomialCoefficientContraction.variables] using
    doubleProjection_mul P (1 : S) (X y) z

theorem baseProjection_mul (P : A →ₗ[S] A) (r : R) (z : A ⊗[S] R) :
    baseCoefficientProjection (Y := Y) A P (((1 : A) ⊗ₜ[S] r)*z)=
      ((1 : A) ⊗ₜ[S] r)*baseCoefficientProjection (Y := Y) A P z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [mul_zero,map_zero]
  | add x y hx hy => simp only [mul_add,map_add,hx,hy]
  | tmul a q =>
      simp only [Algebra.TensorProduct.tmul_mul_tmul, baseCoefficientProjection,
        LinearMap.restrictScalars_apply, LinearMap.rTensor_tmul, one_mul]

theorem baseProjection_idempotent (P : A →ₗ[S] A) (hP : ∀ a, P (P a)=P a)
    (z : A ⊗[S] R) :
    baseCoefficientProjection (Y := Y) A P (baseCoefficientProjection (Y := Y) A P z)=
      baseCoefficientProjection (Y := Y) A P z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul a r => change P (P a) ⊗ₜ[S] r=P a ⊗ₜ[S] r; rw [hP]

theorem coefficientQuotient_projection (P : A →ₗ[S] A) (z : A ⊗[K] R) :
    coefficientQuotient (V := V) (Y := Y) A (doubleCoefficientProjection A P z)=
      baseCoefficientProjection (Y := Y) A P (coefficientQuotient (V := V) (Y := Y) A z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul a r =>
      change coefficientQuotient (V := V) (Y := Y) A (P a ⊗ₜ[K] r)=
        baseCoefficientProjection (Y := Y) A P (coefficientQuotient (V := V) (Y := Y) A (a ⊗ₜ[K] r))
      rw [coefficientQuotient_tmul,coefficientQuotient_tmul]
      rfl

theorem evaluation_projection (P : A →ₗ[S] A) (z : A ⊗[K] R) :
    PolynomialCoefficientContraction.evaluation (doubleCoefficientProjection A P z)=
      P (PolynomialCoefficientContraction.evaluation z) := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | add x y hx hy => simp only [map_add,hx,hy]
  | tmul a r =>
      change PolynomialCoefficientContraction.evaluation (P a ⊗ₜ[K] r)=
        P (PolynomialCoefficientContraction.evaluation (a ⊗ₜ[K] r))
      rw [PolynomialCoefficientContraction.evaluation_tmul,
        PolynomialCoefficientContraction.evaluation_tmul]
      exact ((P.restrictScalars K).map_smul (constantCoeff r) a).symm

variable (w : V → ℕ) (hhom : ∀ v, (f v).IsHomogeneous (w v))
  (hreg : RegularFamilyKoszul.IsRegularFamily f) (hw : ∀ v, 0 < w v)
  (hvars : ∀ v, algebraMap (MvPolynomial V K) (MvPolynomial Y K) (X v)=f v)

/-- A coefficient-family equality transports the entire selected-class
predicate, including the quotient algebra structures. -/
theorem koszulSelectedGeneration_family_congr {A₀ W₀ : Type u}
    [CommRing A₀] [Algebra K A₀] [Fintype W₀] [LinearOrder W₀]
    {x y : W₀ → A₀} (h : x = y)
    (T : Submodule K (A₀ ⊗[K] Simplicial.Ambient W₀ K)) :
    Algebra.adjoin K ((TensorExteriorKoszul.parityDifferential (K := K) x).classesFrom T) = ⊤ ↔
      Algebra.adjoin K ((TensorExteriorKoszul.parityDifferential (K := K) y).classesFrom T) = ⊤ := by
  subst y
  rfl

include hhom hreg hw hvars in
/-- Generation by a projected coefficient degree is invariant under a
positive homogeneous regular substitution. The two sets consist of
literal cycle classes in the actual Koszul homology algebras. -/
theorem selectedGeneration_iff (P : A →ₗ[S] A) (hP : ∀ a, P (P a)=P a) :
    Algebra.adjoin K
      ((TensorExteriorKoszul.parityDifferential (K := K)
        (fun v : V => algebraMap S A (X v))).classesFrom
        (LinearMap.range (KoszulCoefficientProjection.tensor (V := V)
          (P.restrictScalars K))))=⊤ ↔
    Algebra.adjoin K
      ((TensorExteriorKoszul.parityDifferential (K := K)
        (fun y : Y => (1 : A) ⊗ₜ[S] (X y : R))).classesFrom
        (LinearMap.range (KoszulCoefficientProjection.tensor (V := Y)
          (baseCoefficientProjection (Y := Y) A P))))=⊤ := by
  let PD : (A ⊗[K] R) →ₗ[K] (A ⊗[K] R) := doubleCoefficientProjection (Y := Y) A P
  have hgraph := KoszulFamilyElimination.selectedGeneration_iff
    (graphFamily f A) (PolynomialCoefficientContraction.variables (K := K) (A := A) (Y := Y))
    (coefficientQuotient (V := V) (Y := Y) A) (graphTensorContraction f w hhom hreg hw hvars A)
    (graphTensorContraction_d f w hhom hreg hw hvars A)
    (graphTensorContraction_projection f w hhom hreg hw hvars A)
    PD (baseCoefficientProjection (Y := Y) A P) (baseProjection_idempotent (Y := Y) P hP)
    (by intro v z; cases v with
        | inl v => exact doubleProjection_graph_mul f P v z
        | inr y => exact doubleProjection_variable_mul P y z)
    (by intro y z; rw [PolynomialCoefficientContraction.variables,coefficientQuotient_tmul]
        exact baseProjection_mul P (X y) z)
    (coefficientQuotient_projection (Y := Y) P)
  have hvariable := KoszulFamilyElimination.selectedGeneration_iff
    (PolynomialCoefficientContraction.variables (K := K) (A := A) (Y := Y)) (graphFamily f A)
    (PolynomialCoefficientContraction.evaluation (K := K) (A := A) (Y := Y))
    (PolynomialCoefficientContraction.contraction (K := K) (A := A) (Y := Y))
    PolynomialCoefficientContraction.contraction_d PolynomialCoefficientContraction.contraction_projection
    PD (P.restrictScalars K) hP
    (by intro v z; cases v with
        | inl y => exact doubleProjection_variable_mul P y z
        | inr v => exact doubleProjection_graph_mul f P v z)
    (by intro v a; rw [evaluation_graphFamily f w hhom hw]
        exact sourceProjection_mul P (X v) a)
    (evaluation_projection P)
  have hswap := adjoin_eq_top_iff_of_algEquiv
    (TensorKoszulAlgebraRename.homologyEquiv (Equiv.sumComm V Y)
      (Sum.elim (graphFamily f A) (PolynomialCoefficientContraction.variables (K := K) (A := A) (Y := Y)))
      (Sum.elim (PolynomialCoefficientContraction.variables (K := K) (A := A) (Y := Y)) (graphFamily f A))
      (by intro v; cases v <;> rfl)) _ _
    (TensorKoszulAlgebraRename.homologyEquiv_selectedClasses (Equiv.sumComm V Y) _ _
      (by intro v; cases v <;> rfl) PD)
  have ht := hvariable.symm.trans (hswap.symm.trans hgraph)
  have hsource : (fun v : V => PolynomialCoefficientContraction.evaluation
      (graphFamily f A v)) = (fun v : V => algebraMap S A (X v)) :=
    funext (evaluation_graphFamily f w hhom hw A)
  have htarget : (fun y : Y => coefficientQuotient (V := V) (Y := Y) A
      (PolynomialCoefficientContraction.variables (K := K) (A := A) y)) =
      (fun y : Y => (1 : A) ⊗ₜ[S] (X y : R)) := by
    funext y
    exact coefficientQuotient_tmul (V := V) (Y := Y) A 1 (X y)
  have hs := koszulSelectedGeneration_family_congr (K := K) hsource
    (LinearMap.range (KoszulCoefficientProjection.tensor (V := V) (P.restrictScalars K)))
  have ht' := koszulSelectedGeneration_family_congr (K := K) htarget
    (LinearMap.range (KoszulCoefficientProjection.tensor (V := Y)
      (baseCoefficientProjection (Y := Y) A P)))
  exact hs.symm.trans (ht.trans ht')

end FourPapers.PolynomialRegularSubstitution

end
end
end

end
