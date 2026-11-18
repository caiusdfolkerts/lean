module
public import SegreVerified.Stage028.GlobalWedges
public import SegreVerified.Stage028.CriticalPolynomials
import all Lean.Util.CollectAxioms

set_option Elab.async false
set_option linter.all false

#eval do
  let toolchain ← IO.FS.readFile "lean-toolchain"
  let manifest ← IO.FS.readFile "lake-manifest.json"
  IO.println ("SEGRE_PUBLIC_ENVIRONMENT_BEGIN\n" ++ Lean.versionString ++ "\n" ++
    Lean.githash ++ "\n" ++ toolchain.trimAscii.toString ++ "\n" ++ manifest ++
    "\nSEGRE_PUBLIC_ENVIRONMENT_END")

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  unless env.header.trustLevel == 0 do
    throwError "The retained source check requires kernel trust level zero"
  let imported := exportedAxiomsExt.getState (asyncMode := .mainOnly) env
  let rows := CollectAxioms.runM (env.setExporting false) do
    #[``Nat.add_comm, ``Nat.zero_add].mapM fun name =>
      return (name, ← CollectAxioms.collectAndGet imported.find? name)
  for (name, axioms) in rows do
    unless (env.checked.get.find? name).isSome do throwError "Unchecked smoke target: {name}"
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unapproved shared-collector smoke axiom: {ax}"
  logInfo "SEGRE_SHARED_COLLECTOR_READY"


set_option Elab.async false
set_option maxErrors 0
set_option maxRecDepth 2048
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section ProbeLayer391



/-!
# Singular-vector geometry and all-format spanning theorems

The named sections preserve the original proof stages and local scopes.
-/

@[expose] public section

-- Emit compilation progress immediately while checking this large unit.
set_option stderrAsMessages false
-- Style linting is separate from elaboration, kernel checking, and the axiom audit.
set_option linter.all false
noncomputable section
set_option autoImplicit false


section SegreGlobalCriticalSections

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

run_cmd do
  let out ← IO.getStderr
  out.putStrLn "SEGRE_STAGE Stage028.GlobalImage"
  out.flush

/-!
# Global critical sections and their literal chart equations

The named sections preserve the original proof stages and local scopes.
-/


section SegreGlobalCriticalImage

/-!
# The complete global critical image in its original polynomial coordinates

The source is the genuine global section space of the sum of pulled-back
Euler kernels. Its entire image is identified with the span of the literal
critical polynomials, retaining every factor, tensor coefficient and sign.
The covector comparison below uses the ordinary standard-coordinate pairing;
it is an equality of full linear maps and submodules, rather than a rank
comparison or a selected family of source sections.

-/

set_option autoImplicit false
open scoped Classical BigOperators

namespace PaperVerification.Segre.GlobalCriticalImage

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open FixedProductCohomology FixedProductProjections ActualProductKoszulTerms
open ProductGlobalWedges ActualLineGlobalSections EulerSheaf EulerCriticalFunctional
open Staircase Monomials Degeneration Trace GraphSpan CriticalGraph SpanDefect

variable {K : Type} [Field K] {k : ℕ} (n : Fin (k+1) → ℕ)

local notation "I" => (fun i => Fin (n i+1))
set_option quotPrecheck false in local notation "X" => (product K I).scheme

/-- An actual ordered source wedge has its specified actual factor component. -/
theorem orderedSourceWedge_component (q : CriticalIndex n) (j : Fin (k+1)) :
    (Pi.π (ActualProductChartFrames.factorKernel K I) j).app ⊤
      (orderedSourceWedge K I q)=
        Pi.single (M := fun j => ExternalSections.sections K
          ((Scheme.Modules.pullback (factorProjection K I j)).obj
            (eulerKernel («I» := I j) (K := K) 2)) ⊤) q.1
          ((factorProjection K I q.1).pullbackSectionsLE
            (eulerKernel («I» := I q.1) (K := K) 2) ⊤ ⊤ (by simp)
            (coordinateWedge q.2.2 q.2.1 ⊤)) j := by
  rw [← SchemeProductSections.productSectionsEquiv_apply]
  change sourceSectionsEquiv K I (orderedSourceWedge K I q) j=_
  rw [orderedSourceWedge,LinearEquiv.apply_symm_apply]

/-- The whole full-format functional, evaluated on one actual source wedge,
gives its literal critical coordinate. The reversed wedge orientation is the
orientation of the original critical operator. -/
theorem full_map_orderedSourceWedge (T : Cell n → K) (q : CriticalIndex n) :
    (GlobalCriticalMap.criticalMap I (factorProjection K I) T).app ⊤
      (orderedSourceWedge K I q)=
        (GlobalCriticalMap.criticalCoordinate I (factorProjection K I) T
          q.1 q.2.2 q.2.1).app ⊤ (1 : Γ(X,⊤)) := by
  refine (ActualCriticalFrame.sum_projection_app K I
    (fun i => GlobalCriticalMap.factorCritical I (factorProjection K I) T i)
    ⊤ (orderedSourceWedge K I q)).trans ?_
  simp only [orderedSourceWedge_component]
  rw [Finset.sum_eq_single q.1]
  · rw [Pi.single_eq_same,GlobalCriticalMap.factorCritical_coordinateWedge]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj,map_zero]
  · intro h
    exact (h (Finset.mem_univ q.1)).elim

variable {J : Type} [Fintype J] [DecidableEq J]

/-- The whole graph functional has exactly the same source orientation. -/
theorem graph_map_orderedSourceWedge (A : Matrix (Cell n) J K) (q : CriticalIndex n) :
    (GraphCriticalMap.graphCriticalMap I (factorProjection K I) (fun j u => A u j)).app ⊤
      (orderedSourceWedge K I q)=
        (GraphCriticalMap.graphCriticalCoordinate I (factorProjection K I)
          (fun j u => A u j) q.1 q.2.2 q.2.1).app ⊤ (1 : Γ(X,⊤)) := by
  refine (ActualCriticalFrame.sum_projection_app K I
    (fun i => GraphCriticalMap.graphFactorCritical I (factorProjection K I) (fun j u => A u j) i)
    ⊤ (orderedSourceWedge K I q)).trans ?_
  simp only [orderedSourceWedge_component]
  rw [Finset.sum_eq_single q.1]
  · rw [Pi.single_eq_same,GraphCriticalMap.graphFactorCritical_coordinateWedge]
  · intro j _ hj
    rw [Pi.single_eq_of_ne hj,map_zero]
  · intro h
    exact (h (Finset.mem_univ q.1)).elim

/-- The actual complete full-format H⁰ map. -/
def fullGlobalMap (T : Cell n → K) :
    ExternalSections.sections K (source K I) ⊤ →ₗ[K]
      ExternalSections.sections K (line K I 1) ⊤ :=
  (((sectionsBasePresheafFunctor K).map
    (GlobalCriticalMap.criticalMap I (factorProjection K I) T)).app (op ⊤)).hom

/-- The actual complete graph-format H⁰ map. -/
def graphGlobalMap (A : Matrix (Cell n) J K) :
    ExternalSections.sections K (source K I) ⊤ →ₗ[K]
      ExternalSections.sections K (line K I 2) ⊤ :=
  (((sectionsBasePresheafFunctor K).map
    (GraphCriticalMap.graphCriticalMap I (factorProjection K I)
      (fun j u => A u j))).app (op ⊤)).hom

/-- Every global full-format image, with no selected-source restriction. -/
theorem fullGlobalMap_range (T : Cell n → K) :
    LinearMap.range (fullGlobalMap n T)=
      (Submodule.span K (Set.range (fun q : CriticalIndex n =>
        fullCoordinatePolynomial n T q.1 q.2.2 q.2.1))).map
          (degreeOneLineEquiv (K := K) n).toLinearMap := by
  rw [fullGlobalMap,global_range_eq_span_ordered_wedges,Submodule.map_span]
  simp only [full_map_orderedSourceWedge,← Set.range_comp,Function.comp_def,
    LinearEquiv.coe_coe,degreeOneLineEquiv_fullCoordinatePolynomial]
  congr 1
  apply congrArg Set.range
  funext q
  exact full_map_orderedSourceWedge n T q

/-- Every global graph-format image, with no selected-source restriction. -/
theorem graphGlobalMap_range (A : Matrix (Cell n) J K) :
    LinearMap.range (graphGlobalMap n A)=
      (Submodule.span K (Set.range (fun q : CriticalIndex n =>
        graphCoordinatePolynomial n (fun j u => A u j) q.1 q.2.2 q.2.1))).map
          (degreeTwoLineEquiv (K := K) n).toLinearMap := by
  rw [graphGlobalMap,global_range_eq_span_ordered_wedges,Submodule.map_span]
  simp only [graph_map_orderedSourceWedge,← Set.range_comp,Function.comp_def,
    LinearEquiv.coe_coe,degreeTwoLineEquiv_graphCoordinatePolynomial]
  congr 1
  apply congrArg Set.range
  funext q
  exact graph_map_orderedSourceWedge n A q

/-- Every row of a finite linear operator spans its complete dual range. -/
theorem dual_range_eq_span_rows {D E : Type*} [Fintype D] [DecidableEq D]
    [AddCommGroup E] [Module K E] (f : E →ₗ[K] (D → K)) :
    LinearMap.range f.dualMap=
      Submodule.span K (Set.range (fun q : D => f.dualMap (LinearMap.proj q))) := by
  have htop : Submodule.span K (Set.range (fun q : D =>
      (LinearMap.proj q : Module.Dual K (D → K))))=⊤ := by
    have hb : (fun q : D => (Pi.basisFun K D).dualBasis q)=
        (fun q : D => (LinearMap.proj q : Module.Dual K (D → K))) := by
      funext q
      apply LinearMap.ext
      intro v
      simp [Module.Basis.dualBasis_apply]
    rw [← hb]
    exact (Pi.basisFun K D).dualBasis.span_eq
  rw [← Submodule.map_top f.dualMap,← htop,Submodule.map_span,← Set.range_comp]
  rfl

/-- Filtering a complete tensor index by one coordinate is exactly the
sum over all remaining coordinates. -/
theorem sum_cell_filter {V : Type*} [AddCommMonoid V]
    (i : Fin (k+1)) (a : Fin (n i+1)) (f : Cell n → V) :
    (∑ u : Cell n,if u i=a then f u else 0)=
      ∑ w : OtherCell n i,f (assemble i a w) := by
  rw [← Equiv.sum_comp (Equiv.piSplitAt i (fun h => Fin (n h+1))).symm,
    Fintype.sum_prod_type]
  change (∑ b,∑ w : OtherCell n i,if assemble i b w i=a then
    f (assemble i b w) else 0)=_
  simp [assemble_same]

theorem update_assemble (i : Fin (k+1)) (a b : Fin (n i+1))
    (w : OtherCell n i) :
    Function.update (assemble i a w) i b=assemble i b w := by
  funext j
  by_cases hj : j=i
  · subst j
    simp
  · simpa only [Function.update_of_ne hj] using
      (assemble_other i a w ⟨j,hj⟩).trans (assemble_other i b w ⟨j,hj⟩).symm

/-- Evaluation of the entire full polynomial is the original critical
operator on the original pure tensor, with its exact coordinate order. -/
theorem eval_fullCoordinatePolynomial (T : Cell n → K)
    (x : Variables n → K) (i : Fin (k+1)) (p q : Fin (n i+1)) :
    MvPolynomial.eval x (fullCoordinatePolynomial n T i p q).val=
      criticalOperator (fun u (_ : Unit) => T u)
        (SingularSpan.rankOneTensor x AllFactorPointSpan.unitVector) ⟨i,(q,p)⟩ := by
  let e : degreeOne (K := K) (n := n) →ₗ[K] K :=
    (MvPolynomial.aeval x).toLinearMap.comp (degreeOne (K := K) (n := n)).subtype
  change e (fullCoordinatePolynomial n T i p q)=_
  have he (u : Cell n) : e (coordinateElement n u)=
      MvPolynomial.eval x (cellPolynomial u) := rfl
  have heite (P : Prop) [Decidable P] (c : K) (u : Cell n) :
      e (if P then c • coordinateElement n u else 0) =
        if P then c * MvPolynomial.eval x (cellPolynomial u) else 0 := by
    split_ifs <;> simp only [_root_.map_smul,map_zero,he,smul_eq_mul]
  rw [fullCoordinatePolynomial,map_sum]
  simp only [map_sub,heite]
  rw [Finset.sum_sub_distrib,sum_cell_filter,sum_cell_filter]
  simp only [update_assemble]
  change (∑ w : OtherCell n i,T (assemble i q w)*
    MvPolynomial.eval x (cellPolynomial (assemble i p w)))-
    (∑ w : OtherCell n i,T (assemble i p w)*
      MvPolynomial.eval x (cellPolynomial (assemble i q w)))=_
  simp only [criticalOperator,SingularSpan.rankOneTensor,
    AllFactorPointSpan.unitVector,Fintype.sum_unique,mul_one,
    Finset.sum_sub_distrib]
  change _ =
    (∑ w : OtherCell n i, T (assemble i q w) *
      (MvPolynomial.eval x (cellPolynomial (assemble i p w)) * (1 : K))) -
    (∑ w : OtherCell n i, T (assemble i p w) *
      (MvPolynomial.eval x (cellPolynomial (assemble i q w)) * (1 : K)))
  simp only [mul_one]

/-- One half of the graph-coordinate polynomial is precisely the original
contraction against the complete final-factor contraction vector. -/
theorem eval_graphCoordinate_half (A : Matrix (Cell n) J K)
    (x : Variables n → K) (i : Fin (k+1)) (p q : Fin (n i+1)) :
    (∑ j : J,∑ a : Cell n,∑ b : Cell n,
      if b i=q then (A a j*A b j)*
        (MvPolynomial.eval x (cellPolynomial a)*
          MvPolynomial.eval x (cellPolynomial (Function.update b i p))) else 0)=
      ∑ w : OtherCell n i,∑ j : J,A (assemble i q w) j*
        (MvPolynomial.eval x (cellPolynomial (assemble i p w))*
          MvPolynomial.eval x (segreForm A j)) := by
  simp only [sum_cell_filter,update_assemble]
  calc
    (∑ j : J,∑ a : Cell n,∑ w : OtherCell n i,
      (A a j*A (assemble i q w) j)*
        (MvPolynomial.eval x (cellPolynomial a)*
          MvPolynomial.eval x (cellPolynomial (assemble i p w))))=
      ∑ j : J,∑ w : OtherCell n i,∑ a : Cell n,
        (A a j*A (assemble i q w) j)*
          (MvPolynomial.eval x (cellPolynomial a)*
            MvPolynomial.eval x (cellPolynomial (assemble i p w))) := by
              apply Finset.sum_congr rfl
              intro j _
              exact Finset.sum_comm
    _=_ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro w _
      apply Finset.sum_congr rfl
      intro j _
      rw [eval_segreForm]
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      ring

/-- Every graph polynomial evaluates to the original critical operator on
the actual graph tensor, retaining every original coefficient. -/
theorem eval_graphCoordinatePolynomial (A : Matrix (Cell n) J K)
    (x : Variables n → K) (i : Fin (k+1)) (p q : Fin (n i+1)) :
    MvPolynomial.eval x
      (graphCoordinatePolynomial n (fun j u => A u j) i p q).val=
        criticalOperator A (graphTensor A x) ⟨i,(q,p)⟩ := by
  change evaluationCovector x
    (graphCoordinatePolynomial n (fun j u => A u j) i p q)=_
  have he (a b : Cell n) :
      evaluationCovector x (TraceGlobalSections.coordinateProduct a b)=
        MvPolynomial.eval x (cellPolynomial a)*
          MvPolynomial.eval x (cellPolynomial b) := by
    change MvPolynomial.eval x (cellPolynomial a*cellPolynomial b)=_
    exact map_mul _ _ _
  simp only [graphCoordinatePolynomial,map_sub,map_sum,apply_ite,_root_.map_smul,map_zero,
    he,smul_eq_mul]
  rw [eval_graphCoordinate_half,eval_graphCoordinate_half]
  simp only [criticalOperator,graphTensor,Finset.sum_sub_distrib]
  rfl

/-- Restricting an arbitrary original tensor covector to the graph is
exactly the multiplication map used in the defect formula. -/
theorem eval_multiplicationOnCovectors (A : Matrix (Cell n) J K)
    (φ : Module.Dual K (Matrix (Cell n) J K)) (x : Variables n → K) :
    MvPolynomial.eval x (multiplicationOnCovectors A φ).val=φ (graphTensor A x) := by
  change evaluationCovector x
    (actualMultiplication A (coefficientDualEquiv.symm φ))=φ (graphTensor A x)
  have h := LinearMap.congr_fun (dual_multiplication_evaluation A x)
    (coefficientDualEquiv.symm φ)
  change evaluationCovector x (actualMultiplication A (coefficientDualEquiv.symm φ))=
    tensorCovector (graphTensor A x) (coefficientDualEquiv.symm φ) at h
  rw [h]
  simpa only [coefficientDualEquiv_apply] using
    LinearMap.congr_fun (coefficientDualEquiv.apply_symm_apply φ) (graphTensor A x)

/-- The actual graph critical polynomial is the restriction of the exact
ordinary critical row covector. -/
theorem graphCoordinatePolynomial_eq_dual_row [Infinite K]
    (A : Matrix (Cell n) J K) (q : CriticalIndex n) :
    graphCoordinatePolynomial n (fun j u => A u j) q.1 q.2.2 q.2.1=
      multiplicationOnCovectors A ((criticalOperator A).dualMap (LinearMap.proj q)) := by
  apply Subtype.ext
  apply MvPolynomial.funext
  intro x
  rw [eval_graphCoordinatePolynomial,eval_multiplicationOnCovectors]
  rfl

/-- The complete polynomial image is precisely the image of the original
small-factor relation space under the original Segre multiplication map. -/
theorem graph_polynomial_span_eq_mapped_relations [Infinite K]
    (A : Matrix (Cell n) J K) :
    Submodule.span K (Set.range (fun q : CriticalIndex n =>
      graphCoordinatePolynomial n (fun j u => A u j) q.1 q.2.2 q.2.1))=
        (smallRelations A).map (multiplicationOnCovectors A) := by
  rw [smallRelations,dual_range_eq_span_rows,Submodule.map_span,← Set.range_comp]
  simp only [Function.comp_def,graphCoordinatePolynomial_eq_dual_row]

/-- The complete graph H⁰ image in the canonical degree-two coordinates.
This is the full map identity needed by the global image/annihilator bridge. -/
theorem graphGlobalMap_range_eq_mapped_relations [Infinite K]
    (A : Matrix (Cell n) J K) :
    LinearMap.range (graphGlobalMap n A)=
      (smallRelations A).map
        ((degreeTwoLineEquiv (K := K) n).toLinearMap.comp (multiplicationOnCovectors A)) := by
  rw [graphGlobalMap_range,graph_polynomial_span_eq_mapped_relations,← Submodule.map_comp]

/-- The original tensor-coordinate space with a one-dimensional final
factor, with neither a quotient nor a choice of a smaller subspace. -/
def unitTensorCoordinates : (Cell n → K) ≃ₗ[K] Matrix (Cell n) Unit K where
  toFun T u _ := T u
  invFun A u := A u ()
  left_inv _ := rfl
  right_inv A := by
    funext u j
    cases j
    rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The canonical ordinary covector-to-Segre-linear-polynomial equivalence,
using the standard tensor coordinates and the actual Segre monomial basis. -/
def unitCovectorPolynomialEquiv :
    Module.Dual K (Matrix (Cell n) Unit K) ≃ₗ[K] degreeOne (K := K) (n := n) :=
  (unitTensorCoordinates (K := K) n).dualMap.trans
    ((Pi.basisFun K (Cell n)).dualBasis.equivFun.trans
      (degreeOneBasis (K := K) (n := n)).equivFun.symm)

theorem degreeOneBasis_coordinate (u : Cell n) :
    degreeOneBasis (K := K) (n := n) u=coordinateElement n u := by
  apply Subtype.ext
  exact Module.Basis.coe_span_apply _ u

/-- Each coordinate of the polynomial is exactly the value of the original
ordinary covector on the corresponding original coordinate tensor. -/
theorem unitCovectorPolynomialEquiv_coordinates
    (φ : Module.Dual K (Matrix (Cell n) Unit K)) (u : Cell n) :
    (degreeOneBasis (K := K) (n := n)).equivFun
      (unitCovectorPolynomialEquiv n φ) u=
        φ (ProjectivePointSpan.coordinateTensor u ()) := by
  change (degreeOneBasis (K := K) (n := n)).equivFun
    ((degreeOneBasis (K := K) (n := n)).equivFun.symm
      ((Pi.basisFun K (Cell n)).dualBasis.equivFun
        ((unitTensorCoordinates (K := K) n).dualMap φ))) u=_
  rw [LinearEquiv.apply_symm_apply,Module.Basis.dualBasis_equivFun,Pi.basisFun_apply]
  change φ (unitTensorCoordinates n (Pi.single u 1))=_
  congr 1
  funext v j
  cases j
  by_cases hv : v=u
  · subst v
    simp [unitTensorCoordinates,ProjectivePointSpan.coordinateTensor,Pi.single_apply]
  · simp [unitTensorCoordinates,ProjectivePointSpan.coordinateTensor,Pi.single_apply,hv]

/-- The entire polynomial is the ordinary tensor-covector coefficient
expansion, not an arbitrary linear equivalence of equal dimensions. -/
theorem unitCovectorPolynomialEquiv_eq_sum
    (φ : Module.Dual K (Matrix (Cell n) Unit K)) :
    unitCovectorPolynomialEquiv n φ=
      ∑ u : Cell n,φ (ProjectivePointSpan.coordinateTensor u ()) • coordinateElement n u := by
  calc
    unitCovectorPolynomialEquiv n φ=
      ∑ u : Cell n,(degreeOneBasis (K := K) (n := n)).equivFun
        (unitCovectorPolynomialEquiv n φ) u • degreeOneBasis (K := K) (n := n) u := by
          simpa only [Module.Basis.equivFun_apply] using
            ((degreeOneBasis (K := K) (n := n)).sum_repr
              (unitCovectorPolynomialEquiv n φ)).symm
    _=_ := by
      simp only [unitCovectorPolynomialEquiv_coordinates,degreeOneBasis_coordinate]

/-- Evaluation of the canonical full-format polynomial equals the original
ordinary covector on the actual pure tensor. -/
theorem eval_unitCovectorPolynomialEquiv
    (φ : Module.Dual K (Matrix (Cell n) Unit K)) (x : Variables n → K) :
    MvPolynomial.eval x (unitCovectorPolynomialEquiv n φ).val=
      φ (SingularSpan.rankOneTensor x AllFactorPointSpan.unitVector) := by
  let e : degreeOne (K := K) (n := n) →ₗ[K] K :=
    (MvPolynomial.aeval x).toLinearMap.comp (degreeOne (K := K) (n := n)).subtype
  change e (unitCovectorPolynomialEquiv n φ)=_
  rw [unitCovectorPolynomialEquiv_eq_sum,map_sum]
  simp only [_root_.map_smul,smul_eq_mul]
  conv_rhs => rw [ProjectivePointSpan.tensor_coordinate_expansion
    (SingularSpan.rankOneTensor x AllFactorPointSpan.unitVector)]
  simp only [Fintype.sum_unique,map_sum,_root_.map_smul,smul_eq_mul,
    SingularSpan.rankOneTensor,AllFactorPointSpan.unitVector,mul_one]
  apply Finset.sum_congr rfl
  intro u _
  change φ (ProjectivePointSpan.coordinateTensor u ())*MvPolynomial.eval x (cellPolynomial u)=_
  ring

/-- Every full-format critical polynomial is exactly its ordinary original
critical row covector in the canonical Segre degree-one coordinates. -/
theorem fullCoordinatePolynomial_eq_dual_row [Infinite K]
    (T : Cell n → K) (q : CriticalIndex n) :
    fullCoordinatePolynomial n T q.1 q.2.2 q.2.1=
      unitCovectorPolynomialEquiv n
        ((criticalOperator (unitTensorCoordinates n T)).dualMap (LinearMap.proj q)) := by
  apply Subtype.ext
  apply MvPolynomial.funext
  intro x
  rw [eval_fullCoordinatePolynomial,eval_unitCovectorPolynomialEquiv]
  rfl

/-- The full actual degree-one critical polynomial span is precisely the
ordinary full set of original factor relations in canonical coordinates. -/
theorem full_polynomial_span_eq_mapped_relations [Infinite K]
    (T : Cell n → K) :
    Submodule.span K (Set.range (fun q : CriticalIndex n =>
      fullCoordinatePolynomial n T q.1 q.2.2 q.2.1))=
        (smallRelations (unitTensorCoordinates n T)).map
          (unitCovectorPolynomialEquiv (K := K) n).toLinearMap := by
  rw [smallRelations,dual_range_eq_span_rows,Submodule.map_span,← Set.range_comp]
  simp only [Function.comp_def,LinearEquiv.coe_coe,fullCoordinatePolynomial_eq_dual_row]

/-- The ordinary tensor dual is canonically the whole H⁰ of the actual
Segre hyperplane line bundle. -/
def unitCovectorSectionsEquiv :
    Module.Dual K (Matrix (Cell n) Unit K) ≃ₗ[K]
      ExternalSections.sections K (line K I 1) ⊤ :=
  (unitCovectorPolynomialEquiv n).trans (degreeOneLineEquiv (K := K) n)

/-- The complete full-format H⁰ image in the original tensor dual
coordinates, with every original factor equation included. -/
theorem fullGlobalMap_range_eq_mapped_relations [Infinite K] (T : Cell n → K) :
    LinearMap.range (fullGlobalMap n T)=
      (smallRelations (unitTensorCoordinates n T)).map
        (unitCovectorSectionsEquiv (K := K) n).toLinearMap := by
  rw [fullGlobalMap_range,full_polynomial_span_eq_mapped_relations,← Submodule.map_comp]
  rfl

/-- Membership in the complete graph H⁰ image is exactly membership in the
ordinary multiplication image of all small-factor critical row relations. -/
theorem graphGlobalMap_mem_iff [Infinite K] (A : Matrix (Cell n) J K)
    (f : degreeTwo (K := K) (n := n)) :
    degreeTwoLineEquiv n f ∈ LinearMap.range (graphGlobalMap n A) ↔
      f ∈ (smallRelations A).map (multiplicationOnCovectors A) := by
  rw [graphGlobalMap_range,graph_polynomial_span_eq_mapped_relations]
  simp only [Submodule.mem_map_equiv,LinearEquiv.symm_apply_apply]

/-- Membership in the complete full-format H⁰ image is exactly membership
in the ordinary original-factor critical relation space. -/
theorem fullGlobalMap_mem_iff [Infinite K] (T : Cell n → K)
    (φ : Module.Dual K (Matrix (Cell n) Unit K)) :
    unitCovectorSectionsEquiv n φ ∈ LinearMap.range (fullGlobalMap n T) ↔
      φ ∈ smallRelations (unitTensorCoordinates n T) := by
  rw [fullGlobalMap_range_eq_mapped_relations]
  simp only [Submodule.mem_map_equiv,LinearEquiv.symm_apply_apply]

end PaperVerification.Segre.GlobalCriticalImage

end SegreGlobalCriticalImage

section SegreGlobalPolynomialChartRestriction

/-!
# The whole canonical H⁰ comparison commutes with every actual chart

Restricting an arbitrary genuine global line section, applying the actual
line frame and applying the actual product chart-ring isomorphism agrees
with dehomogenizing its complete Segre polynomial. The statement is proved
on every basis coordinate and extended to the entire section space.

Consequently the ordinary tensor covectors used in the annihilator theorem
have exactly the same chart polynomials as the genuine global sheaf sections
used in the Koszul and cohomology arguments.

-/

set_option autoImplicit false
open scoped Classical BigOperators

namespace PaperVerification.Segre.GlobalPolynomialChartRestriction

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open FixedProductCohomology FixedProductProjections ActualProductKoszulTerms
open ActualProductChartFrames ProductChartSections ActualCriticalPolynomial
open ActualLineGlobalSections GlobalCriticalImage
open Staircase Monomials GraphSpan CriticalGraph SpanDefect
open ProjectiveCharts ProjectivePointSpan
open scoped ProjectiveChartSections ProductChartSections

variable {K : Type} [Field K] {k : ℕ} (n : Fin (k+1) → ℕ)

local notation "I" => (fun i => Fin (n i+1))
set_option quotPrecheck false in local notation "X" => (product K I).scheme

local instance chartSectionsBaseModule (p : Cell n) (t : ℤ) :
    Module K Γ(line K I t,chart K I p) :=
  sectionsBaseModule K (line K I t) (chart K I p)

local instance chartSectionsTower (p : Cell n) (t : ℤ) :
    IsScalarTower K Γ(X,chart K I p) Γ(line K I t,chart K I p) :=
  IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)

/-- The actual restriction of a whole global line section, followed by the
actual local line frame and the actual chart coordinate-ring isomorphism. -/
def chartLineCoefficient (p : Cell n) (t : ℤ) :
    ExternalSections.sections K (line K I t) ⊤ →ₗ[K] MvPolynomial (ChartVar p) K :=
  ((numericalProductChartSectionsEquiv (K := K) n p).toLinearMap.comp
    ((lineFrame K I p t).restrictScalars K).toLinearMap).comp
      (((sectionsBasePresheafFunctor K).obj (line K I t)).map
        (chart K I p).leTop.op).hom

/-- On an actual section morphism, global restriction agrees with its
local value by the naturality of that same morphism. -/
theorem chartLineCoefficient_unitHom (p : Cell n) (t : ℤ)
    (s : 𝟙_ (X).Modules ⟶ line K I t) :
    chartLineCoefficient n p t (s.app ⊤ (1 : Γ(X,⊤)))=polynomialSection K n p t s := by
  change numericalProductChartSectionsEquiv n p
    (lineFrame K I p t
      ((line K I t).presheaf.map (chart K I p).leTop.op (s.app ⊤ (1 : Γ(X,⊤)))))=_
  have h := PresheafOfModules.naturality_apply s.val
    (chart K I p).leTop.op (1 : Γ(X,⊤))
  have hunit : (𝟙_ (X).Modules).presheaf.map (chart K I p).leTop.op
      (1 : Γ(X,⊤))=(1 : Γ(X,chart K I p)) := by
    change (X).presheaf.map (chart K I p).leTop.op (1 : Γ(X,⊤))=1
    exact map_one _
  have hclean : s.app (chart K I p) (1 : Γ(X,chart K I p)) =
      (line K I t).presheaf.map (chart K I p).leTop.op (s.app ⊤ (1 : Γ(X,⊤))) :=
    (congrArg (s.app (chart K I p)) hunit).symm.trans h
  exact congrArg (fun z : Γ(line K I t,chart K I p) =>
    numericalProductChartSectionsEquiv n p (lineFrame K I p t z)) hclean.symm

/-- The canonical degree-one comparison commutes with actual chart
restriction as an equality of the entire linear maps. -/
theorem chartLineCoefficient_degreeOne_map (p : Cell n) :
    (chartLineCoefficient (K := K) n p 1).comp
      (degreeOneLineEquiv (K := K) n).toLinearMap=
        (chartSubstitution (K := K) p).toLinearMap.comp
          (degreeOne (K := K) (n := n)).subtype := by
  apply (degreeOneBasis (K := K) (n := n)).ext
  intro a
  rw [degreeOneBasis_coordinate]
  change chartLineCoefficient n p 1 (degreeOneLineEquiv n (coordinateElement n a))=_
  erw [degreeOneLineEquiv_coordinate,chartLineCoefficient_unitHom,
    polynomialSection_tensorCoordinate,CriticalCoordinateExpansion.normalizedMonomial_eq_substitution]
  rfl

/-- The same identity holds for every actual degree-one polynomial. -/
theorem chartLineCoefficient_degreeOne (p : Cell n)
    (f : degreeOne (K := K) (n := n)) :
    chartLineCoefficient n p 1 (degreeOneLineEquiv n f)=chartSubstitution p f.val :=
  LinearMap.congr_fun (chartLineCoefficient_degreeOne_map n p) f

theorem degreeTwoBasis_coordinate (q : SortedPair n) :
    degreeTwoBasis (K := K) (n := n) q=
      TraceGlobalSections.coordinateProduct q.val.1 q.val.2 := by
  apply Subtype.ext
  simp [degreeTwoBasis,Module.Basis.map_apply,LinearEquiv.coe_ofEq_apply,
    Module.Basis.coe_span_apply,TraceGlobalSections.coordinateProduct,sortedMonomial_eq_mul]

/-- The complete degree-two comparison commutes with actual chart
restriction. Its basis consists of all sorted coordinate products. -/
theorem chartLineCoefficient_degreeTwo_map (p : Cell n) :
    (chartLineCoefficient (K := K) n p 2).comp
      (degreeTwoLineEquiv (K := K) n).toLinearMap=
        (chartSubstitution (K := K) p).toLinearMap.comp
          (degreeTwo (K := K) (n := n)).subtype := by
  apply (degreeTwoBasis (K := K) (n := n)).ext
  intro q
  rw [degreeTwoBasis_coordinate]
  change chartLineCoefficient n p 2
    (degreeTwoLineEquiv n (TraceGlobalSections.coordinateProduct q.val.1 q.val.2))=_
  erw [degreeTwoLineEquiv_coordinateProduct,chartLineCoefficient_unitHom,
    polynomialSection_graphCoordinate]
  simp only [CriticalCoordinateExpansion.normalizedMonomial_eq_substitution]
  change chartSubstitution p (cellPolynomial q.val.1)*
    chartSubstitution p (cellPolynomial q.val.2)=
      chartSubstitution p (cellPolynomial q.val.1*cellPolynomial q.val.2)
  exact (map_mul _ _ _).symm

/-- The same identity holds for every actual degree-two polynomial. -/
theorem chartLineCoefficient_degreeTwo (p : Cell n)
    (f : degreeTwo (K := K) (n := n)) :
    chartLineCoefficient n p 2 (degreeTwoLineEquiv n f)=chartSubstitution p f.val :=
  LinearMap.congr_fun (chartLineCoefficient_degreeTwo_map n p) f

/-- The ordinary full tensor covector restricts to precisely the actual
canonical degree-one section's chart coefficient. -/
theorem full_covector_chart (p : Cell n)
    (φ : Module.Dual K (Matrix (Cell n) Unit K)) :
    chartLineCoefficient n p 1 (unitCovectorSectionsEquiv n φ)=
      AllFactorPointSpan.chartRestriction p φ := by
  change chartLineCoefficient n p 1
    (degreeOneLineEquiv n (unitCovectorPolynomialEquiv n φ))=_
  rw [chartLineCoefficient_degreeOne,unitCovectorPolynomialEquiv_eq_sum]
  simp only [Submodule.coe_sum,Submodule.coe_smul,coordinateElement,map_sum,_root_.map_smul,
    MvPolynomial.smul_eq_C_mul,AllFactorPointSpan.chartRestriction,
    AllFactorPointSpan.chartSegreCoordinate]
  change (∑ x, chartSubstitution p
    (MvPolynomial.C (φ (coordinateTensor x ())) * cellPolynomial x)) =
    ∑ x, MvPolynomial.C (φ (coordinateTensor x ())) *
      chartSubstitution p (cellPolynomial x)
  simp only [map_mul, MvPolynomial.algHom_C, MvPolynomial.algebraMap_eq]

variable {J : Type} [Fintype J] [DecidableEq J]

/-- The ordinary graph tensor covector restricts to precisely the actual
canonical degree-two section's chart coefficient. -/
theorem graph_covector_chart (A : Matrix (Cell n) J K) (p : Cell n)
    (φ : Module.Dual K (Matrix (Cell n) J K)) :
    chartLineCoefficient n p 2
      (degreeTwoLineEquiv n (multiplicationOnCovectors A φ))=
        ProjectivePointSpan.chartRestriction A p φ := by
  rw [chartLineCoefficient_degreeTwo,
    ProjectivePointSpan.chartRestriction_eq_multiplicationOnCovectors]

end PaperVerification.Segre.GlobalPolynomialChartRestriction

end SegreGlobalPolynomialChartRestriction

end SegreGlobalCriticalSections

end
end
end ProbeLayer391


/-! Future-only kernel audit for one exported mathematical stage.

Append to the stage being checked, with Lean.Util.CollectAxioms available through
both `public import Lean.Util.CollectAxioms` and `import all Lean.Util.CollectAxioms`
in that stage's header, as required by the reviewed FullFlattenedAudit.

Every new declaration in the checked kernel environment is included: public,
private, generated and vendored declarations receive the same direct-sorry and
transitive-axiom checks. This is evidence for this stage only. Later principal
theorems need not exist yet, and the final full principal audit remains required.

This preparation does not execute the audit, export a module or alter a proof.
-/

open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  unless env.header.trustLevel == 0 do
    throwError "The stage kernel audit requires kernel trust level zero"
  let names := (env.checked.get.constants.foldStage2
    (fun (names : Array Name) name _ => names.push name) #[]).qsort Name.quickLt
  unless names.size > 0 do throwError "The stage mathematical module is empty"
  -- Reject direct proof holes before computing transitive axiom closures.
  -- The complete successful audit below remains unchanged.
  for name in names do
    let some info := env.checked.get.find? name
      | throwError "Authored declaration is not kernel checked: {name}"
    if let .axiomInfo _ := info then throwError "Authored axiom: {name}"
    if info.type.hasSorry || ((info.value? (allowOpaque := true)).any (·.hasSorry)) then
      throwError "Authored declaration contains a sorry expression: {name}"
  let privateEnv := env.setExporting false
  let importedAxioms := exportedAxiomsExt.getState (asyncMode := .mainOnly) env
  -- Match Lean's ordinary export audit, sharing its traversal cache across names.
  let axiomRows := CollectAxioms.runM privateEnv do
    names.mapM fun name =>
      return (name, ← CollectAxioms.collectAndGet importedAxioms.find? name)
  let mut theoremCount : Nat := 0
  for (name, axioms) in axiomRows do
    let some info := env.checked.get.find? name
      | throwError "Authored declaration is not kernel checked: {name}"
    if let .axiomInfo _ := info then throwError "Authored axiom: {name}"
    if info.type.hasSorry || ((info.value? (allowOpaque := true)).any (·.hasSorry)) then
      throwError "Authored declaration contains a sorry expression: {name}"
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unapproved transitive axiom in {name}: {ax}"
    if let .thmInfo _ := info then
      theoremCount := theoremCount + 1
  let report := Json.mkObj [
    ("main_module", toJson env.header.mainModule.toString),
    ("declaration_count", toJson names.size),
    ("theorem_count", toJson theoremCount),
    ("trust_level", toJson env.header.trustLevel.toNat),
    ("allowed_axioms", toJson #["propext", "Classical.choice", "Quot.sound"]),
    ("audit_scope", toJson "current_stage_new_declarations")]
  logInfo m!"SEGRE_STAGE_KERNEL_AUDIT_PASS {report.compress}"
