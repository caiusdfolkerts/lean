module
public import SegreVerified.Stage028.GraphElimination
public import SegreVerified.Stage027.CriticalCoordinates
public import SegreVerified.Stage025.EulerCoordinates
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
  out.putStrLn "SEGRE_STAGE Stage028.CriticalPolynomials"
  out.flush

/-!
# Global critical sections and their literal chart equations

The named sections preserve the original proof stages and local scopes.
-/



section SegreProductCoordinateSections

/-!
# Actual product coordinate sections in the canonical affine frames

The comparisons here evaluate the actual finite tensor of pulled projective
coordinates in the actual local line trivialization. Both the linear and
quadratic formulas retain every factor, the terminal monoidal unit, and the
original coefficient-ring structure map.

-/

set_option autoImplicit false
open scoped Classical BigOperators TensorProduct

namespace PaperVerification.Segre.ProductCoordinateSections

attribute [local instance] MvPolynomial.gradedAlgebra

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open ActualProductKoszulTerms ActualProductChartFrames
open FixedProductCohomology ProductKoszulVanishing ProductCoordinatePullback
open SheafCoefficientContraction FiniteTensorSections
open scoped ProjectiveChartSections ProductChartSections

universe u

section FiniteTensors

variable {Y : Scheme.{u}} (U : Y.Opens)

/-- The finite coordinate section map evaluates to its actual pure section. -/
theorem scheme_sectionMap_one {l : ℕ} (M : Fin l → Y.Modules)
    (s : ∀ i, 𝟙_ Y.Modules ⟶ M i) :
    (FiniteTensor.sectionMap M s).app U (1 : Γ(Y,U)) =
      finiteTensorSection Y.sheaf M (op U) (fun i => (s i).app U (1 : Γ(Y,U))) :=
  sectionMap_one Y.sheaf M s (op U)

/-- Scalar multiplication in each factor is the actual bilinearity of the
canonical sheaf tensor-section map. -/
theorem tensorSection_smul_smul (M N : Y.Modules)
    (a b : Γ(Y,U)) (m : Γ(M,U)) (n : Γ(N,U)) :
    tensorSection Y.sheaf M N (op U) (a • m) (b • n)=
      (a*b) • tensorSection Y.sheaf M N (op U) m n := by
  unfold tensorSection
  rw [TensorProduct.smul_tmul_smul]
  exact _root_.map_smul _ _ _

/-- A finite pure tensor scales by the product of the original factor scalars. -/
theorem finiteTensorSection_smul {l : ℕ} (M : Fin l → Y.Modules)
    (a : Fin l → Γ(Y,U)) (m : ∀ i,Γ(M i,U)) :
    finiteTensorSection Y.sheaf M (op U) (fun i => a i • m i)=
      (∏ i,a i) • finiteTensorSection Y.sheaf M (op U) m := by
  induction l with
  | zero => simp only [finiteTensorSection,Fin.prod_univ_zero,one_smul]
  | succ l ih =>
      simp only [finiteTensorSection]
      rw [ih,tensorSection_smul_smul,Fin.prod_univ_succ]

/-- The inverse of the actual affine finite-tensor frame evaluates a pure
section as the product of its actual individual frame coefficients. -/
theorem finiteTensorFrame_symm_pure (hU : IsAffineOpen U) {l : ℕ}
    (M : Fin l → Y.Modules) (hM : ∀ i,(M i).IsQuasicoherent)
    (e : ∀ i,Γ(Y,U) ≃ₗ[Γ(Y,U)] Γ(M i,U)) (m : ∀ i,Γ(M i,U)) :
    (finiteTensorFrame hU M hM e).symm
      (finiteTensorSection Y.sheaf M (op U) m)=∏ i,(e i).symm (m i) := by
  have hm : m=(fun i => (e i).symm (m i) • e i 1) := by
    funext i
    rw [← _root_.map_smul]
    simp only [smul_eq_mul,mul_one,LinearEquiv.apply_symm_apply]
  conv_lhs => rw [hm]
  rw [finiteTensorSection_smul,← finiteTensorFrame_one hU M hM e,_root_.map_smul,
    LinearEquiv.symm_apply_apply,smul_eq_mul,mul_one]

/-- The original base scalar endomorphism acts through the actual algebra
map to the coordinate ring of the chosen open. -/
theorem baseScalarEndomorphism_app (M : Y.Modules) (K : Type u) [Field K]
    [Y.Over (Spec (.of K))] (c : K) (s : Γ(M,U)) :
    (globalSectionsSmul M (baseRingToGlobalSections K Y c)).app U s=
      algebraMap K Γ(Y,U) c • s := by
  rw [globalSectionsSmul_app]
  change Y.presheaf.map U.leTop.op (baseRingToGlobalSections K Y c) • s =
    (Y.baseRingToStructurePresheaf K).app (op U) c • s
  erw [Scheme.baseRingToStructurePresheaf_app, CommRingCat.comp_apply,
    CommRingCat.ofHom_apply]

end FiniteTensors

variable (K : Type u) [Field K] {k : ℕ}
variable (I : Fin (k+1) → Type u)
variable [∀ i,Fintype (I i)] [∀ i,DecidableEq (I i)]

set_option quotPrecheck false in local notation "X" => (product K I).scheme

/-- The genuine quadratic coordinate has the product of its two normalized
coordinate ratios as its coefficient in the actual pulled-back O(2) frame. -/
theorem factorLineFrame_quadraticCoordinate (p : ∀ i,I i)
    (i : Fin (k+1)) (a b : I i) :
    (factorLineFrame K I p i 2).symm
      ((GraphCriticalMap.quadraticCoordinate I (factorProjection K I) i a b).app
        (chart K I p) (1 : Γ(X,chart K I p)))=
      factorRestriction (fun j => projectiveScheme K (I j)) p i
        (EulerCriticalChart.normalizedCoordinate (p i)
          (ProjectiveCech.coordinateOpen (K := K) (p i)) le_rfl a)*
      factorRestriction (fun j => projectiveScheme K (I j)) p i
        (EulerCriticalChart.normalizedCoordinate (p i)
          (ProjectiveCech.coordinateOpen (K := K) (p i)) le_rfl b) := by
  let U := ProjectiveCech.coordinateOpen (K := K) (p i)
  let h : chart K I p ≤ (factorProjection K I i) ⁻¹ᵁ U :=
    finiteChart_le_preimage (fun j => projectiveScheme K (I j)) p i
  let e := EulerCriticalChart.chartTrivialization (p i) U le_rfl 2
  have he : EulerSheaf.coordinateMulSections a 2 U
      (EulerSheaf.coordinateSection b U)=
      e (EulerCriticalChart.normalizedCoordinate (p i) U le_rfl a*
        EulerCriticalChart.normalizedCoordinate (p i) U le_rfl b) := by
    apply e.symm.injective
    rw [LinearEquiv.symm_apply_apply,EulerCriticalChart.normalized_coordinateMul]
    rfl
  apply (factorLineFrame K I p i 2).injective
  rw [LinearEquiv.apply_symm_apply,← map_mul,factorLineFrame_pullback]
  change ((Scheme.Modules.pullback (factorProjection K I i)).map (EulerSheaf.coordinateMul a 2)).app
      (chart K I p)
      ((GlobalCriticalMap.pullbackCoordinateHom (factorProjection K I i) b).app
        (chart K I p) (1 : Γ(X,chart K I p)))=_
  rw [GlobalCriticalMap.pullbackCoordinateHom_app_one (factorProjection K I i) b U
    (chart K I p) h]
  erw [Scheme.Hom.pullbackSectionsLE_naturality]
  change (factorProjection K I i).pullbackSectionsLE _ U (chart K I p) h
      (EulerSheaf.coordinateMulSections a 2 U (EulerSheaf.coordinateSection b U))=_
  rw [he]

/-- Every actual full tensor coordinate evaluates to the product of the
normalized coordinates in the original factors. -/
theorem lineFrame_tensorCoordinate (p : ∀ i,I i) (a : ∀ i,I i) :
    lineFrame K I p 1
      ((TensorCriticalMap.tensorCoordinate
        (GlobalCriticalMap.factorLine I (factorProjection K I)) I
        (GlobalCriticalMap.factorCoordinate I (factorProjection K I)) a).app
          (chart K I p) (1 : Γ(X,chart K I p)))=
      ∏ i,factorRestriction (fun j => projectiveScheme K (I j)) p i
        (EulerCriticalChart.normalizedCoordinate (p i)
          (ProjectiveCech.coordinateOpen (K := K) (p i)) le_rfl (a i)) := by
  let M := fun i => (Scheme.Modules.pullback (factorProjection K I i)).obj
    (Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (I i) K) 1)
  letI : ∀ i, (Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (I i) K) (1 : ℤ)).IsQuasicoherent :=
    fun i => Proj.isQuasicoherent_twistingSheaf _ _
  have hM : ∀ i, (M i).IsQuasicoherent := fun i => inferInstance
  change (finiteTensorFrame (chart_affine K I p) M hM
    (fun i => factorLineFrame K I p i 1)).symm
      ((FiniteTensor.sectionMap M (fun i => GlobalCriticalMap.factorCoordinate I (factorProjection K I) i (a i))).app (chart K I p)
        (1 : Γ(X,chart K I p))) = _
  rw [scheme_sectionMap_one, finiteTensorFrame_symm_pure]
  apply Finset.prod_congr rfl
  intro i _
  exact factorLineFrame_coordinate K I p i (a i)

/-- The genuine graph coordinate evaluates to the product of the original
two coordinates in every factor, without any characteristic restriction. -/
theorem lineFrame_graphCoordinate (p : ∀ i,I i) (a b : ∀ i,I i) :
    lineFrame K I p 2
      ((GraphCriticalMap.graphCoordinate I (factorProjection K I) a b).app
        (chart K I p) (1 : Γ(X,chart K I p)))=
      ∏ i,(factorRestriction (fun j => projectiveScheme K (I j)) p i
        (EulerCriticalChart.normalizedCoordinate (p i)
          (ProjectiveCech.coordinateOpen (K := K) (p i)) le_rfl (a i)))*
        (factorRestriction (fun j => projectiveScheme K (I j)) p i
          (EulerCriticalChart.normalizedCoordinate (p i)
            (ProjectiveCech.coordinateOpen (K := K) (p i)) le_rfl (b i))) := by
  let M := fun i => (Scheme.Modules.pullback (factorProjection K I i)).obj
    (Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (I i) K) 2)
  letI : ∀ i, (Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (I i) K) (2 : ℤ)).IsQuasicoherent :=
    fun i => Proj.isQuasicoherent_twistingSheaf _ _
  have hM : ∀ i, (M i).IsQuasicoherent := fun i => inferInstance
  change (finiteTensorFrame (chart_affine K I p) M hM
    (fun i => factorLineFrame K I p i 2)).symm
      ((FiniteTensor.sectionMap M (fun i => GraphCriticalMap.quadraticCoordinate I (factorProjection K I) i (a i) (b i))).app (chart K I p)
        (1 : Γ(X,chart K I p))) = _
  rw [scheme_sectionMap_one, finiteTensorFrame_symm_pure]
  apply Finset.prod_congr rfl
  intro i _
  exact factorLineFrame_quadraticCoordinate K I p i (a i) (b i)

end PaperVerification.Segre.ProductCoordinateSections

end SegreProductCoordinateSections

section SegreCriticalCoordinateExpansion

/-!
# Complete tensor-entry expansions of the literal chart equations

These finite-sum identities compare the full sheaf-functional coordinate
expressions with the independently defined singular-vector chart equations.
All entries, all slices, and all factors occur. The sign is fixed explicitly:
the Euler wedge `(a,b)` gives the critical operator coordinate `(b,a)`.

-/

set_option autoImplicit false
open scoped Classical BigOperators

namespace PaperVerification.Segre.CriticalCoordinateExpansion

open Staircase Monomials Degeneration GraphSpan CriticalGraph SingularSpan
open ProjectiveCharts ProjectivePointSpan

variable {I J K : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Field K] {n : I → ℕ}

/-- Updating the distinguished factor leaves precisely the original other
coordinates, including in dependent factor families. -/
theorem update_assemble (i : I) (a b : Fin (n i+1)) (w : OtherCell n i) :
    Function.update (assemble i b w) i a=assemble i a w := by
  funext j
  by_cases hj : j=i
  · subst j
    simp
  · rw [Function.update_of_ne hj]
    exact (assemble_other i b w ⟨j,hj⟩).trans (assemble_other i a w ⟨j,hj⟩).symm

/-- A full tensor-index sum with one fixed coordinate is exactly the sum
over all the other coordinates. No tensor entry is suppressed. -/
theorem sum_update_fiber {R : Type*} [CommRing R]
    (F G : Cell n → R) (i : I) (a b : Fin (n i+1)) :
    (∑ v : Cell n,if v i=b then F v*G (Function.update v i a) else 0)=
      ∑ w : OtherCell n i,F (assemble i b w)*G (assemble i a w) := by
  rw [← Equiv.sum_comp (Equiv.piSplitAt i (fun j => Fin (n j+1))).symm,
    Fintype.sum_prod_type,Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro w _
  have hsplit (c : Fin (n i+1)) :
      (Equiv.piSplitAt i (fun j => Fin (n j+1))).symm (c,w) =
        assemble i c w := rfl
  simp [hsplit,assemble_same,update_assemble]

/-- The actual product of normalized factor coordinates. -/
def normalizedMonomial (p v : Cell n) : MvPolynomial (ChartVar p) K :=
  ∏ i,chartPolynomial p ⟨i,v i⟩

theorem normalizedMonomial_eq_substitution (p v : Cell n) :
    normalizedMonomial (K := K) p v=chartSubstitution p (cellPolynomial v) := by
  rw [cellPolynomial_eq_prod,map_prod]
  simp only [normalizedMonomial,chartSubstitution,MvPolynomial.aeval_X]

@[simp] theorem eval_normalizedMonomial (p v : Cell n) (z : ChartVar p → K) :
    MvPolynomial.eval z (normalizedMonomial p v)=
      MvPolynomial.eval (chartVector p z) (cellPolynomial (K := K) v) := by
  rw [normalizedMonomial_eq_substitution,eval_chartSubstitution]

/-- Complete coefficient formula of the actual full critical section. -/
def fullCoordinatePolynomial (T : Cell n → K) (p : Cell n)
    (i : I) (a b : Fin (n i+1)) : MvPolynomial (ChartVar p) K :=
  ∑ v : Cell n,
    ((if v i=b then MvPolynomial.C (T v)*normalizedMonomial p (Function.update v i a)
      else 0)-
     (if v i=a then MvPolynomial.C (T v)*normalizedMonomial p (Function.update v i b)
      else 0))

/-- Exact sign and all-coordinate agreement with the independently defined
full critical operator on the genuine Segre chart. -/
theorem fullCoordinatePolynomial_eq_critical [Infinite K]
    (T : Cell n → K) (p : Cell n) (i : I) (a b : Fin (n i+1)) :
    fullCoordinatePolynomial T p i a b=
      AllFactorPointSpan.chartCriticalPolynomial (AllFactorIncidence.unitTensorEquiv T)
        p ⟨i,(b,a)⟩ := by
  rw [fullCoordinatePolynomial,Finset.sum_sub_distrib,sum_update_fiber,sum_update_fiber]
  apply MvPolynomial.funext
  intro z
  simp only [map_sub,map_sum,map_mul,MvPolynomial.eval_C,eval_normalizedMonomial,
    AllFactorPointSpan.eval_chartCriticalPolynomial]
  change (∑ w : OtherCell n i,T (assemble i b w)*
      MvPolynomial.eval (chartVector p z) (cellPolynomial (assemble i a w)))-
    (∑ w : OtherCell n i,T (assemble i a w)*
      MvPolynomial.eval (chartVector p z) (cellPolynomial (assemble i b w)))=_
  simp only [criticalOperator,AllFactorIncidence.unitTensorEquiv,rankOneTensor,
    AllFactorPointSpan.unitVector,Fintype.sum_unique,mul_one,
    Finset.sum_sub_distrib]
  change _ =
    (∑ w : OtherCell n i, T (assemble i b w) *
      (MvPolynomial.eval (chartVector p z) (cellPolynomial (assemble i a w)) * (1 : K))) -
    (∑ w : OtherCell n i, T (assemble i a w) *
      (MvPolynomial.eval (chartVector p z) (cellPolynomial (assemble i b w)) * (1 : K)))
  simp only [mul_one]

/-- Graph coordinates retain the complete original last-factor contraction. -/
theorem chartGraphCoordinate_eq_sum [Infinite K]
    (A : Matrix (Cell n) J K) (p v : Cell n) (j : J) :
    chartGraphCoordinate A p v j=
      ∑ a : Cell n,MvPolynomial.C (A a j)*
        (normalizedMonomial p a*normalizedMonomial p v) := by
  apply MvPolynomial.funext
  intro z
  rw [eval_chartGraphCoordinate,graphTensor,eval_segreForm]
  simp only [map_sum,map_mul,MvPolynomial.eval_C,eval_normalizedMonomial,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  ring

/-- The complete quadratic tensor-entry sum is exactly one contraction term
of the graph critical operator. -/
theorem graph_half_sum [Infinite K] (A : Matrix (Cell n) J K)
    (p : Cell n) (i : I) (a b : Fin (n i+1)) :
    (∑ r : J,∑ v : Cell n,∑ w : Cell n,
      if w i=b then MvPolynomial.C (A v r*A w r)*
        (normalizedMonomial p v*normalizedMonomial p (Function.update w i a)) else 0)=
      ∑ w : OtherCell n i,∑ r : J,
        MvPolynomial.C (A (assemble i b w) r)*chartGraphCoordinate A p (assemble i a w) r := by
  have hsum (r : J) (v : Cell n) :
      (∑ w : Cell n, if w i=b then MvPolynomial.C (A v r*A w r)*
        (normalizedMonomial p v*normalizedMonomial p (Function.update w i a)) else 0) =
      ∑ w : OtherCell n i, MvPolynomial.C (A v r*A (assemble i b w) r)*
        (normalizedMonomial p v*normalizedMonomial p (assemble i a w)) := by
    calc
      _ = ∑ w : Cell n, if w i=b then
          (MvPolynomial.C (A v r*A w r)*normalizedMonomial p v)*
            normalizedMonomial p (Function.update w i a) else 0 := by
        apply Finset.sum_congr rfl
        intro w _
        split_ifs
        · exact (mul_assoc _ _ _).symm
        · rfl
      _ = ∑ w : OtherCell n i,
          (MvPolynomial.C (A v r*A (assemble i b w) r)*normalizedMonomial p v)*
            normalizedMonomial p (assemble i a w) :=
        sum_update_fiber (R := MvPolynomial (ChartVar p) K)
          (fun w => MvPolynomial.C (A v r*A w r)*normalizedMonomial p v)
          (fun w => normalizedMonomial p w) i a b
      _ = _ := by
        apply Finset.sum_congr rfl
        intro w _
        exact mul_assoc _ _ _
  simp_rw [hsum]
  calc
    (∑ r : J,∑ v : Cell n,∑ w : OtherCell n i,
      MvPolynomial.C (A v r*A (assemble i b w) r)*
        (normalizedMonomial p v*normalizedMonomial p (assemble i a w)))=
      ∑ r : J,∑ w : OtherCell n i,∑ v : Cell n,
        MvPolynomial.C (A v r*A (assemble i b w) r)*
          (normalizedMonomial p v*normalizedMonomial p (assemble i a w)) := by
            apply Finset.sum_congr rfl
            intro r _
            rw [Finset.sum_comm]
    _ = ∑ w : OtherCell n i,∑ r : J,∑ v : Cell n,
        MvPolynomial.C (A v r*A (assemble i b w) r)*
          (normalizedMonomial p v*normalizedMonomial p (assemble i a w)) :=
      Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro w _
      apply Finset.sum_congr rfl
      intro r _
      rw [chartGraphCoordinate_eq_sum,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro v _
      rw [map_mul]
      ring

/-- Complete coefficient formula of the actual graph critical section. -/
def graphCoordinatePolynomial (A : Matrix (Cell n) J K) (p : Cell n)
    (i : I) (a b : Fin (n i+1)) : MvPolynomial (ChartVar p) K :=
  (∑ r : J,∑ v : Cell n,∑ w : Cell n,
    if w i=b then MvPolynomial.C (A v r*A w r)*
      (normalizedMonomial p v*normalizedMonomial p (Function.update w i a)) else 0)-
  (∑ r : J,∑ v : Cell n,∑ w : Cell n,
    if w i=a then MvPolynomial.C (A v r*A w r)*
      (normalizedMonomial p v*normalizedMonomial p (Function.update w i b)) else 0)

/-- Exact graph coordinate agreement, including every original last-factor
slice and the original alternating sign. -/
theorem graphCoordinatePolynomial_eq_critical [Infinite K]
    (A : Matrix (Cell n) J K) (p : Cell n) (i : I) (a b : Fin (n i+1)) :
    graphCoordinatePolynomial A p i a b=
      chartCriticalPolynomial A p ⟨i,(b,a)⟩ := by
  rw [graphCoordinatePolynomial,graph_half_sum,graph_half_sum,chartCriticalPolynomial]
  simp only [Finset.sum_sub_distrib]

end PaperVerification.Segre.CriticalCoordinateExpansion

end SegreCriticalCoordinateExpansion

section SegreActualCriticalPolynomial

/-!
# The genuine sheaf critical coefficients are the literal chart polynomials

The coefficient map starts with the actual critical morphism, the actual
Euler-kernel source frame, and the actual projective line frame. Its final
coordinate-ring identification is the independently constructed isomorphism
from genuine product-chart sections to the off-pivot polynomial ring.

The endpoint equations identify this entire construction with every original
full or graph pivot critical polynomial. They therefore permit transport of
the entire defining ideal, including its nilpotent scheme structure.

-/

set_option autoImplicit false
open scoped Classical BigOperators

namespace PaperVerification.Segre.ActualCriticalPolynomial

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open Staircase Monomials Degeneration CriticalGraph
open ProjectiveCharts ProjectivePointSpan CriticalCoordinateExpansion
open ActualProductKoszulTerms ActualProductChartFrames ActualCriticalFrame
open ProductCoordinateSections ProductCoordinatePullback ProductChartSections
open scoped ProjectiveChartSections ProductChartSections

variable (K : Type) [Field K] {k : ℕ} (n : Fin (k+1) → ℕ)

local notation "I" => (fun i : Fin (k+1) => Fin (n i+1))
set_option quotPrecheck false in local notation "X" => (product K I).scheme

/-- Evaluate an actual line-valued section morphism at one, express it in
the canonical line frame, and apply the genuine chart-ring isomorphism. -/
def polynomialSection (p : Cell n) (t : ℤ) :
    (𝟙_ (X).Modules ⟶ line K I t) →+ MvPolynomial (ChartVar p) K where
  toFun s := numericalProductChartSectionsEquiv n p
    (lineFrame K I p t (s.app (chart K I p) (1 : Γ(X,chart K I p))))
  map_zero' := by
    change numericalProductChartSectionsEquiv n p (lineFrame K I p t 0)=0
    rw [map_zero,map_zero]
  map_add' s t' := by
    rw [Scheme.Modules.Hom.add_app]
    change numericalProductChartSectionsEquiv n p
      (lineFrame K I p t (s.app (chart K I p) (1 : Γ(X,chart K I p))+t'.app (chart K I p) (1 : Γ(X,chart K I p))))=_
    rw [map_add,map_add]

/-- Original tensor coefficients are constants under the actual chart
algebra isomorphism; the scalar action is the scheme's structure map. -/
theorem polynomialSection_scalar_postcomp (p : Cell n) (t : ℤ)
    (s : 𝟙_ (X).Modules ⟶ line K I t) (c : K) :
    polynomialSection K n p t
      (s ≫ globalSectionsSmul (line K I t) (baseRingToGlobalSections K X c))=
      MvPolynomial.C c*polynomialSection K n p t s := by
  change numericalProductChartSectionsEquiv n p
    (lineFrame K I p t
      ((globalSectionsSmul (line K I t) (baseRingToGlobalSections K X c)).app
        (chart K I p) (s.app (chart K I p) (1 : Γ(X,chart K I p)))))=_
  rw [baseScalarEndomorphism_app,_root_.map_smul,smul_eq_mul,map_mul,AlgEquiv.commutes]
  rfl

/-- Every genuine degree-one tensor coordinate has its original literal
normalized monomial, with all projective factors included. -/
theorem polynomialSection_tensorCoordinate (p a : Cell n) :
    polynomialSection K n p 1
      (TensorCriticalMap.tensorCoordinate
        (GlobalCriticalMap.factorLine I (factorProjection K I)) I
        (GlobalCriticalMap.factorCoordinate I (factorProjection K I)) a)=
      normalizedMonomial p a := by
  change numericalProductChartSectionsEquiv n p
    (lineFrame K I p 1
      ((TensorCriticalMap.tensorCoordinate
        (GlobalCriticalMap.factorLine I (factorProjection K I)) I
        (GlobalCriticalMap.factorCoordinate I (factorProjection K I)) a).app (chart K I p) (1 : Γ(X,chart K I p))))=_
  rw [lineFrame_tensorCoordinate,map_prod]
  apply Finset.prod_congr rfl
  intro i _
  rw [EulerPolynomialCoordinates.normalizedCoordinate_eq_fraction,
    numericalProductChartSectionsEquiv_coordinate]

/-- Every genuine quadratic graph coordinate has the product of the two
original normalized tensor monomials. -/
theorem polynomialSection_graphCoordinate (p a b : Cell n) :
    polynomialSection K n p 2
      (GraphCriticalMap.graphCoordinate I (factorProjection K I) a b)=
      normalizedMonomial p a*normalizedMonomial p b := by
  change numericalProductChartSectionsEquiv n p
    (lineFrame K I p 2
      ((GraphCriticalMap.graphCoordinate _ _ a b).app (chart K I p) (1 : Γ(X,chart K I p))))=_
  rw [lineFrame_graphCoordinate,map_prod]
  simp only [map_mul,EulerPolynomialCoordinates.normalizedCoordinate_eq_fraction,
    numericalProductChartSectionsEquiv_coordinate]
  exact Finset.prod_mul_distrib

/-- Full sheaf coordinate expansion, before any zero-locus or radical
argument, is exactly its complete original tensor-entry polynomial. -/
theorem fullCoordinate_polynomial (T : Cell n → K) (p : Cell n)
    (i : Fin (k+1)) (a b : Fin (n i+1)) :
    polynomialSection K n p 1
      (GlobalCriticalMap.criticalCoordinate I (factorProjection K I) T i a b)=
      fullCoordinatePolynomial T p i a b := by
  have hscalar (s : 𝟙_ (X).Modules ⟶ GlobalCriticalMap.tensorLine I (factorProjection K I)) (c : K) :
      polynomialSection K n p 1
        (s ≫ globalSectionsSmul (GlobalCriticalMap.tensorLine I (factorProjection K I))
          (baseRingToGlobalSections K X c)) =
        MvPolynomial.C c * polynomialSection K n p 1 s :=
    polynomialSection_scalar_postcomp K n p 1 s c
  rw [GlobalCriticalMap.criticalCoordinate_expansion]
  simp only [map_sum,map_sub,apply_ite,map_zero,
    GlobalCriticalMap.scalarEndomorphism,hscalar,
    polynomialSection_tensorCoordinate,fullCoordinatePolynomial]

variable {J : Type} [Fintype J] [DecidableEq J]

/-- Graph sheaf coordinate expansion retains every slice and every pair of
original tensor entries. No quadratic derivative or division by two occurs. -/
theorem graphCoordinate_polynomial (A : Matrix (Cell n) J K) (p : Cell n)
    (i : Fin (k+1)) (a b : Fin (n i+1)) :
    polynomialSection K n p 2
      (GraphCriticalMap.graphCriticalCoordinate I (factorProjection K I)
        (fun j v => A v j) i a b)=graphCoordinatePolynomial A p i a b := by
  have hscalar (s : 𝟙_ (X).Modules ⟶ GraphCriticalMap.graphLine I (factorProjection K I)) (c : K) :
      polynomialSection K n p 2
        (s ≫ globalSectionsSmul (GraphCriticalMap.graphLine I (factorProjection K I))
          (baseRingToGlobalSections K X c)) =
        MvPolynomial.C c * polynomialSection K n p 2 s :=
    polynomialSection_scalar_postcomp K n p 2 s c
  rw [GraphCriticalMap.graphCriticalCoordinate_expansion]
  simp only [map_sub,map_sum,apply_ite,map_zero,
    GraphCriticalMap.graphScalarEndomorphism,hscalar,
    polynomialSection_graphCoordinate,graphCoordinatePolynomial]

/-- The actual full critical functional has precisely the literal original
pivot coefficient on every actual normalized product chart. -/
theorem fullCoefficient_polynomial [Infinite K]
    (T : Cell n → K) (p : Cell n) (q : ChartVar p) :
    numericalProductChartSectionsEquiv n p
      (ActualCriticalFrame.fullCoefficient K I T p ((chartVarEquiv p) q))=
      AllFactorPointSpan.pivotCriticalPolynomial (AllFactorIncidence.unitTensorEquiv T) p q := by
  change polynomialSection K n p 1
    (GlobalCriticalMap.criticalCoordinate I (factorProjection K I) T
      q.val.1 (p q.val.1) q.val.2)=_
  rw [fullCoordinate_polynomial,fullCoordinatePolynomial_eq_critical]
  rfl

/-- The actual graph critical functional has precisely the original pivot
polynomial in every chart, with the full parameter and characteristic range. -/
theorem graphCoefficient_polynomial [Infinite K]
    (A : Matrix (Cell n) J K) (p : Cell n) (q : ChartVar p) :
    numericalProductChartSectionsEquiv n p
      (ActualCriticalFrame.graphCoefficient K I (fun j v => A v j) p
        ((chartVarEquiv p) q))=
      ProjectivePointSpan.pivotCriticalPolynomial A p q := by
  change polynomialSection K n p 2
    (GraphCriticalMap.graphCriticalCoordinate I (factorProjection K I)
      (fun j v => A v j) q.val.1 (p q.val.1) q.val.2)=_
  rw [graphCoordinate_polynomial,graphCoordinatePolynomial_eq_critical]
  rfl

end PaperVerification.Segre.ActualCriticalPolynomial

end SegreActualCriticalPolynomial

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
