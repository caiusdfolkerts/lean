module
public import SegreVerified.Stage028.PullbackSections
public import SegreVerified.Stage027.GraphCriticalMap
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
  out.putStrLn "SEGRE_STAGE Stage028.LineSections"
  out.flush

/-!
# Global critical sections and their literal chart equations

The named sections preserve the original proof stages and local scopes.
-/




section SegreActualLineGlobalSections

/-!
# The actual product line H⁰ and the literal critical coordinate sections

The balanced Segre polynomial space is identified with the actual finite
tensor of projection pullbacks used by the critical functionals. On every
coordinate and every pair of coordinates this is the literal finite tensor
section; hence the comparison retains the concrete coefficient structure.

-/


attribute [local instance] MvPolynomial.gradedAlgebra
set_option autoImplicit false

namespace PaperVerification.Segre.ActualLineGlobalSections

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open FixedProductCohomology FixedProductProjections ActualProductKoszulTerms
open HomogeneousExternalSections FinitePullbackSections FiniteGlobalSections
open EulerSheaf EulerCriticalFunctional SheafCoefficientContraction FiniteTensorSections
open Staircase Monomials
open scoped TensorProduct BigOperators

/-- The finite tensor section formula in native scheme-section notation. -/
theorem scheme_sectionMap_one {Y : Scheme} {m : ℕ}
    (M : Fin m → Y.Modules) (s : ∀ i, 𝟙_ Y.Modules ⟶ M i) (U : Y.Opens) :
    (FiniteTensor.sectionMap M s).app U (1 : Γ(Y, U)) =
      finiteTensorSection Y.sheaf M (op U)
        (fun i => (s i).app U (1 : Γ(Y, U))) :=
  sectionMap_one Y.sheaf M s (op U)

variable {K : Type} [Field K] {k : ℕ} (n : Fin (k+1) → ℕ)

local notation "I" => (fun i => Fin (n i+1))
set_option quotPrecheck false in local notation "X" => (product K I).scheme

/-- Evaluating a genuine section morphism at one is additive, through the
actual global-section functor. -/
def evaluateUnit (L : (X).Modules) : (𝟙_ (X).Modules ⟶ L) →+
    ExternalSections.sections K L ⊤ where
  toFun f := f.app ⊤ (1 : Γ(X, ⊤))
  map_zero' := rfl
  map_add' _ _ := rfl

theorem evaluateUnit_apply (L : (X).Modules) (f : 𝟙_ (X).Modules ⟶ L) :
    evaluateUnit (K := K) n L f=f.app ⊤ (1 : Γ(X, ⊤)) := rfl

/-- The actual external-product comparison, on all global sections of the
actual tensor line. -/
def externalLineSectionsEquiv (q : ℕ) :
    ExternalSections.sections K (externalTwist (K := K) n q) ⊤ ≃ₗ[K]
      ExternalSections.sections K (line K I q) ⊤ :=
  (((sectionsBasePresheafFunctor K).mapIso
    (finiteExternalTensorIso (factors (K := K) n) (factorTwist (K := K) n q)
      (fun _ => inferInstance))).app (op ⊤)).toLinearEquiv

/-- The complete balanced polynomial space in any degree is the genuine
H⁰ of the actual product line used by the weighted complex. -/
def balancedLineSectionsEquiv (q : ℕ) :
    HigherPieces.piece (K := K) (n := n) q ≃ₗ[K]
      ExternalSections.sections K (line K I q) ⊤ :=
  (balancedSectionsEquiv (K := K) n q).trans (externalLineSectionsEquiv n q)

def degreeOneLineEquiv : degreeOne (K := K) (n := n) ≃ₗ[K]
    ExternalSections.sections K (line K I 1) ⊤ :=
  (degreeOneSectionsEquiv (K := K) n).trans (externalLineSectionsEquiv n 1)

def degreeTwoLineEquiv : degreeTwo (K := K) (n := n) ≃ₗ[K]
    ExternalSections.sections K (line K I 2) ⊤ :=
  (degreeTwoSectionsEquiv (K := K) n).trans (externalLineSectionsEquiv n 2)

/-- The actual one-coordinate polynomial section in a factor. -/
theorem factorCoordinate_polynomial (i : Fin (k+1)) (a : Fin (n i+1)) :
    Proj.toTwistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n i+1)) K) rfl ⊤
      (coordinatePolynomial (K := K) n i a)=coordinateSection a ⊤ := rfl

/-- A literal product of two coordinate polynomials gives the literal
coordinate-product section in the actual quadratic twist. -/
theorem factorCoordinatePair_polynomial (i : Fin (k+1)) (a b : Fin (n i+1)) :
    Proj.toTwistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n i+1)) K) rfl ⊤
      (coordinatePairPolynomial (K := K) n i a b)=
        coordinateMulSections a 2 ⊤ (coordinateSection b ⊤) := by
  apply Proj.twistingSheaf.ext
  intro x
  simp only [Proj.toTwistingSheaf_apply_apply,coordinatePairPolynomial,
    Localization.mk_one_eq_algebraMap,map_mul,coordinateMulSections_apply,
    coordinateSection_apply]

/-- The actual pulled quadratic-coordinate morphism has the literal
polynomial-product value, with no substitute section chosen. -/
theorem quadraticCoordinate_app_one (i : Fin (k+1)) (a b : Fin (n i+1)) :
    (GraphCriticalMap.quadraticCoordinate I (factorProjection K I) i a b).app ⊤ (1 : Γ(X, ⊤))=
      (factorProjection K I i).pullbackSectionsLE
        (Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n i+1)) K) 2)
        ⊤ ⊤ (by simp)
        (Proj.toTwistingSheaf (MvPolynomial.homogeneousSubmodule (Fin (n i+1)) K) rfl ⊤
          (coordinatePairPolynomial (K := K) n i a b)) := by
  simp only [GraphCriticalMap.quadraticCoordinate,Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply,GraphCriticalMap.coordinateMultiplier]
  rw [GlobalCriticalMap.pullbackCoordinateHom_app_one _ _ ⊤ ⊤ (by simp)]
  erw [Scheme.Hom.pullbackSectionsLE_naturality, factorCoordinatePair_polynomial]
  rfl

/-- Every degree-one Segre coordinate becomes the actual global tensor
coordinate morphism used by the full critical functional. -/
theorem degreeOneLineEquiv_coordinate (a : Cell n) :
    degreeOneLineEquiv (K := K) n
      ⟨cellPolynomial a,Submodule.subset_span (Set.mem_range_self a)⟩=
        (TensorCriticalMap.tensorCoordinate (GlobalCriticalMap.factorLine I (factorProjection K I))
          I (GlobalCriticalMap.factorCoordinate I (factorProjection K I)) a).app ⊤ (1 : Γ(X, ⊤)) := by
  rw [degreeOneLineEquiv,LinearEquiv.trans_apply,
    HomogeneousExternalSections.degreeOneSectionsEquiv_coordinate]
  change (finiteExternalTensorIso (factors (K := K) n) (factorTwist (K := K) n 1)
    (fun _ => inferInstance)).hom.app ⊤
      ((finiteGlobalSectionsIso (factors (K := K) n) (factorTwist (K := K) n 1)
        (fun _ => inferInstance)).hom _) = _
  rw [finiteGlobalSectionsIso_pure,finiteExternalTensorIso_section]
  refine Eq.trans ?_ (scheme_sectionMap_one
    (GlobalCriticalMap.factorLine I (factorProjection K I))
    (fun i => GlobalCriticalMap.factorCoordinate I (factorProjection K I) i (a i)) ⊤).symm
  apply congrArg (finiteTensorSection (X).sheaf
    (GlobalCriticalMap.factorLine I (factorProjection K I)) (op ⊤))
  funext i
  exact (GlobalCriticalMap.pullbackCoordinateHom_app_one
    (factorProjection K I i) (a i) ⊤ ⊤ (by simp)).symm

/-- Every degree-two coordinate product becomes precisely the actual graph
coordinate morphism used by the graph critical functional. -/
theorem degreeTwoLineEquiv_coordinateProduct (a b : Cell n) :
    degreeTwoLineEquiv (K := K) n (TraceGlobalSections.coordinateProduct a b)=
      (GraphCriticalMap.graphCoordinate I (factorProjection K I) a b).app ⊤ (1 : Γ(X, ⊤)) := by
  rw [degreeTwoLineEquiv,LinearEquiv.trans_apply,
    TraceGlobalSections.degreeTwoSectionsEquiv_coordinateProduct]
  change (finiteExternalTensorIso (factors (K := K) n) (factorTwist (K := K) n 2)
    (fun _ => inferInstance)).hom.app ⊤
      ((finiteGlobalSectionsIso (factors (K := K) n) (factorTwist (K := K) n 2)
        (fun _ => inferInstance)).hom _) = _
  rw [finiteGlobalSectionsIso_pure,finiteExternalTensorIso_section]
  refine Eq.trans ?_ (scheme_sectionMap_one
    (GraphCriticalMap.factorQuadraticLine I (factorProjection K I))
    (fun i => GraphCriticalMap.quadraticCoordinate I (factorProjection K I)
      i (a i) (b i)) ⊤).symm
  apply congrArg (finiteTensorSection (X).sheaf
    (GraphCriticalMap.factorQuadraticLine I (factorProjection K I)) (op ⊤))
  funext i
  exact (quadraticCoordinate_app_one n i (a i) (b i)).symm

/-- The actual degree-one coordinate as an element of the complete Segre
degree-one space. -/
def coordinateElement (a : Cell n) : degreeOne (K := K) (n := n) :=
  ⟨cellPolynomial a,Submodule.subset_span (Set.mem_range_self a)⟩

/-- The complete full-format critical polynomial, before choosing any
affine chart or any basis of a relation space. -/
def fullCoordinatePolynomial (T : Cell n → K) (i : Fin (k+1))
    (p q : Fin (n i+1)) : degreeOne (K := K) (n := n) :=
  ∑ a : Cell n,
    ((if a i=q then T a • coordinateElement n (Function.update a i p) else 0) -
      (if a i=p then T a • coordinateElement n (Function.update a i q) else 0))

/-- The whole degree-one critical polynomial becomes the actual global
critical coordinate section, with every original tensor coefficient. -/
theorem degreeOneLineEquiv_fullCoordinatePolynomial (T : Cell n → K)
    (i : Fin (k+1)) (p q : Fin (n i+1)) :
    degreeOneLineEquiv n (fullCoordinatePolynomial n T i p q)=
      (GlobalCriticalMap.criticalCoordinate I (factorProjection K I) T i p q).app ⊤ (1 : Γ(X, ⊤)) := by
  change _=evaluateUnit n (line K I 1)
    (GlobalCriticalMap.criticalCoordinate I (factorProjection K I) T i p q)
  rw [GlobalCriticalMap.criticalCoordinate_expansion]
  have hscalar (c : K) (s : ExternalSections.sections K
      (GlobalCriticalMap.tensorLine I (factorProjection K I)) ⊤) :
      (GlobalCriticalMap.scalarEndomorphism I (factorProjection K I) c).app ⊤ s=c • s := by
    have h := sectionsBasePresheafFunctor_map_globalSectionsSmul K (line K I 1) c
    exact ConcreteCategory.congr_hom (congrArg (fun f => f.app (op ⊤)) h) s
  simp only [fullCoordinatePolynomial,map_sum,map_sub,apply_ite,_root_.map_smul,map_zero,
    coordinateElement,degreeOneLineEquiv_coordinate,evaluateUnit_apply,
    Scheme.Modules.Hom.comp_app,ConcreteCategory.comp_apply,hscalar]
  apply Finset.sum_congr rfl
  intro a _
  split_ifs <;> congr 1 <;> exact (hscalar _ _).symm

/-- The actual finite coefficient expansion of a graph critical polynomial,
in the complete balanced degree-two space. -/
def graphCoordinatePolynomial {J : Type} [Fintype J]
    (T : J → Cell n → K) (i : Fin (k+1)) (p q : Fin (n i+1)) :
    degreeTwo (K := K) (n := n) :=
  (∑ r : J, ∑ a : Cell n, ∑ b : Cell n,
    if b i=q then (T r a*T r b) •
      TraceGlobalSections.coordinateProduct a (Function.update b i p) else 0) -
  (∑ r : J, ∑ a : Cell n, ∑ b : Cell n,
    if b i=p then (T r a*T r b) •
      TraceGlobalSections.coordinateProduct a (Function.update b i q) else 0)

/-- The entire graph critical polynomial maps to the actual global
critical coordinate section, with every coefficient and sign retained. -/
theorem degreeTwoLineEquiv_graphCoordinatePolynomial {J : Type} [Fintype J]
    (T : J → Cell n → K) (i : Fin (k+1)) (p q : Fin (n i+1)) :
    degreeTwoLineEquiv n (graphCoordinatePolynomial n T i p q)=
      (GraphCriticalMap.graphCriticalCoordinate I (factorProjection K I) T i p q).app ⊤ (1 : Γ(X, ⊤)) := by
  change _=evaluateUnit n (line K I 2)
    (GraphCriticalMap.graphCriticalCoordinate I (factorProjection K I) T i p q)
  rw [GraphCriticalMap.graphCriticalCoordinate_expansion]
  have hscalar (c : K) (s : ExternalSections.sections K
      (GraphCriticalMap.graphLine I (factorProjection K I)) ⊤) :
      (GraphCriticalMap.graphScalarEndomorphism I (factorProjection K I) c).app ⊤ s=c • s := by
    have h := sectionsBasePresheafFunctor_map_globalSectionsSmul K (line K I 2) c
    exact ConcreteCategory.congr_hom (congrArg (fun f => f.app (op ⊤)) h) s
  simp only [graphCoordinatePolynomial,map_sub,map_sum,apply_ite,_root_.map_smul,map_zero,
    degreeTwoLineEquiv_coordinateProduct,evaluateUnit_apply,Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply,hscalar]
  apply congrArg₂ (· - ·)
  all_goals
    apply Finset.sum_congr rfl
    intro r _
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    split_ifs <;> first | rfl | exact (hscalar _ _).symm

end PaperVerification.Segre.ActualLineGlobalSections

end SegreActualLineGlobalSections

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
