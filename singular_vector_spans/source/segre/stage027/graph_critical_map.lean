module
public import SegreVerified.Stage027.ProductTerms
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


section SegreCriticalBundleGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

run_cmd do
  let out ← IO.getStderr
  out.putStrLn "SEGRE_STAGE Stage027.GraphCriticalMap"
  out.flush

/-!
# The actual critical bundle and its weighted Koszul complex

The named sections preserve the original proof stages and local scopes.
-/

set_option autoImplicit false

section SegreGraphCriticalMap

/-!
# The actual graph-format critical functional

For a full family of multilinear forms `T r`, the graph coefficient is the
literal sum of `f_r` times its i-th coordinate contraction. The target is
the actual tensor product of the pulled-back O(2) line bundles. The source
of each factor coefficient remains the pulled-back O(1), so restricting to
the actual positive Euler kernel yields the graph-format critical map.

Every pair of tensor entries and every final-factor coordinate is included.
The coordinate formula uses no division by two and holds in every
characteristic.
-/

set_option autoImplicit false

attribute [local instance] MvPolynomial.gradedAlgebra

namespace PaperVerification.Segre.GraphCriticalMap

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open EulerSheaf EulerSections EulerCriticalFunctional GlobalCriticalMap
open scoped BigOperators

universe u
variable {K : Type u} [Field K] {k : ℕ} (J : Fin k → Type u)
variable [∀ i, Fintype (J i)] [∀ i, DecidableEq (J i)]
variable {P : Scheme.{u}} [P.Over (Spec (.of K))]
variable (f : (i : Fin k) → P ⟶ Proj (MvPolynomial.homogeneousSubmodule (J i) K))
variable {R : Type u} [Fintype R]

/-- The literal pulled-back quadratic twisting line on each small factor. -/
def factorQuadraticLine (i : Fin k) : P.Modules :=
  (Scheme.Modules.pullback (f i)).obj (Proj.twistingSheaf
    (MvPolynomial.homogeneousSubmodule (J i) K) (2 : ℤ))

/-- The genuine graph-format target O(2,...,2). -/
def graphLine : P.Modules := FiniteTensor.tensorObj (factorQuadraticLine J f)

/-- Actual multiplication of the input linear section by one coordinate. -/
def coordinateMultiplier (i : Fin k) (a : J i) :
    factorLine J f i ⟶ factorQuadraticLine J f i :=
  (Scheme.Modules.pullback (f i)).map (coordinateMul (K := K) a 2)

/-- The actual quadratic coordinate section x_a x_b. -/
def quadraticCoordinate (i : Fin k) (a b : J i) :
    𝟙_ P.Modules ⟶ factorQuadraticLine J f i :=
  pullbackCoordinateHom (f i) b ≫ coordinateMultiplier J f i a

/-- The full quadratic tensor coordinate, with all factors present. -/
def graphCoordinate (a b : (i : Fin k) → J i) : 𝟙_ P.Modules ⟶ graphLine J f :=
  FiniteTensor.sectionMap (factorQuadraticLine J f)
    (fun i => quadraticCoordinate J f i (a i) (b i))

/-- Insert the genuine coordinate-multiplication map into the full quadratic tensor. -/
def graphInsertion (a b : (i : Fin k) → J i) (i : Fin k) :
    factorLine J f i ⟶ graphLine J f :=
  FiniteTensor.insertMap (factorQuadraticLine J f)
    (fun j => quadraticCoordinate J f j (a j) (b j)) i
      (coordinateMultiplier J f i (a i))

/-- Actual evaluation replaces only the second coordinate at the input factor. -/
theorem coordinate_comp_graphInsertion (a b : (i : Fin k) → J i)
    (i : Fin k) (p : J i) :
    pullbackCoordinateHom (f i) p ≫ graphInsertion J f a b i =
      graphCoordinate J f a (Function.update b i p) := by
  rw [graphInsertion, FiniteTensor.section_comp_insertMap]
  unfold graphCoordinate
  congr 1
  funext j
  by_cases hji : j = i
  · subst j
    simp only [Function.update_self, quadraticCoordinate]
  · simp only [Function.update_of_ne hji]

/-- Actual scalar multiplication on the genuine graph target. -/
def graphScalarEndomorphism (c : K) : graphLine J f ⟶ graphLine J f :=
  globalSectionsSmul (graphLine J f) (baseRingToGlobalSections K P c)

/-- The complete graph coefficient Σ_r f_r (i-th contraction of f_r). -/
def graphCoefficient (T : R → ((i : Fin k) → J i) → K)
    (i : Fin k) (q : J i) : factorLine J f i ⟶ graphLine J f :=
  ∑ r : R, ∑ a : (j : Fin k) → J j, ∑ b : (j : Fin k) → J j,
    if b i = q then
      graphInsertion J f a b i ≫ graphScalarEndomorphism J f (T r a * T r b)
    else 0

/-- Every actual coefficient has the complete, unrestricted graph contraction expansion. -/
theorem graphCoefficient_coordinate (T : R → ((i : Fin k) → J i) → K)
    (i : Fin k) (p q : J i) :
    pullbackCoordinateHom (f i) p ≫ graphCoefficient J f T i q =
      ∑ r : R, ∑ a : (j : Fin k) → J j, ∑ b : (j : Fin k) → J j,
        if b i = q then
          graphCoordinate J f a (Function.update b i p) ≫
            graphScalarEndomorphism J f (T r a * T r b)
        else 0 := by
  simp only [graphCoefficient, Preadditive.comp_sum]
  apply Finset.sum_congr rfl
  intro r _
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  by_cases hb : b i = q
  · simp only [if_pos hb]
    rw [← Category.assoc, coordinate_comp_graphInsertion]
  · simp only [if_neg hb, comp_zero]

/-- The actual factor functional on the actual pulled-back Euler kernel. -/
def graphFactorCritical (T : R → ((i : Fin k) → J i) → K) (i : Fin k) :
    (Scheme.Modules.pullback (f i)).obj (eulerKernel (I := J i) (K := K) 2) ⟶ graphLine J f :=
  pullbackCriticalFunctional (f i) (graphCoefficient J f T i)

/-- The full graph-format global critical functional, including all small factors. -/
def graphCriticalMap (T : R → ((i : Fin k) → J i) → K) :
    criticalSource J f ⟶ graphLine J f :=
  ∑ i : Fin k,
    Pi.π (fun j : Fin k =>
      (Scheme.Modules.pullback (f j)).obj (eulerKernel (I := J j) (K := K) 2)) i ≫
        graphFactorCritical J f T i

/-- The actual graph critical coordinate as a global section morphism. -/
def graphCriticalCoordinate (T : R → ((i : Fin k) → J i) → K)
    (i : Fin k) (a b : J i) : 𝟙_ P.Modules ⟶ graphLine J f :=
  pullbackCoordinateHom (f i) a ≫ graphCoefficient J f T i b -
    pullbackCoordinateHom (f i) b ≫ graphCoefficient J f T i a

/-- The genuine Euler-kernel map gives exactly the graph critical equation
on every actual pullback chart, in every characteristic. -/
theorem graphFactorCritical_coordinateWedge
    (T : R → ((i : Fin k) → J i) → K) (i : Fin k) (a b : J i)
    (U : (Proj (MvPolynomial.homogeneousSubmodule (J i) K)).Opens)
    (V : P.Opens) (hV : V ≤ (f i) ⁻¹ᵁ U) :
    (graphFactorCritical J f T i).app V
      ((f i).pullbackSectionsLE (eulerKernel (I := J i) (K := K) 2) U V hV
        (coordinateWedge a b U)) =
      (graphCriticalCoordinate J f T i a b).app V (1 : Γ(P, V)) := by
  rw [graphFactorCritical, pullbackCriticalFunctional_coordinateWedge]
  change _ = (graphCoefficient J f T i b).app V
      ((pullbackCoordinateHom (f i) a).app V (1 : Γ(P, V))) -
    (graphCoefficient J f T i a).app V
      ((pullbackCoordinateHom (f i) b).app V (1 : Γ(P, V)))
  rw [pullbackCoordinateHom_app_one (f i) a U V hV,
    pullbackCoordinateHom_app_one (f i) b U V hV]
  rfl

/-- The exact graph critical polynomial, as an equality of actual sheaf morphisms. -/
theorem graphCriticalCoordinate_expansion
    (T : R → ((i : Fin k) → J i) → K) (i : Fin k) (p q : J i) :
    graphCriticalCoordinate J f T i p q =
      (∑ r : R, ∑ a : (j : Fin k) → J j, ∑ b : (j : Fin k) → J j,
        if b i = q then
          graphCoordinate J f a (Function.update b i p) ≫
            graphScalarEndomorphism J f (T r a * T r b) else 0) -
      (∑ r : R, ∑ a : (j : Fin k) → J j, ∑ b : (j : Fin k) → J j,
        if b i = p then
          graphCoordinate J f a (Function.update b i q) ≫
            graphScalarEndomorphism J f (T r a * T r b) else 0) := by
  rw [graphCriticalCoordinate, graphCoefficient_coordinate, graphCoefficient_coordinate]

end PaperVerification.Segre.GraphCriticalMap

end SegreGraphCriticalMap


end SegreCriticalBundleGeometry

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
