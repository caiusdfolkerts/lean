module
public import SegreVerified.Stage025.Euler
public import SegreVerified.Stage025.ChartCoordinates
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

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

/-!
# Canonical normalized coordinates on projective charts

These are the original coordinate trivializations and fraction comparisons,
independent of the later exterior-power and singular-scheme constructions.
-/

section EulerChartCoordinates

attribute [local instance] MvPolynomial.gradedAlgebra

namespace PaperVerification.Segre.EulerCriticalChart

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open ProjectiveCech EulerSheaf EulerSections
open scoped BigOperators

universe u
variable {I K : Type u} [Fintype I] [DecidableEq I] [Field K]

local notation "𝒜" => MvPolynomial.homogeneousSubmodule I K
local notation "X" => Proj (MvPolynomial.homogeneousSubmodule I K)
local notation "O1" => Proj.twistingSheaf (MvPolynomial.homogeneousSubmodule I K) (1 : ℤ)

variable (p : I) (U : (Proj (MvPolynomial.homogeneousSubmodule I K)).Opens)
  (hU : U ≤ coordinateOpen (K := K) p)

/-- The canonical local-fraction trivialization of the actual twisting sheaf. -/
def chartTrivialization (t : ℤ) :
    Γ(X, U) ≃ₗ[Γ(X, U)] Γ(Proj.twistingSheaf 𝒜 t, U) :=
  Proj.twistingSheaf.chartSectionsLinearEquiv («𝒜» := 𝒜) t (MvPolynomial.X p)
    (MvPolynomial.isHomogeneous_X (R := K) p) U hU

/-- The pivot's degree-one chart generator is the actual coordinate section. -/
theorem chartGenerator_one_eq_coordinate :
    Proj.twistingSheaf.chartGenerator («𝒜» := 𝒜) (1 : ℤ) (MvPolynomial.X p)
      (MvPolynomial.isHomogeneous_X (R := K) p) U hU = coordinateSection p U := by
  apply Proj.twistingSheaf.ext
  intro x
  erw [Proj.twistingSheaf.chartGenerator_apply, coordinateSection_apply]
  simp only [show (1 : ℤ).toNat = 1 from rfl,
    show (-(1 : ℤ)).toNat = 0 from rfl, pow_one, pow_zero]
  exact Localization.mk_one_eq_algebraMap _

/-- Literal coordinate ratios, as elements of the actual structure-sheaf ring. -/
def normalizedCoordinate (i : I) : Γ(X, U) :=
  (chartTrivialization p U hU 1).symm (coordinateSection i U)

@[simp]
theorem normalizedCoordinate_pivot : normalizedCoordinate p U hU p = 1 := by
  apply (chartTrivialization p U hU 1).injective
  rw [normalizedCoordinate, LinearEquiv.apply_symm_apply]
  dsimp only [chartTrivialization]
  erw [Proj.twistingSheaf.chartSectionsLinearEquiv_apply]
  rw [one_smul, chartGenerator_one_eq_coordinate]

end PaperVerification.Segre.EulerCriticalChart

end EulerChartCoordinates

section SegreEulerPolynomialCoordinates

/-!
# The Euler-chart coordinates are the actual polynomial variables

This comparison connects the local trivializations of the genuine Euler
kernel with the explicit algebra equivalence on the standard affine chart.
It proves equality of structure-sheaf sections before applying the chart
coordinate ring equivalence.
-/

set_option autoImplicit false
attribute [local instance] MvPolynomial.gradedAlgebra

namespace PaperVerification.Segre.EulerPolynomialCoordinates

open CategoryTheory AlgebraicGeometry MvPolynomial
open ProjectiveCech PolynomialChartRing ProjectiveChartSections
open scoped ProjectiveChartSections

universe u
variable {I K : Type u} [Fintype I] [DecidableEq I] [Field K]

local notation "𝒜" => homogeneousSubmodule I K

/-- The normalized coordinate obtained from the actual O(1) chart
trivialization equals the actual homogeneous fraction Xᵢ/Xₚ. -/
theorem normalizedCoordinate_eq_fraction (p i : I) :
    EulerCriticalChart.normalizedCoordinate p (coordinateOpen p) le_rfl i=
      ProjectiveChartSections.coordinateSection (K := K) p i := by
  apply Subtype.ext
  funext x
  apply HomogeneousLocalization.val_injective
  change (((Proj.twistingSheaf.chartSectionsLinearEquiv 1 (X p)
      (isHomogeneous_X (R := K) p) (coordinateOpen p) le_rfl).symm
        (EulerSheaf.coordinateSection i (coordinateOpen p))).val x).val=_
  erw [Proj.twistingSheaf.chartSectionsLinearEquiv_symm_apply_val,
    EulerSheaf.coordinateSection_apply,Proj.twistingSheaf.chartGenerator_apply]
  change algebraMap (MvPolynomial I K) _ (X i)*
    Localization.mk ((X p : MvPolynomial I K)^(-1 : ℤ).toNat)
      ⟨(X p)^(1 : ℤ).toNat,_⟩=
    ((Proj.awayToSection 𝒜 (X p)
      (HomogeneousLocalization.Away.mk 𝒜 (isHomogeneous_X (R := K) p) 1
        (X i) (by simpa using isHomogeneous_X (R := K) i))).val x).val
  rw [Proj.val_awayToSection_mk_apply,← Localization.mk_one_eq_algebraMap,
    Localization.mk_mul]
  simp

/-- Under the actual section-ring equivalence, normalized Euler coordinates
are exactly the coordinate polynomials used by the singular equations. -/
@[simp] theorem chartSectionsEquiv_normalizedCoordinate (p i : I) :
    chartSectionsEquiv (K := K) p
      (EulerCriticalChart.normalizedCoordinate p (coordinateOpen p) le_rfl i)=
        normalizedVariable p i := by
  rw [normalizedCoordinate_eq_fraction,chartSectionsEquiv_coordinate]

end PaperVerification.Segre.EulerPolynomialCoordinates

end SegreEulerPolynomialCoordinates

end
end

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
