module
public import SegreVerified.Stage030.RankAndOpen
public import SegreVerified.Stage030.ActualTensor
public import SegreVerified.Stage030.FormatReduction
public import SegreVerified.Stage028
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
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
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


section SegreTensorSpanTheorems

run_cmd do
  let out ← IO.getStderr
  out.putStrLn "SEGRE_STAGE Stage030.TensorSpan"
  out.flush

/-!
# The graph-span comparison and tensor membership in all formats

The named sections preserve the original proof stages and local scopes.
-/



section SegreProductGlobalDimension

/-!
# The exact dimension of the actual global critical source

The literal projection pullback is an equivalence on global sections of a
quasicoherent sheaf on one projective factor. Together with the complete
Euler-kernel coefficient equivalence, this gives coordinates on the entire
actual global critical source and its exact binomial dimension.

-/

set_option autoImplicit false
open scoped Classical BigOperators

namespace PaperVerification.Segre.ProductGlobalDimension

open CategoryTheory Limits MonoidalCategory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open FixedProductCohomology FixedProductProjections ProductKoszulVanishing
open ActualProductKoszulTerms EulerSheaf EulerSections EulerCriticalFunctional
open SingleFactorGlobalSections ExternalSections ProductGlobalWedges

universe u
variable (K : Type u) [Field K] {k : ℕ}
variable (I : Fin (k+1) → Type u)
variable [∀ i,Fintype (I i)] [∀ i,DecidableEq (I i)] [∀ i,Nonempty (I i)]

local notation "A" => (fun j => projectiveScheme K (I j))
set_option quotPrecheck false in local notation "X" => (product K I).scheme

/-- The literal global projection pullback is bijective, for every
quasicoherent sheaf on the selected projective factor. -/
theorem projective_projectionPullback_bijective (i : Fin (k+1))
    (N : (A i).scheme.Modules) [N.IsQuasicoherent] :
    Function.Bijective ((projection A i).pullbackSectionsLE N ⊤ ⊤ (by simp)) := by
  let M : ∀ j,(A j).scheme.Modules :=
    Function.update (fun j => 𝟙_ (A j).scheme.Modules) i N
  have hM : ∀ j,(M j).IsQuasicoherent := by
    intro j
    by_cases h : j=i
    · subst j
      simpa only [M,Function.update_self] using (inferInstance : N.IsQuasicoherent)
    · simp only [M,Function.update_of_ne h]
      infer_instance
  let e : ∀ j,j≠i → (M j ≅ 𝟙_ (A j).scheme.Modules) :=
    fun j h => eqToIso (Function.update_of_ne h N (fun j => 𝟙_ (A j).scheme.Modules))
  let E := oneFactorSectionsEquiv A M hM i e
    (fun j => projectiveFunctionsFrame (K := K) (I j))
  have he : (fun s => E s)=((projection A i).pullbackSectionsLE (M i) ⊤ ⊤ (by simp)) := by
    funext s
    exact oneFactorSectionsEquiv_apply A M hM i e
      (fun j => projectiveFunctionsFrame (K := K) (I j))
      (fun j => projectiveFunctionsFrame_one (K := K) (I j)) s
  have h := E.bijective
  change Function.Bijective (fun s => E s) at h
  rw [he] at h
  have hMi : M i = N := by
    dsimp only [M]
    exact @Function.update_self (Fin (k+1)) (fun j => (A j).scheme.Modules)
      _ i N (fun j => 𝟙_ (A j).scheme.Modules)
  rw (config := { transparency := .all }) [hMi] at h
  exact h

/-- The actual global projection pullback, now as its proved full linear
equivalence, with the original pullback map as its forward function. -/
def factorGlobalSectionsEquiv (i : Fin (k+1)) :
    sections K (eulerKernel (I := I i) (K := K) 2) ⊤ ≃ₗ[K]
      sections K ((Scheme.Modules.pullback (factorProjection K I i)).obj
        (eulerKernel (I := I i) (K := K) 2)) ⊤ :=
  by
    letI : (eulerKernel (I := I i) (K := K) 2).IsQuasicoherent :=
      positiveEulerKernel_quasicoherent K (I i)
    apply LinearEquiv.ofBijective
      (pullbackBaseLE K (factorProjection K I i)
        (eulerKernel (I := I i) (K := K) 2) ⊤ ⊤ (by simp))
    have hb := projective_projectionPullback_bijective K I i
      (eulerKernel (I := I i) (K := K) 2)
    have h (s : sections K (eulerKernel (I := I i) (K := K) 2) ⊤) :=
      pullbackBaseLE_apply K (factorProjection K I i)
        (eulerKernel (I := I i) (K := K) 2) ⊤ ⊤ (by simp) s
    constructor
    · intro x y hxy
      exact hb.1 ((h x).symm.trans (hxy.trans (h y)))
    · intro z
      obtain ⟨s,hs⟩ := hb.2 z
      exact ⟨s,(h s).trans hs⟩

variable [∀ i,LinearOrder (I i)]

/-- Strict upper coefficient entries in every factor are coordinates on
the whole actual global source, through genuine projection pullbacks. -/
def sourceCoordinates : sections K (source K I) ⊤ ≃ₗ[K]
    (∀ i : Fin (k+1),{p : I i×I i // p.1<p.2} → K) :=
  (sourceSectionsEquiv K I).trans
    (LinearEquiv.piCongrRight (fun i =>
      (factorGlobalSectionsEquiv K I i).symm.trans
        ((GlobalSectionsScalarComparison.identityEquiv K _).symm.trans
          (GlobalEulerWedges.coordinates (I := I i) (K := K)))))

instance sourceGlobal_finite : Module.Finite K (sections K (source K I) ⊤) :=
  Module.Finite.of_surjective (sourceCoordinates K I).symm.toLinearMap
    (sourceCoordinates K I).symm.surjective

/-- The exact dimension of the complete actual global critical source.
No critical-row independence or genericity is assumed. -/
theorem finrank_source_global :
    Module.finrank K (sections K (source K I) ⊤)=
      ∑ i : Fin (k+1),(Fintype.card (I i)).choose 2 := by
  rw [(sourceCoordinates K I).finrank_eq,Module.finrank_pi_fintype]
  apply Finset.sum_congr rfl
  intro i _
  rw [Module.finrank_pi,Fintype.card_subtype,Fintype.card_product_filter_lt]

end PaperVerification.Segre.ProductGlobalDimension

end SegreProductGlobalDimension

section SegreActualCriticalDimension

/-!
# The critical image dimension under finite-chart hypotheses alone

The entire actual graph H⁰ map is injective by the exact finite resolution
and its cohomology gap. Its domain has the exact binomial dimension. The
canonical polynomial image comparison therefore gives that same dimension
for the multiplication image of the original small-factor critical rows.
No generic row independence or nonzero-minor premise is needed.

-/

set_option autoImplicit false
open scoped Classical BigOperators

namespace PaperVerification.Segre.ActualCriticalDimension

open CategoryTheory Limits AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open ActualProductKoszulTerms ActualCriticalExactness ProductGlobalDimension
open ActualLineGlobalSections GlobalCriticalImage
open Staircase Monomials CriticalGraph SpanDefect ProjectiveCharts

variable {K : Type} [Field K] [Infinite K] {k : ℕ}
variable (n : Fin (k+1) → ℕ)
variable {J : Type} [Fintype J] [DecidableEq J]

local notation "I" => (fun i => Fin (n i+1))
set_option quotPrecheck false in local notation "X" => (product K I).scheme

/-- Finiteness of the actual graph critical charts makes the complete
original graph functional injective on genuine global sections. -/
theorem graph_functional_injective (A : Matrix (Cell n) J K)
    (hf : ∀ p : Cell n,Module.Finite K
      (MvPolynomial (ChartVar p) K ⧸ ProjectivePointSpan.chartCriticalIdeal A p)) :
    Function.Injective ((graphFunctional K n A).app ⊤) := by
  let B := max 1 (∑ i, (Fintype.card (I i) - 1))
  have hI : ∀ i,0<Fintype.card (I i) := by
    intro i
    simp only [Fintype.card_fin]
    omega
  apply ResolutionInjectivity.global_functional_injective_of_resolution
    (term K I 2) (ProductWeightedKoszul.differential K I 2 (graphFunctional K n A))
    (ProductWeightedKoszul.differential_squared_unconditional K I 2 (graphFunctional K n A))
    (fun r => graph_exact_of_finite K n A hf r) B (le_max_left _ _) ?_ ?_
    (graphFunctional K n A) (termOneIso K I 2) (termZeroIso K I 2)
    (ProductWeightedKoszul.differential_degree_one K I 2 (graphFunctional K n A))
  · apply term_isZero_of_degree_gt K I hI 2 (B+1)
    exact Nat.lt_succ_of_le (le_max_right _ _)
  · intro r hr _ q hq
    exact graph_term_cohomology_vanishes K I hI r q hr hq

/-- The same injectivity for the canonical base-field linear map used in
the complete global range comparison. -/
theorem graphGlobalMap_injective (A : Matrix (Cell n) J K)
    (hf : ∀ p : Cell n,Module.Finite K
      (MvPolynomial (ChartVar p) K ⧸ ProjectivePointSpan.chartCriticalIdeal A p)) :
    Function.Injective (graphGlobalMap n A) :=
  graph_functional_injective n A hf

/-- The exact dimension of the entire actual global critical image. -/
theorem finrank_graphGlobalMap_range (A : Matrix (Cell n) J K)
    (hf : ∀ p : Cell n,Module.Finite K
      (MvPolynomial (ChartVar p) K ⧸ ProjectivePointSpan.chartCriticalIdeal A p)) :
    Module.finrank K (LinearMap.range (graphGlobalMap n A))=
      ∑ i : Fin (k+1),(n i+1).choose 2 := by
  rw [LinearMap.finrank_range_of_inj (graphGlobalMap_injective n A hf)]
  simpa only [Fintype.card_fin] using finrank_source_global K I

/-- The exact critical-image count required by Proposition 2.1, under
finiteness of the original critical charts alone. This is the complete
ordinary multiplication image of every original small-factor relation. -/
theorem finrank_mapped_smallRelations (A : Matrix (Cell n) J K)
    (hf : ∀ p : Cell n,Module.Finite K
      (MvPolynomial (ChartVar p) K ⧸ ProjectivePointSpan.chartCriticalIdeal A p)) :
    Module.finrank K ((smallRelations A).map (multiplicationOnCovectors A))=
      ∑ i : Fin (k+1),(n i+1).choose 2 := by
  have h := finrank_graphGlobalMap_range n A hf
  rw [graphGlobalMap_range,graph_polynomial_span_eq_mapped_relations,
    (degreeTwoLineEquiv (K := K) n).finrank_map_eq] at h
  exact h

end PaperVerification.Segre.ActualCriticalDimension

end SegreActualCriticalDimension

section SegreSpanImageDimension

/-!
# The graph-span dimension from the actual critical image

The dimension of the critical image after multiplication is the relevant
quantity before any independence theorem is applied. This identity allows
the geometric global-section calculation to prove Proposition 2.1 under
its stated finite/reduced/basepoint-free hypotheses, without adding a
generic independence premise.

-/

set_option autoImplicit false
open scoped BigOperators

namespace PaperVerification.Segre.SpanImageDimension

open Staircase Monomials Trace SingularSpan SpanDefect MultiplicationSpanBridge

variable {I J K : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Field K] {n : I → ℕ}

/-- Rank-nullity on the actual small-relation subspace identifies the
intersection correction with the loss of dimension in its actual image. -/
theorem smallRelations_image_rank_nullity (A : Matrix (Cell n) J K) :
    Module.finrank K ((smallRelations A).map (multiplicationOnCovectors A)) +
      Module.finrank K ↥(LinearMap.ker (multiplicationOnCovectors A) ⊓ smallRelations A) =
        Module.finrank K (smallRelations A) := by
  let μ := multiplicationOnCovectors A
  let C := smallRelations A
  have hk : Module.finrank K (LinearMap.ker (μ.domRestrict C)) =
      Module.finrank K ↥(LinearMap.ker μ ⊓ C) := by
    calc
      _ = Module.finrank K ((LinearMap.ker (μ.domRestrict C)).map C.subtype) :=
        (Submodule.finrank_map_subtype_eq C _).symm
      _ = _ := by
        rw [LinearMap.ker_domRestrict, Submodule.map_comap_subtype, inf_comm]
  have h := LinearMap.finrank_range_add_finrank_ker (K := K) (V := C)
    (V₂ := degreeTwo (K := K) (n := n)) (μ.domRestrict C)
  rw [LinearMap.range_domRestrict, hk] at h
  exact h

/-- The full singular-span dimension plus the dimension of the actual
critical image equals the actual multiplication rank. No disjointness or
critical-equation independence is assumed. -/
theorem singularSpan_dimension_add_image (A : Matrix (Cell n) J K)
    (hgeometry : (singularSpan A).dualAnnihilator =
      LinearMap.ker (multiplicationOnCovectors A) ⊔ smallRelations A) :
    Module.finrank K (singularSpan A) +
      Module.finrank K ((smallRelations A).map (multiplicationOnCovectors A)) =
        Module.finrank K (LinearMap.range (actualMultiplication A)) := by
  have hs := singularSpan_dimension_of_annihilator A hgeometry
  have hc := smallRelations_image_rank_nullity A
  omega

/-- Once the actual global critical image has its geometric dimension,
the printed dimension formula follows without a separate independence
hypothesis on the original critical equation rows. -/
theorem singularSpan_dimension_of_image_count (A : Matrix (Cell n) J K)
    (hgeometry : (singularSpan A).dualAnnihilator =
      LinearMap.ker (multiplicationOnCovectors A) ⊔ smallRelations A)
    (hcount : Module.finrank K ((smallRelations A).map (multiplicationOnCovectors A)) =
      ∑ i, (n i + 1).choose 2) :
    Module.finrank K (singularSpan A) =
      (Degeneration.multiplicationMatrix 1 A).rank - ∑ i, (n i + 1).choose 2 := by
  have h := singularSpan_dimension_add_image A hgeometry
  rw [hcount, finrank_range_actualMultiplication] at h
  omega

end PaperVerification.Segre.SpanImageDimension

end SegreSpanImageDimension

section SegreGraphGeometry

/-!
# The actual global geometric comparison

The weighted Koszul resolution, its cohomology gap, the complete global
critical image, and the literal chart restriction maps meet here. The chart
image identity is proved from finiteness of the original chart quotients;
it is no longer a premise. Reducedness then identifies these ideal equations
with all actual singular rank-one points. The generic certificates discharge
finiteness and reducedness in the full original tensor parameter space.

-/

set_option autoImplicit false
open scoped Classical BigOperators

namespace PaperVerification.Segre.GraphGeometry

open CategoryTheory AlgebraicGeometry Opposite
open Staircase Monomials GraphSpan CriticalGraph SingularSpan SpanDefect
open ProjectiveCharts ActualProductKoszulTerms ActualLineGlobalSections
open GlobalCriticalImage GlobalPolynomialChartRestriction
open GraphConclusionAssembly ProductKoszulVanishing

variable {K : Type} [Field K] [Infinite K] {k : ℕ}
  {n : Fin (k+1) → ℕ}
variable {J : Type} [Fintype J] [DecidableEq J]

/-- The polynomial chart coefficient used by the actual resolution is
exactly the coefficient used by the complete global restriction map. -/
theorem literalChartSectionPolynomial_eq (d : ℤ)
    (s : ExternalSections.sections K (line K (fun i => Fin (n i+1)) d) ⊤)
    (p : Cell n) :
    ActualCriticalExactness.literalChartSectionPolynomial K n d s p =
      chartLineCoefficient n p d s := rfl

/-- The central graph image identity. The only input is finiteness of the
literal original critical chart quotients; the resolution, cohomology,
global-section map, and coordinate identifications are all supplied by the
preceding geometric results. -/
theorem graph_chart_image_identity (A : Matrix (Cell n) J K)
    (hf : ∀ p : Cell n, Module.Finite K
      (MvPolynomial (ChartVar p) K ⧸ ProjectivePointSpan.chartCriticalIdeal A p)) :
    ChartImageIdentity A := by
  unfold ChartImageIdentity
  ext φ
  simp only [Submodule.mem_iInf, Submodule.mem_comap, Submodule.restrictScalars_mem]
  let s := degreeTwoLineEquiv n (multiplicationOnCovectors A φ)
  have hglobal : s ∈ LinearMap.range (graphGlobalMap n A) ↔
      ∀ p : Cell n, ProjectivePointSpan.chartRestriction A p φ ∈
        ProjectivePointSpan.chartCriticalIdeal A p := by
    change (∃ t, (ActualCriticalExactness.graphFunctional K n A).app ⊤ t = s) ↔ _
    have h := ActualCriticalExactness.graph_global_range_iff_literal_ideals K n A hf s
    simpa only [s, literalChartSectionPolynomial_eq, graph_covector_chart] using h
  rw [← hglobal]
  change degreeTwoLineEquiv n (multiplicationOnCovectors A φ) ∈
    LinearMap.range (graphGlobalMap n A) ↔ _
  rw [graphGlobalMap_mem_iff]
  change φ ∈ ((smallRelations A).map (multiplicationOnCovectors A)).comap
    (multiplicationOnCovectors A) ↔ _
  rw [Submodule.comap_map_eq, sup_comm]

/-- The analogous full-product identity under exactly the triangle
inequalities of Section 2.2, with every factor equation retained. -/
theorem balanced_chart_image_identity
    (htriangle : ∀ i, n i ≤ ∑ j ∈ Finset.univ.erase i, n j)
    (T : Cell n → K)
    (hf : ∀ p : Cell n, Module.Finite K
      (MvPolynomial (ChartVar p) K ⧸
        AllFactorPointSpan.chartCriticalIdeal (AllFactorIncidence.unitTensorEquiv T) p)) :
    (⨅ p : Cell n,
      ((AllFactorPointSpan.chartCriticalIdeal (AllFactorIncidence.unitTensorEquiv T) p).restrictScalars K).comap (AllFactorPointSpan.chartRestriction p)) =
      smallRelations (AllFactorIncidence.unitTensorEquiv T) := by
  have htri : TriangleDimensions (fun i => Fin (n i+1)) := by
    simpa only [TriangleDimensions, Fintype.card_fin, Nat.add_sub_cancel] using htriangle
  ext φ
  simp only [Submodule.mem_iInf, Submodule.mem_comap, Submodule.restrictScalars_mem]
  let s := unitCovectorSectionsEquiv n φ
  have hglobal : s ∈ LinearMap.range (fullGlobalMap n T) ↔
      ∀ p : Cell n, AllFactorPointSpan.chartRestriction p φ ∈
        AllFactorPointSpan.chartCriticalIdeal (AllFactorIncidence.unitTensorEquiv T) p := by
    change (∃ t, (ActualCriticalExactness.fullFunctional K n T).app ⊤ t = s) ↔ _
    have h := ActualCriticalExactness.balanced_global_range_iff_literal_ideals
      K n htri T hf s
    simpa only [s, literalChartSectionPolynomial_eq, full_covector_chart] using h
  rw [← hglobal]
  change unitCovectorSectionsEquiv n φ ∈ LinearMap.range (fullGlobalMap n T) ↔ _
  rw [fullGlobalMap_mem_iff]
  rfl

variable [IsAlgClosed K]

/-- The actual graph span formula and tensor membership of Proposition 2.1
from its literal basepoint-free, finite, reduced hypotheses. -/
theorem graph_span_and_tensor_membership (A : Matrix (Cell n) J K)
    (hb : ∀ x : FactorPoint n K, lastContraction A x.val ≠ 0)
    (hf : ∀ p : Cell n, Module.Finite K
      (MvPolynomial (ChartVar p) K ⧸ ProjectivePointSpan.chartCriticalIdeal A p))
    (hr : ∀ p : Cell n, IsReduced
      (MvPolynomial (ChartVar p) K ⧸ ProjectivePointSpan.chartCriticalIdeal A p)) :
    singularSpan A = graphSpan A ⊓ fullCriticalSpace A ∧ A ∈ singularSpan A := by
  have hann : (singularSpan A).dualAnnihilator =
      LinearMap.ker (multiplicationOnCovectors A) ⊔ smallRelations A :=
    (ProjectivePointSpan.singular_annihilator_eq_chart_ideal_intersection A hb hr).trans
      (graph_chart_image_identity A hf)
  exact ⟨singularSpan_eq_graph_inter_critical_of_annihilator A hann,
    tensor_mem_singularSpan_of_annihilator A hann⟩

/-- Proposition 2.1, including its exact dimension formula, under precisely
the literal basepoint-free, finite, reduced hypotheses. The dimension of the
critical image follows from the full cohomological resolution; no generic
independence or rank premise is added. -/
theorem proposition_2_1 (A : Matrix (Cell n) J K)
    (hb : ∀ x : FactorPoint n K, lastContraction A x.val ≠ 0)
    (hf : ∀ p : Cell n, Module.Finite K
      (MvPolynomial (ChartVar p) K ⧸ ProjectivePointSpan.chartCriticalIdeal A p))
    (hr : ∀ p : Cell n, IsReduced
      (MvPolynomial (ChartVar p) K ⧸ ProjectivePointSpan.chartCriticalIdeal A p)) :
    singularSpan A = graphSpan A ⊓ fullCriticalSpace A ∧
      Module.finrank K (singularSpan A) =
        (Degeneration.multiplicationMatrix 1 A).rank - ∑ i, (n i+1).choose 2 ∧
      A ∈ singularSpan A := by
  have hann : (singularSpan A).dualAnnihilator =
      LinearMap.ker (multiplicationOnCovectors A) ⊔ smallRelations A :=
    (ProjectivePointSpan.singular_annihilator_eq_chart_ideal_intersection A hb hr).trans
      (graph_chart_image_identity A hf)
  exact ⟨singularSpan_eq_graph_inter_critical_of_annihilator A hann,
    SpanImageDimension.singularSpan_dimension_of_image_count A hann
      (ActualCriticalDimension.finrank_mapped_smallRelations n A hf),
    tensor_mem_singularSpan_of_annihilator A hann⟩

/-- The complete graph formula, its exact rank/count dimension, and tensor
membership on the actual simultaneous generic open. -/
theorem graph_span_conclusions (A : Matrix (Cell n) J K)
    (hA : CommonGraphOpen.RegularData A) :
    singularSpan A = graphSpan A ⊓ fullCriticalSpace A ∧
      Module.finrank K (singularSpan A) =
        (Degeneration.multiplicationMatrix 1 A).rank - ∑ i, (n i+1).choose 2 ∧
      A ∈ singularSpan A :=
  GraphConclusionAssembly.graph_span_conclusions A hA
    (graph_chart_image_identity A hA.finiteChart)

/-- Full-product singular points span the entire original critical space
in the balanced range, once the original chart schemes are finite and reduced. -/
theorem balanced_singular_span
    (htriangle : ∀ i, n i ≤ ∑ j ∈ Finset.univ.erase i, n j)
    (T : Cell n → K)
    (hf : ∀ p : Cell n, Module.Finite K
      (MvPolynomial (ChartVar p) K ⧸
        AllFactorPointSpan.chartCriticalIdeal (AllFactorIncidence.unitTensorEquiv T) p))
    (hr : ∀ p : Cell n, IsReduced
      (MvPolynomial (ChartVar p) K ⧸
        AllFactorPointSpan.chartCriticalIdeal (AllFactorIncidence.unitTensorEquiv T) p)) :
    singularSpan (AllFactorIncidence.unitTensorEquiv T) =
      criticalSpace (AllFactorIncidence.unitTensorEquiv T) := by
  have hann : (singularSpan (AllFactorIncidence.unitTensorEquiv T)).dualAnnihilator =
      smallRelations (AllFactorIncidence.unitTensorEquiv T) :=
    (AllFactorPointSpan.singular_annihilator_eq_chart_ideal_intersection _ hr).trans
      (balanced_chart_image_identity htriangle T hf)
  calc
    singularSpan (AllFactorIncidence.unitTensorEquiv T) =
      (singularSpan (AllFactorIncidence.unitTensorEquiv T)).dualAnnihilator.dualCoannihilator :=
        (Subspace.dualAnnihilator_dualCoannihilator_eq
          (W := singularSpan (AllFactorIncidence.unitTensorEquiv T))).symm
    _ = (smallRelations (AllFactorIncidence.unitTensorEquiv T)).dualCoannihilator := by rw [hann]
    _ = criticalSpace (AllFactorIncidence.unitTensorEquiv T) := smallRelations_coannihilator _

/-- The balanced branch of Theorem 1.3 in the full original tensor
coefficient space, on a nonzero polynomial open with no extra geometric premise. -/
theorem generic_balanced_tensor_membership
    (htriangle : ∀ i, n i ≤ ∑ j ∈ Finset.univ.erase i, n j) :
    ∃ p : MvPolynomial (Cell n) K, p ≠ 0 ∧
      ∀ T : Cell n → K, MvPolynomial.eval T p ≠ 0 →
        T ∈ TensorFactorReindex.incidenceSpan T := by
  obtain ⟨p, hp, hw⟩ := AllChartGenericity.exists_all_chart_certificate (K := K) (n := n)
  refine ⟨p, hp, ?_⟩
  intro T hT
  have hT' : MvPolynomial.aeval T p ≠ 0 := by
    simpa only [MvPolynomial.aeval_eq_eval] using hT
  have hspan := balanced_singular_span htriangle T
    (fun q => (hw T hT' q).1) (fun q => (hw T hT' q).2)
  have hmem : AllFactorIncidence.unitTensorEquiv T ∈
      singularSpan (AllFactorIncidence.unitTensorEquiv T) := by
    rw [hspan]
    exact tensor_mem_criticalSpace _
  rw [TensorFactorReindex.incidenceSpan_numeric,
    AllFactorIncidence.incidencePureTensorSpan_eq_unit_singularSpan]
  exact ⟨AllFactorIncidence.unitTensorEquiv T, hmem,
    AllFactorIncidence.unitTensorEquiv.symm_apply_apply T⟩

/-- The graph branch of Theorem 1.3 for every permitted final dimension,
on the entire original slice parameter space. -/
theorem generic_graph_tensor_membership (hlen : sideSum n+1 ≤ Fintype.card J) :
    ∃ p : MvPolynomial (Cell n × J) K, p ≠ 0 ∧
      ∀ A : Matrix (Cell n) J K,
        MvPolynomial.eval (fun q => A q.1 q.2) p ≠ 0 → A ∈ singularSpan A := by
  obtain ⟨p, hp, hw⟩ :=
    GenericGraphChartCertificate.exists_graph_chart_certificate (K := K) hlen
  refine ⟨p, hp, ?_⟩
  intro A hA
  exact (graph_span_and_tensor_membership A (hw A hA).1
    (fun q => ((hw A hA).2 q).1) (fun q => ((hw A hA).2 q).2)).2

/-- Theorem 1.3 in literal tensor coefficients. Every nonnegative numeric
format, every characteristic, and every original coefficient are included.
The asserted open is explicitly nonempty. -/
theorem theorem_1_3 (r : ℕ) (n : Fin (r+1) → ℕ) :
    ∃ p : MvPolynomial (Cell n) K, p ≠ 0 ∧
      (∃ T : Cell n → K, MvPolynomial.eval T p ≠ 0) ∧
      ∀ T : Cell n → K, MvPolynomial.eval T p ≠ 0 →
        T ∈ AllFactorIncidence.incidencePureTensorSpan T := by
  obtain ⟨p, hp, hw⟩ := AllFormatReduction.generic_all_formats_of_geometric_branches
    (K := K)
    (fun _ _ h => generic_balanced_tensor_membership h)
    (fun _ _ _ h => generic_graph_tensor_membership
      (by simpa only [Fintype.card_fin] using h)) r n
  exact ⟨p, hp, AllFormatReduction.nonempty_tensor_certificate hp, hw⟩

end PaperVerification.Segre.GraphGeometry

end SegreGraphGeometry


section SegrePrincipalTensor

/-!
# Theorem 1.3 on the original tensor product

This endpoint uses Mathlib's actual finite tensor product, the original
coordinate bilinear contractions, and the ordinary span of singular pure
tensors. A canonical basis equivalence transfers the full coefficient-space
certificate; both the contractions and rank-one generators have been proved
to agree under that equivalence.

-/

set_option autoImplicit false

namespace PaperVerification.Segre.PrincipalTensor

open Staircase

variable {K : Type} [Field K] [IsAlgClosed K]

/-- Theorem 1.3, faithfully stated in the actual tensor product, over every
algebraically closed field and for every nonempty finite numeric format.
There are no additional generic rank, regularity, reducedness, isotropy, or
cohomology assumptions. The nonempty principal open is part of the conclusion. -/
theorem theorem_1_3 (r : ℕ) (n : Fin (r+1) → ℕ) :
    ∃ p : MvPolynomial (Cell n) K, p ≠ 0 ∧
      (∃ T : ActualTensorSpan.Tensor K (fun i => Fin (n i+1)),
        MvPolynomial.eval (ActualTensorSpan.coefficients K (fun i => Fin (n i+1)) T) p ≠ 0) ∧
      ∀ T : ActualTensorSpan.Tensor K (fun i => Fin (n i+1)),
        MvPolynomial.eval (ActualTensorSpan.coefficients K (fun i => Fin (n i+1)) T) p ≠ 0 →
          T ∈ ActualTensorSpan.singularSpan K (fun i => Fin (n i+1)) T :=
  ActualTensorSpan.generic_actual_tensor_membership K (fun i => Fin (n i+1))
    (GraphGeometry.theorem_1_3 r n)

end PaperVerification.Segre.PrincipalTensor

end SegrePrincipalTensor

end SegreTensorSpanTheorems

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
