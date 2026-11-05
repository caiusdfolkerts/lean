module
public import SegreVerified.Stage028.CriticalExactness
public import SegreVerified.Stage028.GraphElimination
public import SegreVerified.Stage031.SectionZeroScheme
public import SegreVerified.Stage030.TensorCoordinates
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


section SegreProjectiveTheorems

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false

run_cmd do
  let out ← IO.getStderr
  out.putStrLn "SEGRE_STAGE Stage031.IntrinsicScheme"
  out.flush

/-!
# The original embedded scheme and the principal projective span theorems

The named sections preserve the original proof stages and local scopes.
-/



section SegreCriticalZeroScheme

/-!
# Genuine critical zero-schemes and their exact chart algebras

The original functional into a line bundle is untwisted using the actual
line-bundle multiplication isomorphism. The image ideal sheaf of that
functional defines a genuine closed subscheme of the genuine projective
product. Its affine quotient rings are proved to be precisely the whole
critical polynomial quotient rings, before taking radicals or points.

-/

set_option autoImplicit false
open scoped Classical BigOperators TensorProduct

namespace PaperVerification.Segre.CriticalZeroScheme

open CategoryTheory MonoidalCategory AlgebraicGeometry Opposite
open AlgebraicGeometry.Scheme.Modules
open ActualProductKoszulTerms ActualProductChartFrames ActualWeightedExactness
open ProductLineMultiplication AffineTensorProductMap
open SheafCoefficientContraction SheafCoefficientComplex
open scoped ProjectiveChartSections ProductChartSections

universe u
variable (K : Type u) [Field K] {k : ℕ}
variable (I : Fin (k + 1) → Type u)
variable [∀ i, Fintype (I i)] [∀ i, DecidableEq (I i)]

set_option quotPrecheck false in local notation "X" => (product K I).scheme

/-- Actual evaluation of a product line against its inverse line. -/
def lineEvaluation (d : ℤ) : line K I d ⊗ line K I (-d) ≅ 𝟙_ (X).Modules :=
  lineAddIso K I d (-d) ≪≫
    eqToIso (congrArg (line K I) (add_neg_cancel d)) ≪≫ lineZeroIso K I

/-- Untwisting the genuine critical functional gives an actual morphism
to the structure sheaf, whose image is its zero-scheme ideal sheaf. -/
def untwist (d : ℤ) (φ : source K I ⟶ line K I d) :
    source K I ⊗ line K I (-d) ⟶ 𝟙_ (X).Modules :=
  (φ ⊗ₘ 𝟙 (line K I (-d))) ≫ (lineEvaluation K I d).hom

/-- The genuine closed zero-scheme of the original functional. -/
def zeroScheme (d : ℤ) (φ : source K I ⟶ line K I d) : Scheme.{u} :=
  SectionZeroScheme.zeroScheme (untwist K I d φ)

def toBase (d : ℤ) (φ : source K I ⟶ line K I d) :
    zeroScheme K I d φ ⟶ Spec (.of K) :=
  SectionZeroScheme.toBase (untwist K I d φ) K

def affineChart (p : ∀ i, I i) : (X).affineOpens :=
  ⟨chart K I p, chart_affine K I p⟩

/-- The untwisted functional has exactly the same local coefficients as
the original functional in its actual line frame. -/
theorem untwist_tensor (d : ℤ) (φ : source K I ⟶ line K I d)
    (p : ∀ i, I i) (m : Γ(source K I, chart K I p))
    (l : Γ(line K I (-d), chart K I p)) :
    SectionZeroScheme.sectionMap (untwist K I d φ) (chart K I p)
      (sectionTensorMap (source K I) (line K I (-d)) (chart K I p)
        (m ⊗ₜ[Γ(X, chart K I p)] l)) =
      lineFrame K I p d (φ.app (chart K I p) m) * lineFrame K I p (-d) l := by
  change (untwist K I d φ).app (chart K I p)
    (tensorSection (X).sheaf (source K I) (line K I (-d)) (op (chart K I p)) m l) = _
  simp only [untwist, lineEvaluation, Iso.trans_hom, Scheme.Modules.Hom.comp_app,
    ConcreteCategory.comp_apply, tensorSection_map, PresheafOfModules.id_app,
    ConcreteCategory.id_apply]
  erw [tensorSection_map (X).sheaf]
  simp only [SheafOfModules.id_val, PresheafOfModules.id_app, ConcreteCategory.id_apply]
  rw [lineZeroIso_frame K I p, lineFrame_cast K I p (add_neg_cancel d)]
  change lineFrame K I p (d + -d)
    (WeightedSheafKoszul.multiplicationAt (X).sheaf (lineAddIso K I d (-d)).hom
      (op (chart K I p)) (φ.app (chart K I p) m) l) = _
  exact lineAddIso_frame K I p d (-d) (φ.app (chart K I p) m) l

def framedMap (d : ℤ) (φ : source K I ⟶ line K I d) (p : ∀ i, I i) :
    Γ(source K I, chart K I p) →ₗ[Γ(X, chart K I p)] Γ(X, chart K I p) :=
  (lineFrame K I p d).toLinearMap.comp (φ.val.app (op (chart K I p))).hom

/-- Equality of actual image ideals, using surjectivity of the genuine
affine tensor-of-sections map and the actual inverse-line generator. -/
theorem sectionIdeal_eq_range (d : ℤ) (φ : source K I ⟶ line K I d)
    (p : ∀ i, I i) :
    SectionZeroScheme.sectionIdeal (untwist K I d φ) (affineChart K I p) =
      LinearMap.range (framedMap K I d φ p) := by
  change LinearMap.range (SectionZeroScheme.sectionMap (untwist K I d φ) (chart K I p)) =
    LinearMap.range (framedMap K I d φ p)
  ext r
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨w, rfl⟩ := (sectionTensorMap_bijective (source K I)
      (line K I (-d)) (chart K I p) (chart_affine K I p)).surjective s
    induction w using TensorProduct.induction_on with
    | zero =>
        simp only [map_zero]
        exact (LinearMap.range (framedMap K I d φ p)).zero_mem
    | tmul m l =>
        rw [untwist_tensor]
        refine ⟨lineFrame K I p (-d) l • m, ?_⟩
        rw [_root_.map_smul]
        change lineFrame K I p (-d) l *
          lineFrame K I p d (φ.app (chart K I p) m) = _
        exact mul_comm _ _
    | add w₁ w₂ h₁ h₂ =>
        simp only [map_add]
        exact (LinearMap.range (framedMap K I d φ p)).add_mem h₁ h₂
  · rintro ⟨m, rfl⟩
    refine ⟨sectionTensorMap (source K I) (line K I (-d)) (chart K I p)
      (m ⊗ₜ[Γ(X, chart K I p)] (lineFrame K I p (-d)).symm 1), ?_⟩
    rw [untwist_tensor, LinearEquiv.apply_symm_apply, mul_one]
    rfl

/-- The actual section-image ideal is generated by every source-frame
coefficient. No equation or scheme structure is discarded. -/
theorem sectionIdeal_eq_span (d : ℤ) (φ : source K I ⟶ line K I d)
    (p : ∀ i, I i) :
    SectionZeroScheme.sectionIdeal (untwist K I d φ) (affineChart K I p) =
      Ideal.span (Set.range (coefficient K I d φ p)) := by
  rw [sectionIdeal_eq_range]
  have h : (framedMap K I d φ p).comp (sourceFrame K I p).toLinearMap =
      Fintype.linearCombination Γ(X, chart K I p) (coefficient K I d φ p) := by
    apply LinearMap.ext
    intro v
    exact functional_coefficients K I d φ p v
  have hr : LinearMap.range
      ((framedMap K I d φ p).comp (sourceFrame K I p).toLinearMap) =
        LinearMap.range (framedMap K I d φ p) := by
    rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_top]
  rw [← hr, h, Fintype.range_linearCombination]

/-- The genuine affine coordinate equivalence carries the actual
zero-scheme ideal to the full actual coefficient-polynomial ideal. -/
theorem map_sectionIdeal (d : ℤ) (φ : source K I ⟶ line K I d)
    (p : ∀ i, I i) :
    (SectionZeroScheme.sectionIdeal (untwist K I d φ) (affineChart K I p)).map
      (coordinateEquiv K I p).toRingHom = equationIdeal K I d φ p := by
  rw [sectionIdeal_eq_span, Ideal.map_span, ← Set.range_comp]
  rfl

/-- This is an isomorphism of the entire genuine quotient algebra,
including its possible nilpotents, over the original coefficient field. -/
def chartQuotientEquiv (d : ℤ) (φ : source K I ⟶ line K I d)
    (p : ∀ i, I i) :
    (Γ(X, chart K I p) ⧸
        (SectionZeroScheme.sectionIdeal (untwist K I d φ) (affineChart K I p) :
          Ideal Γ(X, chart K I p))) ≃ₐ[K]
      MvPolynomial (FrameIndex I p) K ⧸ equationIdeal K I d φ p :=
  Ideal.quotientEquivAlg _ _ (coordinateEquiv K I p)
    (map_sectionIdeal K I d φ p).symm

theorem finite_algEquiv_iff {R S : Type u} [CommRing R] [CommRing S]
    [Algebra K R] [Algebra K S] (e : R ≃ₐ[K] S) :
    Module.Finite K R ↔ Module.Finite K S := by
  constructor
  · intro h
    letI := h
    exact Module.Finite.of_surjective e.toLinearMap e.surjective
  · intro h
    letI := h
    exact Module.Finite.of_surjective e.symm.toLinearMap e.symm.surjective

theorem reduced_algEquiv_iff {R S : Type u} [CommRing R] [CommRing S]
    [Algebra K R] [Algebra K S] (e : R ≃ₐ[K] S) :
    _root_.IsReduced R ↔ _root_.IsReduced S := by
  constructor
  · intro h
    letI := h
    exact isReduced_of_injective e.symm e.symm.injective
  · intro h
    letI := h
    exact isReduced_of_injective e e.injective

/-- Actual global finite/reducedness is equivalent to the complete
coefficient-polynomial quotient criteria used by the weighted resolution. -/
theorem finite_reduced_iff (d : ℤ) (φ : source K I ⟶ line K I d) :
    (IsFinite (toBase K I d φ) ∧ AlgebraicGeometry.IsReduced (zeroScheme K I d φ)) ↔
      (∀ p : ∀ i, I i,
        Module.Finite K (MvPolynomial (FrameIndex I p) K ⧸ equationIdeal K I d φ p)) ∧
      (∀ p : ∀ i, I i,
        _root_.IsReduced (MvPolynomial (FrameIndex I p) K ⧸ equationIdeal K I d φ p)) := by
  change (IsFinite (SectionZeroScheme.toBase (untwist K I d φ) K) ∧
    AlgebraicGeometry.IsReduced (SectionZeroScheme.zeroScheme (untwist K I d φ))) ↔ _
  rw [SectionZeroScheme.finite_reduced_iff (untwist K I d φ) K (affineChart K I)
    (chart_cover K I)]
  exact and_congr
    (forall_congr' fun p => finite_algEquiv_iff K (chartQuotientEquiv K I d φ p))
    (forall_congr' fun p => reduced_algEquiv_iff K (chartQuotientEquiv K I d φ p))

end PaperVerification.Segre.CriticalZeroScheme

namespace PaperVerification.Segre.LiteralCriticalZeroScheme

open CategoryTheory AlgebraicGeometry
open Staircase ProjectiveCharts AllFactorIncidence
open ActualProductKoszulTerms ActualCriticalExactness CriticalZeroScheme

variable (K : Type) [Field K] [Infinite K] {k : ℕ} (n : Fin (k + 1) → ℕ)

local notation "I" => (fun i => Fin (n i + 1))

/-- The original full singular-tuple zero-scheme in the actual product. -/
def singularScheme (T : Cell n → K) : Scheme :=
  CriticalZeroScheme.zeroScheme K I 1 (fullFunctional K n T)

def singularToBase (T : Cell n → K) : singularScheme K n T ⟶ Spec (.of K) :=
  CriticalZeroScheme.toBase K I 1 (fullFunctional K n T)

/-- Exact equivalence between the original global scheme property and
the literal all-pivot critical quotient rings. -/
theorem full_finite_reduced_iff (T : Cell n → K) :
    (IsFinite (singularToBase K n T) ∧ AlgebraicGeometry.IsReduced (singularScheme K n T)) ↔
      (∀ p : Cell n, Module.Finite K (MvPolynomial (ChartVar p) K ⧸
        AllFactorPointSpan.chartCriticalIdeal (unitTensorEquiv T) p)) ∧
      (∀ p : Cell n, _root_.IsReduced (MvPolynomial (ChartVar p) K ⧸
        AllFactorPointSpan.chartCriticalIdeal (unitTensorEquiv T) p)) := by
  change (IsFinite (CriticalZeroScheme.toBase K I 1 (fullFunctional K n T)) ∧
    AlgebraicGeometry.IsReduced (CriticalZeroScheme.zeroScheme K I 1 (fullFunctional K n T))) ↔ _
  rw [CriticalZeroScheme.finite_reduced_iff]
  exact and_congr
    (forall_congr' fun p => finite_algEquiv_iff K (fullQuotientEquiv K n T p))
    (forall_congr' fun p => reduced_algEquiv_iff K (fullQuotientEquiv K n T p))

/-- The actual graph critical zero-scheme, before taking points or radicals. -/
def graphScheme {J : Type} [Fintype J] (A : Matrix (Cell n) J K) : Scheme :=
  CriticalZeroScheme.zeroScheme K I 2 (graphFunctional K n A)

def graphToBase {J : Type} [Fintype J] (A : Matrix (Cell n) J K) :
    graphScheme K n A ⟶ Spec (.of K) :=
  CriticalZeroScheme.toBase K I 2 (graphFunctional K n A)

/-- The conditional graph proposition's chart hypotheses are exactly
actual global finiteness and reducedness of its genuine zero-scheme. -/
theorem graph_finite_reduced_iff {J : Type} [Fintype J] [DecidableEq J]
    (A : Matrix (Cell n) J K) :
    (IsFinite (graphToBase K n A) ∧ AlgebraicGeometry.IsReduced (graphScheme K n A)) ↔
      (∀ p : Cell n, Module.Finite K (MvPolynomial (ChartVar p) K ⧸
        ProjectivePointSpan.chartCriticalIdeal A p)) ∧
      (∀ p : Cell n, _root_.IsReduced (MvPolynomial (ChartVar p) K ⧸
        ProjectivePointSpan.chartCriticalIdeal A p)) := by
  change (IsFinite (CriticalZeroScheme.toBase K I 2 (graphFunctional K n A)) ∧
    AlgebraicGeometry.IsReduced (CriticalZeroScheme.zeroScheme K I 2 (graphFunctional K n A))) ↔ _
  rw [CriticalZeroScheme.finite_reduced_iff]
  exact and_congr
    (forall_congr' fun p => finite_algEquiv_iff K (graphQuotientEquiv K n A p))
    (forall_congr' fun p => reduced_algEquiv_iff K (graphQuotientEquiv K n A p))

end PaperVerification.Segre.LiteralCriticalZeroScheme

end SegreCriticalZeroScheme

section SegreNormalizedFactorReindex

/-!
# Complete normalized critical ideals under factor and coordinate reindexing

The equivalences below retain every variable and every critical equation.
They therefore identify the entire quotient rings, not just their points.

-/

set_option autoImplicit false
open scoped Classical

namespace PaperVerification.Segre.NormalizedFactorReindex

open MvPolynomial CriticalChart CriticalChartReindex

variable {I I' K : Type*} [Fintype I] [DecidableEq I]
  [Fintype I'] [DecidableEq I'] [Field K] [Infinite K]
variable {σ : I → Type*} {τ : I' → Type*}
  [∀ i, Fintype (σ i)] [∀ i, Fintype (τ i)]

def variableEquiv (e : I' ≃ I) (h : ∀ i, τ i ≃ σ (e i)) :
    (Σ i, τ i) ≃ (Σ i, σ i) := Equiv.sigmaCongr e h

def cellEquiv (e : I' ≃ I) (h : ∀ i, τ i ≃ σ (e i)) :
    (∀ i, Option (τ i)) ≃ (∀ i, Option (σ i)) :=
  (Equiv.piCongrRight (fun i => Equiv.optionCongr (h i))).trans
    (TensorFactorReindex.cellEquiv (σ := fun i => Option (σ i)) e)

def tensor (e : I' ≃ I) (h : ∀ i, τ i ≃ σ (e i))
    (T : (∀ i, Option (σ i)) → K) : (∀ i, Option (τ i)) → K :=
  fun b => T (cellEquiv e h b)

@[simp] theorem cellEquiv_apply (e : I' ≃ I) (h : ∀ i, τ i ≃ σ (e i))
    (b : ∀ i, Option (τ i)) (i : I') :
    cellEquiv e h b (e i) = Equiv.optionCongr (h i) (b i) := by
  exact TensorFactorReindex.cellEquiv_apply (σ := fun i => Option (σ i)) e _ i

@[simp] theorem variableEquiv_apply (e : I' ≃ I)
    (h : ∀ i, τ i ≃ σ (e i)) (i : I') (a : τ i) :
    variableEquiv e h ⟨i, a⟩ = ⟨e i, h i a⟩ := rfl

theorem pointVector_reindex (e : I' ≃ I) (h : ∀ i, τ i ≃ σ (e i))
    (z : (Σ i, σ i) → K) :
    pointVector (z ∘ variableEquiv e h) =
      (fun i a => pointVector z (e i) (Equiv.optionCongr (h i) a)) := by
  funext i a
  cases a <;> rfl

/-- Every normalized critical polynomial is preserved, including its
distinguished pivot coefficient and sign. -/
theorem rename_criticalEquation (e : I' ≃ I)
    (h : ∀ i, τ i ≃ σ (e i)) (T : (∀ i, Option (σ i)) → K)
    (q : Σ i, τ i) :
    rename (variableEquiv e h) (criticalEquation (tensor e h T) q) =
      criticalEquation T (variableEquiv e h q) := by
  apply MvPolynomial.funext
  intro z
  rw [eval_rename, eval_criticalEquation, pointVector_reindex,
    eval_criticalEquation]
  have ht : tensor e h T =
      (fun b => TensorFactorReindex.tensorEquiv e T
        (Equiv.piCongrRight (fun i => Equiv.optionCongr (h i)) b)) := rfl
  rw [ht]
  change TangentKernel.contraction
      (fun i a => (TensorFactorReindex.vectors e (pointVector z)) i
        (Equiv.optionCongr (h i) a))
      (fun b => TensorFactorReindex.tensorEquiv e T
        (Equiv.piCongrRight (fun i => Equiv.optionCongr (h i)) b)) q.1 (some q.2) -
      z (variableEquiv e h q) *
        TangentKernel.contraction
          (fun i a => (TensorFactorReindex.vectors e (pointVector z)) i
            (Equiv.optionCongr (h i) a))
          (fun b => TensorFactorReindex.tensorEquiv e T
            (Equiv.piCongrRight (fun i => Equiv.optionCongr (h i)) b)) q.1 none = _
  rw [contraction_piCongr, contraction_piCongr]
  erw [TensorFactorReindex.contraction_reindex (σ := fun i => Option (σ i))
    e (pointVector z) T q.1 ((h q.1).optionCongr (some q.2)),
    TensorFactorReindex.contraction_reindex (σ := fun i => Option (σ i))
    e (pointVector z) T q.1 ((h q.1).optionCongr none)]
  rfl

/-- Equality of the whole defining ideals under the actual variable
permutation, before taking a radical or a zero locus. -/
theorem map_criticalIdeal (e : I' ≃ I)
    (h : ∀ i, τ i ≃ σ (e i)) (T : (∀ i, Option (σ i)) → K) :
    (Ideal.span (Set.range (criticalEquation (tensor e h T)))).map
      (rename (R := K) (variableEquiv e h)).toRingHom =
      Ideal.span (Set.range (criticalEquation T)) := by
  rw [Ideal.map_span, ← Set.range_comp]
  apply congrArg Ideal.span
  ext f
  constructor
  · rintro ⟨q, rfl⟩
    exact ⟨variableEquiv e h q, (rename_criticalEquation e h T q).symm⟩
  · rintro ⟨q, rfl⟩
    obtain ⟨q', rfl⟩ := (variableEquiv e h).surjective q
    exact ⟨q', rename_criticalEquation e h T q'⟩

/-- The entire normalized critical coordinate algebra is invariant under
simultaneous changes of factor names and free-coordinate names. -/
def quotientEquiv (e : I' ≃ I)
    (h : ∀ i, τ i ≃ σ (e i)) (T : (∀ i, Option (σ i)) → K) :
    (MvPolynomial (Σ i, τ i) K ⧸
        Ideal.span (Set.range (criticalEquation (tensor e h T)))) ≃ₐ[K]
      (MvPolynomial (Σ i, σ i) K ⧸ Ideal.span (Set.range (criticalEquation T))) :=
  Ideal.quotientEquivAlg _ _ (renameEquiv K (variableEquiv e h))
    (map_criticalIdeal e h T).symm

end PaperVerification.Segre.NormalizedFactorReindex

end SegreNormalizedFactorReindex

section SegreSingularSchemeGraphCharts

/-!
# The original singular scheme supplies the graph chart hypotheses

The full tensor retains its last factor. Its genuine singular zero-scheme
is defined on the actual product of all projective factors. The complete
coordinate algebras of its standard charts are identified with the full
chart algebras used in exact graph elimination. Thus global finiteness and
reducedness, together with the original base-point-free slice hypothesis,
imply precisely the graph chart hypotheses of Proposition 2.1.

-/

set_option autoImplicit false
open scoped Classical

namespace PaperVerification.Segre.SingularSchemeGraphCharts

open Staircase GraphSpan SingularSpan ProjectiveCharts ProjectivePointSpan CriticalGraph Degeneration
open CriticalChartReindex FullGraphChartReindex GraphCriticalElimination
open ChartBasePointFree CriticalZeroScheme LiteralCriticalZeroScheme
open CategoryTheory AlgebraicGeometry MvPolynomial

variable {K : Type} [Field K] [Infinite K] {k : ℕ}
  {n : Fin (k + 1) → ℕ} {m : ℕ}

/-- The full numerical format, with the retained last factor listed first. -/
def fullShape (n : Fin (k + 1) → ℕ) (m : ℕ) : Fin (k + 2) → ℕ :=
  Fin.cases m n

/-- The factor permutation with computational zero/successor formulas. -/
def factorEquiv (k : ℕ) : Fin (k + 2) ≃ Option (Fin (k + 1)) where
  toFun := Fin.cases none some
  invFun x := Option.elim x 0 Fin.succ
  left_inv i := by
    refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv i := by cases i <;> rfl

/-- The actual coefficient array of the original sliced tensor. -/
def fullArray (A : Matrix (Cell n) (Fin (m + 1)) K) : Cell (fullShape n m) → K :=
  fun v => A (fun i => v i.succ) (v 0)

/-- A full product chart contains one pivot in every original factor. -/
def fullPivot (p : Cell n) (j : Fin (m + 1)) : Cell (fullShape n m) :=
  Fin.cases j p

theorem fullPivot_eta (q : Cell (fullShape n m)) :
    fullPivot (fun i => q i.succ) (q 0) = q := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

/-- The change from numerical factor indices to `none`/`some` factor
indices is only a relabeling of their off-pivot coordinates. -/
def freeEquiv (p : Cell n) (j : Fin (m + 1)) (i : Fin (k + 2)) :
    FreeFactor (fullPivot p j) i ≃ FullFree p j (factorEquiv k i) := by
  refine Fin.cases ?_ (fun h => ?_) i
  · exact Equiv.refl _
  · exact Equiv.refl _

/-- The normalized coefficient array is exactly the same full tensor
after the proven factor and coordinate permutation. -/
theorem normalized_fullArray (A : Matrix (Cell n) (Fin (m + 1)) K)
    (p : Cell n) (j : Fin (m + 1)) :
    normalizedTensor (fullArray A) (fullPivot p j) =
      NormalizedFactorReindex.tensor (factorEquiv k) (freeEquiv p j)
        (fullTensor A p j) := by
  funext b
  change A (fun i => Equiv.optionSubtypeNe (p i) (b i.succ))
      (Equiv.optionSubtypeNe j (b 0)) =
    A (fun i => Equiv.optionSubtypeNe (p i)
      (NormalizedFactorReindex.cellEquiv (factorEquiv k)
        (freeEquiv p j) b (some i)))
      (Equiv.optionSubtypeNe j
        (NormalizedFactorReindex.cellEquiv (factorEquiv k)
          (freeEquiv p j) b none))
  apply congrArg₂ A
  · funext i
    congr 1
    have hc : b i.succ = (freeEquiv p j i.succ).optionCongr (b i.succ) := by
      cases b i.succ <;> rfl
    exact hc.trans (NormalizedFactorReindex.cellEquiv_apply (factorEquiv k)
      (freeEquiv p j) b i.succ).symm
  · congr 1
    have hc : b 0 = (freeEquiv p j 0).optionCongr (b 0) := by
      cases b 0 <;> rfl
    exact hc.trans (NormalizedFactorReindex.cellEquiv_apply (factorEquiv k)
      (freeEquiv p j) b 0).symm

/-- The whole normalized numerical chart algebra is the whole nested
full chart algebra used for elimination. -/
def normalizedChartEquiv (A : Matrix (Cell n) (Fin (m + 1)) K)
    (p : Cell n) (j : Fin (m + 1)) :
    (MvPolynomial (CriticalChart.Coordinate (σ := FreeFactor (fullPivot p j))) K ⧸
        Ideal.span (Set.range
          (CriticalChart.criticalEquation (normalizedTensor (fullArray A) (fullPivot p j))))) ≃ₐ[K]
      FullChartRing A p j := by
  rw [normalized_fullArray]
  exact (NormalizedFactorReindex.quotientEquiv (factorEquiv k)
    (freeEquiv p j) (fullTensor A p j)).trans (fullChartQuotientEquiv A p j)

/-- Exact identification of a genuine full singular-scheme chart ring
with the full elimination chart; possible nilpotents are preserved. -/
def fullChartEquiv (A : Matrix (Cell n) (Fin (m + 1)) K)
    (p : Cell n) (j : Fin (m + 1)) :
    (MvPolynomial (ChartVar (fullPivot p j)) K ⧸
        AllFactorPointSpan.chartCriticalIdeal
          (AllFactorIncidence.unitTensorEquiv (fullArray A)) (fullPivot p j)) ≃ₐ[K]
      FullChartRing A p j :=
  (CriticalChartReindex.chartQuotientEquiv (fullArray A) (fullPivot p j)).symm.trans
    (normalizedChartEquiv A p j)

/-- This is the original full singular-tuple zero-scheme, with its actual
closed immersion into the product of every original projective factor. -/
def originalSingularScheme (A : Matrix (Cell n) (Fin (m + 1)) K) : Scheme :=
  singularScheme K (fullShape n m) (fullArray A)

def originalSingularToBase (A : Matrix (Cell n) (Fin (m + 1)) K) :
    originalSingularScheme A ⟶ Spec (.of K) :=
  singularToBase K (fullShape n m) (fullArray A)

/-- Actual global finiteness and reducedness supply every full chart
algebra used in graph elimination, with no additional chart assumption. -/
theorem full_charts_of_original_scheme (A : Matrix (Cell n) (Fin (m + 1)) K)
    (hf : IsFinite (originalSingularToBase A))
    (hr : AlgebraicGeometry.IsReduced (originalSingularScheme A)) :
    ∀ (p : Cell n) (j : Fin (m + 1)),
      Module.Finite K (FullChartRing A p j) ∧ _root_.IsReduced (FullChartRing A p j) := by
  have h := (full_finite_reduced_iff K (fullShape n m) (fullArray A)).mp ⟨hf, hr⟩
  intro p j
  exact ⟨(finite_algEquiv_iff K (fullChartEquiv A p j)).mp (h.1 (fullPivot p j)),
    (reduced_algEquiv_iff K (fullChartEquiv A p j)).mp (h.2 (fullPivot p j))⟩

/-- The original global scheme hypothesis is equivalent to the complete
full-chart criterion. Every original pivot is included in this equivalence. -/
theorem original_finite_reduced_iff (A : Matrix (Cell n) (Fin (m + 1)) K) :
    (IsFinite (originalSingularToBase A) ∧
      AlgebraicGeometry.IsReduced (originalSingularScheme A)) ↔
      ∀ (p : Cell n) (j : Fin (m + 1)),
        Module.Finite K (FullChartRing A p j) ∧
          _root_.IsReduced (FullChartRing A p j) := by
  constructor
  · rintro ⟨hf, hr⟩
    exact full_charts_of_original_scheme A hf hr
  · intro h
    apply (full_finite_reduced_iff K (fullShape n m) (fullArray A)).mpr
    constructor
    · intro q
      have hf := (finite_algEquiv_iff K
        (fullChartEquiv A (fun i => q i.succ) (q 0))).mpr
        (h (fun i => q i.succ) (q 0)).1
      exact Eq.mp (congrArg
        (fun r : Cell (fullShape n m) => Module.Finite K
          (MvPolynomial (ChartVar r) K ⧸ AllFactorPointSpan.chartCriticalIdeal
            (AllFactorIncidence.unitTensorEquiv (fullArray A)) r))
        (fullPivot_eta q)) hf
    · intro q
      have hr := (reduced_algEquiv_iff K
        (fullChartEquiv A (fun i => q i.succ) (q 0))).mpr
        (h (fun i => q i.succ) (q 0)).2
      exact Eq.mp (congrArg
        (fun r : Cell (fullShape n m) => _root_.IsReduced
          (MvPolynomial (ChartVar r) K ⧸ AllFactorPointSpan.chartCriticalIdeal
            (AllFactorIncidence.unitTensorEquiv (fullArray A)) r))
        (fullPivot_eta q)) hr

section BasePointFree

variable [IsAlgClosed K]

/-- The paper's literal absence of a common projective slice zero implies
the unit ideal on every normalized affine chart, by Nullstellensatz. -/
theorem chartSliceIdeal_eq_top_of_no_base_point
    (A : Matrix (Cell n) (Fin (m + 1)) K)
    (hb : ∀ x : FactorPoint n K, lastContraction A x.val ≠ 0) (p : Cell n) :
    chartSliceIdeal A p = ⊤ := by
  have hz : zeroLocus K (chartSliceIdeal A p) = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro z hz
    apply hb (chartPoint p z)
    funext j
    have h := hz (chartSubstitution p (segreForm A j))
      (Ideal.subset_span ⟨j, rfl⟩)
    change MvPolynomial.aeval z (chartSubstitution p (segreForm A j)) = 0 at h
    change MvPolynomial.eval (chartVector p z) (segreForm A j) = 0
    simpa only [aeval_eq_eval, eval_chartSubstitution] using h
  apply Ideal.radical_eq_top.mp
  rw [← vanishingIdeal_zeroLocus_eq_radical (K := K), hz, vanishingIdeal_empty]

/-- Over the paper's algebraically closed field, the literal projective
base-point-free condition and the complete affine unit-ideal cover are
equivalent. -/
theorem no_base_point_iff_chart_unit
    (A : Matrix (Cell n) (Fin (m + 1)) K) :
    (∀ x : FactorPoint n K, lastContraction A x.val ≠ 0) ↔
      ∀ p : Cell n, chartSliceIdeal A p = ⊤ :=
  ⟨fun hb p => chartSliceIdeal_eq_top_of_no_base_point A hb p,
    fun h => lastContraction_ne_zero_of_chart_unit A h⟩

/-- The exact chart hypotheses used in the algebraic proof of
Proposition 2.1 follow from the original global scheme hypotheses and
the original base-point-free slice hypothesis. -/
theorem graph_charts_of_original_scheme (A : Matrix (Cell n) (Fin (m + 1)) K)
    (hb : ∀ x : FactorPoint n K, lastContraction A x.val ≠ 0)
    (hf : IsFinite (originalSingularToBase A))
    (hr : AlgebraicGeometry.IsReduced (originalSingularScheme A)) :
    (∀ p : Cell n, Module.Finite K (MvPolynomial (ChartVar p) K ⧸
      ProjectivePointSpan.chartCriticalIdeal A p)) ∧
    (∀ p : Cell n, _root_.IsReduced (MvPolynomial (ChartVar p) K ⧸
      ProjectivePointSpan.chartCriticalIdeal A p)) := by
  have hfull := full_charts_of_original_scheme A hf hr
  have hbase := chartSliceIdeal_eq_top_of_no_base_point A hb
  exact ⟨fun p => graphChart_finite_of_full_charts A p (hbase p)
      (fun j => (hfull p j).1),
    fun p => graphChart_reduced_of_full_charts A p (hbase p)
      (fun j => (hfull p j).2)⟩

/-- In particular, the genuine graph critical scheme is finite and reduced;
this is a theorem about actual schemes, not a renamed chart condition. -/
theorem graph_scheme_of_original_scheme (A : Matrix (Cell n) (Fin (m + 1)) K)
    (hb : ∀ x : FactorPoint n K, lastContraction A x.val ≠ 0)
    (hf : IsFinite (originalSingularToBase A))
    (hr : AlgebraicGeometry.IsReduced (originalSingularScheme A)) :
    IsFinite (graphToBase K n A) ∧ AlgebraicGeometry.IsReduced (graphScheme K n A) :=
  (graph_finite_reduced_iff K n A).mpr (graph_charts_of_original_scheme A hb hf hr)

end BasePointFree
end PaperVerification.Segre.SingularSchemeGraphCharts

end SegreSingularSchemeGraphCharts


end SegreProjectiveTheorems

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
