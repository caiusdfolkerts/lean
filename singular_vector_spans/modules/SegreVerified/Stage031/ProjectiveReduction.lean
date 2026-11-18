module
public import SegreVerified.Stage030
public import SegreVerified.Stage031.CriticalFactorReindex
public import Mathlib.LinearAlgebra.Projectivization.Subspace
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

run_cmd do
  let out ← IO.getStderr
  out.putStrLn "SEGRE_STAGE Stage031.ProjectiveReduction"
  out.flush

/-!
# The original embedded scheme and the principal projective span theorems

The named sections preserve the original proof stages and local scopes.
-/



section SegreMatrixFirstExcess

/-!
# The matrix addendum without an impossible slice-independence hypothesis

For one smaller projective factor, the first-excess family has more slices
than the degree-one space. Its slices therefore cannot all be independent.
The degree-one quotient by the old parameters is zero, which proves enlarged
degree-two Koszul exactness directly. This file retains that full kernel
equality and combines it with the actual geometric prerequisites.

-/

set_option autoImplicit false

namespace PaperVerification.Segre.MatrixFirstExcess

open Staircase Monomials RankParameters Degeneration KoszulDimension
open LefschetzBridge ParameterProducts ActualLefschetz GenericFirstLefschetz
open GenericSurjectivity CommonGraphOpen

variable {I D K : Type} [Fintype I] [DecidableEq I]
  [Fintype D] [DecidableEq D] [Field K] {n : I → ℕ}

/-- Injective actual Lefschetz multiplication and old degree-two exactness
imply enlarged exactness without independence of the enlarged family. -/
theorem enlarged_exactness_of_injective
    (A : Matrix (Cell n) (Option D) K)
    (hold : LinearMap.ker (KoszulRank.multiplication (oldForms A)) =
      LinearMap.range (koszulMatrix (oldForms A)))
    (hℓ : Function.Injective
      (GeneralQuotient.firstLefschetz (oldForms A) (lefschetzForm A))) :
    LinearMap.ker (KoszulRank.multiplication A) =
      LinearMap.range (koszulMatrix A) := by
  apply FixedLefschetzRanks.matrix_exactness_of_actual
  rw [enlarged_forms]
  let θ := forms (oldForms A)
  let ℓ := lefschetzForm A
  have hexact : LinearMap.ker (multiply polynomialProduct θ) = pairRelations θ :=
    actual_exactness_of_matrix_exactness (oldForms A) hold
  apply le_antisymm
  · intro g hg
    have hwide : splitOption (K := K) g ∈ LinearMap.ker (wideMultiply polynomialProduct θ ℓ) := by
      change wideMultiply polynomialProduct θ ℓ (splitOption (K := K) g) = 0
      rw [← multiply_splitOption]
      exact LinearMap.mem_ker.mp hg
    have hproduct : ℓ.val * (g none).val ∈ productSpan (oldForms A) := by
      rw [← range_actual_multiply]
      refine ⟨-(fun r => g (some r)), ?_⟩
      rw [map_neg]
      have he : ℓ.val * (g none).val +
          multiply polynomialProduct θ (fun r => g (some r)) = 0 := hwide
      exact (eq_neg_of_add_eq_zero_left he).symm
    have hfirst : g none ∈ parameterSpan (K := K) θ :=
      (GeneralQuotient.firstLefschetz_injective_iff (oldForms A) ℓ).mp hℓ
        (g none) hproduct
    let z : LinearMap.ker (wideMultiply polynomialProduct θ ℓ) := ⟨splitOption g, hwide⟩
    have hz : z ∈ LinearMap.ker (cycleProjection polynomialProduct polynomialProduct_comm θ ℓ) := by
      apply Subtype.ext
      exact (Submodule.Quotient.mk_eq_zero (parameterSpan (K := K) θ)).mpr hfirst
    rw [kernel_cycleProjection polynomialProduct polynomialProduct_comm θ ℓ hexact] at hz
    have hmem : splitOption (K := K) g ∈ widePairRelations (K := K) θ ℓ := hz
    rw [← widePairRelations_eq_pairRelations] at hmem
    obtain ⟨g', hg', he⟩ := hmem
    exact (splitOption.injective he) ▸ hg'
  · exact pairRelations_le_kernel polynomialProduct polynomialProduct_comm _

/-- One-factor first-excess matrices have no non-Koszul degree-two relations
on an explicit full-coefficient open, despite their dependent slice columns. -/
theorem matrix_exactness_certificate [Infinite K] (n : Fin 1 → ℕ) :
    ∃ f : MvPolynomial (Cell n × Option (Ranks n)) K, f ≠ 0 ∧
      ∀ A : Matrix (Cell n) (Option (Ranks n)) K,
        MvPolynomial.eval (fun q => A q.1 q.2) f ≠ 0 →
          LinearMap.ker (KoszulRank.multiplication A) =
            LinearMap.range (koszulMatrix A) := by
  obtain ⟨r, hr, hrw⟩ := OneFactor.one_factor_rank_certificate (K := K) n
  obtain ⟨b, hb, hbw⟩ := baseline_certificate (K := K) (n := n)
  let f := MvPolynomial.rename (oldVariable (n := n) (D := Ranks n)) (r * b)
  have hf : f ≠ 0 := by
    intro h
    exact mul_ne_zero hr hb ((MvPolynomial.rename_eq_zero_iff_of_injective (r * b)
      (oldVariable (n := n) (D := Ranks n)).injective).mp h)
  refine ⟨f, hf, ?_⟩
  intro A hA
  have hOld : MvPolynomial.eval (fun q => oldForms A q.1 q.2) (r * b) ≠ 0 := by
    simpa only [f, MvPolynomial.eval_rename, Function.comp_def, oldVariable,
      Function.Embedding.coeFn_mk, oldForms] using hA
  rw [map_mul] at hOld
  obtain ⟨hAr, hAb⟩ := mul_ne_zero_iff.mp hOld
  have hrows := hrw (oldForms A) hAr
  have hcols : Function.Surjective (oldForms A).vecMul :=
    Matrix.vecMul_surjective_iff_rank_eq_card.mpr
      ((Matrix.mulVec_surjective_iff_rank_eq_card.mp hrows).trans
        (OneFactor.card_cells_eq_ranks n))
  have hold := KoszulRank.kernel_eq_koszul_range_of_rank_bound (oldForms A)
    hcols (hbw (oldForms A) hAb)
  exact enlarged_exactness_of_injective A hold
    (OneFactorActual.firstLefschetz_injective_of_full_rows (oldForms A) hrows _)

/-- The matrix addendum has the same actual nonempty geometric open; no
extra slice-independence condition is introduced. -/
theorem matrix_common_data [Infinite K] (n : Fin 1 → ℕ) :
    ∃ r : MvPolynomial (Cell n × Option (Ranks n)) K, r ≠ 0 ∧
      (∃ A : Matrix (Cell n) (Option (Ranks n)) K,
        MvPolynomial.eval (fun q => A q.1 q.2) r ≠ 0) ∧
      ∀ A : Matrix (Cell n) (Option (Ranks n)) K,
        MvPolynomial.eval (fun q => A q.1 q.2) r ≠ 0 →
          RegularData A ∧
            LinearMap.ker (KoszulRank.multiplication A) =
              LinearMap.range (koszulMatrix A) := by
  apply combine_certificate
    (show sideSum n + 1 ≤ Fintype.card (Option (Ranks n)) by
      simp only [Fintype.card_option, Ranks, Fintype.card_fin]
      omega)
  exact matrix_exactness_certificate n

end PaperVerification.Segre.MatrixFirstExcess

end SegreMatrixFirstExcess

section SegreGeometricPrincipal

/-!
# The geometric principal theorems on the full tensor coefficient space

The actual sheaf Koszul resolution supplies the chart-image identity used
here. The nonzero coefficient certificates already combine every algebraic,
finite-scheme, reducedness, and independence condition. Consequently the
principal statements below have no geometric image or exactness hypothesis.

The index `Option (Fin (sideSum n + e))` has cardinality `sideSum n + e + 1`;
it describes the full last tensor factor of the paper, without a distinguished
slice or restriction on its coefficients. Every certificate includes an
actual point of its nonvanishing locus over the original field.

-/

set_option autoImplicit false
open scoped BigOperators

namespace PaperVerification.Segre.GeometricPrincipal

open Staircase Monomials RankParameters GraphSpan CriticalGraph SingularSpan
open ProjectiveCharts ProjectivePointSpan CommonGraphOpen PrincipalCommonOpen
open GraphConclusionAssembly

/-- The last coefficient index has exactly the paper's full dimension. -/
theorem last_factor_dimension {k : ℕ} (n : Fin k → ℕ) (e : ℕ) :
    Fintype.card (Option (Fin (sideSum n + e))) = sideSum n + e + 1 := by
  simp only [Fintype.card_option, Fintype.card_fin]

variable {K : Type} [Field K] [Infinite K] [IsAlgClosed K]

/-- The finite-chart geometric theorem works for every positive number of
smaller factors. The successor presentation used by the product construction
does not impose an additional restriction on the theorem's parameter. -/
theorem chart_image_identity {k : ℕ} (hk : 0 < k) (n : Fin k → ℕ)
    {J : Type} [Fintype J] [DecidableEq J] (A : Matrix (Cell n) J K)
    (hfinite : ∀ p : Cell n,
      Module.Finite K (MvPolynomial (ChartVar p) K ⧸ chartCriticalIdeal A p)) :
    ChartImageIdentity A := by
  cases k with
  | zero => omega
  | succ k =>
      exact GraphGeometry.graph_chart_image_identity (K := K) (n := n) A hfinite

/-- The graph-span equality, its dimension formula, and membership of the
original tensor hold together on one nonempty full-coefficient open. -/
theorem generic_graph_span {k : ℕ} (hk : 0 < k) (n : Fin k → ℕ)
    {J : Type} [Fintype J] [DecidableEq J]
    (hlen : sideSum n + 1 ≤ Fintype.card J) :
    ∃ r : MvPolynomial (Cell n × J) K, r ≠ 0 ∧
      (∃ A : Matrix (Cell n) J K,
        MvPolynomial.eval (fun q => A q.1 q.2) r ≠ 0) ∧
      ∀ A : Matrix (Cell n) J K,
        MvPolynomial.eval (fun q => A q.1 q.2) r ≠ 0 →
          singularSpan A = graphSpan A ⊓ fullCriticalSpace A ∧
          Module.finrank K (singularSpan A) =
            (Degeneration.multiplicationMatrix 1 A).rank -
              ∑ i, (n i + 1).choose 2 ∧
          A ∈ singularSpan A := by
  obtain ⟨r, hr, hw⟩ := regular_certificate (K := K) hlen
  refine ⟨r, hr, nonempty_coefficient_open r hr, ?_⟩
  intro A hA
  have hreg := hw A hA
  exact graph_span_conclusions A hreg
    (chart_image_identity hk n A hreg.finiteChart)

/-- Corollary 1.2, including the projective-line addendum: every positive
tuple with at least two smaller factors has exactly the literal first-excess
defect. The equality criterion records full span as well as its codimension.
The explicitly evaluated defect table is given below. -/
theorem corollary_1_2 (k : ℕ) (hk : 2 ≤ k) (n : Fin k → ℕ)
    (hpos : ∀ i, 1 ≤ n i) :
    ∃ r : MvPolynomial (Cell n × Option (Ranks n)) K, r ≠ 0 ∧
      (∃ A : Matrix (Cell n) (Option (Ranks n)) K,
        MvPolynomial.eval (fun q => A q.1 q.2) r ≠ 0) ∧
      ∀ A : Matrix (Cell n) (Option (Ranks n)) K,
        MvPolynomial.eval (fun q => A q.1 q.2) r ≠ 0 →
          Module.finrank K (fullCriticalSpace A) - Module.finrank K (singularSpan A) =
            Principal.kernelDefect k n ∧
          (singularSpan A = fullCriticalSpace A ↔ Principal.kernelDefect k n = 0) ∧
          A ∈ singularSpan A := by
  obtain ⟨r, hr, hne, hw⟩ := first_excess_common_data (K := K) k hk n hpos
  refine ⟨r, hr, hne, ?_⟩
  intro A hA
  obtain ⟨hreg, hcols, hker⟩ := hw A hA
  have himage := chart_image_identity (by omega) n A hreg.finiteChart
  have hspan := graph_span_conclusions A hreg himage
  have hdefect := first_excess_defect n A hreg hcols hker himage
  refine ⟨hdefect, ?_, hspan.2.2⟩
  have hle : singularSpan A ≤ fullCriticalSpace A := by
    rw [hspan.1]
    exact inf_le_right
  constructor
  · intro heq
    have hdim := congrArg
      (fun S : Submodule K (Matrix (Cell n) (Option (Ranks n)) K) =>
        Module.finrank K S) heq
    omega
  · intro hz
    apply Submodule.eq_of_le_of_finrank_le hle
    exact Nat.sub_eq_zero_iff_le.mp (hdefect.trans hz)

/-- The matrix addendum uses the actual kernel equality; no independence
of the enlarged slice family is imposed. -/
theorem matrix_first_excess (n : Fin 1 → ℕ) :
    ∃ r : MvPolynomial (Cell n × Option (Ranks n)) K, r ≠ 0 ∧
      (∃ A : Matrix (Cell n) (Option (Ranks n)) K,
        MvPolynomial.eval (fun q => A q.1 q.2) r ≠ 0) ∧
      ∀ A : Matrix (Cell n) (Option (Ranks n)) K,
        MvPolynomial.eval (fun q => A q.1 q.2) r ≠ 0 →
          singularSpan A = fullCriticalSpace A := by
  obtain ⟨r, hr, hne, hw⟩ := MatrixFirstExcess.matrix_common_data (K := K) n
  refine ⟨r, hr, hne, ?_⟩
  intro A hA
  obtain ⟨hreg, hexact⟩ := hw A hA
  exact full_span_of_exact_kernel A hreg hexact
    (chart_image_identity (by decide) n A hreg.finiteChart)

/-- Convert the complete common-open certificate to a principal full-span
conclusion. The actual geometric input is proved by `GraphGeometry`. -/
theorem full_span_of_common_certificate {k e : ℕ} (hk : 0 < k)
    (n : Fin k → ℕ)
    (h : ∃ r : MvPolynomial (Cell n × Option (Fin (sideSum n + e))) K,
      r ≠ 0 ∧
      (∃ A : Matrix (Cell n) (Option (Fin (sideSum n + e))) K,
        MvPolynomial.eval (fun q => A q.1 q.2) r ≠ 0) ∧
      ∀ A : Matrix (Cell n) (Option (Fin (sideSum n + e))) K,
        MvPolynomial.eval (fun q => A q.1 q.2) r ≠ 0 → ExactData A) :
    ∃ r : MvPolynomial (Cell n × Option (Fin (sideSum n + e))) K, r ≠ 0 ∧
      (∃ A : Matrix (Cell n) (Option (Fin (sideSum n + e))) K,
        MvPolynomial.eval (fun q => A q.1 q.2) r ≠ 0) ∧
      ∀ A : Matrix (Cell n) (Option (Fin (sideSum n + e))) K,
        MvPolynomial.eval (fun q => A q.1 q.2) r ≠ 0 →
          singularSpan A = fullCriticalSpace A := by
  obtain ⟨r, hr, hne, hw⟩ := h
  refine ⟨r, hr, hne, ?_⟩
  intro A hA
  have hdata := hw A hA
  exact full_span A hdata (chart_image_identity hk n A hdata.1.finiteChart)

/-- The first complete parameter range in Theorem 6.1: `k ≥ 4e`, with
every positive smaller factor dimension and every excess `e ≥ 1`. -/
theorem theorem_6_1_first (k e : ℕ) (he : 1 ≤ e) (hk : 4 * e ≤ k)
    (n : Fin k → ℕ) (hpos : ∀ i, 1 ≤ n i) :
    ∃ r : MvPolynomial (Cell n × Option (Fin (sideSum n + e))) K, r ≠ 0 ∧
      (∃ A : Matrix (Cell n) (Option (Fin (sideSum n + e))) K,
        MvPolynomial.eval (fun q => A q.1 q.2) r ≠ 0) ∧
      ∀ A : Matrix (Cell n) (Option (Fin (sideSum n + e))) K,
        MvPolynomial.eval (fun q => A q.1 q.2) r ≠ 0 →
          singularSpan A = fullCriticalSpace A :=
  full_span_of_common_certificate (by omega) n
    (section_6_1_first_common_data k e he hk n hpos)

/-- The full three-block criterion in Theorem 6.1. Natural subtraction
agrees with the printed integer expression throughout `b ≥ 4`. -/
theorem theorem_6_1_second (b e k : ℕ) (hb : 4 ≤ b) (he : 1 ≤ e)
    (hbound : e ≤ 2 ^ b - 3 * b + 1) (hk : 3 * b ≤ k)
    (n : Fin k → ℕ) (hpos : ∀ i, 1 ≤ n i) :
    ∃ r : MvPolynomial (Cell n × Option (Fin (sideSum n + e))) K, r ≠ 0 ∧
      (∃ A : Matrix (Cell n) (Option (Fin (sideSum n + e))) K,
        MvPolynomial.eval (fun q => A q.1 q.2) r ≠ 0) ∧
      ∀ A : Matrix (Cell n) (Option (Fin (sideSum n + e))) K,
        MvPolynomial.eval (fun q => A q.1 q.2) r ≠ 0 →
          singularSpan A = fullCriticalSpace A :=
  full_span_of_common_certificate (by omega) n
    (section_6_1_second_common_data b e k hb he hbound hk n hpos)

/-- The literal integer ceiling of the real logarithm in Theorem 6.1. -/
theorem theorem_6_1_logarithmic (k e : ℕ) (he : 3 ≤ e)
    (hk : 3 * ⌈Real.logb 2 (4 * (e : ℝ))⌉ ≤ (k : ℤ))
    (n : Fin k → ℕ) (hpos : ∀ i, 1 ≤ n i) :
    ∃ r : MvPolynomial (Cell n × Option (Fin (sideSum n + e))) K, r ≠ 0 ∧
      (∃ A : Matrix (Cell n) (Option (Fin (sideSum n + e))) K,
        MvPolynomial.eval (fun q => A q.1 q.2) r ≠ 0) ∧
      ∀ A : Matrix (Cell n) (Option (Fin (sideSum n + e))) K,
        MvPolynomial.eval (fun q => A q.1 q.2) r ≠ 0 →
          singularSpan A = fullCriticalSpace A := by
  have hk' := (ExcessLogarithmic.logarithmic_bound_iff k e (by omega)).mp hk
  have hb := (ExcessLogarithmic.logarithmic_parameters e he).1
  exact full_span_of_common_certificate (by omega) n
    (section_6_1_logarithmic_common_data k e he hk n hpos)

/-- Theorem 6.3 with its exact threshold, balanced-power inequality, and
the complete unbounded range of larger tuples. -/
theorem theorem_6_3 (k e L : ℕ) (hk : 3 ≤ k) (he : 2 ≤ e)
    (hL : DiagonalCore.minimumSide k ≤ L)
    (hbound : k * ExcessSixThree.threshold k e L + e ≤
      (L + 1) ^ (k / 2) + (L + 1) ^ ((k + 1) / 2))
    (n : Fin k → ℕ) (hn : ∀ i, ExcessSixThree.threshold k e L ≤ n i) :
    ∃ r : MvPolynomial (Cell n × Option (Fin (sideSum n + e))) K, r ≠ 0 ∧
      (∃ A : Matrix (Cell n) (Option (Fin (sideSum n + e))) K,
        MvPolynomial.eval (fun q => A q.1 q.2) r ≠ 0) ∧
      ∀ A : Matrix (Cell n) (Option (Fin (sideSum n + e))) K,
        MvPolynomial.eval (fun q => A q.1 q.2) r ≠ 0 →
          singularSpan A = fullCriticalSpace A :=
  full_span_of_common_certificate (by omega) n
    (section_6_3_common_data k e L hk he hL hbound n hn)

/-- The uniform `nᵢ ≥ 3e²` consequence following Theorem 6.3. -/
theorem uniform_large_factors (k e : ℕ) (hk : 3 ≤ k) (he : 2 ≤ e)
    (n : Fin k → ℕ) (hn : ∀ i, 3 * e ^ 2 ≤ n i) :
    ∃ r : MvPolynomial (Cell n × Option (Fin (sideSum n + e))) K, r ≠ 0 ∧
      (∃ A : Matrix (Cell n) (Option (Fin (sideSum n + e))) K,
        MvPolynomial.eval (fun q => A q.1 q.2) r ≠ 0) ∧
      ∀ A : Matrix (Cell n) (Option (Fin (sideSum n + e))) K,
        MvPolynomial.eval (fun q => A q.1 q.2) r ≠ 0 →
          singularSpan A = fullCriticalSpace A :=
  full_span_of_common_certificate (by omega) n
    (uniform_large_common_data k e hk he n hn)

/-- The improved `nᵢ ≥ 6` bound for excess two in every `k ≥ 3`. -/
theorem excess_two_six (k : ℕ) (hk : 3 ≤ k)
    (n : Fin k → ℕ) (hn : ∀ i, 6 ≤ n i) :
    ∃ r : MvPolynomial (Cell n × Option (Fin (sideSum n + 2))) K, r ≠ 0 ∧
      (∃ A : Matrix (Cell n) (Option (Fin (sideSum n + 2))) K,
        MvPolynomial.eval (fun q => A q.1 q.2) r ≠ 0) ∧
      ∀ A : Matrix (Cell n) (Option (Fin (sideSum n + 2))) K,
        MvPolynomial.eval (fun q => A q.1 q.2) r ≠ 0 →
          singularSpan A = fullCriticalSpace A :=
  full_span_of_common_certificate (by omega) n
    (excess_two_common_data k hk n hn)

end PaperVerification.Segre.GeometricPrincipal

end SegreGeometricPrincipal

section SegreGeometricDefectTable

/-!
# Literal interpretation of the first-excess defect table

These identities unpack the defect in `GeometricPrincipal.corollary_1_2`.
They prove the correspondence with each printed format and with the complete
nonexceptional ranges, including all permutations of the three smaller
factors and the unbounded projective-line family.

-/

set_option autoImplicit false
open scoped Classical BigOperators

namespace PaperVerification.Segre.GeometricDefectTable

open Staircase ChainClassification ThreeChainCores

theorem two_factor_defect (n : Fin 2 → ℕ) :
    Principal.kernelDefect 2 n = TwoFactorGeneric.kernelDefect (n 0) (n 1) := by
  simp [Principal.kernelDefect]

theorem three_factor_defect (n : Fin 3 → ℕ) :
    Principal.kernelDefect 3 n =
      if ExceptionalTriple n then (if sideSum n ≤ 4 then 3 else 1) else 0 := by
  simp [Principal.kernelDefect, ThreeFactorLefschetz.kernelDefect]

/-- For two smaller factors of projective dimension at least two, the
table has exactly the three unordered pairs printed in Corollary 1.2. -/
theorem two_factor_table (n : Fin 2 → ℕ) (h0 : 2 ≤ n 0) (h1 : 2 ≤ n 1) :
    Principal.kernelDefect 2 n =
      if (n 0 = 2 ∧ n 1 = 4) ∨ (n 0 = 4 ∧ n 1 = 2) then 2
      else if (n 0 = 2 ∧ (n 1 = 2 ∨ n 1 = 3)) ∨
        (n 1 = 2 ∧ (n 0 = 2 ∨ n 0 = 3)) then 3 else 0 := by
  rw [two_factor_defect]
  simp only [TwoFactorGeneric.kernelDefect,
    if_neg (show ¬(n 0 = 1 ∨ n 1 = 1) by omega)]
  unfold TwoFactorInjectivity.Exceptional
  split_ifs <;> omega

/-- The remaining `(2,b+1,b+3)` family has defect exactly `b`, in
either order of the two smaller factors. There is no bound on `b`. -/
theorem projective_line_defect (n : Fin 2 → ℕ) (hline : n 0 = 1 ∨ n 1 = 1) :
    Principal.kernelDefect 2 n = n 0 * n 1 := by
  rw [two_factor_defect]
  simp only [TwoFactorGeneric.kernelDefect, if_pos hline]

/-- The tensor formats `(3,3,6)` and `(3,4,7)` have defect three. -/
theorem two_factor_defect_three (n : Fin 2 → ℕ)
    (h : (n 0 = 2 ∧ (n 1 = 2 ∨ n 1 = 3)) ∨
      (n 1 = 2 ∧ (n 0 = 2 ∨ n 0 = 3))) :
    Principal.kernelDefect 2 n = 3 := by
  rw [two_factor_table n (by omega) (by omega)]
  split_ifs <;> omega

/-- The tensor format `(3,5,8)` has defect two in both factor orders. -/
theorem two_factor_defect_two (n : Fin 2 → ℕ)
    (h : (n 0 = 2 ∧ n 1 = 4) ∨ (n 0 = 4 ∧ n 1 = 2)) :
    Principal.kernelDefect 2 n = 2 := by
  rw [two_factor_table n (by omega) (by omega), if_pos h]

private theorem sideSum_of_permutation (n m : Fin 3 → ℕ)
    (e : Equiv.Perm (Fin 3)) (h : (fun i => n (e i)) = m) :
    sideSum n = sideSum m := by
  rw [← sideSum_reindex n e, h]

/-- The format `(2,2,2,5)` has defect three under every permutation of
its three smaller factors. -/
theorem triple_111 (n : Fin 3 → ℕ) (e : Equiv.Perm (Fin 3))
    (h : (fun i => n (e i)) = shape111) : Principal.kernelDefect 3 n = 3 := by
  have hex : ExceptionalTriple n := ⟨e, Or.inl h⟩
  have hsum : sideSum n = 3 := by
    rw [sideSum_of_permutation n shape111 e h]
    norm_num [sideSum, shape111, Fin.sum_univ_succ]
  rw [three_factor_defect, if_pos hex, hsum] <;> norm_num

/-- The format `(2,2,3,6)` has defect three under every permutation of
its three smaller factors. -/
theorem triple_112 (n : Fin 3 → ℕ) (e : Equiv.Perm (Fin 3))
    (h : (fun i => n (e i)) = shape112) : Principal.kernelDefect 3 n = 3 := by
  have hex : ExceptionalTriple n := ⟨e, Or.inr (Or.inl h)⟩
  have hsum : sideSum n = 4 := by
    rw [sideSum_of_permutation n shape112 e h]
    norm_num [sideSum, shape112, Fin.sum_univ_succ]
  rw [three_factor_defect, if_pos hex, hsum] <;> norm_num

/-- The format `(2,2,4,7)` has defect one under every permutation of
its three smaller factors. -/
theorem triple_113 (n : Fin 3 → ℕ) (e : Equiv.Perm (Fin 3))
    (h : (fun i => n (e i)) = shape113) : Principal.kernelDefect 3 n = 1 := by
  have hex : ExceptionalTriple n := ⟨e, Or.inr (Or.inr h)⟩
  have hsum : sideSum n = 5 := by
    rw [sideSum_of_permutation n shape113 e h]
    norm_num [sideSum, shape113, Fin.sum_univ_succ]
  rw [three_factor_defect, if_pos hex, hsum] <;> norm_num

/-- Every other triple has defect zero; the exceptional predicate is the
literal three-family permutation predicate, not a bounded enumeration. -/
theorem triple_nonexceptional (n : Fin 3 → ℕ) (h : ¬ExceptionalTriple n) :
    Principal.kernelDefect 3 n = 0 := by
  rw [three_factor_defect, if_neg h]

/-- There are no first-excess exceptions with four or more smaller
factors. -/
theorem at_least_four (k : ℕ) (hk : 4 ≤ k) (n : Fin k → ℕ) :
    Principal.kernelDefect k n = 0 := by
  simp only [Principal.kernelDefect, dif_neg (show k ≠ 2 by omega),
    dif_neg (show k ≠ 3 by omega)]

/-- The one-smaller-factor defect is zero, matching the separately
proved matrix full-span theorem. -/
theorem one_factor (n : Fin 1 → ℕ) : Principal.kernelDefect 1 n = 0 := by
  simp [Principal.kernelDefect]

end PaperVerification.Segre.GeometricDefectTable

end SegreGeometricDefectTable

section SegrePermutedCorollary

/-!
# The full factor-permutation clause of Corollary 1.2

Every permutation includes the originally distinguished last factor. The
coefficient polynomial is transported through actual variable bijections,
and both the singular span and the full critical space are transported
through the same actual linear equivalence. The conclusion is therefore a
defect in the complete original tensor space in the new factor order.

-/

set_option autoImplicit false
open scoped Classical

namespace PaperVerification.Segre.PermutedCorollary

open Staircase RankParameters TensorFactorReindex FullGraphChartReindex
open CriticalFactorReindex

variable {K : Type} [Field K] [Infinite K] [IsAlgClosed K]

omit [IsAlgClosed K] in
/-- Nonzero coefficient polynomials have an actual nonzero evaluation on
the full affine tensor coefficient space over the original field. -/
theorem nonempty_open {α : Type} (p : MvPolynomial α K) (hp : p ≠ 0) :
    ∃ T : α → K, MvPolynomial.eval T p ≠ 0 := by
  by_contra h
  push_neg at h
  apply hp
  apply MvPolynomial.funext
  intro T
  simpa only [map_zero] using h T

/-- Corollary 1.2 in every order of all tensor factors, with exactly the
same first-excess defect and a nonempty open in all original coefficients. -/
theorem corollary_1_2_permuted (k : ℕ) (hk : 2 ≤ k)
    (n : Fin k → ℕ) (hpos : ∀ i, 1 ≤ n i)
    (e : Equiv.Perm (Option (Fin k))) :
    ∃ p : MvPolynomial
      (∀ i : Option (Fin k), FullFactor n (Option (Ranks n)) (e i)) K,
      p ≠ 0 ∧
      (∃ T, MvPolynomial.eval T p ≠ 0) ∧
      ∀ T, MvPolynomial.eval T p ≠ 0 →
        Module.finrank K (criticalSpace T) - Module.finrank K (incidenceSpan T) =
          Principal.kernelDefect k n := by
  obtain ⟨p, hp, _, hw⟩ := GeometricPrincipal.corollary_1_2 (K := K) k hk n hpos
  have hs := generic_defect_of_slices (Principal.kernelDefect k n)
    ⟨p, hp, fun A hA => (hw A hA).1⟩
  obtain ⟨q, hq, hqw⟩ := generic_defect_reindex e (Principal.kernelDefect k n) hs
  exact ⟨q, hq, nonempty_open q hq, hqw⟩

end PaperVerification.Segre.PermutedCorollary

end SegrePermutedCorollary

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
