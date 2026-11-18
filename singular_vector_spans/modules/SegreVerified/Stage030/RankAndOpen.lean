module
public import SegreVerified.Stage030.TensorCoordinates
public import SegreVerified.Stage028.GraphGenericity
public import SegreVerified.Stage029
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


section SegreTensorSpanTheorems

run_cmd do
  let out ← IO.getStderr
  out.putStrLn "SEGRE_STAGE Stage030.RankAndOpen"
  out.flush

/-!
# The graph-span comparison and tensor membership in all formats

The named sections preserve the original proof stages and local scopes.
-/


section SegreCommonGraphOpen

/-!
# One actual coefficient open for every graph-span prerequisite

The generic algebraic and geometric statements must hold at the same tensor.
This file multiplies their nonzero polynomial certificates in the complete
original slice-coefficient space and proves that the common principal open
has an actual point. The geometric data concern the literal chart ideals and
unreduced quotient rings. No genericity, reducedness, or critical-independence
claim is introduced as an assumption.

-/

set_option autoImplicit false

namespace PaperVerification.Segre.CommonGraphOpen

open Staircase Monomials GraphSpan CriticalGraph SingularSpan ProjectiveCharts
open ProjectivePointSpan SpanDefect ChartBasePointFree
open scoped BigOperators

variable {I J K : Type} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Field K] [Infinite K] {n : I → ℕ}

/-- All the actual graph-span prerequisites at one tensor. In particular,
`finiteChart` and `reducedChart` refer to the original equation quotient, not
to a radical quotient or a selected subset of points. -/
structure RegularData (A : Matrix (Cell n) J K) : Prop where
  sliceUnit : ∀ p : Cell n, chartSliceIdeal A p = ⊤
  basePointFree : ∀ x : FactorPoint n K, lastContraction A x.val ≠ 0
  finiteChart : ∀ p : Cell n,
    Module.Finite K (MvPolynomial (ChartVar p) K ⧸ chartCriticalIdeal A p)
  reducedChart : ∀ p : Cell n,
    IsReduced (MvPolynomial (ChartVar p) K ⧸ chartCriticalIdeal A p)
  independentCritical :
    Disjoint (LinearMap.ker (multiplicationOnCovectors A)) (smallRelations A)
  criticalDimension : Module.finrank K (smallRelations A) =
    ∑ i, (n i + 1).choose 2

/-- A nonzero polynomial in the full coefficient array has an actual
nonzero evaluation over the original infinite field. -/
theorem nonempty_coefficient_open
    (r : MvPolynomial (Cell n × J) K) (hr : r ≠ 0) :
    ∃ A : Matrix (Cell n) J K, MvPolynomial.eval (fun q => A q.1 q.2) r ≠ 0 := by
  by_contra h
  push_neg at h
  apply hr
  apply MvPolynomial.funext
  intro v
  simpa only [map_zero] using h (fun u j => v (u, j))

/-- The exact graph-format range has a single nonzero polynomial certifying
all its geometric prerequisites simultaneously. -/
theorem regular_certificate (hlen : sideSum n + 1 ≤ Fintype.card J) :
    ∃ r : MvPolynomial (Cell n × J) K, r ≠ 0 ∧
      ∀ A : Matrix (Cell n) J K,
        MvPolynomial.eval (fun q => A q.1 q.2) r ≠ 0 → RegularData A := by
  obtain ⟨b, hb, hbw⟩ := GeometricBasePointFree.chart_certificate (K := K) hlen
  obtain ⟨g, hg, hgw⟩ :=
    GenericGraphChartCertificate.exists_graph_chart_certificate (K := K) hlen
  obtain ⟨c, hc, hcw⟩ :=
    StarCriticalWitness.generic_independence_dimension (K := K) hlen
  refine ⟨b * g * c, mul_ne_zero (mul_ne_zero hb hg) hc, ?_⟩
  intro A hA
  rw [map_mul, map_mul] at hA
  obtain ⟨hbg, hAc⟩ := mul_ne_zero_iff.mp hA
  obtain ⟨hAb, hAg⟩ := mul_ne_zero_iff.mp hbg
  have hgA := hgw A hAg
  have hcA := hcw A hAc
  exact
    { sliceUnit := fun p => chartSliceIdeal_eq_top A p (hbw A hAb p)
      basePointFree := hgA.1
      finiteChart := fun p => (hgA.2 p).1
      reducedChart := fun p => (hgA.2 p).2
      independentCritical := hcA.1
      criticalDimension := hcA.2 }

/-- Combine any full-coefficient algebraic certificate with all the actual
geometric certificates. Nonemptiness is part of the conclusion. -/
theorem combine_certificate (hlen : sideSum n + 1 ≤ Fintype.card J)
    (P : Matrix (Cell n) J K → Prop)
    (hP : ∃ f : MvPolynomial (Cell n × J) K, f ≠ 0 ∧
      ∀ A : Matrix (Cell n) J K,
        MvPolynomial.eval (fun q => A q.1 q.2) f ≠ 0 → P A) :
    ∃ r : MvPolynomial (Cell n × J) K, r ≠ 0 ∧
      (∃ A : Matrix (Cell n) J K, MvPolynomial.eval (fun q => A q.1 q.2) r ≠ 0) ∧
      ∀ A : Matrix (Cell n) J K,
        MvPolynomial.eval (fun q => A q.1 q.2) r ≠ 0 → RegularData A ∧ P A := by
  obtain ⟨f, hf, hfw⟩ := hP
  obtain ⟨g, hg, hgw⟩ := regular_certificate (K := K) hlen
  refine ⟨f * g, mul_ne_zero hf hg, nonempty_coefficient_open _ (mul_ne_zero hf hg), ?_⟩
  intro A hA
  rw [map_mul] at hA
  obtain ⟨hAf, hAg⟩ := mul_ne_zero_iff.mp hA
  exact ⟨hgw A hAg, hfw A hAf⟩

/-- The actual point-span annihilator is the intersection of the original
defining ideals, at every tensor in the common open. -/
theorem annihilator_eq_chart_intersection [IsAlgClosed K]
    (A : Matrix (Cell n) J K) (hA : RegularData A) :
    (singularSpan A).dualAnnihilator =
      ⨅ p : Cell n, ((chartCriticalIdeal A p).restrictScalars K).comap
        (ProjectivePointSpan.chartRestriction A p) :=
  ProjectivePointSpan.singular_annihilator_eq_chart_ideal_intersection A
    hA.basePointFree hA.reducedChart

end PaperVerification.Segre.CommonGraphOpen

end SegreCommonGraphOpen

section SegreFirstExcessHomology

/-!
# The first-excess Koszul defect equals the actual Lefschetz kernel

This file completes equation (4) at the level of the already verified
literal Segre polynomial and quotient spaces. The old degree-two exactness
is proved generically from the verified rank-sum baseline. No unproved
Cohen--Macaulay or regular-sequence assertion is assumed.
-/

set_option autoImplicit false

namespace PaperVerification.Segre.FirstExcessHomology

open Staircase Monomials RankParameters Degeneration KoszulDimension
open LefschetzBridge ParameterProducts ActualLefschetz
open GenericFirstLefschetz GenericSurjectivity
open scoped BigOperators Matrix

variable {I D K : Type*} [Fintype I] [DecidableEq I]
  [Fintype D] [DecidableEq D] [Field K] {n : I → ℕ}

theorem multiplierCoordinates_kernel_iff (A U : Matrix (Cell n) D K) :
    multiplierCoordinates U ∈ LinearMap.ker (multiply polynomialProduct (forms A)) ↔
      U ∈ LinearMap.ker (KoszulRank.multiplication A) := by
  change multiply polynomialProduct (forms A) (multiplierCoordinates U) = 0 ↔
    KoszulRank.multiplication A U = 0
  rw [multiply_coordinates]
  constructor
  · intro h
    apply evaluateTwo_injective
    exact h.trans (map_zero (evaluateTwo (K := K) (n := n))).symm
  · intro h
    rw [h,map_zero]

theorem map_kernel_multiplierCoordinates (A : Matrix (Cell n) D K) :
    (LinearMap.ker (KoszulRank.multiplication A)).map multiplierCoordinates.toLinearMap =
      LinearMap.ker (multiply polynomialProduct (forms A)) := by
  ext g
  constructor
  · rintro ⟨U,hU,rfl⟩
    exact (multiplierCoordinates_kernel_iff A U).mpr hU
  · intro hg
    refine ⟨multiplierCoordinates.symm g,?_,multiplierCoordinates.apply_symm_apply g⟩
    apply (multiplierCoordinates_kernel_iff A _).mp
    simpa only [LinearEquiv.apply_symm_apply] using hg

theorem finrank_kernel_polynomial_multiply (A : Matrix (Cell n) D K) :
    Module.finrank K (LinearMap.ker (multiply polynomialProduct (forms A))) =
      Module.finrank K (LinearMap.ker (KoszulRank.multiplication A)) := by
  rw [←map_kernel_multiplierCoordinates,LinearEquiv.finrank_map_eq]

theorem map_koszul_pairRelations (A : Matrix (Cell n) D K) :
    (LinearMap.range (koszulMatrix A)).map multiplierCoordinates.toLinearMap =
      pairRelations (K := K) (forms A) := by
  apply le_antisymm
  · rintro g ⟨U,⟨Q,rfl⟩,rfl⟩
    exact multiplierCoordinates_koszul_mem A Q
  · exact FixedLefschetzRanks.pairRelations_le_mapped_koszul A

theorem finrank_pairRelations (A : Matrix (Cell n) D K)
    (hA : Function.Surjective A.vecMul) :
    Module.finrank K (pairRelations (K := K) (forms A)) = (Fintype.card D).choose 2 := by
  rw [←map_koszul_pairRelations,LinearEquiv.finrank_map_eq,finrank_koszulMatrix_range A hA]

theorem degreeOneQuotientEquiv_mk (A : Matrix (Cell n) D K)
    (f : degreeOne (K := K) (n := n)) :
    GeneralQuotient.degreeOneQuotientEquiv A
        ((parameterSpan (K := K) (forms A)).mkQ f) =
      GeneralQuotient.homogeneousResidue A f := rfl

theorem quotientMultiply_kernel_iff (A : Matrix (Cell n) D K)
    (ℓ : degreeOne (K := K) (n := n))
    (x : degreeOne (K := K) (n := n) ⧸ parameterSpan (K := K) (forms A)) :
    GeneralQuotient.degreeOneQuotientEquiv A x ∈
        LinearMap.ker (GeneralQuotient.firstLefschetz A ℓ) ↔
      x ∈ LinearMap.ker (quotientMultiply polynomialProduct polynomialProduct_comm (forms A) ℓ) := by
  obtain ⟨f,rfl⟩ := (parameterSpan (K := K) (forms A)).mkQ_surjective x
  rw [degreeOneQuotientEquiv_mk]
  change GeneralQuotient.firstLefschetz A ℓ
      (GeneralQuotient.homogeneousResidue A f) = 0 ↔
    (LinearMap.range (multiply polynomialProduct (forms A))).mkQ (ℓ.val*f.val) = 0
  rw [GeneralQuotient.firstLefschetz_zero_iff,Submodule.mkQ_apply,
    Submodule.Quotient.mk_eq_zero,range_actual_multiply]

theorem map_kernel_quotientMultiply (A : Matrix (Cell n) D K)
    (ℓ : degreeOne (K := K) (n := n)) :
    (LinearMap.ker (quotientMultiply polynomialProduct polynomialProduct_comm (forms A) ℓ)).map
      (GeneralQuotient.degreeOneQuotientEquiv A).toLinearMap =
        LinearMap.ker (GeneralQuotient.firstLefschetz A ℓ) := by
  ext y
  constructor
  · rintro ⟨x,hx,rfl⟩
    exact (quotientMultiply_kernel_iff A ℓ x).mpr hx
  · intro hy
    refine ⟨(GeneralQuotient.degreeOneQuotientEquiv A).symm y,?_,
      (GeneralQuotient.degreeOneQuotientEquiv A).apply_symm_apply y⟩
    apply (quotientMultiply_kernel_iff A ℓ _).mp
    simpa only [LinearEquiv.apply_symm_apply] using hy

/-- The actual quotient-kernel identification is itself a linear equivalence. -/
def actualLefschetzKernelEquiv (A : Matrix (Cell n) D K)
    (ℓ : degreeOne (K := K) (n := n)) :
    LinearMap.ker (quotientMultiply polynomialProduct polynomialProduct_comm (forms A) ℓ) ≃ₗ[K]
      LinearMap.ker (GeneralQuotient.firstLefschetz A ℓ) :=
  (GeneralQuotient.degreeOneQuotientEquiv A).ofSubmodules _ _
    (map_kernel_quotientMultiply A ℓ)

theorem finrank_wideKernel (A : Matrix (Cell n) (Option D) K) :
    Module.finrank K (LinearMap.ker
      (wideMultiply polynomialProduct (forms (oldForms A)) (lefschetzForm A))) =
      Module.finrank K (LinearMap.ker (KoszulRank.multiplication A)) := by
  have h := (kernelSplitOption polynomialProduct (forms (oldForms A)) (lefschetzForm A)).finrank_eq
  rw [←enlarged_forms A] at h
  exact h.symm.trans (finrank_kernel_polynomial_multiply A)

theorem finrank_cycleBoundaries (A : Matrix (Cell n) (Option D) K)
    (hA : Function.Surjective A.vecMul) :
    Module.finrank K
      (cycleBoundaries polynomialProduct (forms (oldForms A)) (lefschetzForm A)) =
      (Fintype.card (Option D)).choose 2 := by
  calc
    _ = Module.finrank K
        (widePairRelations (K := K) (forms (oldForms A)) (lefschetzForm A)) :=
      (Submodule.comapSubtypeEquivOfLe
        (widePairRelations_le_kernel polynomialProduct polynomialProduct_comm
          (forms (oldForms A)) (lefschetzForm A))).finrank_eq
    _ = Module.finrank K (pairRelations (K := K) (forms A)) := by
      rw [←widePairRelations_eq_pairRelations,LinearEquiv.finrank_map_eq,←enlarged_forms A]
    _ = _ := finrank_pairRelations A hA

/-- Equation (4), with the literal full matrix kernel and actual quotient
Lefschetz map. The old exactness hypothesis is subsequently discharged on a
nonempty open by the verified rank-sum baseline. -/
theorem firstLefschetz_kernel_dimension (A : Matrix (Cell n) (Option D) K)
    (hA : Function.Surjective A.vecMul)
    (hexact : LinearMap.ker (KoszulRank.multiplication (oldForms A)) =
      LinearMap.range (koszulMatrix (oldForms A))) :
    Module.finrank K (LinearMap.ker
      (GeneralQuotient.firstLefschetz (oldForms A) (lefschetzForm A))) =
      Module.finrank K (LinearMap.ker (KoszulRank.multiplication A)) -
        (Fintype.card (Option D)).choose 2 := by
  letI : Module.Finite K (degreeOne (K := K) (n := n)) :=
    Module.Finite.of_basis (degreeOneBasis (K := K) (n := n))
  have hold := actual_exactness_of_matrix_exactness (oldForms A) hexact
  have hdim := (finrank_degreeTwoHomology polynomialProduct polynomialProduct_comm
    (forms (oldForms A)) (lefschetzForm A) hold).symm
  have hquot := Submodule.finrank_quotient_add_finrank (R := K)
    (M := LinearMap.ker
      (wideMultiply polynomialProduct (forms (oldForms A)) (lefschetzForm A)))
    (cycleBoundaries polynomialProduct (forms (oldForms A)) (lefschetzForm A))
  have hsum :
      Module.finrank K (LinearMap.ker
        (quotientMultiply polynomialProduct polynomialProduct_comm
          (forms (oldForms A)) (lefschetzForm A))) +
        Module.finrank K
          (cycleBoundaries polynomialProduct (forms (oldForms A)) (lefschetzForm A)) =
      Module.finrank K (LinearMap.ker
        (wideMultiply polynomialProduct (forms (oldForms A)) (lefschetzForm A))) := by
    rw [hdim]
    exact hquot
  rw [finrank_wideKernel A,finrank_cycleBoundaries A hA] at hsum
  exact (actualLefschetzKernelEquiv (oldForms A) (lefschetzForm A)).finrank_eq.symm.trans
    (Nat.eq_sub_of_add_eq hsum)

theorem independent_certificate
    (hw : ∃ A : Matrix (Cell n) D K, Function.Surjective A.vecMul) :
    ∃ f : MvPolynomial (Cell n × D) K, f ≠ 0 ∧
      ∀ A : Matrix (Cell n) D K, MvPolynomial.eval (fun j => A j.1 j.2) f ≠ 0 →
        Function.Surjective A.vecMul := by
  obtain ⟨A₀,hA₀⟩ := hw
  have hr : Fintype.card D ≤
      ((universalCoefficients (K := K) (n := n) (D := D)).map
        (MvPolynomial.eval (fun j => A₀ j.1 j.2))).rank := by
    rw [eval_universalCoefficients]
    exact (Matrix.vecMul_surjective_iff_rank_eq_card.mp hA₀).ge
  obtain ⟨f,hf,hwf⟩ := GenericRank.minor_witness universalCoefficients
    (fun j => A₀ j.1 j.2) (Fintype.card D) hr
  refine ⟨f,hf,?_⟩
  intro A hA
  have h := hwf (fun j => A j.1 j.2) hA
  rw [eval_universalCoefficients] at h
  exact Matrix.vecMul_surjective_iff_rank_eq_card.mpr
    (le_antisymm (Matrix.rank_le_card_width A) h)

theorem independent_first_excess_family (k : ℕ) (hk : 2 ≤ k)
    (n : Fin k → ℕ) (hpos : ∀ i,1 ≤ n i) :
    ∃ A : Matrix (Cell n) (Option (Ranks n)) K, Function.Surjective A.vecMul := by
  have hs := ChainInduction.sum_add_two_le_product Finset.univ n
    (by simpa only [Finset.card_univ,Fintype.card_fin] using hk) (fun i _ => hpos i)
  have hcard : Fintype.card (Ranks n) + 1 ≤ Fintype.card (Cell n) := by
    change Fintype.card (Fin (sideSum n + 1)) + 1 ≤ Fintype.card (Cell n)
    rw [Fintype.card_fin]
    simpa [Cell,sideSum,Nat.add_assoc] using hs
  obtain ⟨p,hp⟩ := GenericRigidity.exists_affineSpan_of_card (K := K)
    (I := Ranks n) (V := Cell n) hcard
  exact ⟨augmentedPlacement p,augmented_surjective_of_affineSpan p hp⟩

/-- The complete first-excess defect classification on the full slice
coefficient space. This is the algebraic input needed by Corollary 1.2,
including the projective-line families and every factor permutation. -/
theorem first_excess_koszul_defect_certificate [Infinite K]
    (k : ℕ) (hk : 2 ≤ k) (n : Fin k → ℕ) (hpos : ∀ i,1 ≤ n i) :
    ∃ f : MvPolynomial (Cell n × Option (Ranks n)) K, f ≠ 0 ∧
      ∀ A : Matrix (Cell n) (Option (Ranks n)) K,
        MvPolynomial.eval (fun j => A j.1 j.2) f ≠ 0 →
          Function.Surjective A.vecMul ∧
          Module.finrank K (LinearMap.ker (KoszulRank.multiplication A)) -
            (Fintype.card (Option (Ranks n))).choose 2 = Principal.kernelDefect k n := by
  obtain ⟨f,hf,hwf⟩ := Principal.joint_firstLefschetz_certificate (K := K) k (by omega) n hpos
  obtain ⟨g,hg,hwg⟩ := independent_certificate
    (independent_first_excess_family (K := K) k hk n hpos)
  obtain ⟨b,hb,hwb⟩ := baseline_certificate (K := K) (n := n)
  let b' := MvPolynomial.rename (oldVariable (n := n) (D := Ranks n)) b
  have hb' : b' ≠ 0 := by
    intro h
    exact hb ((MvPolynomial.rename_eq_zero_iff_of_injective b
      (oldVariable (n := n) (D := Ranks n)).injective).mp h)
  refine ⟨f*g*b',mul_ne_zero (mul_ne_zero hf hg) hb',?_⟩
  intro A hA
  rw [map_mul,map_mul] at hA
  obtain ⟨hfg,hbA⟩ := mul_ne_zero_iff.mp hA
  obtain ⟨hfA,hgA⟩ := mul_ne_zero_iff.mp hfg
  have hcol := hwg A hgA
  have hbase := hwb (oldForms A) (by
    simpa only [b',MvPolynomial.eval_rename,Function.comp_def,oldVariable,
      Function.Embedding.coeFn_mk,oldForms] using hbA)
  have hexact := KoszulRank.kernel_eq_koszul_range_of_rank_bound (oldForms A)
    (oldForms_surjective A hcol) hbase
  obtain ⟨_,_,_,hdefect⟩ := hwf A hfA
  refine ⟨hcol,?_⟩
  exact (firstLefschetz_kernel_dimension A hcol hexact).symm.trans hdefect

end PaperVerification.Segre.FirstExcessHomology

end SegreFirstExcessHomology

section SegrePrincipalCommonOpen

/-!
# Simultaneous full-coefficient opens for the principal geometric applications

These certificates combine the complete algebraic conclusions with literal
basepoint-freeness, finite and reduced graph-chart rings, and independent
small critical equations. Every statement includes a nonzero evaluation of
the final product polynomial. The only remaining global geometric step is
the identification of the chart ideal intersection with the critical image;
that statement is not assumed or claimed by the certificates in this file.

-/

set_option autoImplicit false

namespace PaperVerification.Segre.PrincipalCommonOpen

open Staircase Monomials RankParameters Degeneration GenericRigidity
open CommonGraphOpen KoszulDimension

variable {K : Type} [Field K] [Infinite K]

/-- The complete first-excess classification holds on one common nonempty
open with all actual geometric prerequisites, including the projective-line
families omitted from the main exception table. -/
theorem first_excess_common_data (k : ℕ) (hk : 2 ≤ k)
    (n : Fin k → ℕ) (hpos : ∀ i, 1 ≤ n i) :
    ∃ r : MvPolynomial (Cell n × Option (Ranks n)) K, r ≠ 0 ∧
      (∃ A : Matrix (Cell n) (Option (Ranks n)) K,
        MvPolynomial.eval (fun q => A q.1 q.2) r ≠ 0) ∧
      ∀ A : Matrix (Cell n) (Option (Ranks n)) K,
        MvPolynomial.eval (fun q => A q.1 q.2) r ≠ 0 →
          RegularData A ∧ Function.Surjective A.vecMul ∧
            Module.finrank K (LinearMap.ker (KoszulRank.multiplication A)) -
              (sideSum n + 2).choose 2 = Principal.kernelDefect k n := by
  have hlen : sideSum n + 1 ≤ Fintype.card (Option (Ranks n)) := by
    simp only [Fintype.card_option, Ranks, Fintype.card_fin]
    omega
  have h := combine_certificate hlen _
    (FirstExcessHomology.first_excess_koszul_defect_certificate (K := K) k hk n hpos)
  simpa only [Fintype.card_option, Ranks, Fintype.card_fin, Nat.add_assoc] using h

section GeneralExcess

variable {I D : Type} [Fintype I] [DecidableEq I]
  [Fintype D] [DecidableEq D] {n : I → ℕ}

/-- Actual full slice independence, the exact multiplication rank, and the
entire ordinary alternating Koszul kernel, together with the geometric data. -/
def ExactData (A : Matrix (Cell n) (Option D) K) : Prop :=
  RegularData A ∧ Function.Surjective A.vecMul ∧
    (multiplicationMatrix 1 A).rank =
      Fintype.card (Cell n) * Fintype.card (Option D) -
        (Fintype.card (Option D)).choose 2 ∧
    LinearMap.ker (KoszulRank.multiplication A) = LinearMap.range (koszulMatrix A)

/-- Any proved chain rigidity statement has a complete, nonempty common
coefficient open for its algebraic and geometric applications. -/
theorem exact_common_certificate
    (hlen : sideSum n ≤ Fintype.card D)
    (hG : GenericallyRigid K D (chainGraph n)) :
    ∃ r : MvPolynomial (Cell n × Option D) K, r ≠ 0 ∧
      (∃ A : Matrix (Cell n) (Option D) K,
        MvPolynomial.eval (fun q => A q.1 q.2) r ≠ 0) ∧
      ∀ A : Matrix (Cell n) (Option D) K,
        MvPolynomial.eval (fun q => A q.1 q.2) r ≠ 0 → ExactData A := by
  have hlen' : sideSum n + 1 ≤ Fintype.card (Option D) := by
    rw [Fintype.card_option]
    omega
  exact combine_certificate hlen' _
    (HigherExcessRank.exactness_certificate_of_rigid hG)

end GeneralExcess

/-- The full range k ≥ 4e in Theorem 6.1, at a single common tensor open. -/
theorem section_6_1_first_common_data (k e : ℕ) (he : 1 ≤ e) (hk : 4 * e ≤ k)
    (n : Fin k → ℕ) (hpos : ∀ i, 1 ≤ n i) :
    ∃ r : MvPolynomial (Cell n × Option (Fin (sideSum n + e))) K, r ≠ 0 ∧
      (∃ A : Matrix (Cell n) (Option (Fin (sideSum n + e))) K,
        MvPolynomial.eval (fun q => A q.1 q.2) r ≠ 0) ∧
      ∀ A : Matrix (Cell n) (Option (Fin (sideSum n + e))) K,
        MvPolynomial.eval (fun q => A q.1 q.2) r ≠ 0 → ExactData A :=
  exact_common_certificate (by simp only [Fintype.card_fin]; omega)
    (ExcessSixOne.section_6_1_first_graph_rigidity (K := K) k e he hk n hpos)

/-- The complete three-block range in Theorem 6.1, with the paper's exact
natural subtraction convention in e ≤ 2ᵇ − 3b + 1. -/
theorem section_6_1_second_common_data (b e k : ℕ) (hb : 4 ≤ b) (he : 1 ≤ e)
    (hbound : e ≤ 2 ^ b - 3 * b + 1) (hk : 3 * b ≤ k)
    (n : Fin k → ℕ) (hpos : ∀ i, 1 ≤ n i) :
    ∃ r : MvPolynomial (Cell n × Option (Fin (sideSum n + e))) K, r ≠ 0 ∧
      (∃ A : Matrix (Cell n) (Option (Fin (sideSum n + e))) K,
        MvPolynomial.eval (fun q => A q.1 q.2) r ≠ 0) ∧
      ∀ A : Matrix (Cell n) (Option (Fin (sideSum n + e))) K,
        MvPolynomial.eval (fun q => A q.1 q.2) r ≠ 0 → ExactData A :=
  exact_common_certificate (by simp only [Fintype.card_fin]; omega)
    (ExcessLogarithmic.section_6_1_second_paper_bound (K := K) b e k hb he hbound hk n hpos)

/-- The exact real-logarithmic bound printed in the paper. -/
theorem section_6_1_logarithmic_common_data (k e : ℕ) (he : 3 ≤ e)
    (hk : 3 * ⌈Real.logb 2 (4 * (e : ℝ))⌉ ≤ (k : ℤ))
    (n : Fin k → ℕ) (hpos : ∀ i, 1 ≤ n i) :
    ∃ r : MvPolynomial (Cell n × Option (Fin (sideSum n + e))) K, r ≠ 0 ∧
      (∃ A : Matrix (Cell n) (Option (Fin (sideSum n + e))) K,
        MvPolynomial.eval (fun q => A q.1 q.2) r ≠ 0) ∧
      ∀ A : Matrix (Cell n) (Option (Fin (sideSum n + e))) K,
        MvPolynomial.eval (fun q => A q.1 q.2) r ≠ 0 → ExactData A :=
  exact_common_certificate (by simp only [Fintype.card_fin]; omega)
    (ExcessLogarithmic.section_6_1_integer_ceil_graph_rigidity (K := K) k e he hk n hpos)

/-- The complete numerical criterion and every larger tuple in Theorem 6.3. -/
theorem section_6_3_common_data (k e L : ℕ) (hk : 3 ≤ k) (he : 2 ≤ e)
    (hL : DiagonalCore.minimumSide k ≤ L)
    (hbound : k * ExcessSixThree.threshold k e L + e ≤
      (L + 1) ^ (k / 2) + (L + 1) ^ ((k + 1) / 2))
    (n : Fin k → ℕ) (hn : ∀ i, ExcessSixThree.threshold k e L ≤ n i) :
    ∃ r : MvPolynomial (Cell n × Option (Fin (sideSum n + e))) K, r ≠ 0 ∧
      (∃ A : Matrix (Cell n) (Option (Fin (sideSum n + e))) K,
        MvPolynomial.eval (fun q => A q.1 q.2) r ≠ 0) ∧
      ∀ A : Matrix (Cell n) (Option (Fin (sideSum n + e))) K,
        MvPolynomial.eval (fun q => A q.1 q.2) r ≠ 0 → ExactData A :=
  exact_common_certificate (by simp only [Fintype.card_fin]; omega)
    (ExcessSixThree.section_6_3_graph_rigidity (K := K) k e L hk he hL hbound n hn)

/-- The unrestricted uniform threshold nᵢ ≥ 3e². -/
theorem uniform_large_common_data (k e : ℕ) (hk : 3 ≤ k) (he : 2 ≤ e)
    (n : Fin k → ℕ) (hn : ∀ i, 3 * e ^ 2 ≤ n i) :
    ∃ r : MvPolynomial (Cell n × Option (Fin (sideSum n + e))) K, r ≠ 0 ∧
      (∃ A : Matrix (Cell n) (Option (Fin (sideSum n + e))) K,
        MvPolynomial.eval (fun q => A q.1 q.2) r ≠ 0) ∧
      ∀ A : Matrix (Cell n) (Option (Fin (sideSum n + e))) K,
        MvPolynomial.eval (fun q => A q.1 q.2) r ≠ 0 → ExactData A :=
  exact_common_certificate (by simp only [Fintype.card_fin]; omega)
    (ExcessArithmetic.uniform_large_factors_rigid (K := K) k e hk he n hn)

/-- The improved nᵢ ≥ 6 threshold for excess two, with no bound on k. -/
theorem excess_two_common_data (k : ℕ) (hk : 3 ≤ k)
    (n : Fin k → ℕ) (hn : ∀ i, 6 ≤ n i) :
    ∃ r : MvPolynomial (Cell n × Option (Fin (sideSum n + 2))) K, r ≠ 0 ∧
      (∃ A : Matrix (Cell n) (Option (Fin (sideSum n + 2))) K,
        MvPolynomial.eval (fun q => A q.1 q.2) r ≠ 0) ∧
      ∀ A : Matrix (Cell n) (Option (Fin (sideSum n + 2))) K,
        MvPolynomial.eval (fun q => A q.1 q.2) r ≠ 0 → ExactData A :=
  exact_common_certificate (by simp only [Fintype.card_fin]; omega)
    (ExcessArithmetic.excess_two_six_rigid (K := K) k hk n hn)

end PaperVerification.Segre.PrincipalCommonOpen

end SegrePrincipalCommonOpen

section SegreMultiplicationSpanBridge

/-!
# The actual graph-span multiplication map and the verified algebra matrices

The source and target identifications are proved for the literal polynomial
map, not imposed as its definition. The actual last-factor critical relations
are identified with the ordinary alternating Koszul image, including in
characteristic two. Thus the algebraic rank and exactness theorems apply to
the geometrically defined tensor spaces.
-/

set_option autoImplicit false

namespace PaperVerification.Segre.MultiplicationSpanBridge

open Staircase Monomials Degeneration Trace GraphSpan CriticalGraph SingularSpan
open SpanDefect ParameterProducts KoszulDimension
open scoped BigOperators Matrix

variable {I J K : Type*} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Field K] {n : I → ℕ}

theorem actualMultiplication_value (A : Matrix (Cell n) J K) (c : J × Cell n → K) :
    (actualMultiplication A c).val = evaluatedMultiplication A c := by
  rw [evaluatedMultiplication_eq]
  rfl

/-- Equality of kernels follows from the injective actual monomial evaluation. -/
theorem kernel_actualMultiplication (A : Matrix (Cell n) J K) :
    LinearMap.ker (actualMultiplication A) =
      LinearMap.ker (multiplicationMatrix 1 A).mulVecLin := by
  ext c
  constructor
  · intro hc
    have hp : evaluatedMultiplication A c = 0 := by
      rw [←actualMultiplication_value]
      exact congrArg Subtype.val hc
    change c ∈ LinearMap.ker (evaluatedMultiplication A) at hp
    rwa [kernel_evaluatedMultiplication] at hp
  · intro hc
    apply Subtype.ext
    rw [actualMultiplication_value]
    have hp : c ∈ LinearMap.ker (evaluatedMultiplication A) := by
      rw [kernel_evaluatedMultiplication]
      exact hc
    exact hp

theorem finrank_range_actualMultiplication (A : Matrix (Cell n) J K) :
    Module.finrank K (LinearMap.range (actualMultiplication A)) =
      (multiplicationMatrix 1 A).rank := by
  have h₁ := (actualMultiplication A).finrank_range_add_finrank_ker
  have h₂ := (multiplicationMatrix 1 A).mulVecLin.finrank_range_add_finrank_ker
  rw [kernel_actualMultiplication] at h₁
  change Module.finrank K (LinearMap.range (actualMultiplication A)) =
    Module.finrank K (LinearMap.range (multiplicationMatrix 1 A).mulVecLin)
  exact Nat.add_right_cancel (h₁.trans h₂.symm)

/-- The coefficient matrix and the actual tensor covector contain exactly
the same coefficients, with the product indexing explicitly transposed. -/
def coefficientTensorEquiv :
    Matrix (Cell n) J K ≃ₗ[K] Module.Dual K (Matrix (Cell n) J K) :=
  KoszulRank.flatten.trans coefficientDualEquiv

theorem coefficientTensorEquiv_kernel_iff (A U : Matrix (Cell n) J K) :
    coefficientTensorEquiv U ∈ LinearMap.ker (multiplicationOnCovectors A) ↔
      U ∈ LinearMap.ker (KoszulRank.multiplication A) := by
  change actualMultiplication A (coefficientDualEquiv.symm
    (coefficientDualEquiv (KoszulRank.flatten U))) = 0 ↔
      (multiplicationMatrix 1 A).mulVecLin (KoszulRank.flatten U) = 0
  rw [LinearEquiv.symm_apply_apply]
  change KoszulRank.flatten U ∈ LinearMap.ker (actualMultiplication A) ↔
    KoszulRank.flatten U ∈ LinearMap.ker (multiplicationMatrix 1 A).mulVecLin
  rw [kernel_actualMultiplication]

theorem map_kernel_multiplication (A : Matrix (Cell n) J K) :
    (LinearMap.ker (KoszulRank.multiplication A)).map coefficientTensorEquiv.toLinearMap =
      LinearMap.ker (multiplicationOnCovectors A) := by
  ext φ
  constructor
  · rintro ⟨U,hU,rfl⟩
    exact (coefficientTensorEquiv_kernel_iff A U).mpr hU
  · intro hφ
    refine ⟨coefficientTensorEquiv.symm φ,?_,coefficientTensorEquiv.apply_symm_apply φ⟩
    apply (coefficientTensorEquiv_kernel_iff A _).mp
    simpa only [LinearEquiv.apply_symm_apply] using hφ

theorem finrank_kernel_multiplicationOnCovectors (A : Matrix (Cell n) J K) :
    Module.finrank K (LinearMap.ker (multiplicationOnCovectors A)) =
      Module.finrank K (LinearMap.ker (KoszulRank.multiplication A)) := by
  rw [←map_kernel_multiplication]
  exact LinearEquiv.finrank_map_eq _ _

/-- One ordered last-factor equation is exactly one ordinary Koszul pair,
with its original sign and original tensor coefficients. -/
theorem coefficientTensorEquiv_pair (A : Matrix (Cell n) J K) (i j : J) :
    coefficientTensorEquiv (koszulMatrix A (pairAlternating i j)) =
      (lastCriticalOperator A).dualMap (LinearMap.proj (i,j)) := by
  classical
  apply LinearMap.ext
  intro B
  change (∑ kv : J × Cell n, B kv.2 kv.1 *
      koszulMatrix A (pairAlternating i j) kv.2 kv.1) =
    ∑ u : Cell n, (A u i * B u j - A u j * B u i)
  rw [Fintype.sum_prod_type,Finset.sum_comm]
  simp only [koszulMatrix_pair_apply,mul_sub,mul_ite,mul_zero,
    Finset.sum_sub_distrib,Finset.sum_ite_eq,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  simp only [mul_comm]

theorem map_koszul_range (A : Matrix (Cell n) J K) :
    (LinearMap.range (koszulMatrix A)).map coefficientTensorEquiv.toLinearMap =
      lastRelations A := by
  classical
  apply le_antisymm
  · rintro φ ⟨U,⟨Q,rfl⟩,rfl⟩
    let decJ : DecidableEq J := inferInstance
    let orderJ : LinearOrder J := LinearOrder.lift' (Fintype.equivFin J)
      (Fintype.equivFin J).injective
    letI : LinearOrder J := { orderJ with
      toDecidableEq := decJ
      compare := fun a b => @compareOfLessAndEq J a b orderJ.toLT
        (orderJ.toDecidableLT a b) decJ
      compare_eq_compareOfLessAndEq := fun _ _ => rfl }
    obtain ⟨c,hQ⟩ := exists_sum_pairAlternating Q
    rw [hQ,map_sum,map_sum]
    apply Submodule.sum_mem
    intro q _
    rw [map_smul,map_smul]
    change c q • coefficientTensorEquiv
      (koszulMatrix A (pairAlternating q.val.1 q.val.2)) ∈ lastRelations A
    rw [coefficientTensorEquiv_pair]
    exact Submodule.smul_mem _ _ ⟨LinearMap.proj (q.val.1,q.val.2),rfl⟩
  · rintro φ ⟨ψ,rfl⟩
    have hψ : ψ = ∑ q : J × J, ψ (Pi.single q (1 : K)) • LinearMap.proj q := by
      apply LinearMap.ext
      intro z
      have hz : z = ∑ q, z q • Pi.single q (1 : K) := by
        funext q
        simp [Pi.single_apply]
      rw [LinearMap.sum_apply]
      simp only [LinearMap.smul_apply,LinearMap.proj_apply,smul_eq_mul]
      conv_lhs => rw [hz]
      simp only [map_sum,map_smul,smul_eq_mul]
      exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
    rw [hψ,map_sum]
    apply Submodule.sum_mem
    intro q _
    rw [map_smul,←coefficientTensorEquiv_pair]
    apply Submodule.smul_mem
    exact ⟨koszulMatrix A (pairAlternating q.1 q.2),
      ⟨pairAlternating q.1 q.2,rfl⟩,rfl⟩

theorem finrank_lastRelations (A : Matrix (Cell n) J K)
    (hA : Function.Surjective A.vecMul) :
    Module.finrank K (lastRelations A) = (Fintype.card J).choose 2 := by
  rw [←map_koszul_range,LinearEquiv.finrank_map_eq,finrank_koszulMatrix_range A hA]

theorem kernel_eq_lastRelations_of_exactness (A : Matrix (Cell n) J K)
    (hexact : LinearMap.ker (KoszulRank.multiplication A) =
      LinearMap.range (koszulMatrix A)) :
    LinearMap.ker (multiplicationOnCovectors A) = lastRelations A := by
  rw [←map_kernel_multiplication,hexact,map_koszul_range]

/-- Once the genuine geometric annihilator identity has been proved, the
complete algebraic exactness conclusion gives equality with the actual full
critical space, without any extra independence assumption. -/
theorem singularSpan_eq_fullCriticalSpace_of_exactness
    (A : Matrix (Cell n) J K)
    (hgeometry : (singularSpan A).dualAnnihilator =
      LinearMap.ker (multiplicationOnCovectors A) ⊔ smallRelations A)
    (hexact : LinearMap.ker (KoszulRank.multiplication A) =
      LinearMap.range (koszulMatrix A)) :
    singularSpan A = fullCriticalSpace A := by
  calc
    singularSpan A = ((singularSpan A).dualAnnihilator).dualCoannihilator :=
      (Subspace.dualAnnihilator_dualCoannihilator_eq (W := singularSpan A)).symm
    _ = (smallRelations A ⊔ lastRelations A).dualCoannihilator := by
      rw [hgeometry,kernel_eq_lastRelations_of_exactness A hexact,sup_comm]
    _ = fullCriticalSpace A := by
      rw [←fullCriticalSpace_annihilator,Subspace.dualAnnihilator_dualCoannihilator_eq]

/-- The actual geometric defect equals the degree-two Koszul homology
dimension computed by the verified algebraic multiplication matrices. -/
theorem critical_span_defect_matrix [Infinite K] (A : Matrix (Cell n) J K)
    (hA : Function.Surjective A.vecMul)
    (hgeometry : (singularSpan A).dualAnnihilator =
      LinearMap.ker (multiplicationOnCovectors A) ⊔ smallRelations A)
    (hind : Disjoint (LinearMap.ker (multiplicationOnCovectors A)) (smallRelations A)) :
    Module.finrank K (fullCriticalSpace A) - Module.finrank K (singularSpan A) =
      Module.finrank K (LinearMap.ker (KoszulRank.multiplication A)) -
        (Fintype.card J).choose 2 := by
  rw [critical_span_defect_of_annihilator A hgeometry hind,
    finrank_kernel_multiplicationOnCovectors,finrank_lastRelations A hA]

theorem critical_span_defect_rank [Infinite K] (A : Matrix (Cell n) J K)
    (hA : Function.Surjective A.vecMul)
    (hgeometry : (singularSpan A).dualAnnihilator =
      LinearMap.ker (multiplicationOnCovectors A) ⊔ smallRelations A)
    (hind : Disjoint (LinearMap.ker (multiplicationOnCovectors A)) (smallRelations A)) :
    Module.finrank K (fullCriticalSpace A) - Module.finrank K (singularSpan A) =
      Fintype.card (Cell n) * Fintype.card J - (multiplicationMatrix 1 A).rank -
        (Fintype.card J).choose 2 := by
  rw [critical_span_defect_matrix A hA hgeometry hind]
  have h := (KoszulRank.multiplication A).finrank_range_add_finrank_ker
  rw [←KoszulRank.multiplication_matrix_rank] at h
  have hd : Module.finrank K (Matrix (Cell n) J K) =
      Fintype.card (Cell n) * Fintype.card J := by simp [Module.finrank_matrix]
  rw [hd] at h
  omega

end PaperVerification.Segre.MultiplicationSpanBridge

end SegreMultiplicationSpanBridge

section SegreGraphConclusionAssembly

/-!
# Final linear-algebra assembly from the actual chart image identity

This file states the finite-dimensional implication of the complete literal
chart-image identity. `GraphGeometry.graph_chart_image_identity` supplies
that identity from the actual Koszul/global-sections construction. The
principal wrappers in `GeometricPrincipal` combine the two steps.

The chart-image identity is an explicit hypothesis here. These conditional
assembly lemmas are not claimed as proofs of the paper's principal geometric
theorems.
-/

set_option autoImplicit false

namespace PaperVerification.Segre.GraphConclusionAssembly

open Staircase Monomials GraphSpan CriticalGraph SingularSpan ProjectiveCharts
open ProjectivePointSpan SpanDefect CommonGraphOpen MultiplicationSpanBridge
open scoped BigOperators

variable {I J K : Type} [Fintype I] [DecidableEq I]
  [Fintype J] [DecidableEq J] [Field K] [Infinite K] [IsAlgClosed K] {n : I → ℕ}

/-- The exact geometric ideal-section equality proved in `GraphGeometry`
by the Koszul/global-section construction. All maps and ideals are literal. -/
def ChartImageIdentity (A : Matrix (Cell n) J K) : Prop :=
  (⨅ p : Cell n, ((chartCriticalIdeal A p).restrictScalars K).comap
      (ProjectivePointSpan.chartRestriction A p)) =
    LinearMap.ker (multiplicationOnCovectors A) ⊔ smallRelations A

theorem annihilator_identity (A : Matrix (Cell n) J K) (hA : RegularData A)
    (hsections : ChartImageIdentity A) :
    (singularSpan A).dualAnnihilator =
      LinearMap.ker (multiplicationOnCovectors A) ⊔ smallRelations A :=
  (annihilator_eq_chart_intersection A hA).trans hsections

/-- Every conclusion of the graph-span comparison, with the actual matrix
rank and printed critical-equation count. -/
theorem graph_span_conclusions (A : Matrix (Cell n) J K) (hA : RegularData A)
    (hsections : ChartImageIdentity A) :
    singularSpan A = graphSpan A ⊓ fullCriticalSpace A ∧
    Module.finrank K (singularSpan A) =
      (Degeneration.multiplicationMatrix 1 A).rank - ∑ i, (n i + 1).choose 2 ∧
    A ∈ singularSpan A := by
  have hann := annihilator_identity A hA hsections
  refine ⟨singularSpan_eq_graph_inter_critical_of_annihilator A hann, ?_,
    tensor_mem_singularSpan_of_annihilator A hann⟩
  rw [singularSpan_dimension_of_disjoint A hann hA.independentCritical,
    finrank_range_actualMultiplication, hA.criticalDimension]

/-- The exact first-excess defect, once the genuine geometric chart image
has been established at the tensor in the common open. -/
theorem first_excess_defect {k : ℕ} (n : Fin k → ℕ)
    (A : Matrix (Cell n) (Option (RankParameters.Ranks n)) K)
    (hA : RegularData A) (hcols : Function.Surjective A.vecMul)
    (hdefect : Module.finrank K (LinearMap.ker (KoszulRank.multiplication A)) -
      (sideSum n + 2).choose 2 = Principal.kernelDefect k n)
    (hsections : ChartImageIdentity A) :
    Module.finrank K (fullCriticalSpace A) - Module.finrank K (singularSpan A) =
      Principal.kernelDefect k n := by
  rw [critical_span_defect_matrix A hcols
    (annihilator_identity A hA hsections) hA.independentCritical]
  simpa only [Fintype.card_option, RankParameters.Ranks, Fintype.card_fin,
    Nat.add_assoc] using hdefect

/-- All higher-excess certificates conclude equality with the entire
critical space, once the same literal geometric identity is supplied. -/
theorem full_span {D : Type} [Fintype D] [DecidableEq D]
    (A : Matrix (Cell n) (Option D) K) (hA : PrincipalCommonOpen.ExactData A)
    (hsections : ChartImageIdentity A) :
    singularSpan A = fullCriticalSpace A :=
  singularSpan_eq_fullCriticalSpace_of_exactness A
    (annihilator_identity A hA.1 hsections) hA.2.2.2

/-- This form also covers matrices, whose enlarged slice family is dependent:
the actual kernel equality suffices and no column-independence hypothesis is used. -/
theorem full_span_of_exact_kernel (A : Matrix (Cell n) J K) (hA : RegularData A)
    (hexact : LinearMap.ker (KoszulRank.multiplication A) =
      LinearMap.range (KoszulDimension.koszulMatrix A))
    (hsections : ChartImageIdentity A) :
    singularSpan A = fullCriticalSpace A :=
  singularSpan_eq_fullCriticalSpace_of_exactness A
    (annihilator_identity A hA hsections) hexact

end PaperVerification.Segre.GraphConclusionAssembly

end SegreGraphConclusionAssembly

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
