module
public import SegreVerified.Stage031.ProjectiveSpan
public import SegreVerified.Stage031.ProjectiveReduction
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
  out.putStrLn "SEGRE_STAGE Stage031.ProjectiveConclusions"
  out.flush

/-!
# The original embedded scheme and the principal projective span theorems

The named sections preserve the original proof stages and local scopes.
-/


section SegreProjectiveSpan

/-!
# The printed projective span and its actual linear cone

The projective span here is Mathlib's independently defined span of projective
points. It is proved equal to the projectivization of the ordinary linear
span, using the existing order equivalence between actual projective subspaces
and linear subspaces. No projective codimension is defined to equal a desired
linear defect. The numerical comparison subtracts one from the dimensions of
the two actual nonzero cones, after nonzeroness is obtained on a refined
nonempty coefficient open.

-/

set_option autoImplicit false
open scoped Classical LinearAlgebra.Projectivization

namespace PaperVerification.Segre.ProjectiveSpan


section FirstExcess

open Staircase RankParameters FullGraphChartReindex
open ActualTensorSpan ActualTensorCriticalSpace

variable {K : Type} [Field K] [Infinite K] [IsAlgClosed K]

/-- Corollary 1.2 with a genuinely nonempty projective singular span. The
coefficient certificate is refined by one coordinate variable, so tensor
nonzeroness is a conclusion of the same generic open and is not an extra
assumption. The dimension expression uses the actual cones of Mathlib's
projective spans, with their projective dimensions one less than cone rank. -/
theorem corollary_1_2_projective (k : ℕ) (hk : 2 ≤ k)
    (n : Fin k → ℕ) (hpos : ∀ i, 1 ≤ n i) :
    ∃ p : MvPolynomial (Cell n × Option (Ranks n)) K, p ≠ 0 ∧
      (∃ T : Tensor K (FullFactor n (Option (Ranks n))),
        MvPolynomial.eval (fun q => slicedCoefficients K n T q.1 q.2) p ≠ 0) ∧
      ∀ T : Tensor K (FullFactor n (Option (Ranks n))),
        MvPolynomial.eval (fun q => slicedCoefficients K n T q.1 q.2) p ≠ 0 →
          ∃ hT : T ≠ 0,
            Projectivization.mk K T hT ∈
              Projectivization.Subspace.span
                (singularPoints K (FullFactor n (Option (Ranks n))) T) ∧
            (Module.finrank K
                (criticalSpace K (FullFactor n (Option (Ranks n))) T).projectivization.submodule - 1) -
              (Module.finrank K
                (Projectivization.Subspace.span
                  (singularPoints K (FullFactor n (Option (Ranks n))) T)).submodule - 1) =
              Principal.kernelDefect k n := by
  obtain ⟨p, hp, _, hw⟩ := GeometricPrincipal.corollary_1_2 (K := K) k hk n hpos
  let a : Cell n × Option (Ranks n) := ((fun _ => 0), none)
  let q : MvPolynomial (Cell n × Option (Ranks n)) K := p * MvPolynomial.X a
  have hq : q ≠ 0 := mul_ne_zero hp (MvPolynomial.X_ne_zero a)
  refine ⟨q, hq, ?_, ?_⟩
  · obtain ⟨A, hA⟩ := CommonGraphOpen.nonempty_coefficient_open q hq
    refine ⟨(slicedCoefficients K n).symm A, ?_⟩
    simpa only [LinearEquiv.apply_symm_apply] using hA
  · intro T hTq
    let A := slicedCoefficients K n T
    have hboth : MvPolynomial.eval (fun z => A z.1 z.2) p ≠ 0 ∧
        A a.1 a.2 ≠ 0 := by
      simpa only [q, map_mul, MvPolynomial.eval_X, mul_ne_zero_iff] using hTq
    have hT : T ≠ 0 := by
      intro hz
      apply hboth.2
      simp only [A, hz, map_zero]
      rfl
    have hmain := hw A hboth.1
    have hmem : T ∈ ActualTensorSpan.singularSpan K (FullFactor n (Option (Ranks n))) T := by
      have hm := hmain.2.2
      change slicedCoefficients K n T ∈
        SingularSpan.singularSpan (slicedCoefficients K n T) at hm
      rw [singularSpan_eq_map_actual] at hm
      obtain ⟨B, hB, hBT⟩ := hm
      exact (slicedCoefficients K n).injective hBT ▸ hB
    have hd := (defect_slicedCoefficients K n T).symm.trans hmain.1
    obtain ⟨hpoint, hdim⟩ := projective_defect_of_tensor_membership K
      (FullFactor n (Option (Ranks n))) T hT hmem
    exact ⟨hT, hpoint, hdim.trans hd⟩

end FirstExcess
end PaperVerification.Segre.ProjectiveSpan

end SegreProjectiveSpan

section SegreOriginalProjectivePrincipal

/-!
# Original tensor and projective statements in every factor order

The generic conclusions in this file use the genuine pi tensor product,
the original contraction-defined critical space, and Mathlib's projective
span. A factor permutation may move the distinguished factor. It only
reorders the original coordinate factors; no invariance under an arbitrary
change of basis of the fixed bilinear forms is asserted.

The common transfer below keeps both the linear defect and tensor membership.
It refines the original nonzero coefficient certificate by one coordinate
variable, proving that the resulting open is nonempty and consists of
nonzero tensors. Thus the projective dimension comparison has no additional
nonzeroness hypothesis. Zero defect gives equality of the actual linear and
projective subspaces, not just a numerical equality.

-/

set_option autoImplicit false
open scoped Classical LinearAlgebra.Projectivization

namespace PaperVerification.Segre.OriginalProjectivePrincipal

open Staircase RankParameters FullGraphChartReindex ActualTensorSpan

section ActualConclusions

variable (K : Type) [Field K] {I : Type} [Fintype I] [DecidableEq I]
  (σ : I → Type) [∀ i, Fintype (σ i)]

/-- A nonempty principal open in the complete original coefficient space
on which the actual tensor and projective statements hold. The two dimension
expressions are written explicitly; projective codimension is not defined
to be a previously computed defect. -/
def GenericProjectiveDefect (d : ℕ) : Prop :=
  ∃ p : MvPolynomial (∀ i, σ i) K, p ≠ 0 ∧
    (∃ T : Tensor K σ, MvPolynomial.eval (coefficients K σ T) p ≠ 0) ∧
    ∀ T : Tensor K σ, MvPolynomial.eval (coefficients K σ T) p ≠ 0 →
      ∃ hT : T ≠ 0,
        T ∈ ActualTensorSpan.singularSpan K σ T ∧
        Projectivization.mk K T hT ∈
          Projectivization.Subspace.span (ProjectiveSpan.singularPoints K σ T) ∧
        Module.finrank K (ActualTensorCriticalSpace.criticalSpace K σ T) -
          Module.finrank K (ActualTensorSpan.singularSpan K σ T) = d ∧
        (Module.finrank K
            (ActualTensorCriticalSpace.criticalSpace K σ T).projectivization.submodule - 1) -
          (Module.finrank K
            (Projectivization.Subspace.span (ProjectiveSpan.singularPoints K σ T)).submodule - 1) = d ∧
        (Projectivization.Subspace.span (ProjectiveSpan.singularPoints K σ T) =
            (ActualTensorCriticalSpace.criticalSpace K σ T).projectivization ↔ d = 0)

/-- A full-span conclusion states equality of the independently defined
linear and projective subspaces and membership of the nonzero original
tensor. Its coefficient open is explicitly nonempty. -/
def GenericProjectiveFullSpan : Prop :=
  ∃ p : MvPolynomial (∀ i, σ i) K, p ≠ 0 ∧
    (∃ T : Tensor K σ, MvPolynomial.eval (coefficients K σ T) p ≠ 0) ∧
    ∀ T : Tensor K σ, MvPolynomial.eval (coefficients K σ T) p ≠ 0 →
      ∃ hT : T ≠ 0,
        T ∈ ActualTensorSpan.singularSpan K σ T ∧
        ActualTensorSpan.singularSpan K σ T =
          ActualTensorCriticalSpace.criticalSpace K σ T ∧
        Projectivization.mk K T hT ∈
          Projectivization.Subspace.span (ProjectiveSpan.singularPoints K σ T) ∧
        Projectivization.Subspace.span (ProjectiveSpan.singularPoints K σ T) =
          (ActualTensorCriticalSpace.criticalSpace K σ T).projectivization

/-- The zero-defect criterion already proves equality of both actual
spaces; this extraction introduces no new geometric hypothesis. -/
theorem fullSpan_of_defect_zero (h : GenericProjectiveDefect K σ 0) :
    GenericProjectiveFullSpan K σ := by
  obtain ⟨p, hp, hne, hw⟩ := h
  refine ⟨p, hp, hne, ?_⟩
  intro T hT
  obtain ⟨hneT, hmem, hpoint, _, _, hfull⟩ := hw T hT
  have hprojective := hfull.mpr rfl
  exact ⟨hneT, hmem,
    (ProjectiveSpan.projective_full_span_iff K σ T).mp hprojective,
    hpoint, hprojective⟩

end ActualConclusions

section SlicedTransfer

variable {K : Type} [Field K] {I J : Type}
  [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

/-- The genuine tensor in the new factor order, expressed as the original
matrix of slices. Every original factor is included in the permutation. -/
def permutedSlices (n : I → ℕ) (ρ : Equiv.Perm (Option I)) :
    Tensor K (fun i => FullFactor n J (ρ i)) ≃ₗ[K] Matrix (Cell n) J K :=
  ((coefficients K (fun i => FullFactor n J (ρ i))).trans
    (TensorFactorReindex.tensorEquiv ρ).symm).trans
      (TensorFactorSplitting.matrixEquiv (n := n) (J := J))

theorem originalTensor_permutedSlices (n : I → ℕ) (ρ : Equiv.Perm (Option I))
    (T : Tensor K (fun i => FullFactor n J (ρ i))) :
    originalTensor (permutedSlices n ρ T) =
      (TensorFactorReindex.tensorEquiv ρ).symm
        (coefficients K (fun i => FullFactor n J (ρ i)) T) :=
  (TensorFactorSplitting.matrixEquiv (n := n) (J := J)).symm_apply_apply _

theorem reindex_originalTensor_permutedSlices (n : I → ℕ)
    (ρ : Equiv.Perm (Option I)) (T : Tensor K (fun i => FullFactor n J (ρ i))) :
    TensorFactorReindex.tensorEquiv ρ (originalTensor (permutedSlices n ρ T)) =
      coefficients K (fun i => FullFactor n J (ρ i)) T := by
  rw [originalTensor_permutedSlices, LinearEquiv.apply_symm_apply]

/-- The defect of the matrix is exactly the defect of the original
genuine tensor after any factor permutation. -/
theorem defect_permutedSlices (n : I → ℕ) (ρ : Equiv.Perm (Option I))
    (T : Tensor K (fun i => FullFactor n J (ρ i))) :
    Module.finrank K (CriticalGraph.fullCriticalSpace (permutedSlices n ρ T)) -
        Module.finrank K (SingularSpan.singularSpan (permutedSlices n ρ T)) =
      Module.finrank K
          (ActualTensorCriticalSpace.criticalSpace K (fun i => FullFactor n J (ρ i)) T) -
        Module.finrank K
          (ActualTensorSpan.singularSpan K (fun i => FullFactor n J (ρ i)) T) := by
  have h₁ := CriticalFactorReindex.defect_originalTensor (permutedSlices n ρ T)
  have h₂ := CriticalFactorReindex.defect_reindex ρ
    (originalTensor (permutedSlices n ρ T))
  rw [reindex_originalTensor_permutedSlices] at h₂
  exact h₁.symm.trans (h₂.symm.trans
    (ActualTensorCriticalSpace.defect_coefficients K
      (fun i => FullFactor n J (ρ i)) T))

/-- Membership of the original tensor itself is transported together with
the complete singular span, including the distinguished factor. -/
theorem mem_permutedSlices (n : I → ℕ) (ρ : Equiv.Perm (Option I))
    (T : Tensor K (fun i => FullFactor n J (ρ i))) :
    permutedSlices n ρ T ∈ SingularSpan.singularSpan (permutedSlices n ρ T) ↔
      T ∈ ActualTensorSpan.singularSpan K (fun i => FullFactor n J (ρ i)) T := by
  have h₁ := TensorFactorSplitting.originalTensor_mem_span_iff (permutedSlices n ρ T)
  have h₂ := TensorFactorReindex.tensor_mem_span_reindex ρ
    (originalTensor (permutedSlices n ρ T))
  rw [reindex_originalTensor_permutedSlices] at h₂
  exact h₁.symm.trans (h₂.symm.trans
    (ActualTensorSpan.mem_singularSpan_iff K (fun i => FullFactor n J (ρ i)) T).symm)

/-- The variable bijection is the same original coefficient reshaping and
factor permutation as the actual tensor equivalence. -/
def permutedCellEquiv (n : I → ℕ) (ρ : Equiv.Perm (Option I)) :
    (∀ i, FullFactor n J (ρ i)) ≃ Cell n × J :=
  (TensorFactorReindex.cellEquiv ρ).trans (originalCellEquiv (n := n) (J := J))

def pullbackPolynomial (n : I → ℕ) (ρ : Equiv.Perm (Option I))
    (p : MvPolynomial (Cell n × J) K) : MvPolynomial (∀ i, FullFactor n J (ρ i)) K :=
  MvPolynomial.rename (permutedCellEquiv n ρ).symm p

theorem pullbackPolynomial_ne_zero (n : I → ℕ) (ρ : Equiv.Perm (Option I))
    {p : MvPolynomial (Cell n × J) K} (hp : p ≠ 0) :
    pullbackPolynomial n ρ p ≠ 0 := by
  intro h
  apply hp
  exact (MvPolynomial.rename_eq_zero_iff_of_injective p
    (permutedCellEquiv n ρ).symm.injective).mp h

theorem eval_pullbackPolynomial (n : I → ℕ) (ρ : Equiv.Perm (Option I))
    (p : MvPolynomial (Cell n × J) K)
    (T : Tensor K (fun i => FullFactor n J (ρ i))) :
    MvPolynomial.eval (coefficients K (fun i => FullFactor n J (ρ i)) T)
        (pullbackPolynomial n ρ p) =
      MvPolynomial.eval (fun q => permutedSlices n ρ T q.1 q.2) p := by
  rw [pullbackPolynomial, MvPolynomial.eval_rename]
  rfl

/-- One common nonempty open gives the literal linear defect, the literal
projective codimension, exact full-span criterion, and membership of `[T]`.
The only nonempty-factor premise is automatic in every paper format. -/
theorem generic_projective_defect_of_slices [Infinite K] [Nonempty J]
    (n : I → ℕ) (ρ : Equiv.Perm (Option I)) (d : ℕ)
    (h : ∃ p : MvPolynomial (Cell n × J) K, p ≠ 0 ∧
      ∀ A : Matrix (Cell n) J K,
        MvPolynomial.eval (fun q => A q.1 q.2) p ≠ 0 →
          (Module.finrank K (CriticalGraph.fullCriticalSpace A) -
              Module.finrank K (SingularSpan.singularSpan A) = d) ∧
            A ∈ SingularSpan.singularSpan A) :
    GenericProjectiveDefect K (fun i => FullFactor n J (ρ i)) d := by
  obtain ⟨p, hp, hw⟩ := h
  let v₀ : ∀ i : Option I, FullFactor n J i := fun i =>
    match i with
    | none => Classical.choice (inferInstance : Nonempty J)
    | some _ => 0
  let b : ∀ i : Option I, FullFactor n J (ρ i) := fun i => v₀ (ρ i)
  let q := pullbackPolynomial n ρ p * MvPolynomial.X b
  have hq : q ≠ 0 := mul_ne_zero (pullbackPolynomial_ne_zero n ρ hp)
    (MvPolynomial.X_ne_zero b)
  refine ⟨q, hq, ?_, ?_⟩
  · obtain ⟨c, hc⟩ := PermutedCorollary.nonempty_open q hq
    refine ⟨(coefficients K (fun i => FullFactor n J (ρ i))).symm c, ?_⟩
    simpa only [LinearEquiv.apply_symm_apply] using hc
  · intro T hTq
    have hboth :
        MvPolynomial.eval (coefficients K (fun i => FullFactor n J (ρ i)) T)
            (pullbackPolynomial n ρ p) ≠ 0 ∧
          coefficients K (fun i => FullFactor n J (ρ i)) T b ≠ 0 := by
      simpa only [q, map_mul, MvPolynomial.eval_X, mul_ne_zero_iff] using hTq
    have hT : T ≠ 0 := by
      intro hz
      apply hboth.2
      simp only [hz, map_zero, Pi.zero_apply]
    have hA := hw (permutedSlices n ρ T)
      (by simpa only [eval_pullbackPolynomial] using hboth.1)
    have hmem := (mem_permutedSlices n ρ T).mp hA.2
    have hdef := (defect_permutedSlices n ρ T).symm.trans hA.1
    have hprojective := ProjectiveSpan.projective_defect_of_tensor_membership K
      (fun i => FullFactor n J (ρ i)) T hT hmem
    have hfull : ActualTensorSpan.singularSpan K (fun i => FullFactor n J (ρ i)) T =
        ActualTensorCriticalSpace.criticalSpace K (fun i => FullFactor n J (ρ i)) T ↔
          d = 0 := by
      constructor
      · intro heq
        have hdim := congrArg
          (fun S : Submodule K (Tensor K (fun i => FullFactor n J (ρ i))) =>
            Module.finrank K S) heq
        omega
      · intro hd
        apply Submodule.eq_of_le_of_finrank_le
          (ActualTensorCriticalSpace.singularSpan_le_criticalSpace K
            (fun i => FullFactor n J (ρ i)) T)
        exact Nat.sub_eq_zero_iff_le.mp (hdef.trans hd)
    exact ⟨hT, hmem, hprojective.1, hdef, hprojective.2.trans hdef,
      (ProjectiveSpan.projective_full_span_iff K
        (fun i => FullFactor n J (ρ i)) T).trans hfull⟩

/-- Every full-span certificate in sliced coordinates gives full linear
and projective span in the genuine tensor space in every factor order. -/
theorem generic_projective_fullSpan_of_slices [Infinite K] [Nonempty J]
    (n : I → ℕ) (ρ : Equiv.Perm (Option I))
    (h : ∃ p : MvPolynomial (Cell n × J) K, p ≠ 0 ∧
      (∃ A : Matrix (Cell n) J K, MvPolynomial.eval (fun q => A q.1 q.2) p ≠ 0) ∧
      ∀ A : Matrix (Cell n) J K,
        MvPolynomial.eval (fun q => A q.1 q.2) p ≠ 0 →
          SingularSpan.singularSpan A = CriticalGraph.fullCriticalSpace A) :
    GenericProjectiveFullSpan K (fun i => FullFactor n J (ρ i)) := by
  apply fullSpan_of_defect_zero
  obtain ⟨p, hp, _, hw⟩ := h
  apply generic_projective_defect_of_slices n ρ 0
  refine ⟨p, hp, ?_⟩
  intro A hA
  have heq := hw A hA
  refine ⟨by rw [heq, Nat.sub_self], ?_⟩
  rw [heq]
  exact (CriticalGraph.tensor_mem_graph_inter_critical A).2

end SlicedTransfer

section PrincipalStatements

variable {K : Type} [Field K] [IsAlgClosed K]

/-- Corollary 1.2, its projective-line addendum, and every permutation of
all factors, in the original genuine tensor and projective spaces. The
independent defect-table lemmas evaluate `Principal.kernelDefect` exactly. -/
theorem corollary_1_2 (k : ℕ) (hk : 2 ≤ k) (n : Fin k → ℕ)
    (hpos : ∀ i, 1 ≤ n i) (ρ : Equiv.Perm (Option (Fin k))) :
    GenericProjectiveDefect K
      (fun i => FullFactor n (Option (Ranks n)) (ρ i)) (Principal.kernelDefect k n) := by
  obtain ⟨p, hp, _, hw⟩ := GeometricPrincipal.corollary_1_2 (K := K) k hk n hpos
  apply generic_projective_defect_of_slices n ρ (Principal.kernelDefect k n)
  exact ⟨p, hp, fun A hA => ⟨(hw A hA).1, (hw A hA).2.2⟩⟩

/-- The full unbounded projective-line family in every order, including
orders in which the originally distinguished factor is moved. If the other
small dimension is `b`, the stated defect is exactly `b`. -/
theorem projective_line_family (n : Fin 2 → ℕ) (hpos : ∀ i, 1 ≤ n i)
    (hline : n 0 = 1 ∨ n 1 = 1) (ρ : Equiv.Perm (Option (Fin 2))) :
    GenericProjectiveDefect K
      (fun i => FullFactor n (Option (Ranks n)) (ρ i)) (n 0 * n 1) := by
  rw [← GeometricDefectTable.projective_line_defect n hline]
  exact corollary_1_2 2 (by decide) n hpos ρ

/-- The matrix addendum includes every nonnegative projective dimension
and both factor orders, with no independence premise on the oversized slice
family. It asserts equality of actual linear and projective subspaces. -/
theorem matrix_first_excess (n : Fin 1 → ℕ) (ρ : Equiv.Perm (Option (Fin 1))) :
    GenericProjectiveFullSpan K (fun i => FullFactor n (Option (Ranks n)) (ρ i)) :=
  generic_projective_fullSpan_of_slices n ρ
    (GeometricPrincipal.matrix_first_excess (K := K) n)

/-- The complete first criterion of Theorem 6.1, in every factor order. -/
theorem theorem_6_1_first (k e : ℕ) (he : 1 ≤ e) (hk : 4 * e ≤ k)
    (n : Fin k → ℕ) (hpos : ∀ i, 1 ≤ n i)
    (ρ : Equiv.Perm (Option (Fin k))) :
    GenericProjectiveFullSpan K
      (fun i => FullFactor n (Option (Fin (sideSum n + e))) (ρ i)) :=
  generic_projective_fullSpan_of_slices n ρ
    (GeometricPrincipal.theorem_6_1_first (K := K) k e he hk n hpos)

/-- The complete three-block criterion of Theorem 6.1, preserving the
unbounded ranges of the excess and every smaller factor dimension. -/
theorem theorem_6_1_second (b e k : ℕ) (hb : 4 ≤ b) (he : 1 ≤ e)
    (hbound : e ≤ 2 ^ b - 3 * b + 1) (hk : 3 * b ≤ k)
    (n : Fin k → ℕ) (hpos : ∀ i, 1 ≤ n i)
    (ρ : Equiv.Perm (Option (Fin k))) :
    GenericProjectiveFullSpan K
      (fun i => FullFactor n (Option (Fin (sideSum n + e))) (ρ i)) :=
  generic_projective_fullSpan_of_slices n ρ
    (GeometricPrincipal.theorem_6_1_second (K := K) b e k hb he hbound hk n hpos)

/-- The literal logarithmic ceiling consequence, with the paper's exact
range `e ≥ 3`, and any order of all original tensor factors. -/
theorem theorem_6_1_logarithmic (k e : ℕ) (he : 3 ≤ e)
    (hk : 3 * ⌈Real.logb 2 (4 * (e : ℝ))⌉ ≤ (k : ℤ))
    (n : Fin k → ℕ) (hpos : ∀ i, 1 ≤ n i)
    (ρ : Equiv.Perm (Option (Fin k))) :
    GenericProjectiveFullSpan K
      (fun i => FullFactor n (Option (Fin (sideSum n + e))) (ρ i)) :=
  generic_projective_fullSpan_of_slices n ρ
    (GeometricPrincipal.theorem_6_1_logarithmic (K := K) k e he hk n hpos)

/-- The exact criterion of Theorem 6.3 and its entire range of larger
tuples, as equality of actual linear and projective subspaces. -/
theorem theorem_6_3 (k e L : ℕ) (hk : 3 ≤ k) (he : 2 ≤ e)
    (hL : DiagonalCore.minimumSide k ≤ L)
    (hbound : k * ExcessSixThree.threshold k e L + e ≤
      (L + 1) ^ (k / 2) + (L + 1) ^ ((k + 1) / 2))
    (n : Fin k → ℕ) (hn : ∀ i, ExcessSixThree.threshold k e L ≤ n i)
    (ρ : Equiv.Perm (Option (Fin k))) :
    GenericProjectiveFullSpan K
      (fun i => FullFactor n (Option (Fin (sideSum n + e))) (ρ i)) :=
  generic_projective_fullSpan_of_slices n ρ
    (GeometricPrincipal.theorem_6_3 (K := K) k e L hk he hL hbound n hn)

/-- The uniform sufficient bound following Theorem 6.3, with membership
of the actual nonzero tensor and its projective point on the same open. -/
theorem uniform_large_factors (k e : ℕ) (hk : 3 ≤ k) (he : 2 ≤ e)
    (n : Fin k → ℕ) (hn : ∀ i, 3 * e ^ 2 ≤ n i)
    (ρ : Equiv.Perm (Option (Fin k))) :
    GenericProjectiveFullSpan K
      (fun i => FullFactor n (Option (Fin (sideSum n + e))) (ρ i)) :=
  generic_projective_fullSpan_of_slices n ρ
    (GeometricPrincipal.uniform_large_factors (K := K) k e hk he n hn)

/-- The improved excess-two bound, for every `k ≥ 3`, every tuple of
smaller dimensions at least six, and every order of all tensor factors. -/
theorem excess_two_six (k : ℕ) (hk : 3 ≤ k) (n : Fin k → ℕ)
    (hn : ∀ i, 6 ≤ n i) (ρ : Equiv.Perm (Option (Fin k))) :
    GenericProjectiveFullSpan K
      (fun i => FullFactor n (Option (Fin (sideSum n + 2))) (ρ i)) :=
  generic_projective_fullSpan_of_slices n ρ
    (GeometricPrincipal.excess_two_six (K := K) k hk n hn)

/-- The square-root bound following Theorem 6.3, for all excesses at least
two and all larger three-factor tuples, in every order of the four tensor
factors. `AsymptoticBounds.ceil_sqrt_cast` identifies the natural ceiling
with the ordinary integer ceiling in the paper. -/
theorem three_factor_sqrt_bound (e : ℕ) (he : 2 ≤ e) (n : Fin 3 → ℕ)
    (hn : ∀ i, 2 * e + 2 * ⌈Real.sqrt (7 * (e : ℝ))⌉₊ ≤ n i)
    (ρ : Equiv.Perm (Option (Fin 3))) :
    GenericProjectiveFullSpan K
      (fun i => FullFactor n (Option (Fin (sideSum n + e))) (ρ i)) := by
  let q := ⌈Real.sqrt (7 * (e : ℝ))⌉₊
  apply theorem_6_3 3 e (q + 2) (by omega) he ?_ ?_ n ?_ ρ
  · change 2 ≤ q + 2
    omega
  · change 3 * (2 * (q + 2) + 2 * (e - 2)) + e ≤ _
    exact AsymptoticBounds.three_factor_threshold e q he
      (AsymptoticBounds.ceil_sqrt_bound e)
  · intro i
    change 2 * (q + 2) + 2 * (e - 2) ≤ n i
    rw [AsymptoticBounds.three_factor_bound_exact e q he]
    exact hn i

/-- The exact real-root bound following Theorem 6.3 for every number of
smaller factors at least four, with the full generic projective conclusion.
The root and ceiling are actual real operations, not asymptotic estimates. -/
theorem many_factor_root_bound (k e : ℕ) (hk : 4 ≤ k) (he : 2 ≤ e)
    (n : Fin k → ℕ)
    (hn : ∀ i,
      e + 2 * ⌈(((k + 1) * e : ℕ) : ℝ) ^
        (1 / (((k + 1) / 2 : ℕ) : ℝ))⌉₊ + 4 * k - 2 ≤ n i)
    (ρ : Equiv.Perm (Option (Fin k))) :
    GenericProjectiveFullSpan K
      (fun i => FullFactor n (Option (Fin (sideSum n + e))) (ρ i)) := by
  let t := ⌈(((k + 1) * e : ℕ) : ℝ) ^
    (1 / (((k + 1) / 2 : ℕ) : ℝ))⌉₊
  have hmin : DiagonalCore.minimumSide k = 1 := by
    simp only [DiagonalCore.minimumSide, if_neg (show k ≠ 3 by omega)]
  apply theorem_6_3 k e (t + 2 * k) (by omega) he ?_ ?_ n ?_ ρ
  · rw [hmin]
    omega
  · simp only [ExcessSixThree.threshold, hmin, one_mul]
    exact AsymptoticBounds.many_factor_threshold k e t hk he
      (AsymptoticBounds.ceil_root_bound ((k + 1) * e) ((k + 1) / 2) (by omega))
  · intro i
    simp only [ExcessSixThree.threshold, hmin, one_mul]
    rw [AsymptoticBounds.many_factor_bound_exact k e t he]
    exact hn i

end PrincipalStatements
end PaperVerification.Segre.OriginalProjectivePrincipal

end SegreOriginalProjectivePrincipal

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
