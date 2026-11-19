module

public import Recovery.Unimodular.KoszulSupport.PaperVerification.NoncommutativeBarFree
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.LinearAlgebra.FreeModule.Basic
public import Lean.Elab.Tactic.Omega

/-!
# Length grading and exactness of the normalized free bar construction

The length pieces are actual supported submodules of the word module. The
differential decreases length and the explicit contraction increases it.
This supplies cycle-to-boundary witnesses in every positive bar degree.
-/

@[expose] public section
noncomputable section
open scoped BigOperators

namespace PaperVerification.NoncommutativeBar

open PaperVerification.AugmentedAlgebraBasis

variable {K A I : Type*} [CommRing K] [Ring A] [Algebra K A]
  (ε : A →ₐ[K] K) (B : Module.Basis (Option I) K A)
  (hunit : B none=1) (hε : ∀ i,ε (B (some i))=0)

def lengthPiece (I A : Type*) [Ring A] (r : ℕ) :
    Submodule A (Words I A) :=
  Finsupp.supported A A {L | L.length=r}

theorem single_mem_lengthPiece (L : List I) (a : A) {r : ℕ} (hL : L.length=r) :
    Finsupp.single L a ∈ lengthPiece I A r :=
  Finsupp.single_mem_supported A a hL

theorem mem_lengthPiece_iff (z : Words I A) (r : ℕ) :
    z ∈ lengthPiece I A r ↔ ∀ L : List I,L.length≠r → z L=0 :=
  Finsupp.mem_supported' A z

theorem lengthPiece_eq_span (r : ℕ) :
    lengthPiece I A r=Submodule.span A
      ((fun L : List I ↦ Finsupp.single L (1 : A)) '' {L | L.length=r}) :=
  Finsupp.supported_eq_span_single A {L : List I | L.length=r}

instance lengthPiece_free (r : ℕ) : Module.Free A (lengthPiece I A r) :=
  Module.Free.of_basis ((Module.Basis.ofRepr (LinearEquiv.refl A _) :
      Module.Basis {L : List I | L.length=r} A ({L : List I | L.length=r} →₀ A)).map
    (Finsupp.supportedEquivFinsupp (M := A) (R := A) {L : List I | L.length=r}).symm)

theorem lift_apply (z : Words I K) (L : List I) :
    lift (A := A) z L=algebraMap K A (z L) := by
  classical
  induction z using Finsupp.induction_linear with
  | zero => simp only [map_zero,Finsupp.zero_apply]
  | add z w hz hw => simp only [map_add,Finsupp.add_apply,hz,hw]
  | single T c =>
    by_cases h : T=L <;>
      simp [lift_single,Finsupp.single_apply,h,Algebra.smul_def]

theorem lift_mem_lengthPiece {r : ℕ} (z : Words I K) (hz : z∈lengthPiece I K r) :
    lift (A := A) z ∈ lengthPiece I A r := by
  rw [mem_lengthPiece_iff] at hz ⊢
  intro L hL
  rw [lift_apply,hz L hL,map_zero]

theorem prefix_mem_lengthPiece (i : I) {r : ℕ} (z : Words I A)
    (hz : z∈lengthPiece I A r) : prepend i z∈lengthPiece I A (r+1) := by
  rw [lengthPiece_eq_span] at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨L,hL,rfl⟩ := hz
    change L.length=r at hL
    rw [prefix_single]
    exact single_mem_lengthPiece _ _ (by simpa only [List.length_cons,hL])
  | zero => simpa only [map_zero] using (lengthPiece I A (r+1)).zero_mem
  | add z w hz hw ihz ihw =>
    simpa only [map_add] using (lengthPiece I A (r+1)).add_mem ihz ihw
  | smul a z hz ih =>
    simpa only [map_smul] using (lengthPiece I A (r+1)).smul_mem a ih

theorem reduced_prefix_eq (i : I) :
    PaperVerification.ReducedBarBasis.prepend (K := K) i=prepend (A := K) i := by
  apply Finsupp.lhom_ext
  intro L c
  simp only [PaperVerification.ReducedBarBasis.prefix_single,prefix_single]

theorem appendTail_mem_lengthPiece (L : List I) (c : I →₀ K) :
    PaperVerification.ReducedBarBasis.appendTail L c∈lengthPiece I K (L.length+1) := by
  rw [PaperVerification.ReducedBarBasis.appendTail,Finsupp.linearCombination_apply,Finsupp.sum]
  apply Submodule.sum_mem
  intro i hi
  exact (lengthPiece I K (L.length+1)).smul_mem _
    (single_mem_lengthPiece _ _ rfl)

theorem reducedDifferentialBasis_mem_lengthPiece (L : List I) :
    PaperVerification.ReducedBarBasis.differentialBasis B L∈
      lengthPiece I K (L.length-1) := by
  induction L with
  | nil =>
    simp only [PaperVerification.ReducedBarBasis.differentialBasis]
    exact Submodule.zero_mem _
  | cons i L ih =>
    cases L with
    | nil =>
      simp only [PaperVerification.ReducedBarBasis.differentialBasis,
        PaperVerification.ReducedBarBasis.merge_single,
        PaperVerification.ReducedBarBasis.mergeBasis,smul_zero,map_zero,sub_zero]
      exact Submodule.zero_mem _
    | cons j L =>
      change PaperVerification.ReducedBarBasis.differentialBasis B (i::j::L)∈
        lengthPiece I K (L.length+1)
      rw [PaperVerification.ReducedBarBasis.differentialBasis]
      apply Submodule.sub_mem
      · rw [PaperVerification.ReducedBarBasis.merge_single,one_smul,
          PaperVerification.ReducedBarBasis.mergeBasis]
        exact appendTail_mem_lengthPiece L _
      · rw [reduced_prefix_eq]
        exact prefix_mem_lengthPiece i _
          (by simpa only [List.length_cons,Nat.add_sub_cancel] using ih)

theorem front_mem_lengthPiece {r : ℕ} (z : Words I A)
    (hz : z∈lengthPiece I A (r+1)) : front B z∈lengthPiece I A r := by
  rw [lengthPiece_eq_span] at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨L,hL,rfl⟩ := hz
    change L.length=r+1 at hL
    cases L with
    | nil => simp only [List.length_nil] at hL; omega
    | cons i L =>
      rw [front_single,one_smul]
      exact single_mem_lengthPiece _ _ (by simpa only [List.length_cons,Nat.add_right_cancel_iff] using hL)
  | zero => simpa only [map_zero] using (lengthPiece I A r).zero_mem
  | add z w hz hw ihz ihw =>
    simpa only [map_add] using (lengthPiece I A r).add_mem ihz ihw
  | smul a z hz ih =>
    simpa only [map_smul] using (lengthPiece I A r).smul_mem a ih

theorem internal_mem_lengthPiece {r : ℕ} (z : Words I A)
    (hz : z∈lengthPiece I A (r+1)) : internal B z∈lengthPiece I A r := by
  rw [lengthPiece_eq_span] at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨L,hL,rfl⟩ := hz
    change L.length=r+1 at hL
    rw [internal_single,one_smul]
    have h := lift_mem_lengthPiece (A := A) _ (reducedDifferentialBasis_mem_lengthPiece B L)
    simpa only [hL,Nat.add_sub_cancel] using h
  | zero => simpa only [map_zero] using (lengthPiece I A r).zero_mem
  | add z w hz hw ihz ihw =>
    simpa only [map_add] using (lengthPiece I A r).add_mem ihz ihw
  | smul a z hz ih =>
    simpa only [map_smul] using (lengthPiece I A r).smul_mem a ih

theorem differential_mem_lengthPiece {r : ℕ} (z : Words I A)
    (hz : z∈lengthPiece I A (r+1)) : differential B z∈lengthPiece I A r :=
  (lengthPiece I A r).sub_mem (front_mem_lengthPiece B z hz)
    (internal_mem_lengthPiece B z hz)

theorem homotopy_mem_lengthPiece {r : ℕ} (z : Words I A)
    (hz : z∈lengthPiece I A r) : homotopy B z∈lengthPiece I A (r+1) := by
  classical
  rw [←Finsupp.sum_single z,Finsupp.sum,map_sum]
  apply Submodule.sum_mem
  intro L hL
  have hlen : L.length=r := hz hL
  rw [homotopy_single,Finsupp.linearCombination_apply,Finsupp.sum]
  apply Submodule.sum_mem
  intro i hi
  exact (lengthPiece I A (r+1)).smul_of_tower_mem _
    (single_mem_lengthPiece _ _ (by simp only [List.length_cons,hlen]))

theorem augmentationProjection_eq_zero_of_positive {r : ℕ} (z : Words I A)
    (hz : z∈lengthPiece I A (r+1)) : augmentationProjection ε z=0 := by
  have hzero : z []=0 := (mem_lengthPiece_iff z (r+1)).mp hz [] (by simp)
  simp only [augmentationProjection,LinearMap.comp_apply,LinearMap.smulRight_apply,
    Finsupp.lapply_apply,hzero,AlgHom.toLinearMap_apply,map_zero,zero_smul]

include hunit hε in
/-- Every positive-length cycle is a boundary of the explicitly constructed
next-length element. This is exactness of the actual differential. -/
theorem positive_cycle_is_boundary {r : ℕ} (z : Words I A)
    (hz : z∈lengthPiece I A (r+1)) (hd : differential B z=0) :
    ∃ y∈lengthPiece I A (r+2),differential B y=z := by
  refine ⟨homotopy B z,homotopy_mem_lengthPiece B z hz,?_⟩
  have h := contracting_identity ε B hunit hε z
  simpa only [hd,map_zero,augmentationProjection_eq_zero_of_positive ε z hz,add_zero] using h

end PaperVerification.NoncommutativeBar
