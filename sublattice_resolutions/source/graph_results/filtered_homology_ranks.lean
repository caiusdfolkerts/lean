module
public import Lean.Elab.Command
public import graph_foundation.part001
public import graph_foundation.part013
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Lean.Elab.Tactic.Omega

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.FilteredHomologyRanks -/
section

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 20000
set_option synthInstance.maxHeartbeats 5000
set_option maxRecDepth 4096
noncomputable section
namespace FourPapers.FilteredHomology
open Classical Module
variable {K X Y : Type*} [Field K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]

/-- An actual leading kernel vector is an associated-graded kernel vector.
The map is induced from representatives; no lift of a graded cycle is assumed. -/
def kernelGradeMap (F : Filtration (K := K) X) (G : Filtration (K := K) Y)
    (f : X →ₗ[K] Y) (hf : Preserves F G f) (n : ℕ) :
    Grade (cyclesFiltration F f) n →ₗ[K] LinearMap.ker (gradeMap F G f hf n) :=
  (lowerInLevel (cyclesFiltration F f) n).liftQ
    (cycleToGradeCycle F G f hf n) (by
      intro z hz
      apply Subtype.ext
      change (Submodule.Quotient.mk (cycleToLevel F f n z) : Grade F n)=0
      exact (Submodule.Quotient.mk_eq_zero (lowerInLevel F n)).mpr hz)

theorem kernelGradeMap_injective
    (F : Filtration (K := K) X) (G : Filtration (K := K) Y)
    (f : X →ₗ[K] Y) (hf : Preserves F G f) (n : ℕ) :
    Function.Injective (kernelGradeMap F G f hf n) := by
  apply LinearMap.ker_eq_bot.mp
  apply le_antisymm _ bot_le
  intro x hx
  obtain ⟨z,rfl⟩ := (lowerInLevel (cyclesFiltration F f) n).mkQ_surjective x
  have h := congrArg Subtype.val hx
  change (Submodule.Quotient.mk (cycleToLevel F f n z) : Grade F n)=0 at h
  have hz := (Submodule.Quotient.mk_eq_zero (lowerInLevel F n)).mp h
  change (Submodule.Quotient.mk z : Grade (cyclesFiltration F f) n)=0
  exact (Submodule.Quotient.mk_eq_zero _).mpr hz

section Finite
variable [FiniteDimensional K X]

/-- Exhaustiveness is a finite bound in finite dimension. -/
theorem Filtration.exists_level_top (F : Filtration (K := K) X) :
    ∃ N, F.level N=⊤ := by
  let b := Module.finBasis K X
  choose degree hdegree using fun i => F.exhaustive (b i)
  let N := ∑ i, degree i
  refine ⟨N,le_antisymm le_top ?_⟩
  rw [← b.span_eq]
  apply Submodule.span_le.mpr
  rintro _ ⟨i,rfl⟩
  apply F.mono (show degree i≤N from Finset.single_le_sum (fun j _ => Nat.zero_le (degree j)) (Finset.mem_univ i))
  exact hdegree i

theorem sum_finrank_grade_of_top (F : Filtration (K := K) X)
    (N : ℕ) (hN : F.level N=⊤) :
    ∑ n∈Finset.range N,finrank K (Grade F n)=finrank K X := by
  rw [sum_finrank_grade F N,hN,finrank_top]

variable [FiniteDimensional K Y]

theorem kernelGrade_finrank_le
    (F : Filtration (K := K) X) (G : Filtration (K := K) Y)
    (f : X →ₗ[K] Y) (hf : Preserves F G f) (n : ℕ) :
    finrank K (Grade (cyclesFiltration F f) n)≤
      finrank K (LinearMap.ker (gradeMap F G f hf n)) := by
  rw [(LinearEquiv.ofInjective _ (kernelGradeMap_injective F G f hf n)).finrank_eq]
  exact Submodule.finrank_le _

/-- Equality of the actual kernel dimension with the total graded kernel
dimension forces every leading cycle to lift. The conclusion gives literal
representatives and the exact filtration bound. -/
theorem liftsCycles_of_kernel_finrank_eq
    (F : Filtration (K := K) X) (G : Filtration (K := K) Y)
    (f : X →ₗ[K] Y) (hf : Preserves F G f)
    (N : ℕ) (hN : F.level N=⊤)
    (heq : finrank K (LinearMap.ker f)=
      ∑ n∈Finset.range N,finrank K (LinearMap.ker (gradeMap F G f hf n))) :
    LiftsCycles F G f := by
  have hkN : (cyclesFiltration F f).level N=⊤ := by
    ext z
    simp [cyclesFiltration,cycleLevel,hN]
  have hsum := sum_finrank_grade_of_top (cyclesFiltration F f) N hkN
  rw [heq] at hsum
  intro n x hx hfx
  by_cases hn : n<N
  · have hmem : n∈Finset.range N := Finset.mem_range.mpr hn
    have ha := Finset.sum_erase_add (Finset.range N)
      (fun i => finrank K (Grade (cyclesFiltration F f) i)) hmem
    have hb := Finset.sum_erase_add (Finset.range N)
      (fun i => finrank K (LinearMap.ker (gradeMap F G f hf i))) hmem
    have hrest :
        ∑ i∈(Finset.range N).erase n,finrank K (Grade (cyclesFiltration F f) i)≤
          ∑ i∈(Finset.range N).erase n,finrank K (LinearMap.ker (gradeMap F G f hf i)) :=
      Finset.sum_le_sum (fun i _ => kernelGrade_finrank_le F G f hf i)
    have hle := kernelGrade_finrank_le F G f hf n
    have he : finrank K (Grade (cyclesFiltration F f) n)=
        finrank K (LinearMap.ker (gradeMap F G f hf n)) := by omega
    let e := LinearEquiv.ofInjectiveOfFinrankEq (kernelGradeMap F G f hf n)
      (kernelGradeMap_injective F G f hf n) he
    let q : LinearMap.ker (gradeMap F G f hf n) :=
      ⟨Submodule.Quotient.mk (⟨x,hx⟩ : F.level (n+1)),by
        change (Submodule.Quotient.mk (levelMap F G f hf (n+1) ⟨x,hx⟩) : Grade G n)=0
        exact (Submodule.Quotient.mk_eq_zero _).mpr hfx⟩
    obtain ⟨u,hu⟩ := e.surjective q
    obtain ⟨z,rfl⟩ := (lowerInLevel (cyclesFiltration F f) n).mkQ_surjective u
    refine ⟨z.val.val,z.property,z.val.property,?_⟩
    have hq := (congrArg Subtype.val hu).symm
    change (Submodule.Quotient.mk (⟨x,hx⟩ : F.level (n+1)) : Grade F n)=
      Submodule.Quotient.mk (cycleToLevel F f n z) at hq
    exact (Submodule.Quotient.eq (lowerInLevel F n)).mp hq
  · have htop : F.level n=⊤ := le_antisymm le_top (by
      rw [← hN]
      exact F.mono (Nat.le_of_not_gt hn))
    exact ⟨0,(F.level (n+1)).zero_mem,map_zero f,by simp [htop]⟩
end Finite

section SquareZero
variable [FiniteDimensional K X]

/-- For a square-zero differential the homology dimension determines its
kernel dimension. Both boundary and cycle spaces here are the actual ones. -/
theorem homology_finrank_add_finrank
    (d : Module.End K X) (hd : d.comp d=0) :
    finrank K (Homology d d hd)+finrank K X=2*finrank K (LinearMap.ker d) := by
  have hk : LinearMap.ker (boundaryMap d d hd)=LinearMap.ker d := by
    ext x
    change boundaryMap d d hd x=0 ↔ d x=0
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hr := (boundaryMap d d hd).finrank_range_add_finrank_ker
  rw [hk] at hr
  have hq := (LinearMap.range (boundaryMap d d hd)).finrank_quotient_add_finrank
  change finrank K (Homology d d hd)+finrank K (LinearMap.range (boundaryMap d d hd))=
    finrank K (LinearMap.ker d) at hq
  omega

/-- The finite filtered Betti-equality implication used in degeneration:
equality of actual total homology dimensions forces actual leading cycle
lifts. No spectral-sequence collapse or splitting is assumed. -/
theorem liftsCycles_of_homology_finrank_eq
    (F : Filtration (K := K) X) (d : Module.End K X)
    (hf : Preserves F F d) (hd : d.comp d=0)
    (N : ℕ) (hN : F.level N=⊤)
    (heq : finrank K (Homology d d hd)=
      ∑ n∈Finset.range N,finrank K
        (GradedHomology F F F d d hf hf hd n)) :
    LiftsCycles F F d := by
  apply liftsCycles_of_kernel_finrank_eq F F d hf N hN
  have hactual := homology_finrank_add_finrank d hd
  have hgrades :
      (∑ n∈Finset.range N,finrank K (GradedHomology F F F d d hf hf hd n))+
        (∑ n∈Finset.range N,finrank K (Grade F n))=
      2*(∑ n∈Finset.range N,finrank K (LinearMap.ker (gradeMap F F d hf n))) := by
    rw [← Finset.sum_add_distrib,Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro n _
    exact homology_finrank_add_finrank (gradeMap F F d hf n)
      (gradeMap_comp F F F d d hf hf hd n)
  rw [sum_finrank_grade_of_top F N hN,← heq] at hgrades
  omega
end SquareZero
end FourPapers.FilteredHomology

#print axioms FourPapers.FilteredHomology.kernelGradeMap_injective
#print axioms FourPapers.FilteredHomology.liftsCycles_of_kernel_finrank_eq
#print axioms FourPapers.FilteredHomology.liftsCycles_of_homology_finrank_eq


end
end
end


end
