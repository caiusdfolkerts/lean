module
public import graph_foundation.part014
public import shared_results.part021_ideal_coordinate_order_leading

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.FiniteBasedComparison -/
section

/-! # A common finite rank enumeration for two homogeneous chain groups -/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace FourPapers.FiniteBasedComparison

open Classical CommAlg FilteredHomology

variable {K X Y I J U Γ : Type*} [Field K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
  [FiniteDimensional K X] [Fintype U] [LinearOrder Γ]
  (b : Module.Basis I K X) (c : Module.Basis J K Y)
  (degreeX : I → U) (degreeY : J → U) (w : U → Γ)

def sourceFiltration : Filtration (K:=K) X :=
  Universal.basisFiltration b (fun i => FiniteOrderedComparison.rankWeight w (degreeX i))

def targetFiltration : Filtration (K:=K) Y :=
  Universal.basisFiltration c (fun j => FiniteOrderedComparison.rankWeight w (degreeY j))

def OrderedLifts (f : X →ₗ[K] Y) : Prop :=
  ∀ n x,x∈BasisCycleLifting.level b (w ∘ degreeX) n →
    f x∈BasisCycleLifting.lower c (w ∘ degreeY) n →
      ∃ z,z∈BasisCycleLifting.level b (w ∘ degreeX) n ∧ f z=0 ∧
        x-z∈BasisCycleLifting.lower b (w ∘ degreeX) n

theorem source_top :
    (sourceFiltration b degreeX w).level (FiniteOrderedComparison.weights w).card=⊤ := by
  apply top_unique
  intro x hx
  rw [sourceFiltration,Universal.basisFiltration,Module.Basis.mem_span_image]
  intro i hi
  exact FiniteOrderedComparison.rankWeight_bound w (degreeX i)

theorem preserves_of_basis (f : X →ₗ[K] Y)
    (hf : ∀ i j,c.repr (f (b i)) j≠0 → w (degreeY j)≤w (degreeX i)) :
    Preserves (sourceFiltration b degreeX w) (targetFiltration c degreeY w) f := by
  intro n x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i,hi,rfl⟩ := hx
    rw [targetFiltration,Universal.basisFiltration,Module.Basis.mem_span_image]
    intro j hj
    exact ((FiniteOrderedComparison.rankWeight_le w (degreeY j) (degreeX i)).mpr
      (hf i j (Finsupp.mem_support_iff.mp hj))).trans_lt hi
  | zero => simpa only [map_zero] using Submodule.zero_mem _
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul r x hx ih => simpa only [map_smul] using Submodule.smul_mem _ r ih

theorem strict_difference (f f₀ : X →ₗ[K] Y)
    (hlead : ∀ i j,w (degreeX i)≤w (degreeY j) → c.repr (f (b i)) j=c.repr (f₀ (b i)) j) :
    ∀ n x,x∈(sourceFiltration b degreeX w).level (n+1) →
      f x-f₀ x∈(targetFiltration c degreeY w).level n := by
  intro n x hx
  change (f-f₀) x∈(targetFiltration c degreeY w).level n
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i,hi,rfl⟩ := hx
    rw [targetFiltration,Universal.basisFiltration,Module.Basis.mem_span_image]
    intro j hj
    have hlt : w (degreeY j)<w (degreeX i) := by
      by_contra hn
      have he := hlead i j (le_of_not_gt hn)
      apply Finsupp.mem_support_iff.mp hj
      simp only [LinearMap.sub_apply,map_sub,Finsupp.sub_apply,he,sub_self]
    exact ((FiniteOrderedComparison.rankWeight_lt w (degreeY j) (degreeX i)).mpr hlt).trans_le
      (Nat.lt_succ_iff.mp hi)
  | zero => simpa only [map_zero] using Submodule.zero_mem _
  | add x y hx hy ihx ihy => simpa only [map_add] using Submodule.add_mem _ ihx ihy
  | smul r x hx ih => simpa only [map_smul] using Submodule.smul_mem _ r ih

theorem orderedLifts_of_rankLifts (f : X →ₗ[K] Y)
    (hlift : LiftsCycles (sourceFiltration b degreeX w) (targetFiltration c degreeY w) f) :
    OrderedLifts b c degreeX degreeY w f := by
  intro n x hx hfx
  by_cases hn : ∃ a,w a=n
  · obtain ⟨a,rfl⟩ := hn
    have hx' : x∈(sourceFiltration b degreeX w).level (FiniteOrderedComparison.rankWeight w a+1) := by
      rw [sourceFiltration,Universal.basisFiltration,Module.Basis.mem_span_image]
      rw [BasisCycleLifting.level,Module.Basis.mem_span_image] at hx
      intro i hi
      exact Nat.lt_succ_iff.mpr ((FiniteOrderedComparison.rankWeight_le w (degreeX i) a).mpr (hx hi))
    have hfx' : f x∈(targetFiltration c degreeY w).level (FiniteOrderedComparison.rankWeight w a) := by
      rw [targetFiltration,Universal.basisFiltration,Module.Basis.mem_span_image]
      rw [BasisCycleLifting.lower,Module.Basis.mem_span_image] at hfx
      intro j hj
      exact (FiniteOrderedComparison.rankWeight_lt w (degreeY j) a).mpr (hfx hj)
    obtain ⟨z,hz,hfz,herr⟩ := hlift (FiniteOrderedComparison.rankWeight w a) x hx' hfx'
    refine ⟨z,?_,hfz,?_⟩
    · rw [BasisCycleLifting.level,Module.Basis.mem_span_image]
      rw [sourceFiltration,Universal.basisFiltration,Module.Basis.mem_span_image] at hz
      intro i hi
      exact (FiniteOrderedComparison.rankWeight_le w (degreeX i) a).mp (Nat.lt_succ_iff.mp (hz hi))
    · rw [BasisCycleLifting.lower,Module.Basis.mem_span_image]
      rw [sourceFiltration,Universal.basisFiltration,Module.Basis.mem_span_image] at herr
      intro i hi
      exact (FiniteOrderedComparison.rankWeight_lt w (degreeX i) a).mp (herr hi)
  · refine ⟨0,Submodule.zero_mem _,map_zero _,?_⟩
    rw [sub_zero,BasisCycleLifting.lower,Module.Basis.mem_span_image]
    rw [BasisCycleLifting.level,Module.Basis.mem_span_image] at hx
    intro i hi
    exact lt_of_le_of_ne (hx hi) (fun he => hn ⟨degreeX i,he⟩)

theorem orderedLifts_of_equal_kernel [FiniteDimensional K Y] (f f₀ : X →ₗ[K] Y)
    (hhom : ∀ i j,c.repr (f₀ (b i)) j≠0 → w (degreeY j)=w (degreeX i))
    (hlead : ∀ i j,w (degreeX i)≤w (degreeY j) → c.repr (f (b i)) j=c.repr (f₀ (b i)) j)
    (hdim : Module.finrank K (LinearMap.ker f)=Module.finrank K (LinearMap.ker f₀)) :
    OrderedLifts b c degreeX degreeY w f := by
  have hd : ∀ i j,c.repr (f (b i)) j≠0 → w (degreeY j)≤w (degreeX i) := by
    intro i j hj
    by_contra hn
    have he := hlead i j (le_of_lt (lt_of_not_ge hn))
    exact (not_lt_of_ge (hhom i j (he ▸ hj)).le) (lt_of_not_ge hn)
  have hhom' : ∀ i,f₀ (b i)∈Grading.Piece c
      (fun j => FiniteOrderedComparison.rankWeight w (degreeY j))
      (FiniteOrderedComparison.rankWeight w (degreeX i)) := by
    intro i
    rw [Grading.mem_piece]
    intro j hj
    apply le_antisymm
    · exact (FiniteOrderedComparison.rankWeight_le w (degreeY j) (degreeX i)).mpr (hhom i j hj).le
    · exact (FiniteOrderedComparison.rankWeight_le w (degreeX i) (degreeY j)).mpr (hhom i j hj).ge
  apply orderedLifts_of_rankLifts b c degreeX degreeY w f
  exact liftsCycles_of_equal_kernel_strict_perturbation
    (sourceFiltration b degreeX w) (targetFiltration c degreeY w) f
    (preserves_of_basis b c degreeX degreeY w f hd) f₀
    (preserves_of_basis b c degreeX degreeY w f₀ (fun i j h => (hhom i j h).le))
    (strict_difference b c degreeX degreeY w f f₀ hlead)
    (Universal.basisHomogeneous_liftsCycles b c _ _ f₀ hhom')
    (FiniteOrderedComparison.weights w).card (source_top b degreeX w) hdim

theorem rankLifts_of_orderedLifts (f : X →ₗ[K] Y)
    (hlift : OrderedLifts b c degreeX degreeY w f) :
    LiftsCycles (sourceFiltration b degreeX w) (targetFiltration c degreeY w) f := by
  intro n x hx hfx
  by_cases hn : ∃ a,FiniteOrderedComparison.rankWeight w a=n
  · obtain ⟨a,ha⟩ := hn
    have hx' : x∈BasisCycleLifting.level b (w ∘ degreeX) (w a) := by
      rw [BasisCycleLifting.level,Module.Basis.mem_span_image]
      rw [sourceFiltration,Universal.basisFiltration,Module.Basis.mem_span_image] at hx
      intro i hi
      apply (FiniteOrderedComparison.rankWeight_le w (degreeX i) a).mp
      rw [ha]
      exact Nat.lt_succ_iff.mp (hx hi)
    have hfx' : f x∈BasisCycleLifting.lower c (w ∘ degreeY) (w a) := by
      rw [BasisCycleLifting.lower,Module.Basis.mem_span_image]
      rw [targetFiltration,Universal.basisFiltration,Module.Basis.mem_span_image] at hfx
      intro j hj
      apply (FiniteOrderedComparison.rankWeight_lt w (degreeY j) a).mp
      rw [ha]
      exact hfx hj
    obtain ⟨z,hz,hfz,herr⟩ := hlift (w a) x hx' hfx'
    refine ⟨z,?_,hfz,?_⟩
    · rw [sourceFiltration,Universal.basisFiltration,Module.Basis.mem_span_image]
      rw [BasisCycleLifting.level,Module.Basis.mem_span_image] at hz
      intro i hi
      apply Nat.lt_succ_iff.mpr
      rw [← ha]
      exact (FiniteOrderedComparison.rankWeight_le w (degreeX i) a).mpr (hz hi)
    · rw [sourceFiltration,Universal.basisFiltration,Module.Basis.mem_span_image]
      rw [BasisCycleLifting.lower,Module.Basis.mem_span_image] at herr
      intro i hi
      rw [← ha]
      exact (FiniteOrderedComparison.rankWeight_lt w (degreeX i) a).mpr (herr hi)
  · refine ⟨0,Submodule.zero_mem _,map_zero _,?_⟩
    rw [sub_zero,sourceFiltration,Universal.basisFiltration,Module.Basis.mem_span_image]
    rw [sourceFiltration,Universal.basisFiltration,Module.Basis.mem_span_image] at hx
    intro i hi
    exact lt_of_le_of_ne (Nat.lt_succ_iff.mp (hx hi)) (fun he => hn ⟨degreeX i,he⟩)

/-- Actual leading-cycle lifting implies equality of kernel dimensions,
with the homogeneous model identified coefficientwise. -/
theorem kernel_finrank_eq_of_orderedLifts [FiniteDimensional K Y] (f f₀ : X →ₗ[K] Y)
    (hhom : ∀ i j,c.repr (f₀ (b i)) j≠0 → w (degreeY j)=w (degreeX i))
    (hlead : ∀ i j,w (degreeX i)≤w (degreeY j) → c.repr (f (b i)) j=c.repr (f₀ (b i)) j)
    (hlift : OrderedLifts b c degreeX degreeY w f) :
    Module.finrank K (LinearMap.ker f)=Module.finrank K (LinearMap.ker f₀) := by
  have hd : ∀ i j,c.repr (f (b i)) j≠0 → w (degreeY j)≤w (degreeX i) := by
    intro i j hj
    by_contra hn
    have he := hlead i j (le_of_lt (lt_of_not_ge hn))
    exact (not_lt_of_ge (hhom i j (he ▸ hj)).le) (lt_of_not_ge hn)
  have hhom' : ∀ i,f₀ (b i)∈Grading.Piece c
      (fun j => FiniteOrderedComparison.rankWeight w (degreeY j))
      (FiniteOrderedComparison.rankWeight w (degreeX i)) := by
    intro i
    rw [Grading.mem_piece]
    intro j hj
    apply le_antisymm
    · exact (FiniteOrderedComparison.rankWeight_le w (degreeY j) (degreeX i)).mpr (hhom i j hj).le
    · exact (FiniteOrderedComparison.rankWeight_le w (degreeX i) (degreeY j)).mpr (hhom i j hj).ge
  let hf := preserves_of_basis b c degreeX degreeY w f hd
  let hf₀ := preserves_of_basis b c degreeX degreeY w f₀ (fun i j hj => (hhom i j hj).le)
  rw [kernel_dimension_eq_of_liftsCycles _ _ f hf _ (source_top b degreeX w)
    (rankLifts_of_orderedLifts b c degreeX degreeY w f hlift)]
  rw [kernel_dimension_eq_of_liftsCycles _ _ f₀ hf₀ _ (source_top b degreeX w)
    (Universal.basisHomogeneous_liftsCycles b c _ _ f₀ hhom')]
  apply Finset.sum_congr rfl
  intro n hn
  exact congrArg (fun h : Grade (sourceFiltration b degreeX w) n →ₗ[K]
      Grade (targetFiltration c degreeY w) n => Module.finrank K (LinearMap.ker h))
    (gradeMap_eq_of_strict_difference _ _ f f₀ hf hf₀
      (strict_difference b c degreeX degreeY w f f₀ hlead) n)

end FourPapers.FiniteBasedComparison

end
end
end


end
