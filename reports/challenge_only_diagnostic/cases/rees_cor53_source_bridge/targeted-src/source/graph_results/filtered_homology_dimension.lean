module
public import graph_results.filtered_homology_ranks

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.FilteredHomologyDimension -/
section

section
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option synthInstance.maxHeartbeats 5000
noncomputable section
namespace FourPapers.FilteredHomology
open Classical Module
variable {K X Y Z : Type*} [Field K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
  [AddCommGroup Z] [Module K Z]

/-- Actual leading cycle lifts make the canonical map from the associated
graded of the actual kernel onto the graded kernel surjective. -/
theorem kernelGradeMap_surjective (F : Filtration (K := K) X)
    (G : Filtration (K := K) Y) (f : X →ₗ[K] Y) (hf : Preserves F G f)
    (hlift : LiftsCycles F G f) (n : ℕ) :
    Function.Surjective (kernelGradeMap F G f hf n) := by
  intro q
  obtain ⟨x,hx⟩ := (lowerInLevel F n).mkQ_surjective q.val
  have hfx : f x.val∈G.level n := by
    have hh := q.property
    rw [←hx] at hh
    change (Submodule.Quotient.mk (levelMap F G f hf (n+1) x) : Grade G n)=0 at hh
    exact (Submodule.Quotient.mk_eq_zero (lowerInLevel G n)).mp hh
  obtain ⟨y,hy,hfy,hxy⟩ := hlift n x.val x.property hfx
  let z : (cyclesFiltration F f).level (n+1) := ⟨⟨y,hfy⟩,hy⟩
  refine ⟨Submodule.Quotient.mk z,?_⟩
  apply Subtype.ext
  change (Submodule.Quotient.mk (⟨y,hy⟩ : F.level (n+1)) : Grade F n)=q.val
  rw [←hx]
  apply (Submodule.Quotient.eq _).mpr
  change y-x.val∈F.level n
  simpa only [neg_sub] using (F.level n).neg_mem hxy

def kernelGradeEquiv (F : Filtration (K := K) X)
    (G : Filtration (K := K) Y) (f : X →ₗ[K] Y) (hf : Preserves F G f)
    (hlift : LiftsCycles F G f) (n : ℕ) :
    Grade (cyclesFiltration F f) n ≃ₗ[K] LinearMap.ker (gradeMap F G f hf n) :=
  LinearEquiv.ofBijective (kernelGradeMap F G f hf n)
    ⟨kernelGradeMap_injective F G f hf n,kernelGradeMap_surjective F G f hf hlift n⟩

/-- Strictly lower corrections give literally equal associated-grade maps
on the same underlying filtrations. -/
theorem gradeMap_eq_of_lower (F : Filtration (K := K) X)
    (G : Filtration (K := K) Y) (f g : X →ₗ[K] Y)
    (hf : Preserves F G f) (hg : Preserves F G g)
    (hlower : ∀n x,x∈F.level (n+1)→f x-g x∈G.level n) (n : ℕ) :
    gradeMap F G f hf n=gradeMap F G g hg n := by
  apply LinearMap.ext
  intro x
  obtain ⟨x,rfl⟩ := (lowerInLevel F n).mkQ_surjective x
  change (Submodule.Quotient.mk (levelMap F G f hf (n+1) x) : Grade G n) =
    Submodule.Quotient.mk (levelMap F G g hg (n+1) x)
  apply (Submodule.Quotient.eq (lowerInLevel G n)).mpr
  exact hlower n x.val x.property

section Finite
variable [FiniteDimensional K X] [FiniteDimensional K Y]

/-- If both actual maps lift their leading cycles and have identical
associated-grade maps, their actual kernel dimensions agree. -/
theorem kernel_finrank_eq_of_liftsCycles
    (F : Filtration (K := K) X) (G : Filtration (K := K) Y)
    (f g : X →ₗ[K] Y) (hf : Preserves F G f) (hg : Preserves F G g)
    (hliftf : LiftsCycles F G f) (hliftg : LiftsCycles F G g)
    (hgrade : ∀n,gradeMap F G f hf n=gradeMap F G g hg n) :
    finrank K (LinearMap.ker f)=finrank K (LinearMap.ker g) := by
  obtain ⟨N,hN⟩ := F.exists_level_top
  have hNf : (cyclesFiltration F f).level N=⊤ := by
    ext x
    simp [cyclesFiltration,cycleLevel,hN]
  have hNg : (cyclesFiltration F g).level N=⊤ := by
    ext x
    simp [cyclesFiltration,cycleLevel,hN]
  rw [←sum_finrank_grade_of_top (cyclesFiltration F f) N hNf,
    ←sum_finrank_grade_of_top (cyclesFiltration F g) N hNg]
  apply Finset.sum_congr rfl
  intro n hn
  rw [(kernelGradeEquiv F G f hf hliftf n).finrank_eq,
    (kernelGradeEquiv F G g hg hliftg n).finrank_eq,hgrade n]

/-- The exact rank-nullity identity for a literal three-term homology
quotient. No nonnegative-dimension subtraction is used. -/
theorem threeTerm_homology_finrank_add
    (f : X →ₗ[K] Y) (g : Y →ₗ[K] Z) (hfg : g.comp f=0) :
    finrank K (Homology f g hfg)+finrank K X=
      finrank K (LinearMap.ker g)+finrank K (LinearMap.ker f) := by
  have hk : LinearMap.ker (boundaryMap f g hfg)=LinearMap.ker f := by
    ext x
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  have hr := (boundaryMap f g hfg).finrank_range_add_finrank_ker
  rw [hk] at hr
  have hq := (LinearMap.range (boundaryMap f g hfg)).finrank_quotient_add_finrank
  change finrank K (Homology f g hfg)+finrank K (LinearMap.range (boundaryMap f g hfg))=
    finrank K (LinearMap.ker g) at hq
  omega

variable [FiniteDimensional K Z]

/-- Equality of actual homology dimensions follows from actual cycle
lifting and equal associated-grade maps at the two differentials. -/
theorem homology_finrank_eq_of_liftsCycles
    (F : Filtration (K := K) X) (G : Filtration (K := K) Y)
    (H : Filtration (K := K) Z)
    (f f₀ : X →ₗ[K] Y) (g g₀ : Y →ₗ[K] Z)
    (hf : Preserves F G f) (hf₀ : Preserves F G f₀)
    (hg : Preserves G H g) (hg₀ : Preserves G H g₀)
    (hfg : g.comp f=0) (hf₀g₀ : g₀.comp f₀=0)
    (hliftf : LiftsCycles F G f) (hliftf₀ : LiftsCycles F G f₀)
    (hliftg : LiftsCycles G H g) (hliftg₀ : LiftsCycles G H g₀)
    (hgradef : ∀n,gradeMap F G f hf n=gradeMap F G f₀ hf₀ n)
    (hgradeg : ∀n,gradeMap G H g hg n=gradeMap G H g₀ hg₀ n) :
    finrank K (Homology f g hfg)=finrank K (Homology f₀ g₀ hf₀g₀) := by
  have hfker := kernel_finrank_eq_of_liftsCycles F G f f₀ hf hf₀ hliftf hliftf₀ hgradef
  have hgker := kernel_finrank_eq_of_liftsCycles G H g g₀ hg hg₀ hliftg hliftg₀ hgradeg
  have ha := threeTerm_homology_finrank_add f g hfg
  have hb := threeTerm_homology_finrank_add f₀ g₀ hf₀g₀
  omega

end Finite
end FourPapers.FilteredHomology
end

end
end


end
