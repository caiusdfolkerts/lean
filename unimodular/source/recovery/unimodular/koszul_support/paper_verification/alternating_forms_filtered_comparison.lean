module

public import Recovery.Unimodular.KoszulSupport.PaperVerification.FilteredComplexExactness

/-!
# From actual basis comparisons to filtered exactness

These lemmas turn a strict coefficient bound on the difference between
two maps into the full filtered-complex hypotheses. They apply to every
finite-support vector, not only to individual basis tensors. The exactness
conclusion is for the original differential and uses its actual
square-zero identity.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.AlternatingForms.FilteredComparison

open scoped BigOperators
open PaperVerification.Fermion.BasisFiltered
open PaperVerification.FilteredComplex

variable {K M₀ M₁ M₂ I₀ I₁ I₂ : Type*} [CommRing K]
  [AddCommGroup M₀] [Module K M₀] [AddCommGroup M₁] [Module K M₁]
  [AddCommGroup M₂] [Module K M₂]
  (b₀ : Module.Basis I₀ K M₀) (w₀ : I₀ → ℕ)
  (b₁ : Module.Basis I₁ K M₁) (w₁ : I₁ → ℕ)
  (b₂ : Module.Basis I₂ K M₂) (w₂ : I₂ → ℕ)

theorem hasTop_of_strict_difference (d : ℕ) (x y : M₀)
    (hy : Homogeneous b₀ w₀ d y)
    (hxy : ∀ i,b₀.repr (x-y) i≠0 → w₀ i<d) :
    HasTop b₀ w₀ d x y := by
  have hcomponent : component b₀ w₀ d (x-y)=0 := by
    apply b₀.repr.injective
    ext i
    rw [repr_component,map_zero,Finsupp.zero_apply]
    by_cases hi : w₀ i=d
    · rw [if_pos hi]
      by_contra hne
      have hlt := hxy i hne
      omega
    · rw [if_neg hi]
  refine ⟨?_,?_⟩
  · intro i hi
    by_cases hyi : b₀.repr y i=0
    · apply le_of_lt
      apply hxy i
      simpa only [map_sub,Finsupp.sub_apply,hyi,sub_zero] using hi
    · exact (hy i hyi).le
  · rw [map_sub,component_of_homogeneous b₀ w₀ hy,if_pos rfl,sub_eq_zero] at hcomponent
    exact hcomponent

theorem leadingMap_of_basis (f g : M₁ →ₗ[K] M₀)
    (h : ∀ i,HasTop b₀ w₀ (w₁ i) (f (b₁ i)) (g (b₁ i))) :
    HasLeadingMap b₀ w₀ b₁ w₁ f g := by
  intro d x hx
  have hstep (i : I₁) (hi : i∈(b₁.repr x).support) :
      HasTop b₀ w₀ d (f (b₁ i)) (g (component b₁ w₁ d (b₁ i))) := by
    have hle := hx i (Finsupp.mem_support_iff.mp hi)
    by_cases he : d=w₁ i
    · subst d
      rw [component_of_homogeneous b₁ w₁ (homogeneous_basis b₁ w₁ i),if_pos rfl]
      exact h i
    · have hlt : w₁ i<d := by omega
      refine ⟨bound_mono b₀ w₀ hle (h i).1,?_⟩
      rw [component_eq_zero_of_bound_lt b₀ w₀ hlt (h i).1,
        component_of_homogeneous b₁ w₁ (homogeneous_basis b₁ w₁ i),if_neg he,map_zero]
  have hs := HasTop.sum b₀ w₀ (b₁.repr x).support
    (fun i ↦ b₁.repr x i • f (b₁ i))
    (fun i ↦ b₁.repr x i • g (component b₁ w₁ d (b₁ i))) d
    (fun i hi ↦ HasTop.smul b₀ w₀ (hstep i hi) (b₁.repr x i))
  have he : ∑ i∈(b₁.repr x).support,b₁.repr x i • b₁ i=x := by
    simpa only [Finsupp.linearCombination_apply,Finsupp.sum] using b₁.linearCombination_repr x
  have hfx : ∑ i∈(b₁.repr x).support,b₁.repr x i • f (b₁ i)=f x := by
    simpa only [map_sum,map_smul] using congrArg f he
  have hgx : ∑ i∈(b₁.repr x).support,
      b₁.repr x i • g (component b₁ w₁ d (b₁ i))=g (component b₁ w₁ d x) := by
    simpa only [map_sum,map_smul] using congrArg (fun z ↦ g (component b₁ w₁ d z)) he
  simpa only [hfx,hgx,HasTop] using hs

theorem preservesComponents_of_basis (g : M₁ →ₗ[K] M₀)
    (h : ∀ i,Homogeneous b₀ w₀ (w₁ i) (g (b₁ i))) :
    PreservesComponents b₀ w₀ b₁ w₁ g := by
  intro d x
  have he : g.comp (component b₁ w₁ d)=(component b₀ w₀ d).comp g := by
    apply b₁.ext
    intro i
    simp only [LinearMap.comp_apply,
      component_of_homogeneous b₁ w₁ (homogeneous_basis b₁ w₁ i),
      component_of_homogeneous b₀ w₀ (h i)]
    split_ifs <;> simp only [map_zero]
  exact LinearMap.congr_fun he x

/-- Once the actual leading basis formulas and the cut exactness are
established, this proves exactness of the original coefficient maps. -/
theorem range_eq_ker_of_basis (f : M₁ →ₗ[K] M₀) (d : M₂ →ₗ[K] M₁)
    (f₀ : M₁ →ₗ[K] M₀) (d₀ : M₂ →ₗ[K] M₁)
    (hzero : f.comp d=0)
    (hf : ∀ i,HasTop b₀ w₀ (w₁ i) (f (b₁ i)) (f₀ (b₁ i)))
    (hd : ∀ i,HasTop b₁ w₁ (w₂ i) (d (b₂ i)) (d₀ (b₂ i)))
    (hexact : d₀.range=f₀.ker) :
    d.range=f.ker := by
  apply PaperVerification.FilteredComplex.range_eq_ker b₀ w₀ b₁ w₁ b₂ w₂
    f d f₀ d₀ hzero (leadingMap_of_basis b₀ w₀ b₁ w₁ f f₀ hf)
    (leadingMap_of_basis b₁ w₁ b₂ w₂ d d₀ hd)
  · apply preservesComponents_of_basis b₁ w₁ b₂ w₂
    intro i
    rw [←(hd i).2]
    exact homogeneous_component b₁ w₁ _ _
  · exact hexact

end PaperVerification.AlternatingForms.FilteredComparison

