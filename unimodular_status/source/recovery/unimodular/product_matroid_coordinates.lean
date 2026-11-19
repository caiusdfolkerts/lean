module
public import Recovery.Unimodular.ProductLineMatroid
@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Unimodular.MatroidCoordinates

variable {K E F V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- An arbitrary field-linear coordinate equivalence and bijective relabeling
preserve every independent subset of the ordinary represented matroid. -/
theorem represented_eq_comap (v : E → V) (w : F → W)
    (g : V ≃ₗ[K] W) (f : E ≃ F) (h : ∀ a, w (f a) = g (v a)) :
    VectorMatroid.ofFamily (K := K) v = (VectorMatroid.ofFamily (K := K) w).comap f := by
  apply Matroid.ext_indep (by simp)
  intro S hS
  rw [VectorMatroid.ofFamily_indep, Matroid.comap_indep_iff, VectorMatroid.ofFamily_indep]
  have he : w ∘ f = g ∘ v := funext h
  constructor
  · intro hv
    have hg : LinearIndepOn K (g ∘ v) S := hv.map_injOn g.toLinearMap g.injective.injOn
    have hw : LinearIndepOn K (w ∘ f) S := by rwa [he]
    exact ⟨hw.image_of_comp f w, f.injective.injOn⟩
  · rintro ⟨hw, _⟩
    have hc : LinearIndepOn K (w ∘ f) S := hw.comp_of_image f.injective.injOn
    rw [he] at hc
    exact hc.of_comp g.toLinearMap

/-- A bijective relabeling preserves circuit-chain components even in the
presence of loops. No looplessness, rank, or finiteness hypothesis is needed. -/
def comapEquivComponents (M : Matroid F) (f : E ≃ F) :
    MatroidComponents.Component (M.comap f) ≃ MatroidComponents.Component M where
  toFun := MatroidComponents.comapComponentMap M f
  invFun := MatroidComponents.sectionComponentMap M f f.symm f.apply_symm_apply
  left_inv c := by
    obtain ⟨a, rfl⟩ := MatroidComponents.component_surjective (M.comap f) c
    change MatroidComponents.component (M.comap f) (f.symm (f a)) = _
    rw [f.symm_apply_apply]
  right_inv c := by
    obtain ⟨a, rfl⟩ := MatroidComponents.component_surjective M c
    change MatroidComponents.component M (f (f.symm a)) = _
    rw [f.apply_symm_apply]

@[simp] theorem comapEquivComponents_component (M : Matroid F) (f : E ≃ F) (a : E) :
    comapEquivComponents M f (MatroidComponents.component (M.comap f) a) =
      MatroidComponents.component M (f a) := rfl

/-- The component equivalence follows from actual vector-matroid equality. -/
def componentEquiv (v : E → V) (w : F → W)
    (g : V ≃ₗ[K] W) (f : E ≃ F) (h : ∀ a, w (f a) = g (v a)) :
    MatroidComponents.Component (VectorMatroid.ofFamily (K := K) v) ≃
      MatroidComponents.Component (VectorMatroid.ofFamily (K := K) w) :=
  (Equiv.cast (congrArg MatroidComponents.Component (represented_eq_comap v w g f h))).trans
    (comapEquivComponents (VectorMatroid.ofFamily (K := K) w) f)

@[simp] theorem componentEquiv_component (v : E → V) (w : F → W)
    (g : V ≃ₗ[K] W) (f : E ≃ F) (h : ∀ a, w (f a) = g (v a)) (a : E) :
    componentEquiv v w g f h (MatroidComponents.component (VectorMatroid.ofFamily (K := K) v) a) =
      MatroidComponents.component (VectorMatroid.ofFamily (K := K) w) (f a) := by
  dsimp only [componentEquiv, Equiv.trans_apply]
  rw [LineMatroid.cast_component (represented_eq_comap v w g f h) a]
  rfl

theorem component_eq_iff (v : E → V) (w : F → W)
    (g : V ≃ₗ[K] W) (f : E ≃ F) (h : ∀ a, w (f a) = g (v a)) (a b : E) :
    MatroidComponents.component (VectorMatroid.ofFamily (K := K) v) a =
        MatroidComponents.component (VectorMatroid.ofFamily (K := K) v) b ↔
      MatroidComponents.component (VectorMatroid.ofFamily (K := K) w) (f a) =
        MatroidComponents.component (VectorMatroid.ofFamily (K := K) w) (f b) := by
  rw [← componentEquiv_component v w g f h a, ← componentEquiv_component v w g f h b]
  exact (componentEquiv v w g f h).injective.eq_iff.symm

end Unimodular.MatroidCoordinates
#print axioms Unimodular.MatroidCoordinates.represented_eq_comap
#print axioms Unimodular.MatroidCoordinates.comapEquivComponents
#print axioms Unimodular.MatroidCoordinates.componentEquiv
#print axioms Unimodular.MatroidCoordinates.component_eq_iff
#check Unimodular.MatroidCoordinates.component_eq_iff
