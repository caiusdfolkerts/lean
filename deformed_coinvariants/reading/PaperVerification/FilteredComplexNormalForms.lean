module

public import PaperVerification.FilteredComplexExactness
public import Mathlib.LinearAlgebra.Projection

/-!
# A fixed graded complement survives a filtered perturbation

The complement is a specified submodule of the original ambient module.
The resulting equivalence is induced by its actual inclusion and the
actual quotient map.  Both existence and uniqueness preserve the given
filtration bound.  The result requires the explicit leading-complex
hypotheses of `FilteredComplexExactness`; it does not replace the missing
construction of a Lie--Rinehart differential in the paper's application.

This source has not yet been compiled.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.FilteredComplex

open Fermion.BasisFiltered

variable {R M₀ M₁ M₂ I₀ I₁ I₂ : Type*} [CommRing R]
  [AddCommGroup M₀] [Module R M₀]
  [AddCommGroup M₁] [Module R M₁]
  [AddCommGroup M₂] [Module R M₂]
  (b₀ : Module.Basis I₀ R M₀) (w₀ : I₀ → ℕ)
  (b₁ : Module.Basis I₁ R M₁) (w₁ : I₁ → ℕ)
  (b₂ : Module.Basis I₂ R M₂) (w₂ : I₂ → ℕ)

def IsGraded (V : Submodule R M₀) : Prop :=
  ∀ m x, x ∈ V → component b₀ w₀ m x ∈ V

variable (f : M₁ →ₗ[R] M₀) (d : M₂ →ₗ[R] M₁)
  (f₀ : M₁ →ₗ[R] M₀) (d₀ : M₂ →ₗ[R] M₁)

/-- A bounded element is the sum of an actual image and an element of the
specified complement, both with the same bound. -/
theorem bounded_normal_form_exists
    (hf : HasLeadingMap b₀ w₀ b₁ w₁ f f₀)
    (hf₀ : PreservesComponents b₀ w₀ b₁ w₁ f₀)
    (V : Submodule R M₀) (hV : IsGraded b₀ w₀ V)
    (hspan : f₀.range ⊔ V = ⊤)
    (m : ℕ) (x : M₀) (hx : Bound b₀ w₀ m x) :
    ∃ u ∈ f.range, ∃ v ∈ V,
      Bound b₀ w₀ m u ∧ Bound b₀ w₀ m v ∧ x = u+v := by
  have step (r : ℕ) (y : M₀) (hy : Bound b₀ w₀ r y) :
      ∃ u ∈ f.range, ∃ v ∈ V,
        Bound b₀ w₀ r u ∧ Bound b₀ w₀ r v ∧
          Bound b₀ w₀ r (y-u-v) ∧ component b₀ w₀ r (y-u-v)=0 := by
    have hm : y ∈ f₀.range ⊔ V := by rw [hspan]; trivial
    obtain ⟨a,ha,v,hv,hav⟩ := Submodule.mem_sup.mp hm
    obtain ⟨z,hz⟩ := ha
    let u := f (component b₁ w₁ r z)
    have hcz := bound_component b₁ w₁ r z
    have hub : Bound b₀ w₀ r u := (hf r _ hcz).1
    have hut : component b₀ w₀ r u = component b₀ w₀ r a := by
      rw [(hf r _ hcz).2,
        component_of_homogeneous b₁ w₁ (homogeneous_component b₁ w₁ r z),if_pos rfl,
        hf₀ r z,hz]
    have hvb := bound_component b₀ w₀ r v
    refine ⟨u,⟨component b₁ w₁ r z,rfl⟩,component b₀ w₀ r v,hV r v hv,
      hub,hvb,bound_sub b₀ w₀ (bound_sub b₀ w₀ hy hub) hvb,?_⟩
    rw [map_sub,map_sub,hut,
      component_of_homogeneous b₀ w₀ (homogeneous_component b₀ w₀ r v),if_pos rfl,
      ←hav,map_add]
    abel
  induction m generalizing x with
  | zero =>
      obtain ⟨u,hu,v,hv,hub,hvb,hr,ht⟩ := step 0 x hx
      have hz := eq_zero_of_bound_zero_component_zero b₀ w₀ hr ht
      refine ⟨u,hu,v,hv,hub,hvb,?_⟩
      have he := sub_eq_zero.mp hz
      have := sub_eq_iff_eq_add.mp he
      simpa only [add_comm] using this
  | succ m ih =>
      obtain ⟨u,hu,v,hv,hub,hvb,hr,ht⟩ := step (m+1) x hx
      obtain ⟨a,ha,b,hb,hab,hbb,he⟩ :=
        ih (x-u-v) (bound_pred_of_component_zero b₀ w₀ hr ht)
      refine ⟨u+a,f.range.add_mem hu ha,v+b,V.add_mem hv hb,
        bound_add b₀ w₀ hub (bound_mono b₀ w₀ (Nat.le_succ m) hab),
        bound_add b₀ w₀ hvb (bound_mono b₀ w₀ (Nat.le_succ m) hbb),?_⟩
      calc
        x = (x-u-v)+u+v := by abel
        _ = (a+b)+u+v := by rw [he]
        _ = (u+a)+(v+b) := by abel

/-- A fixed graded complement to the leading image has zero intersection
with the actual image.  The image-strictness theorem supplies the key
leading-component membership. -/
theorem complement_disjoint_image
    (hzero : f.comp d = 0)
    (hf : HasLeadingMap b₀ w₀ b₁ w₁ f f₀)
    (hd : HasLeadingMap b₁ w₁ b₂ w₂ d d₀)
    (hd₀ : PreservesComponents b₁ w₁ b₂ w₂ d₀)
    (hexact : d₀.range = f₀.ker)
    (V : Submodule R M₀) (hV : IsGraded b₀ w₀ V)
    (hdisjoint : Disjoint V f₀.range) : Disjoint V f.range := by
  apply Submodule.disjoint_def.mpr
  intro x hx him
  obtain ⟨m,hm⟩ := exists_bound b₀ w₀ x
  have descend : ∀ r, Bound b₀ w₀ r x → x=0 := by
    intro r
    induction r with
    | zero =>
        intro hb
        have hc : component b₀ w₀ 0 x=0 :=
          Submodule.disjoint_def.mp hdisjoint _ (hV 0 x hx)
            (component_image_mem_leading_range b₀ w₀ b₁ w₁ b₂ w₂
              f d f₀ d₀ hzero hf hd hd₀ hexact 0 x hb him)
        exact eq_zero_of_bound_zero_component_zero b₀ w₀ hb hc
    | succ r ih =>
        intro hb
        have hc : component b₀ w₀ (r+1) x=0 :=
          Submodule.disjoint_def.mp hdisjoint _ (hV (r+1) x hx)
            (component_image_mem_leading_range b₀ w₀ b₁ w₁ b₂ w₂
              f d f₀ d₀ hzero hf hd hd₀ hexact (r+1) x hb him)
        exact ih (bound_pred_of_component_zero b₀ w₀ hb hc)
  exact descend m hm

/-- The same specified submodule remains a complement after perturbation. -/
theorem complement_survives
    (hzero : f.comp d = 0)
    (hf : HasLeadingMap b₀ w₀ b₁ w₁ f f₀)
    (hf₀ : PreservesComponents b₀ w₀ b₁ w₁ f₀)
    (hd : HasLeadingMap b₁ w₁ b₂ w₂ d d₀)
    (hd₀ : PreservesComponents b₁ w₁ b₂ w₂ d₀)
    (hexact : d₀.range = f₀.ker)
    (V : Submodule R M₀) (hV : IsGraded b₀ w₀ V)
    (hcompl : IsCompl f₀.range V) : IsCompl f.range V := by
  refine ⟨(complement_disjoint_image b₀ w₀ b₁ w₁ b₂ w₂
    f d f₀ d₀ hzero hf hd hd₀ hexact V hV hcompl.disjoint.symm).symm,?_⟩
  apply codisjoint_iff.mpr
  apply top_unique
  intro x hx
  obtain ⟨m,hm⟩ := exists_bound b₀ w₀ x
  obtain ⟨u,hu,v,hv,hub,hvb,he⟩ := bounded_normal_form_exists b₀ w₀ b₁ w₁
    f f₀ hf hf₀ V hV hcompl.sup_eq_top m x hm
  rw [he]
  exact Submodule.add_mem _ (le_sup_left hu) (le_sup_right hv)

/-- The quotient equivalence is the inclusion of the original complement.
Its filtration control is `bounded_normal_form_exists`. -/
def normalFormEquiv
    (hzero : f.comp d = 0)
    (hf : HasLeadingMap b₀ w₀ b₁ w₁ f f₀)
    (hf₀ : PreservesComponents b₀ w₀ b₁ w₁ f₀)
    (hd : HasLeadingMap b₁ w₁ b₂ w₂ d d₀)
    (hd₀ : PreservesComponents b₁ w₁ b₂ w₂ d₀)
    (hexact : d₀.range = f₀.ker)
    (V : Submodule R M₀) (hV : IsGraded b₀ w₀ V)
    (hcompl : IsCompl f₀.range V) : V ≃ₗ[R] M₀ ⧸ f.range :=
  (f.range.quotientEquivOfIsCompl V
    (complement_survives b₀ w₀ b₁ w₁ b₂ w₂ f d f₀ d₀
      hzero hf hf₀ hd hd₀ hexact V hV hcompl)).symm

@[simp] theorem normalFormEquiv_apply
    (hzero : f.comp d = 0)
    (hf : HasLeadingMap b₀ w₀ b₁ w₁ f f₀)
    (hf₀ : PreservesComponents b₀ w₀ b₁ w₁ f₀)
    (hd : HasLeadingMap b₁ w₁ b₂ w₂ d d₀)
    (hd₀ : PreservesComponents b₁ w₁ b₂ w₂ d₀)
    (hexact : d₀.range = f₀.ker)
    (V : Submodule R M₀) (hV : IsGraded b₀ w₀ V)
    (hcompl : IsCompl f₀.range V) (v : V) :
    normalFormEquiv b₀ w₀ b₁ w₁ b₂ w₂ f d f₀ d₀
      hzero hf hf₀ hd hd₀ hexact V hV hcompl v = f.range.mkQ v := by
  rfl

end PaperVerification.FilteredComplex
