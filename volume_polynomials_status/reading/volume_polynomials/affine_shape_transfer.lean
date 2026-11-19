module

public import VolumePolynomials.ShapeProjectionGeometry
public import VolumePolynomials.HolonomyNonsemialgebraic

@[expose] public section
noncomputable section

open Set
open scoped Pointwise

namespace VolumePolynomials.Holonomy

/-- A literal affine copy of a planar set inside three-space. The linear part
is injective, so this records affine equivalence with its two-dimensional image. -/
def AffineCopy (S : Set Plane) (T : Set ThreeSpace) : Prop :=
  ∃ v : ThreeSpace, ∃ f : Plane →L[ℝ] ThreeSpace,
    Function.Injective f ∧ T = v +ᵥ f '' S

/-- The affine-copy predicate is equivalent to an affine embedding whose linear
part has a genuine continuous linear left inverse on the whole ambient space.
This makes invertibility onto the displayed image explicit. -/
theorem affineCopy_iff_exists_linear_leftInverse (S : Set Plane) (T : Set ThreeSpace) :
    AffineCopy S T ↔
      ∃ (v : ThreeSpace) (f : Plane →L[ℝ] ThreeSpace)
        (g : ThreeSpace →L[ℝ] Plane),
        Function.LeftInverse g f ∧ T = v +ᵥ f '' S := by
  first
  | constructor
    · rintro ⟨v, f, hf, hT⟩
      obtain ⟨g, hg⟩ := f.toLinearMap.exists_leftInverse_of_injective
        (LinearMap.ker_eq_bot.mpr hf)
      refine ⟨v, f, g.toContinuousLinearMap, ?_, hT⟩
      intro x
      change g (f x) = x
      exact congrArg (fun L : Plane →ₗ[ℝ] Plane => L x) hg
    · rintro ⟨v, f, g, hgf, hT⟩
      exact ⟨v, f, hgf.injective, hT⟩

/-- An affine copy has actual mutually inverse affine maps on the two sets.
The inverse is defined on all of three-space, so the assertion does not rely on
an informal interpretation of an inverse on an image or on an extra hypothesis.
-/
theorem AffineCopy.exists_affine_inverse {S : Set Plane} {T : Set ThreeSpace}
    (h : AffineCopy S T) :
    ∃ (F : Plane →ᵃ[ℝ] ThreeSpace) (G : ThreeSpace →ᵃ[ℝ] Plane),
      Function.LeftInverse G F ∧ F '' S = T ∧ G '' T = S ∧
        ∀ y ∈ T, F (G y) = y := by
  first
  | obtain ⟨v, f, g, hgf, hT⟩ :=
      (affineCopy_iff_exists_linear_leftInverse S T).mp h
    let F : Plane →ᵃ[ℝ] ThreeSpace :=
      { toFun := fun x => v + f x
        linear := f.toLinearMap
        map_vadd' := by
          first
          | intro p w
            simp only [vadd_eq_add, map_add, ContinuousLinearMap.coe_coe]
            abel }
    let G : ThreeSpace →ᵃ[ℝ] Plane :=
      { toFun := fun y => g (y - v)
        linear := g.toLinearMap
        map_vadd' := by
          first
          | intro p w
            change g (w + p - v) = g w + g (p - v)
            rw [add_sub_assoc, map_add] }
    have hGF : Function.LeftInverse G F := by
      first
      | intro x
        change g (v + f x - v) = x
        simpa only [add_sub_cancel_left] using hgf x
    have hFT : F '' S = T := by
      first
      | change (fun x => v + f x) '' S = T
        rw [hT, ← Set.image_vadd, Set.image_image]
        rfl
    refine ⟨F, G, hGF, hFT, ?_, ?_⟩
    · rw [← hFT, Set.image_image]
      have hfun : (fun x => G (F x)) = id := funext hGF
      rw [hfun, Set.image_id]
    · intro y hy
      rw [← hFT] at hy
      obtain ⟨x, hx, rfl⟩ := hy
      rw [hGF x]

theorem AffinelyNormalized.undo_affineCopy {K L : Fin 9 → Body 3}
    (hKL : AffinelyNormalized K L) (i : Fin 9) (S : Set Plane)
    (E : Plane →L[ℝ] ThreeSpace) (hE : Function.Injective E) (a : ThreeSpace)
    (hshape : (L i : Set ThreeSpace) = a +ᵥ E '' S) :
    AffineCopy S (K i) := by
  first
  | obtain ⟨g, hg, t, ht⟩ := hKL
    let f : Plane →L[ℝ] ThreeSpace := g.symm.toContinuousLinearMap.comp E
    refine ⟨-t i + g.symm a, f, g.symm.injective.comp hE, ?_⟩
    have heq : g '' (t i +ᵥ (K i : Set ThreeSpace)) = a +ᵥ E '' S := by
      first
      | have hh := congrArg (fun B : Body 3 => (B : Set ThreeSpace)) (ht i)
        simp only [coe_mapBody, coe_translateBody, ContinuousLinearEquiv.coe_coe] at hh
        exact hh.symm.trans hshape
    have hpre := congrArg (Set.image g.symm) heq
    have hpre' : t i +ᵥ (K i : Set ThreeSpace) = g.symm a +ᵥ f '' S := by
      first
      | have hf : (fun x => g.symm (E x)) = (f : Plane → ThreeSpace) := by
          funext x
          simp only [f, ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
        simpa only [linear_image_vadd, Set.image_image, Function.comp_apply,
          ContinuousLinearEquiv.symm_apply_apply, Set.image_id', hf] using hpre
    have hshift := congrArg (fun T : Set ThreeSpace => -t i +ᵥ T) hpre'
    simpa only [vadd_vadd, vadd_eq_add, neg_add_cancel, zero_vadd] using hshift

theorem affineCopy_not_semialgebraic (lam : ℝ) (hlam₀ : 0 < lam) (hlam₁ : lam < 1)
    {T : Set ThreeSpace} (hT : AffineCopy (forcedBody lam hlam₀.le hlam₁) T) :
    ¬ TauCeti.IsSemialgebraic T := by
  first
  | obtain ⟨v, f, hf, rfl⟩ := hT
    let L : (Fin 2 → ℝ) →ₗ[ℝ] ThreeSpace :=
      f.toLinearMap.comp (LinearEquiv.finTwoArrow ℝ ℝ).toLinearMap
    have hL : Function.Injective L := hf.comp (LinearEquiv.finTwoArrow ℝ ℝ).injective
    have hnon := forcedBody_affine_image_not_semialgebraic lam hlam₀ hlam₁ L hL v
    have heq : (fun x => v + L x) ''
        ((Homeomorph.finTwoArrow (X := ℝ)) ⁻¹'
          (forcedBody lam hlam₀.le hlam₁ : Set Plane)) =
        v +ᵥ f '' (forcedBody lam hlam₀.le hlam₁ : Set Plane) := by
      first
      | calc
          _ = (fun p : Plane => v + f p) ''
              ((Homeomorph.finTwoArrow (X := ℝ)) ''
                ((Homeomorph.finTwoArrow (X := ℝ)) ⁻¹'
                  (forcedBody lam hlam₀.le hlam₁ : Set Plane))) := by
            rw [Set.image_image]
            rfl
          _ = (fun p : Plane => v + f p) ''
              (forcedBody lam hlam₀.le hlam₁ : Set Plane) := by
            rw [Set.image_preimage_eq _ (Homeomorph.finTwoArrow (X := ℝ)).surjective]
          _ = _ := by
            rw [← Set.image_vadd, Set.image_image]
            rfl
    rwa [heq] at hnon

end VolumePolynomials.Holonomy
