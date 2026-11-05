module

public import PaperVerification.ToricIntrinsicSectionCoaction
public import PaperVerification.ToricFiniteCharacterSubspaces
public import PaperVerification.ToricCartierTensorPowers

@[expose] public section

/-!
# Actual tensor-power characters and finite spanning eigenvector families

The powers use the original normalized fractional frame raised to the
actual integer power. No new independently chosen torus trivialization
is introduced. Every finite family of genuine power sections is spanned
by finitely many genuine sections with literal character rational values.
-/

noncomputable section

universe u v

open AlgebraicGeometry CategoryTheory MonoidalCategory
open PaperVerification.ToricCharacters
open scoped Classical PaperVerification.ToricSchemes.BaseSections

namespace PaperVerification.ToricSchemes.SplitToricEmbedding

variable {k : Type u} [Field k] {n : ℕ}
    {X : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n→ℤ)) X]
    [IsIntegral X.left] [Smooth X.hom]
    (T : SplitToricEmbedding k n X)

theorem normalizedPower_unitFrames (D : CartierData X.left) (r : ℕ) :
    ((torusNormalizedCartier k n X.left T.torus.left D).nsmul r).localCocycle.HasUnitFramesOn
      T.torusOpen :=
  (torusNormalizedCartier k n X.left T.torus.left D).hasUnitFramesOn_nsmul
    (torusNormalizedCartier_unitFrames k n X.left T.torus.left D) r

def normalizedPowerCharacters (D : CartierData X.left) (r : ℕ) :
    Submodule k (AddMonoidAlgebra k (Fin n→ℤ)) :=
  torusSectionCharacters k n X.left T.torus.left
    ((torusNormalizedCartier k n X.left T.torus.left D).nsmul r)

theorem normalizedPowerCharacters_isCharacterStable (D : CartierData X.left) (r : ℕ) :
    IsCharacterStable k (T.normalizedPowerCharacters D r) :=
  T.torusSectionCharacters_isCharacterStable_of_unitFrames
    ((torusNormalizedCartier k n X.left T.torus.left D).nsmul r)
    (T.normalizedPower_unitFrames D r)

def normalizedPowerSectionCoordinates (D : CartierData X.left) (r : ℕ) :
    Γ(((torusNormalizedCartier k n X.left T.torus.left D).nsmul r).sheaf,⊤) ≃ₗ[k]
      T.normalizedPowerCharacters D r :=
  torusSectionCoordinates k n X.left T.torus.left
    ((torusNormalizedCartier k n X.left T.torus.left D).nsmul r)
    (T.normalizedPower_unitFrames D r)

theorem normalizedPowerSectionCoordinates_value (D : CartierData X.left) (r : ℕ)
    (s : Γ(((torusNormalizedCartier k n X.left T.torus.left D).nsmul r).sheaf,⊤)) :
    openTorusRationalAlgHom k n X.left T.torus.left
      ((T.normalizedPowerSectionCoordinates D r s).val) =
      ((torusNormalizedCartier k n X.left T.torus.left D).nsmul r).globalSectionValue k s :=
  torusSectionCoordinates_value k n X.left T.torus.left _ _ s

/-- No finite-dimensionality of all global sections is needed: a finite
family has a finite spanning family of actual character-valued sections. -/
theorem exists_finite_torus_eigensections_of_unitFrames
    (E : CartierData X.left) (hE : E.localCocycle.HasUnitFramesOn T.torusOpen)
    {I : Type v} [Fintype I] (s : I→Γ(E.sheaf,⊤)) :
    ∃ F : Finset (Fin n→ℤ), ∃ e : F→Γ(E.sheaf,⊤),
      (∀ m : F,openTorusRationalAlgHom k n X.left T.torus.left
        (AddMonoidAlgebra.single m.val (1:k))=E.globalSectionValue k (e m)) ∧
      (∀ i : I,s i∈Submodule.span k (Set.range e)) := by
  let V := torusSectionCharacters k n X.left T.torus.left E
  let c := torusSectionCoordinates k n X.left T.torus.left E hE
  let L : Γ(E.sheaf,⊤) →ₗ[k] AddMonoidAlgebra k (Fin n→ℤ) :=
    V.subtype.comp c.toLinearMap
  have hLinj : Function.Injective L := Subtype.val_injective.comp c.injective
  let Q : Finset (AddMonoidAlgebra k (Fin n→ℤ)) := Finset.univ.image (fun i=>L (s i))
  have hQV : ∀ f∈Q,f∈V := by
    intro f hf
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hf
    exact (c (s i)).property
  obtain ⟨F,hQF,hFV,-⟩ := exists_finite_character_subspace k V
    (T.torusSectionCharacters_isCharacterStable_of_unitFrames E hE) Q hQV
  have hsingle (m : F) : AddMonoidAlgebra.single m.val (1:k)∈V := by
    apply hFV
    rw [characterModule_eq_span]
    exact Submodule.subset_span ⟨m.val,m.property,rfl⟩
  let e : F→Γ(E.sheaf,⊤) := fun m=>c.symm ⟨AddMonoidAlgebra.single m.val 1,hsingle m⟩
  have hLe (m : F) : L (e m)=AddMonoidAlgebra.single m.val (1:k) := by
    change (c (c.symm ⟨AddMonoidAlgebra.single m.val 1,hsingle m⟩)).val=_
    rw [LinearEquiv.apply_symm_apply]
  have himage : L '' Set.range e =
      (fun m : Fin n→ℤ=>AddMonoidAlgebra.single m (1:k)) '' (F : Set (Fin n→ℤ)) := by
    ext f
    constructor
    · rintro ⟨t,⟨m,rfl⟩,rfl⟩
      exact ⟨m.val,m.property,(hLe m).symm⟩
    · rintro ⟨m,hm,rfl⟩
      exact ⟨e ⟨m,hm⟩,⟨⟨m,hm⟩,rfl⟩,hLe ⟨m,hm⟩⟩
  have hspan : (Submodule.span k (Set.range e)).map L = characterModule k (F : Set (Fin n→ℤ)) := by
    rw [Submodule.map_span,himage,characterModule_eq_span]
  refine ⟨F,e,?_,?_⟩
  · intro m
    have hv := torusSectionCoordinates_value k n X.left T.torus.left E hE (e m)
    change openTorusRationalAlgHom k n X.left T.torus.left (L (e m))=_ at hv
    rwa [hLe] at hv
  · intro i
    have hi : L (s i)∈(Submodule.span k (Set.range e)).map L := by
      rw [hspan]
      exact hQF (L (s i)) (Finset.mem_image.mpr ⟨i,Finset.mem_univ _,rfl⟩)
    obtain ⟨t,ht,hts⟩ := Submodule.mem_map.mp hi
    simpa only [hLinj hts] using ht

/-- The finite eigenvector replacement for genuine tensor powers used
in the intrinsic ample projective embedding. -/
theorem exists_finite_normalizedPower_eigensections
    (D : CartierData X.left) (r : ℕ) {I : Type v} [Fintype I]
    (s : I→Γ(((torusNormalizedCartier k n X.left T.torus.left D).nsmul r).sheaf,⊤)) :
    ∃ F : Finset (Fin n→ℤ),
      ∃ e : F→Γ(((torusNormalizedCartier k n X.left T.torus.left D).nsmul r).sheaf,⊤),
      (∀ m : F,openTorusRationalAlgHom k n X.left T.torus.left
        (AddMonoidAlgebra.single m.val (1:k))=
          ((torusNormalizedCartier k n X.left T.torus.left D).nsmul r).globalSectionValue k (e m)) ∧
      (∀ i : I,s i∈Submodule.span k (Set.range e)) :=
  T.exists_finite_torus_eigensections_of_unitFrames
    ((torusNormalizedCartier k n X.left T.torus.left D).nsmul r)
    (T.normalizedPower_unitFrames D r) s

end PaperVerification.ToricSchemes.SplitToricEmbedding
