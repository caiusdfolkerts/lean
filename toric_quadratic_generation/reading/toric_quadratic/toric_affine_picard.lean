module

public import PaperVerification.ToricInvertibleAffine
public import PaperVerification.ToricLocallyInvertible
public import PaperVerification.ToricLaurentPicard

@[expose] public section

/-!
# Invertible sheaves on an affine scheme and triviality on the split torus

Actual local frames make the section module locally rank one. The literal
principal-open restriction maps are module localizations by quasi-coherence.
The local algebra criterion therefore makes the global section module
invertible, and the tilde equivalence transports a module trivialization
back to an actual sheaf trivialization. Applied to the Laurent coordinate
ring, this proves that every actual invertible sheaf on the split torus is
trivial, with no affine Picard correspondence assumed.
-/

noncomputable section

universe u

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry

namespace PaperVerification.ToricSchemes

variable {R : CommRingCat.{u}} (M : (Spec R).Modules)

/-- Principal opens subordinate to one of the actual local frames. -/
def framedPrincipalSet (hM : IsInvertibleModule M) : Set R :=
  {f | ∃ x : Spec R,PrimeSpectrum.basicOpen f≤ invertibleOpen hM x}

theorem framedPrincipalSet_span (hM : IsInvertibleModule M) :
    Ideal.span (framedPrincipalSet M hM)=⊤ := by
  apply PrimeSpectrum.iSup_basicOpen_eq_top_iff'.mp
  apply le_antisymm le_top
  intro x hx
  obtain ⟨f,hxf,hf⟩ := exists_basicOpen_frame M hM x
  exact Opens.mem_iSup.mpr ⟨f,Opens.mem_iSup.mpr ⟨⟨x,hf⟩,hxf⟩⟩

set_option maxHeartbeats 2000000 in
/-- The global section module of an actual invertible sheaf is invertible in
Mathlib's tensor-product sense. All finiteness is derived from local frames. -/
theorem invertibleModule_globalSections (hM : IsInvertibleModule M) :
    Module.Invertible R Γ(M,⊤) := by
  classical
  let G : ModuleCat.{u} R := (modulesSpecToSheaf.obj M).obj.obj (op ⊤)
  change Module.Invertible R G
  let s := framedPrincipalSet M hM
  let U (f : s) : (Spec R).Opens := PrimeSpectrum.basicOpen f.val
  let A (f : s) : Type u := Γ(Spec R,U f)
  let N (f : s) : ModuleCat.{u} R := (modulesSpecToSheaf.obj M).obj.obj (op (U f))
  letI (f : s) : Algebra R (A f) := StructureSheaf.openAlgebra R (op (U f))
  letI (f : s) : IsLocalization.Away f.val (A f) :=
    StructureSheaf.IsLocalization.to_basicOpen R f.val
  letI (f : s) : Module (A f) (N f) := (M.val.obj (op (U f))).isModule
  letI (f : s) : IsScalarTower R (A f) (N f) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  let ρ (f : s) : G →ₗ[R] N f :=
    ((modulesSpecToSheaf.obj M).obj.map
      (homOfLE (show U f ≤ (⊤ : (Spec R).Opens) from le_top)).op).hom
  letI (f : s) : IsLocalizedModule.Away f.val (ρ f) :=
    invertibleAffine_isLocalizing M hM f.val
  apply invertible_of_principalCover_rankOne s (framedPrincipalSet_span M hM)
    A (fun f => (N f : Type u)) ρ
  intro f
  obtain ⟨x,hx⟩ := f.property
  exact ⟨invertibleFrameCoordinates hM x (U f) hx⟩

/-- Triviality of the actual ring Picard group trivializes actual invertible
sheaves on its spectrum. This is derived through the affine equivalence. -/
def affineInvertibleSheafIso [Subsingleton (CommRing.Pic R)]
    (hM : IsInvertibleModule M) :
    M ≅ SheafOfModules.unit (Spec R).ringCatSheaf := by
  letI := invertibleModule_globalSections M hM
  let e : Γ(M,⊤) ≃ₗ[R] R :=
    Classical.choice (Module.Invertible.free_iff_linearEquiv.mp inferInstance)
  exact (invertibleAffineTildeIso M hM).symm ≪≫
    (tilde.functor R).mapIso e.toModuleIso ≪≫ tildeSelf

section Torus

variable (k : Type u) [Field k] (n : ℕ)

/-- Every actual invertible sheaf on the split torus is globally rank one. -/
def torusInvertibleSheafIso
    (M : (Spec (CommRingCat.of (ToricCharacters.torusCoordinateRing k n))).Modules)
    (hM : IsInvertibleModule M) :
    M ≅ SheafOfModules.unit
      (Spec (CommRingCat.of (ToricCharacters.torusCoordinateRing k n))).ringCatSheaf := by
  letI := ToricCharacters.torusPic_subsingleton k n
  exact affineInvertibleSheafIso M hM

end Torus

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.invertibleModule_globalSections
#print axioms PaperVerification.ToricSchemes.torusInvertibleSheafIso
