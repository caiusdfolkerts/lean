module

public import PaperVerification.ToricCartierSheaf
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.CategoryTheory.Sites.Spaces

@[expose] public section

/-!
# Actual rank-one sheaves and the affine tilde equivalence

The rank-one condition used for Cartier sheaves implies Mathlib's local-free
and quasi-coherent conditions. Thus the affine section module recovers the
actual sheaf through the existing tilde equivalence. The local statements
below retain actual principal opens and actual restriction maps.
-/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

namespace PaperVerification.ToricSchemes

variable {X : Scheme.{u}} {M : X.Modules}

/-- The free sheaf on one generator is the actual structure module. -/
def freeSingletonIsoUnit (R : CategoryTheory.Sheaf
    (Opens.grothendieckTopology X) RingCat.{u}) :
    SheafOfModules.free (R := R) PUnit.{u+1} ≅ SheafOfModules.unit R :=
  coproductUniqueIso (fun _ : PUnit.{u+1} => SheafOfModules.unit R)

/-- A chosen rank-one neighborhood of each point. -/
def invertibleOpen (hM : IsInvertibleModule M) (x : X) : X.Opens :=
  (hM x).choose

theorem mem_invertibleOpen (hM : IsInvertibleModule M) (x : X) :
    x∈invertibleOpen hM x := (hM x).choose_spec.1

/-- The chosen local trivialization is an actual sheaf isomorphism. -/
def invertibleFrame (hM : IsInvertibleModule M) (x : X) :
    M.over (invertibleOpen hM x) ≅
      SheafOfModules.unit (X.ringCatSheaf.over (invertibleOpen hM x)) :=
  (hM x).choose_spec.2.some

/-- Evaluation of an actual local frame on a smaller open. -/
def invertibleFrameCoordinates (hM : IsInvertibleModule M) (x : X)
    (V : X.Opens) (hV : V ≤ invertibleOpen hM x) :
    Γ(M,V) ≃ₗ[Γ(X,V)] Γ(X,V) :=
  ((PresheafOfModules.evaluation
    (X.ringCatSheaf.over (invertibleOpen hM x)).obj
      (op (Over.mk (homOfLE hV)))).mapIso
    ((SheafOfModules.forget _).mapIso (invertibleFrame hM x))).toLinearEquiv

set_option backward.isDefEq.respectTransparency false in
/-- The chosen rank-one frame viewed as an isomorphism from a free sheaf. -/
def invertibleFreeFrame (hM : IsInvertibleModule M) (x : X) :
    SheafOfModules.free (R := X.ringCatSheaf.over (invertibleOpen hM x))
      PUnit.{u+1} ≅ (M : SheafOfModules.{u} X.ringCatSheaf).over (invertibleOpen hM x) :=
  coproductUniqueIso (fun _ : PUnit.{u+1} =>
    SheafOfModules.unit (X.ringCatSheaf.over (invertibleOpen hM x))) ≪≫
      (invertibleFrame hM x).symm

set_option backward.isDefEq.respectTransparency false in
/-- Actual local free generators, constructed from rank-one frames. -/
def invertibleLocalGenerators (hM : IsInvertibleModule M) :
    (M : SheafOfModules.{u} X.ringCatSheaf).LocalGeneratorsData where
  I := X
  X := invertibleOpen hM
  coversTop := by
    rw [Opens.coversTop_iff]
    apply le_antisymm le_top
    intro x hx
    exact Opens.mem_iSup.mpr ⟨x,mem_invertibleOpen hM x⟩
  generators x :=
    (SheafOfModules.GeneratingSections.equivOfIso (invertibleFreeFrame hM x))
      (SheafOfModules.free.generatingSections PUnit.{u+1})

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 2000000 in
instance invertibleLocalGenerators_isLocallyFree (hM : IsInvertibleModule M) :
    (invertibleLocalGenerators hM).IsLocallyFreeData where
  isIso x := by
    change X at x
    change IsIso
      (((SheafOfModules.free.generatingSections
        (R := X.ringCatSheaf.over (invertibleOpen hM x)) PUnit.{u+1}).ofEpi
          (invertibleFreeFrame hM x).hom).π)
    rw [SheafOfModules.GeneratingSections.ofEpi_π,
      SheafOfModules.free.generatingSections_π]
    exact IsIso.comp_isIso' (IsIso.id _) (invertibleFreeFrame hM x).isIso_hom

/-- Rank-one local triviality is genuine local freeness in Mathlib's sense. -/
theorem isLocallyFree_of_isInvertibleModule (hM : IsInvertibleModule M) :
    SheafOfModules.IsLocallyFree (R := X.ringCatSheaf)
      (M : SheafOfModules.{u} X.ringCatSheaf) :=
  (invertibleLocalGenerators hM).isLocallyFree

/-- In particular the actual invertible sheaf is quasi-coherent. -/
theorem isQuasicoherent_of_isInvertibleModule (hM : IsInvertibleModule M) :
    SheafOfModules.IsQuasicoherent (R := X.ringCatSheaf)
      (M : SheafOfModules.{u} X.ringCatSheaf) := by
  exact (invertibleLocalGenerators hM).quasiCoherentData.isQuasicoherent

section Affine

variable {R : CommRingCat.{u}} (M : (Spec R).Modules)

set_option backward.isDefEq.respectTransparency.types false in
/-- The global section module of an invertible sheaf recovers the actual
sheaf, by the established quasi-coherent affine equivalence. -/
def invertibleAffineTildeIso (hM : IsInvertibleModule M) :
    tilde ((moduleSpecΓFunctor (R := R)).obj M) ≅ M := by
  exact @asIso (Spec R).Modules _ _ _ M.fromTildeΓ
    ((isQuasicoherent_iff_isIso_fromTildeΓ M).mp (isQuasicoherent_of_isInvertibleModule hM))

/-- The actual restriction map on a principal open is module localization. -/
theorem invertibleAffine_isLocalizing (hM : IsInvertibleModule M) :
    IsLocalizing (modulesSpecToSheaf.obj M) := by
  letI := isQuasicoherent_of_isInvertibleModule hM
  exact (isIso_fromTildeΓ_iff_isLocalizing M).mp inferInstance

/-- Each point has a principal neighborhood on which the actual sheaf is
trivial. No finite generation or affine correspondence is assumed. -/
theorem exists_basicOpen_frame (hM : IsInvertibleModule M)
    (x : Spec R) :
    ∃ f : R, x∈PrimeSpectrum.basicOpen f ∧
      PrimeSpectrum.basicOpen f ≤ invertibleOpen hM x := by
  obtain ⟨U,⟨_,⟨f,rfl⟩,rfl⟩,hx,hU⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open
      (mem_invertibleOpen hM x) (invertibleOpen hM x).isOpen
  exact ⟨f,hx,hU⟩

/-- A finite principal-open cover subordinate to the actual rank-one frames.
The cover is extracted from compactness of the affine spectrum. -/
theorem exists_finite_basicOpen_frames (hM : IsInvertibleModule M) :
    ∃ (ι : Type u) (_ : Fintype ι) (f : ι→R) (p : ι→Spec R),
      (⨆ i,PrimeSpectrum.basicOpen (f i))=⊤ ∧
      ∀ i,PrimeSpectrum.basicOpen (f i) ≤ invertibleOpen hM (p i) := by
  classical
  choose f hf hsub using exists_basicOpen_frame M hM
  have hcover : IsOpenCover (fun x : Spec R => PrimeSpectrum.basicOpen (f x)) := by
    apply le_antisymm le_top
    intro x hx
    exact Opens.mem_iSup.mpr ⟨x,hf x⟩
  obtain ⟨s,hs⟩ := hcover.exists_finite_of_compactSpace
  exact ⟨s,inferInstance,fun i=>f i.val,fun i=>i.val,hs,fun i=>hsub i.val⟩

end Affine

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.isQuasicoherent_of_isInvertibleModule
#print axioms PaperVerification.ToricSchemes.invertibleAffineTildeIso
#print axioms PaperVerification.ToricSchemes.exists_finite_basicOpen_frames
