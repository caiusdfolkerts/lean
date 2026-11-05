module

public import PaperVerification.TwistingSheafMap
public import PaperVerification.LineSheafSurjective
public import PaperVerification.ModulePullbackLocal
public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.LocalTriviality

/-!
# Pullback of actual twisting sheaves under generated graded maps

Suppose degree-one standard opens cover the source of a graded map. The
canonical map on the actual homogeneous-fraction sheaves induces an
isomorphism `Proj(f)^* O(n) ≅ O(n)` for every integer `n`.

On a standard open, the section `a^n` pulls back to `f(a)^n`. Every target
section is a regular multiple of that generator. Thus the pullback map
is surjective on a basis of opens, and a surjective morphism between
actual line bundles is invertible. In particular this applies to maps of
symmetric algebras induced by quotients or by coefficient localization;
no inverse graded map is required.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.TwistingSheafMap

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf

universe u

variable {A B σ τ : Type u} [CommRing A] [CommRing B]
  [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} [GradedRing 𝒜] [GradedRing ℬ]
  (f : 𝒜 →+*ᵍ ℬ)
  (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)

/-- The adjoint pullback map sends a pulled-back section to its actual
fraction image. This is the defining adjunction identity on sections. -/
theorem pullbackHom_pullbackSections (n : ℤ) (U : (Proj 𝒜).Opens)
    (s : Γ(Proj.twistingSheaf 𝒜 n, U)) :
    (pullbackHom f hf n).app ((Proj.map f hf) ⁻¹ᵁ U)
      (ModulePullbackLocal.sections (Proj.map f hf) (Proj.twistingSheaf 𝒜 n) U s) =
        sectionsMap f hf n U s := by
  have h := ((Scheme.Modules.pullbackPushforwardAdjunction (Proj.map f hf)).homEquiv
    (Proj.twistingSheaf 𝒜 n) (Proj.twistingSheaf ℬ n)).apply_symm_apply
      (pushforwardHom f hf n)
  rw [Adjunction.homEquiv_unit] at h
  exact congrArg (fun q => q.app U s) h

/-- The same identity after restriction to an arbitrary smaller open. -/
theorem pullbackHom_pullbackSectionsLE (n : ℤ) (U : (Proj 𝒜).Opens)
    (V : (Proj ℬ).Opens) (hV : V ≤ (Proj.map f hf) ⁻¹ᵁ U)
    (s : Γ(Proj.twistingSheaf 𝒜 n, U)) :
    (pullbackHom f hf n).app V
      (ModulePullbackLocal.sectionsLE (Proj.map f hf) (Proj.twistingSheaf 𝒜 n) U V hV s) =
        (Proj.twistingSheaf ℬ n).presheaf.map (homOfLE hV).op
          (sectionsMap f hf n U s) := by
  have hn := PresheafOfModules.naturality_apply (pullbackHom f hf n).val
    (homOfLE hV).op
    (ModulePullbackLocal.sections (Proj.map f hf) (Proj.twistingSheaf 𝒜 n) U s)
  exact hn.trans (congrArg
    ((Proj.twistingSheaf ℬ n).presheaf.map (homOfLE hV).op)
    (pullbackHom_pullbackSections f hf n U s))

set_option backward.isDefEq.respectTransparency false in
/-- The standard generator is carried to the standard generator, including
negative twists and rings with zero divisors. -/
theorem pullbackHom_chartGenerator (n : ℤ) (a : A) (ha : a ∈ 𝒜 1)
    (V : (Proj ℬ).Opens) (hV : V ≤ Proj.basicOpen ℬ (f a)) :
    (pullbackHom f hf n).app V
      (ModulePullbackLocal.sectionsLE (Proj.map f hf) (Proj.twistingSheaf 𝒜 n)
        (Proj.basicOpen 𝒜 a) V hV
        (Proj.twistingSheaf.chartGenerator n a ha _ le_rfl)) =
      Proj.twistingSheaf.chartGenerator n (f a) (f.map_mem ha) V hV := by
  rw [pullbackHom_pullbackSectionsLE]
  apply Proj.twistingSheaf.ext
  intro x
  change Localization.localRingHom _ _ f.toRingHom rfl
    ((Proj.twistingSheaf.chartGenerator n a ha (Proj.basicOpen 𝒜 a) le_rfl).val
      ⟨ProjectiveSpectrum.comap f hf x.val, hV x.property⟩) = _
  simp only [Proj.twistingSheaf.chartGenerator_apply, Localization.localRingHom_mk,
    map_pow, GradedRingHom.coe_toRingHom]

/-- On every open inside an image coordinate chart, the actual pullback
map on sections is surjective. -/
theorem pullbackHom_app_surjective (n : ℤ) (a : A) (ha : a ∈ 𝒜 1)
    (V : (Proj ℬ).Opens) (hV : V ≤ Proj.basicOpen ℬ (f a)) :
    Function.Surjective ((pullbackHom f hf n).app V) := by
  intro s
  let c := (Proj.twistingSheaf.chartSectionsLinearEquiv
    n (f a) (f.map_mem ha) V hV).symm s
  refine ⟨c • ModulePullbackLocal.sectionsLE (Proj.map f hf) (Proj.twistingSheaf 𝒜 n)
    (Proj.basicOpen 𝒜 a) V hV
    (Proj.twistingSheaf.chartGenerator n a ha _ le_rfl), ?_⟩
  rw [(pullbackHom f hf n).app_smul, pullbackHom_chartGenerator]
  exact (Proj.twistingSheaf.chartSectionsLinearEquiv
    n (f a) (f.map_mem ha) V hV).apply_symm_apply s

include hf in
/-- A degree-one covering family remains a covering family after the
actual projective morphism. -/
theorem image_degreeOne_cover {ι : Type u} (a : ι → A)
    (hcover : ⨆ i, Proj.basicOpen 𝒜 (a i) = ⊤) :
    ⨆ i, Proj.basicOpen ℬ (f (a i)) = ⊤ := by
  apply top_unique
  intro x hx
  have hx' : ProjectiveSpectrum.comap f hf x ∈
      (⨆ i, Proj.basicOpen 𝒜 (a i)) := by rw [hcover]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hx'
  exact Opens.mem_iSup.mpr ⟨i, hi⟩

/-- The canonical pullback map is an isomorphism whenever degree-one
standard opens cover. This is a theorem about the original sheaves. -/
theorem pullbackHom_isIso_of_degreeOne_cover {ι : Type u} (a : ι → A)
    (ha : ∀ i, a i ∈ 𝒜 1)
    (hcover : ⨆ i, Proj.basicOpen 𝒜 (a i) = ⊤) (n : ℤ) :
    IsIso (pullbackHom f hf n) := by
  have htarget := image_degreeOne_cover f hf a hcover
  apply SheafOfModules.isIso_of_coversTop
    ((_root_.Opens.coversTop_iff _ _).mpr (IsOpenCover.mk htarget))
    (pullbackHom f hf n)
  intro i
  let p := Proj.map f hf
  let U := Proj.basicOpen 𝒜 (a i)
  let e : ((Scheme.Modules.pullback p).obj (Proj.twistingSheaf 𝒜 n)).over (p ⁻¹ᵁ U) ≅
      SheafOfModules.unit ((Proj ℬ).ringCatSheaf.over (p ⁻¹ᵁ U)) :=
    ((ModulePullbackLocal.overUnitIso p U) ≪≫
      (ModulePullbackLocal.overPullback p U).mapIso (Proj.twistingSheaf.chartIso n (a i) (ha i)) ≪≫
      ModulePullbackLocal.overObjIso p U (Proj.twistingSheaf 𝒜 n)).symm
  apply LineSheafSurjective.isIso_over_of_surjective (pullbackHom f hf n)
    (Proj.basicOpen ℬ (f (a i))) e
    (Proj.twistingSheaf.chartIso n (f (a i)) (f.map_mem (ha i))).symm
  intro V
  exact pullbackHom_app_surjective f hf n (a i) (ha i) V.left V.hom.le

/-- Canonical pullback of every integer twist under any generated graded
map. Inverse coordinates or an isomorphism hypothesis are unnecessary. -/
def pullbackIso_of_degreeOne_cover {ι : Type u} (a : ι → A)
    (ha : ∀ i, a i ∈ 𝒜 1)
    (hcover : ⨆ i, Proj.basicOpen 𝒜 (a i) = ⊤) (n : ℤ) :
    (Scheme.Modules.pullback (Proj.map f hf)).obj (Proj.twistingSheaf 𝒜 n) ≅
      Proj.twistingSheaf ℬ n := by
  letI := pullbackHom_isIso_of_degreeOne_cover f hf a ha hcover n
  exact asIso (pullbackHom f hf n)

end PaperVerification.TwistingSheafMap
