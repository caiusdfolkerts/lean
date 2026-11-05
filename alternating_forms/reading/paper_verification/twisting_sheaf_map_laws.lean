module

public import PaperVerification.TwistingSheafMap

/-!
# Identity, composition, and changes of graded coordinates

These are laws for the actual fraction map on twisting sheaves. They are
the coherence data needed to transport twisting sheaves through changes of
frame and to glue them over a locally free module.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.TwistingSheafMap

open AlgebraicGeometry CategoryTheory TopologicalSpace
open AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf

universe u

variable {A B C σ τ ψ : Type u} [CommRing A] [CommRing B] [CommRing C]
  [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  [SetLike ψ C] [AddSubgroupClass ψ C]
  {𝒜 : ℕ → σ} {ℬ : ℕ → τ} {𝒞 : ℕ → ψ}
  [GradedRing 𝒜] [GradedRing ℬ] [GradedRing 𝒞]

theorem projMap_congr {f g : 𝒜 →+*ᵍ ℬ} (h : f = g)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hg : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map g) :
    Proj.map f hf = Proj.map g hg := by
  subst g
  rfl

/-- Inverse graded maps induce the actual inverse projective morphisms. -/
def projectiveIso (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hg : HomogeneousIdeal.irrelevant 𝒜 ≤ (HomogeneousIdeal.irrelevant ℬ).map g)
    (hgf : g.comp f = .id 𝒜) (hfg : f.comp g = .id ℬ) : Proj ℬ ≅ Proj 𝒜 where
  hom := Proj.map f hf
  inv := Proj.map g hg
  hom_inv_id :=
    (Proj.map_comp g f hg hf).symm.trans
      ((projMap_congr hfg _ (by simp)).trans Proj.map_id)
  inv_hom_id :=
    (Proj.map_comp f g hf hg).symm.trans
      ((projMap_congr hgf _ (by simp)).trans Proj.map_id)

set_option backward.isDefEq.respectTransparency false in
/-- Composition acts on fractions by composition of the coefficient maps. -/
theorem sectionsMap_comp (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒞)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hg : HomogeneousIdeal.irrelevant 𝒞 ≤ (HomogeneousIdeal.irrelevant ℬ).map g)
    (n : ℤ) (U : (Proj 𝒜).Opens) (s : Γ(Proj.twistingSheaf 𝒜 n, U)) :
    sectionsMap g hg n ((Proj.map f hf) ⁻¹ᵁ U) (sectionsMap f hf n U s) =
      sectionsMap (g.comp f) (HomogeneousIdeal.irrelevant_le_map_comp hf hg) n U s := by
  apply Proj.twistingSheaf.ext
  intro x
  dsimp [sectionsMap, fractionMap, Localization.localRingHom]
  rw [IsLocalization.map_map]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The identity graded map fixes every local homogeneous fraction. -/
theorem sectionsMap_id (n : ℤ) (U : (Proj 𝒜).Opens)
    (s : Γ(Proj.twistingSheaf 𝒜 n, U)) :
    sectionsMap (.id 𝒜) (by simp) n U s = s := by
  apply Proj.twistingSheaf.ext
  intro x
  letI := x.val.isPrime
  change Localization.localRingHom x.val.asHomogeneousIdeal.toIdeal
    x.val.asHomogeneousIdeal.toIdeal (RingHom.id A)
    (Ideal.comap_id x.val.asHomogeneousIdeal.toIdeal).symm (s.val x) = s.val x
  rw [Localization.localRingHom_id]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The sheaf morphisms obey composition, with the canonical pushforward
identifications explicitly displayed. -/
theorem pushforwardHom_comp (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒞)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hg : HomogeneousIdeal.irrelevant 𝒞 ≤ (HomogeneousIdeal.irrelevant ℬ).map g)
    (n : ℤ) :
    pushforwardHom (g.comp f) (HomogeneousIdeal.irrelevant_le_map_comp hf hg) n =
      pushforwardHom f hf n ≫
        (Scheme.Modules.pushforward (Proj.map f hf)).map (pushforwardHom g hg n) ≫
        (Scheme.Modules.pushforwardComp (Proj.map g hg) (Proj.map f hf)).hom.app
          (Proj.twistingSheaf 𝒞 n) ≫
        (Scheme.Modules.pushforwardCongr (Proj.map_comp f g hf hg).symm).hom.app
          (Proj.twistingSheaf 𝒞 n) := by
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  exact (sectionsMap_comp f g hf hg n U s).symm

set_option backward.isDefEq.respectTransparency false in
theorem pushforwardHom_id (n : ℤ) :
    pushforwardHom (.id 𝒜) (by simp) n ≫
      (Scheme.Modules.pushforwardCongr Proj.map_id).hom.app (Proj.twistingSheaf 𝒜 n) ≫
      (Scheme.Modules.pushforwardId (Proj 𝒜)).hom.app (Proj.twistingSheaf 𝒜 n) =
        𝟙 (Proj.twistingSheaf 𝒜 n) := by
  apply Scheme.Modules.hom_ext
  intro U
  ext s
  exact sectionsMap_id n U s

theorem pushforwardHom_id_isIso (n : ℤ) :
    IsIso (pushforwardHom (.id 𝒜) (by simp) n) := by
  have h := pushforwardHom_id (𝒜 := 𝒜) n
  exact IsIso.of_isIso_fac_right h

/-- One inverse graded-map identity makes the corresponding composite of
twisting-sheaf maps an isomorphism. -/
theorem pushforwardHom_comp_isIso (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hg : HomogeneousIdeal.irrelevant 𝒜 ≤ (HomogeneousIdeal.irrelevant ℬ).map g)
    (hgf : g.comp f = .id 𝒜) (n : ℤ) :
    IsIso (pushforwardHom f hf n ≫
      (Scheme.Modules.pushforward (Proj.map f hf)).map (pushforwardHom g hg n)) := by
  have h : IsIso
      (pushforwardHom (g.comp f) (HomogeneousIdeal.irrelevant_le_map_comp hf hg) n) := by
    have hidentity (u : 𝒜 →+*ᵍ 𝒜)
        (hu : HomogeneousIdeal.irrelevant 𝒜 ≤ (HomogeneousIdeal.irrelevant 𝒜).map u)
        (he : u = GradedRingHom.id 𝒜) : IsIso (pushforwardHom u hu n) := by
      subst u
      exact pushforwardHom_id_isIso n
    exact hidentity (g.comp f) (HomogeneousIdeal.irrelevant_le_map_comp hf hg) hgf
  rw [pushforwardHom_comp] at h
  simpa only [← Category.assoc, isIso_comp_right_iff] using h

/-- A genuine graded change of coordinates gives an isomorphism of the
twisting sheaf with its actual pushforward. -/
theorem pushforwardHom_isIso (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hg : HomogeneousIdeal.irrelevant 𝒜 ≤ (HomogeneousIdeal.irrelevant ℬ).map g)
    (hgf : g.comp f = .id 𝒜) (hfg : f.comp g = .id ℬ) (n : ℤ) :
    IsIso (pushforwardHom f hf n) := by
  let e := projectiveIso f g hf hg hgf hfg
  letI : IsIso (Proj.map g hg) := (show IsIso e.inv from inferInstance)
  letI := pushforwardHom_comp_isIso f g hf hg hgf n
  letI := pushforwardHom_comp_isIso g f hg hf hfg n
  letI : Mono (pushforwardHom f hf n) := mono_of_mono _
    ((Scheme.Modules.pushforward (Proj.map f hf)).map (pushforwardHom g hg n))
  letI : Epi ((Scheme.Modules.pushforward (Proj.map g hg)).map (pushforwardHom f hf n)) :=
    epi_of_epi (pushforwardHom g hg n) _
  letI : Epi (pushforwardHom f hf n) :=
    (Scheme.Modules.pushforward (Proj.map g hg)).epi_of_epi_map inferInstance
  exact isIso_of_mono_of_epi _

/-- The canonical map `Proj(f)^* 𝒪(n) → 𝒪(n)` is invertible for
degree-preserving changes of coordinates. -/
theorem pullbackHom_isIso (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hg : HomogeneousIdeal.irrelevant 𝒜 ≤ (HomogeneousIdeal.irrelevant ℬ).map g)
    (hgf : g.comp f = .id 𝒜) (hfg : f.comp g = .id ℬ) (n : ℤ) :
    IsIso (pullbackHom f hf n) := by
  let e := projectiveIso f g hf hg hgf hfg
  letI : IsIso (Proj.map f hf) := (show IsIso e.hom from inferInstance)
  letI := pushforwardHom_isIso f g hf hg hgf hfg n
  unfold pullbackHom
  rw [Adjunction.homEquiv_counit]
  infer_instance

/-- Canonical transport of all integer twists through an actual graded
frame change. -/
def pullbackIso (f : 𝒜 →+*ᵍ ℬ) (g : ℬ →+*ᵍ 𝒜)
    (hf : HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map f)
    (hg : HomogeneousIdeal.irrelevant 𝒜 ≤ (HomogeneousIdeal.irrelevant ℬ).map g)
    (hgf : g.comp f = .id 𝒜) (hfg : f.comp g = .id ℬ) (n : ℤ) :
    (Scheme.Modules.pullback (Proj.map f hf)).obj (Proj.twistingSheaf 𝒜 n) ≅
      Proj.twistingSheaf ℬ n := by
  letI := pullbackHom_isIso f g hf hg hgf hfg n
  exact asIso (pullbackHom f hf n)

end PaperVerification.TwistingSheafMap
