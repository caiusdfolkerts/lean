module

public import ToricPower.CoherentCategory

/-! ## Source module `ToricPower.FinitePushforward`
Original SHA256: 3dd7e70f0c49215c6b6f171af738dcf2a59dd5eb59cd32ba792e6fb516309a40.
Original sources are retained in `third_party/coherent_sources`.
-/
section CoherentSource08

/-! # Exact finite pushforward on actual coherent sheaves

The ambient pushforward of all module sheaves is only left exact. Here its
right exactness is proved on quasicoherent sheaves by taking sections on
inverse images of affine opens. The resulting exact functor on coherent
sheaves is the ordinary scheme pushforward, restricted to the actual full
subcategory of finitely presented sheaves.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Scheme.Modules

namespace ToricPower

universe u

section AffineSections

variable {X : Scheme.{u}} {M N : X.Modules}

theorem fromSpecSectionsEquiv_naturality (φ : M ⟶ N) {U : X.Opens}
    (hU : IsAffineOpen U) (s : Γ(M, U)) :
    N.fromSpecSectionsEquiv hU (φ.app U s) =
      ((restrictFunctor hU.fromSpec).map φ).app ⊤
        (M.fromSpecSectionsEquiv hU s) := by
  rw [Scheme.Modules.fromSpecSectionsEquiv_apply,
    Scheme.Modules.fromSpecSectionsEquiv_apply]
  change N.presheaf.map (homOfLE (by
      rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec])).op (φ.app U s) =
    φ.app (hU.fromSpec ''ᵁ ⊤)
      (M.presheaf.map (homOfLE (by
        rw [Scheme.Hom.image_top_eq_opensRange, hU.opensRange_fromSpec])).op s)
  exact (ConcreteCategory.congr_hom (φ.mapPresheaf.naturality _) s).symm

/-- An epimorphism between quasicoherent sheaves is surjective on sections
over every affine open. -/
theorem affineSections_surjective_of_epi (φ : M ⟶ N) [Epi φ]
    [M.IsQuasicoherent] [N.IsQuasicoherent] {U : X.Opens}
    (hU : IsAffineOpen U) : Function.Surjective (φ.app U) := by
  let ψ := (restrictFunctor hU.fromSpec).map φ
  have hψ := TauCeti.AlgebraicGeometry.moduleSpecΓFunctor_map_surjective_of_epi_of_isQuasicoherent
    ψ
  intro t
  obtain ⟨s, hs⟩ := hψ (N.fromSpecSectionsEquiv hU t)
  refine ⟨(M.fromSpecSectionsEquiv hU).symm s, ?_⟩
  apply (N.fromSpecSectionsEquiv hU).injective
  rw [fromSpecSectionsEquiv_naturality]
  change ψ.app ⊤ s = N.fromSpecSectionsEquiv hU t at hs
  exact (congrArg (fun z => ψ.app ⊤ z)
    ((M.fromSpecSectionsEquiv hU).apply_symm_apply s)).trans hs

end AffineSections

section AffinePushforward

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [IsAffineHom f]

/-- Affine pushforward preserves epimorphisms between quasicoherent sheaves.
No exactness assertion is made for arbitrary module sheaves. -/
theorem affinePushforward_epi {M N : X.Modules} (φ : M ⟶ N) [Epi φ]
    [M.IsQuasicoherent] [N.IsQuasicoherent] :
    Epi ((pushforward f).map φ) := by
  apply (SheafOfModules.toSheaf.{u} Y.ringCatSheaf).epi_of_epi_map
  let η := (SheafOfModules.toSheaf.{u} Y.ringCatSheaf).map ((pushforward f).map φ)
  have hη : TopCat.Presheaf.IsLocallySurjective η.hom := by
    apply (TopCat.Presheaf.isLocallySurjective_iff η.hom).2
    intro U t y hy
    obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVU⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open hy U.isOpen
    refine ⟨V, hVU, ?_, hyV⟩
    exact affineSections_surjective_of_epi φ (hV.preimage f) _
  letI : CategoryTheory.Sheaf.IsLocallySurjective η := hη
  exact inferInstanceAs (Epi η)

/-- The ordinary pushforward of a short exact sequence of quasicoherent
sheaves under an affine morphism is short exact. -/
theorem affinePushforward_shortExact {S : ShortComplex X.Modules}
    (hS : S.ShortExact) [S.X₂.IsQuasicoherent] [S.X₃.IsQuasicoherent] :
    (S.map (pushforward f)).ShortExact := by
  have hleft := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
    (pushforward f)).mp inferInstance S hS
  letI : Epi S.g := hS.epi_g
  exact { exact := hleft.1, mono_f := hleft.2, epi_g := affinePushforward_epi f S.g }

end AffinePushforward

section CoherentPushforward

variable (X Y : Scheme.{u}) [IsLocallyNoetherian X] [IsLocallyNoetherian Y]

instance coherentInclusion_preservesFiniteLimits :
    PreservesFiniteLimits (SheafOfModules.isFinitePresentation X.ringCatSheaf).ι := by
  letI : ∀ {M N : TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf X} (φ : M ⟶ N),
      PreservesLimit (parallelPair φ 0)
        (SheafOfModules.isFinitePresentation X.ringCatSheaf).ι :=
    fun φ => (SheafOfModules.isFinitePresentation X.ringCatSheaf).preservesKernels_ι φ
  exact CategoryTheory.Functor.preservesFiniteLimits_of_preservesKernels _

instance coherentInclusion_preservesFiniteColimits :
    PreservesFiniteColimits (SheafOfModules.isFinitePresentation X.ringCatSheaf).ι := by
  letI : ∀ {M N : TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf X} (φ : M ⟶ N),
      PreservesColimit (parallelPair φ 0)
        (SheafOfModules.isFinitePresentation X.ringCatSheaf).ι :=
    fun φ => (SheafOfModules.isFinitePresentation X.ringCatSheaf).preservesCokernels_ι φ
  exact CategoryTheory.Functor.preservesFiniteColimits_of_preservesCokernels _

variable {X Y} (f : X ⟶ Y) [IsFinite f]

instance coherentPushforward_preservesFiniteLimits :
    PreservesFiniteLimits (TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.pushforward f) := by
  let F := TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.pushforward f
  let I := (SheafOfModules.isFinitePresentation Y.ringCatSheaf).ι
  have hFI : PreservesFiniteLimits (F ⋙ I) := by
    dsimp only [F, I]
    rw [TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.pushforward_comp_inclusion]
    exact @comp_preservesFiniteLimits _ _ _ _ _ _ _ _
      (coherentInclusion_preservesFiniteLimits X)
      (inferInstanceAs (PreservesFiniteLimits (Scheme.Modules.pushforward f)))
  letI := hFI
  exact preservesFiniteLimits_of_reflects_of_preserves F I

instance coherentPushforward_preservesFiniteColimits :
    PreservesFiniteColimits (TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.pushforward f) := by
  let F := TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.pushforward f
  apply (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi F).2
  intro S hS
  have hleft := (Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono F).mp
    inferInstance S hS
  letI : Epi S.g := hS.epi_g
  let I := (SheafOfModules.isFinitePresentation X.ringCatSheaf).ι
  let J := (SheafOfModules.isFinitePresentation Y.ringCatSheaf).ι
  letI : PreservesFiniteColimits I := coherentInclusion_preservesFiniteColimits X
  have hbase : Epi ((pushforward f).map S.g.hom) :=
    @affinePushforward_epi X Y f inferInstance _ _ S.g.hom
      (inferInstance : Epi (I.map S.g)) inferInstance inferInstance
  have hepi : Epi (F.map S.g) := by
    apply J.epi_of_epi_map
    change Epi ((F ⋙ J).map S.g)
    dsimp only [F, J]
    rw [TauCeti.AlgebraicGeometry.FinitelyPresentedSheaf.pushforward_comp_inclusion]
    exact hbase
  exact ⟨hleft.1, hepi⟩

end CoherentPushforward

end ToricPower


-- Close scopes implicitly ended by the original source EOF.
end
end CoherentSource08
