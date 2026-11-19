module

public import TauCeti.AlgebraicGeometry.ProjectiveSpectrum.TwistingSheaf.Basic
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor

/-!
# Functorial homogeneous fractions in the actual twisting sheaves

A degree-preserving ring map sends a local fraction `a / b` to `f a / f b`.
This gives the canonical morphism from the twisting sheaf on the target
of `Proj.map` to the pushforward of the twisting sheaf on its source.
Its adjoint is the actual pullback morphism of sheaves of modules.

The construction uses the existing local-fraction definition of `𝒪(n)`;
it introduces neither a substitute sheaf nor any cohomological assumption.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

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

/-- The map on the ambient localizations, evaluated on a section. -/
def fractionMap (U : (Proj 𝒜).Opens) (V : (Proj ℬ).Opens)
    (hUV : V ≤ (Proj.map f hf) ⁻¹ᵁ U)
    (s : ∀ x : U, Localizations 𝒜 x.val) (y : V) : Localizations ℬ y.val := by
  letI := y.val.isPrime
  letI := (ProjectiveSpectrum.comap f hf y.val).isPrime
  exact Localization.localRingHom
    (ProjectiveSpectrum.comap f hf y.val).asHomogeneousIdeal.toIdeal
    y.val.asHomogeneousIdeal.toIdeal f.toRingHom rfl
      (s ⟨ProjectiveSpectrum.comap f hf y.val, hUV y.property⟩)

set_option backward.isDefEq.respectTransparency false in
/-- Being locally a fraction of degree `n` is preserved by the actual map. -/
theorem fractionMap_isLocallyFraction (n : ℤ)
    (U : (Proj 𝒜).Opens) (V : (Proj ℬ).Opens)
    (hUV : V ≤ (Proj.map f hf) ⁻¹ᵁ U)
    (s : ∀ x : U, Localizations 𝒜 x.val)
    (hs : (isLocallyFraction 𝒜 n).pred s) :
    (isLocallyFraction ℬ n).pred (fractionMap f hf U V hUV s) := by
  rintro ⟨p, hpV⟩
  obtain ⟨W, m, iWU, i, j, hij, a, b, hb, hfrac⟩ :=
    hs ⟨ProjectiveSpectrum.comap f hf p, hUV hpV⟩
  refine ⟨W.comap (ProjectiveSpectrum.comap f hf) ⊓ V, ⟨m, hpV⟩,
    Opens.infLERight _ _, i, j, hij, f.gradedAddHom j a, f.gradedAddHom i b,
    fun ⟨q, hqW, hqV⟩ => hb ⟨_, hqW⟩, fun ⟨q, hqW, hqV⟩ => ?_⟩
  letI := q.isPrime
  have h := hfrac ⟨_, hqW⟩
  exact (congrArg (Localization.localRingHom
    (ProjectiveSpectrum.comap f hf q).asHomogeneousIdeal.toIdeal
    q.asHomogeneousIdeal.toIdeal f.toRingHom rfl) h).trans (by simp)

/-- Pull a genuine local-fraction section back along `Proj.map`. -/
def sectionsMap (n : ℤ) (U : (Proj 𝒜).Opens) :
    Γ(Proj.twistingSheaf 𝒜 n, U) →
      Γ(Proj.twistingSheaf ℬ n, (Proj.map f hf) ⁻¹ᵁ U) :=
  fun s => ⟨fractionMap f hf U _ le_rfl s.val,
    fractionMap_isLocallyFraction f hf n U _ le_rfl s.val s.property⟩

@[simp] theorem sectionsMap_add (n : ℤ) (U : (Proj 𝒜).Opens)
    (s t : Γ(Proj.twistingSheaf 𝒜 n, U)) :
    sectionsMap f hf n U (s + t) = sectionsMap f hf n U s + sectionsMap f hf n U t := by
  apply Proj.twistingSheaf.ext
  intro x
  exact map_add _ _ _

set_option backward.isDefEq.respectTransparency false in
/-- The section map is linear with the actual structure-sheaf pullback. -/
theorem sectionsMap_smul (n : ℤ) (U : (Proj 𝒜).Opens)
    (a : Γ(Proj 𝒜, U)) (s : Γ(Proj.twistingSheaf 𝒜 n, U)) :
    sectionsMap f hf n U (a • s) =
      (Proj.map f hf).app U a • sectionsMap f hf n U s := by
  apply Proj.twistingSheaf.ext
  intro x
  change Localization.localRingHom _ _ f.toRingHom rfl
    (((a.val ⟨_, x.property⟩).val) * s.val ⟨_, x.property⟩) =
    (HomogeneousLocalization.localRingHom f _ _ rfl
      (a.val ⟨_, x.property⟩)).val *
        Localization.localRingHom _ _ f.toRingHom rfl (s.val ⟨_, x.property⟩)
  rw [map_mul, HomogeneousLocalization.val_localRingHom]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The canonical morphism of actual sheaves of modules, before adjunction. -/
def pushforwardHom (n : ℤ) :
    Proj.twistingSheaf 𝒜 n ⟶
      (Scheme.Modules.pushforward (Proj.map f hf)).obj (Proj.twistingSheaf ℬ n) where
  val :=
    { app := fun U => by
        let M := (Proj.twistingSheaf 𝒜 n).val.obj U
        let N := ((Scheme.Modules.pushforward (Proj.map f hf)).obj
          (Proj.twistingSheaf ℬ n)).val.obj U
        exact ModuleCat.ofHom (X := M) (Y := N)
          { toFun := sectionsMap f hf n U.unop
            map_add' := sectionsMap_add f hf n U.unop
            map_smul' := fun a s => sectionsMap_smul f hf n U.unop a s }
      naturality := by
        intro U V i
        ext s x
        rfl }

/-- The canonical pullback map `Proj(f)^* 𝒪(n) → 𝒪(n)`. -/
def pullbackHom (n : ℤ) :
    (Scheme.Modules.pullback (Proj.map f hf)).obj (Proj.twistingSheaf 𝒜 n) ⟶
      Proj.twistingSheaf ℬ n :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (Proj.map f hf)).homEquiv _ _).symm
    (pushforwardHom f hf n)

end PaperVerification.TwistingSheafMap
