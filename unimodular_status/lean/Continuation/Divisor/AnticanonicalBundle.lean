module

public import Continuation.Divisor.Geometry
public import Continuation.Divisor.AnticanonicalPairing
public import Continuation.Divisor.LineBundleFoundations

/-!
# The intrinsic anticanonical line bundle and its section growth

The canonical bundle is the top exterior power of the universal Kähler
sheaf, and the anticanonical bundle is its actual internal-Hom dual.
The rational differential calculation identifies it with the unit
boundary. All section spaces and all tensor powers below are ordinary
sheaf-theoretic constructions. Bigness is measured at the proved Krull
dimension of the actual fan scheme.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

universe u
namespace Unimodular.NefBig

open AlgebraicGeometry CategoryTheory Order MonoidalCategory
open PaperVerification.ToricSchemes PaperVerification.ToricGeometry
open TauCeti.AlgebraicGeometry
open scoped BaseSections

section IntrinsicPositivity

variable (k : Type u) [Field k] {X : Scheme.{u}}

variable [X.Over (Spec (CommRingCat.of k))]

/-- Bigness through the usual asymptotic section-growth characterization.
The exponent is the actual Krull dimension, and all section spaces are
required to be finite dimensional. The harmless factor `n!` from one
normalization of volume does not affect strict positivity. -/
def IsBig (M : X.Modules) : Prop :=
  ∃ n : ℕ, topologicalKrullDim X = n ∧
    (∀ m : ℕ, Module.Finite k Γ(tensorSheafPower M m, ⊤)) ∧
    0 < SectionGrowth.normalizedVolume n
      (fun m => Module.finrank k Γ(tensorSheafPower M m, ⊤))

/-- Bigness is invariant under actual sheaf isomorphisms. -/
theorem isBig_iff_of_iso {M N : X.Modules} (e : M ≅ N) :
    IsBig k M ↔ IsBig k N := by
  have forward : ∀ {M N : X.Modules}, (M ≅ N) → IsBig k M → IsBig k N := by
    intro M N e h
    obtain ⟨n, hdim, hfinite, hvolume⟩ := h
    refine ⟨n, hdim, ?_, ?_⟩
    · intro m
      letI := hfinite m
      exact (BaseSections.globalSectionsIso k (tensorSheafPowerIso e m)).finiteDimensional
    · have he : (fun m => Module.finrank k Γ(tensorSheafPower M m, ⊤)) =
          (fun m => Module.finrank k Γ(tensorSheafPower N m, ⊤)) := by
        funext m
        exact (BaseSections.globalSectionsIso k (tensorSheafPowerIso e m)).finrank_eq
      rw [← he]
      exact hvolume
  exact ⟨forward e, forward e.symm⟩

end IntrinsicPositivity

section TensorInverse
variable {X : Scheme.{u}}

local instance : MonoidalCategory X.Modules :=
  TauCeti.SheafOfModules.monoidalCategory X.sheaf
local instance : SymmetricCategory X.Modules :=
  TauCeti.SheafOfModules.symmetricCategory X.sheaf

/-- The standard monoidal tensor and the ordinary sheafified tensor are
canonically isomorphic. -/
def standardTensorIso (M N : X.Modules) : M ⊗ N ≅ tensorSheaf M N :=
  SheafOfModules.tensorUnderlyingIso M N

/-- Uniqueness of the tensor inverse, proved by associators, unitors and
the actual internal-Hom evaluation map. -/
def tensorInverseIsoDual (K : InvertibleSheaf X) (A : X.Modules)
    (h : tensorSheaf K.obj A ≅ SheafOfModules.unit X.ringCatSheaf) :
    A ≅ (InvertibleSheaf.dual K).obj := by
  let D := (InvertibleSheaf.dual K).obj
  let eval : K.obj ⊗ D ≅ SheafOfModules.unit X.ringCatSheaf :=
    by
      simpa only [D, InvertibleSheaf.dual_obj] using
        (Scheme.Modules.isoOfSheafIso X (K.evaluationDualIsoSheaf))
  let h' : K.obj ⊗ A ≅ SheafOfModules.unit X.ringCatSheaf :=
    standardTensorIso K.obj A ≪≫ h
  exact (λ_ A).symm ≪≫
    tensorIso ((β_ D K.obj) ≪≫ eval).symm (Iso.refl A) ≪≫
    (α_ D K.obj A) ≪≫ tensorIso (Iso.refl D) h' ≪≫ (ρ_ D)

end TensorInverse

variable {n : ℕ} (F : PaperVerification.ToricGeometry.SmoothCompleteFan n)
  (k : Type u) [Field k]

/-- The actual canonical line bundle: the top exterior power of the
universal Kähler differential sheaf on the actual smooth scheme. -/
def canonicalLineBundle : InvertibleSheaf (F.fanScheme k) :=
  ⟨topDifferentialSheaf k (F.fanScheme k) n,
    (isInvertibleModule_iff_standard _).mp
      (F.intrinsicTopDifferential_isInvertible k F.isPure)⟩

/-- The anticanonical line bundle is defined intrinsically by the
internal-Hom dual of the canonical bundle. -/
def anticanonicalLineBundle : InvertibleSheaf (F.fanScheme k) :=
  InvertibleSheaf.dual (canonicalLineBundle F k)

/-- The computed all-ones divisor is isomorphic to the intrinsically
defined anticanonical line bundle. -/
def anticanonical_unitBoundaryIso :
    (anticanonicalLineBundle F k).obj ≅
      (F.fanCartierData k F.isPure (fun _ => (1 : ℤ))).sheaf :=
  (tensorInverseIsoDual (canonicalLineBundle F k) _
    (intrinsicCanonical_unitBoundary_tensorIso F k)).symm

/-- Every ordinary tensor power of every toric Cartier line bundle on a
complete fan has a finite-dimensional global-section space. -/
theorem fanCartier_tensorPower_sections_finite (a : Lattice n → ℤ) (m : ℕ) :
    Module.Finite k Γ(tensorSheafPower (F.fanCartierData k F.isPure a).sheaf m, ⊤) := by
  let C := F.fanCartierCocycle k F.isPure a
  have hfinite : Module.Finite k Γ((C.pow m).sheaf, ⊤) := by
    change Module.Finite k Γ(((F.fanCartierCocycle k F.isPure a).pow m).sheaf, ⊤)
    rw [fanCartierCocycle_pow F k]
    exact fanSections_finite F k _
  letI := hfinite
  exact (BaseSections.globalSectionsIso k (C.tensorSheafPowerIso m)).symm.finiteDimensional

/-- The anticanonical bundle is big on every smooth complete fan. This
uses the integer cube in a fixed positive dilate of the unit-boundary
polytope, the exact global-section basis, and the actual dimension. -/
theorem anticanonical_isBig : IsBig k (anticanonicalLineBundle F k).obj := by
  apply (isBig_iff_of_iso k (anticanonical_unitBoundaryIso F k)).mpr
  exact ⟨n, F.fanScheme_topologicalKrullDim k F.isPure,
    fanCartier_tensorPower_sections_finite F k (fun _ => 1),
    unitBoundary_normalizedVolume_pos F k⟩

/-- Whenever all-ones support is convex, the intrinsic anticanonical
bundle is globally generated. -/
theorem anticanonical_isGloballyGenerated_of_support
    (h : F.IsNef (fun _ => 1)) :
    (anticanonicalLineBundle F k).IsGloballyGenerated := by
  apply (InvertibleSheaf.isGloballyGenerated_iff_of_iso
    (L := anticanonicalLineBundle F k)
    (N := cocycleInvertibleSheaf (F.fanCartierCocycle k F.isPure (fun _ => 1)))
    (anticanonical_unitBoundaryIso F k)).mpr
  exact fanCartier_isGloballyGenerated F k (fun _ => 1) (by simpa using h)

#print axioms tensorInverseIsoDual
#print axioms anticanonical_unitBoundaryIso
#print axioms anticanonical_isBig

end Unimodular.NefBig
