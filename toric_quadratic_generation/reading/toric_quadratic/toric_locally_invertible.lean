module

public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.LocalProperties.FinitePresentation
public import Mathlib.RingTheory.LocalProperties.Exactness
public import Mathlib.RingTheory.Localization.BaseChange

@[expose] public section

/-!
# Actual rank-one local frames imply module invertibility

Local rank-one trivializations first imply finite presentation. Localization
then commutes with the dual and tensor product, carrying the canonical
evaluation pairing to its local counterpart. Its local bijectivity proves
global bijectivity. Neither finite generation nor projectivity nor a
global trivialization is an extra input.
-/

noncomputable section

namespace PaperVerification.ToricSchemes

open Module TensorProduct
open scoped TensorProduct

section OneLocalization

variable {R M N : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N]
  (S : Submonoid R) (A : Type*) [CommRing A] [Algebra R A]
  [IsLocalization S A] [Module A N] [IsScalarTower R A N]
  (f : M →ₗ[R] N) [IsLocalizedModule S f]

/-- Localization of actual linear functionals, with scalars extended
to the localized ring. -/
def localizedDual : Dual R M →ₗ[R] Dual A N :=
  IsLocalizedModule.mapExtendScalars S f (Algebra.linearMap R A) A

@[simp] theorem localizedDual_apply (φ : Dual R M) (m : M) :
    localizedDual S A f φ (f m) = algebraMap R A (φ m) := by
  exact IsLocalizedModule.map_apply S f (Algebra.linearMap R A) φ m

instance localizedDual_isLocalized [Module.FinitePresentation R M] :
    IsLocalizedModule S (localizedDual S A f) := by
  dsimp only [localizedDual]
  infer_instance

/-- The actual localization map on the domain of the evaluation
pairing. The tensor product in the codomain is over the localized ring. -/
def localizedEvaluationDomainMap :
    Dual R M ⊗[R] M →ₗ[R] Dual A N ⊗[A] N :=
  ((IsLocalization.moduleTensorEquiv S A (Dual A N) N).symm.restrictScalars R).toLinearMap.comp
    (TensorProduct.map (localizedDual S A f) f)

@[simp] theorem localizedEvaluationDomainMap_tmul (φ : Dual R M) (m : M) :
    localizedEvaluationDomainMap S A f (φ ⊗ₜ[R] m) =
      localizedDual S A f φ ⊗ₜ[A] f m := rfl

instance localizedEvaluationDomainMap_isLocalized [Module.FinitePresentation R M] :
    IsLocalizedModule S (localizedEvaluationDomainMap S A f) := by
  exact IsLocalizedModule.of_linearEquiv S
    (TensorProduct.map (localizedDual S A f) f)
    ((IsLocalization.moduleTensorEquiv S A (Dual A N) N).symm.restrictScalars R)

/-- The evaluation pairing commutes with the genuine localization maps. -/
theorem contractLeft_localization [Module.FinitePresentation R M] :
    IsLocalizedModule.map S (localizedEvaluationDomainMap S A f)
        (Algebra.linearMap R A) (contractLeft R M) =
      (contractLeft A N).restrictScalars R := by
  apply IsLocalizedModule.linearMap_ext S (localizedEvaluationDomainMap S A f)
    (Algebra.linearMap R A)
  apply TensorProduct.ext'
  intro φ m
  simpa only [LinearMap.comp_apply, contractLeft_apply, Algebra.linearMap_apply,
    LinearMap.restrictScalars_apply, localizedEvaluationDomainMap_tmul, localizedDual_apply] using
    IsLocalizedModule.map_apply S (localizedEvaluationDomainMap S A f)
      (Algebra.linearMap R A) (contractLeft R M) (φ ⊗ₜ[R] m)

end OneLocalization

section PrincipalCover

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M]
  (s : Set R) (hs : Ideal.span s = ⊤)
  (A : s → Type*) [∀ r, CommRing (A r)] [∀ r, Algebra R (A r)]
  [∀ r : s, IsLocalization.Away r.val (A r)]
  (N : s → Type*) [∀ r, AddCommGroup (N r)] [∀ r, Module R (N r)]
  [∀ r, Module (A r) (N r)] [∀ r, IsScalarTower R (A r) (N r)]
  (f : ∀ r, M →ₗ[R] N r) [∀ r : s, IsLocalizedModule.Away r.val (f r)]

include hs f in
/-- A module with actual rank-one frames on a principal-open cover is
invertible in the tensor-product sense used by Mathlib's Picard group.
The cover need not be presented as finite: finite presentation is derived
from the unit-ideal cover by the local-property theorem. -/
theorem invertible_of_principalCover_rankOne
    (hframe : ∀ r : s, Nonempty (N r ≃ₗ[A r] A r)) :
    Module.Invertible R M := by
  classical
  let e (r : s) : N r ≃ₗ[A r] A r := Classical.choice (hframe r)
  letI (r : s) : Module.FinitePresentation (A r) (N r) :=
    Module.FinitePresentation.of_equiv (e r).symm
  letI : Module.FinitePresentation R M :=
    Module.FinitePresentation.of_localizationSpan' (Rₚ := A) s hs f (fun r => inferInstance)
  letI (r : s) : Module.Invertible (A r) (N r) :=
    Module.Invertible.congr (e r).symm
  refine ⟨?_⟩
  apply bijective_of_isLocalized_span s hs
    (fun r => Dual (A r) (N r) ⊗[A r] N r)
    (fun r => localizedEvaluationDomainMap (Submonoid.powers r.val) (A r) (f r))
    A (fun r => Algebra.linearMap R (A r)) (contractLeft R M)
  intro r
  rw [contractLeft_localization]
  exact Module.Invertible.bijective

include hs in
/-- Specialization to the canonical localized ring and module, without
requiring any identifications as extra structure. -/
theorem invertible_of_localizationCover_rankOne
    (hframe : ∀ r : s, Nonempty
      (LocalizedModule.Away r.val M ≃ₗ[Localization.Away r.val] Localization.Away r.val)) :
    Module.Invertible R M :=
  invertible_of_principalCover_rankOne s hs
    (fun r => Localization.Away r.val) (fun r => LocalizedModule.Away r.val M)
    (fun r => LocalizedModule.mkLinearMap (Submonoid.powers r.val) M) hframe

end PrincipalCover

end PaperVerification.ToricSchemes

#print axioms PaperVerification.ToricSchemes.invertible_of_principalCover_rankOne
