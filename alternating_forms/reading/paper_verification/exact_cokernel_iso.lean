module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Comparing two genuine cokernels of isomorphic maps

The inverse identities are proved once in an abstract abelian category,
before applying the construction to the large sheaf-cohomology objects in
the degree-one Leray comparison.
-/

@[expose] public section
noncomputable section
set_option autoImplicit false

namespace PaperVerification.ExactCokernelIso

open CategoryTheory CategoryTheory.Limits

variable {C : Type*} [Category C] [Abelian C]
  {S T : ShortComplex C} (hS : S.Exact) (hT : T.Exact)
  [Epi S.g] [Epi T.g]
  (e₁ : S.X₁ ≅ T.X₁) (e₂ : S.X₂ ≅ T.X₂)
  (h : S.f ≫ e₂.hom = e₁.hom ≫ T.f)

include h in
theorem inverse_square : T.f ≫ e₂.inv = e₁.inv ≫ S.f := by
  apply (cancel_epi e₁.hom).1
  rw [Iso.hom_inv_id_assoc, ← Category.assoc, ← h,
    Category.assoc, Iso.hom_inv_id, Category.comp_id]

include h in
theorem forward_zero : S.f ≫ (e₂.hom ≫ T.g) = 0 := by
  rw [← Category.assoc, h, Category.assoc, T.zero, comp_zero]

include h in
theorem backward_zero : T.f ≫ (e₂.inv ≫ S.g) = 0 := by
  rw [← Category.assoc, inverse_square e₁ e₂ h, Category.assoc, S.zero, comp_zero]

/-- An isomorphism of the first two terms induces an actual isomorphism
of the cokernel objects, assuming exactness and epimorphic cokernel maps. -/
def iso : S.X₃ ≅ T.X₃ where
  hom := hS.desc (e₂.hom ≫ T.g) (forward_zero e₁ e₂ h)
  inv := hT.desc (e₂.inv ≫ S.g) (backward_zero e₁ e₂ h)
  hom_inv_id := by
    rw [← cancel_epi S.g, hS.g_desc_assoc, Category.assoc,
      hT.g_desc, Iso.hom_inv_id_assoc, Category.comp_id]
  inv_hom_id := by
    rw [← cancel_epi T.g, hT.g_desc_assoc, Category.assoc,
      hS.g_desc, Iso.inv_hom_id_assoc, Category.comp_id]

/-- The induced isomorphism commutes with the original cokernel maps. -/
@[reassoc] theorem g_iso_hom :
    S.g ≫ (iso hS hT e₁ e₂ h).hom = e₂.hom ≫ T.g :=
  hS.g_desc _ _

end PaperVerification.ExactCokernelIso
