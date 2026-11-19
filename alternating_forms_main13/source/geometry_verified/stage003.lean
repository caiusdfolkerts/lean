module

public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Limits.Lattice

set_option Elab.async false

section GeometryLiteralSource029
/- Original source: PaperVerification.ExactCokernelIso -/


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
end
end
end GeometryLiteralSource029

run_cmd Lean.logInfo "GEOMETRY_SOURCE_END: PaperVerification.ExactCokernelIso"

section GeometryLiteralSource030
/- Original source: TauCeti.CategoryTheory.Limits.Lattice -/
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Finite products of reindexed families in a lattice

In a `SemilatticeInf` with `OrderTop`, Mathlib identifies the finite product of a family with the
infimum of its members (`CategoryTheory.Limits.CompleteLattice.finite_product_eq_finset_inf`). This
file records the reindexed form used for Čech complexes: the product of the members `f (a j)` of a
family `f`, for `a : J → ι` with `J` finite, is the infimum of `f` over the image of `a`.
-/

public section

universe u v w

namespace CategoryTheory.Limits.CompleteLattice

variable {α : Type u} [SemilatticeInf α] [OrderTop α]

/-- The finite product of the members `f (a j)` of a family `f` is the infimum of `f` over the
image of `a`. Unlike `finite_product_eq_finset_inf`, the index type `J` may live in any universe,
as for the products `U (a 0) × ⋯ × U (a n)` indexed by `Fin (n + 1)` in Čech complexes. -/
theorem finite_product_eq_finset_image_inf {ι : Type v} [DecidableEq ι] {J : Type w}
    [Fintype J] (f : ι → α) (a : J → ι) :
    (∏ᶜ fun j ↦ f (a j)) = (Finset.univ.image a).inf f := by
  rw [Finset.inf_image]
  refine (finite_limit_eq_finset_univ_inf _).trans ?_
  -- reindex the infimum over `Discrete J` along `discreteEquiv`
  rw [← Finset.univ_map_equiv_to_embedding (discreteEquiv (α := J)).symm, Finset.inf_map]
  rfl

end CategoryTheory.Limits.CompleteLattice
end
end GeometryLiteralSource030

run_cmd Lean.logInfo "GEOMETRY_SOURCE_END: TauCeti.CategoryTheory.Limits.Lattice"

