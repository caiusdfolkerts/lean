module

public import PaperVerification.AlternatingFormsExteriorKoszul
public import PaperVerification.ExteriorMonomialRenaming
public import Mathlib.Order.Lattice

/-!
# Finite-index Koszul certificates in arbitrary universes

The ordinary derived-functor construction uses coefficient, module and
basis types in one universe. A literal finite coordinate basis is lifted
along its order isomorphism, and the preceding renaming theorem proves
that its actual exterior monomial ideal is unchanged. No algebraic
hypothesis or restriction on the field/vector-space universe is added.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped Classical

namespace PaperVerification.AlternatingForms.ExteriorKoszul

open PaperVerification ExteriorMonomialQuotient

universe u
variable {K M : Type u} [Field K] [AddCommGroup M] [Module K M]
  {I : Type} [LinearOrder I] [Fintype I]
  (b : Module.Basis I K M) (F : Set (Finset I)) (hF : ∀ S∈F,S.Nonempty)
  (R : I→I→Prop) [IsTrans I R] (hlt : ∀ i j,R i j→i<j)
  (hchain : ∀ S : Finset I,¬Bad F S↔S.sort.IsChain R)
  (f g : ⋀[K]^2 M) (he : monomialIdeal b F=exteriorRelationIdeal f g)

/-- The actual original-grading ordinary-Tor certificate, using a finite
coordinate index type without restricting the ambient universe. -/
def certificateOfFiniteMonomialIdeal : HomogeneousKoszulCertificate f g := by
  let e : ULift.{u} I ≃o I := ULift.orderIso
  let b' : Module.Basis (ULift.{u} I) K M := b.reindex e.toEquiv.symm
  let F' : Set (Finset (ULift.{u} I)) := renamedForbidden e F
  let R' : ULift.{u} I→ULift.{u} I→Prop := renamedRelation e R
  letI : IsTrans (ULift.{u} I) R' := renamedRelation_trans e R
  exact certificateOfMonomialIdeal b' F' (renamedForbidden_nonempty e F hF)
    R' (renamedRelation_increasing e R hlt) (renamed_chain e F R hchain) f g
    ((monomialIdeal_reindex b e F).trans he)

end PaperVerification.AlternatingForms.ExteriorKoszul
