module

public import ToricPower.Cohomology.SchemeBasic
public import ToricPower.CartierCore
public import ToricPower.AdditiveEndAction

@[expose] public section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 1000000

section SchemeCohomologySource67Action
/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/


/-!
# Scalar actions on the cohomology of a sheaf of modules on a scheme

This file equips the cohomology of a sheaf of modules on a scheme with its canonical module
structure over the ring of global functions. The construction first realizes a global function
as a scalar endomorphism of the coefficient sheaf, then applies the cohomology functor. No
coherence or quasi-coherence hypothesis is imposed on the coefficient sheaf.

The resulting action agrees in degree zero with the usual action on global sections, and every
map on cohomology induced by a morphism of coefficient sheaves is linear. For a scheme over a
base commutative ring, `TauCeti.AlgebraicGeometry.Cohomology.Module.Base` restricts these
actions along the induced map on global functions to actions of the base ring.
-/

public section

open CategoryTheory Limits TopologicalSpace AlgebraicGeometry Scheme.Modules Opposite

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

namespace Scheme.Modules

variable {X : Scheme.{u}} {M N : X.Modules}

/-- The action of global functions on cohomology, bundled as a ring homomorphism into additive
endomorphisms. -/
def _root_.AlgebraicGeometry.Scheme.Modules.cohomologyAction
    (M : X.Modules) (i : ℕ) :
    Γ(X, ⊤) →+* AddMonoid.End (Cohomology M i) :=
  (ToricPower.additiveFunctorEndAction (cohomologyFunctor X i) M).comp
    (globalSectionsAction M)


@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomologyAction_apply
    (M : X.Modules) (i : ℕ) (r : Γ(X, ⊤)) (x : Cohomology M i) :
    cohomologyAction M i r x =
      (cohomologyFunctor X i).map (M.globalSectionsSmul r) x := by
  change ((cohomologyFunctor X i).map ((globalSectionsAction M r).asHom)).hom x = _
  rw [globalSectionsAction_apply]

/-- Cohomology is canonically a module over the ring of global functions. -/
instance _root_.AlgebraicGeometry.Scheme.Modules.cohomologyModule
    (M : X.Modules) (i : ℕ) : Module Γ(X, ⊤) (Cohomology M i) :=
  Module.compHom (Cohomology M i) (cohomologyAction M i)

/-- Scalar multiplication on cohomology is induced by the cohomology map of the corresponding
scalar endomorphism of the coefficient sheaf. -/
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.Modules.cohomology_smul
    (M : X.Modules) (i : ℕ) (r : Γ(X, ⊤)) (x : Cohomology M i) :
    r • x = (cohomologyFunctor X i).map (M.globalSectionsSmul r) x :=
  by
    -- `Module.compHom` exposes its action definitionally, without an accessor lemma.
    change cohomologyAction M i r x = _
    exact cohomologyAction_apply M i r x


end Scheme.Modules

end

end AlgebraicGeometry

end TauCeti

end
end SchemeCohomologySource67Action
