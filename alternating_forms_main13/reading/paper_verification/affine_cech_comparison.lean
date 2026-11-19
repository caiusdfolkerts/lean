/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Affine
public import TauCeti.Topology.Sheaves.Leray

/-!
# Čech comparison for finite affine covers

This is the additive comparison from
`TauCeti.AlgebraicGeometry.Cohomology.Cech.Basic`, with only the dependencies
needed for that comparison. The scalar-action and affine-pushforward
extensions in the larger upstream module are unnecessary here.
-/

@[expose] public section
noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open TauCeti.CategoryTheory TauCeti.AlgebraicGeometry.Scheme.Modules

namespace PaperVerification.AffineCechComparison

universe u
variable {X : Scheme.{u}} {ι : Type u} [Finite ι]

/-- A finite cover with affine intersections computes actual sheaf cohomology. -/
def homologyCechComplexIsoCohomology (U : ι → X.Opens)
    (hU : ∀ s : Finset ι, s.Nonempty → IsAffineOpen (s.inf U))
    (hcover : iSup U = ⊤) (M : X.Modules) [M.IsQuasicoherent] (n : ℕ) :
    ((cechComplexFunctor U).obj
      ((SheafOfModules.toSheaf X.ringCatSheaf).obj M).obj).homology n ≅
      AddCommGrpCat.of (Cohomology M n) :=
  TauCeti.Topology.homologyCechComplexIsoH U hcover _
    (fun s hs k => AlgebraicGeometry.Scheme.Modules.subsingleton_cohomologyOn_succ_of_isAffineOpen
      M (hU s hs) k) n

end PaperVerification.AffineCechComparison
