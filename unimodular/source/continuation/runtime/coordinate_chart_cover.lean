module

public import Continuation.Runtime.RealValuativeSchemeCharts

/-!
# A finite cover by actual character coordinate charts

This record stores literal open immersions and their proved agreement on
the original torus. It contains no fan, overlap assumption, projective
embedding, or assumed cone-completeness statement. The invariant affine
neighbourhood construction supplies this record for the original smooth
complete split toric scheme.
-/

@[expose] public noncomputable section

universe u

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricCharacters PaperVerification.ToricGeometry

namespace PaperVerification.ToricSchemes

structure CoordinateChartCover (k : Type u) [Field k] (n : ℕ) (X : Scheme.{u})
    (j : Spec (CommRingCat.of (AddMonoidAlgebra k (Lattice n))) ⟶ X) where
  Index : Type u
  finiteIndex : Fintype Index
  basis : Index → Module.Basis (Fin n) ℤ (Lattice n)
  coordinates : Index → Finset (Fin n)
  map : ∀ i, monoidChartScheme k (coordinateConeMonoid (basis i) (coordinates i)) ⟶ X
  isOpenImmersion : ∀ i, IsOpenImmersion (map i)
  torus_eq : ∀ i, characterChartTorusMap k (coordinateConeMonoid (basis i) (coordinates i)) ≫
    map i = j
  covers : ∀ x : X, ∃ i z, map i z = x

attribute [instance] CoordinateChartCover.finiteIndex CoordinateChartCover.isOpenImmersion

end PaperVerification.ToricSchemes
