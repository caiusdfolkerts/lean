module

public import Recovery.Unimodular.GraphicSectionRing.ToricDictionary.Part10
import all Recovery.Unimodular.GraphicSectionRing.ToricDictionary.Part10

public import Continuation.Divisor.IntrinsicAmple

/-! The genuine degree-one affine-section cover supplied by strict integral support.
This theorem is shared by ordinary ampleness and the positive-wall applications. -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricGeometry PaperVerification.ToricSchemes PaperVerification.ToricCharacters
open TauCeti.AlgebraicGeometry
open scoped Classical

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

variable {n : ℕ} (F : SmoothCompleteFan n)

local instance (k : Type*) [Field k] (a : Lattice n → ℤ) :
    SheafOfModules.isInvertible (F.fanScheme k) (F.fanCartierData k F.isPure a).sheaf := by
  change SheafOfModules.isInvertible (F.fanScheme k)
    (F.fanCartierCocycle k F.isPure a).sheaf
  infer_instance

/-- Each maximal-cone Cartier character is an ordinary degree-one
section whose actual nonvanishing open is that affine chart. -/
theorem fanCartier_affine_nonvanishing_cover_of_strictSupport
    (k : Type*) [Field k] (a : Lattice n → ℤ)
    (ha : F.IsStrictSupport (fun u => (a u : ℝ))) :
    ∀ x : F.fanScheme k, ∃ q : Γ((F.fanCartierData k F.isPure a).sheaf, ⊤),
      x ∈ (F.fanCartierData k F.isPure a).sheaf.nonvanishingLocus q ∧
      IsAffineOpen ((F.fanCartierData k F.isPure a).sheaf.nonvanishingLocus q) := by
  intro x
  let C := F.fanCartierCocycle k F.isPure a
  obtain ⟨s, hs⟩ := F.fullChartOpen_cover k F.isPure x
  obtain ⟨q, hq⟩ := Unimodular.NefBig.fanCartier_global_generators F k a
    (IsStrictSupport.isNef F ha) (ULift.up s)
  have hqopen : C.sheaf.nonvanishingLocus q = F.fullChartOpen k s :=
    (Unimodular.NefBig.cocycle_nonvanishingOpen_eq C q).symm.trans
      (Unimodular.NefBig.cartierCharacter_nonvanishingOpen F k a ha s q hq)
  refine ⟨q, ?_, ?_⟩
  · change x ∈ C.sheaf.nonvanishingLocus q
    rw [hqopen]
    exact hs
  · change IsAffineOpen (C.sheaf.nonvanishingLocus q)
    rw [hqopen]
    letI : IsAffine (coneChart k (F.fullConeIndex s).val) := by
      change IsAffine (Spec (CommRingCat.of
        (monoidChartAlgebra k (dualConeMonoid (F.fullConeIndex s).val))))
      infer_instance
    exact isAffineOpen_opensRange (F.fanChartMap k (F.fullConeIndex s))

end PaperVerification.ToricGeometry.SmoothCompleteFan
