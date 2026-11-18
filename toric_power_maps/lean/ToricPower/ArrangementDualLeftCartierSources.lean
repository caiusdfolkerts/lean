module

public import ToricPower.ArrangementQuasicoherentLabels
public import ToricPower.ToricMonomialDualityFunctor
public import ToricPower.ToricInverseCartierTensor

/-! # The original covariant cellular labels as Cartier sources

The divisor and every actual positive-character incidence map are kept.
This adapter supplies genuine inverse-tensor adjunction mates.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory Opposite TauCeti.Toric
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  [nonempty : Nonempty fan.cones] (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local instance closedDualSourceIntegral : IsIntegral fan.algebraicRealization :=
  toricSchemeIntegral fan nonempty

local notation "C" => IncidenceObject (fanArrangementMatrix fan basis rays)

def arrangementDualLeftCartierSources : C ⥤ CartierSources fan.algebraicRealization where
  obj c := invariantCartierDivisor fan nonempty regular
    (arrangementDualLeftCoefficients fan basis rays c)
  map f := InducedCategory.homMk
    ((arrangementDualLeftCartierDiagram fan nonempty regular basis rays).map f)
  map_id c := InducedCategory.hom_ext
    ((arrangementDualLeftCartierDiagram fan nonempty regular basis rays).map_id c)
  map_comp f g := InducedCategory.hom_ext
    ((arrangementDualLeftCartierDiagram fan nonempty regular basis rays).map_comp f g)

def arrangementDualLeftCartierSourcesQuasicoherentIso :
    arrangementDualLeftCartierSources fan regular basis rays ⋙
      cartierSourcesQuasicoherent fan.algebraicRealization ≅
        arrangementDualLeftQuasicoherentDiagram fan nonempty regular basis rays :=
  Iso.refl _

theorem arrangementDualLeftCharacter_regular {c d : C} (f : c ⟶ d) :
    ∀ ρ, 0 ≤ arrangementDualLeftCoefficients fan basis rays d ρ -
      arrangementDualLeftCoefficients fan basis rays c ρ +
        basis.equivFun.symm f.val (fanRayPrimitiveGenerator fan ρ) := by
  intro ρ
  have h := (diagonalEntryRegular_of_incidence fan basis rays f).1 ρ
  change 0 ≤ -(diagonalLeftCoefficients fan basis rays d.2 ρ) -
    -(diagonalLeftCoefficients fan basis rays c.2 ρ) +
      basis.equivFun.symm f.val (fanRayPrimitiveGenerator fan ρ)
  omega

def arrangementDualDifferenceCoefficientDiagram (b : fan.Ray → ℤ) :
    Cᵒᵖ ⥤ fan.algebraicRealization.Modules where
  obj c := (invariantCartierDivisor fan nonempty regular
    (b-arrangementDualLeftCoefficients fan basis rays c.unop)).sheaf
  map {c d} f := toricCartierMonomialMap fan nonempty regular
    (b-arrangementDualLeftCoefficients fan basis rays c.unop)
    (b-arrangementDualLeftCoefficients fan basis rays d.unop)
    (basis.equivFun.symm f.unop.val)
    (toricMonomialNonnegative_inverseTwist fan
      (arrangementDualLeftCoefficients fan basis rays d.unop)
      (arrangementDualLeftCoefficients fan basis rays c.unop) b
      (basis.equivFun.symm f.unop.val)
      (arrangementDualLeftCharacter_regular fan basis rays f.unop))
  map_id c := by
    simp only [unop_id,incidence_id_val,map_zero,toricCartierMonomialMap_id]
  map_comp f g := by
    rw [toricCartierMonomialMap_comp]
    simp only [unop_comp,incidence_comp_val,map_add]
    congr 1
    exact add_comm _ _

def arrangementDualInverseTensorCoefficientDiagram (b : fan.Ray → ℤ) :
    Cᵒᵖ ⥤ fan.algebraicRealization.Modules :=
  (arrangementDualLeftCartierSources fan regular basis rays).op ⋙
    cartierSourcesInverseTensor fan.algebraicRealization ⋙
      (evaluation fan.algebraicRealization.Modules fan.algebraicRealization.Modules).obj
        (invariantCartierDivisor fan nonempty regular b).sheaf

def arrangementDualInverseTensorCoefficientIso (b : fan.Ray → ℤ) :
    arrangementDualInverseTensorCoefficientDiagram fan regular basis rays b ≅
      arrangementDualDifferenceCoefficientDiagram fan regular basis rays b :=
  NatIso.ofComponents (fun c => invariantInverseTensorIso fan nonempty regular
    (arrangementDualLeftCoefficients fan basis rays c.unop) b) (by
      intro c d f
      exact toricCartierMonomialMap_inverseTwist fan nonempty regular
        (arrangementDualLeftCoefficients fan basis rays d.unop)
        (arrangementDualLeftCoefficients fan basis rays c.unop) b
        (basis.equivFun.symm f.unop.val)
        (arrangementDualLeftCharacter_regular fan basis rays f.unop))

end ToricPower

end
