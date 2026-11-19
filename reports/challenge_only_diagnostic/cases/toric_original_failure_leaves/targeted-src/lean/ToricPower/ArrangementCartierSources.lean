module

public import ToricPower.CartierSourceFunctor
public import ToricPower.ArrangementQuasicoherentLabels
public import ToricPower.ToricInverseCartierTensor
public import ToricPower.CechToricMonomialComplex

/-!
# Actual arrangement Cartier sources and difference-coefficient Čech diagrams

The right label is a functor to actual Cartier sources, and its
quasicoherent realization is the previously defined label functor.
Inverse tensoring a coefficient line `O(d)` gives the literal sheaves
`O(d-right(c))`. Every translated incidence acts by the actual character
`χ^(-a)`. The comparison retains complete Čech complexes and every
incidence arrow; its Laurent map translates the full character by `-a`.
-/

@[expose] public noncomputable section
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 600000

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TauCeti.Toric TauCeti.AlgebraicGeometry.Scheme
open ToricPower.IntegralArrangement
open BondalThomsen.FiniteAffineCechHigherComparison

namespace ToricPower

def conjugateFunctorObjects {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (G : C → D) (e : ∀ c, F.obj c ≅ G c) : C ⥤ D where
  obj := G
  map {c d} f := (e c).inv ≫ F.map f ≫ (e d).hom
  map_id c := by simp only [F.map_id, Category.id_comp, Iso.inv_hom_id]
  map_comp f g := by simp only [F.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

def conjugateFunctorObjectsIso {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) (G : C → D) (e : ∀ c, F.obj c ≅ G c) :
    F ≅ conjugateFunctorObjects F G e :=
  NatIso.ofComponents e (by
    intro c d f
    simp only [conjugateFunctorObjects, Iso.hom_inv_id_assoc])

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}
  (fan : Fan i) [nonempty : Nonempty fan.cones] (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "C" => IncidenceObject A
local instance arrangementSourceIntegral : IsIntegral fan.algebraicRealization :=
  toricSchemeIntegral fan nonempty

/-- The right label with its actual Cartier divisor retained as data. -/
def arrangementRightCartierSources : Cᵒᵖ ⥤ CartierSources fan.algebraicRealization where
  obj c := invariantCartierDivisor fan nonempty regular
    (diagonalRightCoefficients fan basis rays c.unop.2)
  map f := InducedCategory.homMk
    ((arrangementRightCartierDiagram fan nonempty regular basis rays).map f)
  map_id c := InducedCategory.hom_ext
    ((arrangementRightCartierDiagram fan nonempty regular basis rays).map_id c)
  map_comp f g := InducedCategory.hom_ext
    ((arrangementRightCartierDiagram fan nonempty regular basis rays).map_comp f g)

/-- The adapter has exactly the original actual quasicoherent label
functor, on objects and every morphism. -/
def arrangementRightCartierSourcesQuasicoherentIso :
    arrangementRightCartierSources fan regular basis rays ⋙
        cartierSourcesQuasicoherent fan.algebraicRealization ≅
      arrangementRightQuasicoherentDiagram fan nonempty regular basis rays := Iso.refl _

omit nonempty in
/-- Every right-label incidence is regular with its specified negative
character, including wall incidences and repeated endpoints. -/
theorem arrangementRightCharacter_regular {c e : C} (f : c ⟶ e) :
    ∀ ρ, 0 ≤ diagonalRightCoefficients fan basis rays c.2 ρ -
      diagonalRightCoefficients fan basis rays e.2 ρ +
        (-(basis.equivFun.symm f.val)) (fanRayPrimitiveGenerator fan ρ) := by
  intro ρ
  simpa only [AddMonoidHom.neg_apply, sub_eq_add_neg] using
    (diagonalEntryRegular_of_incidence fan basis rays f).2 ρ

/-- The literal difference-coefficient sheaf diagram at the actual
coefficient line `O(d)`. -/
def arrangementDifferenceCoefficientDiagram (d : fan.Ray → ℤ) :
    C ⥤ fan.algebraicRealization.Modules where
  obj c := (invariantCartierDivisor fan nonempty regular
    (d - diagonalRightCoefficients fan basis rays c.2)).sheaf
  map {c e} f := toricCartierMonomialMap fan nonempty regular
    (d - diagonalRightCoefficients fan basis rays c.2)
    (d - diagonalRightCoefficients fan basis rays e.2)
    (-(basis.equivFun.symm f.val))
    (toricMonomialNonnegative_inverseTwist fan
      (diagonalRightCoefficients fan basis rays e.2)
      (diagonalRightCoefficients fan basis rays c.2) d
      (-(basis.equivFun.symm f.val)) (arrangementRightCharacter_regular fan basis rays f))
  map_id c := by
    simp only [incidence_id_val, map_zero, neg_zero, toricCartierMonomialMap_id]
  map_comp f g := by
    rw [toricCartierMonomialMap_comp]
    simp only [incidence_comp_val, map_add, neg_add]

/-- The actual inverse-adjunction-mate diagram evaluated at `O(d)`. -/
def arrangementInverseTensorCoefficientDiagram (d : fan.Ray → ℤ) :
    C ⥤ fan.algebraicRealization.Modules :=
  (arrangementRightCartierSources fan regular basis rays).rightOp ⋙
    cartierSourcesInverseTensor fan.algebraicRealization ⋙
      (evaluation fan.algebraicRealization.Modules fan.algebraicRealization.Modules).obj
        (invariantCartierDivisor fan nonempty regular d).sheaf

/-- Actual Cartier multiplication gives a natural isomorphism of the
whole incidence diagrams, with the mate computed as the literal character. -/
def arrangementInverseTensorCoefficientIso (d : fan.Ray → ℤ) :
    arrangementInverseTensorCoefficientDiagram fan regular basis rays d ≅
      arrangementDifferenceCoefficientDiagram fan regular basis rays d :=
  NatIso.ofComponents (fun c => invariantInverseTensorIso fan nonempty regular
    (diagonalRightCoefficients fan basis rays c.2) d) (by
      intro c e f
      exact toricCartierMonomialMap_inverseTwist fan nonempty regular
        (diagonalRightCoefficients fan basis rays e.2)
        (diagonalRightCoefficients fan basis rays c.2) d
        (-(basis.equivFun.symm f.val)) (arrangementRightCharacter_regular fan basis rays f))

variable {Index : Type} (charts : Index → fan.cones)

/-- Complete actual Čech complexes for all the difference-coefficient
lines, as a genuine incidence functor. -/
def arrangementDifferenceCechDiagram (d : fan.Ray → ℤ) :
    C ⥤ CochainComplex AddCommGrpCat ℕ :=
  arrangementDifferenceCoefficientDiagram fan regular basis rays d ⋙
    schemeCechComplexFunctor (toricCechChartOpen fan charts)

/-- The same complete complexes in full Laurent coordinates. The map
formula below computes the conjugated map independently. -/
def arrangementDifferenceLaurentDiagram (d : fan.Ray → ℤ) :
    C ⥤ CochainComplex AddCommGrpCat ℕ :=
  conjugateFunctorObjects
    (arrangementDifferenceCechDiagram fan regular basis rays charts d)
    (fun c => toricCechLaurentComplex fan charts
      (d - diagonalRightCoefficients fan basis rays c.2))
    (fun c => toricCechLaurentComplexIso fan charts
      (d - diagonalRightCoefficients fan basis rays c.2) nonempty regular)

/-- A genuine natural isomorphism of complete Čech complex diagrams. -/
def arrangementDifferenceCechLaurentIso (d : fan.Ray → ℤ) :
    arrangementDifferenceCechDiagram fan regular basis rays charts d ≅
      arrangementDifferenceLaurentDiagram fan regular basis rays charts d :=
  conjugateFunctorObjectsIso _ _ _

/-- Every actual incidence translates the whole Laurent character by
its negative translation vector and preserves every complex coefficient. -/
theorem arrangementDifferenceLaurentDiagram_map_coefficients (d : fan.Ray → ℤ)
    {c e : C} (f : c ⟶ e) (q : ℕ) (tuple : Fin (q+1) → Index)
    (p : ((arrangementDifferenceLaurentDiagram fan regular basis rays charts d).obj c).X q) :
    (Limits.Pi.π (toricCechLaurentCoefficient fan charts
      (d - diagonalRightCoefficients fan basis rays e.2) q) tuple
      (((arrangementDifferenceLaurentDiagram fan regular basis rays charts d).map f).f q p)).val =
    Finsupp.mapDomain (fun m : N →+ ℤ => -(basis.equivFun.symm f.val) + m)
      (Limits.Pi.π (toricCechLaurentCoefficient fan charts
        (d - diagonalRightCoefficients fan basis rays c.2) q) tuple p).val :=
  toricCechLaurentMonomialMap_coefficients fan charts nonempty regular
    (d - diagonalRightCoefficients fan basis rays c.2)
    (d - diagonalRightCoefficients fan basis rays e.2)
    (-(basis.equivFun.symm f.val))
    (toricMonomialNonnegative_inverseTwist fan
      (diagonalRightCoefficients fan basis rays e.2)
      (diagonalRightCoefficients fan basis rays c.2) d
      (-(basis.equivFun.symm f.val)) (arrangementRightCharacter_regular fan basis rays f)) q tuple p

end ToricPower
