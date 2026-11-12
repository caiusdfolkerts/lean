module

public import ToricPower.DivisorWeightMonomialMaps

/-!
# Cartier coefficients and actual character morphisms

This small category records a divisor coefficient at every ray and the
literal character of a regular monomial map.  Its realization is the
actual invariant Cartier sheaf; composition is multiplication of rational
characters.  Factoring diagrams through this category separates elementary
integer identities from the large sheaf constructions they realize.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory TauCeti.Toric

namespace ToricPower.ToricMonomial

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)

@[ext]
structure Object where
  coefficients : fan.Ray → ℤ

def Hom (b c : Object fan) :=
  {a : N →+ ℤ // ∀ ρ, 0 ≤ c.coefficients ρ - b.coefficients ρ +
    a (fanRayPrimitiveGenerator fan ρ)}

instance : Category (Object fan) where
  Hom := Hom fan
  id b := ⟨0, by intro ρ; simp⟩
  comp {a b c} f g := ⟨f.val + g.val, by
    intro ρ
    have hf := f.property ρ
    have hg := g.property ρ
    simp only [AddMonoidHom.add_apply]
    omega⟩
  id_comp f := Subtype.ext (zero_add _)
  comp_id f := Subtype.ext (add_zero _)
  assoc f g h := Subtype.ext (add_assoc _ _ _)

@[ext]
theorem hom_ext {b c : Object fan} {f g : b ⟶ c} (h : f.val = g.val) : f = g :=
  Subtype.ext h

/-- Equal coefficients are identified by the actual unit character. -/
def coefficientIso (b c : Object fan) (h : b.coefficients = c.coefficients) : b ≅ c where
  hom := ⟨0, by intro ρ; simp [h]⟩
  inv := ⟨0, by intro ρ; simp [h]⟩
  hom_inv_id := Subtype.ext (add_zero 0)
  inv_hom_id := Subtype.ext (add_zero 0)

/-- Realization retains the exact divisor and the exact character map. -/
def realization (nonempty : Nonempty fan.cones) (regular : fan.IsRegular) :
    Object fan ⥤ fan.algebraicRealization.Modules := by
  letI := toricSchemeIntegral fan nonempty
  exact {
    obj := fun b => (invariantCartierDivisor fan nonempty regular b.coefficients).sheaf
    map := fun {b c} f => toricCartierMonomialMap fan nonempty regular
      b.coefficients c.coefficients f.val f.property
    map_id := fun b => toricCartierMonomialMap_id fan nonempty regular b.coefficients
    map_comp := fun f g => (toricCartierMonomialMap_comp fan nonempty regular
      _ _ _ f.val g.val f.property g.property).symm }

end ToricPower.ToricMonomial

end
