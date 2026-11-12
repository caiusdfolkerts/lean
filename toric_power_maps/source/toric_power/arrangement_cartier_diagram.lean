module

public import ToricPower.ArrangementIncidenceCeilings
public import ToricPower.DiagonalSheafComposition
public import ToricPower.CellularFoundations

/-!
# Actual Cartier labels on the translated incidence category

The incidence category is covariant from faces to cofaces. Its two
Cartier-label diagrams are contravariant: the incidence with translation
`a` gives the actual character maps `χ^a` for `L(-x)` and `χ^(-a)` for
`L(x)`. Their composition laws are proved using actual multiplication of
rational characters. Pullback to the actual toric product and tensoring
gives the actual diagonal-kernel diagram.

The final detection statement uses the genuine derived category of
complexes of module diagrams. No equivalence with sheaves on a torus, or
with coherent sheaves, is asserted or assumed here.

Candidate source pending checking by the pinned Lean compiler.
-/

@[expose] public noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TauCeti.Toric ToricPower.IntegralArrangement
open scoped Classical


namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {latticeMap : N →+ V}
  (fan : Fan latticeMap) (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "C" => IncidenceObject A

/-- Every literal translated incidence defines both actual Cartier
character maps on the whole fan. -/
theorem diagonalEntryRegular_of_incidence {c d : C} (f : c ⟶ d) :
    DiagonalEntryRegular fan basis rays d.2 c.2 f.val := by
  constructor
  · intro ρ
    have h := (incidence_ceiling_bounds A f (rays.symm ρ)).1
    rw [fanArrangementMatrix_character] at h
    unfold diagonalLeftCoefficients
    omega
  · intro ρ
    have h := (incidence_ceiling_bounds A f (rays.symm ρ)).2
    rw [fanArrangementMatrix_character] at h
    unfold diagonalRightCoefficients
    omega

/-- The actual reflected Cartier label, contravariant on every
translated incidence. -/
def arrangementLeftCartierDiagram : Cᵒᵖ ⥤ fan.algebraicRealization.Modules where
  obj c := diagonalLeftSheaf fan nonempty regular basis rays c.unop.2
  map {c d} f := by
    letI := toricSchemeIntegral fan nonempty
    exact toricCartierMonomialMap fan nonempty regular
      (diagonalLeftCoefficients fan basis rays c.unop.2)
      (diagonalLeftCoefficients fan basis rays d.unop.2)
      (basis.equivFun.symm f.unop.val)
      (diagonalEntryRegular_of_incidence fan basis rays f.unop).1
  map_id c := by
    letI := toricSchemeIntegral fan nonempty
    simp only [unop_id, incidence_id_val, map_zero, toricCartierMonomialMap_id]
    rfl
  map_comp f g := by
    letI := toricSchemeIntegral fan nonempty
    rw [toricCartierMonomialMap_comp]
    simp only [unop_comp, incidence_comp_val, map_add, add_comm]

/-- The actual unreflected Cartier label `L(x)`, with the opposite
character on each incidence. This is the unshifted line-bundle part of
the paper's contravariant kernel `P`. -/
def arrangementRightCartierDiagram : Cᵒᵖ ⥤ fan.algebraicRealization.Modules where
  obj c := diagonalRightSheaf fan nonempty regular basis rays c.unop.2
  map {c d} f := by
    letI := toricSchemeIntegral fan nonempty
    exact toricCartierMonomialMap fan nonempty regular
      (diagonalRightCoefficients fan basis rays c.unop.2)
      (diagonalRightCoefficients fan basis rays d.unop.2)
      (-(basis.equivFun.symm f.unop.val))
      (by intro ρ
          simpa only [AddMonoidHom.neg_apply, sub_eq_add_neg] using
            (diagonalEntryRegular_of_incidence fan basis rays f.unop).2 ρ)
  map_id c := by
    letI := toricSchemeIntegral fan nonempty
    simp only [unop_id, incidence_id_val, map_zero, neg_zero,
      toricCartierMonomialMap_id]
    rfl
  map_comp f g := by
    letI := toricSchemeIntegral fan nonempty
    rw [toricCartierMonomialMap_comp]
    simp only [unop_comp, incidence_comp_val, map_add, neg_add, add_comm]

/-- The actual diagonal-kernel label diagram on the actual product
scheme. Its functoriality retains the actual maps of both factors. -/
def arrangementDiagonalKernelDiagram : Cᵒᵖ ⥤ (toricDiagonalProduct fan).Modules where
  obj c := diagonalProductSheaf fan nonempty regular basis rays c.unop.2
  map f :=
    (Scheme.Modules.pullback (toricDiagonalFirst fan)).map
      ((arrangementLeftCartierDiagram fan nonempty regular basis rays).map f) ⊗ₘ
    (Scheme.Modules.pullback (toricDiagonalSecond fan)).map
      ((arrangementRightCartierDiagram fan nonempty regular basis rays).map f)
  map_id c := by
    change
      (Scheme.Modules.pullback (toricDiagonalFirst fan)).map
          ((arrangementLeftCartierDiagram fan nonempty regular basis rays).map (𝟙 c)) ⊗ₘ
        (Scheme.Modules.pullback (toricDiagonalSecond fan)).map
          ((arrangementRightCartierDiagram fan nonempty regular basis rays).map (𝟙 c)) =
      𝟙 (((Scheme.Modules.pullback (toricDiagonalFirst fan)).obj
          ((arrangementLeftCartierDiagram fan nonempty regular basis rays).obj c)) ⊗
        ((Scheme.Modules.pullback (toricDiagonalSecond fan)).obj
          ((arrangementRightCartierDiagram fan nonempty regular basis rays).obj c)))
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
      CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id,
      id_tensorHom_id]
  map_comp f g := by
    simp only [Functor.map_comp, tensorHom_comp_tensorHom]

/-- Each morphism of the kernel diagram is exactly the monomial map
used in the actual global diagonal resolution. -/
theorem arrangementDiagonalKernelDiagram_map {c d : C} (f : c ⟶ d) :
    (arrangementDiagonalKernelDiagram fan nonempty regular basis rays).map f.op =
      diagonalProductCharacterMap fan nonempty regular basis rays d.2 c.2 f.val
        (diagonalEntryRegular_of_incidence fan basis rays f) := by
  rfl

/-- The actual abelian category of covariant module diagrams on the
finite translated incidence category. -/
abbrev ArrangementModules := C ⥤ ModuleCat ℂ

/-- The actual unbounded derived category of those diagrams. Complexes
are formed before localization, preserving their higher coherence. -/
abbrev ArrangementDerived [HasDerivedCategory (ArrangementModules fan basis rays)] :=
  DerivedCategory (ArrangementModules fan basis rays)

/-- The genuine representable diagram retains all incidence copies in
each free module, including distinct face maps with the same endpoints. -/
def arrangementRepresentable (c : C) : ArrangementModules fan basis rays :=
  Cellular.representable ℂ c

instance arrangementRepresentable_projective (c : C) :
    Projective (arrangementRepresentable fan basis rays c) :=
  inferInstanceAs (Projective (Cellular.representable ℂ c))

/-- Literal shifted representables detect every nonzero object of the
actual unbounded derived diagram category. This is a derived-module
statement, with no assumed correspondence to toric coherent sheaves. -/
theorem arrangementDerived_isZero_iff
    [HasDerivedCategory (ArrangementModules fan basis rays)]
    (E : ArrangementDerived fan basis rays) :
    IsZero E ↔ ∀ (c : C) (d : ℤ), ∀ φ :
      ((DerivedCategory.singleFunctor (ArrangementModules fan basis rays) 0).obj
        (arrangementRepresentable fan basis rays c))⟦d⟧ ⟶ E, φ = 0 :=
  Cellular.isZero_iff_shifted_representable_maps_zero ℂ E

end ToricPower

end
