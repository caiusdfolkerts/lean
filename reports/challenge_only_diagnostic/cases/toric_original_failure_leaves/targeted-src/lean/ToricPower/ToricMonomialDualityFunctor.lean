module

public import ToricPower.ToricMonomialCategory
public import ToricPower.ToricCartierMonomialDuality
public import ToricPower.CartierSourceFunctor

/-!
# Inverse Cartier tensoring as a functor of monomial labels

Duality negates divisor coefficients and reverses arrows, while keeping
the actual rational character multiplier. This agrees naturally with
the mates of the Cartier tensor adjunctions, including for arbitrary
quasicoherent coefficient sheaves.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory MonoidalCategory Opposite TauCeti.Toric
open TauCeti.AlgebraicGeometry.Scheme

namespace ToricPower.ToricMonomial

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)

/-- The same-character contravariant dual of the actual coefficient category. -/
def dual : (Object fan)ᵒᵖ ⥤ Object fan where
  obj b := ⟨-b.unop.coefficients⟩
  map f := ⟨f.unop.val,
    toricMonomialNonnegative_dual fan _ _ f.unop.val f.unop.property⟩
  map_id b := Subtype.ext rfl
  map_comp f g := Subtype.ext (add_comm _ _)

variable (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)

local notation "X" => fan.algebraicRealization
local notation "Q" => QCoh X

/-- Retain the actual invariant Cartier divisor as the source label. -/
def sources : letI := toricSchemeIntegral fan nonempty
    Object fan ⥤ CartierSources X := by
  letI := toricSchemeIntegral fan nonempty
  exact
    { obj b := invariantCartierDivisor fan nonempty regular b.coefficients
      map f := InducedCategory.homMk ((realization fan nonempty regular).map f)
      map_id b := InducedCategory.hom_ext ((realization fan nonempty regular).map_id b)
      map_comp f g := InducedCategory.hom_ext ((realization fan nonempty regular).map_comp f g) }

/-- Realization in the actual category of quasicoherent sheaves. -/
def quasicoherent : Object fan ⥤ Q := by
  letI := toricSchemeIntegral fan nonempty
  exact sources fan nonempty regular ⋙ cartierSourcesQuasicoherent X

/-- The canonical identification of an inverse divisor with negated coefficients. -/
def inverseCoefficientIso (b : fan.Ray → ℤ) :
    letI := toricSchemeIntegral fan nonempty
    (-(invariantCartierDivisor fan nonempty regular b)).sheaf ≅
      (invariantCartierDivisor fan nonempty regular (-b)).sheaf := by
  letI := toricSchemeIntegral fan nonempty
  exact (eqToIso (congrArg CartierDivisor.sheaf
    (invariantCartierDivisor_neg fan nonempty regular b))).symm

@[reassoc]
theorem dualMap_inverseCoefficientIso (b c : fan.Ray → ℤ) (a : N →+ ℤ)
    (ha : ∀ ρ, 0 ≤ c ρ - b ρ + a (fanRayPrimitiveGenerator fan ρ)) :
    letI := toricSchemeIntegral fan nonempty
    toricCartierMonomialDualMap fan nonempty regular b c a ha ≫
        (inverseCoefficientIso fan nonempty regular b).hom =
      (inverseCoefficientIso fan nonempty regular c).hom ≫
        toricCartierMonomialMap fan nonempty regular (-c) (-b) a
          (toricMonomialNonnegative_dual fan b c a ha) := by
  letI := toricSchemeIntegral fan nonempty
  change ((inverseCoefficientIso fan nonempty regular c).hom ≫
      toricCartierMonomialMap fan nonempty regular (-c) (-b) a
        (toricMonomialNonnegative_dual fan b c a ha) ≫
      (inverseCoefficientIso fan nonempty regular b).inv) ≫
      (inverseCoefficientIso fan nonempty regular b).hom = _
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- All actual inverse-adjunction mates are the same-character dual
monomial maps, naturally as endofunctors on module sheaves. -/
def inverseTensorIso :
    letI := toricSchemeIntegral fan nonempty
    (sources fan nonempty regular).op ⋙ cartierSourcesInverseTensor X ≅
      dual fan ⋙ realization fan nonempty regular ⋙ tensoringLeft (Scheme.Modules X) := by
  letI := toricSchemeIntegral fan nonempty
  exact NatIso.ofComponents
    (fun b => (tensoringLeft (Scheme.Modules X)).mapIso
      (inverseCoefficientIso fan nonempty regular b.unop.coefficients)) (by
        intro b c f
        change cartierDualTwistMap X
            (toricCartierMonomialMap fan nonempty regular
              c.unop.coefficients b.unop.coefficients f.unop.val f.unop.property) ≫
            (tensoringLeft (Scheme.Modules X)).map
              (inverseCoefficientIso fan nonempty regular c.unop.coefficients).hom =
          (tensoringLeft (Scheme.Modules X)).map
              (inverseCoefficientIso fan nonempty regular b.unop.coefficients).hom ≫
            (tensoringLeft (Scheme.Modules X)).map
              (toricCartierMonomialMap fan nonempty regular
                (-b.unop.coefficients) (-c.unop.coefficients) f.unop.val _)
        rw [toricCartierMonomialMap_dualTwist,
          ← Functor.map_comp, ← Functor.map_comp]
        exact congrArg (tensoringLeft (Scheme.Modules X)).map
          (dualMap_inverseCoefficientIso fan nonempty regular
            c.unop.coefficients b.unop.coefficients f.unop.val f.unop.property))

/-- Restriction of the same natural comparison to arbitrary
quasicoherent coefficients. -/
def inverseTensorQuasicoherentIso :
    letI := toricSchemeIntegral fan nonempty
    (sources fan nonempty regular).op ⋙ cartierSourcesQuasicoherentInverseTensor X ≅
      dual fan ⋙ quasicoherent fan nonempty regular ⋙ tensoringLeft Q := by
  letI := toricSchemeIntegral fan nonempty
  exact NatIso.ofComponents (fun b => NatIso.ofComponents
    (fun M => ObjectProperty.isoMk _
      (((inverseTensorIso fan nonempty regular).app b).app M.obj)) (by
        intro M M' g
        apply ObjectProperty.hom_ext
        exact ((inverseTensorIso fan nonempty regular).app b).hom.naturality g.hom)) (by
          intro b c f
          apply NatTrans.ext
          funext M
          apply ObjectProperty.hom_ext
          exact congrArg (fun α => α.app M.obj)
            ((inverseTensorIso fan nonempty regular).hom.naturality f))

end ToricPower.ToricMonomial

end
