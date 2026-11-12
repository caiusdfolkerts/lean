module

public import ToricPower.DiagonalSheafEntries
public import ToricPower.DiagonalGlobalSquare
public import ToricPower.SchemeModulesBaseLinear

/-!
# Composition of the actual global diagonal monomial entries

The regularity predicate below is precisely the ray criterion for an
actual character morphism between the two displayed Cartier factors.
Supported cellular entries satisfy it by the proved incidence inequalities.
It is closed under composing paths because their characters add.

The resulting morphisms are built using the actual Cartier maps, scheme
pullbacks and tensor product. Their multiplication law is proved from
equality in the actual rational-function sheaf on each factor.

Candidate until the pinned compiler checks the full dependency closure.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory
open TauCeti.Toric ToricPower.IntegralArrangement
open scoped Classical BigOperators

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {latticeMap : N →+ V}
  (fan : Fan latticeMap) (nonempty : Nonempty fan.cones)
  (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ))
  (rays : Fin s ≃ fan.Ray)

/-- The two literal Cartier regularity conditions for the character
pair `(a,-a)`, on every ray of the actual fan. -/
def DiagonalEntryRegular {e d : ℕ}
    (j : NormalizedCell (fanArrangementMatrix fan basis rays) e)
    (i : NormalizedCell (fanArrangementMatrix fan basis rays) d)
    (a : Fin n → ℤ) : Prop :=
  (∀ ρ, 0 ≤ diagonalLeftCoefficients fan basis rays i ρ -
      diagonalLeftCoefficients fan basis rays j ρ +
        basis.equivFun.symm a (fanRayPrimitiveGenerator fan ρ)) ∧
    ∀ ρ, 0 ≤ diagonalRightCoefficients fan basis rays i ρ -
      diagonalRightCoefficients fan basis rays j ρ -
        basis.equivFun.symm a (fanRayPrimitiveGenerator fan ρ)

theorem diagonalEntryRegular_of_globalColumn_ne_zero (d : ℕ)
    (j : NormalizedCell (fanArrangementMatrix fan basis rays) (d+1))
    (i : NormalizedCell (fanArrangementMatrix fan basis rays) d)
    (a : Fin n → ℤ)
    (h : diagonalGlobalColumn ℂ (fanArrangementMatrix fan basis rays) d j (i,a) ≠ 0) :
    DiagonalEntryRegular fan basis rays j i a := by
  let p : DiagonalGlobalColumnTerm ℂ (fanArrangementMatrix fan basis rays) d j :=
    ⟨(i,a),Finsupp.mem_support_iff.mpr h⟩
  have hp (ρ : fan.Ray) := diagonalGlobalColumnTerm_regular ℂ
    (fanArrangementMatrix fan basis rays) d j p (rays.symm ρ)
  constructor
  · intro ρ
    have hρ := (hp ρ).1
    rw [fanArrangementMatrix_character] at hρ
    unfold diagonalLeftCoefficients
    change reflectedCeiling (fanArrangementMatrix fan basis rays) i.val (rays.symm ρ) -
        reflectedCeiling (fanArrangementMatrix fan basis rays) j.val (rays.symm ρ) ≤
      basis.equivFun.symm a (fanRayPrimitiveGenerator fan ρ) at hρ
    omega
  · intro ρ
    have hρ := (hp ρ).2
    rw [fanArrangementMatrix_character] at hρ
    unfold diagonalRightCoefficients
    change i.val.val.1 (.inl (rays.symm ρ)) - j.val.val.1 (.inl (rays.symm ρ)) ≤
      -basis.equivFun.symm a (fanRayPrimitiveGenerator fan ρ) at hρ
    omega

theorem diagonalEntryRegular_comp {d e f : ℕ}
    (j : NormalizedCell (fanArrangementMatrix fan basis rays) f)
    (i : NormalizedCell (fanArrangementMatrix fan basis rays) e)
    (h : NormalizedCell (fanArrangementMatrix fan basis rays) d)
    (a b : Fin n → ℤ)
    (ha : DiagonalEntryRegular fan basis rays j i a)
    (hb : DiagonalEntryRegular fan basis rays i h b) :
    DiagonalEntryRegular fan basis rays j h (a+b) := by
  constructor
  · intro ρ
    have h₁ := ha.1 ρ
    have h₂ := hb.1 ρ
    simp only [map_add, AddMonoidHom.add_apply]
    omega
  · intro ρ
    have h₁ := ha.2 ρ
    have h₂ := hb.2 ρ
    simp only [map_add, AddMonoidHom.add_apply]
    omega

/-- The actual morphism attached to a regular character pair, for
arbitrary two labelled degrees. -/
def diagonalProductCharacterMap {e d : ℕ}
    (j : NormalizedCell (fanArrangementMatrix fan basis rays) e)
    (i : NormalizedCell (fanArrangementMatrix fan basis rays) d)
    (a : Fin n → ℤ) (ha : DiagonalEntryRegular fan basis rays j i a) :
    diagonalProductSheaf fan nonempty regular basis rays j ⟶
      diagonalProductSheaf fan nonempty regular basis rays i := by
  letI := toricSchemeIntegral fan nonempty
  exact
    (Scheme.Modules.pullback (toricDiagonalFirst fan)).map
      (toricCartierMonomialMap fan nonempty regular
        (diagonalLeftCoefficients fan basis rays j)
        (diagonalLeftCoefficients fan basis rays i)
        (basis.equivFun.symm a) ha.1) ⊗ₘ
    (Scheme.Modules.pullback (toricDiagonalSecond fan)).map
      (toricCartierMonomialMap fan nonempty regular
        (diagonalRightCoefficients fan basis rays j)
        (diagonalRightCoefficients fan basis rays i)
        (-(basis.equivFun.symm a))
        (by intro ρ; simpa only [AddMonoidHom.neg_apply, sub_eq_add_neg] using ha.2 ρ))

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Composition is proved for the actual global sheaf morphisms, not
specified as a law of a newly introduced representation. -/
theorem diagonalProductCharacterMap_comp {d e f : ℕ}
    (j : NormalizedCell (fanArrangementMatrix fan basis rays) f)
    (i : NormalizedCell (fanArrangementMatrix fan basis rays) e)
    (h : NormalizedCell (fanArrangementMatrix fan basis rays) d)
    (a b : Fin n → ℤ)
    (ha : DiagonalEntryRegular fan basis rays j i a)
    (hb : DiagonalEntryRegular fan basis rays i h b) :
    diagonalProductCharacterMap fan nonempty regular basis rays j i a ha ≫
      diagonalProductCharacterMap fan nonempty regular basis rays i h b hb =
    diagonalProductCharacterMap fan nonempty regular basis rays j h (a+b)
      (diagonalEntryRegular_comp fan basis rays j i h a b ha hb) := by
  letI := toricSchemeIntegral fan nonempty
  dsimp only [diagonalProductCharacterMap]
  rw [tensorHom_comp_tensorHom, ← Functor.map_comp, ← Functor.map_comp,
    toricCartierMonomialMap_comp, toricCartierMonomialMap_comp]
  simp only [map_add, neg_add]

/-- A total coefficient-indexed hom family. Unsupported irregular
characters contribute the actual zero map; every cellular support term
uses the genuine regular character map. -/
def diagonalProductCharacterHom {e d : ℕ}
    (j : NormalizedCell (fanArrangementMatrix fan basis rays) e)
    (i : NormalizedCell (fanArrangementMatrix fan basis rays) d)
    (a : Fin n → ℤ) :
    diagonalProductSheaf fan nonempty regular basis rays j ⟶
      diagonalProductSheaf fan nonempty regular basis rays i :=
  if ha : DiagonalEntryRegular fan basis rays j i a then
    diagonalProductCharacterMap fan nonempty regular basis rays j i a ha
  else 0

theorem diagonalProductCharacterHom_comp {d e f : ℕ}
    (j : NormalizedCell (fanArrangementMatrix fan basis rays) f)
    (i : NormalizedCell (fanArrangementMatrix fan basis rays) e)
    (h : NormalizedCell (fanArrangementMatrix fan basis rays) d)
    (a b : Fin n → ℤ)
    (ha : DiagonalEntryRegular fan basis rays j i a)
    (hb : DiagonalEntryRegular fan basis rays i h b) :
    diagonalProductCharacterHom fan nonempty regular basis rays j i a ≫
      diagonalProductCharacterHom fan nonempty regular basis rays i h b =
    diagonalProductCharacterHom fan nonempty regular basis rays j h (a+b) := by
  rw [diagonalProductCharacterHom, dif_pos ha,
    diagonalProductCharacterHom, dif_pos hb,
    diagonalProductCharacterHom,
    dif_pos (diagonalEntryRegular_comp fan basis rays j i h a b ha hb)]
  exact diagonalProductCharacterMap_comp fan nonempty regular basis rays j i h a b ha hb

theorem diagonalProductMonomialEntry_eq_characterHom (d : ℕ)
    (j : NormalizedCell (fanArrangementMatrix fan basis rays) (d+1))
    (p : DiagonalGlobalColumnTerm ℂ (fanArrangementMatrix fan basis rays) d j) :
    diagonalProductMonomialEntry fan nonempty regular basis rays d j p =
      diagonalProductCharacterHom fan nonempty regular basis rays j p.val.1 p.val.2 := by
  have h := diagonalEntryRegular_of_globalColumn_ne_zero fan basis rays d j
    p.val.1 p.val.2 (Finsupp.mem_support_iff.mp p.property)
  rw [diagonalProductCharacterHom, dif_pos h]
  rfl

end ToricPower
