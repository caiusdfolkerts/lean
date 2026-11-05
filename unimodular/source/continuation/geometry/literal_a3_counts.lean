module

public import Recovery.Unimodular.PriorExtensions.LiteralA3Projectivity
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.Data.Fintype.Card

/-!
# The complementary count in the literal A3 lattice

The objects are all labelled complete fans on the twelve roots in the
integral zero-sum lattice. The complement is taken inside that entire
geometric fan type, using the actual polytope-normal-fan predicate.

Source candidate only: native compilation and the final axiom audit are pending.
-/

set_option autoImplicit false

@[expose] public noncomputable section

namespace Unimodular.LiteralA3Projectivity

open LiteralRootCoordinates NormalFanSupport

/-- Exactly 126 of the 729 literal labelled complete root fans are
nonprojective. This is the finite complement of the proved 603 projective
fans, not a count of a selected list of sign patterns. -/
theorem literal_nonprojective_fan_count :
    Nat.card {Φ : LiteralCompleteRootFan // ¬HasPolytopeNormalFan Φ.val} = 126 := by
  classical
  letI : Finite LiteralCompleteRootFan := Nat.finite_of_card_ne_zero (by
    change Nat.card {Φ : TauCeti.Toric.Fan (rootEmbedding 3) //
      Φ.IsComplete ∧ HasLiteralRays Φ} ≠ 0
    rw [a3_literal_complete_fan_count]
    decide)
  letI : Fintype LiteralCompleteRootFan := Fintype.ofFinite _
  have htotal : Fintype.card LiteralCompleteRootFan = 729 := by
    simpa only [Nat.card_eq_fintype_card] using a3_literal_complete_fan_count
  have hprojective :
      Fintype.card {Φ : LiteralCompleteRootFan // HasPolytopeNormalFan Φ.val} = 603 := by
    simpa only [Nat.card_eq_fintype_card] using literal_projective_fan_count
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
    htotal, hprojective]

/-- The same complement count when projectivity requires an actual
integral dual-lattice normal polytope. -/
theorem literal_non_lattice_projective_fan_count :
    Nat.card {Φ : LiteralCompleteRootFan // ¬HasIntegralNormalFan Φ.val} = 126 := by
  have h : (fun Φ : LiteralCompleteRootFan => ¬HasIntegralNormalFan Φ.val) =
      (fun Φ : LiteralCompleteRootFan => ¬HasPolytopeNormalFan Φ.val) := by
    funext Φ
    exact propext (not_congr (literal_normalFan_iff_integral Φ).symm)
  rw [h]
  exact literal_nonprojective_fan_count

end Unimodular.LiteralA3Projectivity

#print axioms Unimodular.LiteralA3Projectivity.literal_nonprojective_fan_count
#print axioms Unimodular.LiteralA3Projectivity.literal_non_lattice_projective_fan_count
