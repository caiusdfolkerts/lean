module

public import Papers.GraphicalZonotopes.BookQuadrilateralModules

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
namespace BooleanModule
open Finset
open scoped BigOperators

variable {H : Type*} [Fintype H] [LinearOrder H]

/-- Positive integral pure module data, with the actual quotient classes and
actual monotone Boolean realizations as part of the construction. -/
structure WeightedPureBlock (C : Finset H) (M : ℤ)
    (v : ResponseQuotient H) (r : ℕ) where
  column : Fin r → PairIn C → ℝ
  realizable : ∀ j,PureRealizable C (column j)
  weight : Fin r → ℤ
  positive : ∀ j,0<weight j
  bounded : ∀ j,weight j≤M
  independent : LinearIndependent ℝ (fun j => blockClass C (column j))
  weighted_sum : (∑ j,(weight j : ℝ) • blockClass C (column j))=v

namespace WeightedStarFamily

def toPureBlock {C : Finset H} {M : ℤ} {v : ResponseQuotient H} {r : ℕ}
    (P : WeightedStarFamily C M v r) : WeightedPureBlock C M v r where
  column := fun j => (P.piece j).vector
  realizable := fun j => (P.piece j).realizable
  weight := P.weight
  positive := P.positive
  bounded := P.bounded
  independent := P.independent
  weighted_sum := P.weighted_sum

end WeightedStarFamily

namespace BalancedQuad
variable {s : ℕ}

def pureBlock (Q : BalancedQuad s) :
    WeightedPureBlock Q.clique ((s-1 : ℕ) : ℤ) (ordinaryBookTarget Q.clique) 4 where
  column := Q.column
  realizable := Q.column_realizable
  weight := Q.weight
  positive := Q.weight_positive
  bounded := Q.weight_bounded
  independent := Q.columns_independent
  weighted_sum := Q.weighted_columns_response

end BalancedQuad

theorem ordinary_book_pure_block {s : ℕ} (C : Finset (Fin s)) (hC : 3≤C.card)
    {k : ℕ} (hklo : C.card-1≤k) (hkhi : k≤C.card.choose 2-1) :
    Nonempty (WeightedPureBlock C ((s-1 : ℕ) : ℤ) (ordinaryBookTarget C) k) := by
  exact ⟨(Classical.choice (ordinary_book_block_interpolation C hC hklo hkhi)).toPureBlock⟩

end BooleanModule
end GraphicalZonotopes
