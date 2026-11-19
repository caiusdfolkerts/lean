import FacetSatEdges

open Papers.RationalityTen
open FacetSat

namespace FacetSatEdgesTest

def edgeRows (_ : Fin 1) : Nat := 5

example : EdgeCover.ownersCheck 5 ([0, 2] : List (Fin 3)) = true := by
  decide +kernel

-- Omitting a possible owner cannot justify the edge clause.
example : EdgeCover.ownersCheck 5 ([0] : List (Fin 3)) = false := by
  decide +kernel

-- Extra literals weaken a positive clause and are safe.
example : EdgeCover.ownersCheck 5 ([0, 1, 2] : List (Fin 3)) = true := by
  decide +kernel

example (S : List (Fin 3)) (H : EdgeCover 1 edgeRows S)
    (h0 : (0 : Fin 3) ∈ S → False) (h2 : (2 : Fin 3) ∈ S → False) : False := by
  apply EdgeCover.clause H 0 [0, 2] (by decide) (by decide +kernel)
  intro c hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact h0
  · rcases List.mem_cons.mp hc with rfl | hc
    · exact h2
    · exact False.elim (List.not_mem_nil hc)

#print axioms EdgeCover.of_target
#print axioms EdgeCover.clause

end FacetSatEdgesTest
