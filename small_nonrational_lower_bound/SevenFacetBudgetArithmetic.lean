module
prelude
public import Init.Omega
public import Init.ByCases

@[expose] public section

/-!
# Arithmetic reductions for a distinguished seven-vertex facet

These lemmas isolate the integer arithmetic in Appendix C.3. Their hypotheses
are the geometric incidence, Euler, weight, and relation-rank identities;
the geometric application must prove every one of them. No completeness of
the facet catalogues or finite searches is asserted in this file.

Here `m` counts all facets, `N` the nonsimplicial facets, `E` the facet excess,
`q` the quadrilateral two-faces, `c` the selected relation rows, and `D` the
nonedges. The variable `r` counts quadrilaterals of the distinguished facet.
`SP`, `BP`, and `T` count square pyramids, triangular bipyramids, and tetrahedra.
-/

namespace Papers.RationalityTen.SevenFacetBudgetArithmetic

/-- No six-vertex facet: the complete numerical reduction before the 69-row
finite lookup. The upper bound `cap` will be the exceptional-template indicator. -/
theorem no_six
    (m N E q c D r eps cap SP BP T : Nat)
    (hN : 10 ≤ N) (hNm : N ≤ m) (hE : E = N + 2)
    (hc : 9 ≤ c) (hrows : c + q = E + eps)
    (heps : eps ≤ cap) (hcap : cap ≤ 1)
    (heps_small : r ≤ 2 → eps = 0)
    (heuler : m + E + D = 35 + q)
    (hweight : E + 3 ≤ D)
    (hridge : 11 ≤ m + r) (hneighbors : N + r ≤ 13)
    (hrglobal : r ≤ q)
    (hquad : SP + r = 2 * q)
    (hnonsimp : SP + BP + 1 = N)
    (hall : T + N = m) :
    E = 12 ∧ N = 10 ∧ 10 ≤ m ∧ m ≤ 12 ∧
      11 - m ≤ r ∧ r ≤ 3 ∧ r ≤ q ∧ m - 8 ≤ q ∧
      q ≤ 3 + cap ∧ r ≤ 2 * q ∧ 2 * q ≤ 9 + r ∧
      SP = 2 * q - r ∧ BP = 9 + r - 2 * q ∧ T = m - 10 := by
  have hsum : m + E ≤ 23 + eps := by omega
  have hElo : 12 ≤ E := by omega
  have hEhi : E ≤ 13 := by omega
  have hEexact : E = 12 := by
    by_cases he : E = 12
    · exact he
    · have hr : r ≤ 2 := by omega
      have hz := heps_small hr
      omega
  have hNexact : N = 10 := by omega
  omega

/-- One six-vertex facet and no pentagon: the complete reduction to the
nonpentagonal rows of the mixed seven/six catalogue. -/
theorem one_six_no_pentagon
    (m N E q c D r s eps7 eps6 cap7 cap6 SP BP T : Nat)
    (hN : 10 ≤ N) (hNm : N ≤ m) (hE : E = N + 3)
    (hc : 9 ≤ c) (hrows : c + q = E + eps7 + eps6)
    (heps7 : eps7 ≤ cap7) (hcap7 : cap7 ≤ 1)
    (heps6 : eps6 ≤ cap6) (hcap6 : cap6 ≤ 1)
    (heuler : m + E + D = 35 + q)
    (hweight : E + 4 ≤ D)
    (hridge : 11 ≤ m + r)
    (hquad : SP + r + s = 2 * q)
    (hnonsimp : SP + BP + 2 = N)
    (hall : T + N = m) :
    E = 13 ∧ N = 10 ∧ 11 - m ≤ r ∧
      ((m = 10 ∧ q = 5 ∧ 1 ≤ cap7 + cap6) ∨
        ((m = 10 ∨ m = 11) ∧ q = 6 ∧ cap7 = 1 ∧ cap6 = 1)) ∧
      r + s ≤ 2 * q ∧ 2 * q ≤ 8 + r + s ∧
      SP = 2 * q - (r + s) ∧ BP = 8 + r + s - 2 * q ∧ T = m - 10 := by
  have hsum : m + E ≤ 22 + eps7 + eps6 := by omega
  have hEexact : E = 13 := by omega
  have hNexact : N = 10 := by omega
  have hm : m = 10 ∨ m = 11 := by omega
  have hq : q = 5 ∨ q = 6 := by omega
  have hcases :
      (m = 10 ∧ q = 5 ∧ 1 ≤ cap7 + cap6) ∨
        ((m = 10 ∨ m = 11) ∧ q = 6 ∧ cap7 = 1 ∧ cap6 = 1) := by omega
  omega

/-- One six-vertex facet and a pentagon. The geometric lemmas establish
that there is exactly one pentagon and that both local relation excesses vanish. -/
theorem one_six_with_pentagon
    (m N E q c D r SP BP T : Nat)
    (hN : 10 ≤ N) (hNm : N ≤ m) (hE : E = N + 3)
    (hc : 9 ≤ c) (hrows : c + q + 2 = E)
    (heuler : m + E + D = 37 + q)
    (hweight : E + 3 ≤ D)
    (hneighbors : N + r ≤ 11)
    (hquad : SP + r = 2 * q)
    (hnonsimp : SP + BP + 2 = N)
    (hall : T + N = m) :
    m = 10 ∧ E = 13 ∧ N = 10 ∧ q = 2 ∧ r ≤ 1 ∧
      SP = 4 - r ∧ BP = 4 + r ∧ T = 0 := by
  have hsum : m + E ≤ 23 := by omega
  have hEexact : E = 13 := by omega
  have hm : m = 10 := by omega
  have hq : q = 2 := by omega
  omega

end Papers.RationalityTen.SevenFacetBudgetArithmetic
