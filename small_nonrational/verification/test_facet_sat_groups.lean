import FacetSatGroups

open Papers.RationalityTen
open FacetSat

namespace FacetSatGroupsTest

def grouped : Grouping 3 where
  count := 2
  members := fun g => if g = 0 then [0, 1, 1] else [2]
  color := fun c => c.val / 2

def compatible (a b : Fin 3) : Bool := decide (a.val / 2 ≠ b.val / 2)

-- Repeated members are harmless: a class records occupancy, not multiplicity.
example : grouped.check (fun _ => 1) compatible 1 = true := by decide +kernel

-- A class containing two compatible facets would invalidate exact counting.
example : grouped.check (fun _ => 1) (fun a b => decide (a ≠ b)) 1 = false := by
  decide +kernel

def omitted : Grouping 3 := { grouped with members := fun g => if g = 0 then [0] else [2] }

example : omitted.check (fun _ => 1) compatible 1 = false := by decide +kernel

example : grouped.check (fun c => if c = 1 then 2 else 1) compatible 1 = false := by
  decide +kernel

example (S : List (Fin 3)) :
    (1 : Fin 3) ∈ S → (grouped.selected S 0 → False) → False :=
  Grouping.group_take grouped S 0 1 (by decide)

example (S : List (Fin 3)) (ridges : Fin 3 → Fin 0 → Bool) (quota : Nat → Nat)
    (H : Boundary (fun _ => 1) compatible ridges quota S) :
    SequentialCounter.selectedCount (grouped.selected S) [0, 1] = quota 1 :=
  H.group_count grouped 1 (by decide +kernel)

#print axioms Boundary.group_count
#print axioms Grouping.group_or
#print axioms Grouping.group_take

end FacetSatGroupsTest
