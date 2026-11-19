module
public import Papers.FiniteProjectionChecks
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs

@[expose] public section

namespace Papers.RationalityTen.ChirotopeDensity.FiniteProjection

-- The upper bit distinguishes extra polygon planes from ordinary facet planes.
def projectionPlaneKey (p : Bool × Finset (Fin 10)) : Nat :=
  (if p.1 then 1024 else 0) + p.2.sum (fun i => 2 ^ i.val)

def projectionRetainedPoints {n : Nat} {B : Boundary n}
    (priority : Node B → Nat) (p : PlaneNode B) : Finset (Fin n) :=
  Finset.univ.filter fun i => incidence i p ∧ priority (Sum.inr p) < priority (Sum.inl i)

def projectionRetainedPlanes {n : Nat} {B : Boundary n}
    (priority : Node B → Nat) (i : Fin n) : Finset (PlaneNode B) :=
  Finset.univ.filter fun p => incidence i p ∧ priority (Sum.inl i) < priority (Sum.inr p)

theorem projectionRetainedPoints_eq {n : Nat} {B : Boundary n}
    (priority : Node B → Nat) (p : PlaneNode B) :
    projectionRetainedPoints priority p = retainedPoints priority p := by
  apply Finset.ext
  intro i
  simp only [projectionRetainedPoints, retainedPoints, Finset.mem_filter, Finset.mem_univ, true_and]
  exact and_comm

theorem projectionRetainedPlanes_eq {n : Nat} {B : Boundary n}
    (priority : Node B → Nat) (i : Fin n) :
    projectionRetainedPlanes priority i = retainedPlanes priority i := by
  apply Finset.ext
  intro p
  simp only [projectionRetainedPlanes, retainedPlanes, Finset.mem_filter, Finset.mem_univ, true_and]
  exact and_comm

-- Transport the checked rules back to the existing reconstruction interface.
def projectionIncidenceOfChecks {n : Nat} (B : Boundary n) (priority : Node B → Nat)
    (hinj : Function.Injective priority)
    (hplane : ∀ p, PointRuleValid B (projectionRetainedPoints priority p))
    (hpoint : ∀ i, PlaneRuleValid B (projectionRetainedPlanes priority i)) : IncidenceCertificate B :=
  incidenceCertificateOfChecks B priority hinj
    (fun p => projectionRetainedPoints_eq priority p ▸ hplane p)
    (fun i => projectionRetainedPlanes_eq priority i ▸ hpoint i)

end Papers.RationalityTen.ChirotopeDensity.FiniteProjection
