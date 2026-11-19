module

public import ToricPower.CechToricDependencies
public import ToricPower.FanRayPrimitive

/-!
# Every toric chart intersection and its literal negative-ray condition

The nonempty finite intersection is formed inside the actual fan, using
binary intersections only. Every degree of the ordinary Čech complex is
therefore an actual affine chart, including when the fan is incomplete
or its cones have smaller dimension than the lattice. The availability
of a character is exactly the absence of a negative ray common to all
the selected charts.

Candidate source, pending pinned compilation.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open TauCeti.Toric
open scoped Classical

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  {Index : Type} (charts : Index → fan.cones)

/-- A nonempty tuple of fan cones has its actual intersection in the fan. -/
def toricCechCone : (degree : ℕ) → (Fin (degree + 1) → Index) → fan.cones
  | 0, tuple => charts (tuple 0)
  | degree + 1, tuple => charts (tuple 0) ⊓
      toricCechCone degree (tuple ∘ Fin.succ)

/-- The universal property of the actual finite intersection. -/
theorem le_toricCechCone_iff (cone : fan.cones) (degree : ℕ)
    (tuple : Fin (degree + 1) → Index) :
    cone ≤ toricCechCone fan charts degree tuple ↔
      ∀ column, cone ≤ charts (tuple column) := by
  induction degree with
  | zero =>
    constructor
    · intro h column
      have hzero : column = 0 := by omega
      simpa only [toricCechCone, hzero] using h
    · intro h
      exact h 0
  | succ degree induction =>
    change cone ≤ charts (tuple 0) ⊓
      toricCechCone fan charts degree (tuple ∘ Fin.succ) ↔ _
    rw [le_inf_iff, induction]
    constructor
    · rintro ⟨first, rest⟩ column
      exact Fin.cases first (fun j => rest j) column
    · intro h
      exact ⟨h 0, fun j => h j.succ⟩

theorem toricCechCone_le_chart (degree : ℕ)
    (tuple : Fin (degree + 1) → Index) (column : Fin (degree + 1)) :
    toricCechCone fan charts degree tuple ≤ charts (tuple column) :=
  (le_toricCechCone_iff fan charts _ degree tuple).mp le_rfl column

/-- Every reindexing of a tuple gives the actual inclusion between its
intersection cones, including all cofaces and codegeneracies. -/
theorem toricCechCone_le_selection {degree next : ℕ}
    (selection : Fin (degree + 1) → Fin (next + 1))
    (tuple : Fin (next + 1) → Index) :
    toricCechCone fan charts next tuple ≤
      toricCechCone fan charts degree (tuple ∘ selection) := by
  apply (le_toricCechCone_iff fan charts _ degree (tuple ∘ selection)).mpr
  intro column
  exact toricCechCone_le_chart fan charts next tuple (selection column)

abbrev toricCechChartOpen (index : Index) : fan.algebraicRealization.Opens :=
  (fan.affineToricChartι (charts index)).opensRange

theorem toricCechCone_opensRange (degree : ℕ)
    (tuple : Fin (degree + 1) → Index) :
    (fan.affineToricChartι (toricCechCone fan charts degree tuple)).opensRange =
      ⨅ column, toricCechChartOpen fan charts (tuple column) := by
  induction degree with
  | zero =>
    apply le_antisymm
    · refine le_iInf fun column => ?_
      have hzero : column = 0 := by omega
      subst column
      exact le_rfl
    · exact iInf_le _ 0
  | succ degree induction =>
    rw [toricCechCone, chart_opensRange_intersection, induction]
    apply le_antisymm
    · refine le_iInf fun column => ?_
      refine Fin.cases ?_ (fun j => ?_) column
      · exact inf_le_left
      · exact inf_le_right.trans (iInf_le _ j)
    · exact le_inf (iInf_le _ 0) (le_iInf fun j => iInf_le _ j.succ)

/-- The product of opens used by Mathlib's actual Čech complex is
exactly the open image of the intersection-cone chart. -/
theorem toricCechIntersection_eq_chart (degree : ℕ)
    (tuple : Fin (degree + 1) → Index) :
    BondalThomsen.FiniteAffineCechHigherComparison.cechIntersection
      (toricCechChartOpen fan charts) degree tuple =
    (fan.affineToricChartι (toricCechCone fan charts degree tuple)).opensRange := by
  rw [BondalThomsen.FiniteAffineCechHigherComparison.cechIntersection,
    BondalThomsen.FiniteAffineCechHigherComparison.productOpens_eq_iInf,
    toricCechCone_opensRange]
  rfl

theorem toricCechChartOpen_isAffine (index : Index) :
    IsAffineOpen (toricCechChartOpen fan charts index) :=
  isAffineOpen_opensRange _

/-- Enumerating every cone gives an actual open cover. Surjectivity is
only an interface for an enumeration, discharged by a finite equivalence. -/
theorem toricCechChartOpen_covers (surjective : Function.Surjective charts) :
    IsOpenCover (toricCechChartOpen fan charts) := by
  apply IsOpenCover.mk
  apply top_le_iff.mp
  intro point _
  obtain ⟨cone, localPoint, rfl⟩ := fan.exists_affineToricChartι_apply_eq point
  obtain ⟨index, rfl⟩ := surjective cone
  exact Opens.mem_iSup.mpr ⟨index, localPoint, rfl⟩

/-- The actual invariant divisor inequality, indexed by the fan's
intrinsic one-dimensional cones. -/
def toricCharacterAllowed (b : fan.Ray → ℤ) (cone : fan.cones) (m : N →+ ℤ) : Prop :=
  ∀ ray : fan.Ray, ray.toCone ≤ cone →
    0 ≤ b ray + m (fanRayPrimitiveGenerator fan ray)

/-- Cone-ray and global-fan-ray formulations impose exactly the same
inequalities, with the same primitive lattice generators. -/
theorem toricCharacterAllowed_iff (b : fan.Ray → ℤ) (cone : fan.cones) (m : N →+ ℤ) :
    toricCharacterAllowed fan b cone m ↔
      ∀ ray : ToricRay cone.val,
        0 ≤ coneDivisorCoefficients fan b cone ray +
          m (primitiveGenerator fan.lattice (fan.isToricCone cone.property) ray) := by
  constructor
  · intro h ray
    have bound := h (Fan.Ray.ofToricRay fan cone ray)
      (Fan.Ray.toCone_ofToricRay_le fan cone ray)
    simpa only [coneDivisorCoefficients, fanRayPrimitiveGenerator_ofToricRay] using bound
  · intro h ray included
    let localRay := Fan.Ray.toToricRay fan ray cone included
    have back : Fan.Ray.ofToricRay fan cone localRay = ray := by
      apply Subtype.ext
      apply Subtype.ext
      rfl
    have generator := fanRayPrimitiveGenerator_ofToricRay fan cone localRay
    rw [back] at generator
    have bound := h localRay
    simpa only [coneDivisorCoefficients, back, ← generator] using bound

/-- The exact supported character type is unchanged by switching ray
indices; this is a proved equivalence rather than an extra condition. -/
def toricChartWeightGlobalEquiv (b : fan.Ray → ℤ) (cone : fan.cones) :
    ToricChartDivisorWeight fan b cone ≃ {m : N →+ ℤ // toricCharacterAllowed fan b cone m} where
  toFun m := ⟨m.val, (toricCharacterAllowed_iff fan b cone m.val).mpr m.property⟩
  invFun m := ⟨m.val, (toricCharacterAllowed_iff fan b cone m.val).mp m.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Incidence here is literal containment of a ray cone in a chart cone. -/
def toricCechRayIncidence (ray : fan.Ray) (index : Index) : Prop :=
  ray.toCone ≤ charts index

def toricCharacterNegative (b : fan.Ray → ℤ) (m : N →+ ℤ) (ray : fan.Ray) : Prop :=
  b ray + m (fanRayPrimitiveGenerator fan ray) < 0

/-- A weight is present precisely when the chart tuple is not forbidden
by a ray on which the actual divisor inequality is negative. -/
theorem toricCechCharacterAllowed_iff_not_forbidden (b : fan.Ray → ℤ)
    (m : N →+ ℤ) (degree : ℕ) (tuple : Fin (degree + 1) → Index) :
    toricCharacterAllowed fan b (toricCechCone fan charts degree tuple) m ↔
      ¬ NegativeSupportCech.tupleForbidden (toricCechRayIncidence fan charts)
        (toricCharacterNegative fan b m) degree tuple := by
  constructor
  · intro h
    rintro ⟨ray, negative, incident⟩
    exact (not_lt.mpr (h ray
      ((le_toricCechCone_iff fan charts ray.toCone degree tuple).mpr incident))) negative
  · intro h ray included
    apply le_of_not_gt
    intro negative
    exact h ⟨ray, negative,
      (le_toricCechCone_iff fan charts ray.toCone degree tuple).mp included⟩

end ToricPower
