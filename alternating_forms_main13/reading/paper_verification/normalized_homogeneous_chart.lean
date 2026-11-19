module

public import TauCeti.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.Algebra.Group.Units.Hom

/-!
# Normalized homogeneous charts on arbitrary coefficient algebras

The points here have values in every commutative algebra, including rings
with nilpotents. A homogeneous equation is evaluated literally; its zero
locus is never replaced by its radical or by field-valued points. On the
overlap where a second coordinate is a unit, rescaling by that unit gives
the other normalized chart. The inverse, naturality under algebra maps,
and the three-chart cocycle are proved from actual coordinate identities.

This is the functor-of-points overlap construction. Identifying these
functors with particular quotient/localization algebras, and identifying
those algebras with row-isotropy charts, are separate obligations.
This new source candidate has not yet been compiled.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.NormalizedHomogeneousChart

universe u v w uA uB
variable {K : Type u} [CommRing K] {ι : Type v} {η : Type w}

/-- Literal homogeneous equations, with their proved degrees. -/
structure System (K : Type u) [CommRing K] (ι : Type v) (η : Type w) where
  degree : η → ℕ
  equation : η → MvPolynomial ι K
  homogeneous : ∀ j, (equation j).IsHomogeneous (degree j)

variable (E : System K ι η)

/-- An arbitrary-algebra point satisfying the original equations and the
literal normalization `x_p = 1`. -/
structure ChartPoint (p : ι) (A : Type uA) [CommRing A] [Algebra K A] where
  coordinate : ι → A
  normalized : coordinate p = 1
  vanishes : ∀ j, MvPolynomial.aeval coordinate (E.equation j) = 0

namespace ChartPoint

variable {E} {p : ι} {A : Type uA} [CommRing A] [Algebra K A]

@[ext] theorem ext {x y : ChartPoint E p A}
    (h : ∀ i, x.coordinate i = y.coordinate i) : x = y := by
  have hc : x.coordinate = y.coordinate := funext h
  cases x
  cases y
  cases hc
  rfl

/-- Every algebra homomorphism acts on the actual coordinates and equations. -/
def map {B : Type uB} [CommRing B] [Algebra K B] (φ : A →ₐ[K] B)
    (x : ChartPoint E p A) : ChartPoint E p B where
  coordinate i := φ (x.coordinate i)
  normalized := by rw [x.normalized, map_one]
  vanishes j := by
    rw [← MvPolynomial.comp_aeval_apply, x.vanishes, map_zero]

@[simp] theorem map_coordinate {B : Type uB} [CommRing B] [Algebra K B]
    (φ : A →ₐ[K] B) (x : ChartPoint E p A) (i : ι) :
    (x.map φ).coordinate i = φ (x.coordinate i) := rfl

@[simp] theorem map_id (x : ChartPoint E p A) : x.map (AlgHom.id K A) = x := by
  ext i
  rfl

@[simp] theorem map_comp {B : Type uB} [CommRing B] [Algebra K B]
    {D : Type*} [CommRing D] [Algebra K D]
    (φ : A →ₐ[K] B) (ψ : B →ₐ[K] D) (x : ChartPoint E p A) :
    (x.map φ).map ψ = x.map (ψ.comp φ) := by
  ext i
  rfl

end ChartPoint

/-- The overlap remembers the unique unit whose value is the other pivot.
The unit is data only to give a literal denominator in every algebra. -/
structure Overlap (p q : ι) (A : Type uA) [CommRing A] [Algebra K A]
    extends ChartPoint E p A where
  pivot : Aˣ
  pivot_eq : (pivot : A) = coordinate q

namespace Overlap

variable {E} {p q : ι} {A : Type uA} [CommRing A] [Algebra K A]

@[ext] theorem ext {x y : Overlap E p q A}
    (h : ∀ i, x.coordinate i = y.coordinate i) : x = y := by
  have hp : x.toChartPoint = y.toChartPoint := ChartPoint.ext h
  cases x with
  | mk x u hu =>
    cases y with
    | mk y v hv =>
      cases hp
      have huv : u = v := Units.ext (hu.trans hv.symm)
      cases huv
      rfl

/-- Change to the other normalized chart by dividing every coordinate by
its actual unit-valued pivot. -/
def transition (x : Overlap E p q A) : Overlap E q p A where
  coordinate i := (↑x.pivot⁻¹ : A) * x.coordinate i
  normalized := by rw [← x.pivot_eq]; simp
  vanishes j := by
    change MvPolynomial.eval₂ (algebraMap K A)
      (fun i => (↑x.pivot⁻¹ : A) * x.coordinate i) (E.equation j) = 0
    rw [(E.homogeneous j).eval₂_const_mul]
    change (↑x.pivot⁻¹ : A) ^ E.degree j *
      MvPolynomial.aeval x.coordinate (E.equation j) = 0
    rw [x.vanishes, mul_zero]
  pivot := x.pivot⁻¹
  pivot_eq := by rw [x.normalized, mul_one]

@[simp] theorem transition_coordinate (x : Overlap E p q A) (i : ι) :
    x.transition.coordinate i = (↑x.pivot⁻¹ : A) * x.coordinate i := rfl

@[simp] theorem transition_pivot (x : Overlap E p q A) :
    x.transition.pivot = x.pivot⁻¹ := rfl

@[simp] theorem transition_transition (x : Overlap E p q A) :
    x.transition.transition = x := by
  ext i
  simp only [transition_coordinate, transition_pivot, inv_inv, ← mul_assoc]
  simp

/-- The complete normalized overlap equivalence, without a reducedness or
field hypothesis. -/
def transitionEquiv : Overlap E p q A ≃ Overlap E q p A where
  toFun := transition
  invFun := transition
  left_inv := transition_transition
  right_inv := transition_transition

/-- The overlap functor acts on units by the actual induced unit homomorphism. -/
def map {B : Type uB} [CommRing B] [Algebra K B] (φ : A →ₐ[K] B)
    (x : Overlap E p q A) : Overlap E p q B where
  toChartPoint := x.toChartPoint.map φ
  pivot := Units.map (φ : A →* B) x.pivot
  pivot_eq := by
    simpa only [Units.coe_map, AlgHom.coe_toMonoidHom, ChartPoint.map_coordinate]
      using congrArg φ x.pivot_eq

@[simp] theorem map_coordinate {B : Type uB} [CommRing B] [Algebra K B]
    (φ : A →ₐ[K] B) (x : Overlap E p q A) (i : ι) :
    (x.map φ).coordinate i = φ (x.coordinate i) := rfl

/-- The chart change commutes with every algebra homomorphism, so it is an
isomorphism of the full algebra-valued point functors. -/
theorem transition_natural {B : Type uB} [CommRing B] [Algebra K B]
    (φ : A →ₐ[K] B) (x : Overlap E p q A) :
    (Overlap.map φ x).transition = Overlap.map φ x.transition := by
  ext i
  change (↑(Units.map (φ : A →* B) x.pivot)⁻¹ : B) * φ (x.coordinate i) =
    φ ((↑x.pivot⁻¹ : A) * x.coordinate i)
  simp only [Units.coe_map_inv, AlgHom.coe_toMonoidHom, map_mul]

end Overlap

/-- An actual point on the common overlap of three normalized charts. -/
structure TripleOverlap (p q r : ι) (A : Type uA) [CommRing A] [Algebra K A]
    extends ChartPoint E p A where
  qPivot : Aˣ
  rPivot : Aˣ
  qPivot_eq : (qPivot : A) = coordinate q
  rPivot_eq : (rPivot : A) = coordinate r

namespace TripleOverlap

variable {E} {p q r : ι} {A : Type uA} [CommRing A] [Algebra K A]

/-- The first overlap in the three-chart calculation. -/
def first (x : TripleOverlap E p q r A) : Overlap E p q A :=
  ⟨x.toChartPoint, x.qPivot, x.qPivot_eq⟩

/-- The direct overlap from the first chart to the third. -/
def direct (x : TripleOverlap E p q r A) : Overlap E p r A :=
  ⟨x.toChartPoint, x.rPivot, x.rPivot_eq⟩

/-- In the intermediate normalized chart, the third pivot is the literal
ratio `x_r/x_q`, represented by `qPivot⁻¹ * rPivot`. -/
def second (x : TripleOverlap E p q r A) : Overlap E q r A where
  toChartPoint := x.first.transition.toChartPoint
  pivot := x.qPivot⁻¹ * x.rPivot
  pivot_eq := by
    change ((x.qPivot⁻¹ * x.rPivot : Aˣ) : A) =
      (↑x.qPivot⁻¹ : A) * x.coordinate r
    rw [Units.val_mul, x.rPivot_eq]

/-- The actual ratio cocycle: the two successive normalizations give exactly
the same third-chart coordinates as the direct normalization. -/
theorem cocycle (x : TripleOverlap E p q r A) :
    x.second.transition.toChartPoint = x.direct.transition.toChartPoint := by
  apply ChartPoint.ext
  intro i
  change (↑((x.qPivot⁻¹ * x.rPivot)⁻¹) : A) *
      ((↑x.qPivot⁻¹ : A) * x.coordinate i) =
    (↑x.rPivot⁻¹ : A) * x.coordinate i
  rw [← mul_assoc, ← Units.val_mul]
  congr 1
  apply congrArg Units.val
  simp [mul_assoc]

end TripleOverlap
end PaperVerification.NormalizedHomogeneousChart
