module

public import PaperVerification.NormalizedHomogeneousChart
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Localization.Away.Basic

/-!
# Actual coordinate rings representing normalized homogeneous charts

The normalized chart is the literal polynomial quotient by the original
homogeneous equations and `X_p - 1`. Its overlap is the actual localization
away from the class of `X_q`. Both universal properties are proved as
bijections on points over every commutative coefficient algebra, naturally
in that algebra. In particular this construction retains nilpotents.

These results provide the quotient/localization interpretation of the
coordinate transitions in `NormalizedHomogeneousChart`. Identifying a
particular system with Plucker or common-isotropic equations remains a
separate specialization. This source candidate has not yet been compiled.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section

namespace PaperVerification.NormalizedHomogeneousChart

universe u v w uA uB
variable {K : Type u} [CommRing K] {ι : Type v} {η : Type w}
variable (E : System K ι η)

/-- The full defining ideal of the actual normalized chart. -/
def chartIdeal (p : ι) : Ideal (MvPolynomial ι K) :=
  Ideal.span (Set.range E.equation) ⊔ Ideal.span {MvPolynomial.X p - 1}

/-- The actual normalized polynomial quotient, without radicalization. -/
abbrev ChartRing (p : ι) := MvPolynomial ι K ⧸ chartIdeal E p

/-- The canonical polynomial quotient homomorphism. -/
def quotientMap (p : ι) : MvPolynomial ι K →ₐ[K] ChartRing E p :=
  Ideal.Quotient.mkₐ K (chartIdeal E p)

/-- A literal coordinate in the normalized quotient. -/
def coordinate (p i : ι) : ChartRing E p := quotientMap E p (MvPolynomial.X i)

@[simp] theorem quotient_equation (p : ι) (j : η) :
    quotientMap E p (E.equation j) = 0 := by
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.mem_sup_left (Ideal.subset_span (Set.mem_range_self j))

@[simp] theorem coordinate_normalized (p : ι) : coordinate E p p = 1 := by
  apply sub_eq_zero.mp
  change quotientMap E p (MvPolynomial.X p) - 1 = 0
  rw [← map_one (quotientMap E p), ← map_sub]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  exact Ideal.mem_sup_right (Ideal.subset_span (Set.mem_singleton _))

/-- Substituting the quotient coordinates is exactly the quotient map. -/
theorem aeval_coordinate (p : ι) :
    MvPolynomial.aeval (coordinate E p) = quotientMap E p := by
  ext i
  exact MvPolynomial.aeval_X (coordinate E p) i

variable {E} {p q : ι} {A : Type uA} [CommRing A] [Algebra K A]

/-- Every actual normalized point annihilates the entire defining ideal. -/
theorem chartIdeal_le_ker (x : ChartPoint E p A) :
    chartIdeal E p ≤ RingHom.ker (MvPolynomial.aeval x.coordinate).toRingHom := by
  apply sup_le
  · apply Ideal.span_le.mpr
    rintro f ⟨j, rfl⟩
    exact x.vanishes j
  · apply Ideal.span_le.mpr
    intro f hf
    obtain rfl := Set.mem_singleton_iff.mp hf
    change MvPolynomial.aeval x.coordinate (MvPolynomial.X p - 1) = 0
    rw [map_sub, MvPolynomial.aeval_X, map_one, x.normalized, sub_self]

/-- The homomorphism defined by a normalized point, via the actual quotient
universal property. -/
def pointToHom (x : ChartPoint E p A) : ChartRing E p →ₐ[K] A :=
  Ideal.Quotient.liftₐ (chartIdeal E p) (MvPolynomial.aeval x.coordinate)
    (fun f hf => chartIdeal_le_ker x hf)

@[simp] theorem pointToHom_quotient (x : ChartPoint E p A) (f : MvPolynomial ι K) :
    pointToHom x (quotientMap E p f) = MvPolynomial.aeval x.coordinate f := by
  exact AlgHom.congr_fun
    (Ideal.Quotient.liftₐ_comp (chartIdeal E p)
      (MvPolynomial.aeval x.coordinate) (fun f hf => chartIdeal_le_ker x hf)) f

@[simp] theorem pointToHom_coordinate (x : ChartPoint E p A) (i : ι) :
    pointToHom x (coordinate E p i) = x.coordinate i := by
  rw [coordinate, pointToHom_quotient, MvPolynomial.aeval_X]

/-- Reading the coordinates of any homomorphism from the quotient produces
an actual normalized point satisfying the original equations. -/
def homToPoint (f : ChartRing E p →ₐ[K] A) : ChartPoint E p A where
  coordinate i := f (coordinate E p i)
  normalized := by rw [coordinate_normalized, map_one]
  vanishes j := by
    rw [← MvPolynomial.comp_aeval_apply, aeval_coordinate, quotient_equation, map_zero]

@[simp] theorem homToPoint_coordinate (f : ChartRing E p →ₐ[K] A) (i : ι) :
    (homToPoint f).coordinate i = f (coordinate E p i) := rfl

@[simp] theorem homToPoint_pointToHom (x : ChartPoint E p A) :
    homToPoint (pointToHom x) = x := by
  ext i
  exact pointToHom_coordinate x i

@[simp] theorem pointToHom_homToPoint (f : ChartRing E p →ₐ[K] A) :
    pointToHom (homToPoint f) = f := by
  apply Ideal.Quotient.algHom_ext K
  ext i
  change pointToHom (homToPoint f) (coordinate E p i) = f (coordinate E p i)
  rw [pointToHom_coordinate, homToPoint_coordinate]

/-- Representability of the complete normalized point functor by the
literal quotient ring, for every commutative coefficient algebra. -/
def chartPointEquiv (E : System K ι η) (p : ι) (A : Type uA)
    [CommRing A] [Algebra K A] :
    ChartPoint E p A ≃ (ChartRing E p →ₐ[K] A) where
  toFun := pointToHom
  invFun := homToPoint
  left_inv := homToPoint_pointToHom
  right_inv := pointToHom_homToPoint

/-- The quotient representation commutes with every coefficient algebra map. -/
theorem pointToHom_natural {B : Type uB} [CommRing B] [Algebra K B]
    (φ : A →ₐ[K] B) (x : ChartPoint E p A) :
    pointToHom (x.map φ) = φ.comp (pointToHom x) := by
  apply Ideal.Quotient.algHom_ext K
  ext i
  change pointToHom (x.map φ) (coordinate E p i) =
    φ (pointToHom x (coordinate E p i))
  rw [pointToHom_coordinate, ChartPoint.map_coordinate, pointToHom_coordinate]

@[simp] theorem homToPoint_natural {B : Type uB} [CommRing B] [Algebra K B]
    (φ : A →ₐ[K] B) (f : ChartRing E p →ₐ[K] A) :
    homToPoint (φ.comp f) = (homToPoint f).map φ := by
  ext i
  rfl

/-- The actual affine overlap ring is localization at the other coordinate. -/
abbrev OverlapRing (E : System K ι η) (p q : ι) :=
  Localization.Away (coordinate E p q)

/-- The canonical map from the normalized chart ring to its overlap. -/
def overlapMap (E : System K ι η) (p q : ι) :
    ChartRing E p →ₐ[K] OverlapRing E p q :=
  Algebra.algHom K (ChartRing E p) (OverlapRing E p q)

/-- The original unit-valued pivot gives exactly the invertibility required
by the localization universal property. -/
theorem pointToHom_pivot_isUnit (x : Overlap E p q A) :
    IsUnit (pointToHom x.toChartPoint (coordinate E p q)) := by
  rw [pointToHom_coordinate, ← x.pivot_eq]
  exact x.pivot.isUnit

/-- The actual localization homomorphism induced by an overlap point. -/
def overlapToHom (x : Overlap E p q A) : OverlapRing E p q →ₐ[K] A :=
  IsLocalization.Away.liftAlgHom (S := OverlapRing E p q)
    (coordinate E p q) (pointToHom_pivot_isUnit x)

@[simp] theorem overlapToHom_base (x : Overlap E p q A) (z : ChartRing E p) :
    overlapToHom x (overlapMap E p q z) = pointToHom x.toChartPoint z := by
  exact IsLocalization.Away.lift_eq (S := OverlapRing E p q)
    (coordinate E p q) (pointToHom_pivot_isUnit x) z

/-- The image of the localized coordinate is a unit under every algebra map. -/
theorem localized_pivot_isUnit (f : OverlapRing E p q →ₐ[K] A) :
    IsUnit (f (overlapMap E p q (coordinate E p q))) :=
  (IsLocalization.Away.algebraMap_isUnit
    (S := OverlapRing E p q) (coordinate E p q)).map f

/-- Read a literal overlap point from a homomorphism out of its localization. -/
def homToOverlap (f : OverlapRing E p q →ₐ[K] A) : Overlap E p q A where
  toChartPoint := homToPoint (f.comp (overlapMap E p q))
  pivot := (localized_pivot_isUnit f).unit
  pivot_eq := (localized_pivot_isUnit f).unit_spec

@[simp] theorem homToOverlap_coordinate (f : OverlapRing E p q →ₐ[K] A) (i : ι) :
    (homToOverlap f).coordinate i = f (overlapMap E p q (coordinate E p i)) := rfl

@[simp] theorem homToOverlap_overlapToHom (x : Overlap E p q A) :
    homToOverlap (overlapToHom x) = x := by
  ext i
  rw [homToOverlap_coordinate, overlapToHom_base, pointToHom_coordinate]

@[simp] theorem overlapToHom_homToOverlap (f : OverlapRing E p q →ₐ[K] A) :
    overlapToHom (homToOverlap f) = f := by
  apply IsLocalization.algHom_ext (Submonoid.powers (coordinate E p q))
  apply Ideal.Quotient.algHom_ext K
  ext i
  change overlapToHom (homToOverlap f) (overlapMap E p q (coordinate E p i)) =
    f (overlapMap E p q (coordinate E p i))
  rw [overlapToHom_base, pointToHom_coordinate, homToOverlap_coordinate]

/-- The full overlap point functor is represented by the actual Away
localization, including its nonreduced coefficient algebras. -/
def overlapPointEquiv (E : System K ι η) (p q : ι) (A : Type uA)
    [CommRing A] [Algebra K A] :
    Overlap E p q A ≃ (OverlapRing E p q →ₐ[K] A) where
  toFun := overlapToHom
  invFun := homToOverlap
  left_inv := homToOverlap_overlapToHom
  right_inv := overlapToHom_homToOverlap

/-- Naturality of the actual localization representation. -/
theorem overlapToHom_natural {B : Type uB} [CommRing B] [Algebra K B]
    (φ : A →ₐ[K] B) (x : Overlap E p q A) :
    overlapToHom (x.map φ) = φ.comp (overlapToHom x) := by
  apply IsLocalization.algHom_ext (Submonoid.powers (coordinate E p q))
  apply Ideal.Quotient.algHom_ext K
  ext i
  change overlapToHom (x.map φ) (overlapMap E p q (coordinate E p i)) =
    φ (overlapToHom x (overlapMap E p q (coordinate E p i)))
  rw [overlapToHom_base, pointToHom_coordinate, Overlap.map_coordinate,
    overlapToHom_base, pointToHom_coordinate]

@[simp] theorem homToOverlap_natural {B : Type uB} [CommRing B] [Algebra K B]
    (φ : A →ₐ[K] B) (f : OverlapRing E p q →ₐ[K] A) :
    homToOverlap (φ.comp f) = (homToOverlap f).map φ := by
  ext i
  rfl

/-- The actual contravariant algebra map between the two coordinate rings
of the same overlap, obtained by normalizing the universal point. -/
def transitionHom (E : System K ι η) (p q : ι) :
    OverlapRing E q p →ₐ[K] OverlapRing E p q :=
  overlapToHom
    ((homToOverlap (AlgHom.id K (OverlapRing E p q))).transition)

/-- The ring map represents exactly the already-proved point transition. -/
theorem transitionHom_natural (f : OverlapRing E p q →ₐ[K] A) :
    overlapToHom (homToOverlap f).transition = f.comp (transitionHom E p q) := by
  have h : homToOverlap f =
      (homToOverlap (AlgHom.id K (OverlapRing E p q))).map f := by
    ext i
    rfl
  rw [h, Overlap.transition_natural]
  exact overlapToHom_natural f _

/-- The two actual transition ring maps are inverse. -/
theorem transitionHom_comp (E : System K ι η) (p q : ι) :
    (transitionHom E p q).comp (transitionHom E q p) =
      AlgHom.id K (OverlapRing E p q) := by
  rw [← transitionHom_natural (E := E) (p := q) (q := p) (transitionHom E p q)]
  simp only [transitionHom, homToOverlap_overlapToHom,
    Overlap.transition_transition, overlapToHom_homToOverlap]

/-- An actual algebra equivalence of the localized chart rings; the map on
all algebra-valued points is the literal unit-ratio normalization. -/
def transitionRingEquiv (E : System K ι η) (p q : ι) :
    OverlapRing E q p ≃ₐ[K] OverlapRing E p q :=
  AlgEquiv.ofAlgHom (transitionHom E p q) (transitionHom E q p)
    (transitionHom_comp E p q) (transitionHom_comp E q p)

/-- The overlap ring morphism has the promised literal ratio on coordinates. -/
theorem transitionHom_coordinate (E : System K ι η) (p q i : ι) :
    transitionHom E p q (overlapMap E q p (coordinate E q i)) =
      (↑(homToOverlap (AlgHom.id K (OverlapRing E p q))).pivot⁻¹ : OverlapRing E p q) *
        overlapMap E p q (coordinate E p i) := by
  simp only [transitionHom, overlapToHom_base, pointToHom_coordinate,
    Overlap.transition_coordinate, homToOverlap_coordinate, AlgHom.id_apply]

end PaperVerification.NormalizedHomogeneousChart
