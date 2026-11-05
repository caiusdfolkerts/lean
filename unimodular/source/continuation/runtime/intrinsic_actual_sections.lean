module

public import Recovery.Unimodular.GraphicSectionRing.OrdinaryCartierSectionAlgebra
import all Recovery.Unimodular.GraphicSectionRing.OrdinaryCartierSectionAlgebra

public import Continuation.Runtime.IntrinsicReconstruction
public import Continuation.Runtime.IntrinsicBoundaryRays
public import Continuation.Runtime.EmbeddingPolynomialRestriction
public import Recovery.Unimodular.GraphicSectionRing.GradedCharacters
public import Recovery.Unimodular.GraphicSectionRing.GraphicIncidenceCoordinates
public import Recovery.Unimodular.GraphicSectionRing.PointFiniteness
public import Recovery.Unimodular.GraphicSectionRing.CartierRingEquivalence

/-! Exact previously checked character-section and ordinary section-ring proofs
for the original smooth complete toric scheme. Existing fan-scheme owners
are reused without a second declaration of their contents. -/

@[expose] public section
set_option autoImplicit false
set_option maxHeartbeats 0
set_option maxRecDepth 100000

section Recovered_IntrinsicCompleteSections
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

namespace PaperVerification.ToricSchemes.CartierData

open AlgebraicGeometry CategoryTheory
open Unimodular.GraphicSectionRing.ActualSections
open scoped PaperVerification.ToricSchemes.BaseSections

variable {k : Type u} [Field k] {X : Scheme.{u}} [IsIntegral X]
    [IsLocallyNoetherian X] [X.Over (Spec (CommRingCat.of k))]
    (D : CartierData X)

/-- The selected rational cocycle computes the actual Weil coefficient
at every point of each of its opens. -/
theorem powerFrame_coefficient (i : D.localCocycle.index) (x : X)
    (hx : x ∈ D.localCocycle.openSet i) :
    D.weilCoefficient x = -X.ord (D.localCocycle.generator i : X.functionField) x := by
  rw [congrFun (D.equivalent_weilCoefficient D.localCocycle.toCartierData
    D.equivalent_localCocycle) x]
  exact D.localCocycle.weilCoefficient_eq_neg_generator i x hx

/-- Every degree uses the genuine local frame raised to that degree.
The converse uses normality on whole local opens, not merely regularity
at the particular point whose codimension might exceed one. -/
theorem mem_powerValues_iff_orders (f : X ⟶ Spec (CommRingCat.of k)) [Smooth f]
    (d : ℕ) (r : X.functionField) (hr : r ≠ 0) :
    r ∈ powerValues k D.localCocycle d ↔
      ∀ x : X, 0 ≤ X.ord r x + (d : ℤ) * D.weilCoefficient x := by
  constructor
  · intro h x
    by_cases hx : Order.coheight x = 1
    · letI : IsIntegrallyClosed (X.presheaf.stalk x) :=
        smooth_stalk_isIntegrallyClosed f x
      obtain ⟨i, hi⟩ := D.localCocycle.covers x
      have hreg := (mem_powerValues_iff k D.localCocycle d r).mp h i x hi
      have horder := (rationalOrder_nonnegative_iff_regularAt x hx
        (r / (D.localCocycle.generator i : X.functionField) ^ d)
        (div_ne_zero hr (pow_ne_zero d (D.localCocycle.generator i).ne_zero))).mpr hreg
      rw [rationalOrder_div hr (pow_ne_zero d (D.localCocycle.generator i).ne_zero),
        rationalOrder_pow (D.localCocycle.generator i).ne_zero] at horder
      rw [D.powerFrame_coefficient i x hi]
      simpa only [mul_neg, sub_eq_add_neg] using horder
    · simp only [Scheme.ord_eq_zero_of_coheight_neq_one hx,
        D.weilCoefficient_eq_zero_of_coheight_ne_one hx, mul_zero, add_zero, le_refl]
  · intro h
    apply (mem_powerValues_iff k D.localCocycle d r).mpr
    intro i x hx
    let U := D.localCocycle.openSet i
    letI : Nonempty U := ⟨⟨x, hx⟩⟩
    have hreg : r / (D.localCocycle.generator i : X.functionField) ^ d ∈
        (X.germToFunctionField U).hom.range := by
      apply (smooth_regular_range_iff_orders f U _
        (div_ne_zero hr (pow_ne_zero d (D.localCocycle.generator i).ne_zero))).mpr
      intro y hy
      rw [rationalOrder_div hr (pow_ne_zero d (D.localCocycle.generator i).ne_zero),
        rationalOrder_pow (D.localCocycle.generator i).ne_zero]
      have hh := h y
      rw [D.powerFrame_coefficient i y hy] at hh
      simpa only [mul_neg, sub_eq_add_neg] using hh
    obtain ⟨s, hs⟩ := hreg
    rw [← hs]
    exact regular_germ_mem_regularAt X U s x hx

/-- Unit frames on an open make every actual divisor coefficient there zero. -/
theorem coefficient_zero_of_unitFrames (U : X.Opens)
    (hU : D.localCocycle.HasUnitFramesOn U) (x : X) (hx : x ∈ U) :
    D.weilCoefficient x = 0 := by
  rw [congrFun (D.equivalent_weilCoefficient D.localCocycle.toCartierData
    D.equivalent_localCocycle) x]
  exact D.localCocycle.weilCoefficient_zero_of_unitFrames U hU x hx

end PaperVerification.ToricSchemes.CartierData

namespace PaperVerification.ToricSchemes.SplitToricEmbedding

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricGeometry PaperVerification.ToricCharacters
open Unimodular.GraphicSectionRing.ActualSections
open scoped PaperVerification.ToricSchemes.BaseSections

variable {k : Type u} [Field k] {n : ℕ}
    {X : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n → ℤ)) X]
    [IsIntegral X.left] [Smooth X.hom]
    (T : SplitToricEmbedding k n X)

local instance completeSectionLocallyNoetherian : IsLocallyNoetherian X.left :=
  LocallyOfFiniteType.isLocallyNoetherian X.hom

/-- Literal inequalities at every genuine boundary prime divisor. -/
def boundaryPowerExponents (E : CartierData X.left) (d : ℕ) : Set (Lattice n) :=
  {m | ∀ q : T.BoundaryPrime,
    0 ≤ T.characterOrder q.val m + (d : ℤ) * E.weilCoefficient q.val}

/-- The actual global character sections are exactly the boundary
inequalities. Torus points and non-height-one points are proved redundant. -/
theorem character_mem_powerValues_iff_boundary
    (E : CartierData X.left) (hE : E.localCocycle.HasUnitFramesOn T.torusOpen)
    (d : ℕ) (m : Lattice n) :
    T.intrinsicCharacter m ∈ powerValues k E.localCocycle d ↔
      m ∈ T.boundaryPowerExponents E d := by
  rw [E.mem_powerValues_iff_orders X.hom d _ (T.intrinsicCharacter_ne_zero m)]
  constructor
  · intro h q
    exact h q.val
  · intro h x
    by_cases hx : Order.coheight x = 1
    · by_cases hb : x ∈ T.boundary
      · exact h ⟨x, hx, hb⟩
      · have ht : x ∈ (T.torusOpen : Set X.left) := by simpa only [boundary, Set.mem_compl_iff,
          not_not] using hb
        obtain ⟨z, rfl⟩ := ht
        change 0 ≤ T.characterOrder (T.torus.left z) m +
          (d : ℤ) * E.weilCoefficient (T.torus.left z)
        rw [T.characterOrder_torus z m,
          E.coefficient_zero_of_unitFrames T.torusOpen hE (T.torus.left z) ⟨z, rfl⟩]
        simp
    · simp only [Scheme.ord_eq_zero_of_coheight_neq_one hx,
        E.weilCoefficient_eq_zero_of_coheight_ne_one hx, mul_zero, add_zero, le_refl]

/-- The complete power section space, not only its individual monomials,
is the Laurent subspace supported on the actual boundary inequalities. -/
theorem powerCharacters_eq_boundaryModule
    (E : CartierData X.left) (hE : E.localCocycle.HasUnitFramesOn T.torusOpen)
    (d : ℕ) :
    torusSectionCharacters k n X.left T.torus.left (E.nsmul d) =
      characterModule k (T.boundaryPowerExponents E d) := by
  rw [stable_eq_characterModule k _
    (T.torusSectionCharacters_isCharacterStable_of_unitFrames (E.nsmul d)
      (E.hasUnitFramesOn_nsmul hE d))]
  congr 1
  ext m
  change T.intrinsicCharacter m ∈ powerValues k E.localCocycle d ↔ _
  exact T.character_mem_powerValues_iff_boundary E hE d m

/-- A genuine rational section is precisely the value of a Laurent
polynomial with support in the proved character inequalities. This includes
the zero section, every degree, and empty character spaces. -/
theorem mem_powerValues_iff_boundary_support
    (E : CartierData X.left) (hE : E.localCocycle.HasUnitFramesOn T.torusOpen)
    (d : ℕ) (r : X.left.functionField) :
    r ∈ powerValues k E.localCocycle d ↔
      ∃ p : AddMonoidAlgebra k (Lattice n),
        (∀ m, m ∉ T.boundaryPowerExponents E d → p.coeff m = 0) ∧
        openTorusRationalAlgHom k n X.left T.torus.left p = r := by
  constructor
  · intro hr
    obtain ⟨p, hp⟩ := globalSectionValue_in_torusRange_of_unitFrames
      k n X.left T.torus.left (E.nsmul d) (E.hasUnitFramesOn_nsmul hE d) r hr
    refine ⟨p, ?_, hp⟩
    have hmem : p ∈ torusSectionCharacters k n X.left T.torus.left (E.nsmul d) := by
      change openTorusRationalAlgHom k n X.left T.torus.left p ∈
        powerValues k E.localCocycle d
      rwa [hp]
    rw [T.powerCharacters_eq_boundaryModule E hE d, mem_characterModule_iff] at hmem
    intro m hm
    by_contra hne
    exact hm (hmem (Finsupp.mem_support_iff.mpr hne))
  · rintro ⟨p, hp, rfl⟩
    change p ∈ torusSectionCharacters k n X.left T.torus.left (E.nsmul d)
    rw [T.powerCharacters_eq_boundaryModule E hE d, mem_characterModule_iff]
    intro m hm
    by_contra hnot
    exact (Finsupp.mem_support_iff.mp hm) (hp m hnot)

/-- The full semigroup of actual boundary-admissible characters in every
nonnegative degree. Its definition imposes no degree-zero condition; that
condition will be derived from properness when it is needed. -/
def boundarySectionSemigroup (E : CartierData X.left) :
    AddSubmonoid (ℕ × Lattice n) where
  carrier := {z | z.2 ∈ T.boundaryPowerExponents E z.1}
  zero_mem' := by
    intro q
    simp only [Prod.fst_zero, Prod.snd_zero, map_zero, Nat.cast_zero,
      zero_mul, add_zero, le_refl]
  add_mem' := by
    intro z w hz hw q
    have hqz := hz q
    have hqw := hw q
    change 0 ≤ T.characterOrder q.val (z.2 + w.2) +
      ((z.1 + w.1 : ℕ) : ℤ) * E.weilCoefficient q.val
    rw [map_add, Nat.cast_add, add_mul]
    linarith

/-- The independently constructed ordinary section ring is the semigroup
algebra of precisely its actual characters. This equivalence is proved
from the global-section image, not used to define the section ring. -/
def actualBoundarySectionRingEquiv
    (E : CartierData X.left) (hE : E.localCocycle.HasUnitFramesOn T.torusOpen) :
    AddMonoidAlgebra k (T.boundarySectionSemigroup E) ≃ₐ[k]
      sectionRing k E.localCocycle :=
  Unimodular.GraphicSectionRing.GradedCharacters.equivActual
    (T.boundarySectionSemigroup E)
    (openTorusRationalAlgHom k n X.left T.torus.left)
    (openTorusRationalAlgHom_injective k n X.left T.torus.left)
    (sectionRing k E.localCocycle) (by
      intro p
      change (∀ d, p.coeff d ∈ powerValues k E.localCocycle d) ↔ _
      constructor
      · intro hp d
        exact (T.mem_powerValues_iff_boundary_support E hE d (p.coeff d)).mp (hp d)
      · intro hp d
        exact (T.mem_powerValues_iff_boundary_support E hE d (p.coeff d)).mpr (hp d))

/-- Every semigroup monomial maps to its original character rational
function in its original degree. -/
theorem actualBoundarySectionRingEquiv_single
    (E : CartierData X.left) (hE : E.localCocycle.HasUnitFramesOn T.torusOpen)
    (z : T.boundarySectionSemigroup E) (a : k) :
    (T.actualBoundarySectionRingEquiv E hE (AddMonoidAlgebra.single z a)).val =
      AddMonoidAlgebra.single z.val.1
        (openTorusRationalAlgHom k n X.left T.torus.left
          (AddMonoidAlgebra.single z.val.2 a)) :=
  Unimodular.GraphicSectionRing.GradedCharacters.evaluation_single
    (T.boundarySectionSemigroup E)
    (openTorusRationalAlgHom k n X.left T.torus.left) z a


end PaperVerification.ToricSchemes.SplitToricEmbedding


end
end Recovered_IntrinsicCompleteSections

section Recovered_CompleteGraphicCoordinates
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace PaperVerification.ToricSchemes.SplitToricEmbedding

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricGeometry
open Unimodular.GraphicRootedLattice Unimodular.GraphicSectionRing
open scoped Classical BigOperators PaperVerification.ToricSchemes.BaseSections

variable {k : Type u} [Field k] {n : ℕ}
    {X : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n → ℤ)) X]
    [IsIntegral X.left] [Smooth X.hom]
    (T : SplitToricEmbedding k n X)

local instance graphicBoundaryLocallyNoetherian : IsLocallyNoetherian X.left :=
  LocallyOfFiniteType.isLocallyNoetherian X.hom

/-- Integral graphicity in the actual original lattice. Its vector labels
are the original valuation vectors themselves, not an abstract matroid or
an independently supplied fan. -/
structure IntegralGraphicBoundaryPresentation {V : Type v} [Fintype V]
    (H : SimpleGraph V) where
  equiv : PaperVerification.ToricGeometry.Lattice n ≃ₗ[ℤ] incidenceSpan H
  source : T.completeBoundaryRaySet → V
  target : T.completeBoundaryRaySet → V
  adjacent : ∀ q, H.Adj (source q) (target q)
  ray_image : ∀ q, (equiv q.val).val = edge (source q) (target q)

namespace IntegralGraphicBoundaryPresentation

variable {T} {V : Type v} [Fintype V] {H : SimpleGraph V}
    (P : T.IntegralGraphicBoundaryPresentation H)

abbrev Index := FreeVertex H.connectedComponentMk (graphRoot H)

def rawCoordinates : PaperVerification.ToricGeometry.Lattice n ≃ₗ[ℤ] (Index (H := H) → ℤ) :=
  P.equiv.trans (incidenceCoordinates H)

include P in
theorem index_card : Fintype.card (Index (H := H)) = n := by
  have h := integral_coordinate_card P.rawCoordinates
  simpa only [Fintype.card_fin] using h.symm

def indexEquiv : Index (H := H) ≃ Fin n :=
  Fintype.equivOfCardEq (by rw [P.index_card, Fintype.card_fin])

def vertexIndex (x : V) : Coordinate n :=
  (vertexCoordinate H.connectedComponentMk (graphRoot H) x).map P.indexEquiv

def rayCoordinates : PaperVerification.ToricGeometry.Lattice n ≃ₗ[ℤ] PaperVerification.ToricGeometry.Lattice n :=
  P.rawCoordinates.trans (LinearEquiv.funCongrLeft ℤ ℤ P.indexEquiv.symm)

theorem rawCoordinates_apply (x : PaperVerification.ToricGeometry.Lattice n) (i : Index (H := H)) :
    P.rawCoordinates x i = (P.equiv x).val i.val := by
  simp only [rawCoordinates, incidenceCoordinates, LinearEquiv.trans_apply,
    coordinates_apply, LinearEquiv.coe_ofEq_apply]

theorem rawCoordinates_ray (q : T.completeBoundaryRaySet) :
    P.rawCoordinates q.val =
      coordinateVertex H.connectedComponentMk (graphRoot H)
        (vertexCoordinate H.connectedComponentMk (graphRoot H) (P.source q)) -
      coordinateVertex H.connectedComponentMk (graphRoot H)
        (vertexCoordinate H.connectedComponentMk (graphRoot H) (P.target q)) := by
  ext i
  rw [P.rawCoordinates_apply, P.ray_image]
  have h := coordinates_edge H.connectedComponentMk (graphRoot H) (graphRoot_component H)
    (SimpleGraph.ConnectedComponent.sound (P.adjacent q).reachable)
  exact congrFun h i

theorem coordinateVertex_reindex (i : Option (Index (H := H))) :
    LinearEquiv.funCongrLeft ℤ ℤ P.indexEquiv.symm
        (coordinateVertex H.connectedComponentMk (graphRoot H) i) =
      coordinateNormal (i.map P.indexEquiv) := by
  cases i with
  | none => rfl
  | some i =>
    ext j
    change (Pi.single i (1 : ℤ) : Index (H := H) → ℤ) (P.indexEquiv.symm j) =
      (Pi.single (P.indexEquiv i) (1 : ℤ) : Fin n → ℤ) j
    simp [Pi.single_apply, Equiv.apply_eq_iff_eq_symm_apply]

theorem rayCoordinates_ray (q : T.completeBoundaryRaySet) :
    P.rayCoordinates q.val = coordinateNormal (P.vertexIndex (P.source q)) -
      coordinateNormal (P.vertexIndex (P.target q)) := by
  simp only [rayCoordinates, LinearEquiv.trans_apply, P.rawCoordinates_ray, map_sub,
    P.coordinateVertex_reindex, vertexIndex]

def characterCoordinates : PaperVerification.ToricGeometry.Lattice n ≃ₗ[ℤ] PaperVerification.ToricGeometry.Lattice n := dualCoordinates P.rayCoordinates

def originalRay (q : T.BoundaryPrime) : T.completeBoundaryRaySet :=
  ⟨T.boundaryValuation q, q, rfl⟩

def left (q : T.BoundaryPrime) : Coordinate n :=
  P.vertexIndex (P.target (originalRay (T := T) q))

def right (q : T.BoundaryPrime) : Coordinate n :=
  P.vertexIndex (P.source (originalRay (T := T) q))

/-- Every original boundary valuation is transformed with its exact
pairing and sign; no primitive vector is rescaled. -/
theorem character_pairing (q : T.BoundaryPrime) (m : PaperVerification.ToricGeometry.Lattice n) :
    T.characterOrder q.val m =
      -difference (P.characterCoordinates m) (P.left q) (P.right q) := by
  rw [T.characterOrder_eq_integerPairing]
  change dotProduct (originalRay (T := T) q).val m = _
  rw [dualCoordinates_pairing P.rayCoordinates, P.rayCoordinates_ray,
    differenceNormal_pairing]
  unfold characterCoordinates left right difference
  ring

/-- The actual inequalities, including the coefficients of every boundary
prime. The set is allowed to be infinite until its point-finiteness theorem. -/
def constraints (E : CartierData X.left) : Set (Constraint n) :=
  Set.range (fun q : T.BoundaryPrime =>
    ⟨P.left q, P.right q, E.weilCoefficient q.val⟩)

theorem mem_exponents_iff (E : CartierData X.left) (d : ℕ) (m : PaperVerification.ToricGeometry.Lattice n) :
    m ∈ T.boundaryPowerExponents E d ↔
      ∀ c ∈ P.constraints E,
        difference (P.characterCoordinates m) c.left c.right ≤ (d : ℤ) * c.bound := by
  constructor
  · intro h c hc
    obtain ⟨q, rfl⟩ := hc
    have hh := h q
    rw [P.character_pairing q m] at hh
    linarith
  · intro h q
    have hh := h ⟨P.left q, P.right q, E.weilCoefficient q.val⟩ ⟨q, rfl⟩
    change 0 ≤ T.characterOrder q.val m + (d : ℤ) * E.weilCoefficient q.val
    rw [P.character_pairing q m]
    linarith

variable [IsProper X.hom]

/-- Properness proves the exact integral recession condition; it is not
inserted into the input graphic presentation. -/
theorem homogeneous_zero (E : CartierData X.left) (m : PaperVerification.ToricGeometry.Lattice n)
    (hm : ∀ c ∈ P.constraints E, difference m c.left c.right ≤ 0) : m = 0 := by
  have hz : P.characterCoordinates.symm m = 0 := by
    apply (T.nonnegative_boundary_orders_iff_zero _).mp
    intro q
    rw [P.character_pairing, LinearEquiv.apply_symm_apply]
    exact neg_nonneg.mpr (hm
      ⟨P.left q, P.right q, E.weilCoefficient q.val⟩ ⟨q, rfl⟩)
  have h := congrArg P.characterCoordinates hz
  simpa only [LinearEquiv.apply_symm_apply, map_zero] using h

theorem points_finite (E : CartierData X.left) : Finite (Point (P.constraints E)) :=
  finite_point_of_homogeneous_zero (P.constraints E) (P.homogeneous_zero E)

/-- The exact equivalence of the whole original graded character
semigroup. The degree-zero condition is deduced from actual properness. -/
def semigroupEquiv (E : CartierData X.left) :
    T.boundarySectionSemigroup E ≃+ sectionSemigroup (P.constraints E) where
  toFun z := ⟨(z.val.1, P.characterCoordinates z.val.2), by
    constructor
    · intro hz
      change z.val.1 = 0 at hz
      have ho : ∀ q : T.BoundaryPrime, 0 ≤ T.characterOrder q.val z.val.2 := by
        have hh := z.property
        change ∀ q : T.BoundaryPrime,
          0 ≤ T.characterOrder q.val z.val.2 +
            (z.val.1 : ℤ) * E.weilCoefficient q.val at hh
        simpa only [hz, Nat.cast_zero, zero_mul, add_zero] using hh
      rw [(T.nonnegative_boundary_orders_iff_zero z.val.2).mp ho, map_zero]
    · exact (P.mem_exponents_iff E z.val.1 z.val.2).mp z.property⟩
  invFun z := ⟨(z.val.1, P.characterCoordinates.symm z.val.2),
    (P.mem_exponents_iff E z.val.1 (P.characterCoordinates.symm z.val.2)).mpr (by
      simpa only [LinearEquiv.apply_symm_apply] using z.property.2)⟩
  left_inv z := Subtype.ext (Prod.ext rfl (P.characterCoordinates.symm_apply_apply z.val.2))
  right_inv z := Subtype.ext (Prod.ext rfl (P.characterCoordinates.apply_symm_apply z.val.2))
  map_add' z w := Subtype.ext (Prod.ext rfl (map_add P.characterCoordinates z.val.2 w.val.2))

/-- The actual ring of a torus-normalized Cartier presentation, proved
without an ample divisor or a fan reconstruction. -/
def normalizedGraphicRingEquiv (E : CartierData X.left)
    (hE : E.localCocycle.HasUnitFramesOn T.torusOpen) :
    SectionAlgebra (P.constraints E) k ≃ₐ[k] ActualSections.sectionRing k E.localCocycle :=
  (AddMonoidAlgebra.domCongr k k (P.semigroupEquiv E).symm).trans
    (T.actualBoundarySectionRingEquiv E hE)

theorem normalizedGraphicRingEquiv_single (E : CartierData X.left)
    (hE : E.localCocycle.HasUnitFramesOn T.torusOpen)
    (z : sectionSemigroup (P.constraints E)) (a : k) :
    (P.normalizedGraphicRingEquiv E hE (AddMonoidAlgebra.single z a)).val =
      AddMonoidAlgebra.single z.val.1
        (openTorusRationalAlgHom k n X.left T.torus.left
          (AddMonoidAlgebra.single (P.characterCoordinates.symm z.val.2) a)) := by
  change (T.actualBoundarySectionRingEquiv E hE
    (AddMonoidAlgebra.domCongr k k (P.semigroupEquiv E).symm
      (AddMonoidAlgebra.single z a))).val = _
  rw [AddMonoidAlgebra.domCongr_single, T.actualBoundarySectionRingEquiv_single]
  rfl


end IntegralGraphicBoundaryPresentation

/-- The actual rational scaling used to trivialize the input Cartier
presentation on the original dense torus. -/
def completeNormalizationUnit (D : CartierData X.left) : X.left.functionFieldˣ :=
  (torusCartierGenerator k n X.left T.torus.left D)⁻¹

theorem completeNormalizedCocycleEquivalent (D : CartierData X.left) :
    (D.localCocycle.scale (T.completeNormalizationUnit D)).toCartierData.Equivalent
      (torusNormalizedCartier k n X.left T.torus.left D).localCocycle.toCartierData := by
  have he : (torusNormalizedCartier k n X.left T.torus.left D).localCocycle =
      D.localCocycle.scale (T.completeNormalizationUnit D) :=
    D.scale_localCocycle (T.completeNormalizationUnit D)
  rw [he]
  exact CartierData.equivalent_refl _

def completeNormalizeRingEquiv (D : CartierData X.left) :
    ActualSections.sectionRing k D.localCocycle ≃ₐ[k]
      ActualSections.sectionRing k
        (torusNormalizedCartier k n X.left T.torus.left D).localCocycle :=
  (ActualSections.scaleEquivalence k D.localCocycle (T.completeNormalizationUnit D)).trans
    (ActualSections.equivalenceOfEquivalent k _ _ (T.completeNormalizedCocycleEquivalent D))

theorem completeNormalizeRingEquiv_coefficient (D : CartierData X.left)
    (s : ActualSections.sectionRing k D.localCocycle) (d : ℕ) :
    (T.completeNormalizeRingEquiv D s).val.coeff d =
      (T.completeNormalizationUnit D : X.left.functionField) ^ d * s.val.coeff d := by
  change (ActualSections.equivalenceOfEquivalent k _ _
    (T.completeNormalizedCocycleEquivalent D)
    (ActualSections.scaleEquivalence k D.localCocycle (T.completeNormalizationUnit D) s)).val.coeff d = _
  rw [ActualSections.equivalenceOfEquivalent_value]
  exact ActualSections.scaleEquivalence_coefficient k D.localCocycle
    (T.completeNormalizationUnit D) s d

theorem completeNormalizeRingEquiv_symm_coefficient (D : CartierData X.left)
    (s : ActualSections.sectionRing k
      (torusNormalizedCartier k n X.left T.torus.left D).localCocycle) (d : ℕ) :
    ((T.completeNormalizeRingEquiv D).symm s).val.coeff d =
      ((T.completeNormalizationUnit D : X.left.functionField)⁻¹) ^ d * s.val.coeff d := by
  have he := T.completeNormalizeRingEquiv_coefficient D
    ((T.completeNormalizeRingEquiv D).symm s) d
  rw [AlgEquiv.apply_symm_apply] at he
  rw [he, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ (Units.ne_zero _), one_pow, one_mul]

namespace IntegralGraphicBoundaryPresentation

variable {T} {V : Type v} [Fintype V] {H : SimpleGraph V}
    (P : T.IntegralGraphicBoundaryPresentation H) [IsProper X.hom]

/-- The whole ordinary section ring of every original Cartier divisor.
Normalization is a proved graded algebra equivalence, not an invariant
presentation supplied as an extra hypothesis. -/
def graphicSectionRingEquiv (D : CartierData X.left) :
    SectionAlgebra (P.constraints (torusNormalizedCartier k n X.left T.torus.left D)) k ≃ₐ[k]
      ActualSections.sectionRing k D.localCocycle :=
  (P.normalizedGraphicRingEquiv (torusNormalizedCartier k n X.left T.torus.left D)
    (torusNormalizedCartier_unitFrames k n X.left T.torus.left D)).trans
    (T.completeNormalizeRingEquiv D).symm

/-- The exact normalization factor preserves the original section degree. -/
theorem graphicSectionRingEquiv_single_coefficient (D : CartierData X.left)
    (z : sectionSemigroup (P.constraints (torusNormalizedCartier k n X.left T.torus.left D)))
    (a : k) (d : ℕ) :
    (P.graphicSectionRingEquiv D (AddMonoidAlgebra.single z a)).val.coeff d =
      ((T.completeNormalizationUnit D : X.left.functionField)⁻¹) ^ d *
        (AddMonoidAlgebra.single z.val.1
          (openTorusRationalAlgHom k n X.left T.torus.left
            (AddMonoidAlgebra.single (P.characterCoordinates.symm z.val.2) a))).coeff d := by
  change ((T.completeNormalizeRingEquiv D).symm
    (P.normalizedGraphicRingEquiv _ _ (AddMonoidAlgebra.single z a))).val.coeff d = _
  rw [T.completeNormalizeRingEquiv_symm_coefficient, P.normalizedGraphicRingEquiv_single]

theorem graphicSectionRingEquiv_homogeneous (D : CartierData X.left)
    (z : sectionSemigroup (P.constraints (torusNormalizedCartier k n X.left T.torus.left D)))
    (a : k) (d : ℕ) (hd : d ≠ z.val.1) :
    (P.graphicSectionRingEquiv D (AddMonoidAlgebra.single z a)).val.coeff d = 0 := by
  rw [P.graphicSectionRingEquiv_single_coefficient]
  simp only [AddMonoidAlgebra.coeff_single, Finsupp.single_apply,
    if_neg (Ne.symm hd), mul_zero]


end IntegralGraphicBoundaryPresentation
end PaperVerification.ToricSchemes.SplitToricEmbedding


end
end Recovered_CompleteGraphicCoordinates

section Recovered_CompleteGraphicSectionRingAudited
noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

namespace PaperVerification.ToricSchemes.SplitToricEmbedding

open AlgebraicGeometry CategoryTheory
open PaperVerification.ToricGeometry
open Unimodular.GraphicSectionRing
open scoped Classical BigOperators TensorProduct PaperVerification.ToricSchemes.BaseSections

variable {k : Type u} [Field k] {n : ℕ}
    {X : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n → ℤ)) X]
    [IsIntegral X.left] [Smooth X.hom] [IsProper X.hom]
    {T : SplitToricEmbedding k n X}

local instance completeRingLocallyNoetherian : IsLocallyNoetherian X.left :=
  LocallyOfFiniteType.isLocallyNoetherian X.hom

namespace IntegralGraphicBoundaryPresentation

variable {V : Type v} [Fintype V] {H : SimpleGraph V}
    (P : T.IntegralGraphicBoundaryPresentation H)

def sectionConstraints (D : CartierData X.left) : Set (Constraint n) :=
  P.constraints (torusNormalizedCartier k n X.left T.torus.left D)

/-- Variables are precisely the original degree-one character sections in
the derived integral coordinates. Their images lie in the actual ring. -/
def polynomialMap (D : CartierData X.left) :
    MvPolynomial (Point (P.sectionConstraints D)) k →ₐ[k]
      ActualSections.sectionRing k D.localCocycle :=
  (P.graphicSectionRingEquiv D).toAlgHom.comp (sectionMap (P.sectionConstraints D) k)

theorem polynomialMap_X (D : CartierData X.left) (a : Point (P.sectionConstraints D)) :
    P.polynomialMap D (MvPolynomial.X a) =
      P.graphicSectionRingEquiv D (AddMonoidAlgebra.single (degreeOnePoint a) 1) := by
  change P.graphicSectionRingEquiv D (sectionMap _ k (MvPolynomial.X a)) = _
  rw [sectionMap_X]

theorem polynomialMap_surjective (D : CartierData X.left) :
    Function.Surjective (P.polynomialMap D) :=
  (P.graphicSectionRingEquiv D).surjective.comp (sectionMap_surjective _ k)

theorem polynomialMap_ker (D : CartierData X.left) :
    RingHom.ker (P.polynomialMap D).toRingHom =
      toricIdeal (Subtype.val : Point (P.sectionConstraints D) →
        Unimodular.GraphicSectionRing.Lattice n) k := by
  rw [← sectionMap_ker]
  ext f
  change P.graphicSectionRingEquiv D (sectionMap _ k f) = 0 ↔ sectionMap _ k f = 0
  constructor
  · intro h
    exact (P.graphicSectionRingEquiv D).injective
      (h.trans (map_zero (P.graphicSectionRingEquiv D)).symm)
  · intro h
    exact (congrArg (P.graphicSectionRingEquiv D) h).trans
      (map_zero (P.graphicSectionRingEquiv D))

/-- A genuine squarefree quadratic initial ideal of the original
section-ring presentation, including empty or lower-dimensional spaces. -/
theorem polynomialMap_squarefree_initial (D : CartierData X.left) :
    ∃ m : MonomialOrder.{0,0} (Point (P.sectionConstraints D)),
      initialIdeal m (RingHom.ker (P.polynomialMap D).toRingHom) =
        quadraticMonomialIdeal (Subtype.val : Point (P.sectionConstraints D) →
          Unimodular.GraphicSectionRing.Lattice n) k ∧
      ∀ z ∈ forbiddenExponents (Subtype.val : Point (P.sectionConstraints D) →
          Unimodular.GraphicSectionRing.Lattice n),
        z.degree = 2 ∧ ∀ i, z i ≤ 1 := by
  letI : Finite (Point (P.sectionConstraints D)) :=
    P.points_finite (torusNormalizedCartier k n X.left T.torus.left D)
  obtain ⟨m, hm⟩ := exists_squarefree_quadratic_initial_ideal
    (C := P.sectionConstraints D) k
  refine ⟨m, ?_, fun z hz => forbiddenExponents_squarefree_quadratic _ hz⟩
  rw [P.polynomialMap_ker]
  exact hm

theorem cartier_hasDiagonalTor (D : CartierData X.left) :
    PaperVerification.WeightedBar.HasDiagonalTor
      (GeometricKoszul.augmentation (P.sectionConstraints D) k (P.graphicSectionRingEquiv D))
      (GeometricKoszul.basis (P.sectionConstraints D) k (P.graphicSectionRingEquiv D))
      (GeometricKoszul.basis_none (P.sectionConstraints D) k (P.graphicSectionRingEquiv D))
      (GeometricKoszul.augmentation_basis (P.sectionConstraints D) k (P.graphicSectionRingEquiv D))
      (GeometricKoszul.degree (P.sectionConstraints D))
      (GeometricKoszul.product_degree (P.sectionConstraints D) k (P.graphicSectionRingEquiv D)) := by
  letI : Finite (Point (P.sectionConstraints D)) :=
    P.points_finite (torusNormalizedCartier k n X.left T.torus.left D)
  letI := Fintype.ofFinite (Point (P.sectionConstraints D))
  exact GeometricKoszul.hasDiagonalTor _ k _

/-- The actual basis used by ordinary Tor is homogeneous for exactly the
original section degree, not a term order or an auxiliary weight. -/
theorem actualTorBasis_homogeneous (D : CartierData X.left)
    (z : GeometricKoszul.Index.{u} (P.sectionConstraints D))
    (d : ℕ) (hd : d ≠ GeometricKoszul.degree (P.sectionConstraints D) z) :
    (GeometricKoszul.basis (P.sectionConstraints D) k
      (P.graphicSectionRingEquiv D) (some z)).val.coeff d = 0 := by
  simp only [GeometricKoszul.basis, Unimodular.FlagKoszul.BarReindex.basis_some,
    Unimodular.FlagKoszul.AlgebraTransport.basis_apply]
  change (P.graphicSectionRingEquiv D
    (FlagModel.basis (P.sectionConstraints D) k (some z.down))).val.coeff d = 0
  rw [FlagModel.basis_some]
  apply P.graphicSectionRingEquiv_homogeneous
  change d ≠ internalDegree (P.sectionConstraints D)
    (sectionDegree (P.sectionConstraints D) z.down.val)
  rw [internalDegree_sectionDegree]
  exact hd

theorem graphicSectionRingEquiv_zero_coefficient (D : CartierData X.left)
    (f : SectionAlgebra (P.sectionConstraints D) k) :
    (P.graphicSectionRingEquiv D f).val.coeff 0 =
      algebraMap k X.left.functionField (sectionAugmentation (P.sectionConstraints D) k f) := by
  induction f using AddMonoidAlgebra.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simpa only [map_add, Subalgebra.coe_add, AddMonoidAlgebra.coeff_add, Finsupp.add_apply]
      using congrArg₂ (· + ·) hf hg
  | single z a =>
    rw [P.graphicSectionRingEquiv_single_coefficient, sectionAugmentation_single]
    change _ = algebraMap k X.left.functionField (if z.val.1 = 0 then a else 0)
    simp only [pow_zero, one_mul, AddMonoidAlgebra.coeff_single, Finsupp.single_apply]
    by_cases hz : z.val.1 = 0
    · simp only [hz, if_pos rfl]
      rw [z.property.1 hz, map_zero]
      change openTorusRationalAlgHom k n X.left T.torus.left
        (algebraMap k (AddMonoidAlgebra k (PaperVerification.ToricGeometry.Lattice n)) a) = _
      exact (openTorusRationalAlgHom k n X.left T.torus.left).commutes a
    · simp only [if_neg hz, map_zero]

/-- The augmentation in the Tor conclusion is the original degree-zero
coefficient under the actual structural scalar inclusion. -/
theorem actualAugmentation_is_degreeZero (D : CartierData X.left)
    (s : ActualSections.sectionRing k D.localCocycle) :
    algebraMap k X.left.functionField
      (GeometricKoszul.augmentation (P.sectionConstraints D) k (P.graphicSectionRingEquiv D) s) =
        s.val.coeff 0 := by
  have h := P.graphicSectionRingEquiv_zero_coefficient D
    ((P.graphicSectionRingEquiv D).symm s)
  rw [AlgEquiv.apply_symm_apply] at h
  exact h.symm

/-- The complete geometric clause of Proposition 6.10. Every ordinary
invertible sheaf is admitted, hence in particular every nef line bundle.
Properness is the original completeness hypothesis; projectivity is absent. -/
theorem theorem_6_10_complete_toric (M : X.left.Modules) (hM : IsInvertibleModule M) :
    let D := invertibleFractionalPresentation M hM
    let C := P.sectionConstraints D
    let e := P.graphicSectionRingEquiv D
    Function.Surjective (P.polynomialMap D) ∧
    (∃ m : MonomialOrder.{0,0} (Point C),
      initialIdeal m (RingHom.ker (P.polynomialMap D).toRingHom) =
        quadraticMonomialIdeal (Subtype.val : Point C → Unimodular.GraphicSectionRing.Lattice n) k ∧
      ∀ z ∈ forbiddenExponents (Subtype.val : Point C → Unimodular.GraphicSectionRing.Lattice n),
        z.degree = 2 ∧ ∀ i, z i ≤ 1) ∧
    PaperVerification.WeightedBar.HasDiagonalTor
      (GeometricKoszul.augmentation C k e) (GeometricKoszul.basis C k e)
      (GeometricKoszul.basis_none C k e) (GeometricKoszul.augmentation_basis C k e)
      (GeometricKoszul.degree C) (GeometricKoszul.product_degree C k e) :=
  ⟨P.polynomialMap_surjective (invertibleFractionalPresentation M hM),
    P.polynomialMap_squarefree_initial (invertibleFractionalPresentation M hM),
    P.cartier_hasDiagonalTor (invertibleFractionalPresentation M hM)⟩


end IntegralGraphicBoundaryPresentation

/-! These comparisons explicitly identify the ring appearing above with
the ordinary finite direct sum of the original tensor-power sections. -/

def completeOrdinaryRing (M : X.left.Modules) (hM : IsInvertibleModule M) :=
  ActualSections.sectionRing k (invertibleFractionalPresentation M hM).localCocycle

def completeOrdinaryInclusion (M : X.left.Modules) (hM : IsInvertibleModule M) (d : ℕ) :
    Γ(tensorSheafPower M d, ⊤) →ₗ[k] completeOrdinaryRing (k := k) M hM :=
  ActualSections.ordinaryHomogeneousSection k (invertibleFractionalPresentation M hM) d

def completeOrdinaryCoefficient (M : X.left.Modules) (hM : IsInvertibleModule M)
    (d : ℕ) (s : completeOrdinaryRing (k := k) M hM) : Γ(tensorSheafPower M d, ⊤) :=
  (ActualSections.ordinaryPowerValueEquiv k (invertibleFractionalPresentation M hM) d).symm
    ⟨s.val.coeff d, s.property d⟩

theorem completeOrdinaryInclusion_injective (M : X.left.Modules)
    (hM : IsInvertibleModule M) (d : ℕ) :
    Function.Injective (completeOrdinaryInclusion (k := k) M hM d) :=
  ActualSections.ordinaryHomogeneousSection_injective k (invertibleFractionalPresentation M hM) d

theorem completeOrdinary_finite_sum (M : X.left.Modules) (hM : IsInvertibleModule M)
    (s : completeOrdinaryRing (k := k) M hM) :
    (∑ d ∈ s.val.coeff.support, completeOrdinaryInclusion (k := k) M hM d
      (completeOrdinaryCoefficient (k := k) M hM d s)) = s := by
  apply Subtype.ext
  change (ActualSections.sectionRing k (invertibleFractionalPresentation M hM).localCocycle).val
    (∑ d ∈ s.val.coeff.support, completeOrdinaryInclusion (k := k) M hM d
      (completeOrdinaryCoefficient (k := k) M hM d s)) = s.val
  rw [map_sum]
  change (∑ d ∈ s.val.coeff.support,
    (ActualSections.ordinaryHomogeneousSection k (invertibleFractionalPresentation M hM) d
      ((ActualSections.ordinaryPowerValueEquiv k (invertibleFractionalPresentation M hM) d).symm
        ⟨s.val.coeff d, s.property d⟩)).val) = s.val
  simp only [ActualSections.ordinaryHomogeneousSection_value, LinearEquiv.apply_symm_apply]
  exact AddMonoidAlgebra.sum_coeff_single s.val

/-- Equality of the full canonical multiplication maps, for every pair
of natural degrees and all original sections. -/
theorem completeOrdinary_canonicalMultiplication (M : X.left.Modules)
    (hM : IsInvertibleModule M) (i j : ℕ) :
    (completeOrdinaryInclusion (k := k) M hM (i + j)).comp
      (CanonicalPowers.sectionMultiplication k M i j) =
        (LinearMap.mul' k (completeOrdinaryRing (k := k) M hM)).comp
          (TensorProduct.map (completeOrdinaryInclusion (k := k) M hM i)
            (completeOrdinaryInclusion (k := k) M hM j)) :=
  ActualSections.ordinaryHomogeneousSection_comp_canonicalMultiplication
    k (invertibleFractionalPresentation M hM) i j

/-- The degree-zero unit is the genuine original structure-sheaf unit. -/
theorem completeOrdinary_zero_one (M : X.left.Modules) (hM : IsInvertibleModule M) :
    completeOrdinaryInclusion (k := k) M hM 0 (1 : Γ(X.left, ⊤)) = 1 :=
  ActualSections.ordinaryHomogeneousSection_zero_one k (invertibleFractionalPresentation M hM)


end PaperVerification.ToricSchemes.SplitToricEmbedding



end
end Recovered_CompleteGraphicSectionRingAudited

#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.actualBoundarySectionRingEquiv
#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.IntegralGraphicBoundaryPresentation.polynomialMap_surjective
#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.IntegralGraphicBoundaryPresentation.theorem_6_10_complete_toric
