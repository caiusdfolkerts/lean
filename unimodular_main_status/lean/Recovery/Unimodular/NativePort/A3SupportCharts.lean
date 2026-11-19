module

public import Recovery.Unimodular.NativePort.A3Enumeration
public import Unimodular.A3SupportSignRealization
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Logic.Equiv.Prod

@[expose] public section

/-! UNVERIFIED until the exact native compiler run succeeds.
Actual six-square coordinates, full-dimensional cell cones, and
explicit linear facet support points. No full projectivity claim. -/

/- Exact current draft body: A3FacetSupports. -/
section SupportCharts_A3FacetSupports



/-!
UNVERIFIED EXTENSION DRAFT. Explicit linear support points on the actual A3
cut facets. The four square corners are ac,bc,bd,ad. The displayed square
defect is exactly h_ac+h_bd-h_ad-h_bc. The formulas keep all twelve directed
root heights independent and also cover the unsplit square when the defect
vanishes. These are linear support points, not an assumed projectivity test.
-/

set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators

namespace Unimodular.A3FacetSupports

open TypeAFanGeometry

abbrev Labels := Fin 4 ≃ Vertex 3
abbrev HeightMatrix := Fin 4 → Fin 4 → ℝ

/-- Potentials on the four vertices induce actual linear functionals on
the original three-dimensional ambient lattice space. -/
def potentialMap (e : Labels) : (Fin 4 → ℝ) →ₗ[ℝ] Module.Dual ℝ (Ambient 3) where
  toFun t :=
    { toFun := fun x => ∑ k : Fin 4, t k * augmented 3 x (e k)
      map_add' := by
        intro x y
        simp only [map_add,Pi.add_apply,mul_add,Finset.sum_add_distrib]
      map_smul' := by
        intro a x
        change (∑ k : Fin 4, t k * augmented 3 (a • x) (e k)) =
          a * (∑ k : Fin 4, t k * augmented 3 x (e k))
        simp only [map_smul,Pi.smul_apply,smul_eq_mul,Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro k hk
        ring }
  map_add' := by
    intro t s
    apply LinearMap.ext
    intro x
    change (∑ k : Fin 4, (t k + s k) * augmented 3 x (e k)) =
      (∑ k : Fin 4, t k * augmented 3 x (e k)) +
        (∑ k : Fin 4, s k * augmented 3 x (e k))
    simp only [add_mul,Finset.sum_add_distrib]
  map_smul' := by
    intro a t
    apply LinearMap.ext
    intro x
    change (∑ k : Fin 4, (a * t k) * augmented 3 x (e k)) =
      a * (∑ k : Fin 4, t k * augmented 3 x (e k))
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k hk
    ring

@[simp] theorem potentialMap_root (e : Labels) (t : Fin 4 → ℝ) (a b : Fin 4) :
    potentialMap e t (realRoot (e a) (e b)) = t a - t b := by
  simp [potentialMap,augmented_root,Pi.single_apply,e.injective.eq_iff,
    mul_sub,Finset.sum_sub_distrib]

def squarePairs : Fin 4 → Fin 4 × Fin 4 := ![(0,2),(1,2),(1,3),(0,3)]

def squareDefect (h : HeightMatrix) : ℝ := h 0 2 + h 1 3 - h 0 3 - h 1 2

/-- Index i specifies the corner omitted by a triangular maximal cell.
For a whole square one may use i=0; vanishing defect makes all four
interpolation equations hold. -/
def squareCoefficients (i : Fin 4) : HeightMatrix →ₗ[ℝ] (Fin 4 → ℝ) where
  toFun h := ![
    ![h 0 3,h 1 3,h 1 3-h 1 2,0],
    ![h 0 3,h 1 3,h 0 3-h 0 2,0],
    ![h 0 3,h 1 2+h 0 3-h 0 2,h 0 3-h 0 2,0],
    ![h 0 2+h 1 3-h 1 2,h 1 3,h 1 3-h 1 2,0]] i
  map_add' := by
    intro h k
    ext j
    fin_cases i <;> fin_cases j <;> simp <;> ring
  map_smul' := by
    intro a h
    ext j
    fin_cases i <;> fin_cases j <;> simp [smul_eq_mul] <;> ring

def squarePoint (e : Labels) (i : Fin 4) :
    HeightMatrix →ₗ[ℝ] Module.Dual ℝ (Ambient 3) :=
  (potentialMap e).comp (squareCoefficients i)

def alternatingSign : Fin 4 → ℝ := ![1,-1,1,-1]

/-- Every interpolation residual is computed exactly. In particular,
omitting corners 0 or 2 requires positive square defect, and omitting
corners 1 or 3 requires negative square defect. -/
theorem squarePoint_residual (e : Labels) (h : HeightMatrix) (i j : Fin 4) :
    h (squarePairs j).1 (squarePairs j).2 -
      squarePoint e i h (realRoot (e (squarePairs j).1) (e (squarePairs j).2)) =
        if j = i then alternatingSign i * squareDefect h else 0 := by
  rw [show squarePoint e i h = potentialMap e (squareCoefficients i h) from rfl,
    potentialMap_root]
  fin_cases i <;> fin_cases j <;>
    simp [squareCoefficients,squarePairs,alternatingSign,squareDefect] <;> ring

theorem squarePoint_on_corner (e : Labels) (h : HeightMatrix) (i j : Fin 4)
    (hji : j ≠ i) :
    squarePoint e i h (realRoot (e (squarePairs j).1) (e (squarePairs j).2)) =
      h (squarePairs j).1 (squarePairs j).2 := by
  have hr := squarePoint_residual e h i j
  rw [if_neg hji] at hr
  exact (sub_eq_zero.mp hr).symm

theorem squarePoint_whole (e : Labels) (h : HeightMatrix) (hz : squareDefect h = 0)
    (j : Fin 4) :
    squarePoint e 0 h (realRoot (e (squarePairs j).1) (e (squarePairs j).2)) =
      h (squarePairs j).1 (squarePairs j).2 := by
  have hr := squarePoint_residual e h 0 j
  simp only [hz,mul_zero,ite_self] at hr
  exact (sub_eq_zero.mp hr).symm

theorem squarePoint_missing_strict (e : Labels) (h : HeightMatrix) (i : Fin 4)
    (hpos : 0 < alternatingSign i * squareDefect h) :
    squarePoint e i h (realRoot (e (squarePairs i).1) (e (squarePairs i).2)) <
      h (squarePairs i).1 (squarePairs i).2 := by
  have hr := squarePoint_residual e h i i
  rw [if_pos rfl] at hr
  linarith

/-- The literal vector relation of the four square rays. -/
theorem square_root_relation (e : Labels) :
    realRoot (e 0) (e 2) + realRoot (e 1) (e 3) =
      realRoot (e 0) (e 3) + realRoot (e 1) (e 2) := by
  have h : augmented 3 (realRoot (e 0) (e 2) + realRoot (e 1) (e 3)) =
      augmented 3 (realRoot (e 0) (e 3) + realRoot (e 1) (e 2)) := by
    simp only [map_add,augmented_root]
    abel
  funext j
  exact congrFun h (some j)

/-- Every actual linear functional satisfies the square relation. -/
theorem squareDefect_evaluation (e : Labels) (p : Module.Dual ℝ (Ambient 3)) :
    squareDefect (fun a b => p (realRoot (e a) (e b))) = 0 := by
  have h := congrArg p (square_root_relation e)
  simp only [map_add] at h
  unfold squareDefect
  linarith

theorem squareDefect_eq_missing_residual (e : Labels) (h : HeightMatrix)
    (p : Module.Dual ℝ (Ambient 3)) (i : Fin 4)
    (hon : ∀ j : Fin 4, j ≠ i →
      p (realRoot (e (squarePairs j).1) (e (squarePairs j).2)) =
        h (squarePairs j).1 (squarePairs j).2) :
    alternatingSign i * squareDefect h = h (squarePairs i).1 (squarePairs i).2 -
      p (realRoot (e (squarePairs i).1) (e (squarePairs i).2)) := by
  have hc := squareDefect_evaluation e p
  fin_cases i
  all_goals
    have h0 := hon 0
    have h1 := hon 1
    have h2 := hon 2
    have h3 := hon 3
    norm_num [squarePairs,squareDefect,alternatingSign] at h0 h1 h2 h3 hc ⊢
    linarith

/-- The strict sign is necessary, because an actual full-cone supporting
functional interpolates its three rays and is strictly below the omitted ray. -/
theorem squareDefect_strict_of_support (e : Labels) (h : HeightMatrix)
    (p : Module.Dual ℝ (Ambient 3)) (i : Fin 4)
    (hon : ∀ j : Fin 4, j ≠ i →
      p (realRoot (e (squarePairs j).1) (e (squarePairs j).2)) =
        h (squarePairs j).1 (squarePairs j).2)
    (hoff : p (realRoot (e (squarePairs i).1) (e (squarePairs i).2)) <
      h (squarePairs i).1 (squarePairs i).2) :
    0 < alternatingSign i * squareDefect h := by
  rw [squareDefect_eq_missing_residual e h p i hon]
  exact sub_pos.mpr hoff

theorem squareDefect_zero_of_whole_support (e : Labels) (h : HeightMatrix)
    (p : Module.Dual ℝ (Ambient 3))
    (hon : ∀ j : Fin 4,
      p (realRoot (e (squarePairs j).1) (e (squarePairs j).2)) =
        h (squarePairs j).1 (squarePairs j).2) : squareDefect h = 0 := by
  have hc := squareDefect_evaluation e p
  have h0 := hon 0
  have h1 := hon 1
  have h2 := hon 2
  have h3 := hon 3
  norm_num [squarePairs,squareDefect] at h0 h1 h2 h3 hc ⊢
  linarith

def singletonCoefficients : HeightMatrix →ₗ[ℝ] (Fin 4 → ℝ) where
  toFun h := ![0,-h 0 1,-h 0 2,-h 0 3]
  map_add' := by intro h k; ext j; fin_cases j <;> simp <;> ring
  map_smul' := by intro a h; ext j; fin_cases j <;> simp

def tripleCoefficients : HeightMatrix →ₗ[ℝ] (Fin 4 → ℝ) where
  toFun h := ![h 0 3,h 1 3,h 2 3,0]
  map_add' := by intro h k; ext j; fin_cases j <;> simp
  map_smul' := by intro a h; ext j; fin_cases j <;> simp

def singletonPoint (e : Labels) := (potentialMap e).comp singletonCoefficients
def triplePoint (e : Labels) := (potentialMap e).comp tripleCoefficients

theorem singletonPoint_on_root (e : Labels) (h : HeightMatrix) (j : Fin 4)
    (hj : j ≠ 0) : singletonPoint e h (realRoot (e 0) (e j)) = h 0 j := by
  change potentialMap e (singletonCoefficients h) _ = _
  rw [potentialMap_root]
  fin_cases j <;> simp_all [singletonCoefficients]

theorem triplePoint_on_root (e : Labels) (h : HeightMatrix) (j : Fin 4)
    (hj : j ≠ 3) : triplePoint e h (realRoot (e j) (e 3)) = h j 3 := by
  change potentialMap e (tripleCoefficients h) _ = _
  rw [potentialMap_root]
  fin_cases j <;> simp_all [tripleCoefficients]

/-- Constant unit heights give precisely the ordinary cut support values,
independently of which square triangle was used for interpolation. -/
theorem squarePoint_unit (e : Labels) (i a b : Fin 4) :
    squarePoint e i (fun _ _ => 1) (realRoot (e a) (e b)) =
      (if a ∈ ({0,1} : Finset (Fin 4)) then 1 else 0) -
        (if b ∈ ({0,1} : Finset (Fin 4)) then 1 else 0) := by
  change potentialMap e (squareCoefficients i (fun _ _ => 1)) _ = _
  rw [potentialMap_root]
  fin_cases i <;> fin_cases a <;> fin_cases b <;> norm_num [squareCoefficients]

theorem singletonPoint_unit (e : Labels) (a b : Fin 4) :
    singletonPoint e (fun _ _ => 1) (realRoot (e a) (e b)) =
      (if a = 0 then 1 else 0) - (if b = 0 then 1 else 0) := by
  change potentialMap e (singletonCoefficients (fun _ _ => 1)) _ = _
  rw [potentialMap_root]
  fin_cases a <;> fin_cases b <;> norm_num [singletonCoefficients]

theorem triplePoint_unit (e : Labels) (a b : Fin 4) :
    triplePoint e (fun _ _ => 1) (realRoot (e a) (e b)) =
      (if a ≠ 3 then 1 else 0) - (if b ≠ 3 then 1 else 0) := by
  change potentialMap e (tripleCoefficients (fun _ _ => 1)) _ = _
  rw [potentialMap_root]
  fin_cases a <;> fin_cases b <;> norm_num [tripleCoefficients]

#print axioms potentialMap_root
#print axioms squarePoint_residual
#print axioms squarePoint_whole
#print axioms squarePoint_missing_strict
#print axioms squareDefect_strict_of_support
#print axioms squareDefect_zero_of_whole_support
#print axioms singletonPoint_on_root
#print axioms triplePoint_on_root
#print axioms squarePoint_unit

end Unimodular.A3FacetSupports
end

end SupportCharts_A3FacetSupports

/- Exact current draft body: A3CanonicalSigns. -/
section SupportCharts_A3CanonicalSigns



/-!
UNVERIFIED EXTENSION DRAFT. Canonical coordinates on the six actual square
facets, in source-cut order 01,02,03,12,13,23. These give a literal equivalence
from actual complete fans to six signs. Their order matches A3SupportForms;
projectivity is not defined or assumed by a condition on these signs.
-/

set_option maxHeartbeats 0
set_option maxRecDepth 10000
set_option backward.isDefEq.respectTransparency false
noncomputable section

namespace Unimodular.A3CanonicalSigns

open TypeAFanGeometry A3FacetCharts A3FanChoices A3RegularFanCount
open TauCeti.Toric

def order : Fin 6 → Fin 4 → Fin 4 :=
  ![![0,1,2,3],![0,2,1,3],![0,3,1,2],
    ![1,2,0,3],![1,3,0,2],![2,3,0,1]]

theorem order_bijective : ∀ i : Fin 6, Function.Bijective (order i) := by decide

def labels (i : Fin 6) : Labels :=
  (Equiv.ofBijective (order i) (order_bijective i)).trans (finSuccEquiv 3)

theorem squareCut_card (e : Labels) : (squareCut e).card = 2 := by
  have h01 : e 0 ≠ e 1 := e.injective.ne (by decide : (0 : Fin 4) ≠ 1)
  simp [squareCut,h01]

def indexedCut (i : Fin 6) : ProperCut 3 :=
  ⟨squareCut (labels i),⟨labels i 0,by simp [squareCut]⟩,by
    intro he
    have hc := congrArg Finset.card he
    rw [squareCut_card,Finset.card_univ] at hc
    norm_num at hc⟩

abbrev SquareCut := {S : ProperCut 3 // S.val.card = 2}
abbrev TriangularCut := {S : ProperCut 3 // S.val.card ≠ 2}

def indexedSquareCut (i : Fin 6) : SquareCut :=
  ⟨indexedCut i,squareCut_card (labels i)⟩

theorem indexedSquareCut_bijective : Function.Bijective indexedSquareCut := by
  decide

def squareCutIndexEquiv : Fin 6 ≃ SquareCut :=
  Equiv.ofBijective indexedSquareCut indexedSquareCut_bijective

abbrev CutFamily := ∀ S : ProperCut 3, VertexSubdivision (cutFace S.val)

/-- Reindex the six actual square facets and apply the actual affine-chart
subdivision equivalence separately to each one. -/
def squareFactorEquiv :
    (∀ S : SquareCut, VertexSubdivision (cutFace S.val.val)) ≃
      (Fin 6 → Option Bool) :=
  ((Equiv.piCongrLeft (fun S : SquareCut => VertexSubdivision (cutFace S.val.val))
      squareCutIndexEquiv).symm).trans
    (Equiv.piCongrRight (fun i => squareFacetSubdivisionEquiv (labels i)))

/-- The eight triangular facets contribute a genuinely unique subdivision,
as proved geometrically earlier. -/
def triangularFactorEquiv :
    (∀ S : TriangularCut, VertexSubdivision (cutFace S.val.val)) ≃ PUnit.{1} := by
  let f (S : TriangularCut) : VertexSubdivision (cutFace S.val.val) ≃ PUnit.{1} :=
    (cutSubdivisionEquiv S.val).trans (Equiv.cast (by
      simp only [CutChoice,if_neg S.property]))
  exact (Equiv.piCongrRight f).trans (Equiv.ofUnique _ _)

/-- Independent facet subdivisions are identified with the six canonical
square choices. No additional compatibility conditions are discarded. -/
def cutFamilySixEquiv : CutFamily ≃ (Fin 6 → Option Bool) :=
  (Equiv.piEquivPiSubtypeProd (fun S : ProperCut 3 => S.val.card = 2)
    (fun S => VertexSubdivision (cutFace S.val))).trans
      ((Equiv.prodCongr squareFactorEquiv triangularFactorEquiv).trans (Equiv.prodPUnit _))

@[simp] theorem cutFamilySixEquiv_apply (D : CutFamily) (i : Fin 6) :
    cutFamilySixEquiv D i = squareFacetSubdivisionEquiv (labels i) (D (indexedCut i)) := by
  rfl

def choiceSignEquiv : Option Bool ≃ SignType where
  toFun c := match c with | none => 0 | some false => 1 | some true => -1
  invFun s := match s with | .zero => none | .pos => some false | .neg => some true
  left_inv c := by cases c with | none => rfl | some b => cases b <;> rfl
  right_inv s := by cases s <;> rfl

theorem choiceSign_nonzero (c : Option Bool) : choiceSignEquiv c ≠ 0 ↔ c ≠ none := by
  cases c with
  | none => simp [choiceSignEquiv]
  | some b => cases b <;> simp [choiceSignEquiv]

/-- Actual complete root fans correspond to the ordered six signs; positive
chooses diagonal bc-ad, negative chooses ac-bd, and zero keeps the square. -/
def a3SignEquiv : CompleteRootFan ≃ (Fin 6 → SignType) :=
  (fanSubdivisionEquiv (n := 3) (by decide)).trans
    (independentCutSubdivisionsEquiv.trans
      (cutFamilySixEquiv.trans (Equiv.piCongrRight (fun _ => choiceSignEquiv))))

@[simp] theorem a3SignEquiv_apply (Φ : CompleteRootFan) (i : Fin 6) :
    a3SignEquiv Φ i = choiceSignEquiv (squareFacetSubdivisionEquiv (labels i)
      ((fanCutSubdivisions Φ.val Φ.property.1 Φ.property.2).subdivision (indexedCut i))) := by
  rfl

/-- The defect in each canonical chart is the corresponding actual support
form, with no coordinate sign change or opposite-root symmetry suppressed. -/
theorem ordered_square_defect (h : A3SupportForms.Heights) (i : Fin 6) :
    A3SupportForms.height h (order i 0) (order i 2) +
      A3SupportForms.height h (order i 1) (order i 3) -
      A3SupportForms.height h (order i 0) (order i 3) -
      A3SupportForms.height h (order i 1) (order i 2) = A3SupportForms.forms h i := by
  fin_cases i <;> simp [order,A3SupportForms.forms]

#print axioms indexedSquareCut_bijective
#print axioms cutFamilySixEquiv
#print axioms a3SignEquiv
#print axioms ordered_square_defect

end Unimodular.A3CanonicalSigns
end

end SupportCharts_A3CanonicalSigns

/- Exact current draft body: A3SquareCones. -/
section SupportCharts_A3SquareCones



/-!
UNVERIFIED EXTENSION DRAFT. Actual cones over the square cells are full
dimensional at every maximal cell, and contain precisely the corresponding
square rays. These facts supply the geometric content needed when the
support-height equations are evaluated on a complete fan.
-/

set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set

namespace Unimodular.A3SquareCones

open TypeAFanGeometry A3FacetCharts SquareSubdivision SubdivisionTriangulations
open VertexSubdivisionTransport

def cellSet (e : Labels) (s : Key) : Set (Ambient 3) := squareChart e '' hull s
def cellCone (e : Labels) (s : Key) : PointedCone ℝ (Ambient 3) :=
  PointedCone.hull ℝ (cellSet e s)

theorem cellSet_convex (e : Labels) (s : Key) : Convex ℝ (cellSet e s) :=
  (convex_convexHull ℝ _).affine_image (squareChart e)

theorem cellSet_subset_facet (e : Labels) (s : Key) :
    cellSet e s ⊆ cutFace (squareCut e) := by
  rw [← squareChart_image e]
  exact Set.image_mono (hull_mono (Finset.subset_univ s))

theorem cellSet_level (e : Labels) (s : Key) {x : Ambient 3} (hx : x ∈ cellSet e s) :
    cutFunctional (squareCut e) x = 1 := (cellSet_subset_facet e s hx).2

theorem corner_level (e : Labels) (j : Fin 4) :
    cutFunctional (squareCut e)
      (realRoot (e (squarePairs j).1) (e (squarePairs j).2)) = 1 := by
  rw [← squareChart_vertex e j]
  exact cellSet_level e Finset.univ
    ⟨vertex j,(vertex_mem_hull j).mpr (Finset.mem_univ j),rfl⟩

/-- Conic hull membership of a normalized root is ordinary cell membership,
so no extra square ray enters a triangle cone. -/
theorem corner_mem_cellCone (e : Labels) (s : Key) (j : Fin 4) :
    realRoot (e (squarePairs j).1) (e (squarePairs j).2) ∈ cellCone e s ↔ j ∈ s := by
  constructor
  · intro hj
    have hsection := (NormalizedConeFaces.slice_hull (cellSet e s) (cellSet_convex e s)
      (cutFunctional (squareCut e)) (fun x hx => cellSet_level e s hx)).subset
        ⟨hj,corner_level e j⟩
    obtain ⟨x,hx,heq⟩ := hsection
    rw [← squareChart_vertex e j] at heq
    have hxv : x = vertex j := squareChart_injective e heq
    exact (vertex_mem_hull j).mp (hxv ▸ hx)
  · intro hj
    rw [← squareChart_vertex e j]
    exact PointedCone.subset_hull ⟨vertex j,(vertex_mem_hull j).mpr hj,rfl⟩

/-- The three actual roots above any square triangle are linearly independent
in the original ambient space, not merely affinely independent in a chart. -/
theorem triangle_roots_linearIndependent (e : Labels) (i : Fin 4) :
    LinearIndependent ℝ (fun j : Fin 3 => squareChart e (triangleVertices i j)) := by
  have ha : AffineIndependent ℝ
      (fun j : Fin 3 => squareChart e (triangleVertices i j)) :=
    ((squareChart e).affineIndependent_iff (squareChart_injective e)).mpr
      (triangleVertices_affineIndependent i)
  apply (NormalizedConeFaces.affineIndependent_iff_linearIndependent _
    (cutFunctional (squareCut e)) ?_).mp ha
  intro j
  apply cellSet_level e (triangle i)
  refine ⟨triangleVertices i j,?_,rfl⟩
  exact (vertex_mem_hull _).mpr ((triangle_index_range i _).mpr ⟨j,rfl⟩)

theorem cellCone_triangle_full (e : Labels) (i : Fin 4) :
    Submodule.span ℝ (cellCone e (triangle i) : Set (Ambient 3)) = ⊤ := by
  have hspan := (triangle_roots_linearIndependent e i).span_eq_top_of_card_eq_finrank'
    (by simp [Ambient])
  apply top_unique
  rw [← hspan]
  apply Submodule.span_mono
  rintro x ⟨j,rfl⟩
  exact PointedCone.subset_hull ⟨triangleVertices i j,
    (vertex_mem_hull _).mpr ((triangle_index_range i _).mpr ⟨j,rfl⟩),rfl⟩

theorem cellCone_mono (e : Labels) {s t : Key} (hst : s ⊆ t) :
    cellCone e s ≤ cellCone e t :=
  Submodule.span_mono (Set.image_mono (hull_mono hst))

theorem cellCone_square_full (e : Labels) :
    Submodule.span ℝ (cellCone e Finset.univ : Set (Ambient 3)) = ⊤ := by
  apply top_unique
  rw [← cellCone_triangle_full e 0]
  exact Submodule.span_mono (cellCone_mono e (Finset.subset_univ _))

theorem maximal_cellCone_full (e : Labels) (c : Option Bool) {s : Key}
    (hs : s ∈ maximalKeys c) :
    Submodule.span ℝ (cellCone e s : Set (Ambient 3)) = ⊤ := by
  cases c with
  | none =>
    have he : s = Finset.univ := by simpa only [maximalKeys,Finset.mem_singleton] using hs
    subst s
    exact cellCone_square_full e
  | some b =>
    cases b
    · simp only [maximalKeys,Finset.mem_insert,Finset.mem_singleton] at hs
      rcases hs with rfl | rfl <;> exact cellCone_triangle_full e _
    · simp only [maximalKeys,Finset.mem_insert,Finset.mem_singleton] at hs
      rcases hs with rfl | rfl <;> exact cellCone_triangle_full e _

/-- Membership in the pullback cell family is reflected by the actual
injective affine map; no surjectivity on ambient spaces is needed. -/
theorem pullback_cell_iff {V W : Type*} [AddCommGroup V] [Module ℝ V]
    [AddCommGroup W] [Module ℝ W] (f : V →ᵃ[ℝ] W) (hf : Function.Injective f)
    {P : Set V} (D : VertexSubdivision (f '' P)) (F : Set V) :
    F ∈ (pullback f hf D).cells ↔ f '' F ∈ D.cells := by
  constructor
  · rintro ⟨G,hG,hF⟩
    change f ⁻¹' G = F at hF
    have he : f '' (f ⁻¹' G) = G := Set.image_preimage_eq_iff.mpr
      ((D.cell_subset hG).trans (Set.image_subset_range f P))
    rw [← hF,he]
    exact hG
  · intro hF
    exact ⟨f '' F,hF,Set.preimage_image_eq F hf⟩

theorem cast_cell_iff {V : Type*} [AddCommGroup V] [Module ℝ V]
    {P Q : Set V} (h : P = Q) (D : VertexSubdivision P) (F : Set V) :
    F ∈ (Equiv.cast (congrArg (fun A => VertexSubdivision A) h) D).cells ↔
      F ∈ D.cells := by
  subst Q
  rfl

/-- Every square coordinate is connected to its exact family of geometric
cells in the original ambient space. -/
theorem facet_cell_iff (e : Labels)
    (D : VertexSubdivision (cutFace (squareCut e))) (s : Key) :
    cellSet e s ∈ D.cells ↔ s ∈ catalogue (squareFacetSubdivisionEquiv e D) := by
  let E := (Equiv.cast (congrArg (fun P : Set (Ambient 3) => VertexSubdivision P)
    (squareChart_image e).symm)) D
  let D' := (affineEmbeddingEquiv (squareChart e) (squareChart_injective e) square).symm E
  have hc : cellSet e s ∈ D.cells ↔ hull s ∈ D'.cells := by
    rw [← cast_cell_iff (squareChart_image e).symm D (cellSet e s)]
    exact (pullback_cell_iff (squareChart e) (squareChart_injective e) E (hull s)).symm
  rw [hc]
  have hD' : D' = canonicalSubdivision (squareSubdivisionEquiv D') :=
    (squareSubdivisionEquiv.symm_apply_apply D').symm
  rw [hD',hull_mem_canonical]
  rfl

#print axioms corner_mem_cellCone
#print axioms triangle_roots_linearIndependent
#print axioms maximal_cellCone_full
#print axioms facet_cell_iff

end Unimodular.A3SquareCones
end

end SupportCharts_A3SquareCones

#check "UNIMODULAR_A3_SUPPORT_CHARTS_EOF_V2"
