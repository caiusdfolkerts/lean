module
public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Order.Real
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.PiProd
public import Mathlib.Tactic.Ext
/-!
# Normal-projective equivalence and the exact cube bound

Independent statement of the main results of Caius Folkerts, paper.pdf.
A presentation consists of unit-normal irredundant facet inequalities for an
actual compact full-dimensional polytope. The topology is induced from the
normal/support coordinates. PN words count each admissible projectivity and
each equality-of-outward-unit-normals move separately. Affine transformations
are projective moves, rather than free operations in a counted word.

The custom definitions are copied independently with exact original names and
semantics. Proof fields needed only to construct these definitions are left
as Challenge holes; no mathematical data field is left unspecified. All of
their Solution values come from the complete original development. Source
locations and selection of equivalent README formulations are in map.json.
-/
@[expose] public section
noncomputable section
open Set Filter
open scoped BigOperators Topology
namespace NormalProjective.CanonicalModel

abbrev Space (d : ℕ) := Fin d → ℝ

def dot {d : ℕ} (v x : Space d) : ℝ :=
  ∑ j, v j * x j

def region {d : ℕ} {F : Type*} (n : F → Space d) (h : F → ℝ) :
    Set (Space d) :=
  {x | ∀ i, dot (n i) x ≤ h i}

def facetSet {d : ℕ} {F : Type*} (n : F → Space d) (h : F → ℝ)
    (i : F) : Set (Space d) :=
  {x ∈ region n h | dot (n i) x = h i}

/-- A finite, compact, full-dimensional, irredundant facet presentation.

The strict facet point says precisely that each displayed inequality is a facet
and is distinct from every other displayed facet. Its equivalence with the usual
facet-complete presentation is a separate geometric bridge to be proved.
-/
structure Presentation (d : ℕ) (F : Type*) [Fintype F] where
  normal : F → Space d
  support : F → ℝ
  unit_normal : ∀ i, (∑ j, (normal i j) ^ 2) = 1
  compact : IsCompact (region normal support)
  full_dimensional : (interior (region normal support)).Nonempty
  strict_facet_point : ∀ i, ∃ x ∈ region normal support,
    dot (normal i) x = support i ∧
      ∀ j, j ≠ i → dot (normal j) x < support j

namespace Presentation

variable {d : ℕ} {F : Type*} [Fintype F]

def carrier (P : Presentation d F) : Set (Space d) :=
  region P.normal P.support

def facet (P : Presentation d F) (i : F) : Set (Space d) :=
  facetSet P.normal P.support i

/-- The standard exposed-face predicate with the normed-space dictionaries used
throughout the halfspace geometry. This helper prevents a Pi-instance diamond. -/
abbrev NormedExposedFaces {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K : Set E) := {S : Set E // IsExposed ℝ K S}

/-- The actual exposed faces, ordered by inclusion of their underlying point sets. -/
abbrev Faces (P : Presentation d F) := NormedExposedFaces P.carrier

def Simple (P : Presentation d F) : Prop :=
  ∀ x ∈ P.carrier.extremePoints ℝ,
    Nat.card {i : F // x ∈ P.facet i} = d

instance : TopologicalSpace (Presentation d F) :=
  TopologicalSpace.induced (fun P => (P.normal, P.support)) inferInstance

/-- A face order isomorphism that preserves the specified facet labels. -/
def SameLabelledType (P Q : Presentation d F) : Prop :=
  ∃ e : P.Faces ≃o Q.Faces,
    ∀ i : F, ∃ s : P.Faces,
      (s : Set (Space d)) = P.facet i ∧
      (e s : Set (Space d)) = Q.facet i

end Presentation

variable {d : ℕ} {F : Type*} [Fintype F]

/-- Realizations of one fixed actual labelled face lattice. -/
abbrev Realization (R : Presentation d F) :=
  {P : Presentation d F // R.SameLabelledType P}

namespace Realization

variable {R : Presentation d F}

def carrier (P : Realization R) : Set (Space d) :=
  P.val.carrier

def facet (P : Realization R) (i : F) : Set (Space d) :=
  P.val.facet i

/-- Genuine labelled affine equivalence; no relabelling is silently quotiented out. -/
def AffineRelated (P Q : Realization R) : Prop :=
  ∃ a : Space d ≃ᵃ[ℝ] Space d,
    a '' P.carrier = Q.carrier ∧
      ∀ i : F, a '' P.facet i = Q.facet i

theorem affineRelated_refl (P : Realization R) : AffineRelated P P := by
  refine ⟨AffineEquiv.refl ℝ (Space d), ?_, ?_⟩
  · ext x
    simp
  · intro i
    ext x
    simp

theorem affineRelated_symm {P Q : Realization R}
    (h : AffineRelated P Q) : AffineRelated Q P := by
  obtain ⟨a, hP, hF⟩ := h
  refine ⟨a.symm, ?_, ?_⟩
  · rw [← hP, Set.image_image]
    simp
  · intro i
    rw [← hF i, Set.image_image]
    simp

theorem affineRelated_trans {P Q U : Realization R}
    (hPQ : AffineRelated P Q) (hQU : AffineRelated Q U) :
    AffineRelated P U := by
  obtain ⟨a, hPa, hFa⟩ := hPQ
  obtain ⟨b, hQb, hFb⟩ := hQU
  refine ⟨a.trans b, ?_, ?_⟩
  · change (fun x => b (a x)) '' P.carrier = U.carrier
    rw [← Set.image_image, hPa, hQb]
  · intro i
    change (fun x => b (a x)) '' P.facet i = U.facet i
    rw [← Set.image_image, hFa i, hFb i]

def affineSetoid (R : Presentation d F) : Setoid (Realization R) where
  r := AffineRelated
  iseqv :=
    ⟨affineRelated_refl, fun h => affineRelated_symm h,
      fun h₁ h₂ => affineRelated_trans h₁ h₂⟩

def AffineQuotient (R : Presentation d F) :=
  Quotient (affineSetoid R)

instance (R : Presentation d F) : TopologicalSpace (AffineQuotient R) :=
  TopologicalSpace.coinduced
    (Quotient.mk (affineSetoid R)) inferInstance

def affineClass (P : Realization R) : AffineQuotient R :=
  Quotient.mk (affineSetoid R) P

/-- Finite homogeneous coordinates; none is the affine denominator coordinate. -/
abbrev HomogeneousMatrix (d : ℕ) :=
  Matrix (Option (Fin d)) (Option (Fin d)) ℝ

def denominator (M : HomogeneousMatrix d) (x : Space d) : ℝ :=
  M none none + ∑ j, M none (some j) * x j

def numerator (M : HomogeneousMatrix d) (x : Space d) : Space d :=
  fun j => M (some j) none + ∑ k, M (some j) (some k) * x k

def projectiveMap (M : HomogeneousMatrix d) (x : Space d) : Space d :=
  fun j => numerator M x j / denominator M x

/-- An actual admissible projectivity, with the specified facet correspondence. -/
def ProjectiveStep (P Q : Realization R) : Prop :=
  ∃ M : HomogeneousMatrix d,
    M.det ≠ 0 ∧
    (∀ x ∈ P.carrier, denominator M x ≠ 0) ∧
    projectiveMap M '' P.carrier = Q.carrier ∧
    (∀ i : F, projectiveMap M '' P.facet i = Q.facet i)

/-- Equality of corresponding outward Euclidean unit normals. -/
def NormalStep (P Q : Realization R) : Prop :=
  P.val.normal = Q.val.normal

/-- Counts are part of the relation; every affine move must enter as a P-step. -/
inductive PNWord : Realization R → Realization R → ℕ → ℕ → Prop
  | nil (P : Realization R) : PNWord P P 0 0
  | projective {P Q U : Realization R} {p n : ℕ} :
      ProjectiveStep P Q → PNWord Q U p n → PNWord P U (p + 1) n
  | normal {P Q U : Realization R} {p n : ℕ} :
      NormalStep P Q → PNWord Q U p n → PNWord P U p (n + 1)

def PNRelated (P Q : Realization R) : Prop :=
  ∃ p n : ℕ, PNWord P Q p n

/-- Lemma 4: local words use d projective and d normal steps. -/
theorem local_word_neighbourhood {d : ℕ} {R : Presentation d F}
    (P : Realization R) (hs : P.val.Simple) :
    ∀ᶠ Q : Realization R in 𝓝 P, PNWord P Q d d := by sorry

/-- Theorem 1: PN classes are precisely connected components in the affine quotient. -/
theorem pnRelated_iff_same_component (hs : R.Simple) (P Q : Realization R) :
    PNRelated P Q ↔ affineClass Q ∈ connectedComponent (affineClass P) := by sorry
end Realization
end NormalProjective.CanonicalModel

namespace NormalProjective
/-- The region cut out by a finite list of linear inequalities. -/
def halfspaceRegion {E ι : Type*} [AddCommGroup E] [Module ℝ E]
    (f : ι → E →ₗ[ℝ] ℝ) (h : ι → ℝ) : Set E :=
  {x | ∀ i, f i x ≤ h i}
/-- Continuous real linear normal forms and their support numbers. -/
abbrev HalfspaceData (ι E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  (ι → E →L[ℝ] ℝ) × (ι → ℝ)
/-- The geometric intersection of the inequalities in a halfspace datum. -/
def dataRegion {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p : HalfspaceData ι E) : Set E :=
  halfspaceRegion (fun i => (p.1 i).toLinearMap) p.2

namespace UnitNormalization
abbrev Space := CanonicalModel.Space
/-- Continuous linear form whose coefficient vector is a. -/
def rowForm {d : ℕ} (a : Space d) : Space d →L[ℝ] ℝ :=
  ∑ j, a j • ContinuousLinearMap.proj j
/-- Standard coordinate coefficients of a linear form. -/
def coefficients {d : ℕ} (f : Space d →L[ℝ] ℝ) : Space d :=
  fun j => f (Pi.single j 1)
/-- Euclidean length of a facet normal. -/
def length {d : ℕ} (f : Space d →L[ℝ] ℝ) : ℝ :=
  Real.sqrt (∑ j, coefficients f j ^ 2)
/-- Outward unit normal obtained by positive row normalization. -/
def unitRow {d : ℕ} (f : Space d →L[ℝ] ℝ) : Space d :=
  fun j => coefficients f j / length f
/-- A compact full-dimensional irredundant halfspace system with nonzero normals. -/
structure RegularData (d : ℕ) (ι : Type*) [Fintype ι] where
  data : HalfspaceData ι (Space d)
  normal_ne_zero : ∀ i, data.1 i ≠ 0
  compact : IsCompact (dataRegion data)
  full_dimensional : (interior (dataRegion data)).Nonempty
  strict_facet_point : ∀ i, ∃ x ∈ dataRegion data,
    data.1 i x = data.2 i ∧ ∀ j, j ≠ i → data.1 j x < data.2 j
variable {d : ℕ} {ι : Type*} [Fintype ι]
/-- Positive Euclidean row normalization of a regular halfspace system. -/
def presentation (p : RegularData d ι) : CanonicalModel.Presentation d ι where
  normal := fun i => unitRow (p.data.1 i)
  support := fun i => p.data.2 i / length (p.data.1 i)
  unit_normal := by sorry
  compact := by sorry
  full_dimensional := by sorry
  strict_facet_point := by sorry
/-- Read a canonical presentation as its continuous halfspace forms and supports. -/
def ofCanonical (P : CanonicalModel.Presentation d ι) : RegularData d ι where
  data := (fun i => rowForm (P.normal i), P.support)
  normal_ne_zero := by sorry
  compact := by sorry
  full_dimensional := by sorry
  strict_facet_point := by sorry
end UnitNormalization

namespace LabelTransport
open CanonicalModel UnitNormalization
variable {d : ℕ} {V W : Type*} [Fintype V] [Fintype W]
/-- Reindex the same linear inequalities by a label equivalence. -/
def relabelData (p : HalfspaceData W (CanonicalModel.Space d)) (e : V ≃ W) :
    HalfspaceData V (CanonicalModel.Space d) := (fun i => p.1 (e i), fun i => p.2 (e i))
/-- Reindex a regular halfspace system; its data and geometry are unchanged. -/
def relabelRegular (q : RegularData d W) (e : V ≃ W) : RegularData d V where
  data := relabelData q.data e
  normal_ne_zero i := q.normal_ne_zero (e i)
  compact := by sorry
  full_dimensional := by sorry
  strict_facet_point := by sorry
end LabelTransport

namespace CanonicalModel.Presentation
open UnitNormalization LabelTransport
variable {d : ℕ} {V W : Type*} [Fintype V] [Fintype W]
/-- The identical geometric presentation indexed by an equivalent label type. -/
def relabel (Q : Presentation d W) (e : V ≃ W) : Presentation d V :=
  presentation (relabelRegular (ofCanonical Q) e)
/-- Reflexivity of equality of the actual labelled face lattice. -/
theorem sameLabelledType_refl (P : Presentation d V) : P.SameLabelledType P := by sorry
end CanonicalModel.Presentation

open CanonicalModel CanonicalModel.Realization
/-- Corollary 2 for every simple convex three-polytope, in its labelled space. -/
theorem simple_three_pn_unique {V : Type*} [Fintype V]
    {R : Presentation 3 V} (hR : R.Simple) (P Q : Realization R) : PNRelated P Q := by sorry
/-- Corollary 2 with arbitrary facet-label sets and an actual unlabelled face isomorphism. -/
theorem simple_three_faceOrderIso_pn {V W : Type*} [Fintype V] [Fintype W]
    (P : Presentation 3 V) (Q : Presentation 3 W)
    (hP : P.Simple) (e : P.Faces ≃o Q.Faces) :
    ∃ (l : V ≃ W) (h : P.SameLabelledType (Q.relabel l)),
      (Q.relabel l).carrier = Q.carrier ∧
      PNRelated (⟨P, Presentation.sameLabelledType_refl P⟩ : Realization P)
        ⟨Q.relabel l, h⟩ := by sorry
end NormalProjective

namespace NormalProjective.RootedGeometry
open UnitNormalization CanonicalModel
/-- The two opposite facet labels in each coordinate direction. -/
abbrev Labels (d : ℕ) := Sum (Fin d) (Fin d)
/-- Rooted inequalities -x_j <= 0 and (Ax)_i <= 1. -/
def rootedData {d : ℕ} (A : Matrix (Fin d) (Fin d) ℝ) :
    HalfspaceData (Labels d) (CanonicalModel.Space d) :=
  (Sum.elim (fun j => -ContinuousLinearMap.proj j) (fun i => rowForm (A i)),
    Sum.elim (fun _ => 0) (fun _ => 1))
end NormalProjective.RootedGeometry

namespace NormalProjective.RankObstruction
/-- Cyclic successor in n+1 coordinates. -/
def cyclicSucc (n : ℕ) (i : Fin (n + 1)) : Fin (n + 1) :=
  if h : i.val + 1 < n + 1 then ⟨i.val + 1, h⟩ else 0
/-- Identity plus epsilon times the cyclic successor matrix. -/
def cyclicMatrix (n : ℕ) (ε : ℝ) : Matrix (Fin (n + 1)) (Fin (n + 1)) ℝ :=
  fun i j => (if i = j then 1 else 0) + if cyclicSucc n i = j then ε else 0
end NormalProjective.RankObstruction

namespace NormalProjective.CyclicCube
open UnitNormalization CanonicalModel CanonicalModel.Realization RootedGeometry RankObstruction
variable {n : ℕ}
/-- Ambient coordinates of the (n+1)-cube family. -/
abbrev E (n : ℕ) := Fin (n + 1) → ℝ
/-- The cyclic cube inequalities. -/
def cubeData (n : ℕ) (ε : ℝ) := rootedData (cyclicMatrix n ε)
/-- The regular halfspace presentation of the cyclic cube family. -/
def cyclicRegular {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) :
    RegularData (n + 1) (Labels (n + 1)) where
  data := cubeData n ε
  normal_ne_zero := by sorry
  compact := by sorry
  full_dimensional := by sorry
  strict_facet_point := by sorry
/-- The reference realization is literally the ordinary closed unit cube. -/
def referenceCube (n : ℕ) : Presentation (n + 1) (Labels (n + 1)) :=
  presentation (cyclicRegular (n := n) (ε := 0) le_rfl zero_lt_one)
/-- Cyclic cube inequalities realized in the fixed labelled cube type. -/
def realization {ε : ℝ} (hε0 : 0 ≤ ε) (hε1 : ε < 1) : Realization (referenceCube n) :=
  ⟨presentation (cyclicRegular hε0 hε1), by sorry⟩
end NormalProjective.CyclicCube

namespace NormalProjective.CubeUpper
open CanonicalModel CanonicalModel.Realization CyclicCube
/-- Theorem 3 upper bound, from any actual face-order isomorphism: d-1
projective and d-2 normal moves with ambient dimension d=n+1. -/
theorem every_cube_exact_word_of_faceOrderIso
    {V : Type*} [Fintype V] {n : ℕ} (hn : 1 ≤ n)
    (P : Presentation (n + 1) V)
    (e : P.Faces ≃o (referenceCube n).Faces) :
    ∃ (Q : Presentation (n + 1) V) (hPQ : P.SameLabelledType Q),
      Q.carrier = Set.Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)) ∧
      PNWord (⟨P, Presentation.sameLabelledType_refl P⟩ : Realization P)
        ⟨Q, hPQ⟩ n (n - 1) := by sorry
end NormalProjective.CubeUpper

namespace NormalProjective.CubeTargetLabels
open CanonicalModel CanonicalModel.Realization CyclicCube
variable {n : ℕ}
/-- Theorem 3 lower bound for each cyclic member and every target labelling. -/
theorem cyclic_to_geometric_cube_lower_bound {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1)
    (hn : 1 ≤ n) (Q : Realization (referenceCube n))
    (hQ : Q.carrier = Set.Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)))
    {p q : ℕ} (hword : PNWord (CyclicCube.realization hε0.le hε1) Q p q) :
    n ≤ p ∧ n - 1 ≤ q ∧ 2 * (n + 1) - 3 ≤ p + q := by sorry
/-- Total length k of a word ending at the geometric cube with any induced labels. -/
def GeometricLength (P : Realization (referenceCube n)) (k : ℕ) : Prop :=
  ∃ Q : Realization (referenceCube n), ∃ p q : ℕ,
    Q.carrier = Set.Icc (fun _ => (-1 : ℝ)) (fun _ => (1 : ℝ)) ∧
      PNWord P Q p q ∧ p + q = k
/-- Every cube realization has a finite length to the geometric cube. -/
theorem geometricLength_exists (hn : 1 ≤ n) (P : Realization (referenceCube n)) :
    ∃ k : ℕ, GeometricLength P k := by sorry
/-- The least total length to the geometric cube, allowing all endpoint labels. -/
def geometricPNDistance (hn : 1 ≤ n) (P : Realization (referenceCube n)) : ℕ := by
  classical
  exact Nat.find (geometricLength_exists hn P)
/-- Theorem 3: the exact largest distance is 2d-3 in every d=n+1 >= 2. -/
theorem geometric_largest_PN_distance (hn : 1 ≤ n) :
    IsGreatest (Set.range (geometricPNDistance hn)) (2 * (n + 1) - 3) := by sorry
end NormalProjective.CubeTargetLabels

namespace NormalProjective.PolarCorrection
/-- One-dimensional polar body. -/
def polar (K : Set ℝ) : Set ℝ := {y | ∀ x ∈ K, x * y ≤ 1}
/-- Translation of the body by minus the recentering point. -/
def recentered (K : Set ℝ) (o : ℝ) : Set ℝ := (fun x => x - o) '' K
/-- Fractional map appearing in the auxiliary polarity identity. -/
def fractionalRecenter (o x : ℝ) : ℝ := x / (1 - x * o)
/-- Correction to the auxiliary identity: boundary origin does not suffice. -/
theorem boundary_origin_counterexample :
    IsCompact (Set.Icc (0 : ℝ) 1) ∧ Convex ℝ (Set.Icc (0 : ℝ) 1) ∧
    (0 : ℝ) ∈ Set.Icc 0 1 ∧ (1 / 2 : ℝ) ∈ interior (Set.Icc 0 1) ∧
    polar (recentered (Set.Icc 0 1) (1 / 2)) ≠
      fractionalRecenter (1 / 2) '' polar (Set.Icc 0 1) := by sorry
end NormalProjective.PolarCorrection
