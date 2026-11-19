module
public import cubical.polytope.face_order
public import papers.complete_face_lattice
public import Mathlib.Algebra.Field.Subfield.Basic
public import Mathlib.Algebra.Group.Pointwise.Set.Basic
public import Mathlib.Combinatorics.SimpleGraph.Finite
public import Mathlib.Analysis.Real.Sqrt

@[expose] public section

/-!
# Exact geometric targets for the two polytope papers

All objects below are actual finite convex hulls with their extreme vertices.
Faces are exposed faces, and combinatorial equivalence is an order isomorphism
of their ordinary face posets. In particular, neither field realizability nor
Minkowski decomposability is encoded by a conclusion to be proved.

The declarations ending in `Claim` are proposition-valued definitions recording
the original targets. Their presence does NOT assert or prove these claims.
-/

noncomputable section

open Set
open scoped Classical
open scoped Pointwise
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

namespace Papers.Polytopes

variable {d : ℕ}

/-- The actual combinatorial equivalence relation on nonempty face posets.
The omitted empty face can be adjoined as a new least element. -/
def CombinatoriallyEquivalent (P Q : ConvexPolytope d) : Prop :=
  Nonempty (FaceType P ≃o FaceType Q)

/-- Adjoining the empty face gives exactly the ordinary complete face-lattice
notion of combinatorial equivalence. -/
theorem combinatoriallyEquivalent_iff_complete_face_iso (P Q : ConvexPolytope d) :
    CombinatoriallyEquivalent P Q ↔
      Nonempty (CompleteFaceType P ≃o CompleteFaceType Q) :=
  nonempty_face_iso_iff_complete_face_iso P Q

theorem CombinatoriallyEquivalent.refl (P : ConvexPolytope d) :
    CombinatoriallyEquivalent P P := ⟨OrderIso.refl _⟩

theorem CombinatoriallyEquivalent.symm {P Q : ConvexPolytope d}
    (h : CombinatoriallyEquivalent P Q) : CombinatoriallyEquivalent Q P :=
  h.elim (fun e => ⟨e.symm⟩)

theorem CombinatoriallyEquivalent.trans {P Q R : ConvexPolytope d}
    (h₁ : CombinatoriallyEquivalent P Q) (h₂ : CombinatoriallyEquivalent Q R) :
    CombinatoriallyEquivalent P R :=
  h₁.elim (fun e₁ => h₂.elim (fun e₂ => ⟨e₁.trans e₂⟩))

/-- A positive homothety, exactly as in the paper's cited definition.
A point summand is trivial because the other summand is a translate of P. -/
def IsHomotheticCopy (P A : ConvexPolytope d) : Prop :=
  ∃ r : ℝ, 0 < r ∧ ∃ b : E d,
    A.toSet = (fun x : E d => r • x + b) '' P.toSet

/-- Ordinary nontrivial Minkowski decomposability, allowing summands of
any affine dimension in the ambient space. -/
def MinkowskiDecomposable (P : ConvexPolytope d) : Prop :=
  ∃ A B : ConvexPolytope d,
    P.toSet = A.toSet + B.toSet ∧
    ¬IsHomotheticCopy P A ∧ ¬IsHomotheticCopy P B

def ConditionallyDecomposable (P : ConvexPolytope d) : Prop :=
  (∃ Q : ConvexPolytope d, CombinatoriallyEquivalent P Q ∧ MinkowskiDecomposable Q) ∧
  (∃ Q : ConvexPolytope d, CombinatoriallyEquivalent P Q ∧ ¬MinkowskiDecomposable Q)

/-- Theorem 1 of the conditional-decomposability paper, including sharpness
for every dimension, not only a lower bound or a fixed-dimensional case. -/
def ConditionalDecomposabilityClaim : Prop :=
  ∀ d : ℕ, 3 ≤ d →
    (∀ P : ConvexPolytope d, P.IsFullDim → ConditionallyDecomposable P →
      4 * d - 4 ≤ P.vertices.card) ∧
    (∃ P : ConvexPolytope d, P.IsFullDim ∧ ConditionallyDecomposable P ∧
      P.vertices.card = 4 * d - 4)

def CoordinatesIn (K : Subfield ℝ) (P : ConvexPolytope d) : Prop :=
  ∀ v ∈ P.vertices, ∀ i : Fin d, v i ∈ K

def RationalCoordinates (P : ConvexPolytope d) : Prop :=
  ∀ v ∈ P.vertices, ∀ i : Fin d, ∃ q : ℚ, (q : ℝ) = v i

def RealizableOver (P : ConvexPolytope d) (K : Subfield ℝ) : Prop :=
  ∃ Q : ConvexPolytope d, CombinatoriallyEquivalent P Q ∧ CoordinatesIn K Q

theorem realizableOver_iff_complete_face_iso (P : ConvexPolytope d) (K : Subfield ℝ) :
    RealizableOver P K ↔ ∃ Q : ConvexPolytope d,
      Nonempty (CompleteFaceType P ≃o CompleteFaceType Q) ∧ CoordinatesIn K Q := by
  constructor
  · rintro ⟨Q, hPQ, hK⟩
    exact ⟨Q, (combinatoriallyEquivalent_iff_complete_face_iso P Q).mp hPQ, hK⟩
  · rintro ⟨Q, hPQ, hK⟩
    exact ⟨Q, (combinatoriallyEquivalent_iff_complete_face_iso P Q).mpr hPQ, hK⟩

def RationallyRealizable (P : ConvexPolytope d) : Prop :=
  ∃ Q : ConvexPolytope d, CombinatoriallyEquivalent P Q ∧ RationalCoordinates Q

/-- Density in the space of labeled realizations, expressed without choosing
an enumeration of the vertices. The face-poset isomorphism identifies the
labels, and every vertex must move by less than the prescribed tolerance. -/
def RationallyDense (P : ConvexPolytope d) : Prop :=
  ∀ Q : ConvexPolytope d, CombinatoriallyEquivalent P Q →
    ∀ ε : ℝ, 0 < ε →
      ∃ R : ConvexPolytope d, ∃ φ : FaceType Q ≃o FaceType R,
        RationalCoordinates R ∧
        ∀ v : VertexType Q, dist (imageVertex φ v).val v.val < ε

theorem RationallyDense.realizable {P : ConvexPolytope d}
    (h : RationallyDense P) : RationallyRealizable P := by
  obtain ⟨Q, φ, hQ, _⟩ := h P (CombinatoriallyEquivalent.refl P) 1 zero_lt_one
  exact ⟨Q, ⟨φ⟩, hQ⟩

/-- Theorem 1 of the nonrational four-polytope paper. -/
def SeventeenVertexFieldClaim : Prop :=
  ∃ P : ConvexPolytope 4, P.IsFullDim ∧ P.vertices.card = 17 ∧
    ∀ K : Subfield ℝ, RealizableOver P K ↔ Real.sqrt 5 ∈ K

/-- Theorem 2 of the nonrational four-polytope paper. -/
def RationalityThroughTenClaim : Prop :=
  ∀ P : ConvexPolytope 4, P.IsFullDim → P.vertices.card ≤ 10 → RationallyRealizable P

/-- Taking a nonempty subset of actual extreme vertices produces the
ordinary convex hull of exactly those vertices. -/
def vertexSubsetPolytope (P : ConvexPolytope d) (S : Finset (E d))
    (hne : S.Nonempty) (hsub : S ⊆ P.vertices) : ConvexPolytope d where
  vertices := S
  vertices_nonempty := hne
  vertices_eq_extremePoints := by
    apply Set.Subset.antisymm
    · intro x hx
      have hxP : x ∈ P.vertices := hsub hx
      have hxext : x ∈ P.toSet.extremePoints ℝ := by
        change x ∈ (convexHull ℝ (P.vertices : Set (E d))).extremePoints ℝ
        rw [← P.vertices_eq_extremePoints]
        exact hxP
      have hhull : convexHull ℝ (S : Set (E d)) ⊆ P.toSet := by
        apply convexHull_mono
        exact hsub
      exact inter_extremePoints_subset_extremePoints_of_subset hhull
        ⟨subset_convexHull ℝ _ hx, hxext⟩
    · exact extremePoints_convexHull_subset

def deleteVertex (P : ConvexPolytope d) (v : E d)
    (hne : (P.vertices.erase v).Nonempty) : ConvexPolytope d :=
  vertexSubsetPolytope P (P.vertices.erase v) hne (Finset.erase_subset _ _)

@[simp] theorem deleteVertex_vertices (P : ConvexPolytope d) (v : E d)
    (hne : (P.vertices.erase v).Nonempty) :
    (deleteVertex P v hne).vertices = P.vertices.erase v := rfl

@[simp] theorem deleteVertex_toSet (P : ConvexPolytope d) (v : E d)
    (hne : (P.vertices.erase v).Nonempty) :
    (deleteVertex P v hne).toSet = convexHull ℝ (P.vertices.erase v : Set (E d)) := rfl

def IsSimpleVertex (P : ConvexPolytope d) (v : VertexType P) : Prop := by
  classical
  exact (polytopeGraph P).degree v = P.dim

/-- The field-equality assertion of Theorem 3. Its additional density and
combinatorial-deletion assertions require separate targets. -/
def SimpleDeletionFieldsClaim : Prop :=
  ∀ (d : ℕ) (P : ConvexPolytope d) (v : VertexType P),
    P.IsFullDim → d + 1 < P.vertices.card → IsSimpleVertex P v →
    ∀ hne : (P.vertices.erase v.val).Nonempty,
      ∀ K : Subfield ℝ, RealizableOver P K ↔ RealizableOver (deleteVertex P v.val hne) K

/-- The full Theorem 3: deletion preserves dimension, is determined by the
original face lattice and distinguished vertex, preserves every real
realization field, and preserves rational density in both directions. -/
def SimpleDeletionClaim : Prop :=
  ∀ (d : ℕ) (P : ConvexPolytope d) (v : VertexType P),
    P.IsFullDim → d + 1 < P.vertices.card → IsSimpleVertex P v →
    ∃ hne : (P.vertices.erase v.val).Nonempty,
      (deleteVertex P v.val hne).IsFullDim ∧
      (∀ (Q : ConvexPolytope d) (φ : FaceType P ≃o FaceType Q)
          (hneQ : (Q.vertices.erase (imageVertex φ v).val).Nonempty),
        CombinatoriallyEquivalent (deleteVertex P v.val hne)
          (deleteVertex Q (imageVertex φ v).val hneQ)) ∧
      (∀ K : Subfield ℝ,
        RealizableOver P K ↔ RealizableOver (deleteVertex P v.val hne) K) ∧
      (RationallyDense P ↔ RationallyDense (deleteVertex P v.val hne))

/-- Corollary 4, with the exact simple-vertex hypothesis. -/
def ElevenVertexSimpleClaim : Prop :=
  ∀ P : ConvexPolytope 4, P.IsFullDim → P.vertices.card = 11 →
    (∃ v : VertexType P, IsSimpleVertex P v) → RationallyRealizable P

end Papers.Polytopes
