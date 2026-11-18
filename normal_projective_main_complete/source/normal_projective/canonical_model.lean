module
public import normal_projective.geometry
public import Mathlib.Analysis.Convex.Exposed
public import Mathlib.LinearAlgebra.AffineSpace.AffineEquiv
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Topology.Connected.Basic
public import Mathlib.Topology.Order.Real

/-!
# Canonical labelled realizations and genuine counted PN words

RECOVERY DRAFT. This source was prepared after execution access failed.
It has not been compiled. No principal theorem is asserted here.

Coordinates use the usual finite-dimensional real vector space. The condition
sum (normal i j)^2 = 1 is the Euclidean unit-normal normalization; the product
topology on the coordinate data is the usual Euclidean topology.
-/

@[expose] public section
noncomputable section
open Set
open scoped BigOperators

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

theorem PNWord.append {P Q U : Realization R} {p n q m : ℕ}
    (h₁ : PNWord P Q p n) (h₂ : PNWord Q U q m) :
    PNWord P U (p + q) (n + m) := by
  induction h₁ with
  | nil =>
      simpa using h₂
  | projective hstep htail ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        PNWord.projective hstep (ih h₂)
  | normal hstep htail ih =>
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
        PNWord.normal hstep (ih h₂)

theorem PNRelated.refl (P : Realization R) : PNRelated P P :=
  ⟨0, 0, PNWord.nil P⟩

theorem PNRelated.trans {P Q U : Realization R}
    (h₁ : PNRelated P Q) (h₂ : PNRelated Q U) : PNRelated P U := by
  obtain ⟨p, n, h₁⟩ := h₁
  obtain ⟨q, m, h₂⟩ := h₂
  exact ⟨p + q, n + m, h₁.append h₂⟩

theorem normalStep_trans {P Q U : Realization R}
    (h₁ : NormalStep P Q) (h₂ : NormalStep Q U) : NormalStep P U :=
  Eq.trans h₁ h₂

end Realization
end NormalProjective.CanonicalModel

