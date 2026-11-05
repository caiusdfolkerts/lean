module

public import Continuation.Fano.SegmentSimplexBundleUT
public import Continuation.Fano.SegmentSimplexBundleDeterminants

/-!
# The general paragraph following Proposition 5.4

For every integer `a` with `0 ≤ a ≤ n - 1`, and every `n ≥ 2`, the
literal displayed region in `Ambient n` has a smooth reflexive presentation.
The actual geometric facet normals are uniform exactly when `a ≤ 1`;
the region is free of unimodular triangular faces exactly when
`n = 2` or `a ≤ n - 2`.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace Unimodular.SegmentSimplexBundle

open SegmentSimplex
open scoped BigOperators

/-- The displayed family in its total ambient dimension.  At positive
dimension the final coordinate is the height; the zero-dimensional clause
only makes the definition total and is excluded from the main theorem. -/
def SSB : (n : ℕ) → ℤ → Set (Ambient n)
  | 0, _ => Set.univ
  | d + 1, a => Q d a

def totalNormals : (n : ℕ) → ℤ → Finset (Lattice n)
  | 0, _ => ∅
  | d + 1, a => normals d a

def lastCoordinate (n : ℕ) (hn : 0 < n) : Fin n :=
  ⟨n - 1, Nat.sub_lt hn (by decide)⟩

def fibreCoordinate (n : ℕ) (i : Fin (n - 1)) : Fin n :=
  ⟨i.val, lt_of_lt_of_le i.is_lt (Nat.sub_le n 1)⟩

/-- This is an equality of subsets in the original coordinates, not a
statement only up to an unspecified affine or lattice isomorphism. -/
theorem SSB_mem_iff (n : ℕ) (a : ℤ) (hn : 0 < n) (x : Ambient n) :
    x ∈ SSB n a ↔
      -1 ≤ x (lastCoordinate n hn) ∧ x (lastCoordinate n hn) ≤ 1 ∧
      (∀ i : Fin (n - 1), x (fibreCoordinate n i) ≤ 1) ∧
      -(∑ i : Fin (n - 1), x (fibreCoordinate n i)) +
        (a : ℝ) * x (lastCoordinate n hn) ≤ 1 := by
  cases n with
  | zero => omega
  | succ d => rfl

/-- Every maximal minor of the literal normal family has absolute value
zero, one, or the absolute value of the single integral parameter. -/
theorem totalNormals_determinant_spectrum (n : ℕ) (a : ℤ) (hn : 2 ≤ n)
    (u : Fin n → Lattice n) (hu : ∀ i, u i ∈ totalNormals n a) :
    |(Pi.basisFun ℤ (Fin n)).det u| = 0 ∨
      |(Pi.basisFun ℤ (Fin n)).det u| = 1 ∨
      |(Pi.basisFun ℤ (Fin n)).det u| = |a| := by
  cases n with
  | zero => omega
  | succ d => exact normals_determinant_spectrum (by omega) a u hu

/-- The full unnumbered extension of Proposition 5.4, on the actual
`n`-dimensional ambient lattice and with the original integral parameter. -/
theorem segment_simplex_extension (n : ℕ) (a : ℤ)
    (hn : 2 ≤ n) (ha : 0 ≤ a) (han : a ≤ (n : ℤ) - 1) :
    ∃ P : SmoothReflexivePresentation n,
      P.carrier = SSB n a ∧
      (0 : Ambient n) ∈ interior (SSB n a) ∧
      realPolar (SSB n a) = convexHull ℝ
        (embed '' (insert 0 (totalNormals n a : Set (Lattice n)))) ∧
      P.geometricFacetNormals = (totalNormals n a : Set (Lattice n)) ∧
      ((∀ E : Set (Ambient n), IsExtreme ℝ (SSB n a) E →
          ¬ IsUnimodularTriangle E) ↔ n = 2 ∨ a ≤ (n : ℤ) - 2) ∧
      (IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
        (fun u : {u // u ∈ P.geometricFacetNormals} => u.val) ↔ a ≤ 1) := by
  cases n with
  | zero => omega
  | succ d =>
      have hd : 1 ≤ d := by omega
      have had : a ≤ (d : ℤ) := by simpa using han
      refine ⟨presentation d a hd ha had,
        presentation_carrier d a hd ha had,
        zero_mem_interior d a hd ha had,
        polar_eq_hull_normals d a hd ha had,
        geometricFacetNormals_eq d a hd ha had, ?_,
        geometric_normals_uniform_iff hd ha had⟩
      change (∀ E : Set (Ambient (d + 1)), IsExtreme ℝ (Q d a) E →
        ¬ IsUnimodularTriangle E) ↔ d + 1 = 2 ∨ a ≤ ((d + 1 : ℕ) : ℤ) - 2
      rw [Q_UT_free_iff hd ha had]
      push_cast
      omega

end Unimodular.SegmentSimplexBundle

#print axioms Unimodular.SegmentSimplexBundle.SSB_mem_iff
#print axioms Unimodular.SegmentSimplexBundle.totalNormals_determinant_spectrum
#print axioms Unimodular.SegmentSimplexBundle.segment_simplex_extension
