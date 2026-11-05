module
public import Projection.Normalization.Frames
public import Projection.CoordinateIdentity

/-!
# Theorem 3.1: coordinate projection compactification

`allProjectionLocus n k` is the range of literal coordinate deletion followed
by ordinary Lebesgue volume in the retained coordinates. `allMarkedArray`
is independently defined using the actual mixed-volume coefficient and the
centered segments `[-U_i/2,U_i/2]`. The coordinate extrusion theorem identifies
these two constructions for standard basis marks.

The two results below give both assertions of Theorem 3.1, for every
`1 ≤ k < n`, with no restriction on the marked vectors and no interior
assumption on the representing body.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open Set

namespace RankThreeProjection

theorem allProjectionLocus_eq_basisMarkedLocus (n k : ℕ) :
    allProjectionLocus n k = basisMarkedLocus n k := by
  unfold allProjectionLocus basisMarkedLocus
  congr 1
  funext K
  exact allProjectionArray_eq_standardMarked K

/-- **Theorem 3.1, closure formula.** Every parameter and every actual mixed
volume in the paper's statement is retained. -/
theorem theorem31 {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n) (P : Deleted n k → ℝ) :
    P ∈ closure (allProjectionLocus n k) ↔
      ∃ (K : Body n) (U : Fin n → Space n), allMarkedArray K U = P := by
  rw [allProjectionLocus_eq_basisMarkedLocus,
    closure_basisMarkedLocus_eq_markedArrayLocus hk hkn]
  constructor
  · rintro ⟨⟨K, U⟩, hKU⟩
    exact ⟨K, U, hKU⟩
  · rintro ⟨K, U, hKU⟩
    exact ⟨(K, U), hKU⟩

/-- **Theorem 3.1, dimension conclusion.** The same closure formula admits a
representation retaining at least `n-k+1` actual affine dimensions. -/
theorem theorem31_with_dimension {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n)
    (P : Deleted n k → ℝ) :
    P ∈ closure (allProjectionLocus n k) ↔
      ∃ (K : Body n) (U : Fin n → Space n),
        n - k + 1 ≤ bodyDimension K ∧ allMarkedArray K U = P := by
  rw [allProjectionLocus_eq_basisMarkedLocus]
  exact basis_marked_compactification hk hkn P

/-- Every marked tuple, including degenerate marks and lower-dimensional
initial bodies, has a representation with the dimension stated in Theorem 3.1. -/
theorem theorem31_renormalize_dimension {n k : ℕ} (hk : 1 ≤ k) (hkn : k < n)
    (K : Body n) (U : Fin n → Space n) :
    ∃ (L : Body n) (V : Fin n → Space n),
      n - k + 1 ≤ bodyDimension L ∧ allMarkedArray (k := k) L V = allMarkedArray K U :=
  marked_representation_with_dimension hk hkn.le ⟨(K, U), rfl⟩

end RankThreeProjection
