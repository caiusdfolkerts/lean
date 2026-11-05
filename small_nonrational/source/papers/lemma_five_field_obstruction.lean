module
public import Consolidated.Seventeen

@[expose] public section

namespace Papers.Nonrational

/-- Paper Lemma 5 in homogeneous coordinates over an arbitrary real subfield.

The seven rows are labelled `1, 2, 3, 4, 6, 7, 8`, and `w` represents point 5.
`GoldenIncidences` lists the nine coplanarities in equation (1).  The first
four rows are a projective frame, every three of the seven rows are linearly
independent, and `w` is not projectively equal to point 2.  No choice of a
positive golden root, affine chart, or normalized realization is assumed.
-/
theorem lemma5_field_obstruction (K : Subfield ℝ)
    (p : Fin 7 → Fin 4 → K) (w : Fin 4 → K)
    (hframe : LinearIndependent K ![p 0, p 1, p 2, p 3])
    (htriples : NoCollinearTriples p)
    (hw : ∀ t : K, w ≠ t • p 1)
    (hinc : GoldenIncidences p w) :
    Real.sqrt 5 ∈ K := by
  obtain ⟨t, ht⟩ := projective_golden_root p w hframe htriples hw hinc
  apply sqrt_five_mem_of_golden K (t : ℝ) t.property
  exact_mod_cast ht

end Papers.Nonrational
