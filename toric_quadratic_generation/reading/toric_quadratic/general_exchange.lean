module

public import paper_verification.toric002

@[expose] public section

/-!
# The exchange criterion for arbitrary finite lattice convex hulls

This is Proposition 2.1 without a full-dimensionality assumption. The set
is an ordinary convex hull of finitely many lattice points, and the face
hypotheses quantify over its actual convex extreme faces and their relative
interiors. Ambient parity on an affine face agrees with parity in its
saturated direction lattice by `sameParity_iff_saturated_direction`.
-/

namespace ToricQuadratic

open Set
open PaperVerification.ToricGeometry
open PaperVerification.ToricExchange

/-- Proposition 2.1 for every finite lattice convex hull, including lower
dimensional hulls, with connectivity in every degree and the actual toric
ideal equality over any commutative coefficient ring. -/
theorem proposition2_1_finite_lattice_hull
    (R : Type*) [CommRing R] (n : ℕ) (P : Set (Ambient n))
    (hfinite : ∃ s : Finset (Lattice n),
      P = convexHull ℝ ((embed n) '' (s : Set (Lattice n))))
    (hidp : IntegerDecompositionProperty (embed n) P)
    (hparity : FaceParity (embed n) P)
    (hadjoint : FaceAdjoint (embed n) P) :
    (∀ s t : Multiset (latticePoints (embed n) P),
      s.card = t.card → total (latticePoints (embed n) P) s =
        total (latticePoints (embed n) P) t →
      Connected (latticePoints (embed n) P) s t) ∧
      RingHom.ker (paperToricMap (latticePoints (embed n) P) R) =
        polynomialQuadraticIdeal (latticePoints (embed n) P) R := by
  classical
  obtain ⟨s, hs⟩ := hfinite
  have hhalf : HasFiniteHalfspaces P := by
    rw [hs]
    simpa only [Finset.coe_image] using
      finite_convexHull_hasFiniteHalfspaces (s.image (embed n))
  obtain ⟨ι, hι, H, hP⟩ := hhalf
  letI : Fintype ι := hι
  rw [hP] at hidp hparity hadjoint ⊢
  have hmid := midpointDecomposition_of_convex_idp
    (embed n) H.region H.convex_region hidp
  have htriple := tripleReduction_of_face_parity_adjoint
    H (embed n) hparity hadjoint
  exact ⟨all_fibers_connected _ hmid htriple,
    paper_kernel_eq_quadrics _ R hmid htriple⟩

end ToricQuadratic

#print axioms ToricQuadratic.proposition2_1_finite_lattice_hull
