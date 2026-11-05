module
public import PaperVerification.ToricMatchedCenters
public import PaperVerification.ToricBasisBoxFamily
@[expose] public section
/-!
# Interior lattice targets in a sum of smooth long-edge polytopes

This composes the actual normal-fan and shifted-center construction with the
finite-family lattice covering theorem. The resulting statement has only the
paper's geometric hypotheses and concerns actual integer-coordinate summands.
Boundary targets still require the separate face reduction in Lemma 4.2.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators
open PaperVerification.Toric

theorem mem_standardIntegerLattice_iff {n : ℕ} (x : Ambient n) :
    x ∈ standardIntegerLattice n ↔ ∃ z : Lattice n, embed n z = x := by
  constructor
  · intro hx
    obtain ⟨z, hz⟩ := (standardLatticeEquiv n).surjective ⟨x, hx⟩
    refine ⟨z, ?_⟩
    have he := congrArg (fun y : standardIntegerLattice n => (y : Ambient n)) hz
    simpa only [standardLatticeEquiv_coe] using he
  · rintro ⟨z, rfl⟩
    rw [← standardLatticeEquiv_coe z]
    exact (standardLatticeEquiv n z).property

namespace LatticePolytope

/-- The interior-target part of Lemma 4.2, with the smoothness, edge lengths,
same normal fan, and lattice summands interpreted literally. -/
theorem interior_lattice_decomposition {n : ℕ} (P Q : LatticePolytope n)
    (hP : P.Smooth) (hQ : Q.Smooth) (hfan : P.SameNormalFan Q)
    (hlP : P.EdgesAtLeast n) (hlQ : Q.EdgesAtLeast n)
    (m : Lattice n) (hm : embed n m ∈ interior (P.minkowskiSum Q)) :
    ∃ x y : Lattice n, embed n x ∈ P.carrier ∧ embed n y ∈ Q.carrier ∧ x + y = m := by
  classical
  let J := P.carrier.extremePoints ℝ
  letI : Fintype J := P.finite_vertices.fintype
  obtain ⟨b, a, c, hboxP, hboxQ, hcenters⟩ := P.matched_unit_box_centers Q hP hQ hfan hlP hlQ
  obtain ⟨p, hp, hpsum, hpm⟩ :=
    exists_probability_of_mem_convexHull_range (fun j : J => a j + c j) (hcenters m hm)
  let L := standardIntegerLattice n
  letI : DiscreteTopology L := standardIntegerLattice_discreteTopology n
  letI : DiscreteTopology L.toAddSubgroup := inferInstanceAs (DiscreteTopology L)
  have hclosed : IsClosed (L.toAddSubgroup : Set (Ambient n)) :=
    AddSubgroup.isClosed_of_discreteTopology
  have hbL (j : J) (i : Fin n) : integralBasisReal (b j) i ∈ L.toAddSubgroup := by
    rw [integralBasisReal_apply]
    exact (mem_standardIntegerLattice_iff _).mpr ⟨b j i, rfl⟩
  have hmL : embed n m ∈ L.toAddSubgroup :=
    (mem_standardIntegerLattice_iff _).mpr ⟨m, rfl⟩
  obtain ⟨x, hxP, y, hyQ, hxL, hyL, hxy⟩ :=
    finite_basis_boxes_lattice_decomposition_pi (fun j : J => integralBasisReal (b j))
      L.toAddSubgroup hclosed hbL P.carrier Q.carrier
      (convex_convexHull ℝ _) (convex_convexHull ℝ _) p hp hpsum a c
      hboxP hboxQ (embed n m) hmL hpm.symm
  obtain ⟨xZ, hxZ⟩ := (mem_standardIntegerLattice_iff x).mp hxL
  obtain ⟨yZ, hyZ⟩ := (mem_standardIntegerLattice_iff y).mp hyL
  refine ⟨xZ, yZ, ?_, ?_, ?_⟩
  · simpa only [hxZ] using hxP
  · simpa only [hyZ] using hyQ
  · apply embed_injective n
    simpa only [map_add, hxZ, hyZ] using hxy

end LatticePolytope

end PaperVerification.ToricGeometry
