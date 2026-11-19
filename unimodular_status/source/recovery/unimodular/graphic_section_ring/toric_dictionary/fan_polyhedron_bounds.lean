module

public import Recovery.Unimodular.GraphicSectionRing.ToricDictionary.Part08
public import Recovery.Unimodular.GraphicSectionRing.ToricDictionary.FanPurity
public import Recovery.Unimodular.GraphicSectionRing.PolytopeEndpoints

/-!
# Bounded divisor polyhedra and degree-zero constants on complete fans

Every real divisor coefficient vector gives a bounded support polyhedron.
No nefness, strict convexity or nonempty-interior assumption is made. The
zero coefficient vector has exactly the origin, so its integral exponents
are exactly zero. These are consequences of the actual complete fan.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
noncomputable section
open scoped BigOperators
open Set

namespace PaperVerification.ToricGeometry.SmoothCompleteFan

variable {n : ℕ} (F : SmoothCompleteFan n)

/-- The finite Cartier-point hull contains every support polyhedron, even
when some Cartier points are infeasible and the support is not nef. -/
theorem fanPolytope_subset_convexHull_cartier (a : Lattice n → ℝ) :
    F.fanPolytope a ⊆ convexHull ℝ (Set.range (F.cartierPoint a)) := by
  intro x hx
  apply mem_finite_convexHull_of_lower_support (F.cartierPoint a) x
  intro f
  obtain ⟨s, hs⟩ := F.exists_cartierBasis_nonnegative F.isPure f
  exact ⟨s, linear_le_of_basis_coordinates (F.cartierBasis s) f (F.cartierPoint a s) x
    hs (F.cartierPoint_orthant s hx)⟩

/-- Actual metric boundedness for every divisor polyhedron on a complete fan. -/
theorem fanPolytope_isBounded (a : Lattice n → ℝ) : Bornology.IsBounded (F.fanPolytope a) :=
  ((Set.finite_range (F.cartierPoint a)).isCompact_convexHull ℝ).isBounded.subset
    (F.fanPolytope_subset_convexHull_cartier a)

/-- A complete fan has no nonzero exponent in degree zero. -/
theorem fanPolytope_zero : F.fanPolytope (fun _ => (0 : ℝ)) = {0} := by
  apply Set.Subset.antisymm
  · apply (F.fanPolytope_subset_convexHull_cartier (fun _ => 0)).trans
    apply convexHull_min
    · rintro _ ⟨s, rfl⟩
      simp [cartierPoint]
    · exact convex_singleton 0
  · rintro x rfl
    intro u hu
    simp

theorem fanIntegralExponents_zero : F.fanIntegralExponents (fun _ => (0 : ℤ)) = {0} := by
  ext m
  change embed n m ∈ F.fanPolytope (fun _ => ((0 : ℤ) : ℝ)) ↔ m ∈ ({0} : Set (Lattice n))
  simp only [Int.cast_zero, F.fanPolytope_zero, Set.mem_singleton_iff]
  constructor
  · intro hm
    apply embed_injective n
    simpa only [map_zero] using hm
  · rintro rfl
    exact map_zero _

theorem fanIntegralExponents_finite (a : Lattice n → ℤ) : (F.fanIntegralExponents a).Finite := by
  exact Unimodular.GraphicSectionRing.finite_lattice_points_of_bounded
    (F.fanPolytope (fun u => (a u : ℝ))) (F.fanPolytope_isBounded _)

#print axioms fanPolytope_subset_convexHull_cartier
#print axioms fanPolytope_isBounded
#print axioms fanPolytope_zero
#print axioms fanIntegralExponents_zero
#print axioms fanIntegralExponents_finite

end PaperVerification.ToricGeometry.SmoothCompleteFan

#check PaperVerification.ToricGeometry.SmoothCompleteFan.fanIntegralExponents_zero
