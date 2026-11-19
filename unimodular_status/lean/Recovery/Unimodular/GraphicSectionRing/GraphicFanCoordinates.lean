module

public import Recovery.Unimodular.GraphicSectionRing.FanSectionRing
public import Recovery.Unimodular.GraphicSectionRing.SectionAlgebra

/-!
# Integral graphic fan coordinates and the actual section algebra

A graphic coordinate system records an actual integral linear equivalence
and the exact primitive ray pairings as signed coordinate differences. The
proof transports the complete lattice semigroup, in every degree, to the
original difference-inequality semigroup. Completeness supplies the degree-zero
constant clause and finiteness; neither is assumed as additional data.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

universe u
namespace PaperVerification.ToricGeometry.SmoothCompleteFan

open Unimodular.GraphicSectionRing

variable {n : ℕ} (F : SmoothCompleteFan n)

/-- Exact integral graphic coordinates: the ray normals are signed coordinate
vectors and signed differences, with the anchored zero coordinate included. -/
structure GraphicCoordinates where
  equiv : Lattice n ≃ₗ[ℤ] Lattice n
  left : F.rays → Coordinate n
  right : F.rays → Coordinate n
  pairing : ∀ (v : F.rays) (m : Lattice n),
    integerPairing v.val m = -difference (equiv m) (left v) (right v)

namespace GraphicCoordinates

variable {F} (G : F.GraphicCoordinates)

/-- These are exactly the original ray inequalities expressed in the integral
coordinate system; repeated identical inequalities have no effect. -/
def constraints (a : Lattice n → ℤ) : Set (Constraint n) :=
  Set.range (fun v : F.rays => ⟨G.left v, G.right v, a v.val⟩)

end GraphicCoordinates

 theorem mem_fanIntegralExponents_iff_pairing (a : Lattice n → ℤ) (m : Lattice n) :
    m ∈ F.fanIntegralExponents a ↔ ∀ v ∈ F.rays, -a v ≤ integerPairing v m := by
  constructor
  · intro h v hv
    have hh := h v hv
    rw [normalRay_pairing_lattice] at hh
    change -(a v : ℝ) ≤ ((integerPairing v m : ℤ) : ℝ) at hh
    exact_mod_cast hh
  · intro h v hv
    have hh := h v hv
    change -(a v : ℝ) ≤ (dotProductEquiv ℝ (Fin n) (embed n v)) (embed n m)
    rw [normalRay_pairing_lattice]
    exact_mod_cast hh

namespace GraphicCoordinates

variable {F} (G : F.GraphicCoordinates)

/-- The original lattice-point inequalities are equivalent in every degree,
without deleting lower-dimensional cases or assuming a nonempty polytope. -/
theorem mem_exponents_iff (a : Lattice n → ℤ) (d : ℕ) (m : Lattice n) :
    m ∈ F.fanIntegralExponents (d • a) ↔
      ∀ c ∈ G.constraints a, difference (G.equiv m) c.left c.right ≤ (d : ℤ) * c.bound := by
  rw [F.mem_fanIntegralExponents_iff_pairing]
  constructor
  · intro h c hc
    obtain ⟨v, rfl⟩ := hc
    have hh := h v.val v.property
    rw [G.pairing v m] at hh
    have hh' := neg_le_neg_iff.mp hh
    simpa only [Pi.smul_apply, nsmul_eq_mul] using hh'
  · intro h v hv
    let v' : F.rays := ⟨v, hv⟩
    have hh := h ⟨G.left v', G.right v', a v⟩ ⟨v', rfl⟩
    rw [G.pairing v' m]
    apply neg_le_neg
    simpa only [Pi.smul_apply, nsmul_eq_mul] using hh

 theorem mem_exponents_iff_satisfies (a : Lattice n → ℤ) (m : Lattice n) :
    m ∈ F.fanIntegralExponents a ↔ Satisfies (G.constraints a) (G.equiv m) := by
  simpa only [one_smul, Nat.cast_one, one_mul, Satisfies] using G.mem_exponents_iff a 1 m

/-- The degree-one coordinates are a genuine bijection of the original
lattice points, not a replacement finite configuration. -/
def pointEquiv (a : Lattice n → ℤ) : F.fanIntegralExponents a ≃ Point (G.constraints a) where
  toFun m := ⟨G.equiv m.val, (G.mem_exponents_iff_satisfies a m.val).mp m.property⟩
  invFun x := ⟨G.equiv.symm x.val, (G.mem_exponents_iff_satisfies a _).mpr (by
    simpa only [LinearEquiv.apply_symm_apply] using x.property)⟩
  left_inv m := Subtype.ext (G.equiv.symm_apply_apply m.val)
  right_inv x := Subtype.ext (G.equiv.apply_symm_apply x.val)

 theorem points_finite (a : Lattice n → ℤ) : Finite (Point (G.constraints a)) := by
  letI := (F.fanIntegralExponents_finite a).fintype
  exact Finite.of_equiv (F.fanIntegralExponents a) (G.pointEquiv a)

/-- The exact integral coordinate equivalence on the full original graded
semigroup, with its genuine zero element. -/
def semigroupEquiv (a : Lattice n → ℤ) :
    F.fanSectionSemigroup a ≃+ sectionSemigroup (G.constraints a) where
  toFun z := ⟨(z.val.1, G.equiv z.val.2), by
    constructor
    · intro hz
      have hm : z.val.2 = 0 := (F.fanSectionSemigroup_degree_zero a z.val.2).mp (by
        have he : z.val = (0, z.val.2) := Prod.ext hz rfl
        exact he ▸ z.property)
      rw [hm, map_zero]
    · exact (G.mem_exponents_iff a z.val.1 z.val.2).mp z.property⟩
  invFun z := ⟨(z.val.1, G.equiv.symm z.val.2),
    (G.mem_exponents_iff a z.val.1 (G.equiv.symm z.val.2)).mpr (by
      simpa only [LinearEquiv.apply_symm_apply] using z.property.2)⟩
  left_inv z := Subtype.ext (Prod.ext rfl (G.equiv.symm_apply_apply z.val.2))
  right_inv z := Subtype.ext (Prod.ext rfl (G.equiv.apply_symm_apply z.val.2))
  map_add' z w := Subtype.ext (Prod.ext rfl (map_add G.equiv z.val.2 w.val.2))

/-- The independently defined genuine section ring is the proved graphic
semigroup algebra, with ordinary algebra structure and all graded pieces. -/
def actualSectionRingEquiv (k : Type u) [Field k] (a : Lattice n → ℤ) :
    SectionAlgebra (G.constraints a) k ≃ₐ[k]
      ActualSections.sectionRing k (F.fanCartierCocycle k F.isPure a) :=
  (AddMonoidAlgebra.domCongr k k (G.semigroupEquiv a).symm).trans
    (F.fanSectionRingEquiv k a)

#print axioms mem_exponents_iff
#print axioms points_finite
#print axioms semigroupEquiv
#print axioms actualSectionRingEquiv

end GraphicCoordinates
end PaperVerification.ToricGeometry.SmoothCompleteFan

#check PaperVerification.ToricGeometry.SmoothCompleteFan.GraphicCoordinates.actualSectionRingEquiv
