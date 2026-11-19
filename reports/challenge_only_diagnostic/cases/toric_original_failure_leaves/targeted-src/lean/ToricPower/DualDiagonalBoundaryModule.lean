module

public import ToricPower.DualDiagonalTranslations
public import ToricPower.DiagonalChartModules

/-!
# The actual boundary-weight module over the product chart

The basis consists of exactly the integral total characters whose open
dual strip is nonempty. Regular monomials on the two affine factors act
by their literal sum on this character. For toric fan charts the separate
geometric nonemptiness theorem identifies this support with the sections
of the boundary Cartier divisor on the actual chart intersection.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped Classical

namespace ToricPower.IntegralArrangement

variable {n s : ℕ} (A : Fin s → Fin n → ℤ) (S T : Set (Fin s))

abbrev DualDiagonalBoundaryWeight :=
  {u : Fin n → ℤ // (dualDiagonalStrip A S T u).Nonempty}

/-- Every regular product-chart monomial preserves the exact geometric
support of top cohomology. -/
theorem dualDiagonalStrip_monomial_nonempty (u : Fin n → ℤ)
    (a : rayCharacterMonoid A S) (b : rayCharacterMonoid A T)
    (h : (dualDiagonalStrip A S T u).Nonempty) :
    (dualDiagonalStrip A S T (u+a.val+b.val)).Nonempty :=
  (h.image (fun x => x + latticeLift (-a.val))).mono
    (dualDiagonalStrip_monomial_translation A S T u a b)

def dualDiagonalBoundaryTranslate (p : rayCharacterMonoid A S × rayCharacterMonoid A T)
    (u : DualDiagonalBoundaryWeight A S T) : DualDiagonalBoundaryWeight A S T :=
  ⟨u.val+p.1.val+p.2.val,
    dualDiagonalStrip_monomial_nonempty A S T u.val p.1 p.2 u.property⟩

@[simp]
theorem dualDiagonalBoundaryTranslate_zero (u : DualDiagonalBoundaryWeight A S T) :
    dualDiagonalBoundaryTranslate A S T 0 u = u := by
  apply Subtype.ext
  change u.val + (0 : Fin n → ℤ) + 0 = u.val
  simp

theorem dualDiagonalBoundaryTranslate_add
    (p q : rayCharacterMonoid A S × rayCharacterMonoid A T)
    (u : DualDiagonalBoundaryWeight A S T) :
    dualDiagonalBoundaryTranslate A S T (p+q) u =
      dualDiagonalBoundaryTranslate A S T p (dualDiagonalBoundaryTranslate A S T q u) := by
  apply Subtype.ext
  change u.val+(p.1.val+q.1.val)+(p.2.val+q.2.val) =
    u.val+q.1.val+q.2.val+p.1.val+p.2.val
  abel

variable (k : Type) [CommRing k]

abbrev DualDiagonalBoundaryCoefficients := DualDiagonalBoundaryWeight A S T →₀ k

/-- The original monomial character action, extended linearly. -/
def dualDiagonalBoundaryRepresentation :
    Multiplicative (rayCharacterMonoid A S × rayCharacterMonoid A T) →*
      Module.End k (DualDiagonalBoundaryCoefficients A S T k) where
  toFun p := Finsupp.lmapDomain k k (dualDiagonalBoundaryTranslate A S T p.toAdd)
  map_one' := by
    change Finsupp.lmapDomain k k (dualDiagonalBoundaryTranslate A S T 0) = LinearMap.id
    have equal : dualDiagonalBoundaryTranslate A S T
        (0 : rayCharacterMonoid A S × rayCharacterMonoid A T) = id := by
      funext u
      exact dualDiagonalBoundaryTranslate_zero A S T u
    rw [equal, Finsupp.lmapDomain_id]
  map_mul' p q := by
    change Finsupp.lmapDomain k k (dualDiagonalBoundaryTranslate A S T (p.toAdd+q.toAdd)) =
      (Finsupp.lmapDomain k k (dualDiagonalBoundaryTranslate A S T p.toAdd)).comp
        (Finsupp.lmapDomain k k (dualDiagonalBoundaryTranslate A S T q.toAdd))
    rw [← Finsupp.lmapDomain_comp]
    congr 1
    funext u
    exact dualDiagonalBoundaryTranslate_add A S T p.toAdd q.toAdd u

def dualDiagonalBoundaryAction :
    DiagonalChartRing k A S T →ₐ[k] Module.End k (DualDiagonalBoundaryCoefficients A S T k) :=
  AddMonoidAlgebra.lift k _ _ (dualDiagonalBoundaryRepresentation A S T k)

instance dualDiagonalBoundaryCoefficients_module :
    Module (DiagonalChartRing k A S T) (DualDiagonalBoundaryCoefficients A S T k) :=
  Module.compHom _ (dualDiagonalBoundaryAction A S T k).toRingHom

/-- The target of the actual top cohomology comparison, with its
concrete action by the actual product-chart coordinate ring. -/
def dualDiagonalBoundaryModule : ModuleCat (DiagonalChartRing k A S T) :=
  ModuleCat.of (DiagonalChartRing k A S T) (DualDiagonalBoundaryCoefficients A S T k)

theorem dualDiagonalBoundary_single_smul
    (p : rayCharacterMonoid A S × rayCharacterMonoid A T) (r : k)
    (v : DualDiagonalBoundaryCoefficients A S T k) :
    AddMonoidAlgebra.single p r • v =
      r • Finsupp.mapDomain (dualDiagonalBoundaryTranslate A S T p) v := by
  change (dualDiagonalBoundaryAction A S T k (AddMonoidAlgebra.single p r)) v = _
  rw [dualDiagonalBoundaryAction, AddMonoidAlgebra.lift_single]
  rfl

theorem dualDiagonalBoundary_single_smul_single
    (p : rayCharacterMonoid A S × rayCharacterMonoid A T) (r t : k)
    (u : DualDiagonalBoundaryWeight A S T) :
    AddMonoidAlgebra.single p r • (Finsupp.single u t : DualDiagonalBoundaryCoefficients A S T k) =
      Finsupp.single (dualDiagonalBoundaryTranslate A S T p u) (r*t) := by
  rw [dualDiagonalBoundary_single_smul, Finsupp.mapDomain_single, Finsupp.smul_single,
    smul_eq_mul]

end ToricPower.IntegralArrangement
