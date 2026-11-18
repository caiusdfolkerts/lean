module

public import ToricPower.PrincipalInvariantTransport
public import ToricPower.ToricEffectiveLineBundles

/-!
# Agreement of the principal and effective generation predicates

Both statements use the same actual coherent direct image in degree zero
in the literal bounded coherent derived category. The imported minimal
transport module proves invariance under actual Cartier-sheaf isomorphisms.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TauCeti.Toric

namespace ToricPower

universe u v

variable {N : Type u} {V : Type v} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

/-- The two independently assembled statements use definitionally the same
actual coherent direct image in degree zero. -/
theorem toricPowerGeneratesDbCoh_iff_lineBundlePowerGenerates (fan : Fan i)
    (regular : fan.IsRegular) (hne : fan.cones.Nonempty)
    (D : toricCartierDivisor fan hne) (ell : ℕ) (hell : 0 < ell) :
    letI := toricScheme_isIntegral fan hne
    toricPowerGeneratesDbCoh fan regular hne D ell hell ↔
      toricLineBundlePowerGenerates fan regular D.toInvertibleSheaf ell hell := by
  letI := toricScheme_isIntegral fan hne
  rfl

end ToricPower

end
