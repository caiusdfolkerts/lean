module
public import Recovery.Unimodular.GraphicSectionRing.ToricFiber
@[expose] public section
set_option autoImplicit false
noncomputable section

namespace Unimodular.GraphicSectionRing

variable {n m : ℕ} {σ : Type*}

/-- The degree-preserving map on the actual Laurent monomial exponents. -/
def degreeMap (e : Lattice n →+ Lattice m) :
    (ℕ × Lattice n) →+ (ℕ × Lattice m) where
  toFun x := (x.1, e x.2)
  map_zero' := by simp
  map_add' x y := by simp [map_add]

theorem degreeMap_injective {e : Lattice n →+ Lattice m}
    (he : Function.Injective e) : Function.Injective (degreeMap e) := by
  intro x y h
  exact Prod.ext (congrArg (fun z : ℕ × Lattice m => z.1) h)
    (he (congrArg (fun z : ℕ × Lattice m => z.2) h))

/-- Changing the ambient lattice acts through the actual monoid-algebra map. -/
theorem toricMap_coordinates (p : σ → Lattice n) (e : Lattice n →+ Lattice m)
    (K : Type*) [CommSemiring K] :
    toricMap (e ∘ p) K =
      (AddMonoidAlgebra.mapDomainAlgHom K K (degreeMap e)).comp (toricMap p K) := by
  apply MvPolynomial.algHom_ext
  intro a
  simp only [AlgHom.comp_apply, toricMap_X, Function.comp_apply,
    AddMonoidAlgebra.mapDomainAlgHom_apply, AddMonoidAlgebra.mapDomain_single]
  rfl

/-- An injective change of ambient lattice changes no toric relation among
the original labelled variables. This includes every integral coordinate
change, and even injective embeddings into a larger lattice. -/
theorem toricIdeal_coordinates (p : σ → Lattice n) (e : Lattice n →+ Lattice m)
    (he : Function.Injective e) (K : Type*) [CommSemiring K] :
    toricIdeal (e ∘ p) K = toricIdeal p K := by
  have hinj : Function.Injective
      (AddMonoidAlgebra.mapDomainAlgHom K K (degreeMap e)) :=
    AddMonoidAlgebra.mapDomain_injective (degreeMap_injective he)
  ext f
  change toricMap (e ∘ p) K f = 0 ↔ toricMap p K f = 0
  rw [toricMap_coordinates, AlgHom.comp_apply]
  constructor
  · intro h
    apply hinj
    simpa only [map_zero] using h
  · intro h
    rw [h, map_zero]

/-- The original lattice-point ideal is literally preserved by every integral
linear coordinate isomorphism; no equivalence is merely asserted informally. -/
theorem toricIdeal_integralLinearEquiv (p : σ → Lattice n)
    (e : Lattice n ≃ₗ[ℤ] Lattice m) (K : Type*) [CommSemiring K] :
    toricIdeal (e ∘ p) K = toricIdeal p K :=
  toricIdeal_coordinates p e.toAddMonoidHom e.injective K

end Unimodular.GraphicSectionRing
#print axioms Unimodular.GraphicSectionRing.toricMap_coordinates
#print axioms Unimodular.GraphicSectionRing.toricIdeal_coordinates
#print axioms Unimodular.GraphicSectionRing.toricIdeal_integralLinearEquiv
#check Unimodular.GraphicSectionRing.toricIdeal_integralLinearEquiv
