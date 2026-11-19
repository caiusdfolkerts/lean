module

public import PaperVerification.TwoStepExteriorComplex
public import PaperVerification.TwoCentralKoszulOperator
public import PaperVerification.CentralLieCochainCoordinates
public import PaperVerification.ExteriorDerivationTransport
public import PaperVerification.ChevalleyEilenbergExterior

/-!
# The actual Chevalley--Eilenberg differential of the two-step Lie algebra

Every original pair of exterior two-forms is allowed. The constructed
operator acts on the genuine exterior algebra of the dual of the actual
ordinary Lie algebra. It satisfies the intrinsic CE equations, is their
unique solution, squares to zero, and has cohomological degree one.
The same operator is identified with the already constructed exterior and
Koszul models by explicit linear and algebra equivalences.
-/

@[expose] public section
noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace PaperVerification.TwoStepChevalleyEilenberg

open ExteriorQuadraticDifferential ExteriorDerivationTransport
open CentralLieCochainCoordinates

variable {K M : Type*} [Field K] [AddCommGroup M] [Module K M]
  [FiniteDimensional K M]

instance (f g : ⋀[K]^2 M) : FiniteDimensional K (L f g) :=
  inferInstanceAs (FiniteDimensional K (Module.Dual K M × (Fin 2 → K)))

/-- All actual cochains, with their ordinary exterior multiplication. -/
def cochainEquiv (f g : ⋀[K]^2 M) :
    ExteriorAlgebra K (TwoStepExteriorComplex.ExtendedModule K M) ≃ₐ[K]
      ExteriorAlgebra K (Module.Dual K (L f g)) :=
  mapEquiv (oneCochainEquiv f g)

/-- The differential on the actual exterior algebra of Lie one-cochains. -/
def differential (f g : ⋀[K]^2 M) :
    Module.End K (ExteriorAlgebra K (Module.Dual K (L f g))) :=
  conjugate (oneCochainEquiv f g) (TwoStepExteriorComplex.d f g)

/-- The prescribed negative bracket dual as an actual quadratic cochain. -/
def bracketDualTwoForm (f g : ⋀[K]^2 M) (α : Module.Dual K (L f g)) :
    ⋀[K]^2 (Module.Dual K (L f g)) :=
  ((oneCochainEquiv f g).symm α).2 0 • originalTwoCochain f g f +
    ((oneCochainEquiv f g).symm α).2 1 • originalTwoCochain f g g

/-- The included original form is literally its exterior cochain image. -/
theorem originalTwoCochain_coe (f g h : ⋀[K]^2 M) :
    (originalTwoCochain f g h : ExteriorAlgebra K (Module.Dual K (L f g))) =
      cochainEquiv f g (TwoStepExteriorComplex.baseMap (h : ExteriorAlgebra K M)) := by
  simp only [originalTwoCochain, exteriorPower.coe_map, cochainEquiv, mapEquiv_apply,
    TwoStepExteriorComplex.baseMap, TwoStepExteriorComplex.inclusion]
  exact (DFunLike.congr_fun
    (ExteriorAlgebra.map_comp_map (LinearMap.inl K M (Fin 2 → K))
      (oneCochainEquiv f g).toLinearMap) (h : ExteriorAlgebra K M)).symm

/-- The differential has the genuine bracket-dual value on every one-cochain. -/
theorem differential_generator (f g : ⋀[K]^2 M) (α : Module.Dual K (L f g)) :
    differential f g (ExteriorAlgebra.ι K α) =
      (bracketDualTwoForm f g α : ExteriorAlgebra K (Module.Dual K (L f g))) := by
  rw [differential, conjugate_apply, mapEquiv_symm_ι]
  change mapEquiv (oneCochainEquiv f g)
    (ExteriorQuadraticDifferential.differential _ _ _ _
      (ExteriorAlgebra.ι K ((oneCochainEquiv f g).symm α))) = _
  rw [ExteriorQuadraticDifferential.differential_generator]
  change cochainEquiv f g
      (((oneCochainEquiv f g).symm α).2 0 • TwoStepExteriorComplex.baseMap (f : ExteriorAlgebra K M) +
        ((oneCochainEquiv f g).symm α).2 1 • TwoStepExteriorComplex.baseMap (g : ExteriorAlgebra K M)) =
    ((oneCochainEquiv f g).symm α).2 0 •
        (originalTwoCochain f g f : ExteriorAlgebra K (Module.Dual K (L f g))) +
      ((oneCochainEquiv f g).symm α).2 1 •
        (originalTwoCochain f g g : ExteriorAlgebra K (Module.Dual K (L f g)))
  rw [map_add, map_smul, map_smul, originalTwoCochain_coe, originalTwoCochain_coe]

/-- The constructed map satisfies the usual odd Leibniz rule. -/
theorem differential_isOddDerivation (f g : ⋀[K]^2 M) : IsOddDerivation (differential f g) :=
  conjugate_isOddDerivation _ _ (TwoStepExteriorComplex.d_isOddDerivation f g)

/-- Intrinsic identification with the ordinary CE differential, including
its sign convention and all one-cochains. -/
theorem differential_isChevalleyEilenberg (f g : ⋀[K]^2 M) :
    ChevalleyEilenbergExterior.IsDifferential (differential f g) := by
  refine ⟨differential_isOddDerivation f g, ?_⟩
  intro α
  refine ⟨bracketDualTwoForm f g α, differential_generator f g α, ?_⟩
  intro x y
  simp only [bracketDualTwoForm, map_add, map_smul, LinearMap.add_apply,
    LinearMap.smul_apply, originalTwoCochain_pairing, smul_eq_mul]
  simpa only [LinearEquiv.apply_symm_apply] using
    (negative_bracket_dual f g ((oneCochainEquiv f g).symm α) x y).symm

/-- These defining equations admit no different exterior operator. -/
theorem differential_unique (f g : ⋀[K]^2 M)
    (D : Module.End K (ExteriorAlgebra K (Module.Dual K (L f g))))
    (hD : ChevalleyEilenbergExterior.IsDifferential D) : D = differential f g :=
  ChevalleyEilenbergExterior.differential_unique hD (differential_isChevalleyEilenberg f g)

/-- The ordinary CE differential squares to zero for every pair of forms. -/
theorem differential_square_zero (f g : ⋀[K]^2 M)
    (x : ExteriorAlgebra K (Module.Dual K (L f g))) :
    differential f g (differential f g x) = 0 :=
  conjugate_square_zero _ _ (TwoStepExteriorComplex.d_square_zero f g) x

/-- The ordinary CE differential raises the actual exterior degree by one. -/
theorem differential_mem_exteriorPower (f g : ⋀[K]^2 M) {q : ℕ}
    {x : ExteriorAlgebra K (Module.Dual K (L f g))}
    (hx : x ∈ ⋀[K]^q (Module.Dual K (L f g))) :
    differential f g x ∈ ⋀[K]^(q+1) (Module.Dual K (L f g)) :=
  conjugate_degree _ _ (fun _ _ hx ↦ TwoStepExteriorComplex.d_mem_exteriorPower f g hx) q x hx

/-- The original exterior model and the explicit Koszul operator are the
same linear map by their definitions, not merely equal in dimension. -/
theorem exterior_d_eq_koszul_operator (f g : ⋀[K]^2 M) :
    TwoStepExteriorComplex.d f g = TwoCentralKoszulOperator.operator f g := rfl

/-- The cochain coordinate equivalence intertwines the actual differentials. -/
theorem cochainEquiv_d (f g : ⋀[K]^2 M)
    (x : ExteriorAlgebra K (TwoStepExteriorComplex.ExtendedModule K M)) :
    differential f g (cochainEquiv f g x) = cochainEquiv f g (TwoStepExteriorComplex.d f g x) := by
  simp only [differential, cochainEquiv, conjugate_apply, AlgEquiv.symm_apply_apply]

end PaperVerification.TwoStepChevalleyEilenberg
