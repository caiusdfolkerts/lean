module

public import ToricPower.ToricMonomialDualityFunctor
public import ToricPower.ArrangementPowerQuasicoherent
public import ToricPower.CartierMeetDerivedCech

/-!
# The actual boundary-normalized Cartier source diagram

The source coefficient is `right(c) + 1` on every ray and every source
arrow is the literal character `χ^(-a)`. Its inverse tensor diagram is
identified with the normalized dual coefficient diagram before deriving
either functor. The dimension shift is kept separate from this line
bundle normalization.
-/

@[expose] public noncomputable section

set_option maxHeartbeats 1500000
set_option maxRecDepth 2048
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open TauCeti.Toric TauCeti.AlgebraicGeometry.Scheme
open ToricPower.IntegralArrangement

namespace ToricPower

variable {N : Type} {V : Type*} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V} (fan : Fan i)
  (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
  {n s : ℕ} (basis : Module.Basis (Fin n) ℤ (N →+ ℤ)) (rays : Fin s ≃ fan.Ray)

local notation "A" => fanArrangementMatrix fan basis rays
local notation "C" => IncidenceObject A
local notation "X" => fan.algebraicRealization
local notation "Q" => QCoh X

/-- The actual normalized source coefficients and all their monomial arrows. -/
def normalizedCartierCoefficientSources : Cᵒᵖ ⥤ ToricMonomial.Object fan where
  obj c := ⟨(fun _ => 1) + diagonalRightCoefficients fan basis rays c.unop.2⟩
  map {c d} f := ⟨-basis.equivFun.symm f.unop.val, by
    intro ρ
    have h := (diagonalEntryRegular_of_incidence fan basis rays f.unop).2 ρ
    simp only [Pi.add_apply, AddMonoidHom.neg_apply]
    omega⟩
  map_id c := by
    apply Subtype.ext
    simp only [unop_id, incidence_id_val, map_zero, neg_zero]
    rfl
  map_comp f g := by
    apply Subtype.ext
    simp only [unop_comp, incidence_comp_val, map_add, neg_add, add_comm]
    rfl

/-- The normalized source carries a genuine Cartier divisor. -/
def normalizedCartierSources : letI := toricSchemeIntegral fan nonempty
    Cᵒᵖ ⥤ CartierSources X := by
  letI := toricSchemeIntegral fan nonempty
  exact normalizedCartierCoefficientSources fan basis rays ⋙
    ToricMonomial.sources fan nonempty regular

/-- The same actual normalized sources, in the quasicoherent category. -/
def normalizedCartierQuasicoherentSources : Cᵒᵖ ⥤ Q := by
  letI := toricSchemeIntegral fan nonempty
  exact normalizedCartierSources fan nonempty regular basis rays ⋙ cartierSourcesQuasicoherent X

/-- Negating the source gives exactly the normalized dual coefficients;
the comparison uses the unit character at every cell. -/
def normalizedSourceDualCoefficientIso :
    (normalizedCartierCoefficientSources fan basis rays).rightOp ⋙ ToricMonomial.dual fan ≅
      normalizedDualCoefficientDiagram fan basis rays :=
  NatIso.ofComponents (fun c => ToricMonomial.coefficientIso fan _ _ (by
    change -((fun _ => 1) + diagonalRightCoefficients fan basis rays c.2) = _
    rw [add_comm]
    exact (normalizedDualCartierCoefficients_eq fan basis rays c).symm)) (by
      intro c d f
      apply Subtype.ext
      exact (add_zero _).trans (zero_add _).symm)

/-- Inverse Cartier tensoring agrees with the actual normalized dual
tensor diagram, naturally in every incidence and every coefficient. -/
def normalizedCartierInverseTensorIso :
    letI := toricSchemeIntegral fan nonempty
    cartierLabelTwistDiagram X (normalizedCartierSources fan nonempty regular basis rays) ≅
      normalizedDualQuasicoherentTensorDiagram fan nonempty regular basis rays := by
  letI := toricSchemeIntegral fan nonempty
  change ((normalizedCartierCoefficientSources fan basis rays).rightOp ⋙
      (ToricMonomial.sources fan nonempty regular).op ⋙
        cartierSourcesQuasicoherentInverseTensor X).flip ≅
    (normalizedDualCoefficientDiagram fan basis rays ⋙
      ToricMonomial.quasicoherent fan nonempty regular ⋙ tensoringLeft Q).flip
  exact (flipFunctor C Q Q).mapIso
    (Functor.isoWhiskerLeft (normalizedCartierCoefficientSources fan basis rays).rightOp
        (ToricMonomial.inverseTensorQuasicoherentIso fan nonempty regular) ≪≫
      Functor.isoWhiskerRight (normalizedSourceDualCoefficientIso fan basis rays)
        (ToricMonomial.quasicoherent fan nonempty regular ⋙ tensoringLeft Q))

end ToricPower

end
