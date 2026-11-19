module

public import ToricPower.ToricSectionExtension
public import ToricPower.CoherentEpimorphismLifting

/-!
# Finite Cartier covers of coherent sheaves on smooth toric varieties

Every coherent sheaf is the quotient of a finite direct sum of actual
Cartier line bundles. More generally, a quasi-coherent epimorphism onto
a coherent sheaf is dominated by such a sum. The summands and the actual
epimorphism are retained for finite-dimensionality and resolution arguments.
-/

@[expose] public noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local instance] CategoryTheory.Limits.HasFiniteBiproducts.of_hasFiniteProducts

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TauCeti.Toric

namespace ToricPower

universe u v

variable {N : Type u} {V : Type v} [AddCommGroup N] [AddCommGroup V]
  [Module ℝ V] {i : N →+ V}

/-- A finite Cartier sum can lift any quasi-coherent epimorphism with
coherent target, while keeping its composite epimorphic. -/
theorem toricFiniteCartierEpimorphismLift (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    {E F : fan.algebraicRealization.Modules} [E.IsQuasicoherent] [F.IsFinitePresentation]
    (p : E ⟶ F) [Epi p] :
    letI := toricSchemeIntegral fan nonempty
    ∃ (J : Type (max u v)) (finite : Finite J),
      letI := finite
      ∃ (D : J → TauCeti.AlgebraicGeometry.Scheme.CartierDivisor fan.algebraicRealization)
        (q : (⨁ fun a => (D a).sheaf) ⟶ E), Epi (q ≫ p) := by
  letI := toricSchemeIntegral fan nonempty
  let opens := fun σ : fan.cones => (fan.affineToricChartι σ).opensRange
  have covers : TopologicalSpace.IsOpenCover opens :=
    ((toricChartBoundaryAtlas fan regular (Classical.choice nonempty)).cartierEquationAtlas
      nonempty).covers
  apply exists_finiteCartier_epimorphism_lift opens covers
    (fun σ => isAffineOpen_opensRange (fan.affineToricChartι σ)) ?_ p
  intro σ M hM s
  exact toricSection_exists_cartier_extension fan nonempty regular σ M s

/-- The smooth toric resolution property, with explicit finite Cartier
summands and the genuine sheaf epimorphism. -/
theorem toricFiniteCartierEpimorphism (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (M : fan.algebraicRealization.Modules) [M.IsFinitePresentation] :
    letI := toricSchemeIntegral fan nonempty
    ∃ (J : Type (max u v)) (finite : Finite J),
      letI := finite
      ∃ (D : J → TauCeti.AlgebraicGeometry.Scheme.CartierDivisor fan.algebraicRealization)
        (q : (⨁ fun a => (D a).sheaf) ⟶ M), Epi q := by
  letI := toricSchemeIntegral fan nonempty
  obtain ⟨J, finite, D, q, epi⟩ :=
    toricFiniteCartierEpimorphismLift fan nonempty regular (𝟙 M)
  letI := finite
  exact ⟨J, finite, D, q, by simpa only [Category.comp_id] using epi⟩

/-- The same genuine Cartier cover, enumerated by an ordinary finite
set. This reindexing does not change any summand or the epimorphism. -/
theorem toricFiniteCartierEpimorphismFin (fan : Fan i)
    (nonempty : Nonempty fan.cones) (regular : fan.IsRegular)
    (M : fan.algebraicRealization.Modules) [M.IsFinitePresentation] :
    letI := toricSchemeIntegral fan nonempty
    ∃ (n : ℕ)
      (D : Fin n → TauCeti.AlgebraicGeometry.Scheme.CartierDivisor fan.algebraicRealization)
      (q : (⨁ fun a => (D a).sheaf) ⟶ M), Epi q := by
  classical
  letI := toricSchemeIntegral fan nonempty
  obtain ⟨J, finite, D, q, epi⟩ := toricFiniteCartierEpimorphism fan nonempty regular M
  letI := finite
  letI := epi
  letI : Fintype J := Fintype.ofFinite J
  let e := Fintype.equivFin J
  let reindexed := fun a : Fin (Fintype.card J) => D (e.symm a)
  let comparison : (⨁ fun a => (D a).sheaf) ≅ ⨁ fun a => (reindexed a).sheaf :=
    biproduct.whiskerEquiv e (fun a => eqToIso (by simp [reindexed]))
  exact ⟨Fintype.card J, reindexed, comparison.inv ≫ q, inferInstance⟩

end ToricPower

end
