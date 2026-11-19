module
public import graph_foundation.part001
public import shared_results.part018_linear_lifts_equivalence
public import graph_foundation.part010

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.FilteredLiftsEquivalence -/
section

/-! # Transport of filtered cycle lifting by actual linear equivalences

The comparison preserves every filtration level, the literal differential,
and the lower-filtration error in the cycle-lifting conclusion.
-/

section
set_option autoImplicit false
set_option maxHeartbeats 20000
set_option synthInstance.maxHeartbeats 5000
noncomputable section
namespace FourPapers.FilteredHomology

variable {K X Y X' Y' I J : Type*} [CommRing K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
  [AddCommGroup X'] [Module K X'] [AddCommGroup Y'] [Module K Y']

/-- A filtered chain equivalence transports the actual chosen cycle lift. -/
theorem liftsCycles_map
    (F : Filtration (K := K) X) (G : Filtration (K := K) Y)
    (F' : Filtration (K := K) X') (G' : Filtration (K := K) Y')
    (D : X →ₗ[K] Y) (D' : X' →ₗ[K] Y')
    (e : X ≃ₗ[K] X') (f : Y ≃ₗ[K] Y')
    (hF : ∀ n x, e x ∈ F'.level n ↔ x ∈ F.level n)
    (hG : ∀ n y, f y ∈ G'.level n ↔ y ∈ G.level n)
    (hD : ∀ x, D' (e x) = f (D x))
    (hlift : LiftsCycles F G D) : LiftsCycles F' G' D' := by
  intro n x hx hdx
  have hx' : e.symm x ∈ F.level (n+1) :=
    (hF (n+1) (e.symm x)).mp (by
      simpa only [e.apply_symm_apply] using hx)
  have hdiff : f (D (e.symm x)) = D' x := by
    rw [← hD, e.apply_symm_apply]
  have hdx' : D (e.symm x) ∈ G.level n :=
    (hG n (D (e.symm x))).mp (hdiff.symm ▸ hdx)
  obtain ⟨z, hz, hDz, herr⟩ := hlift n (e.symm x) hx' hdx'
  refine ⟨e z, (hF (n+1) z).mpr hz, ?_, ?_⟩
  · exact (hD z).trans ((congrArg f hDz).trans f.map_zero)
  · have he := (hF n (e.symm x-z)).mpr herr
    simpa only [map_sub, LinearEquiv.apply_symm_apply] using he

/-- No cycle-lifting or filtration-bound information is lost by transport. -/
theorem liftsCycles_iff_of_equiv
    (F : Filtration (K := K) X) (G : Filtration (K := K) Y)
    (F' : Filtration (K := K) X') (G' : Filtration (K := K) Y')
    (D : X →ₗ[K] Y) (D' : X' →ₗ[K] Y')
    (e : X ≃ₗ[K] X') (f : Y ≃ₗ[K] Y')
    (hF : ∀ n x, e x ∈ F'.level n ↔ x ∈ F.level n)
    (hG : ∀ n y, f y ∈ G'.level n ↔ y ∈ G.level n)
    (hD : ∀ x, D' (e x) = f (D x)) :
    LiftsCycles F G D ↔ LiftsCycles F' G' D' := by
  refine ⟨liftsCycles_map F G F' G' D D' e f hF hG hD, ?_⟩
  apply liftsCycles_map F' G' F G D' D e.symm f.symm
  · intro n x
    simpa only [e.apply_symm_apply] using (hF n (e.symm x)).symm
  · intro n y
    simpa only [f.apply_symm_apply] using (hG n (f.symm y)).symm
  · intro x
    apply f.injective
    rw [f.apply_symm_apply, ← hD, e.apply_symm_apply]

/-- A basis-preserving chain equivalence preserves the literal weight
filtration, including its strict inequality convention at every level. -/
theorem basisLiftsCycles_iff_of_equiv
    (b : Module.Basis I K X) (c : Module.Basis J K Y)
    (b' : Module.Basis I K X') (c' : Module.Basis J K Y')
    (w : I → ℕ) (v : J → ℕ) (D : X →ₗ[K] Y) (D' : X' →ₗ[K] Y')
    (e : X ≃ₗ[K] X') (f : Y ≃ₗ[K] Y')
    (hb : ∀ i, e (b i) = b' i) (hc : ∀ j, f (c j) = c' j)
    (hD : ∀ x, D' (e x) = f (D x)) :
    LiftsCycles (Universal.basisFiltration b w) (Universal.basisFiltration c v) D ↔
      LiftsCycles (Universal.basisFiltration b' w) (Universal.basisFiltration c' v) D' := by
  apply liftsCycles_iff_of_equiv _ _ _ _ D D' e f
  · intro n x
    exact BasisCycleLifting.basisSpan_equiv_iff b b' e hb {i | w i < n} x
  · intro n y
    exact BasisCycleLifting.basisSpan_equiv_iff c c' f hc {j | v j < n} y
  · exact hD

end FourPapers.FilteredHomology

end
end
end


end
