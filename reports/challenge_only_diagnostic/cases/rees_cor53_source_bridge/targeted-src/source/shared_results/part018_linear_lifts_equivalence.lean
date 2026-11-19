module
public import graph_foundation.part013
public import shared_results.part018_mixed_integer_tor

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Common.LinearLiftsEquivalence -/
section

/-! # Transport of actual cycle lifting by basis-preserving equivalences -/

section
set_option autoImplicit false
noncomputable section
namespace FourPapers.BasisCycleLifting

open Classical
variable {K X Y X' Y' I J Γ : Type*} [CommRing K]
  [AddCommGroup X] [Module K X] [AddCommGroup Y] [Module K Y]
  [AddCommGroup X'] [Module K X'] [AddCommGroup Y'] [Module K Y']
  [LinearOrder Γ]

lemma basisSpan_equiv_iff (b : Module.Basis I K X) (b' : Module.Basis I K X')
    (e : X ≃ₗ[K] X') (hb : ∀ i, e (b i) = b' i) (S : Set I) (x : X) :
    e x ∈ Submodule.span K (b' '' S) ↔ x ∈ Submodule.span K (b '' S) := by
  have he : b.map e = b' := by
    apply DFunLike.ext
    intro i
    exact hb i
  rw [← he]
  simp only [Module.Basis.mem_span_image, Module.Basis.map_repr,
    LinearEquiv.trans_apply, LinearEquiv.symm_apply_apply]

/-- The maps retain the actual differential and every filtration bound. -/
theorem linearLifts_map
    (b : Module.Basis I K X) (c : Module.Basis J K Y)
    (b' : Module.Basis I K X') (c' : Module.Basis J K Y')
    (w : I → Γ) (v : J → Γ) (D : X →ₗ[K] Y) (D' : X' →ₗ[K] Y')
    (e : X ≃ₗ[K] X') (f : Y ≃ₗ[K] Y')
    (hb : ∀ i, e (b i) = b' i) (hc : ∀ j, f (c j) = c' j)
    (hD : ∀ x, D' (e x) = f (D x))
    (hlift : LinearLifts b c w v D) : LinearLifts b' c' w v D' := by
  intro n x hx hdx
  have hlev : e (e.symm x) ∈ level b' w n := by
    simpa only [e.apply_symm_apply] using hx
  have hx' : e.symm x ∈ level b w n :=
    (basisSpan_equiv_iff b b' e hb {i | w i ≤ n} (e.symm x)).mp hlev
  have hdiff : f (D (e.symm x)) = D' x := by
    rw [← hD, e.apply_symm_apply]
  have hdx' : D (e.symm x) ∈ lower c v n :=
    (basisSpan_equiv_iff c c' f hc {j | v j < n} (D (e.symm x))).mp
      (hdiff.symm ▸ hdx)
  obtain ⟨z, hz, hDz, herr⟩ := hlift n (e.symm x) hx' hdx'
  refine ⟨e z, (basisSpan_equiv_iff b b' e hb {i | w i ≤ n} z).mpr hz, ?_, ?_⟩
  · rw [hD, hDz, f.map_zero]
  · have he := (basisSpan_equiv_iff b b' e hb {i | w i < n}
      (e.symm x - z)).mpr herr
    simpa only [lower, map_sub, e.apply_symm_apply] using he

theorem linearLifts_iff_of_equiv
    (b : Module.Basis I K X) (c : Module.Basis J K Y)
    (b' : Module.Basis I K X') (c' : Module.Basis J K Y')
    (w : I → Γ) (v : J → Γ) (D : X →ₗ[K] Y) (D' : X' →ₗ[K] Y')
    (e : X ≃ₗ[K] X') (f : Y ≃ₗ[K] Y')
    (hb : ∀ i, e (b i) = b' i) (hc : ∀ j, f (c j) = c' j)
    (hD : ∀ x, D' (e x) = f (D x)) :
    LinearLifts b c w v D ↔ LinearLifts b' c' w v D' := by
  refine ⟨linearLifts_map b c b' c' w v D D' e f hb hc hD, ?_⟩
  apply linearLifts_map b' c' b c w v D' D e.symm f.symm
  · intro i
    apply e.injective
    rw [e.apply_symm_apply, hb]
  · intro j
    apply f.injective
    rw [f.apply_symm_apply, hc]
  · intro x
    apply f.injective
    rw [f.apply_symm_apply, ← hD, e.apply_symm_apply]

end FourPapers.BasisCycleLifting

end
end
end


end
