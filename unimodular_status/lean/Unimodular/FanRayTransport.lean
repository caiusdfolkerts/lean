module

public import Unimodular.FanTransport
public import Unimodular.AllowedBlocks

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

/-! UNVERIFIED exact transport of prescribed ray sets. Dimension-one cones
are transported as actual cones; the conclusion is the original HasRays
predicate, including both the absence of extra rays and use of every ray. -/

namespace Unimodular.FanTransport

open TauCeti.Toric
open scoped NNReal

variable {E N N' V V' : Type*} [Fintype E]
  [AddCommGroup N] [AddCommGroup N']
  [NormedAddCommGroup V] [NormedAddCommGroup V']
  [NormedSpace ℝ V] [NormedSpace ℝ V']
  [FiniteDimensional ℝ V] [FiniteDimensional ℝ V']
  {ι : N →+ V} {ι' : N' →+ V'}
  {u : E → N} {u' : E → N'}

theorem map_ray (e : V ≃ₗ[ℝ] V') (v : V) :
    (AllowedBlocks.ray v).map (e : V →ₗ[ℝ] V') =
      AllowedBlocks.ray (e v) := by
  change Submodule.map ((e : V →ₗ[ℝ] V') : V →ₗ[ℝ≥0] V') (Submodule.span ℝ≥0 {v}) =
    Submodule.span ℝ≥0 {e v}
  rw [Submodule.map_span, Set.image_singleton]
  rfl

theorem map_span_finrank (e : V ≃ₗ[ℝ] V') (C : PointedCone ℝ V) :
    Module.finrank ℝ (Submodule.span ℝ (C.map (e : V →ₗ[ℝ] V') : Set V')) =
      Module.finrank ℝ (Submodule.span ℝ (C : Set V)) := by
  rw [PointedCone.coe_map, Submodule.span_image, e.finrank_map_eq]

theorem hasRays_of_equiv {Φ : Fan ι} {Ψ : Fan ι'} (e : FanEquiv Φ Ψ)
    (hu : ∀ a, e.realEquiv (ι (u a)) = ι' (u' a))
    (hΦ : AllowedBlocks.HasRays ι u Φ) : AllowedBlocks.HasRays ι' u' Ψ := by
  intro R
  constructor
  · rintro ⟨hR, hdim⟩
    let Q := R.map (e.realEquiv.symm : V' →ₗ[ℝ] V)
    have hQ : Q ∈ Φ.cones := by
      simpa only [Q, FanEquiv.symm_realEquiv] using (e.symm.map_mem R).mpr hR
    have hqdim : Module.finrank ℝ (Submodule.span ℝ (Q : Set V)) = 1 :=
      (map_span_finrank e.realEquiv.symm R).trans hdim
    obtain ⟨a, ha⟩ := (hΦ Q).mp ⟨hQ, hqdim⟩
    refine ⟨a, ?_⟩
    have hm := congrArg (fun C : PointedCone ℝ V =>
      C.map (e.realEquiv : V →ₗ[ℝ] V')) ha
    change (R.map (e.realEquiv.symm : V' →ₗ[ℝ] V)).map
      (e.realEquiv : V →ₗ[ℝ] V') = _ at hm
    simpa only [map_inverse_rev, map_ray, hu a] using hm
  · rintro ⟨a, rfl⟩
    have hsource := (hΦ (AllowedBlocks.ray (ι (u a)))).mpr ⟨a, rfl⟩
    have hmem := (e.map_mem (AllowedBlocks.ray (ι (u a)))).mpr hsource.1
    have hdim := (map_span_finrank e.realEquiv
      (AllowedBlocks.ray (ι (u a)))).trans hsource.2
    have hmap : (AllowedBlocks.ray (ι (u a))).map
        (e.realEquiv : V →ₗ[ℝ] V') = AllowedBlocks.ray (ι' (u' a)) := by
      rw [map_ray,hu a]
    rw [hmap] at hmem hdim
    exact ⟨hmem,hdim⟩

theorem hasRays_equiv_iff {Φ : Fan ι} {Ψ : Fan ι'} (e : FanEquiv Φ Ψ)
    (hu : ∀ a, e.realEquiv (ι (u a)) = ι' (u' a)) :
    AllowedBlocks.HasRays ι' u' Ψ ↔ AllowedBlocks.HasRays ι u Φ := by
  constructor
  · apply hasRays_of_equiv e.symm
    intro a
    apply e.realEquiv.injective
    simpa using (hu a).symm
  · exact hasRays_of_equiv e hu

end Unimodular.FanTransport

#print axioms Unimodular.FanTransport.hasRays_of_equiv
#print axioms Unimodular.FanTransport.hasRays_equiv_iff
