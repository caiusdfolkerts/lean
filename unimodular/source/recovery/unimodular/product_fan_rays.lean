module

public import Unimodular.FanDecomposition
public import Unimodular.AllowedBlocks

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open Set TauCeti.Toric
open scoped NNReal

namespace Unimodular.FanProducts

variable {J E : Type*} [Fintype J] [DecidableEq J] [Fintype E]
variable {N V : J → Type*} [∀ j, AddCommGroup (N j)]
  [∀ j, NormedAddCommGroup (V j)] [∀ j, NormedSpace ℝ (V j)]
  [∀ j, FiniteDimensional ℝ (V j)]

theorem map_ray_linear {W W' : Type*} [AddCommGroup W] [AddCommGroup W']
    [Module ℝ W] [Module ℝ W'] (g : W →ₗ[ℝ] W') (v : W) :
    (PointedCone.hull ℝ {v}).map g = PointedCone.hull ℝ {g v} := by
  change Submodule.map (g.restrictScalars ℝ≥0) (Submodule.span ℝ≥0 {v}) = _
  rw [Submodule.map_span, Set.image_singleton]
  rfl

theorem map_single_span_finrank (j : J) (C : PointedCone ℝ (V j)) :
    Module.finrank ℝ (Submodule.span ℝ (C.map (LinearMap.single ℝ V j) : Set (∀ k, V k))) =
      Module.finrank ℝ (Submodule.span ℝ (C : Set (V j))) := by
  rw [PointedCone.coe_map, Submodule.span_image]
  exact (Submodule.equivMapOfInjective (LinearMap.single ℝ V j)
    (single_injective j) (Submodule.span ℝ (C : Set (V j)))).finrank_eq.symm

theorem ray_coordinate_zero (v : ∀ j, V j) {k : J} (hvk : v k = 0)
    {x : ∀ j, V j} (hx : x ∈ PointedCone.hull ℝ {v}) : x k = 0 := by
  let q : (∀ j, V j) →ₗ[ℝ≥0] V k :=
    (LinearMap.proj k : (∀ j, V j) →ₗ[ℝ] V k).restrictScalars ℝ≥0
  have hle : PointedCone.hull ℝ {v} ≤ LinearMap.ker q := by
    apply Submodule.span_le.mpr
    intro y hy
    rw [Set.mem_singleton_iff.mp hy]
    exact hvk
  exact hle hx

variable (i : ∀ j, N j →+ V j) (u : E → ∀ j, N j) (f : E → J)
  (Φ : Fan (piEmbedding i))

/-- Exact prescribed rays lying in chosen summands imply the geometric ray
condition; it is not an additional premise of the resulting product theorem. -/
theorem hasSummandRays_of_hasRays
    (hr : AllowedBlocks.HasRays (piEmbedding i) u Φ)
    (hs : ∀ e k, k ≠ f e → i k (u e k) = 0) : HasSummandRays i Φ := by
  intro C hC ρ
  obtain ⟨e, he⟩ := (hr ρ.toPointedCone).mp
    ⟨Φ.mem_of_isFaceOf hC ρ.1.isFaceOf, ρ.2⟩
  refine ⟨f e, ?_⟩
  intro x hx k hk
  rw [he] at hx
  exact ray_coordinate_zero ((piEmbedding i) (u e)) (hs e k hk) hx

theorem single_eq_of_support (hs : ∀ e k, k ≠ f e → i k (u e k) = 0)
    (e : E) (j : J) (he : f e = j) :
    Pi.single j (i j (u e j)) = (piEmbedding i) (u e) := by
  subst j
  ext k
  by_cases hk : k = f e
  · subst k
    simp [piEmbedding]
  · simp [Pi.single_eq_of_ne hk, piEmbedding, hs e k hk]

/-- The canonical factor fan has exactly the prescribed rays assigned to
that component, retaining all signs and excluding every extra ray. -/
theorem factorFan_hasRays (hi : ∀ j, IsIntegralLattice (i j))
    (hr : AllowedBlocks.HasRays (piEmbedding i) u Φ)
    (hnz : ∀ e, (piEmbedding i) (u e) ≠ 0)
    (hs : ∀ e k, k ≠ f e → i k (u e k) = 0) (j : J) :
    AllowedBlocks.HasRays (i j) (fun e : {e : E // f e = j} => u e.val j)
      (factorFan i hi Φ (hasSummandRays_of_hasRays i u f Φ hr hs) j) := by
  classical
  let h := hasSummandRays_of_hasRays i u f Φ hr hs
  intro R
  constructor
  · rintro ⟨hR, hdim⟩
    have hm : R.map (LinearMap.single ℝ V j) ∈ Φ.cones :=
      (map_single_mem_iff i hi Φ h j R).mpr hR
    have hd : Module.finrank ℝ
        (Submodule.span ℝ (R.map (LinearMap.single ℝ V j) : Set (∀ k, V k))) = 1 :=
      (map_single_span_finrank j R).trans hdim
    obtain ⟨e, he⟩ := (hr _).mp ⟨hm, hd⟩
    have hve : (piEmbedding i) (u e) ∈ R.map (LinearMap.single ℝ V j) := by
      rw [he]
      exact PointedCone.subset_hull (by simp)
    obtain ⟨x, _, hx⟩ := hve
    have hej : f e = j := by
      by_contra hne
      apply hnz e
      ext k
      by_cases hk : k = f e
      · subst k
        have hz := congrFun hx (f e)
        simpa [Pi.single_eq_of_ne hne, piEmbedding] using hz.symm
      · exact hs e k hk
    refine ⟨⟨e, hej⟩, ?_⟩
    have hmap : (PointedCone.hull ℝ {i j (u e j)}).map (LinearMap.single ℝ V j) =
        PointedCone.hull ℝ {(piEmbedding i) (u e)} := by
      rw [map_ray_linear]
      exact congrArg (fun v => PointedCone.hull ℝ {v}) (single_eq_of_support i u f hs e j hej)
    have hh := congrArg (fun C => sectionCone C j) (he.trans hmap.symm)
    simpa only [sectionCone_map_single] using hh
  · rintro ⟨⟨e, hej⟩, rfl⟩
    have hmap : (PointedCone.hull ℝ {i j (u e j)}).map (LinearMap.single ℝ V j) =
        PointedCone.hull ℝ {(piEmbedding i) (u e)} := by
      rw [map_ray_linear]
      exact congrArg (fun v => PointedCone.hull ℝ {v}) (single_eq_of_support i u f hs e j hej)
    have he := (hr (PointedCone.hull ℝ {(piEmbedding i) (u e)})).mpr ⟨e, rfl⟩
    refine ⟨(map_single_mem_iff i hi Φ h j _).mp (hmap.symm ▸ he.1), ?_⟩
    rw [← map_single_span_finrank j, hmap]
    exact he.2

end Unimodular.FanProducts

#print axioms Unimodular.FanProducts.map_single_span_finrank
#print axioms Unimodular.FanProducts.hasSummandRays_of_hasRays
#print axioms Unimodular.FanProducts.factorFan_hasRays
#check "UNIMODULAR_PRODUCT_EXACT_FACTOR_RAYS_EOF_V3"
