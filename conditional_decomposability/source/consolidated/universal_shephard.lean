module
public import consolidated.dense_cone_rigidity
public import consolidated_dev.exact_shephard_criterion

set_option Elab.async false

section BundlePart0
/- Source: Papers/UniversalShephard.lean -/




@[expose] public section

/-! Shephard's geometric property, nontriviality, and all realizations. -/
noncomputable section
namespace Papers.Polytopes
open Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
variable {d : ℕ}

theorem facet_complement_card_ge_two_of_nontrivial_parallel
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (hnon : ¬IsHomothetyOnVertices P f)
    {F : Set (E d)} (hF : IsFacet P F) :
    2 ≤ (P.vertices.filter (fun x => x ∉ F)).card := by
  by_contra hn
  have hsmall : (P.vertices.filter (fun x => x ∉ F)).card ≤ 1 := by omega
  obtain ⟨x,hx⟩ := (facePolytope P hF.1).vertices_nonempty
  have hx' := Finset.mem_filter.mp hx
  obtain ⟨y,hxy,hyF⟩ := IsFacet.exists_neighbor_outside P hP hF hx'.1 hx'.2
  obtain ⟨α,hα⟩ := hf x hx'.1 y hxy.1 hxy
  let b := f x-α•x
  have hfx : f x=α•x+b := by dsimp [b]; abel
  have hfy : f y=α•y+b := by
    calc
      f y=(f y-f x)+f x := by abel
      _=α•y+b := by rw [hα,hfx]; module
  have hout : ∀ z∈P.vertices,z∉F → f z=α•z+b := by
    intro z hz hzF
    have hzy : z=y := Finset.card_le_one.mp hsmall z
      (Finset.mem_filter.mpr ⟨hz,hzF⟩) y (Finset.mem_filter.mpr ⟨hxy.1,hyF⟩)
    simpa only [hzy] using hfy
  exact hnon ⟨α,b,homothety_everywhere_of_facet_point P hP f hf hF α b hout
    hx'.1 hx'.2 hfx⟩

theorem exactShephardFacet_of_property_and_nontrivial_parallel
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (hnon : ¬IsHomothetyOnVertices P f)
    (hS : HasShephardProperty P) : Papers.ActualPaperCoverReduction.ExactShephardFacet P := by
  obtain ⟨F,hF,hunique⟩ := hS
  exact ⟨F,hF.1,hF.2.trans hP,
    facet_complement_card_ge_two_of_nontrivial_parallel P hP f hf hnon hF,
    fun x hx hxF => Papers.ActualPaperCoverReduction.card_one_of_unique_exit P
      (hunique x hx hxF)⟩

theorem decomposable_after_iso_of_shephard_property
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (hnon : ¬IsHomothetyOnVertices P f)
    (hS : HasShephardProperty P)
    (Q : ConvexPolytope d) (hQ : Q.IsFullDim)
    (e : Papers.ActualFaceOrder.FaceObject P ≃o Papers.ActualFaceOrder.FaceObject Q) :
    MinkowskiDecomposable Q :=
  Papers.ExactShephardCriterion.decomposable_after_iso_of_exact_shephard_facet P
    (exactShephardFacet_of_property_and_nontrivial_parallel P hP f hf hnon hS) Q hQ e

end Papers.Polytopes

end
end
end BundlePart0

