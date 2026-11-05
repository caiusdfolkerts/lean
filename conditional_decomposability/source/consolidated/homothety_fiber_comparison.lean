module
public import consolidated.homothety_fiber_rows

set_option Elab.async false

section BundlePart0
/- Source: Papers/HomothetyFiberComparison.lean -/



@[expose] public section
noncomputable section
namespace Papers.Polytopes.HomothetyParameters
open Set Module
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
variable {d : ℕ} {I : Type*} [Fintype I]

theorem exists_minimumClass_basis
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (a : I → ℝ) (b : I → E d)
    (hinj : Function.Injective (parameterVector a b))
    (hcover : ∀ y∈P.vertices,∃ j,f y=a j•y+b j)
    (i : I) (hmin : (noncentralClass P f a b i).card=
      d+1-finrank ℝ (parameterDirectionSpan a b))
    (hr : 1 ≤ d+1-finrank ℝ (parameterDirectionSpan a b)) :
    ∃ B : Basis (noncentralClass P f a b i) ℝ ((ℝ × E d) ⧸ parameterDirectionSpan a b),
      ∀ u,B u=quotientVertex a b u.val := by
  obtain ⟨x,hx⟩ := Finset.card_pos.mp (by omega :
    0<(noncentralClass P f a b i).card)
  exact exists_classQuotientBasis P hP f hf a b hcover i
    (Finset.mem_filter.mp hx).1 (noncentral_vertex_private P f a b hinj hx) hmin

theorem fiber_subset_of_mem
    (P : ConvexPolytope d) (a : I → ℝ) (b : I → E d) {x y : E d}
    (hy : y∈parameterFiber P a b x) : parameterFiber P a b y ⊆ parameterFiber P a b x := by
  have hsub : parameterDirectionSpan a b ⊔ Submodule.span ℝ {vertexVector y} ≤
      parameterDirectionSpan a b ⊔ Submodule.span ℝ {vertexVector x} := by
    apply sup_le le_sup_left
    apply Submodule.span_le.mpr
    rintro z (rfl : z=vertexVector y)
    exact hy.2
  intro z hz
  exact ⟨hz.1,hsub hz.2⟩

theorem crossing_fibers_equal
    (P : ConvexPolytope d) (f : E d → E d) (hf : IsParallelMap P f)
    (a : I → ℝ) (b : I → E d) (hinj : Function.Injective (parameterVector a b))
    {i j : I} {x y : E d} (hx : x∈noncentralClass P f a b i)
    (hy : y∈noncentralClass P f a b j) (hji : j≠i) (hxy : GeneralVertexStep P x y) :
    parameterFiber P a b x=parameterFiber P a b y := by
  have hxP := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
  apply Set.Subset.antisymm
  · exact fiber_subset_of_mem P a b (crossing_target_mem_fiber P f hf a b hinj hy
      (Finset.mem_filter.mp hx).1 hji.symm (generalVertexStep_symm hxP hxy))
  · exact fiber_subset_of_mem P a b (crossing_target_mem_fiber P f hf a b hinj hx
      (Finset.mem_filter.mp hy).1 hji hxy)

theorem quotient_scalar_of_fiber
    (P : ConvexPolytope d) (a : I → ℝ) (b : I → E d) {x y : E d}
    (hy : y∈parameterFiber P a b x) :
    ∃ c : ℝ,quotientVertex a b y=c•quotientVertex a b x := by
  let D := parameterDirectionSpan a b
  obtain ⟨u,hu,v,hv,heq⟩ := Submodule.mem_sup.mp hy.2
  obtain ⟨c,hc⟩ := Submodule.mem_span_singleton.mp hv
  refine ⟨c,?_⟩
  change D.mkQ (vertexVector y)=c•D.mkQ (vertexVector x)
  have hz : D.mkQ u=0 := (Submodule.Quotient.mk_eq_zero D).mpr hu
  rw [←heq,←hc,map_add,map_smul,hz,zero_add]

theorem minimumClass_same_fiber_unique
    (P : ConvexPolytope d) (f : E d → E d) (a : I → ℝ) (b : I → E d)
    (j : I) (B : Basis (noncentralClass P f a b j) ℝ
      ((ℝ × E d) ⧸ parameterDirectionSpan a b))
    (hB : ∀ u,B u=quotientVertex a b u.val)
    {x y z : E d} (hy : y∈noncentralClass P f a b j)
    (hz : z∈noncentralClass P f a b j)
    (hyF : y∈parameterFiber P a b x) (hzF : z∈parameterFiber P a b x) : y=z := by
  obtain ⟨c,hc⟩ := quotient_scalar_of_fiber P a b hyF
  obtain ⟨e,he⟩ := quotient_scalar_of_fiber P a b hzF
  have he0 : e≠0 := by
    intro he0
    rw [he0,zero_smul] at he
    exact (Finset.mem_filter.mp hz).2 ((Submodule.Quotient.mk_eq_zero _).mp he)
  have hrel : e•B ⟨y,hy⟩=c•B ⟨z,hz⟩ := by
    rw [hB,hB,hc,he,smul_smul,smul_smul,mul_comm]
  exact congrArg Subtype.val
    (B.linearIndependent.eq_of_smul_apply_eq_smul_apply e c ⟨y,hy⟩ ⟨z,hz⟩ he0 hrel)

/-- A crossing edge toward a class sharing an actual center must end at
that center: otherwise three distinct extreme points violate affine independence. -/
theorem neighbor_toward_shared_class_is_center
    (P : ConvexPolytope d) (f : E d → E d) (hf : IsParallelMap P f)
    (a : I → ℝ) (b : I → E d) (hinj : Function.Injective (parameterVector a b))
    {i h : I} (hhi : h≠i) {z x y : E d}
    (hz : z∈centralVertices P a b) (hzi : f z=a i•z+b i) (hzh : f z=a h•z+b h)
    (hx : x∈noncentralClass P f a b i) (hy : y∈fullClass P f a b h)
    (hxy : GeneralVertexStep P x y) : y=z := by
  by_contra hyz
  have hxP := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
  have hzP := (Finset.mem_filter.mp hz).1
  have hxz : x≠z := by
    intro he
    exact (Finset.mem_filter.mp hx).2 (he ▸ (Finset.mem_filter.mp hz).2)
  have hxi := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
  have hpar : ∃c : ℝ,f x-f z=c•(x-z) := by
    refine ⟨a i,?_⟩
    rw [hxi,hzi]
    module
  have hxh := homothety_at_two_neighbors P f hzP hxP hxy.1 (Ne.symm hyz)
    hxz hxy.2.1 hzh (Finset.mem_filter.mp hy).2 hpar
    (hf y hxy.1 x hxP (generalVertexStep_symm hxP hxy))
  exact noncentral_not_other_parameter P f a b hinj hx hhi hxh

end Papers.Polytopes.HomothetyParameters

end
end
end BundlePart0

