module
public import consolidated.small_order_rigidity
public import consolidated.homothety_unowned_facet
public import consolidated_dev.minkowski_map_core

set_option Elab.async false

section BundlePart0
/- Source: Papers/DenseConeRigidity.lean -/



@[expose] public section
noncomputable section
namespace Papers.PolytopeFourRegularTail
open Set Finset Papers.Polytopes
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
open scoped Classical
variable {n : ℕ}

/-- A universal vertex over a graph of minimum degree at least its order
minus two yields a rigid cone. The graph consists of actual polytope edges. -/
theorem rigid_of_universal_vertex_dense
    (P : ConvexPolytope n) (T : Finset (E n)) (hTV : T ⊆ P.vertices)
    (t : ℕ) (ht : 3 ≤ t) (hcard : T.card ≤ t+1)
    (hmin : ∀ x ∈ T, t-1 ≤ (T.filter (GeneralVertexStep P x)).card)
    {v : E n} (hv : v ∈ T)
    (hstar : ∀ x ∈ T, x ≠ v → GeneralVertexStep P v x) :
    RigidInTail P T T := by
  have hvmin := hmin v hv
  obtain ⟨w, hw⟩ := Finset.card_pos.mp (by omega :
    0 < (T.filter (GeneralVertexStep P v)).card)
  obtain ⟨hwT, hvw⟩ := Finset.mem_filter.mp hw
  have hpair : ({v,w} : Finset (E n)) ⊆ T := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl <;> assumption
  obtain ⟨A, hA⟩ := exists_largest_rigid P T
  have hAc : 2 ≤ A.card := by
    have hh := hA.largest {v,w} hpair (rigid_pair hv hwT hvw)
    simpa only [Finset.card_pair hvw.2.1] using hh
  have hvA : v ∈ A := by
    by_contra hvA
    have hc := hA.outside_degree_le_one hTV hv hvA
    have he : A.filter (GeneralVertexStep P v) = A := by
      apply Finset.filter_eq_self.mpr
      intro x hx
      exact hstar x (hA.subset hx) (fun he => hvA (he ▸ hx))
    rw [he] at hc
    omega
  by_cases hAT : A = T
  · exact hAT ▸ hA.rigid
  have hnot : ¬T ⊆ A := fun h => hAT (Finset.Subset.antisymm hA.subset h)
  obtain ⟨b, hbT, hbA⟩ := Finset.not_subset.mp hnot
  let B := T \ A
  have hbB : b ∈ B := Finset.mem_sdiff.mpr ⟨hbT, hbA⟩
  have hres := hA.residual_min_degree hTV (t-2) (by
    have he : t-2+1=t-1 := by omega
    simpa only [he] using hmin)
  have hmB := hres b hbB
  change t-2 ≤ (B.filter (GeneralVertexStep P b)).card at hmB
  have hltB := actual_degree_lt_card P B hbB
  have hBc : t-1 ≤ B.card := by omega
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by
    rw [Finset.card_erase_of_mem hvA]
    omega : 0 < (A.erase v).card)
  obtain ⟨hav, haA⟩ := Finset.mem_erase.mp ha
  have hsub : T.filter (GeneralVertexStep P a) ⊆ A.erase a := by
    intro x hx
    obtain ⟨hxT, hax⟩ := Finset.mem_filter.mp hx
    refine Finset.mem_erase.mpr ⟨hax.2.1.symm, ?_⟩
    by_contra hxA
    have hcount := hA.outside_degree_le_one hTV hxT hxA
    have hxv : GeneralVertexStep P x v :=
      actualStep_symm (hTV hv) (hstar x hxT (fun he => hxA (he.symm ▸ hvA)))
    have hxa := actualStep_symm (hTV (hA.subset haA)) hax
    exact hav (Finset.card_le_one.mp hcount a
      (Finset.mem_filter.mpr ⟨haA, hxa⟩) v (Finset.mem_filter.mpr ⟨hvA, hxv⟩))
  have ham := hmin a (hA.subset haA)
  have hacount := Finset.card_le_card hsub
  rw [Finset.card_erase_of_mem haA] at hacount
  have hAc' : t ≤ A.card := by omega
  have hcards : B.card+A.card=T.card := Finset.card_sdiff_add_card_eq_card hA.subset
  exfalso
  omega

end Papers.PolytopeFourRegularTail

end
end
end BundlePart0

section BundlePart1
/- Source: Papers/ShephardRigidComplement.lean -/







@[expose] public section

/-!
# A facet with a rigid complement

This is the intended full proof of Lemma 3. The parallel map is obtained
from actual Minkowski decomposability, and rigidity of the actual
complement supplies its homothety there. The supporting normal of the
facet and the edge maximum principle then force exactly one exterior
neighbor at every facet vertex.

Development status: this new module awaits its first compiler check.
-/

noncomputable section
namespace Papers.Polytopes

open Set
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem IsFacet.exists_neighbor_outside (P : ConvexPolytope d) (hP : P.IsFullDim)
    {F : Set (E d)} (hF : IsFacet P F) {x : E d}
    (hx : x ∈ P.vertices) (hxF : x ∈ F) :
    ∃ y : E d, GeneralVertexStep P x y ∧ y ∉ F := by
  obtain ⟨g, hg⟩ := exists_supportsFace P hF.1
  obtain ⟨w, hw, hwg⟩ : ∃ w ∈ P.vertices, g w ≠ 0 := by
    by_contra hn
    push_neg at hn
    exact hF.support_ne_zero hg (affine_eq_zero_of_vertices P hP g hn)
  have hpos : 0 < g w := lt_of_le_of_ne
    (hg.1 w (subset_convexHull ℝ _ hw)) (Ne.symm hwg)
  have hxg := hg.eq_zero hxF
  have hlt : g.linear.toContinuousLinearMap x < g.linear.toContinuousLinearMap w := by
    rw [affine_form_apply g x] at hxg
    rw [affine_form_apply g w] at hpos
    change g.linear x < g.linear w
    linarith
  obtain ⟨y, hxy, hxylt⟩ := exists_increasing_edge P
    g.linear.toContinuousLinearMap hx hw hlt
  refine ⟨y, hxy, ?_⟩
  intro hyF
  have hyg := hg.eq_zero hyF
  rw [affine_form_apply g x] at hxg
  rw [affine_form_apply g y] at hyg
  change g.linear x < g.linear y at hxylt
  linarith

/-- If a parallel map is a fixed homothety off a facet and at one
facet vertex, then the supporting-normal argument forces that same
homothety at every vertex. -/
theorem homothety_everywhere_of_facet_point
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f)
    {F : Set (E d)} (hF : IsFacet P F) (α : ℝ) (b : E d)
    (hout : ∀ y ∈ P.vertices, y ∉ F → f y = α • y + b)
    {x : E d} (hx : x ∈ P.vertices) (hxF : x ∈ F)
    (hfx : f x = α • x + b) :
    ∀ y ∈ P.vertices, f y = α • y + b := by
  obtain ⟨g, hg⟩ := exists_supportsFace P hF.1
  let l := g.linear.toContinuousLinearMap
  have hconst : ∀ u ∈ F, ∀ v ∈ F, l u = l v := by
    intro u hu v hv
    have hgu := hg.eq_zero hu
    have hgv := hg.eq_zero hv
    rw [affine_form_apply g u] at hgu
    rw [affine_form_apply g v] at hgv
    change g.linear u = g.linear v
    linarith
  have hnormal (y : E d) (hy : y ∈ P.vertices) (hyF : y ∈ F) :
      l (f y) = α * l y + l b := by
    have he := parallel_constant_on_face hf hF.1 l hconst hy hx hyF hxF
    rw [hfx, map_add, map_smul, smul_eq_mul, hconst x hxF y hyF] at he
    exact he
  intro y hy
  by_cases hyF : y ∈ F
  · obtain ⟨w, hyw, hwF⟩ := IsFacet.exists_neighbor_outside P hP hF hy hyF
    have hfw := hout w hyw.1 hwF
    have hne : l w - l y ≠ 0 := by
      intro hz
      have hgw : g w = 0 := by
        have hgy := hg.eq_zero hyF
        rw [affine_form_apply g y] at hgy
        rw [affine_form_apply g w]
        change g.linear w - g.linear y = 0 at hz
        linarith
      exact hwF ((hg.mem_iff w).mpr ⟨subset_convexHull ℝ _ hyw.1, hgw⟩)
    obtain ⟨c, hc⟩ := hf y hy w hyw.1 hyw
    have hnormalEdge := congrArg l hc
    rw [map_sub, map_smul, map_sub, smul_eq_mul, hfw, map_add,
      map_smul, smul_eq_mul, hnormal y hy hyF] at hnormalEdge
    have hzero : (c - α) * (l w - l y) = 0 := by nlinarith
    have hca : c = α := sub_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right hne)
    calc
      f y = f w - (f w - f y) := by abel
      _ = (α • w + b) - c • (w - y) := by rw [hc, hfw]
      _ = α • y + b := by rw [hca]; module
  · exact hout y hy hyF

theorem facet_shephard_of_parallel_complement
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f)
    (hnon : ¬ IsHomothetyOnVertices P f)
    {F : Set (E d)} (hF : IsFacet P F)
    (hcomplement : HomotheticOn f ((P.vertices : Set (E d)) \ F)) :
    ∀ x ∈ P.vertices, x ∈ F →
      ∃! y : E d, GeneralVertexStep P x y ∧ y ∉ F := by
  obtain ⟨α, b, hH⟩ := hcomplement
  have hout : ∀ y ∈ P.vertices, y ∉ F → f y = α • y + b :=
    fun y hy hyF => hH y ⟨hy, hyF⟩
  intro x hx hxF
  obtain ⟨y, hxy, hyF⟩ := IsFacet.exists_neighbor_outside P hP hF hx hxF
  refine ⟨y, ⟨hxy, hyF⟩, ?_⟩
  intro z hz
  by_contra hzy
  have hfx : f x = α • x + b :=
    homothety_at_two_neighbors P f hxy.1 hx hz.1.1 (Ne.symm hzy)
      hxy.2.1 hz.1.2.1 (hout y hxy.1 hyF) (hout z hz.1.1 hz.2)
      (hf y hxy.1 x hx (generalVertexStep_symm hx hxy))
      (hf z hz.1.1 x hx (generalVertexStep_symm hx hz.1))
  exact hnon ⟨α, b, homothety_everywhere_of_facet_point P hP f hf hF α b hout
    hx hxF hfx⟩

/-- Lemma 3, stated with actual Minkowski decomposability and local
parallel rigidity of the induced geometric complement. -/
theorem shephard_of_rigid_complement
    (P : ConvexPolytope d) (hP : P.IsFullDim) (hdecomp : MinkowskiDecomposable P)
    {F : Set (E d)} (hF : IsFacet P F)
    (hrigid : ParallelRigid P ((P.vertices : Set (E d)) \ F)) :
    HasShephardProperty P := by
  obtain ⟨f, hf, hnon⟩ := (minkowski_decomposable_iff_parallel_map P).mp hdecomp
  have hparallel : IsParallelOn P ((P.vertices : Set (E d)) \ F) f := by
    intro x hx y hy hxy
    exact hf x hx.1 y hy.1 hxy
  exact ⟨F, hF, facet_shephard_of_parallel_complement P hP f hf hnon hF
    (hrigid f hparallel)⟩

end Papers.Polytopes

end
end
end BundlePart1

