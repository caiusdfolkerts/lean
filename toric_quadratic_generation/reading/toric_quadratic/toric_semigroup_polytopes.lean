module

public import PaperVerification.ToricSmoothPointedSemigroup
public import PaperVerification.ToricProjectiveVertexCover
public import PaperVerification.ToricOrthantEdges
public import PaperVerification.ToricFaceInheritance
public import PaperVerification.ToricFanConstruction
public import Mathlib.Algebra.Group.Submonoid.Finsupp
public import Mathlib.Tactic.Module

@[expose] public section

/-!
# Primitive affine semigroup charts reconstruct the actual smooth polytope

The input semigroups are the additive closures of literal weight
differences. Their basis descriptions give supporting orthants and
positive points on every coordinate ray of the actual convex hull.
Every incident edge is then proved to be a coordinate edge using its
actual minimal face. This supplies the ordinary polytope smoothness
predicate and its complete normal fan, without inserting an edge or
fan correspondence as an assumption.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open PaperVerification.ToricCharacters PaperVerification.ToricExchange
open PaperVerification.ToricVertexCone
open scoped BigOperators Classical

variable {ι : Type*} [Fintype ι] {n : ℕ}

theorem positive_axis_point_of_differenceMonoid (a : ι → Lattice n) (j : ι)
    (z : Lattice n) (hz : z∈differenceWeightMonoid a j) (hz0 : z≠0) :
    ∃ ε : ℝ,0<ε ∧ embed n (a j)+ε • embed n z∈
      convexHull ℝ (Set.range (fun i=>embed n (a i))) := by
  obtain ⟨c,hc⟩ := AddSubmonoid.exists_of_mem_closure_range
    (fun i=>a i-a j) z hz
  let N : ℕ := ∑ i,c i
  have hN : 0<N := by
    by_contra h
    have hzero : N=0 := Nat.eq_zero_of_le_zero (le_of_not_gt h)
    have hci : ∀ i,c i=0 := fun i=>
      (Finset.sum_eq_zero_iff.mp hzero) i (Finset.mem_univ i)
    exact hz0 (by simpa [hci] using hc)
  have hNR : (0 : ℝ)<N := by exact_mod_cast hN
  let w : ι → ℝ := fun i=>(c i : ℝ)/(N : ℝ)
  have hw0 (i : ι) : 0≤w i := div_nonneg (Nat.cast_nonneg _) hNR.le
  have hw1 : ∑ i,w i=1 := by
    simp only [w,← Finset.sum_div,← Nat.cast_sum,show ∑ i,c i=N from rfl]
    exact div_self hNR.ne'
  have hcR : embed n z=∑ i,(c i : ℝ) • (embed n (a i)-embed n (a j)) := by
    simpa only [map_sum,map_nsmul,map_sub,Nat.cast_smul_eq_nsmul] using congrArg (embed n) hc
  have hcomb : ∑ i,w i • embed n (a i)=
      embed n (a j)+(N : ℝ)⁻¹ • embed n z := by
    have hNcast : ∑ i,(c i : ℝ)=(N : ℝ) := by simp [N]
    rw [hcR,Finset.smul_sum]
    simp only [smul_sub,Finset.sum_sub_distrib,smul_smul]
    rw [← Finset.sum_smul]
    have hsum : ∑ i,(N : ℝ)⁻¹*(c i : ℝ)=1 := by
      rw [← Finset.mul_sum,hNcast,inv_mul_cancel₀ hNR.ne']
    rw [hsum,one_smul]
    simp only [w,div_eq_mul_inv,mul_comm]
    module
  refine ⟨(N : ℝ)⁻¹,inv_pos.mpr hNR,?_⟩
  rw [← hcomb]
  exact mem_convexHull_of_exists_fintype w (fun i=>embed n (a i)) hw0 hw1
    (fun i=>Set.mem_range_self i) rfl

theorem affineSpan_eq_top_of_difference_basis (a : ι → Lattice n) (j : ι)
    (b : Module.Basis (Fin n) ℤ (Lattice n))
    (hb : ∀ i,b i∈differenceWeightMonoid a j) :
    affineSpan ℝ (convexHull ℝ (Set.range (fun i=>embed n (a i))))=⊤ := by
  let P := convexHull ℝ (Set.range (fun i=>embed n (a i)))
  let A := affineSpan ℝ P
  have hv : embed n (a j)∈A :=
    subset_affineSpan ℝ _ (subset_convexHull ℝ _ (Set.mem_range_self j))
  have hdir (i : Fin n) : integralBasisReal b i∈A.direction := by
    obtain ⟨ε,hε,hpoint⟩ := positive_axis_point_of_differenceMonoid a j (b i) (hb i)
      (b.ne_zero i)
    have h := AffineSubspace.vsub_mem_direction (subset_affineSpan ℝ _ hpoint) hv
    have h' : ε • integralBasisReal b i∈A.direction := by
      simpa only [vsub_eq_sub,add_sub_cancel_left,integralBasisReal_apply] using h
    simpa only [smul_smul,inv_mul_cancel₀ hε.ne',one_smul] using
      A.direction.smul_mem ε⁻¹ h'
  have hall (x : Ambient n) : x∈A.direction := by
    rw [← (integralBasisReal b).sum_repr x]
    exact Submodule.sum_mem _ (fun i hi=>A.direction.smul_mem _ (hdir i))
  apply top_unique
  intro x hx
  simpa only [vadd_eq_add,sub_add_cancel] using
    AffineSubspace.vadd_mem_of_mem_direction (hall (x-embed n (a j))) hv

theorem hull_orthant_of_difference_basis (a : ι → Lattice n) (j : ι)
    (b : Module.Basis (Fin n) ℤ (Lattice n))
    (hS : differenceWeightMonoid a j=coordinateConeMonoid b Finset.univ) :
    ∀ x∈convexHull ℝ (Set.range (fun i=>embed n (a i))),∀ l,
      0≤(integralBasisReal b).repr (x-embed n (a j)) l := by
  intro x hx l
  let f := (integralBasisReal b).coord l
  have hgen (i : ι) : f (embed n (a j))≤f (embed n (a i)) := by
    have hi : a i-a j∈coordinateConeMonoid b Finset.univ := hS ▸
      AddSubmonoid.subset_closure (Set.mem_range_self i)
    have hcoord : 0≤b.repr (a i-a j) l := hi l (Finset.mem_univ l)
    have hreal : 0≤(integralBasisReal b).repr
        (embed n (a i)-embed n (a j)) l := by
      rw [← map_sub,integralBasisReal_repr]
      exact_mod_cast hcoord
    simpa only [f,Module.Basis.coord_apply,map_sub,Finsupp.sub_apply,sub_nonneg] using hreal
  have hbound : f (embed n (a j))≤f x :=
    convexHull_min (by rintro _ ⟨i,rfl⟩;exact hgen i)
      ((convex_Ici (f (embed n (a j)))).linear_preimage f) hx
  simpa only [f,Module.Basis.coord_apply,map_sub,Finsupp.sub_apply,sub_nonneg] using hbound

namespace LatticePolytope

variable (P : LatticePolytope n)

/-- Orthant coordinates plus genuine positive feasible axis points
exhaust all incident edges of an actual polytope. -/
theorem edge_has_coordinate_direction_of_orthant_axes (v : Ambient n)
    (b : Module.Basis (Fin n) ℝ (Ambient n))
    (horthant : ∀ x∈P.carrier,∀ j,0≤b.repr (x-v) j)
    (haxes : ∀ i,∃ ε : ℝ,0<ε ∧ v+ε • b i∈P.carrier)
    (w : Ambient n) (hedge : P.IsEdge v w) :
    ∃ i,w∈P.coordinateRayFace v b i := by
  obtain ⟨κ,hκ,H,hPH⟩ := P.hasFiniteHalfspaces
  letI := hκ
  obtain ⟨hv,hw⟩ := P.edge_endpoints_extreme hedge
  have hpositive : ∃ i,0<b.repr (w-v) i := by
    by_contra hn
    push_neg at hn
    apply hedge.1
    apply b.ext_elem
    intro i
    have hz := le_antisymm (hn i) (horthant w hw.1 i)
    have he : b.repr w i=b.repr v i := by
      simpa only [map_sub,Finsupp.sub_apply,sub_eq_zero] using hz
    exact he.symm
  obtain ⟨i,hi⟩ := hpositive
  choose ε hε hεP using haxes
  have hvF : v∈H.face (H.jointZeros v w) := by
    exact ⟨hPH ▸ hv.1,fun k hk=>hk.1⟩
  have hwF : w∈H.face (H.jointZeros v w) := by
    exact ⟨hPH ▸ hw.1,fun k hk=>hk.2⟩
  have hzF := positive_coordinate_endpoint_mem_face H (H.jointZeros v w)
    b v hvF ε hε (fun j=>hPH ▸ hεP j)
    (fun x hx=>horthant x (hPH.symm ▸ hx)) w hwF i hi
  have hmin := H.jointFace_minimal (hPH ▸ hv.1) (hPH ▸ hw.1)
    (convex_segment v w) (by simpa only [← hPH] using hedge.2)
    (left_mem_segment ℝ v w) (right_mem_segment ℝ v w)
  obtain ⟨r,t,hr,ht,hrt,hline⟩ := hmin hzF
  have hcoords (j : Fin n) :
      ε i*(if i=j then 1 else 0)=t*b.repr (w-v) j := by
    have he := congrArg (fun x=>b.repr x j) hline
    simp only [map_add,map_smul,Finsupp.add_apply,Finsupp.smul_apply,
      Module.Basis.repr_self_apply,smul_eq_mul] at he
    simp only [map_sub,Finsupp.sub_apply]
    have hrtj := congrArg (fun s : ℝ=>s * (b.repr v) j) hrt
    nlinarith only [he,hrtj]
  have htne : t≠0 := by
    intro h
    exact (hε i).ne' (by simpa [h] using hcoords i)
  refine ⟨i,hw.1,?_⟩
  intro j hji
  have h := hcoords j
  rw [if_neg (Ne.symm hji),mul_zero] at h
  exact (mul_eq_zero.mp h.symm).resolve_left htne

theorem smooth_of_vertex_orthants_and_axes
    (hlocal : ∀ v∈P.carrier.extremePoints ℝ,
      ∃ (vZ : Lattice n) (b : Module.Basis (Fin n) ℤ (Lattice n)),
        vZ∈P.generators ∧ embed n vZ=v ∧
        (∀ x∈P.carrier,∀ i,0≤(integralBasisReal b).repr (x-v) i) ∧
        (∀ i,∃ ε : ℝ,0<ε ∧ v+ε • integralBasisReal b i∈P.carrier)) : P.Smooth := by
  intro v hv
  obtain ⟨vZ,b,hvZ,rfl,horthant,haxes⟩ := hlocal v hv
  choose lengths hlengths using fun i=>P.coordinateRayFace_eq_integral_edge
    vZ hvZ b horthant i (haxes i)
  refine ⟨vZ,b,lengths,rfl,fun i=>⟨(hlengths i).1,(hlengths i).2.1⟩,?_⟩
  intro w hw
  obtain ⟨i,hi⟩ := P.edge_has_coordinate_direction_of_orthant_axes
    (embed n vZ) (integralBasisReal b) horthant haxes w hw
  have hwseg := (hlengths i).2.2 ▸ hi
  have hverts := P.edge_endpoints_extreme hw
  have hend := (P.edge_endpoints_extreme (hlengths i).2.1).2.1
  rcases (mem_extremePoints_iff_forall_segment.mp hverts.2).2
    _ hverts.1.1 _ hend hwseg with hvw|hew
  · exact (hw.1 hvw).elim
  · exact ⟨i,hew.symm⟩

end LatticePolytope

/-- Literal basis semigroups at all actual vertex charts reconstruct the
actual finite convex hull as a smooth full-dimensional lattice polytope. -/
theorem exists_smooth_polytope_of_vertex_semigroups [Nonempty ι]
    (a : ι → Lattice n)
    (hlocal : ∀ j : vertexWeightIndices a,
      ∃ b : Module.Basis (Fin n) ℤ (Lattice n),
        differenceWeightMonoid a j.val=coordinateConeMonoid b Finset.univ) :
    ∃ P : LatticePolytope n,
      P.carrier=convexHull ℝ (Set.range (fun i=>embed n (a i))) ∧ P.Smooth := by
  have hverts : (vertexWeightIndices a : Set ι).Nonempty := by
    by_contra h
    have hempty : vertexWeightIndices a=∅ := Finset.eq_empty_iff_forall_notMem.mpr
      (fun i hi=>h ⟨i,hi⟩)
    have hH := hull_vertexWeightIndices a
    have hzero : convexHull ℝ (Set.range (fun i : vertexWeightIndices a=>embed n (a i.val)))=∅ := by
      haveI : IsEmpty (vertexWeightIndices a) := ⟨fun i=>by simpa [hempty] using i.property⟩
      simp only [Set.range_eq_empty,convexHull_empty]
    have hmem := subset_convexHull ℝ (Set.range (fun i=>embed n (a i)))
      (Set.mem_range_self (Classical.arbitrary ι))
    rw [← hH,hzero] at hmem
    exact hmem
  obtain ⟨j,hj⟩ := hverts
  obtain ⟨b,hb⟩ := hlocal ⟨j,hj⟩
  have hfull : affineSpan ℝ
      (convexHull ℝ (Set.range (fun i=>embed n (a i))))=⊤ :=
    affineSpan_eq_top_of_difference_basis a j b (fun i=>by
      rw [hb]
      intro l hl
      simp only [Module.Basis.repr_self_apply]
      split_ifs <;> norm_num)
  let P : LatticePolytope n :=
    { generators := Finset.univ.image a
      nonempty := ⟨a j,Finset.mem_image.mpr ⟨j,Finset.mem_univ j,rfl⟩⟩
      fullDimensional := by
        simpa only [Finset.coe_image,Finset.coe_univ,Set.image_univ,← Set.range_comp'] using hfull }
  have hcarrier : P.carrier=convexHull ℝ (Set.range (fun i=>embed n (a i))) := by
    simp only [P,LatticePolytope.carrier,Finset.coe_image,Finset.coe_univ,
      Set.image_univ,← Set.range_comp']
  refine ⟨P,hcarrier,P.smooth_of_vertex_orthants_and_axes ?_⟩
  intro v hv
  rw [hcarrier] at hv
  obtain ⟨j,rfl⟩ := extremePoints_convexHull_subset hv
  have hj : j∈vertexWeightIndices a := Finset.mem_filter.mpr ⟨Finset.mem_univ j,hv⟩
  obtain ⟨b,hb⟩ := hlocal ⟨j,hj⟩
  refine ⟨a j,b,Finset.mem_image.mpr ⟨j,Finset.mem_univ j,rfl⟩,rfl,?_,?_⟩
  · simpa only [hcarrier] using hull_orthant_of_difference_basis a j b hb
  · intro i
    have hbi : b i∈differenceWeightMonoid a j := by
      rw [hb]
      intro l hl
      simp only [Module.Basis.repr_self_apply]
      split_ifs <;> norm_num
    simpa only [hcarrier,integralBasisReal_apply] using
      positive_axis_point_of_differenceMonoid a j (b i) hbi (b.ne_zero i)

end PaperVerification.ToricGeometry

#print axioms PaperVerification.ToricGeometry.exists_smooth_polytope_of_vertex_semigroups
