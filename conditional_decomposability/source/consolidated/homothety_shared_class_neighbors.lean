module
public import consolidated.homothety_unowned_class

set_option Elab.async false

section BundlePart0
/- Source: Papers/HomothetySharedClassNeighbors.lean -/



@[expose] public section
noncomputable section
namespace Papers.Polytopes.HomothetyParameters
open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
variable {d : ℕ} {I : Type*}

/-- A class whose central vertices all have another owner has no
additional neighbors beyond its noncentral part and the other classes. -/
theorem sharedCentral_neighbors_covered [Fintype I]
    (P : ConvexPolytope d) (f : E d → E d) (a : I → ℝ) (b : I → E d)
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y+b j)
    {i : I}
    (hshare : ∀ z ∈ centralVertices P a b, f z = a i • z+b i →
      ∃ j, j ≠ i ∧ f z = a j • z+b j)
    {x : E d} (hx : x ∈ noncentralClass P f a b i) :
    actualNeighbors P x ⊆ (noncentralClass P f a b i).erase x ∪
      ((Finset.univ : Finset I).erase i).biUnion (classNeighbors P f a b x) := by
  intro y hy
  obtain ⟨hyP,hxy⟩ := Finset.mem_filter.mp hy
  by_cases hyi : y ∈ noncentralClass P f a b i
  · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hxy.2.1.symm,hyi⟩)
  obtain ⟨j,hji,hyj⟩ : ∃ j, j ≠ i ∧ f y=a j • y+b j := by
    obtain ⟨j,hyj⟩ := hcover y hyP
    by_cases hji : j=i
    · subst j
      have hyD : vertexVector y ∈ parameterDirectionSpan a b := by
        by_contra hyD
        exact hyi (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hyP,hyj⟩,hyD⟩)
      exact hshare y (Finset.mem_filter.mpr ⟨hyP,hyD⟩) hyj
    · exact ⟨j,hji,hyj⟩
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
    ⟨j,Finset.mem_erase.mpr ⟨hji,Finset.mem_univ j⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hyP,hyj⟩,hxy⟩⟩)

theorem sharedCentral_neighbor_count_le [Fintype I]
    (P : ConvexPolytope d) (f : E d → E d) (hf : IsParallelMap P f)
    (a : I → ℝ) (b : I → E d)
    (hinj : Function.Injective (parameterVector a b))
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    {i : I}
    (hshare : ∀ z ∈ centralVertices P a b, f z = a i • z+b i →
      ∃ j, j ≠ i ∧ f z = a j • z+b j) {x : E d} (hx : x ∈ noncentralClass P f a b i) :
    (actualNeighbors P x).card ≤ (noncentralClass P f a b i).card - 1 +
      (Fintype.card I - 1) := by
  classical
  have hxP := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
  let J := (Finset.univ : Finset I).erase i
  have hcross : (J.biUnion (classNeighbors P f a b x)).card ≤ J.card := by
    simpa only [Nat.mul_one] using Finset.card_biUnion_le_card_mul J
      (classNeighbors P f a b x) 1 (by
        intro j hj
        exact classNeighbors_card_le_one P f hf a b hxP j
          (noncentral_not_other_parameter P f a b hinj hx (Finset.mem_erase.mp hj).1))
  have hc := (Finset.card_le_card
    (sharedCentral_neighbors_covered P f a b hcover hshare hx)).trans
    (Finset.card_union_le _ _)
  have hJ : J.card = Fintype.card I - 1 := by simp [J]
  rw [Finset.card_erase_of_mem hx] at hc
  change (actualNeighbors P x).card ≤ (noncentralClass P f a b i).card - 1 +
    (J.biUnion (classNeighbors P f a b x)).card at hc
  omega

/-- A vertex of a minimum class other than the common central class is
simple in the actual polytope. The cardinality `r` is its actual
quotient dimension, derived from the independent parameter family. -/
theorem sharedCentral_minimumClass_simple [Fintype I]
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (a : I → ℝ) (b : I → E d)
    (hind : AffineIndependent ℝ (parameterVector a b))
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    {i : I}
    (hshare : ∀ z ∈ centralVertices P a b, f z = a i • z+b i →
      ∃ j, j ≠ i ∧ f z = a j • z+b j)
    (hmin : (noncentralClass P f a b i).card =
      d + 1 - finrank ℝ (parameterDirectionSpan a b))
    (hsize : 2 ≤ (noncentralClass P f a b i).card)
    {x : E d} (hx : x ∈ noncentralClass P f a b i) :
    IsSimpleVertex P ⟨x, (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1⟩ := by
  letI : Nonempty I := ⟨i⟩
  have htm : finrank ℝ (parameterDirectionSpan a b) + 1 = Fintype.card I := by
    rw [parameterDirectionSpan_eq_vectorSpan]
    exact hind.finrank_vectorSpan_add_one
  have hupper := sharedCentral_neighbor_count_le P f hf a b hind.injective
    hcover hshare hx
  have hxP := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
  have hlower := dim_le_actualNeighbors_card P hxP
  rw [hP] at hlower
  rw [hmin] at hupper hsize
  have heq : (actualNeighbors P x).card = d := by omega
  change (polytopeGraph P).degree ⟨x, hxP⟩ = P.dim
  rw [← actualNeighbors_card_eq_degree P hxP, hP]
  exact heq

/-- Equality in the local degree bound forces a unique neighbor in
each other full class. This includes the common central class and
does not assume a pre-existing system of crossing matchings. -/
theorem sharedCentral_minimumClass_other_neighbor [Fintype I]
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (a : I → ℝ) (b : I → E d)
    (hind : AffineIndependent ℝ (parameterVector a b))
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    {i : I}
    (hshare : ∀ z ∈ centralVertices P a b, f z = a i • z+b i →
      ∃ j, j ≠ i ∧ f z = a j • z+b j)
    (hmin : (noncentralClass P f a b i).card =
      d + 1 - finrank ℝ (parameterDirectionSpan a b))
    (hsize : 2 ≤ (noncentralClass P f a b i).card)
    {x : E d} (hx : x ∈ noncentralClass P f a b i) (j : I) (hji : j ≠ i) :
    ∃! y : E d, y ∈ fullClass P f a b j ∧ GeneralVertexStep P x y := by
  classical
  letI : Nonempty I := ⟨i⟩
  let J := (Finset.univ : Finset I).erase i
  let N := classNeighbors P f a b x
  have hxP := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
  have htm : finrank ℝ (parameterDirectionSpan a b) + 1 = Fintype.card I := by
    rw [parameterDirectionSpan_eq_vectorSpan]
    exact hind.finrank_vectorSpan_add_one
  have hJ : J.card = Fintype.card I - 1 := by simp [J]
  have hNj (k : I) (hk : k ∈ J) : (N k).card ≤ 1 :=
    classNeighbors_card_le_one P f hf a b hxP k
      (noncentral_not_other_parameter P f a b hind.injective hx
        (Finset.mem_erase.mp hk).1)
  have hsimple := sharedCentral_minimumClass_simple P hP f hf a b hind
    hcover hshare hmin hsize hx
  have hactual : (actualNeighbors P x).card = d := by
    rw [actualNeighbors_card_eq_degree P hxP]
    exact hsimple.trans hP
  have htotal : (actualNeighbors P x).card ≤
      (noncentralClass P f a b i).card - 1 + ∑ k ∈ J, (N k).card := by
    have hc := (Finset.card_le_card
      (sharedCentral_neighbors_covered P f a b hcover hshare hx)).trans
      (Finset.card_union_le _ _)
    rw [Finset.card_erase_of_mem hx] at hc
    exact hc.trans (Nat.add_le_add_left Finset.card_biUnion_le _)
  have hj : j ∈ J := Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩
  have hnonempty : (N j).Nonempty := by
    by_contra hn
    have hz : (N j).card = 0 :=
      Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hn)
    have hstrict := Finset.sum_lt_sum hNj
      ⟨j, hj, (by omega : (N j).card < 1)⟩
    have hsum : (∑ k ∈ J, (N k).card) < J.card := calc
      (∑ k ∈ J, (N k).card) < ∑ k ∈ J, (1 : ℕ) :=
        Finset.sum_lt_sum hNj ⟨j, hj, (by omega : (N j).card < 1)⟩
      _ = J.card := by simp
    rw [hactual, hmin] at htotal
    rw [hmin] at hsize
    omega
  obtain ⟨y, hy⟩ := hnonempty
  refine ⟨y, Finset.mem_filter.mp hy, ?_⟩
  intro z hz
  exact Finset.card_le_one.mp (hNj j hj) z
    (Finset.mem_filter.mpr hz) y hy


theorem sharedCentral_other_neighbor_noncentral [Fintype I]
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (a : I → ℝ) (b : I → E d)
    (hind : AffineIndependent ℝ (parameterVector a b))
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y+b j)
    {i j : I}
    (hshare : ∀ z ∈ centralVertices P a b, f z = a i • z+b i →
      ∃ j, j ≠ i ∧ f z = a j • z+b j)
    (hji : j ≠ i)
    (hnever : ∀ z ∈ centralVertices P a b,
      f z = a i • z+b i → f z ≠ a j • z+b j)
    (hmin : (noncentralClass P f a b i).card =
      d+1-finrank ℝ (parameterDirectionSpan a b))
    (hsize : 2 ≤ (noncentralClass P f a b i).card)
    {x : E d} (hx : x ∈ noncentralClass P f a b i) :
    ∃! y : E d, y ∈ noncentralClass P f a b j ∧ GeneralVertexStep P x y := by
  obtain ⟨y,⟨hy,hxy⟩,huniq⟩ := sharedCentral_minimumClass_other_neighbor
    P hP f hf a b hind hcover hshare hmin hsize hx j hji
  have hyD : vertexVector y ∉ parameterDirectionSpan a b := by
    intro hyD
    have hxP := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
    have hyi := central_edge_owner P f hf a b hcover hxy.1 hyD
      (Finset.mem_filter.mp hx).2 (generalVertexStep_symm hxP hxy)
      (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
    exact hnever y (Finset.mem_filter.mpr ⟨hxy.1,hyD⟩) hyi (Finset.mem_filter.mp hy).2
  refine ⟨y,⟨Finset.mem_filter.mpr ⟨hy,hyD⟩,hxy⟩,?_⟩
  intro z hz
  exact huniq z ⟨(Finset.mem_filter.mp hz.1).1,hz.2⟩

theorem exists_sharedCentral_crossing_matching [Fintype I]
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (a : I → ℝ) (b : I → E d)
    (hind : AffineIndependent ℝ (parameterVector a b))
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    {i j : I}
    (hshare : ∀ z ∈ centralVertices P a b, f z = a i • z+b i →
      ∃ j, j ≠ i ∧ f z = a j • z+b j)
    (hji : j ≠ i)
    (hnever : ∀ z ∈ centralVertices P a b,
      f z = a i • z+b i → f z ≠ a j • z+b j)
    (hmin : (noncentralClass P f a b i).card =
      d + 1 - finrank ℝ (parameterDirectionSpan a b))
    (hsize : 2 ≤ (noncentralClass P f a b i).card) :
    ∃ M : noncentralClass P f a b i → noncentralClass P f a b j,
      Function.Injective M ∧ ∀ u, GeneralVertexStep P u.val (M u).val := by
  classical
  have hex (u : noncentralClass P f a b i) :
      ∃ y : noncentralClass P f a b j, GeneralVertexStep P u.val y.val := by
    obtain ⟨y, hy, _⟩ := sharedCentral_other_neighbor_noncentral
      P hP f hf a b hind hcover hshare hji hnever hmin hsize u.property
    exact ⟨⟨y, hy.1⟩, hy.2⟩
  let M := fun u => (hex u).choose
  have hM (u : noncentralClass P f a b i) :
      GeneralVertexStep P u.val (M u).val := (hex u).choose_spec
  refine ⟨M, ?_, hM⟩
  intro u v huv
  let y := (M u).val
  have hyj : y ∈ noncentralClass P f a b j := (M u).property
  have hyP := (Finset.mem_filter.mp (Finset.mem_filter.mp hyj).1).1
  have hnot := noncentral_not_other_parameter P f a b hind.injective hyj hji.symm
  have hc := classNeighbors_card_le_one P f hf a b hyP i hnot
  have huy : GeneralVertexStep P y u.val :=
    generalVertexStep_symm
      (Finset.mem_filter.mp (Finset.mem_filter.mp u.property).1).1 (hM u)
  have hvy : GeneralVertexStep P y v.val := by
    have hv := generalVertexStep_symm
      (Finset.mem_filter.mp (Finset.mem_filter.mp v.property).1).1 (hM v)
    change GeneralVertexStep P (M u).val v.val
    rwa [huv]
  apply Subtype.ext
  exact Finset.card_le_one.mp hc u.val
    (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp u.property).1, huy⟩) v.val
    (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp v.property).1, hvy⟩)

end Papers.Polytopes.HomothetyParameters

end
end
end BundlePart0

