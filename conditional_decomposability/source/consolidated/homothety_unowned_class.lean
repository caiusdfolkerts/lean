module
public import consolidated.homothety_central_clique
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

set_option Elab.async false

section BundlePart0
/- Source: Papers/HomothetyClassNeighbors.lean -/







@[expose] public section

/-!
# Neighbors of a homothety class

A vertex outside a full homothety class has at most one neighbor in
that class: two neighbors force the same homothety at the vertex by
the noncollinearity of three actual polytope vertices. If all central
vertices have a common owner, this gives the local degree bound used
in Lemma 10. At a minimum noncentral class, the bound is exactly the
ambient dimension, so its vertices are simple and have a neighbor in
every other full class.

These assertions concern the actual edge graph. They do not assume
simple vertices, crossing matchings, or a combinatorial model of the
classes. The subsequent supporting-facet construction is separate.

Development status: this new module awaits its first compiler check.
-/

noncomputable section
namespace Papers.Polytopes.HomothetyParameters

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {I : Type*}

def actualNeighbors (P : ConvexPolytope d) (x : E d) : Finset (E d) :=
  P.vertices.filter (GeneralVertexStep P x)

def classNeighbors (P : ConvexPolytope d) (f : E d → E d)
    (a : I → ℝ) (b : I → E d) (x : E d) (j : I) : Finset (E d) :=
  (fullClass P f a b j).filter (GeneralVertexStep P x)

theorem actualNeighbors_eq_neighborVertices (P : ConvexPolytope d)
    {x : E d} (hx : x ∈ P.vertices) :
    actualNeighbors P x = neighborVertices P ⟨x, hx⟩ := by
  classical
  ext y
  constructor
  · intro hy
    obtain ⟨hyP, hxy⟩ := Finset.mem_filter.mp hy
    exact Finset.mem_image.mpr
      ⟨⟨⟨y, hyP⟩, (adj_iff_generalVertexStep P ⟨x, hx⟩ ⟨y, hyP⟩).mpr hxy⟩,
        Finset.mem_univ _, rfl⟩
  · intro hy
    obtain ⟨u, _, rfl⟩ := Finset.mem_image.mp hy
    exact Finset.mem_filter.mpr ⟨u.val.property,
      (adj_iff_generalVertexStep P ⟨x, hx⟩ u.val).mp u.property⟩

theorem actualNeighbors_card_eq_degree (P : ConvexPolytope d)
    {x : E d} (hx : x ∈ P.vertices) :
    (actualNeighbors P x).card = (polytopeGraph P).degree ⟨x, hx⟩ := by
  rw [actualNeighbors_eq_neighborVertices P hx, neighborVertices,
    Finset.card_image_of_injective _
      (fun u v h => Subtype.ext (Subtype.ext h)), Finset.card_univ,
    SimpleGraph.card_neighborSet_eq_degree]

theorem dim_le_actualNeighbors_card (P : ConvexPolytope d)
    {x : E d} (hx : x ∈ P.vertices) : P.dim ≤ (actualNeighbors P x).card := by
  apply dim_le_neighbor_cover P hx
  intro y hxy
  exact Finset.mem_filter.mpr ⟨hxy.1, hxy⟩

/-- The actual crossing edges toward a full class form a partial
matching on the vertices outside that class. -/
theorem classNeighbors_card_le_one (P : ConvexPolytope d)
    (f : E d → E d) (hf : IsParallelMap P f) (a : I → ℝ) (b : I → E d)
    {x : E d} (hx : x ∈ P.vertices) (j : I)
    (hxj : f x ≠ a j • x + b j) : (classNeighbors P f a b x j).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro y hy z hz
  by_contra hyz
  obtain ⟨hyj, hxy⟩ := Finset.mem_filter.mp hy
  obtain ⟨hzj, hxz⟩ := Finset.mem_filter.mp hz
  obtain ⟨hyP, hfy⟩ := Finset.mem_filter.mp hyj
  obtain ⟨hzP, hfz⟩ := Finset.mem_filter.mp hzj
  exact hxj (homothety_at_two_neighbors P f hyP hx hzP hyz
    hxy.2.1 hxz.2.1 hfy hfz
    (hf y hyP x hx (generalVertexStep_symm hx hxy))
    (hf z hzP x hx (generalVertexStep_symm hx hxz)))

theorem noncentral_not_other_parameter (P : ConvexPolytope d)
    (f : E d → E d) (a : I → ℝ) (b : I → E d)
    (hinj : Function.Injective (parameterVector a b))
    {i j : I} {x : E d} (hx : x ∈ noncentralClass P f a b i) (hji : j ≠ i) :
    f x ≠ a j • x + b j := by
  intro hxj
  exact hji (noncentral_vertex_private P f a b hinj hx j hxj)

/-- Every neighbor is either a noncentral classmate or belongs to a
different full class. A central classmate is placed in the common
central class, which is why it is not silently counted among the `r`
noncentral vertices. -/
theorem neighbors_covered_by_other_classes [Fintype I]
    (P : ConvexPolytope d) (f : E d → E d) (a : I → ℝ) (b : I → E d)
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    (h : I) (hcentral : ∀ z ∈ centralVertices P a b, f z = a h • z + b h)
    {i : I} (hih : i ≠ h) {x : E d} (hx : x ∈ noncentralClass P f a b i) :
    actualNeighbors P x ⊆ (noncentralClass P f a b i).erase x ∪
      ((Finset.univ : Finset I).erase i).biUnion (classNeighbors P f a b x) := by
  classical
  intro y hy
  obtain ⟨hyP, hxy⟩ := Finset.mem_filter.mp hy
  by_cases hyi : y ∈ noncentralClass P f a b i
  · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hxy.2.1.symm, hyi⟩)
  · apply Finset.mem_union_right
    by_cases hyD : vertexVector y ∈ parameterDirectionSpan a b
    · exact Finset.mem_biUnion.mpr ⟨h, Finset.mem_erase.mpr
        ⟨hih.symm, Finset.mem_univ h⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
          ⟨hyP, hcentral y (Finset.mem_filter.mpr ⟨hyP, hyD⟩)⟩, hxy⟩⟩
    · obtain ⟨j, hyj⟩ := hcover y hyP
      have hji : j ≠ i := by
        intro he
        subst j
        exact hyi (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hyP, hyj⟩, hyD⟩)
      exact Finset.mem_biUnion.mpr ⟨j, Finset.mem_erase.mpr
        ⟨hji, Finset.mem_univ j⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hyP, hyj⟩, hxy⟩⟩

theorem commonCentral_neighbor_count_le [Fintype I]
    (P : ConvexPolytope d) (f : E d → E d) (hf : IsParallelMap P f)
    (a : I → ℝ) (b : I → E d)
    (hinj : Function.Injective (parameterVector a b))
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    (h : I) (hcentral : ∀ z ∈ centralVertices P a b, f z = a h • z + b h)
    {i : I} (hih : i ≠ h) {x : E d} (hx : x ∈ noncentralClass P f a b i) :
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
    (neighbors_covered_by_other_classes P f a b hcover h hcentral hih hx)).trans
    (Finset.card_union_le _ _)
  have hJ : J.card = Fintype.card I - 1 := by simp [J]
  rw [Finset.card_erase_of_mem hx] at hc
  change (actualNeighbors P x).card ≤ (noncentralClass P f a b i).card - 1 +
    (J.biUnion (classNeighbors P f a b x)).card at hc
  omega

/-- A vertex of a minimum class other than the common central class is
simple in the actual polytope. The cardinality `r` is its actual
quotient dimension, derived from the independent parameter family. -/
theorem commonCentral_minimumClass_simple [Fintype I]
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (a : I → ℝ) (b : I → E d)
    (hind : AffineIndependent ℝ (parameterVector a b))
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    (h : I) (hcentral : ∀ z ∈ centralVertices P a b, f z = a h • z + b h)
    {i : I} (hih : i ≠ h)
    (hmin : (noncentralClass P f a b i).card =
      d + 1 - finrank ℝ (parameterDirectionSpan a b))
    (hsize : 2 ≤ (noncentralClass P f a b i).card)
    {x : E d} (hx : x ∈ noncentralClass P f a b i) :
    IsSimpleVertex P ⟨x, (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1⟩ := by
  letI : Nonempty I := ⟨i⟩
  have htm : finrank ℝ (parameterDirectionSpan a b) + 1 = Fintype.card I := by
    rw [parameterDirectionSpan_eq_vectorSpan]
    exact hind.finrank_vectorSpan_add_one
  have hupper := commonCentral_neighbor_count_le P f hf a b hind.injective
    hcover h hcentral hih hx
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
theorem commonCentral_minimumClass_other_neighbor [Fintype I]
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (a : I → ℝ) (b : I → E d)
    (hind : AffineIndependent ℝ (parameterVector a b))
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    (h : I) (hcentral : ∀ z ∈ centralVertices P a b, f z = a h • z + b h)
    {i : I} (hih : i ≠ h)
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
  have hsimple := commonCentral_minimumClass_simple P hP f hf a b hind
    hcover h hcentral hih hmin hsize hx
  have hactual : (actualNeighbors P x).card = d := by
    rw [actualNeighbors_card_eq_degree P hxP]
    exact hsimple.trans hP
  have htotal : (actualNeighbors P x).card ≤
      (noncentralClass P f a b i).card - 1 + ∑ k ∈ J, (N k).card := by
    have hc := (Finset.card_le_card
      (neighbors_covered_by_other_classes P f a b hcover h hcentral hih hx)).trans
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

/-- The excess hypothesis in Lemma 10 supplies a minimum class other
than the common central one. Its existence is a proved pigeonhole
consequence of the actual class bound, not an additional assumption. -/
theorem exists_minimum_class_away_of_excess [Fintype I]
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (a : I → ℝ) (b : I → E d)
    (hind : AffineIndependent ℝ (parameterVector a b))
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    (hprivate : ∀ i, ∃ x ∈ fullClass P f a b i,
      ∀ j, f x = a j • x + b j → j = i)
    (hm : 2 ≤ Fintype.card I) (h : I)
    (hbudget : (∑ j ∈ (Finset.univ : Finset I).erase h,
      ((noncentralClass P f a b j).card -
        (d + 1 - finrank ℝ (parameterDirectionSpan a b)))) ≤
      finrank ℝ (parameterDirectionSpan a b) - 2) :
    ∃ i : I, i ≠ h ∧ (noncentralClass P f a b i).card =
      d + 1 - finrank ℝ (parameterDirectionSpan a b) := by
  classical
  letI : Nonempty I := ⟨h⟩
  let t := finrank ℝ (parameterDirectionSpan a b)
  let r := d + 1 - t
  let J := (Finset.univ : Finset I).erase h
  let e : I → ℕ := fun j => (noncentralClass P f a b j).card - r
  have htm : t + 1 = Fintype.card I := by
    dsimp [t]
    rw [parameterDirectionSpan_eq_vectorSpan]
    exact hind.finrank_vectorSpan_add_one
  have hJ : J.card = t := by simp only [J, Finset.card_erase_of_mem
    (Finset.mem_univ h), Finset.card_univ]; omega
  by_contra hn
  push_neg at hn
  have he (j : I) (hj : j ∈ J) : 1 ≤ e j := by
    obtain ⟨x, hx, hpriv⟩ := hprivate j
    have hb := class_bound P hP f hf a b hcover j hx hpriv
    have hne := hn j (Finset.mem_erase.mp hj).1
    change r ≤ (noncentralClass P f a b j).card at hb
    change (noncentralClass P f a b j).card ≠ r at hne
    dsimp [e]
    omega
  have hsum := Finset.sum_le_sum (s := J) (fun j hj => he j hj)
  have htotal : t ≤ ∑ j ∈ J, e j := calc
    t = ∑ j ∈ J, (1 : ℕ) := by simp [hJ]
    _ ≤ ∑ j ∈ J, e j := Finset.sum_le_sum he
  change (∑ j ∈ J, e j) ≤ t - 2 at hbudget
  omega

end Papers.Polytopes.HomothetyParameters

end
end
end BundlePart0

section BundlePart1
/- Source: Papers/HomothetyCrossingMatching.lean -/




@[expose] public section

/-!
# Actual crossing matchings from a minimum class

With independent homothety parameters and a common central owner, the
neighbor from a minimum class toward any other noncentral class is
noncentral. Its existence comes from the actual degree equality, and
its uniqueness comes from two-neighbor homothety propagation.
The resulting maps between classes are proved injective. No abstract
matching is supplied as a hypothesis.

Development status: this new module awaits its first compiler check.
-/

noncomputable section
namespace Papers.Polytopes.HomothetyParameters

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {I : Type*} [Fintype I]

theorem third_owner_eq (f : E d → E d) (a : I → ℝ) (b : I → E d)
    (hind : AffineIndependent ℝ (parameterVector a b))
    {x : E d} {i j k : I} (hij : i ≠ j)
    (hi : f x = a i • x + b i) (hj : f x = a j • x + b j)
    (hk : f x = a k • x + b k) : k = i ∨ k = j := by
  classical
  by_contra hn
  push_neg at hn
  have hsub : ({i, j, k} : Finset I) ⊆ owners f a b x := by
    intro l hl
    simp only [Finset.mem_insert, Finset.mem_singleton] at hl
    rcases hl with rfl | rfl | rfl
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hi⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hj⟩
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hk⟩
  have hc := (Finset.card_le_card hsub).trans (owners_card_le_two f a b hind x)
  have hcard : ({i, j, k} : Finset I).card = 3 := by
    simp [hij, hn.1.symm, hn.2.symm]
  rw [hcard] at hc
  omega

/-- If a neighbor of a noncentral `i` vertex lies in class `j`, with
both indices different from the common central class, then that
neighbor is noncentral. Otherwise it would have three owners. -/
theorem other_class_neighbor_noncentral
    (P : ConvexPolytope d) (f : E d → E d) (hf : IsParallelMap P f)
    (a : I → ℝ) (b : I → E d)
    (hind : AffineIndependent ℝ (parameterVector a b))
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    (h : I) (hcentral : ∀ z ∈ centralVertices P a b, f z = a h • z + b h)
    {i j : I} (hih : i ≠ h) (hji : j ≠ i) (hjh : j ≠ h)
    {x y : E d} (hx : x ∈ noncentralClass P f a b i)
    (hy : y ∈ fullClass P f a b j) (hxy : GeneralVertexStep P x y) :
    y ∈ noncentralClass P f a b j := by
  refine Finset.mem_filter.mpr ⟨hy, ?_⟩
  intro hyD
  obtain ⟨hyP, hyj⟩ := Finset.mem_filter.mp hy
  obtain ⟨hxi, hxD⟩ := Finset.mem_filter.mp hx
  obtain ⟨hxP, hxi⟩ := Finset.mem_filter.mp hxi
  have hyi := central_edge_owner P f hf a b hcover hyP hyD hxD
    (generalVertexStep_symm hxP hxy) hxi
  have hyh := hcentral y (Finset.mem_filter.mpr ⟨hyP, hyD⟩)
  exact (third_owner_eq f a b hind hih hyi hyh hyj).elim hji hjh

/-- The degree argument supplies an actual noncentral neighbor toward
each class different from the source and common central classes. -/
theorem commonCentral_minimumClass_noncentral_neighbor
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (a : I → ℝ) (b : I → E d)
    (hind : AffineIndependent ℝ (parameterVector a b))
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    (h : I) (hcentral : ∀ z ∈ centralVertices P a b, f z = a h • z + b h)
    {i j : I} (hih : i ≠ h) (hji : j ≠ i) (hjh : j ≠ h)
    (hmin : (noncentralClass P f a b i).card =
      d + 1 - finrank ℝ (parameterDirectionSpan a b))
    (hsize : 2 ≤ (noncentralClass P f a b i).card)
    {x : E d} (hx : x ∈ noncentralClass P f a b i) :
    ∃! y : E d, y ∈ noncentralClass P f a b j ∧ GeneralVertexStep P x y := by
  obtain ⟨y, ⟨hy, hxy⟩, huniq⟩ :=
    commonCentral_minimumClass_other_neighbor P hP f hf a b hind hcover
      h hcentral hih hmin hsize hx j hji
  refine ⟨y, ⟨other_class_neighbor_noncentral P f hf a b hind hcover h hcentral
    hih hji hjh hx hy hxy, hxy⟩, ?_⟩
  intro z hz
  exact huniq z ⟨(Finset.mem_filter.mp hz.1).1, hz.2⟩

/-- Actual matching from a minimum class to another noncentral class.
The matching is built from edges already present in the polytope. -/
theorem exists_crossing_matching
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (a : I → ℝ) (b : I → E d)
    (hind : AffineIndependent ℝ (parameterVector a b))
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    (h : I) (hcentral : ∀ z ∈ centralVertices P a b, f z = a h • z + b h)
    {i j : I} (hih : i ≠ h) (hji : j ≠ i) (hjh : j ≠ h)
    (hmin : (noncentralClass P f a b i).card =
      d + 1 - finrank ℝ (parameterDirectionSpan a b))
    (hsize : 2 ≤ (noncentralClass P f a b i).card) :
    ∃ M : noncentralClass P f a b i → noncentralClass P f a b j,
      Function.Injective M ∧ ∀ u, GeneralVertexStep P u.val (M u).val := by
  classical
  have hex (u : noncentralClass P f a b i) :
      ∃ y : noncentralClass P f a b j, GeneralVertexStep P u.val y.val := by
    obtain ⟨y, hy, _⟩ := commonCentral_minimumClass_noncentral_neighbor
      P hP f hf a b hind hcover h hcentral hih hji hjh hmin hsize u.property
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
end BundlePart1

section BundlePart2
/- Source: Papers/SimpleVertexFacets.lean -/





@[expose] public section

/-!
# The facets incident with a simple vertex

The edge-basis coordinates define the actual incident facets.  Their
dimensions are obtained by identifying their direction spaces with the
kernels of basis coordinates.  Conversely every incident facet is one of
these coordinate facets, using its nonnegative expansion in the edge
basis.  Thus the local facet labels used by restoration are derived from
simplicity and ordinary exposed faces.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

def simpleFacetForm (P : ConvexPolytope d) (hP : P.IsFullDim)
    (v : VertexType P) (hs : IsSimpleVertex P v) (i : NeighborIndex P v) :
    E d →ᵃ[ℝ] ℝ :=
  ((simpleVertexBasis P hP v hs).coord i).toAffineMap -
    AffineMap.const ℝ (E d) ((simpleVertexBasis P hP v hs).coord i v.val)

theorem simpleFacetForm_apply (P : ConvexPolytope d) (hP : P.IsFullDim)
    (v : VertexType P) (hs : IsSimpleVertex P v) (i : NeighborIndex P v) (x : E d) :
    simpleFacetForm P hP v hs i x = (simpleVertexBasis P hP v hs).coord i (x - v.val) := by
  change (simpleVertexBasis P hP v hs).coord i x -
    (simpleVertexBasis P hP v hs).coord i v.val = _
  rw [map_sub]

@[simp] theorem simpleFacetForm_at_vertex (P : ConvexPolytope d) (hP : P.IsFullDim)
    (v : VertexType P) (hs : IsSimpleVertex P v) (i : NeighborIndex P v) :
    simpleFacetForm P hP v hs i v.val = 0 := by
  rw [simpleFacetForm_apply, sub_self, map_zero]

@[simp] theorem simpleFacetForm_at_neighbor (P : ConvexPolytope d) (hP : P.IsFullDim)
    (v : VertexType P) (hs : IsSimpleVertex P v) (i j : NeighborIndex P v) :
    simpleFacetForm P hP v hs i j.val.val = if i = j then 1 else 0 := by
  rw [simpleFacetForm_apply, ← simpleVertexBasis_apply P hP v hs j]
  simp only [Basis.coord_apply, Basis.repr_self, Finsupp.single_apply, eq_comm]

theorem simpleFacetForm_nonneg (P : ConvexPolytope d) (hP : P.IsFullDim)
    (v : VertexType P) (hs : IsSimpleVertex P v) (i : NeighborIndex P v) :
    ∀ x ∈ P.toSet, 0 ≤ simpleFacetForm P hP v hs i x := by
  intro x hx
  rw [simpleFacetForm_apply]
  exact simpleVertexBasis_coordinates_nonneg P hP v hs x hx i

def simpleFacetSet (P : ConvexPolytope d) (hP : P.IsFullDim)
    (v : VertexType P) (hs : IsSimpleVertex P v) (i : NeighborIndex P v) : Set (E d) :=
  affineZeroFace P (simpleFacetForm P hP v hs i)

theorem vertex_mem_simpleFacetSet (P : ConvexPolytope d) (hP : P.IsFullDim)
    (v : VertexType P) (hs : IsSimpleVertex P v) (i : NeighborIndex P v) :
    v.val ∈ simpleFacetSet P hP v hs i :=
  ⟨subset_convexHull ℝ _ v.property, simpleFacetForm_at_vertex P hP v hs i⟩

theorem neighbor_mem_simpleFacetSet_iff (P : ConvexPolytope d) (hP : P.IsFullDim)
    (v : VertexType P) (hs : IsSimpleVertex P v) (i j : NeighborIndex P v) :
    j.val.val ∈ simpleFacetSet P hP v hs i ↔ i ≠ j := by
  change (j.val.val ∈ P.toSet ∧ simpleFacetForm P hP v hs i j.val.val = 0) ↔ _
  have hjP : j.val.val ∈ P.toSet := subset_convexHull ℝ _ j.val.property
  rw [and_iff_right hjP, simpleFacetForm_at_neighbor]
  by_cases hij : i = j <;> simp [hij]

theorem simpleFacetSet_isFace (P : ConvexPolytope d) (hP : P.IsFullDim)
    (v : VertexType P) (hs : IsSimpleVertex P v) (i : NeighborIndex P v) :
    P.IsFace (simpleFacetSet P hP v hs i) :=
  affineZeroFace_isFace P _ (simpleFacetForm_nonneg P hP v hs i)
    ⟨v.val, vertex_mem_simpleFacetSet P hP v hs i⟩

theorem simpleFacetSet_support (P : ConvexPolytope d) (hP : P.IsFullDim)
    (v : VertexType P) (hs : IsSimpleVertex P v) (i : NeighborIndex P v) :
    SupportsFace P (simpleFacetSet P hP v hs i) (simpleFacetForm P hP v hs i) :=
  ⟨simpleFacetForm_nonneg P hP v hs i, rfl⟩

theorem simpleFacetSet_direction (P : ConvexPolytope d) (hP : P.IsFullDim)
    (v : VertexType P) (hs : IsSimpleVertex P v) (i : NeighborIndex P v) :
    vectorSpan ℝ (simpleFacetSet P hP v hs i) =
      ((simpleVertexBasis P hP v hs).coord i).ker := by
  let b := simpleVertexBasis P hP v hs
  let F := simpleFacetSet P hP v hs i
  apply le_antisymm
  · rw [vectorSpan_def]
    apply Submodule.span_le.mpr
    intro z hz
    obtain ⟨x, hx, y, hy, rfl⟩ := Set.mem_vsub.mp hz
    have hx0 := hx.2
    have hy0 := hy.2
    rw [simpleFacetForm_apply] at hx0 hy0
    change b.coord i (x - y) = 0
    change b.coord i (x - v.val) = 0 at hx0
    change b.coord i (y - v.val) = 0 at hy0
    rw [map_sub] at hx0 hy0 ⊢
    linarith
  · intro z hz
    change b.coord i z = 0 at hz
    rw [← b.sum_repr z]
    apply Submodule.sum_mem
    intro j _
    by_cases hji : j = i
    · subst j
      have hrepr : b.repr z i = 0 := hz
      rw [hrepr, zero_smul]
      exact Submodule.zero_mem _
    · apply Submodule.smul_mem
      rw [show b j = j.val.val - v.val from simpleVertexBasis_apply P hP v hs j]
      exact vsub_mem_vectorSpan ℝ
        ((neighbor_mem_simpleFacetSet_iff P hP v hs i j).mpr (Ne.symm hji))
        (vertex_mem_simpleFacetSet P hP v hs i)

theorem simpleFacetSet_isFacet (P : ConvexPolytope d) (hP : P.IsFullDim)
    (v : VertexType P) (hs : IsSimpleVertex P v) (i : NeighborIndex P v) :
    IsFacet P (simpleFacetSet P hP v hs i) := by
  refine ⟨simpleFacetSet_isFace P hP v hs i, ?_⟩
  let b := simpleVertexBasis P hP v hs
  have hsur : Function.Surjective (b.coord i) := by
    intro t
    refine ⟨t • b i, ?_⟩
    simp [map_smul, Basis.coord_apply, Basis.repr_self, Finsupp.single_apply,
      smul_eq_mul]
  have hr : (b.coord i).range = ⊤ := LinearMap.range_eq_top.mpr hsur
  have hdim := (b.coord i).finrank_range_add_finrank_ker
  rw [hr, finrank_top, finrank_self, finrank_euclideanSpace_fin] at hdim
  change finrank ℝ (vectorSpan ℝ (simpleFacetSet P hP v hs i)) + 1 = P.dim
  rw [simpleFacetSet_direction, hP]
  change finrank ℝ (b.coord i).ker + 1 = d
  omega

theorem simpleFacetSet_injective (P : ConvexPolytope d) (hP : P.IsFullDim)
    (v : VertexType P) (hs : IsSimpleVertex P v) :
    Function.Injective (simpleFacetSet P hP v hs) := by
  intro i j heq
  by_contra hij
  have hmem := (neighbor_mem_simpleFacetSet_iff P hP v hs j i).mpr (Ne.symm hij)
  rw [← heq] at hmem
  exact ((neighbor_mem_simpleFacetSet_iff P hP v hs i i).mp hmem) rfl

theorem incident_support_expansion
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (v : VertexType P) (hs : IsSimpleVertex P v)
    (f : E d →ᵃ[ℝ] ℝ) (hv : f v.val = 0) (x : E d) :
    f x = ∑ i : NeighborIndex P v,
      f i.val.val * simpleFacetForm P hP v hs i x := by
  let b := simpleVertexBasis P hP v hs
  have h := congrArg f.linear (b.sum_repr (x - v.val))
  have hlin (y : E d) : f.linear (y - v.val) = f y := by
    simpa only [vsub_eq_sub, hv, sub_zero] using f.linear_apply_vsub y v.val
  simp only [map_sum, map_smul, smul_eq_mul,
    show ∀ i, b i = i.val.val - v.val from fun i => simpleVertexBasis_apply P hP v hs i,
    hlin] at h
  rw [h.symm]
  apply Finset.sum_congr rfl
  intro i _
  rw [simpleFacetForm_apply]
  change b.repr (x - v.val) i * f i.val.val = f i.val.val * b.coord i (x - v.val)
  exact mul_comm _ _

/-- Every actual facet through the simple vertex is exactly one of the
edge-coordinate facets. -/
theorem incident_facet_iff_simpleFacetSet
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (v : VertexType P) (hs : IsSimpleVertex P v) (F : Set (E d)) :
    IsFacet P F ∧ v.val ∈ F ↔ ∃ i, F = simpleFacetSet P hP v hs i := by
  constructor
  · rintro ⟨hF, hvF⟩
    obtain ⟨f, hf⟩ := exists_supportsFace P hF.1
    have hfv : f v.val = 0 := hf.eq_zero hvF
    have hc : ∀ i : NeighborIndex P v, 0 ≤ f i.val.val :=
      fun i => hf.1 _ (subset_convexHull ℝ _ i.val.property)
    obtain ⟨i, hi⟩ : ∃ i : NeighborIndex P v, 0 < f i.val.val := by
      by_contra hall
      push_neg at hall
      have hz : ∀ i : NeighborIndex P v, f i.val.val = 0 :=
        fun i => le_antisymm (hall i) (hc i)
      apply hF.support_ne_zero hf
      ext x
      rw [incident_support_expansion P hP v hs f hfv x]
      simp only [hz, zero_mul, Finset.sum_const_zero, AffineMap.coe_zero, Pi.zero_apply]
    refine ⟨i, hF.eq_of_subset (simpleFacetSet_isFace P hP v hs i)
      (simpleFacetSet_isFacet P hP v hs i).ne_toSet ?_⟩
    intro x hx
    have hxP := face_subset_toSet P hF.1 hx
    have hnonneg : ∀ j ∈ (Finset.univ : Finset (NeighborIndex P v)),
        0 ≤ f j.val.val * simpleFacetForm P hP v hs j x :=
      fun j _ => mul_nonneg (hc j) (simpleFacetForm_nonneg P hP v hs j x hxP)
    have hsum : (∑ j : NeighborIndex P v,
        f j.val.val * simpleFacetForm P hP v hs j x) = 0 := by
      rw [← incident_support_expansion P hP v hs f hfv x, hf.eq_zero hx]
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum i (Finset.mem_univ _)
    exact ⟨hxP, (mul_eq_zero.mp hzero).resolve_left (ne_of_gt hi)⟩
  · rintro ⟨i, rfl⟩
    exact ⟨simpleFacetSet_isFacet P hP v hs i, vertex_mem_simpleFacetSet P hP v hs i⟩

end Papers.Polytopes

end
end
end BundlePart2

section BundlePart3
/- Source: Papers/HomothetyCommonFacet.lean -/






@[expose] public section

/-!
# The supporting facet used by a common central class

Choose a minimum class different from the common central class. At one
of its actual simple vertices, omit the unique edge toward the common
class. The resulting ordinary incident facet contains the whole
minimum class. Its homogeneous supporting functional annihilates every
parameter difference between the other classes and is nonzero on the
difference toward the common class.

This constructs the initial facet in Lemma 10. Containment of all the
other full classes and the Shephard conclusion require the subsequent
excess argument; neither is asserted here without proof.

Development status: this new module awaits its first compiler check.
-/

noncomputable section
namespace Papers.Polytopes.HomothetyParameters

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {I : Type*}

theorem edge_target_scale_ne_zero
    (f : E d → E d) (a : I → ℝ) (b : I → E d)
    {x y : E d} {j : I} {μ : ℝ}
    (hxj : f x ≠ a j • x + b j)
    (hyj : f y = a j • y + b j)
    (hμ : f y - f x = μ • (y - x)) : a j - μ ≠ 0 := by
  intro hz
  have hjμ := sub_eq_zero.mp hz
  apply hxj
  calc
    f x = f y - (f y - f x) := by abel
    _ = (a j • y + b j) - μ • (y - x) := by rw [hμ, hyj]
    _ = a j • x + b j := by rw [← hjμ]; module

/-- A supporting functional with zero parameter difference propagates
its zero value along an actual crossing edge. -/
theorem edge_functional_zero_transfer
    (f : E d → E d) (a : I → ℝ) (b : I → E d)
    (L : (ℝ × E d) →ₗ[ℝ] ℝ)
    {x y : E d} {i j : I} {μ : ℝ}
    (hxi : f x = a i • x + b i) (hxj : f x ≠ a j • x + b j)
    (hyj : f y = a j • y + b j)
    (hμ : f y - f x = μ • (y - x))
    (hdiff : L (parameterVector a b j - parameterVector a b i) = 0)
    (hxL : L (vertexVector x) = 0) : L (vertexVector y) = 0 := by
  have hc := edge_target_scale_ne_zero f a b hxj hyj hμ
  rw [edge_parameter_identity f a b hxi hyj hμ, map_sub, map_smul,
    map_smul, hxL, smul_zero, sub_zero, smul_eq_mul] at hdiff
  exact (mul_eq_zero.mp hdiff).resolve_left hc

/-- The facet obtained by omitting the common-class edge at a minimum
class vertex, with its actual supporting functional and exact
parameter-difference values. -/
theorem exists_commonCentral_supporting_facet [Fintype I]
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (a : I → ℝ) (b : I → E d)
    (hind : AffineIndependent ℝ (parameterVector a b))
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    (hprivate : ∀ i, ∃ x ∈ fullClass P f a b i,
      ∀ j, f x = a j • x + b j → j = i)
    (h : I) (hcentral : ∀ z ∈ centralVertices P a b, f z = a h • z + b h)
    {i : I} (hih : i ≠ h)
    (hmin : (noncentralClass P f a b i).card =
      d + 1 - finrank ℝ (parameterDirectionSpan a b))
    (hsize : 2 ≤ (noncentralClass P f a b i).card) :
    ∃ (g : E d →ᵃ[ℝ] ℝ) (L : (ℝ × E d) →ₗ[ℝ] ℝ),
      IsFacet P (affineZeroFace P g) ∧
      (∀ y, L (vertexVector y) = g y) ∧
      (∀ y ∈ P.toSet, 0 ≤ g y) ∧
      (∀ u ∈ noncentralClass P f a b i, g u = 0) ∧
      (∀ j, j ≠ h → L (parameterVector a b j - parameterVector a b i) = 0) ∧
      L (parameterVector a b h - parameterVector a b i) ≠ 0 ∧
      ∃ w ∈ P.vertices, 0 < g w := by
  classical
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega :
    0 < (noncentralClass P f a b i).card)
  have hxP := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
  let v : VertexType P := ⟨x, hxP⟩
  have hs : IsSimpleVertex P v := commonCentral_minimumClass_simple P hP f hf
    a b hind hcover h hcentral hih hmin hsize hx
  obtain ⟨w, ⟨hwh, hxw⟩, _⟩ := commonCentral_minimumClass_other_neighbor
    P hP f hf a b hind hcover h hcentral hih hmin hsize hx h hih.symm
  let widx : NeighborIndex P v :=
    ⟨⟨w, hxw.1⟩, (adj_iff_generalVertexStep P v ⟨w, hxw.1⟩).mpr hxw⟩
  let g := simpleFacetForm P hP v hs widx
  let L := (Papers.AffineCoordinates.affineLift g).comp
    signedHomogeneousEquiv.symm.toLinearMap
  have hL (y : E d) : L (vertexVector y) = g y := by
    change Papers.AffineCoordinates.homogeneousEvaluation (-(-y), (1 : ℝ)) g = g y
    rw [neg_neg, Papers.AffineCoordinates.homogeneousEvaluation_homogenize]
  have hxg : g x = 0 := simpleFacetForm_at_vertex P hP v hs widx
  have hwg : g w = 1 := by
    exact (simpleFacetForm_at_neighbor P hP v hs widx widx).trans (if_pos rfl)
  have hzero_neighbor {y : E d} (hxy : GeneralVertexStep P x y)
      (hyw : y ≠ w) : g y = 0 := by
    let yidx : NeighborIndex P v :=
      ⟨⟨y, hxy.1⟩, (adj_iff_generalVertexStep P v ⟨y, hxy.1⟩).mpr hxy⟩
    have hwiy : widx ≠ yidx := by
      intro he
      exact hyw (congrArg (fun z : NeighborIndex P v => z.val.val) he).symm
    exact (simpleFacetForm_at_neighbor P hP v hs widx yidx).trans (if_neg hwiy)
  obtain ⟨B, hB, hclique, hnonneg, hfacets, hfibers, hinter, hF⟩ :=
    minimumClass_fiber_faces P hP f hf a b hcover hprivate i hsize hmin
  have hAi (u : E d) (hu : u ∈ noncentralClass P f a b i) : g u = 0 := by
    by_cases hux : u = x
    · simpa only [hux] using hxg
    have hxu : GeneralVertexStep P x u :=
      hclique ⟨x, hx⟩ ⟨u, hu⟩ (fun he => hux
        (congrArg Subtype.val he).symm)
    apply hzero_neighbor hxu
    intro huw
    exact noncentral_not_other_parameter P f a b hind.injective hu hih.symm
      (huw.symm ▸ (Finset.mem_filter.mp hwh).2)
  have hother (j : I) (hjh : j ≠ h) :
      L (parameterVector a b j - parameterVector a b i) = 0 := by
    by_cases hji : j = i
    · rw [hji, sub_self, map_zero]
    obtain ⟨y, ⟨hy, hxy⟩, _⟩ := commonCentral_minimumClass_noncentral_neighbor
      P hP f hf a b hind hcover h hcentral hih hji hjh hmin hsize hx
    have hyw : y ≠ w := by
      intro hyw
      exact noncentral_not_other_parameter P f a b hind.injective hy hjh.symm
        (hyw.symm ▸ (Finset.mem_filter.mp hwh).2)
    have hyg := hzero_neighbor hxy hyw
    obtain ⟨μ, hμ⟩ := hf x hxP y hxy.1 hxy
    rw [edge_parameter_identity f a b
      (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
      (Finset.mem_filter.mp (Finset.mem_filter.mp hy).1).2 hμ,
      map_sub, map_smul, map_smul, hL, hL, hxg, hyg,
      smul_zero, smul_zero, sub_self]
  have hcommon : L (parameterVector a b h - parameterVector a b i) ≠ 0 := by
    obtain ⟨μ, hμ⟩ := hf x hxP w hxw.1 hxw
    have hne := edge_target_scale_ne_zero f a b
      (noncentral_not_other_parameter P f a b hind.injective hx hih.symm)
      (Finset.mem_filter.mp hwh).2 hμ
    rw [edge_parameter_identity f a b
      (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
      (Finset.mem_filter.mp hwh).2 hμ,
      map_sub, map_smul, map_smul, hL, hL, hxg, hwg,
      smul_zero, sub_zero, smul_eq_mul, mul_one]
    exact hne
  exact ⟨g, L, simpleFacetSet_isFacet P hP v hs widx, hL,
    simpleFacetForm_nonneg P hP v hs widx, hAi, hother, hcommon,
    w, hxw.1, by rw [hwg]; norm_num⟩

end Papers.Polytopes.HomothetyParameters

end
end
end BundlePart3

section BundlePart4
/- Source: Papers/HomothetyCommonFacetContainment.lean -/




@[expose] public section

/-!
# The excess argument for the common-class facet

The actual crossing matchings place at least `r` vertices of every
noncentral class other than the common central class in the supporting
facet. A vertex of such a class outside that facet could only meet its
own class, the common class, and the excess vertices of the remaining
classes. Its degree would then be less than the dimension.

The excess hypothesis is written `E + 2 ≤ t`, so its meaning does not
depend on truncated natural subtraction at small parameter dimensions.

Development status: this new module awaits its first compiler check.
-/

noncomputable section
namespace Papers.Polytopes.HomothetyParameters

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {I : Type*} [Fintype I]

def supportInside (P : ConvexPolytope d) (f : E d → E d)
    (a : I → ℝ) (b : I → E d) (g : E d →ᵃ[ℝ] ℝ) (j : I) : Finset (E d) :=
  (noncentralClass P f a b j).filter (fun x => g x = 0)

def supportOutside (P : ConvexPolytope d) (f : E d → E d)
    (a : I → ℝ) (b : I → E d) (g : E d →ᵃ[ℝ] ℝ) (j : I) : Finset (E d) :=
  (noncentralClass P f a b j).filter (fun x => g x ≠ 0)

theorem parameter_difference_support_zero
    (a : I → ℝ) (b : I → E d) (L : (ℝ × E d) →ₗ[ℝ] ℝ) {i h j k : I}
    (hother : ∀ l, l ≠ h → L (parameterVector a b l - parameterVector a b i) = 0)
    (hjh : j ≠ h) (hkh : k ≠ h) :
    L (parameterVector a b j - parameterVector a b k) = 0 := by
  calc
    L (parameterVector a b j - parameterVector a b k) =
        L ((parameterVector a b j - parameterVector a b i) -
          (parameterVector a b k - parameterVector a b i)) := congrArg L (by abel)
    _ = 0 := by rw [map_sub, hother j hjh, hother k hkh, sub_self]

theorem minimumClass_supportInside_card_le
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (a : I → ℝ) (b : I → E d)
    (hind : AffineIndependent ℝ (parameterVector a b))
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    (h : I) (hcentral : ∀ z ∈ centralVertices P a b, f z = a h • z + b h)
    {i : I} (hih : i ≠ h)
    (hmin : (noncentralClass P f a b i).card =
      d + 1 - finrank ℝ (parameterDirectionSpan a b))
    (hsize : 2 ≤ (noncentralClass P f a b i).card)
    (g : E d →ᵃ[ℝ] ℝ) (L : (ℝ × E d) →ₗ[ℝ] ℝ)
    (hL : ∀ x, L (vertexVector x) = g x)
    (hAi : ∀ x ∈ noncentralClass P f a b i, g x = 0)
    (hother : ∀ j, j ≠ h → L (parameterVector a b j - parameterVector a b i) = 0)
    (j : I) (hjh : j ≠ h) :
    d + 1 - finrank ℝ (parameterDirectionSpan a b) ≤
      (supportInside P f a b g j).card := by
  classical
  by_cases hji : j = i
  · subst j
    have heq : supportInside P f a b g i = noncentralClass P f a b i := by
      apply Finset.filter_eq_self.mpr
      exact hAi
    rw [heq, hmin]
  obtain ⟨M, hinj, hM⟩ := exists_crossing_matching P hP f hf a b hind hcover
    h hcentral hih hji hjh hmin hsize
  have hMg (u : noncentralClass P f a b i) : g (M u).val = 0 := by
    have hu := Finset.mem_filter.mp (Finset.mem_filter.mp u.property).1
    have hv := Finset.mem_filter.mp (Finset.mem_filter.mp (M u).property).1
    obtain ⟨μ, hμ⟩ := hf u.val hu.1 (M u).val hv.1 (hM u)
    have he := edge_functional_zero_transfer f a b L hu.2
      (noncentral_not_other_parameter P f a b hind.injective u.property hji)
      hv.2 hμ (hother j hjh) (by rw [hL, hAi u.val u.property])
    rwa [hL] at he
  let T : noncentralClass P f a b i → supportInside P f a b g j :=
    fun u => ⟨(M u).val, Finset.mem_filter.mpr ⟨(M u).property, hMg u⟩⟩
  have hT : Function.Injective T := by
    intro u v huv
    apply hinj
    apply Subtype.ext
    exact congrArg (fun v : supportInside P f a b g j => v.val) huv
  have hc := Fintype.card_le_of_injective T hT
  simpa only [Fintype.card_coe, hmin] using hc

theorem supportOutside_card_le_excess
    (P : ConvexPolytope d) (f : E d → E d) (a : I → ℝ) (b : I → E d)
    (g : E d →ᵃ[ℝ] ℝ) (j : I) (r : ℕ)
    (hinside : r ≤ (supportInside P f a b g j).card) :
    (supportOutside P f a b g j).card ≤ (noncentralClass P f a b j).card - r := by
  have hp := Finset.card_filter_add_card_filter_not
    (s := noncentralClass P f a b j) (fun x => g x = 0)
  change (supportInside P f a b g j).card +
    (supportOutside P f a b g j).card = (noncentralClass P f a b j).card at hp
  omega

/-- The degree contradiction in Lemma 10: every noncentral vertex of
every class other than the common central class is in the supporting
hyperplane. The seed and functional are the ones constructed by
`exists_commonCentral_supporting_facet`. -/
theorem all_other_classes_on_support
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (a : I → ℝ) (b : I → E d)
    (hind : AffineIndependent ℝ (parameterVector a b))
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    (h : I) (hcentral : ∀ z ∈ centralVertices P a b, f z = a h • z + b h)
    {i : I} (hih : i ≠ h)
    (hmin : (noncentralClass P f a b i).card =
      d + 1 - finrank ℝ (parameterDirectionSpan a b))
    (hsize : 2 ≤ (noncentralClass P f a b i).card)
    (hbudget : (∑ j ∈ (Finset.univ : Finset I).erase h,
      ((noncentralClass P f a b j).card -
        (d + 1 - finrank ℝ (parameterDirectionSpan a b)))) + 2 ≤
      finrank ℝ (parameterDirectionSpan a b))
    (g : E d →ᵃ[ℝ] ℝ) (L : (ℝ × E d) →ₗ[ℝ] ℝ)
    (hL : ∀ x, L (vertexVector x) = g x)
    (hAi : ∀ x ∈ noncentralClass P f a b i, g x = 0)
    (hother : ∀ j, j ≠ h → L (parameterVector a b j - parameterVector a b i) = 0) :
    ∀ j, j ≠ h → ∀ x ∈ noncentralClass P f a b j, g x = 0 := by
  classical
  let t := finrank ℝ (parameterDirectionSpan a b)
  let r := d + 1 - t
  let J := (Finset.univ : Finset I).erase h
  let e : I → ℕ := fun j => (noncentralClass P f a b j).card - r
  have hinside (j : I) (hjh : j ≠ h) :
      r ≤ (supportInside P f a b g j).card :=
    minimumClass_supportInside_card_le P hP f hf a b hind hcover h hcentral
      hih hmin hsize g L hL hAi hother j hjh
  have houtside (j : I) (hjh : j ≠ h) :
      (supportOutside P f a b g j).card ≤ e j :=
    supportOutside_card_le_excess P f a b g j r (hinside j hjh)
  intro j hjh x hx
  by_contra hxg
  have hxP := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
  have hxj := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
  have hsub : actualNeighbors P x ⊆
      (noncentralClass P f a b j).erase x ∪ classNeighbors P f a b x h ∪
        (J.erase j).biUnion (supportOutside P f a b g) := by
    intro y hy
    obtain ⟨hyP, hxy⟩ := Finset.mem_filter.mp hy
    by_cases hyj : y ∈ noncentralClass P f a b j
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_erase.mpr ⟨hxy.2.1.symm, hyj⟩))
    by_cases hyD : vertexVector y ∈ parameterDirectionSpan a b
    · exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
          ⟨hyP, hcentral y (Finset.mem_filter.mpr ⟨hyP, hyD⟩)⟩, hxy⟩))
    obtain ⟨k, hyk⟩ := hcover y hyP
    by_cases hkh : k = h
    · subst k
      exact Finset.mem_union_left _ (Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hyP, hyk⟩, hxy⟩))
    have hyUk : y ∈ noncentralClass P f a b k :=
      Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hyP, hyk⟩, hyD⟩
    have hkj : k ≠ j := by intro he; exact hyj (he ▸ hyUk)
    have hyg : g y ≠ 0 := by
      intro hyg
      obtain ⟨μ, hμ⟩ := hf y hyP x hxP (generalVertexStep_symm hxP hxy)
      have hh := edge_functional_zero_transfer f a b L hyk
        (noncentral_not_other_parameter P f a b hind.injective hyUk hkj.symm)
        hxj hμ (parameter_difference_support_zero a b L hother hjh hkh)
        (by rw [hL, hyg])
      exact hxg ((hL x).symm.trans hh)
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨k, Finset.mem_erase.mpr ⟨hkj, Finset.mem_erase.mpr
        ⟨hkh, Finset.mem_univ k⟩⟩,
        Finset.mem_filter.mpr ⟨hyUk, hyg⟩⟩)
  have hcommon : (classNeighbors P f a b x h).card ≤ 1 :=
    classNeighbors_card_le_one P f hf a b hxP h
      (noncentral_not_other_parameter P f a b hind.injective hx hjh.symm)
  have hbi : ((J.erase j).biUnion (supportOutside P f a b g)).card ≤
      ∑ k ∈ J.erase j, e k := by
    apply Finset.card_biUnion_le.trans
    apply Finset.sum_le_sum
    intro k hk
    exact houtside k (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
  have hcount := Finset.card_le_card hsub
  have hu₁ := Finset.card_union_le
    ((noncentralClass P f a b j).erase x) (classNeighbors P f a b x h)
  have hu₂ := Finset.card_union_le
    ((noncentralClass P f a b j).erase x ∪ classNeighbors P f a b x h)
    ((J.erase j).biUnion (supportOutside P f a b g))
  rw [Finset.card_erase_of_mem hx] at hu₁
  have hupper : (actualNeighbors P x).card ≤
      (noncentralClass P f a b j).card - 1 + 1 + ∑ k ∈ J.erase j, e k := by omega
  have hj : j ∈ J := Finset.mem_erase.mpr ⟨hjh, Finset.mem_univ j⟩
  have hsum := Finset.sum_erase_add J e hj
  have hclass : r ≤ (noncentralClass P f a b j).card :=
    (hinside j hjh).trans (Finset.card_filter_le _ _)
  have hcard : (noncentralClass P f a b j).card = r + e j := by dsimp [e]; omega
  have hlower := dim_le_actualNeighbors_card P hxP
  rw [hP] at hlower
  have hr : 2 ≤ r := by rw [hmin] at hsize; exact hsize
  have htr : t + r = d + 1 := by dsimp [r]; omega
  change (∑ k ∈ J, e k) + 2 ≤ t at hbudget
  omega

end Papers.Polytopes.HomothetyParameters

end
end
end BundlePart4

section BundlePart5
/- Source: Papers/ShephardDefinitions.lean -/





@[expose] public section

/-! The literal facet property used in the conditional-decomposability paper. -/

namespace Papers.Polytopes

open Set
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

def HasShephardProperty {d : ℕ} (P : ConvexPolytope d) : Prop :=
  ∃ F : Set (E d), IsFacet P F ∧
    ∀ x ∈ P.vertices, x ∈ F →
      ∃! y : E d, GeneralVertexStep P x y ∧ y ∉ F

end Papers.Polytopes

end
end BundlePart5

section BundlePart6
/- Source: Papers/HomothetyCommonCentral.lean -/





@[expose] public section

/-!
# A common central class gives Shephard's property

This is the complete intended proof of Lemma 10. A minimum class away
from the common central owner is obtained from the excess budget. Its
simple vertices construct an actual supporting facet; actual crossing
matchings and the degree bound put every other noncentral class in
that facet. Connectivity of the facet excludes vertices of the common
class. Each remaining facet vertex has exactly one edge leaving it.

Shephard's property is expressed using an ordinary facet of the actual
polytope and uniqueness of an actual exterior neighbor. It is not
defined as decomposability, and the separate theorem relating this
property to decomposability is not asserted here.

The final corollary closes the `s=t-1` case of Proposition 12 under its
full uniform hypotheses. No central clique, common homothety, simple
vertex, matching, or facet is assumed in that corollary.

Development status: these new proofs await their first compiler check.
-/

noncomputable section
namespace Papers.Polytopes

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

namespace HomothetyParameters

variable {I : Type*} [Fintype I]

theorem common_owner_not_on_support_edge
    (P : ConvexPolytope d) (f : E d → E d) (hf : IsParallelMap P f)
    (a : I → ℝ) (b : I → E d) (g : E d →ᵃ[ℝ] ℝ)
    (L : (ℝ × E d) →ₗ[ℝ] ℝ) (hL : ∀ x, L (vertexVector x) = g x)
    {i h j : I}
    (hother : ∀ k, k ≠ h → L (parameterVector a b k - parameterVector a b i) = 0)
    (hcommon : L (parameterVector a b h - parameterVector a b i) ≠ 0)
    (hjh : j ≠ h) {x y : E d} (hx : x ∈ P.vertices)
    (hxj : f x = a j • x + b j) (hxg : g x = 0) (hyg : g y = 0)
    (hxy : GeneralVertexStep P x y) : f y ≠ a h • y + b h := by
  intro hyh
  obtain ⟨μ, hμ⟩ := hf x hx y hxy.1 hxy
  have hzero : L (parameterVector a b h - parameterVector a b j) = 0 := by
    rw [edge_parameter_identity f a b hxj hyh hμ, map_sub, map_smul,
      map_smul, hL, hL, hxg, hyg, smul_zero, smul_zero, sub_self]
  apply hcommon
  calc
    L (parameterVector a b h - parameterVector a b i) =
        L ((parameterVector a b h - parameterVector a b j) +
          (parameterVector a b j - parameterVector a b i)) := congrArg L (by abel)
    _ = 0 := by rw [map_add, hzero, hother j hjh, add_zero]

/-- Connectivity of the actual face rules out any vertex of the common
class in its support. This does not assume that the noncentral part is
connected, or that all face vertices have already been classified. -/
theorem common_owner_not_on_support_face
    (P : ConvexPolytope d) (f : E d → E d) (hf : IsParallelMap P f)
    (a : I → ℝ) (b : I → E d)
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    (g : E d →ᵃ[ℝ] ℝ) (L : (ℝ × E d) →ₗ[ℝ] ℝ)
    (hF : P.IsFace (affineZeroFace P g))
    (hL : ∀ x, L (vertexVector x) = g x)
    {i h : I}
    (hother : ∀ j, j ≠ h → L (parameterVector a b j - parameterVector a b i) = 0)
    (hcommon : L (parameterVector a b h - parameterVector a b i) ≠ 0)
    {x : E d} (hx : x ∈ P.vertices) (hxg : g x = 0)
    (hxnot : f x ≠ a h • x + b h) :
    ∀ y ∈ P.vertices, g y = 0 → f y ≠ a h • y + b h := by
  let Q := facePolytope P hF
  have hxQ : x ∈ Q.vertices := Finset.mem_filter.mpr
    ⟨hx, subset_convexHull ℝ _ hx, hxg⟩
  have hwalk : ∀ z, Relation.ReflTransGen (GeneralVertexStep Q) x z →
      z ∈ Q.vertices ∧ f z ≠ a h • z + b h := by
    intro z hz
    induction hz with
    | refl => exact ⟨hxQ, hxnot⟩
    | @tail u v hpath huv ih =>
      have hu := Finset.mem_filter.mp ih.1
      have hv := Finset.mem_filter.mp huv.1
      obtain ⟨j, huj⟩ := hcover u hu.1
      have hjh : j ≠ h := by intro he; exact ih.2 (he ▸ huj)
      obtain ⟨_, hne, e, he, hde, hue, hve⟩ := huv
      have hstep : GeneralVertexStep P u v :=
        ⟨hv.1, hne, e, isFace_of_facePolytope P hF he, hde, hue, hve⟩
      exact ⟨Finset.mem_filter.mpr hv,
        common_owner_not_on_support_edge P f hf a b g L hL hother hcommon hjh
          hu.1 huj hu.2.2 hv.2.2 hstep⟩
  intro y hy hyg
  have hyQ : y ∈ Q.vertices := Finset.mem_filter.mpr
    ⟨hy, subset_convexHull ℝ _ hy, hyg⟩
  exact (hwalk y (balinski_light_general Q hxQ hyQ)).2

/-- Lemma 10, with its entire facet construction and actual exterior
neighbor uniqueness. The budget uses addition to preserve its integer
meaning at every possible parameter dimension. -/
theorem common_central_class_shephard
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (a : I → ℝ) (b : I → E d)
    (hind : AffineIndependent ℝ (parameterVector a b))
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    (hprivate : ∀ i, ∃ x ∈ fullClass P f a b i,
      ∀ j, f x = a j • x + b j → j = i)
    (h : I) (hcentral : ∀ z ∈ centralVertices P a b, f z = a h • z + b h)
    (hr : 2 ≤ d + 1 - finrank ℝ (parameterDirectionSpan a b))
    (hbudget : (∑ j ∈ (Finset.univ : Finset I).erase h,
      ((noncentralClass P f a b j).card -
        (d + 1 - finrank ℝ (parameterDirectionSpan a b)))) + 2 ≤
      finrank ℝ (parameterDirectionSpan a b)) : HasShephardProperty P := by
  classical
  letI : Nonempty I := ⟨h⟩
  have htm : finrank ℝ (parameterDirectionSpan a b) + 1 = Fintype.card I := by
    rw [parameterDirectionSpan_eq_vectorSpan]
    exact hind.finrank_vectorSpan_add_one
  have hm : 2 ≤ Fintype.card I := by omega
  obtain ⟨i, hih, hmin⟩ := exists_minimum_class_away_of_excess P hP f hf a b
    hind hcover hprivate hm h (by omega)
  have hsize : 2 ≤ (noncentralClass P f a b i).card := by rw [hmin]; exact hr
  obtain ⟨g, L, hfacet, hL, hnonneg, hAi, hother, hcommon, w, hw, hwg⟩ :=
    exists_commonCentral_supporting_facet P hP f hf a b hind hcover hprivate
      h hcentral hih hmin hsize
  have hall := all_other_classes_on_support P hP f hf a b hind hcover h hcentral
    hih hmin hsize hbudget g L hL hAi hother
  obtain ⟨x₀, hx₀⟩ := Finset.card_pos.mp (by omega :
    0 < (noncentralClass P f a b i).card)
  have hx₀P := (Finset.mem_filter.mp (Finset.mem_filter.mp hx₀).1).1
  have hexclude := common_owner_not_on_support_face P f hf a b hcover g L hfacet.1
    hL hother hcommon hx₀P (hAi x₀ hx₀)
    (noncentral_not_other_parameter P f a b hind.injective hx₀ hih.symm)
  have hiff (x : E d) (hx : x ∈ P.vertices) :
      x ∈ affineZeroFace P g ↔ x ∉ fullClass P f a b h := by
    constructor
    · intro hxF hxh
      exact hexclude x hx hxF.2 (Finset.mem_filter.mp hxh).2
    · intro hxnot
      obtain ⟨j, hxj⟩ := hcover x hx
      have hjh : j ≠ h := by
        intro he
        exact hxnot (Finset.mem_filter.mpr ⟨hx, he ▸ hxj⟩)
      have hxD : vertexVector x ∉ parameterDirectionSpan a b := by
        intro hxD
        exact hxnot (Finset.mem_filter.mpr ⟨hx,
          hcentral x (Finset.mem_filter.mpr ⟨hx, hxD⟩)⟩)
      exact ⟨subset_convexHull ℝ _ hx,
        hall j hjh x (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hx, hxj⟩, hxD⟩)⟩
  refine ⟨affineZeroFace P g, hfacet, ?_⟩
  intro x hx hxF
  have hxnot := hexclude x hx hxF.2
  have hlt : g.linear.toContinuousLinearMap x < g.linear.toContinuousLinearMap w := by
    have hxg := hxF.2
    rw [affine_form_apply g x] at hxg
    rw [affine_form_apply g w] at hwg
    change g.linear x < g.linear w
    linarith
  obtain ⟨y, hxy, hxylt⟩ := exists_increasing_edge P g.linear.toContinuousLinearMap
    hx hw hlt
  have hyg : 0 < g y := by
    have hxg := hxF.2
    rw [affine_form_apply g x] at hxg
    rw [affine_form_apply g y]
    change g.linear x < g.linear y at hxylt
    linarith
  have hyF : y ∉ affineZeroFace P g := by intro hyF; exact hyg.ne' hyF.2
  have hyh : y ∈ fullClass P f a b h := by
    by_contra hn
    exact hyF ((hiff y hxy.1).mpr hn)
  refine ⟨y, ⟨hxy, hyF⟩, ?_⟩
  intro z hz
  have hzh : z ∈ fullClass P f a b h := by
    by_contra hn
    exact hz.2 ((hiff z hz.1.1).mpr hn)
  exact Finset.card_le_one.mp (classNeighbors_card_le_one P f hf a b hx h hxnot)
    z (Finset.mem_filter.mpr ⟨hzh, hz.1⟩) y (Finset.mem_filter.mpr ⟨hyh, hxy⟩)

/-- The complete `s=t-1` branch of Proposition 12, before invoking the
separate Shephard decomposability theorem. -/
theorem uniform_central_deficit_one_shephard
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (a : I → ℝ) (b : I → E d)
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    (hprivate : ∀ i, ∃ x ∈ fullClass P f a b i,
      ∀ j, f x = a j • x + b j → j = i)
    (hm : 4 ≤ Fintype.card I) (hd : Fintype.card I + 1 ≤ d)
    (hN : P.vertices.card ≤ 4 * d - 5)
    (hs : (centralVertices P a b).card =
      finrank ℝ (parameterDirectionSpan a b) - 1) : HasShephardProperty P := by
  obtain ⟨hind, htm, ht, hr, hbudget, i, hi⟩ :=
    uniform_parameter_budget P hP f hf a b hcover hprivate hm hd hN
  obtain ⟨h, hh⟩ := uniform_central_deficit_one_common_parameter
    P hP f hf a b hcover hprivate hm hd hN hs
  apply common_central_class_shephard P hP f hf a b hind hcover hprivate h hh (by omega)
  have hsum := Finset.sum_le_sum_of_subset
    (f := fun j => (noncentralClass P f a b j).card -
      (d + 1 - finrank ℝ (parameterDirectionSpan a b)))
    (Finset.subset_univ ((Finset.univ : Finset I).erase h))
  omega

end HomothetyParameters
end Papers.Polytopes

end
end
end BundlePart6

section BundlePart7
/- Source: Papers/HomothetyZeroExcess.lean -/




@[expose] public section

/-!
# The zero-excess central-face case

In the `s = t` case of Proposition 12, the original vertex budget forces
every noncentral class to have the minimum size. Equation (3) then says
that the actual degree in the central face, plus the number of actual
owners, is at least `t`. If the parallel map is homothetic on that face
with a new parameter, the independent-parameter incidence argument
forces the face graph to be complete.

These are reductions within the full parameter range of the proposition.
The existence of a homothety in the remaining cases and the final facet
construction for a new parameter are separate obligations.

Development status: this new module awaits its first compiler check.
-/

noncomputable section
namespace Papers.Polytopes.HomothetyParameters

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {I : Type*} [Fintype I]

/-- Every class is a minimum class when the central count exhausts the
uniform budget. No separate zero-excess assumption is supplied. -/
theorem uniform_zero_excess
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (a : I → ℝ) (b : I → E d)
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    (hprivate : ∀ i, ∃ x ∈ fullClass P f a b i,
      ∀ j, f x = a j • x + b j → j = i)
    (hm : 4 ≤ Fintype.card I) (hd : Fintype.card I + 1 ≤ d)
    (hN : P.vertices.card ≤ 4 * d - 5)
    (hs : (centralVertices P a b).card =
      finrank ℝ (parameterDirectionSpan a b)) :
    ∀ j, (noncentralClass P f a b j).card =
      d + 1 - finrank ℝ (parameterDirectionSpan a b) := by
  classical
  obtain ⟨hind, htm, ht, hr, hbudget, i, hi⟩ :=
    uniform_parameter_budget P hP f hf a b hcover hprivate hm hd hN
  let r := d + 1 - finrank ℝ (parameterDirectionSpan a b)
  let e : I → ℕ := fun j => (noncentralClass P f a b j).card - r
  have hsum : (∑ j, e j) = 0 := by
    change (∑ j, e j) + (centralVertices P a b).card ≤
      finrank ℝ (parameterDirectionSpan a b) at hbudget
    omega
  intro j
  have hej : e j ≤ ∑ k, e k :=
    Finset.single_le_sum (fun k _ => Nat.zero_le (e k)) (Finset.mem_univ j)
  obtain ⟨x, hx, hpriv⟩ := hprivate j
  have hbound := class_bound P hP f hf a b hcover j hx hpriv
  change r ≤ (noncentralClass P f a b j).card at hbound
  rw [hsum] at hej
  dsimp [e] at hej
  change (noncentralClass P f a b j).card = r
  omega

/-- Equation (3), after deriving zero excess from `s=t`. -/
theorem uniform_zero_excess_degree_owners
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (a : I → ℝ) (b : I → E d)
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    (hprivate : ∀ i, ∃ x ∈ fullClass P f a b i,
      ∀ j, f x = a j • x + b j → j = i)
    (hm : 4 ≤ Fintype.card I) (hd : Fintype.card I + 1 ≤ d)
    (hN : P.vertices.card ≤ 4 * d - 5)
    (hs : (centralVertices P a b).card =
      finrank ℝ (parameterDirectionSpan a b))
    {z : E d} (hz : z ∈ centralVertices P a b) :
    finrank ℝ (parameterDirectionSpan a b) ≤
      (faceNeighbors P (centralSection P a b) z).card +
        (owners f a b z).card := by
  classical
  obtain ⟨hind, htm, ht, hr, hbudget, i, hi⟩ :=
    uniform_parameter_budget P hP f hf a b hcover hprivate hm hd hN
  have hmin := uniform_zero_excess P hP f hf a b hcover hprivate hm hd hN hs
  have hsize : 2 ≤ (noncentralClass P f a b i).card := by rw [hi]; omega
  obtain ⟨hzP, hzD⟩ := Finset.mem_filter.mp hz
  have hineq := central_neighbor_inequality P hP f hf a b hcover hprivate
    i hsize hi hzP hzD
  let r := d + 1 - finrank ℝ (parameterDirectionSpan a b)
  let t := finrank ℝ (parameterDirectionSpan a b)
  let deg := (faceNeighbors P (centralSection P a b) z).card
  let o := (owners f a b z).card
  have hzero : (∑ j ∈ owners f a b z,
      ((noncentralClass P f a b j).card - r)) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [hmin j]
    exact Nat.sub_self r
  change r * t ≤ r * deg + r * o + _ at hineq
  rw [hzero, add_zero] at hineq
  change 3 ≤ r at hr
  change t ≤ deg + o
  by_contra hn
  have hgap : deg + o + 1 ≤ t := by omega
  have hmul := Nat.mul_le_mul_left r hgap
  nlinarith

/-- A missing actual central edge reduces the degree bound by two,
because neither its other endpoint nor the vertex itself is a neighbor. -/
theorem central_degree_bound_of_nonadjacent
    (P : ConvexPolytope d) (a : I → ℝ) (b : I → E d)
    {x y : E d} (hx : x ∈ centralVertices P a b)
    (hy : y ∈ centralVertices P a b) (hxy : x ≠ y)
    (hnot : ¬GeneralVertexStep P x y) :
    (faceNeighbors P (centralSection P a b) x).card + 2 ≤
      (centralVertices P a b).card := by
  classical
  let S := centralVertices P a b
  have hyerase : y ∈ S.erase x := Finset.mem_erase.mpr ⟨hxy.symm, hy⟩
  have hsub : faceNeighbors P (centralSection P a b) x ⊆
      (S.erase x).erase y := by
    intro z hz
    refine Finset.mem_erase.mpr ⟨?_, central_neighbors_subset_erase P a b x hz⟩
    intro hzy
    subst z
    exact hnot (Finset.mem_filter.mp hz).2.2
  have hc := Finset.card_le_card hsub
  have hxcard := Finset.card_erase_add_one hx
  have hycard := Finset.card_erase_add_one hyerase
  change (S.erase x).card + 1 = S.card at hxcard
  change (faceNeighbors P (centralSection P a b) x).card + 2 ≤ S.card
  omega

/-- A new homothety on the central face in the `s=t` case forces every
pair of distinct central vertices to be joined by an actual edge. -/
theorem uniform_zero_excess_new_homothety_clique
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (a : I → ℝ) (b : I → E d)
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    (hprivate : ∀ i, ∃ x ∈ fullClass P f a b i,
      ∀ j, f x = a j • x + b j → j = i)
    (hm : 4 ≤ Fintype.card I) (hd : Fintype.card I + 1 ≤ d)
    (hN : P.vertices.card ≤ 4 * d - 5)
    (hs : (centralVertices P a b).card =
      finrank ℝ (parameterDirectionSpan a b))
    {α : ℝ} {c : E d}
    (hH : ∀ z ∈ centralVertices P a b, f z = α • z + c)
    (hnew : ∀ i, (α, c) ≠ parameterVector a b i) :
    ∀ x ∈ centralVertices P a b, ∀ y ∈ centralVertices P a b,
      x ≠ y → GeneralVertexStep P x y := by
  classical
  obtain ⟨hind, htm, ht, hr, hbudget, i, hi⟩ :=
    uniform_parameter_budget P hP f hf a b hcover hprivate hm hd hN
  intro x hx y hy hxy
  by_contra hnot
  have hnot' : ¬GeneralVertexStep P y x := by
    intro hyx
    exact hnot (generalVertexStep_symm (Finset.mem_filter.mp hy).1 hyx)
  have hshared (z w : E d) (hz : z ∈ centralVertices P a b)
      (hw : w ∈ centralVertices P a b) (hzw : z ≠ w)
      (hno : ¬GeneralVertexStep P z w) :
      ∃ i ∈ ownerSet f a b z, ∃ j ∈ ownerSet f a b z, i ≠ j := by
    have hdeg := central_degree_bound_of_nonadjacent P a b hz hw hzw hno
    have hineq := uniform_zero_excess_degree_owners P hP f hf a b
      hcover hprivate hm hd hN hs hz
    have ho : 1 < (owners f a b z).card := by omega
    obtain ⟨j, hj, k, hk, hjk⟩ := Finset.one_lt_card.mp ho
    exact ⟨j, (Finset.mem_filter.mp hj).2, k, (Finset.mem_filter.mp hk).2, hjk⟩
  exact hxy (at_most_one_shared_point_of_new_homothety f a b hind hnew
    (hH x hx) (hH y hy) (hshared x y hx hy hxy hnot)
    (hshared y x hy hx hxy.symm hnot'))

/-- The existing-parameter subcase of `s=t` is the full common-central
class lemma with its excess bound derived from the original budget. -/
theorem uniform_zero_excess_common_parameter_shephard
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (a : I → ℝ) (b : I → E d)
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    (hprivate : ∀ i, ∃ x ∈ fullClass P f a b i,
      ∀ j, f x = a j • x + b j → j = i)
    (hm : 4 ≤ Fintype.card I) (hd : Fintype.card I + 1 ≤ d)
    (hN : P.vertices.card ≤ 4 * d - 5)
    (hs : (centralVertices P a b).card =
      finrank ℝ (parameterDirectionSpan a b))
    (h : I) (hH : ∀ z ∈ centralVertices P a b, f z = a h • z + b h) :
    HasShephardProperty P := by
  obtain ⟨hind, htm, ht, hr, hbudget, i, hi⟩ :=
    uniform_parameter_budget P hP f hf a b hcover hprivate hm hd hN
  have hmin := uniform_zero_excess P hP f hf a b hcover hprivate hm hd hN hs
  apply common_central_class_shephard P hP f hf a b hind hcover hprivate h hH (by omega)
  have he : (∑ j ∈ (Finset.univ : Finset I).erase h,
      ((noncentralClass P f a b j).card -
        (d + 1 - finrank ℝ (parameterDirectionSpan a b)))) = 0 := by
    apply Finset.sum_eq_zero
    intro j hj
    rw [hmin j, Nat.sub_self]
  omega

end Papers.Polytopes.HomothetyParameters

end
end
end BundlePart7

section BundlePart8
/- Source: Papers/HomothetyUnownedClass.lean -/




@[expose] public section

/-!
# A minimum class owning no central vertex

If fewer central vertices than classes are each singly owned, some
class owns none of them. Its minimum-class vertices are simple, and
their actual crossing edges give an injective matching into every
other noncentral class. Central endpoints are excluded by the proved
central-edge ownership identity.

The matching is constructed from actual edge degrees, rather than
included as a combinatorial premise. These lemmas are used in the
new-central-homothety branch of Proposition 12.

Development status: this new module awaits its first compiler check.
-/

noncomputable section
namespace Papers.Polytopes.HomothetyParameters

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {I : Type*} [Fintype I]

theorem exists_unowned_class_of_central_count
    (P : ConvexPolytope d) (f : E d → E d) (a : I → ℝ) (b : I → E d)
    (hcount : (centralVertices P a b).card < Fintype.card I)
    (hsingle : ∀ z ∈ centralVertices P a b, (owners f a b z).card ≤ 1) :
    ∃ i, ∀ z ∈ centralVertices P a b, f z ≠ a i • z + b i := by
  classical
  by_contra hn
  push_neg at hn
  choose z hz howner using hn
  let g : I → centralVertices P a b := fun i => ⟨z i, hz i⟩
  have hinj : Function.Injective g := by
    intro i j hij
    have hpoint : z i = z j := congrArg Subtype.val hij
    have hi : i ∈ owners f a b (z i) :=
      Finset.mem_filter.mpr ⟨Finset.mem_univ i, howner i⟩
    have hj : j ∈ owners f a b (z i) := by
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ j, ?_⟩
      rw [hpoint]
      exact howner j
    exact Finset.card_le_one.mp (hsingle (z i) (hz i)) i hi j hj
  have hc := Fintype.card_le_of_injective g hinj
  rw [Fintype.card_coe] at hc
  omega

/-- The no-shared-central-vertex branch supplies an unowned class from
the original uniform hypotheses. -/
theorem uniform_zero_excess_exists_unowned_class
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (a : I → ℝ) (b : I → E d)
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    (hprivate : ∀ i, ∃ x ∈ fullClass P f a b i,
      ∀ j, f x = a j • x + b j → j = i)
    (hm : 4 ≤ Fintype.card I) (hd : Fintype.card I + 1 ≤ d)
    (hN : P.vertices.card ≤ 4 * d - 5)
    (hs : (centralVertices P a b).card =
      finrank ℝ (parameterDirectionSpan a b))
    (hsingle : ∀ z ∈ centralVertices P a b, (owners f a b z).card ≤ 1) :
    ∃ i, ∀ z ∈ centralVertices P a b, f z ≠ a i • z + b i := by
  obtain ⟨hind, htm, ht, hr, hbudget, i, hi⟩ :=
    uniform_parameter_budget P hP f hf a b hcover hprivate hm hd hN
  exact exists_unowned_class_of_central_count P f a b (by omega) hsingle

theorem unowned_neighbors_covered_by_other_classes
    (P : ConvexPolytope d) (f : E d → E d) (a : I → ℝ) (b : I → E d)
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    {i : I} (hunowned : ∀ z ∈ centralVertices P a b, f z ≠ a i • z + b i)
    {x : E d} (hx : x ∈ noncentralClass P f a b i) :
    actualNeighbors P x ⊆ (noncentralClass P f a b i).erase x ∪
      ((Finset.univ : Finset I).erase i).biUnion (classNeighbors P f a b x) := by
  classical
  intro y hy
  obtain ⟨hyP, hxy⟩ := Finset.mem_filter.mp hy
  by_cases hyi : y ∈ noncentralClass P f a b i
  · exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hxy.2.1.symm, hyi⟩)
  · obtain ⟨j, hyj⟩ := hcover y hyP
    have hji : j ≠ i := by
      intro he
      subst j
      by_cases hyD : vertexVector y ∈ parameterDirectionSpan a b
      · exact hunowned y (Finset.mem_filter.mpr ⟨hyP, hyD⟩) hyj
      · exact hyi (Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hyP, hyj⟩, hyD⟩)
    exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
      ⟨j, Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hyP, hyj⟩, hxy⟩⟩)

theorem unowned_neighbor_count_le
    (P : ConvexPolytope d) (f : E d → E d) (hf : IsParallelMap P f)
    (a : I → ℝ) (b : I → E d)
    (hinj : Function.Injective (parameterVector a b))
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    {i : I} (hunowned : ∀ z ∈ centralVertices P a b, f z ≠ a i • z + b i)
    {x : E d} (hx : x ∈ noncentralClass P f a b i) :
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
    (unowned_neighbors_covered_by_other_classes P f a b hcover hunowned hx)).trans
    (Finset.card_union_le _ _)
  have hJ : J.card = Fintype.card I - 1 := by simp [J]
  rw [Finset.card_erase_of_mem hx] at hc
  change (actualNeighbors P x).card ≤ (noncentralClass P f a b i).card - 1 +
    (J.biUnion (classNeighbors P f a b x)).card at hc
  omega

theorem unowned_minimumClass_simple
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (a : I → ℝ) (b : I → E d)
    (hind : AffineIndependent ℝ (parameterVector a b))
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    {i : I} (hunowned : ∀ z ∈ centralVertices P a b, f z ≠ a i • z + b i)
    (hmin : (noncentralClass P f a b i).card =
      d + 1 - finrank ℝ (parameterDirectionSpan a b))
    (hsize : 2 ≤ (noncentralClass P f a b i).card)
    {x : E d} (hx : x ∈ noncentralClass P f a b i) :
    IsSimpleVertex P ⟨x, (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1⟩ := by
  letI : Nonempty I := ⟨i⟩
  have htm : finrank ℝ (parameterDirectionSpan a b) + 1 = Fintype.card I := by
    rw [parameterDirectionSpan_eq_vectorSpan]
    exact hind.finrank_vectorSpan_add_one
  have hupper := unowned_neighbor_count_le P f hf a b hind.injective hcover hunowned hx
  have hxP := (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
  have hlower := dim_le_actualNeighbors_card P hxP
  rw [hP] at hlower
  rw [hmin] at hupper hsize
  have heq : (actualNeighbors P x).card = d := by omega
  change (polytopeGraph P).degree ⟨x, hxP⟩ = P.dim
  rw [← actualNeighbors_card_eq_degree P hxP, hP]
  exact heq

/-- Every other class contributes its actual unique neighbor. The
neighbor is necessarily noncentral because the source class is unowned. -/
theorem unowned_minimumClass_other_neighbor
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (a : I → ℝ) (b : I → E d)
    (hind : AffineIndependent ℝ (parameterVector a b))
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    {i : I} (hunowned : ∀ z ∈ centralVertices P a b, f z ≠ a i • z + b i)
    (hmin : (noncentralClass P f a b i).card =
      d + 1 - finrank ℝ (parameterDirectionSpan a b))
    (hsize : 2 ≤ (noncentralClass P f a b i).card)
    {x : E d} (hx : x ∈ noncentralClass P f a b i) (j : I) (hji : j ≠ i) :
    ∃! y : E d, y ∈ noncentralClass P f a b j ∧ GeneralVertexStep P x y := by
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
      (noncentral_not_other_parameter P f a b hind.injective hx (Finset.mem_erase.mp hk).1)
  have hsimple := unowned_minimumClass_simple P hP f hf a b hind
    hcover hunowned hmin hsize hx
  have hactual : (actualNeighbors P x).card = d := by
    rw [actualNeighbors_card_eq_degree P hxP]
    exact hsimple.trans hP
  have htotal : (actualNeighbors P x).card ≤
      (noncentralClass P f a b i).card - 1 + ∑ k ∈ J, (N k).card := by
    have hc := (Finset.card_le_card
      (unowned_neighbors_covered_by_other_classes P f a b hcover hunowned hx)).trans
      (Finset.card_union_le _ _)
    rw [Finset.card_erase_of_mem hx] at hc
    exact hc.trans (Nat.add_le_add_left Finset.card_biUnion_le _)
  have hj : j ∈ J := Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩
  have hnonempty : (N j).Nonempty := by
    by_contra hn
    have hz : (N j).card = 0 :=
      Finset.card_eq_zero.mpr (Finset.not_nonempty_iff_eq_empty.mp hn)
    have hstrict := Finset.sum_lt_sum hNj ⟨j, hj, (by omega : (N j).card < 1)⟩
    have hsum : (∑ k ∈ J, (N k).card) < J.card := calc
      (∑ k ∈ J, (N k).card) < ∑ k ∈ J, (1 : ℕ) :=
        Finset.sum_lt_sum hNj ⟨j, hj, (by omega : (N j).card < 1)⟩
      _ = J.card := by simp
    rw [hactual, hmin] at htotal
    rw [hmin] at hsize
    omega
  obtain ⟨y, hy⟩ := hnonempty
  obtain ⟨hyj, hxy⟩ := Finset.mem_filter.mp hy
  have hyD : vertexVector y ∉ parameterDirectionSpan a b := by
    intro hyD
    have hyi := central_edge_owner P f hf a b hcover hxy.1 hyD
      (Finset.mem_filter.mp hx).2 (generalVertexStep_symm hxP hxy)
      (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).2
    exact hunowned y (Finset.mem_filter.mpr ⟨hxy.1, hyD⟩) hyi
  refine ⟨y, ⟨Finset.mem_filter.mpr ⟨hyj, hyD⟩, hxy⟩, ?_⟩
  intro z hz
  exact Finset.card_le_one.mp (hNj j hj) z
    (Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hz.1).1, hz.2⟩) y hy

theorem exists_unowned_class_crossing_matching
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (a : I → ℝ) (b : I → E d)
    (hind : AffineIndependent ℝ (parameterVector a b))
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    {i j : I} (hunowned : ∀ z ∈ centralVertices P a b, f z ≠ a i • z + b i)
    (hji : j ≠ i)
    (hmin : (noncentralClass P f a b i).card =
      d + 1 - finrank ℝ (parameterDirectionSpan a b))
    (hsize : 2 ≤ (noncentralClass P f a b i).card) :
    ∃ M : noncentralClass P f a b i → noncentralClass P f a b j,
      Function.Injective M ∧ ∀ u, GeneralVertexStep P u.val (M u).val := by
  classical
  have hex (u : noncentralClass P f a b i) :
      ∃ y : noncentralClass P f a b j, GeneralVertexStep P u.val y.val := by
    obtain ⟨y, hy, _⟩ := unowned_minimumClass_other_neighbor
      P hP f hf a b hind hcover hunowned hmin hsize u.property j hji
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
end BundlePart8

