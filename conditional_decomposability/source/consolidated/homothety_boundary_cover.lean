module
public import consolidated.homothety_unowned_facet
public import consolidated.small_order_rigidity
public import consolidated.three_dimensional_incidences
public import Mathlib.Tactic.Choose

set_option Elab.async false

section BundlePart0
/- Source: Papers/HomothetyCentralBasics.lean -/




@[expose] public section
noncomputable section
namespace Papers.Polytopes.HomothetyParameters
open Set Module
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope
variable {d : ℕ} {I : Type*}

theorem noncentral_ne_central (P : ConvexPolytope d) (f : E d → E d)
    (a : I → ℝ) (b : I → E d) {i : I} {x y : E d}
    (hx : x ∈ noncentralClass P f a b i) (hy : y ∈ centralVertices P a b) : x ≠ y := by
  intro hxy
  exact (Finset.mem_filter.mp hx).2 (hxy ▸ (Finset.mem_filter.mp hy).2)

theorem central_neighbors_eq_filter (P : ConvexPolytope d)
    (a : I → ℝ) (b : I → E d) (x : E d) :
    faceNeighbors P (centralSection P a b) x =
      (centralVertices P a b).filter (GeneralVertexStep P x) := by
  ext y
  constructor
  · intro hy
    obtain ⟨hyP, hyF, hxy⟩ := Finset.mem_filter.mp hy
    exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hyP, hyF.2⟩, hxy⟩
  · intro hy
    obtain ⟨hyC, hxy⟩ := Finset.mem_filter.mp hy
    obtain ⟨hyP, hyD⟩ := Finset.mem_filter.mp hyC
    exact Finset.mem_filter.mpr ⟨hyP, ⟨subset_convexHull ℝ _ hyP, hyD⟩, hxy⟩

theorem faceDim_ge_two_of_three_vertices
    (P : ConvexPolytope d) {F : Set (E d)} {u v w : E d}
    (hu : u ∈ P.vertices) (hv : v ∈ P.vertices) (hw : w ∈ P.vertices)
    (huF : u ∈ F) (hvF : v ∈ F) (hwF : w ∈ F)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) : 2 ≤ faceDim F := by
  by_contra hdim
  have hle : faceDim F ≤ 1 := by omega
  have hcol : Collinear ℝ F := collinear_iff_finrank_le_one.mpr hle
  apply vertices_not_collinear P hu hv hw huv huw hvw
  apply Collinear.subset (s₂ := F) ?_ hcol
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl <;> assumption

end Papers.Polytopes.HomothetyParameters

end
end
end BundlePart0

section BundlePart1
/- Source: Papers/HomothetyBoundaryData.lean -/







@[expose] public section

/-!
# Boundary-cover data and exact parameter counts

The original cover pieces have at most four vertices, with two triangles
sharing a point and a further two-vertex piece. Noncentral vertices have
a unique parameter, so each noncentral class is contained in its original
piece. The two-vertex piece forces parameter dimension d-1 and quotient
dimension two when the essential cover has d colors.
-/

noncomputable section
namespace Papers.Polytopes.HomothetyParameters

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {I : Type*} [Fintype I]

structure BoundaryPieces (P : ConvexPolytope d) (f : E d → E d)
    (a : I → ℝ) (b : I → E d) (c e j : I) (z : E d) where
  piece : I → Finset (E d)
  within : ∀ i, piece i ⊆ P.vertices
  cover : ∀ x ∈ P.vertices, ∃ i, x ∈ piece i
  values : ∀ i, ∀ x ∈ piece i, f x = a i • x + b i
  card_le_four : ∀ i, (piece i).card ≤ 4
  left_card : (piece c).card ≤ 3
  right_card : (piece e).card ≤ 3
  edge_card : (piece j).card ≤ 2
  left_mem : z ∈ piece c
  right_mem : z ∈ piece e
  distinct : c ≠ e ∧ c ≠ j ∧ e ≠ j

namespace BoundaryPieces

variable {P : ConvexPolytope d} {f : E d → E d} {a : I → ℝ} {b : I → E d}
    {c e j : I} {z : E d} (R : BoundaryPieces P f a b c e j z)

include R

theorem parameter_cover : ∀ x ∈ P.vertices, ∃ i, f x = a i • x + b i := by
  intro x hx
  obtain ⟨i, hi⟩ := R.cover x hx
  exact ⟨i, R.values i x hi⟩

theorem noncentral_subset_piece
    (hinj : Function.Injective (parameterVector a b)) (i : I) :
    noncentralClass P f a b i ⊆ R.piece i := by
  intro x hx
  obtain ⟨k, hk⟩ := R.cover x
    (Finset.mem_filter.mp (Finset.mem_filter.mp hx).1).1
  have hki := noncentral_vertex_private P f a b hinj hx k (R.values k x hk)
  simpa only [hki] using hk

theorem noncentral_eq_piece_filter
    (hinj : Function.Injective (parameterVector a b)) (i : I) :
    noncentralClass P f a b i =
      (R.piece i).filter (fun x => vertexVector x ∉ parameterDirectionSpan a b) := by
  ext x
  constructor
  · intro hx
    exact Finset.mem_filter.mpr
      ⟨R.noncentral_subset_piece hinj i hx, (Finset.mem_filter.mp hx).2⟩
  · intro hx
    obtain ⟨hxS, hxD⟩ := Finset.mem_filter.mp hx
    exact Finset.mem_filter.mpr
      ⟨Finset.mem_filter.mpr ⟨R.within i hxS, R.values i x hxS⟩, hxD⟩

theorem special_central (hinj : Function.Injective (parameterVector a b)) :
    z ∈ centralVertices P a b := by
  apply Finset.mem_filter.mpr
  refine ⟨R.within c R.left_mem, ?_⟩
  exact central_of_two_distinct_parameters f a b
    (R.values c z R.left_mem) (R.values e z R.right_mem)
    (fun h => R.distinct.1 (hinj h).symm)

theorem noncentral_subset_erase_central
    (hinj : Function.Injective (parameterVector a b)) (i : I)
    {x : E d} (hx : x ∈ centralVertices P a b) :
    noncentralClass P f a b i ⊆ (R.piece i).erase x := by
  intro y hy
  exact Finset.mem_erase.mpr
    ⟨noncentral_ne_central P f a b hy hx, R.noncentral_subset_piece hinj i hy⟩

theorem noncentral_card_le_three_of_central_piece
    (hinj : Function.Injective (parameterVector a b)) (i : I)
    {x : E d} (hx : x ∈ centralVertices P a b) (hxi : x ∈ R.piece i) :
    (noncentralClass P f a b i).card ≤ 3 := by
  have h := Finset.card_le_card (R.noncentral_subset_erase_central hinj i hx)
  rw [Finset.card_erase_of_mem hxi] at h
  have hcard := R.card_le_four i
  omega

def originalCentral (i : I) : Finset (E d) :=
  (R.piece i).filter (fun x => vertexVector x ∈ parameterDirectionSpan a b)

theorem originalCentral_subset (i : I) :
    R.originalCentral i ⊆ centralVertices P a b := by
  intro x hx
  exact Finset.mem_filter.mpr
    ⟨R.within i (Finset.mem_filter.mp hx).1, (Finset.mem_filter.mp hx).2⟩

theorem originalCentral_card_le_two
    (hinj : Function.Injective (parameterVector a b))
    (hmin : ∀ i, 2 ≤ (noncentralClass P f a b i).card) (i : I) :
    (R.originalCentral i).card ≤ 2 := by
  have hp := Finset.card_filter_add_card_filter_not
    (s := R.piece i) (fun x => vertexVector x ∈ parameterDirectionSpan a b)
  rw [← R.noncentral_eq_piece_filter hinj i] at hp
  have hi := hmin i
  have hs := R.card_le_four i
  change (R.originalCentral i).card + (noncentralClass P f a b i).card =
    (R.piece i).card at hp
  omega

theorem parameters_data (hP : P.IsFullDim) (hf : IsParallelMap P f)
    (hprivate : ∀ i, ∃ x ∈ fullClass P f a b i,
      ∀ k, f x = a k • x + b k → k = i)
    (hcolors : Fintype.card I = d) (hd : 4 ≤ d)
    (hN : P.vertices.card ≤ 4 * d - 5) :
    finrank ℝ (parameterDirectionSpan a b) + 1 = d ∧
      d + 1 - finrank ℝ (parameterDirectionSpan a b) = 2 ∧
      AffineIndependent ℝ (parameterVector a b) ∧
      (∀ i, 2 ≤ (noncentralClass P f a b i).card) ∧
      (noncentralClass P f a b c).card = 2 ∧
      (noncentralClass P f a b e).card = 2 ∧
      (noncentralClass P f a b j).card = 2 ∧
      (∑ i, ((noncentralClass P f a b i).card - 2)) +
        (centralVertices P a b).card ≤ 2 * d - 5 := by
  classical
  letI : Nonempty I := ⟨j⟩
  let t := finrank ℝ (parameterDirectionSpan a b)
  have hinj := parameterVector_injective_of_private P f a b hprivate
  have htupper := parameter_finrank_add_one_le a b
  rw [hcolors] at htupper
  have hbound (i : I) :
      d + 1 - t ≤ (noncentralClass P f a b i).card := by
    obtain ⟨x, hx, hpriv⟩ := hprivate i
    exact class_bound P hP f hf a b R.parameter_cover i hx hpriv
  have hjupper : (noncentralClass P f a b j).card ≤ 2 :=
    (Finset.card_le_card (R.noncentral_subset_piece hinj j)).trans R.edge_card
  have ht : t + 1 = d := by
    have hjlower := hbound j
    change t + 1 ≤ d at htupper
    omega
  have hr : d + 1 - t = 2 := by omega
  have hmin (i : I) : 2 ≤ (noncentralClass P f a b i).card := by
    simpa only [hr] using hbound i
  have htm : Fintype.card I = t + 1 := hcolors.trans ht.symm
  have hind : AffineIndependent ℝ (parameterVector a b) := by
    apply (affineIndependent_iff_finrank_vectorSpan_eq ℝ
      (parameterVector a b) htm).mpr
    rw [← parameterDirectionSpan_eq_vectorSpan]
  have hz := R.special_central hinj
  have hcupper : (noncentralClass P f a b c).card ≤ 2 := by
    have h := Finset.card_le_card (R.noncentral_subset_erase_central hinj c hz)
    rw [Finset.card_erase_of_mem R.left_mem] at h
    have hcard := R.left_card
    omega
  have heupper : (noncentralClass P f a b e).card ≤ 2 := by
    have h := Finset.card_le_card (R.noncentral_subset_erase_central hinj e hz)
    rw [Finset.card_erase_of_mem R.right_mem] at h
    have hcard := R.right_card
    omega
  have hc : (noncentralClass P f a b c).card = 2 := le_antisymm hcupper (hmin c)
  have he : (noncentralClass P f a b e).card = 2 := le_antisymm heupper (hmin e)
  have hj : (noncentralClass P f a b j).card = 2 := le_antisymm hjupper (hmin j)
  have hcount := essential_cover_vertex_count P hP f hf a b R.parameter_cover hprivate
  change P.vertices.card = Fintype.card I * (d + 1 - t) +
    (∑ i, ((noncentralClass P f a b i).card - (d + 1 - t))) +
      (centralVertices P a b).card at hcount
  rw [hcolors, hr] at hcount
  refine ⟨ht, hr, hind, hmin, hc, he, hj, ?_⟩
  omega

def bigColors (R : BoundaryPieces P f a b c e j z) : Finset I := Finset.univ \ {c, e, j}

theorem bigColors_card : R.bigColors.card = Fintype.card I - 3 := by
  classical
  rw [bigColors, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ]
  simp [R.distinct.1, R.distinct.2.1, R.distinct.2.2]

theorem mem_bigColors (i : I) :
    i ∈ R.bigColors ↔ i ≠ c ∧ i ≠ e ∧ i ≠ j := by
  classical
  simp [bigColors, not_or]

theorem original_central_small_left
    (hinj : Function.Injective (parameterVector a b))
    (hc : (noncentralClass P f a b c).card = 2)
    {x : E d} (hx : x ∈ centralVertices P a b) (hxS : x ∈ R.piece c) : x = z := by
  have hz := R.special_central hinj
  have heq : noncentralClass P f a b c = (R.piece c).erase z := by
    apply Finset.eq_of_subset_of_card_le (R.noncentral_subset_erase_central hinj c hz)
    rw [Finset.card_erase_of_mem R.left_mem, hc]
    have hs := R.left_card
    omega
  by_contra hxz
  have hxU : x ∈ noncentralClass P f a b c := by
    rw [heq]
    exact Finset.mem_erase.mpr ⟨hxz, hxS⟩
  exact (Finset.mem_filter.mp hxU).2 (Finset.mem_filter.mp hx).2

theorem original_central_small_right
    (hinj : Function.Injective (parameterVector a b))
    (he : (noncentralClass P f a b e).card = 2)
    {x : E d} (hx : x ∈ centralVertices P a b) (hxS : x ∈ R.piece e) : x = z := by
  have hz := R.special_central hinj
  have heq : noncentralClass P f a b e = (R.piece e).erase z := by
    apply Finset.eq_of_subset_of_card_le (R.noncentral_subset_erase_central hinj e hz)
    rw [Finset.card_erase_of_mem R.right_mem, he]
    have hs := R.right_card
    omega
  by_contra hxz
  have hxU : x ∈ noncentralClass P f a b e := by
    rw [heq]
    exact Finset.mem_erase.mpr ⟨hxz, hxS⟩
  exact (Finset.mem_filter.mp hxU).2 (Finset.mem_filter.mp hx).2

theorem original_central_not_edge_piece
    (hinj : Function.Injective (parameterVector a b))
    (hj : (noncentralClass P f a b j).card = 2)
    {x : E d} (hx : x ∈ centralVertices P a b) : x ∉ R.piece j := by
  have heq : noncentralClass P f a b j = R.piece j :=
    Finset.eq_of_subset_of_card_le (R.noncentral_subset_piece hinj j) (by
      rw [hj]
      exact R.edge_card)
  intro hxS
  have hxU : x ∈ noncentralClass P f a b j := heq.symm ▸ hxS
  exact (Finset.mem_filter.mp hxU).2 (Finset.mem_filter.mp hx).2

theorem central_erase_subset_big_union
    (hinj : Function.Injective (parameterVector a b))
    (hc : (noncentralClass P f a b c).card = 2)
    (he : (noncentralClass P f a b e).card = 2)
    (hj : (noncentralClass P f a b j).card = 2) :
    (centralVertices P a b).erase z ⊆
      R.bigColors.biUnion R.originalCentral := by
  intro x hx
  obtain ⟨hxz, hxC⟩ := Finset.mem_erase.mp hx
  obtain ⟨i, hxi⟩ := R.cover x (Finset.mem_filter.mp hxC).1
  have hic : i ≠ c := by
    intro hi
    exact hxz (R.original_central_small_left hinj hc hxC (hi ▸ hxi))
  have hie : i ≠ e := by
    intro hi
    exact hxz (R.original_central_small_right hinj he hxC (hi ▸ hxi))
  have hij : i ≠ j := by
    intro hi
    exact R.original_central_not_edge_piece hinj hj hxC (hi ▸ hxi)
  exact Finset.mem_biUnion.mpr
    ⟨i, (R.mem_bigColors i).mpr ⟨hic, hie, hij⟩,
      Finset.mem_filter.mpr ⟨hxi, (Finset.mem_filter.mp hxC).2⟩⟩

end BoundaryPieces
end Papers.Polytopes.HomothetyParameters


end
end
end BundlePart1

section BundlePart2
/- Source: Papers/HomothetyBoundaryDeficit.lean -/





@[expose] public section

/-!
# The small central faces in the boundary covers

The central shared point forces at least t-1 central vertices. If there
are exactly t-1, the central face has two or three vertices. Its homothety
must be an existing parameter: a new parameter leaves every other central
point singly owned, and Equation (3) then contradicts the four-vertex
size bound of that point's original cover piece.
-/

noncomputable section
namespace Papers.Polytopes.HomothetyParameters

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {I : Type*} [Fintype I]

theorem central_three_homothetic
    (P : ConvexPolytope d) (f : E d → E d) (hf : IsParallelMap P f)
    (a : I → ℝ) (b : I → E d)
    (hF : P.IsFace (centralSection P a b))
    (hcard : (centralVertices P a b).card = 3) :
    HomotheticOn f (centralVertices P a b : Set (E d)) := by
  classical
  let C := centralVertices P a b
  have hCC : C.card = 3 := hcard
  obtain ⟨x, y, z, hxy, hxz, hyz, hCeq⟩ := Finset.card_eq_three.mp hCC
  have hxC : x ∈ C := by rw [hCeq]; simp
  have hyC : y ∈ C := by rw [hCeq]; simp
  have hzC : z ∈ C := by rw [hCeq]; simp
  have hsub : C ⊆ P.vertices := Finset.filter_subset _ _
  have hmem {w : E d} (hw : w ∈ C) : w ∈ centralSection P a b :=
    ⟨subset_convexHull ℝ _ (hsub hw), (Finset.mem_filter.mp hw).2⟩
  have hdim := faceDim_ge_two_of_three_vertices P (hsub hxC) (hsub hyC)
    (hsub hzC) (hmem hxC) (hmem hyC) (hmem hzC) hxy hxz hyz
  apply homotheticOn_of_vertexSubset_degree P f hf C hsub (k := 2) ?_ (by
    change (centralVertices P a b).card ≤ 2 * 2 - 1
    omega)
  intro w hw
  rw [← central_neighbors_eq_filter]
  exact hdim.trans (faceDim_le_faceNeighbors_card P hF (hsub hw) (hmem hw))

namespace BoundaryPieces

variable {P : ConvexPolytope d} {f : E d → E d} {a : I → ℝ} {b : I → E d}
    {c e j : I} {z : E d} (R : BoundaryPieces P f a b c e j z)

include R

theorem central_face (hP : P.IsFullDim) (hf : IsParallelMap P f)
    (hprivate : ∀ i, ∃ x ∈ fullClass P f a b i,
      ∀ k, f x = a k • x + b k → k = i)
    (hr : d + 1 - finrank ℝ (parameterDirectionSpan a b) = 2)
    (hj : (noncentralClass P f a b j).card = 2) :
    P.IsFace (centralSection P a b) := by
  have hinj := parameterVector_injective_of_private P f a b hprivate
  obtain ⟨B, hB, hclique, hpos, hfacets, hfibers, hinter, hF⟩ :=
    minimumClass_fiber_faces P hP f hf a b R.parameter_cover hprivate j
      (by omega) (hj.trans hr.symm)
  rcases hF with hempty | hF
  · have hz := R.special_central hinj
    have hzF : z ∈ centralSection P a b :=
      ⟨subset_convexHull ℝ _ (Finset.mem_filter.mp hz).1, (Finset.mem_filter.mp hz).2⟩
    rw [hempty] at hzF
    exact hzF.elim
  · exact hF

theorem central_inequality (hP : P.IsFullDim) (hf : IsParallelMap P f)
    (hprivate : ∀ i, ∃ x ∈ fullClass P f a b i,
      ∀ k, f x = a k • x + b k → k = i)
    (hr : d + 1 - finrank ℝ (parameterDirectionSpan a b) = 2)
    (hj : (noncentralClass P f a b j).card = 2)
    {w : E d} (hw : w ∈ centralVertices P a b) :
    2 * finrank ℝ (parameterDirectionSpan a b) ≤
      2 * (faceNeighbors P (centralSection P a b) w).card +
      2 * (owners f a b w).card +
      ∑ i ∈ owners f a b w, ((noncentralClass P f a b i).card - 2) := by
  have h := central_neighbor_inequality P hP f hf a b R.parameter_cover hprivate
    j (by omega) (hj.trans hr.symm)
    (Finset.mem_filter.mp hw).1 (Finset.mem_filter.mp hw).2
  simpa only [hr] using h

theorem special_owners
    (hind : AffineIndependent ℝ (parameterVector a b)) :
    owners f a b z = {c, e} := by
  classical
  have hc : c ∈ owners f a b z := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, R.values c z R.left_mem⟩
  have he : e ∈ owners f a b z := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, R.values e z R.right_mem⟩
  have hsub : ({c, e} : Finset I) ⊆ owners f a b z := by
    intro i hi
    simp only [Finset.mem_insert, Finset.mem_singleton] at hi
    rcases hi with rfl | rfl <;> assumption
  apply (Finset.eq_of_subset_of_card_le hsub ?_).symm
  have hcard := owners_card_le_two f a b hind z
  simpa [R.distinct.1] using hcard

theorem central_card_lower (hP : P.IsFullDim) (hf : IsParallelMap P f)
    (hprivate : ∀ i, ∃ x ∈ fullClass P f a b i,
      ∀ k, f x = a k • x + b k → k = i)
    (hind : AffineIndependent ℝ (parameterVector a b))
    (hr : d + 1 - finrank ℝ (parameterDirectionSpan a b) = 2)
    (hc : (noncentralClass P f a b c).card = 2)
    (he : (noncentralClass P f a b e).card = 2)
    (hj : (noncentralClass P f a b j).card = 2) :
    finrank ℝ (parameterDirectionSpan a b) ≤
      (centralVertices P a b).card + 1 := by
  have hz := R.special_central hind.injective
  have hineq := R.central_inequality hP hf hprivate hr hj hz
  rw [R.special_owners hind] at hineq
  simp only [hc, he, Nat.sub_self, Finset.sum_insert, Finset.sum_singleton,
    Finset.mem_singleton, R.distinct.1, not_false_eq_true, add_zero,
    Finset.card_insert_of_notMem, Finset.card_singleton] at hineq
  have hdeg := central_face_neighbor_card_lt P a b
    (Finset.mem_filter.mp hz).1 (Finset.mem_filter.mp hz).2
  omega

theorem deficit_homothetic (hP : P.IsFullDim) (hf : IsParallelMap P f)
    (hprivate : ∀ i, ∃ x ∈ fullClass P f a b i,
      ∀ k, f x = a k • x + b k → k = i)
    (hind : AffineIndependent ℝ (parameterVector a b))
    (ht : finrank ℝ (parameterDirectionSpan a b) + 1 = d)
    (hr : d + 1 - finrank ℝ (parameterDirectionSpan a b) = 2)
    (hj : (noncentralClass P f a b j).card = 2)
    (hdlo : 4 ≤ d) (hdhi : d ≤ 5)
    (hs : (centralVertices P a b).card =
      finrank ℝ (parameterDirectionSpan a b) - 1)
    (hbudget : (∑ i, ((noncentralClass P f a b i).card - 2)) +
      (centralVertices P a b).card ≤ 2 * d - 5) :
    HomotheticOn f (centralVertices P a b : Set (E d)) := by
  have hF := R.central_face hP hf hprivate hr hj
  by_cases hd5 : d = 5
  · apply central_three_homothetic P f hf a b hF
    omega
  · have hd4 : d = 4 := by omega
    apply homotheticOn_of_vertex_clique P f hf (centralVertices P a b)
      (Finset.filter_subset _ _) (by omega)
    intro x hx y hy hxy
    have hineq := R.central_inequality hP hf hprivate hr hj hx
    have howner := owners_card_le_two f a b hind x
    have hsum := Finset.sum_le_sum_of_subset
      (f := fun i => (noncentralClass P f a b i).card - 2)
      (Finset.subset_univ (owners f a b x))
    have hmax := central_face_neighbor_card_lt P a b
      (Finset.mem_filter.mp hx).1 (Finset.mem_filter.mp hx).2
    have hdegeq : (faceNeighbors P (centralSection P a b) x).card + 1 =
        (centralVertices P a b).card := by omega
    exact central_adjacent_of_full_degree P a b hx hy hxy hdegeq

theorem deficit_new_homothety_impossible
    (hP : P.IsFullDim) (hf : IsParallelMap P f)
    (hprivate : ∀ i, ∃ x ∈ fullClass P f a b i,
      ∀ k, f x = a k • x + b k → k = i)
    (hind : AffineIndependent ℝ (parameterVector a b))
    (ht : 3 ≤ finrank ℝ (parameterDirectionSpan a b))
    (hr : d + 1 - finrank ℝ (parameterDirectionSpan a b) = 2)
    (hj : (noncentralClass P f a b j).card = 2)
    (hs : (centralVertices P a b).card =
      finrank ℝ (parameterDirectionSpan a b) - 1)
    {α : ℝ} {u : E d}
    (hH : ∀ w ∈ centralVertices P a b, f w = α • w + u)
    (hnew : ∀ i, (α, u) ≠ parameterVector a b i) : False := by
  classical
  have hz := R.special_central hind.injective
  obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp
    (by omega : 1 < (centralVertices P a b).card)
  obtain ⟨w, hw, hwz⟩ : ∃ w ∈ centralVertices P a b, w ≠ z := by
    by_cases hxz : x = z
    · exact ⟨y, hy, fun hyz => hxy (hxz.trans hyz.symm)⟩
    · exact ⟨x, hx, hxz⟩
  have hown : (owners f a b w).card ≤ 1 := by
    by_contra hn
    obtain ⟨i, hi, k, hk, hik⟩ := Finset.one_lt_card.mp (by omega :
      1 < (owners f a b w).card)
    have heq := at_most_one_shared_point_of_new_homothety f a b hind hnew
      (hH w hw) (hH z hz)
      ⟨i, (Finset.mem_filter.mp hi).2, k, (Finset.mem_filter.mp hk).2, hik⟩
      ⟨c, R.values c z R.left_mem, e, R.values e z R.right_mem, R.distinct.1⟩
    exact hwz heq
  obtain ⟨i, hwi⟩ := R.cover w (Finset.mem_filter.mp hw).1
  have hi : i ∈ owners f a b w := Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, R.values i w hwi⟩
  have hsub : owners f a b w ⊆ {i} := by
    intro k hk
    exact Finset.mem_singleton.mpr (Finset.card_le_one.mp hown k hk i hi)
  have hsum := Finset.sum_le_sum_of_subset
    (f := fun k => (noncentralClass P f a b k).card - 2) hsub
  rw [Finset.sum_singleton] at hsum
  have hclass := R.noncentral_card_le_three_of_central_piece hind.injective i hw hwi
  have hdeg := central_face_neighbor_card_lt P a b
    (Finset.mem_filter.mp hw).1 (Finset.mem_filter.mp hw).2
  have hineq := R.central_inequality hP hf hprivate hr hj hw
  omega

theorem deficit_shephard
    (hP : P.IsFullDim) (hf : IsParallelMap P f)
    (hprivate : ∀ i, ∃ x ∈ fullClass P f a b i,
      ∀ k, f x = a k • x + b k → k = i)
    (hind : AffineIndependent ℝ (parameterVector a b))
    (ht : finrank ℝ (parameterDirectionSpan a b) + 1 = d)
    (hr : d + 1 - finrank ℝ (parameterDirectionSpan a b) = 2)
    (hj : (noncentralClass P f a b j).card = 2)
    (hdlo : 4 ≤ d) (hdhi : d ≤ 5)
    (hs : (centralVertices P a b).card =
      finrank ℝ (parameterDirectionSpan a b) - 1)
    (hbudget : (∑ i, ((noncentralClass P f a b i).card - 2)) +
      (centralVertices P a b).card ≤ 2 * d - 5) : HasShephardProperty P := by
  classical
  obtain ⟨α, u, hH⟩ := R.deficit_homothetic hP hf hprivate hind
    ht hr hj hdlo hdhi hs hbudget
  have hold : ∃ i, (α, u) = parameterVector a b i := by
    by_contra hn
    have hnew : ∀ i, (α, u) ≠ parameterVector a b i :=
      fun i hi => hn ⟨i, hi⟩
    exact R.deficit_new_homothety_impossible hP hf hprivate hind
      (by omega) hr hj hs hH hnew
  obtain ⟨i, hi⟩ := hold
  have hα : α = a i := congrArg Prod.fst hi
  have hu : u = b i := congrArg Prod.snd hi
  apply common_central_class_shephard P hP f hf a b hind R.parameter_cover
    hprivate i (by
      intro w hw
      simpa only [hα, hu] using hH w hw) (by omega)
  have hsum := Finset.sum_le_sum_of_subset
    (f := fun k => (noncentralClass P f a b k).card - 2)
    (Finset.subset_univ ((Finset.univ : Finset I).erase i))
  rw [hr]
  omega

end BoundaryPieces
end Papers.Polytopes.HomothetyParameters


end
end
end BundlePart2

section BundlePart3
/- Source: Papers/HomothetyBoundaryLarge.lean -/






@[expose] public section

/-!
# The planar central face in the five-dimensional boundary cover

A large central face cannot be homothetic, because two of its vertices
would belong to the same original four-set and force a third owner at the
distinguished shared point. A nonhomothetic face on at most five vertices
has dimension at most two. All four non-edge colors then own central
points, so the owning-color dimension bound makes the edge color unowned.
Equation (3) forces every central vertex to be shared.
-/

noncomputable section
namespace Papers.Polytopes.HomothetyParameters

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {I : Type*} [Fintype I]

theorem faceNeighbors_card_le_two_of_dim_le_two
    (P : ConvexPolytope d) (F : Set (E d)) (hdim : faceDim F ≤ 2)
    {w : E d} (hw : w ∈ P.vertices) (hwF : w ∈ F) :
    (faceNeighbors P F w).card ≤ 2 := by
  classical
  let N := faceNeighbors P F w
  by_contra hn
  change ¬N.card ≤ 2 at hn
  obtain ⟨x, hx⟩ := Finset.card_pos.mp (by omega : 0 < N.card)
  have hcarderase : 1 < (N.erase x).card := by
    rw [Finset.card_erase_of_mem hx]
    omega
  obtain ⟨y, hy, z, hz, hyz⟩ := Finset.one_lt_card.mp hcarderase
  have hyN := Finset.mem_of_mem_erase hy
  have hzN := Finset.mem_of_mem_erase hz
  have hxy : x ≠ y := (Finset.ne_of_mem_erase hy).symm
  have hxz : x ≠ z := (Finset.ne_of_mem_erase hz).symm
  obtain ⟨hxP, hxF, hwx⟩ := Finset.mem_filter.mp hx
  obtain ⟨hyP, hyF, hwy⟩ := Finset.mem_filter.mp hyN
  obtain ⟨hzP, hzF, hwz⟩ := Finset.mem_filter.mp hzN
  have hsub : ({w, x, y, z} : Set (E d)) ⊆ F := by
    intro v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hv
    rcases hv with rfl | rfl | rfl | rfl <;> assumption
  have hplane : finrank ℝ (vectorSpan ℝ ({w, x, y, z} : Set (E d))) ≤ 2 :=
    (Submodule.finrank_mono (vectorSpan_mono ℝ hsub)).trans hdim
  exact no_three_actual_edges_in_plane P hw hxP hyP hzP hxy hxz hyz hwx hwy hwz hplane

theorem central_nonhomothetic_dim_le_two_of_card_le_five
    (P : ConvexPolytope d) (f : E d → E d) (hf : IsParallelMap P f)
    (a : I → ℝ) (b : I → E d)
    (hF : P.IsFace (centralSection P a b))
    (hcard : (centralVertices P a b).card ≤ 5)
    (hnot : ¬HomotheticOn f (centralVertices P a b : Set (E d))) :
    faceDim (centralSection P a b) ≤ 2 := by
  by_contra hn
  apply hnot
  apply homotheticOn_of_vertexSubset_degree P f hf (centralVertices P a b)
    (Finset.filter_subset _ _) (k := 3) ?_ (by omega)
  intro w hw
  rw [← central_neighbors_eq_filter]
  have hle := faceDim_le_faceNeighbors_card P hF (Finset.mem_filter.mp hw).1
    ⟨subset_convexHull ℝ _ (Finset.mem_filter.mp hw).1, (Finset.mem_filter.mp hw).2⟩
  omega

namespace BoundaryPieces

variable {P : ConvexPolytope d} {f : E d → E d} {a : I → ℝ} {b : I → E d}
    {c e j : I} {z : E d} (R : BoundaryPieces P f a b c e j z)

include R

theorem large_central_nonhomothetic
    (hind : AffineIndependent ℝ (parameterVector a b))
    (hcolors : Fintype.card I = d) (hd : 4 ≤ d)
    (hc : (noncentralClass P f a b c).card = 2)
    (he : (noncentralClass P f a b e).card = 2)
    (hj : (noncentralClass P f a b j).card = 2)
    (hlarge : d - 1 ≤ (centralVertices P a b).card) :
    ¬HomotheticOn f (centralVertices P a b : Set (E d)) := by
  classical
  rintro ⟨α, u, hH⟩
  have hz := R.special_central hind.injective
  have hsingle (i : I) (hi : i ∈ R.bigColors) : (R.originalCentral i).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x hx y hy
    by_contra hxy
    have hxC := R.originalCentral_subset i hx
    have hyC := R.originalCentral_subset i hy
    have hparam : (α, u) = parameterVector a b i :=
      homothety_parameters_eq_of_two_points hxy
        ((hH x hxC).symm.trans (R.values i x (Finset.mem_filter.mp hx).1))
        ((hH y hyC).symm.trans (R.values i y (Finset.mem_filter.mp hy).1))
    have hα : α = a i := congrArg Prod.fst hparam
    have hu : u = b i := congrArg Prod.snd hparam
    have hzi : f z = a i • z + b i := by simpa only [hα, hu] using hH z hz
    have hiC := (R.mem_bigColors i).mp hi
    exact (third_owner_eq f a b hind R.distinct.1
      (R.values c z R.left_mem) (R.values e z R.right_mem) hzi).elim hiC.1 hiC.2.1
  have hsub := R.central_erase_subset_big_union hind.injective hc he hj
  have hcard := Finset.card_le_card hsub
  have hbi : (R.bigColors.biUnion R.originalCentral).card ≤
      ∑ i ∈ R.bigColors, (R.originalCentral i).card := Finset.card_biUnion_le
  have hsum : (∑ i ∈ R.bigColors, (R.originalCentral i).card) ≤ R.bigColors.card := calc
    _ ≤ ∑ i ∈ R.bigColors, (1 : ℕ) := Finset.sum_le_sum hsingle
    _ = R.bigColors.card := by simp
  rw [Finset.card_erase_of_mem hz] at hcard
  have hbig := R.bigColors_card
  rw [hcolors] at hbig
  omega

theorem big_color_owned_of_four_central
    (hind : AffineIndependent ℝ (parameterVector a b))
    (hcolors : Fintype.card I = 5)
    (hmin : ∀ i, 2 ≤ (noncentralClass P f a b i).card)
    (hc : (noncentralClass P f a b c).card = 2)
    (he : (noncentralClass P f a b e).card = 2)
    (hj : (noncentralClass P f a b j).card = 2)
    (hlarge : 4 ≤ (centralVertices P a b).card)
    (i : I) (hi : i ∈ R.bigColors) :
    ∃ w ∈ centralVertices P a b, f w = a i • w + b i := by
  classical
  by_contra hn
  have hzero : (R.originalCentral i).card = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    exact hn ⟨w, R.originalCentral_subset i hw, R.values i w (Finset.mem_filter.mp hw).1⟩
  have hbig : R.bigColors.card = 2 := by rw [R.bigColors_card, hcolors]
  have hsum := Finset.sum_erase_add R.bigColors (fun k => (R.originalCentral k).card) hi
  rw [hzero, add_zero] at hsum
  have hbound := Finset.sum_le_sum (s := R.bigColors.erase i)
    (fun k _ => R.originalCentral_card_le_two hind.injective hmin k)
  simp only [Finset.sum_const, nsmul_eq_mul] at hbound
  rw [Finset.card_erase_of_mem hi, hbig] at hbound
  have hsub := R.central_erase_subset_big_union hind.injective hc he hj
  have hcard := Finset.card_le_card hsub
  have hbi : (R.bigColors.biUnion R.originalCentral).card ≤
      ∑ k ∈ R.bigColors, (R.originalCentral k).card := Finset.card_biUnion_le
  have hz := R.special_central hind.injective
  rw [Finset.card_erase_of_mem hz] at hcard
  omega

theorem edge_color_unowned_of_large_planar
    (hf : IsParallelMap P f)
    (hind : AffineIndependent ℝ (parameterVector a b))
    (hcolors : Fintype.card I = 5)
    (hmin : ∀ i, 2 ≤ (noncentralClass P f a b i).card)
    (hc : (noncentralClass P f a b c).card = 2)
    (he : (noncentralClass P f a b e).card = 2)
    (hj : (noncentralClass P f a b j).card = 2)
    (hlarge : 4 ≤ (centralVertices P a b).card)
    (hF : P.IsFace (centralSection P a b))
    (hdim : faceDim (centralSection P a b) ≤ 2) :
    ∀ w ∈ centralVertices P a b, f w ≠ a j • w + b j := by
  classical
  have hz := R.special_central hind.injective
  have howners := centralOwners_card_le_faceDim_add_two P f hf a b hind
    R.parameter_cover hF ⟨z, hz⟩
  have hother (i : I) (hij : i ≠ j) : i ∈ centralOwners P f a b := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _, ?_⟩
    by_cases hic : i = c
    · subst i
      exact ⟨z, hz, R.values c z R.left_mem⟩
    by_cases hie : i = e
    · subst i
      exact ⟨z, hz, R.values e z R.right_mem⟩
    exact R.big_color_owned_of_four_central hind hcolors hmin hc he hj hlarge i
      ((R.mem_bigColors i).mpr ⟨hic, hie, hij⟩)
  intro w hw hwj
  have hjowner : j ∈ centralOwners P f a b :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, w, hw, hwj⟩
  have hall : centralOwners P f a b = Finset.univ := by
    apply Finset.eq_univ_iff_forall.mpr
    intro i
    by_cases hij : i = j
    · simpa only [hij] using hjowner
    · exact hother i hij
  rw [hall, Finset.card_univ, hcolors] at howners
  omega

theorem large_planar_all_shared
    (hP : P.IsFullDim) (hf : IsParallelMap P f)
    (hprivate : ∀ i, ∃ x ∈ fullClass P f a b i,
      ∀ k, f x = a k • x + b k → k = i)
    (ht : finrank ℝ (parameterDirectionSpan a b) = 4)
    (hr : d + 1 - finrank ℝ (parameterDirectionSpan a b) = 2)
    (hj : (noncentralClass P f a b j).card = 2)
    (hE : (∑ i, ((noncentralClass P f a b i).card - 2)) ≤ 1)
    (hdim : faceDim (centralSection P a b) ≤ 2) :
    ∀ w ∈ centralVertices P a b, 2 ≤ (owners f a b w).card := by
  intro w hw
  by_contra hn
  have hdeg := faceNeighbors_card_le_two_of_dim_le_two P (centralSection P a b)
    hdim (Finset.mem_filter.mp hw).1
    ⟨subset_convexHull ℝ _ (Finset.mem_filter.mp hw).1, (Finset.mem_filter.mp hw).2⟩
  have hsum := Finset.sum_le_sum_of_subset
    (f := fun i => (noncentralClass P f a b i).card - 2)
    (Finset.subset_univ (owners f a b w))
  have hineq := R.central_inequality hP hf hprivate hr hj hw
  rw [ht] at hineq
  omega

end BoundaryPieces
end Papers.Polytopes.HomothetyParameters


end
end
end BundlePart3

section BundlePart4
/- Source: Papers/HomothetyBoundaryCover.lean -/






@[expose] public section

/-!
# The complete essential boundary-cover argument

For dimensions four and five, the full essential boundary cover has one
homothety for each original rigid piece. All numerical, central-face,
ownership, and facet conclusions are derived from those actual pieces.
The unique possible excess color is omitted from the Shephard facet.
-/

noncomputable section
namespace Papers.Polytopes.HomothetyParameters

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {I : Type*} [Fintype I]

theorem exists_color_containing_all_excess
    (e : I → ℕ) (hE : (∑ i, e i) ≤ 1)
    (j c : I) (hcj : c ≠ j) (hej : e j = 0) :
    ∃ h, j ≠ h ∧ ∀ k, k ≠ h → e k = 0 := by
  classical
  by_cases hex : ∃ h, e h ≠ 0
  · obtain ⟨h, hh⟩ := hex
    have hjh : j ≠ h := by intro he; exact hh (he ▸ hej)
    refine ⟨h, hjh, ?_⟩
    intro k hkh
    have hsub : ({h, k} : Finset I) ⊆ Finset.univ := Finset.subset_univ _
    have hsum := Finset.sum_le_sum_of_subset (f := e) hsub
    simp only [Finset.sum_insert, Finset.mem_singleton, hkh.symm,
      not_false_eq_true, Finset.sum_singleton] at hsum
    omega
  · refine ⟨c, hcj.symm, ?_⟩
    intro k hk
    by_contra he
    exact hex ⟨k, he⟩

namespace BoundaryPieces

variable {P : ConvexPolytope d} {f : E d → E d} {a : I → ℝ} {b : I → E d}
    {c e j : I} {z : E d} (R : BoundaryPieces P f a b c e j z)

include R

/-- The full essential-parameter case of Lemma 13, with no assumed
central graph, owner-cycle classification, or supporting facet. -/
theorem essential_cover_shephard (hP : P.IsFullDim) (hf : IsParallelMap P f)
    (hprivate : ∀ i, ∃ x ∈ fullClass P f a b i,
      ∀ k, f x = a k • x + b k → k = i)
    (hcolors : Fintype.card I = d) (hdlo : 4 ≤ d) (hdhi : d ≤ 5)
    (hN : P.vertices.card ≤ 4 * d - 5) : HasShephardProperty P := by
  classical
  obtain ⟨ht, hr, hind, hmin, hc, he, hj, hbudget⟩ :=
    R.parameters_data hP hf hprivate hcolors hdlo hN
  have hF := R.central_face hP hf hprivate hr hj
  have hlow := R.central_card_lower hP hf hprivate hind hr hc he hj
  by_cases hs : (centralVertices P a b).card =
      finrank ℝ (parameterDirectionSpan a b) - 1
  · exact R.deficit_shephard hP hf hprivate hind ht hr hj hdlo hdhi hs hbudget
  · have hlarge : d - 1 ≤ (centralVertices P a b).card := by omega
    have hnot := R.large_central_nonhomothetic hind hcolors hdlo hc he hj hlarge
    have hsmall : (centralVertices P a b).card ≤ 5 := by omega
    by_cases hd4 : d = 4
    · have hcard : (centralVertices P a b).card = 3 := by omega
      exact (hnot (central_three_homothetic P f hf a b hF hcard)).elim
    · have hd5 : d = 5 := by omega
      have hcolors5 : Fintype.card I = 5 := hcolors.trans hd5
      have ht4 : finrank ℝ (parameterDirectionSpan a b) = 4 := by omega
      have hlarge4 : 4 ≤ (centralVertices P a b).card := by omega
      have hdim := central_nonhomothetic_dim_le_two_of_card_le_five
        P f hf a b hF hsmall hnot
      have hunowned := R.edge_color_unowned_of_large_planar hf hind
        hcolors5 hmin hc he hj hlarge4 hF hdim
      have hE : (∑ i, ((noncentralClass P f a b i).card - 2)) ≤ 1 := by omega
      have hshared := R.large_planar_all_shared hP hf hprivate ht4 hr hj hE hdim
      obtain ⟨h, hjh, hzero⟩ := exists_color_containing_all_excess
        (fun i => (noncentralClass P f a b i).card - 2) hE
        j c R.distinct.2.1 (by rw [hj, Nat.sub_self])
      apply unowned_minimum_shared_central_shephard P hP f hf a b hind
        R.parameter_cover hjh hunowned (hj.trans hr.symm) (by omega) ?_ hshared
      intro k hkh
      have hk := hzero k hkh
      have hkmin := hmin k
      rw [hr]
      omega

end BoundaryPieces

/-- Ordinary geometric rigid pieces of the boundary configuration. -/
structure RigidBoundaryPieces (P : ConvexPolytope d) (c e j : I) (z : E d) where
  piece : I → Finset (E d)
  within : ∀ i, piece i ⊆ P.vertices
  cover : ∀ x ∈ P.vertices, ∃ i, x ∈ piece i
  rigid : ∀ i, ParallelRigid P (piece i : Set (E d))
  card_le_four : ∀ i, (piece i).card ≤ 4
  left_card : (piece c).card ≤ 3
  right_card : (piece e).card ≤ 3
  edge_card : (piece j).card ≤ 2
  left_mem : z ∈ piece c
  right_mem : z ∈ piece e
  distinct : c ≠ e ∧ c ≠ j ∧ e ≠ j

theorem RigidBoundaryPieces.parameters
    {P : ConvexPolytope d} {c e j : I} {z : E d}
    (R : RigidBoundaryPieces P c e j z)
    (f : E d → E d) (hf : IsParallelMap P f) :
    ∃ (a : I → ℝ) (b : I → E d), Nonempty (BoundaryPieces P f a b c e j z) := by
  classical
  have hex (i : I) : ∃ α : ℝ, ∃ u : E d,
      ∀ x ∈ R.piece i, f x = α • x + u :=
    R.rigid i f (((parallelOn_vertices_iff P f).mpr hf).mono (R.within i))
  choose a b hab using hex
  exact ⟨a, b, ⟨{
    piece := R.piece
    within := R.within
    cover := R.cover
    values := hab
    card_le_four := R.card_le_four
    left_card := R.left_card
    right_card := R.right_card
    edge_card := R.edge_card
    left_mem := R.left_mem
    right_mem := R.right_mem
    distinct := R.distinct }⟩⟩

end Papers.Polytopes.HomothetyParameters


end
end
end BundlePart4

