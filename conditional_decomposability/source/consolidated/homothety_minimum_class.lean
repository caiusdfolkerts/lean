module
public import consolidated.actual_rigid_seeds
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty

set_option Elab.async false

section BundlePart0
/- Source: Papers/HomothetyParameters.lean -/






@[expose] public section

/-!
# The class bound for a cover by homotheties

The parameter space and homogeneous vertex vectors are exactly those of
Section 4 of the conditional-decomposability paper: `pᵢ = (αᵢ,bᵢ)` and
`Xᵥ = (1,-v)`.  The direction space is the span of all parameter differences.
The classes are the full equality classes of an actual parallel map on the
vertices.  An essential class is supplied with one private vertex, as in the
paper after redundant classes have been removed.

The proof of the class bound uses the actual edge-star spanning theorem.
No bound on the number of homotheties, generic-position condition, or
assumed quotient-spanning property enters the statement.

Development status: this new module awaits its first compiler check.
-/

noncomputable section
namespace Papers.Polytopes.HomothetyParameters

open Set Module
open scoped Classical BigOperators
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {I : Type*}

def vertexVector (x : E d) : ℝ × E d := (1, -x)

def parameterVector (a : I → ℝ) (b : I → E d) (i : I) : ℝ × E d :=
  (a i, b i)

def parameterDirectionSpan (a : I → ℝ) (b : I → E d) :
    Submodule ℝ (ℝ × E d) :=
  Submodule.span ℝ (Set.range (fun ij : I × I =>
    parameterVector a b ij.1 - parameterVector a b ij.2))

def fullClass (P : ConvexPolytope d) (f : E d → E d)
    (a : I → ℝ) (b : I → E d) (i : I) : Finset (E d) :=
  P.vertices.filter (fun x => f x = a i • x + b i)

def noncentralClass (P : ConvexPolytope d) (f : E d → E d)
    (a : I → ℝ) (b : I → E d) (i : I) : Finset (E d) :=
  (fullClass P f a b i).filter (fun x => vertexVector x ∉ parameterDirectionSpan a b)

def centralVertices (P : ConvexPolytope d) (a : I → ℝ) (b : I → E d) :
    Finset (E d) :=
  P.vertices.filter (fun x => vertexVector x ∈ parameterDirectionSpan a b)

theorem parameterDirectionSpan_eq_vectorSpan (a : I → ℝ) (b : I → E d) :
    parameterDirectionSpan a b = vectorSpan ℝ (Set.range (parameterVector a b)) := by
  unfold parameterDirectionSpan
  rw [vectorSpan_def]
  congr 1
  ext z
  constructor
  · rintro ⟨⟨i, j⟩, rfl⟩
    exact Set.mem_vsub.mpr ⟨parameterVector a b i, Set.mem_range_self i,
      parameterVector a b j, Set.mem_range_self j, rfl⟩
  · intro hz
    obtain ⟨u, ⟨i, rfl⟩, v, ⟨j, rfl⟩, rfl⟩ := Set.mem_vsub.mp hz
    exact Set.mem_range_self (i, j)

/-- The natural-number codimension is the dimension of the actual
quotient, rather than an independently assigned numerical parameter. -/
theorem quotient_finrank (a : I → ℝ) (b : I → E d) :
    finrank ℝ ((ℝ × E d) ⧸ parameterDirectionSpan a b) =
      d + 1 - finrank ℝ (parameterDirectionSpan a b) := by
  rw [Submodule.finrank_quotient]
  simp only [Module.finrank_prod, Module.finrank_self, finrank_euclideanSpace_fin]
  omega

theorem parameter_finrank_add_one_le [Fintype I] [Nonempty I]
    (a : I → ℝ) (b : I → E d) :
    finrank ℝ (parameterDirectionSpan a b) + 1 ≤ Fintype.card I := by
  rw [parameterDirectionSpan_eq_vectorSpan]
  exact finrank_vectorSpan_range_add_one_le ℝ (parameterVector a b)

/-- A common value of two homotheties locates their difference center. -/
theorem parameter_difference_at_common_point
    (f : E d → E d) (a : I → ℝ) (b : I → E d)
    {x : E d} {i j : I}
    (hxi : f x = a i • x + b i) (hxj : f x = a j • x + b j) :
    parameterVector a b j - parameterVector a b i =
      (a j - a i) • vertexVector x := by
  have hbi : b i = f x - a i • x := by rw [hxi]; abel
  have hbj : b j = f x - a j • x := by rw [hxj]; abel
  apply Prod.ext
  · simp [parameterVector, vertexVector]
  · change b j - b i = (a j - a i) • (-x)
    rw [hbi, hbj]
    module

theorem central_of_two_distinct_parameters
    (f : E d → E d) (a : I → ℝ) (b : I → E d)
    {x : E d} {i j : I}
    (hxi : f x = a i • x + b i) (hxj : f x = a j • x + b j)
    (hne : parameterVector a b j ≠ parameterVector a b i) :
    vertexVector x ∈ parameterDirectionSpan a b := by
  have he := parameter_difference_at_common_point f a b hxi hxj
  have hscalar : a j - a i ≠ 0 := by
    intro hz
    apply hne
    apply sub_eq_zero.mp
    rw [he, hz, zero_smul]
  have hd : parameterVector a b j - parameterVector a b i ∈
      parameterDirectionSpan a b :=
    Submodule.subset_span (Set.mem_range_self (j, i))
  rw [he] at hd
  have h := (parameterDirectionSpan a b).smul_mem (a j - a i)⁻¹ hd
  simpa only [smul_smul, inv_mul_cancel₀ hscalar, one_smul] using h

theorem parameterVector_injective_of_private
    (P : ConvexPolytope d) (f : E d → E d) (a : I → ℝ) (b : I → E d)
    (hprivate : ∀ i, ∃ x ∈ fullClass P f a b i,
      ∀ j, f x = a j • x + b j → j = i) :
    Function.Injective (parameterVector a b) := by
  intro i j hij
  obtain ⟨x, hxi, hpriv⟩ := hprivate i
  have ha : a i = a j := congrArg Prod.fst hij
  have hb : b i = b j := congrArg Prod.snd hij
  have hfxj : f x = a j • x + b j := by
    rw [← ha, ← hb]
    exact (Finset.mem_filter.mp hxi).2
  exact (hpriv j hfxj).symm

theorem noncentralClasses_disjoint
    (P : ConvexPolytope d) (f : E d → E d) (a : I → ℝ) (b : I → E d)
    (hinj : Function.Injective (parameterVector a b)) {i j : I} (hij : i ≠ j) :
    Disjoint (noncentralClass P f a b i) (noncentralClass P f a b j) := by
  apply Finset.disjoint_left.mpr
  intro x hxi hxj
  obtain ⟨hxi, hnon⟩ := Finset.mem_filter.mp hxi
  have hxj := (Finset.mem_filter.mp hxj).1
  apply hnon
  exact central_of_two_distinct_parameters f a b
    (Finset.mem_filter.mp hxi).2 (Finset.mem_filter.mp hxj).2
    (fun h => hij (hinj h).symm)

/-- Equation (2), with the paper's actual homogeneous coordinates. -/
theorem edge_parameter_identity (f : E d → E d) (a : I → ℝ) (b : I → E d)
    {x y : E d} {i j : I} {μ : ℝ}
    (hxi : f x = a i • x + b i) (hyj : f y = a j • y + b j)
    (hxy : f y - f x = μ • (y - x)) :
    parameterVector a b j - parameterVector a b i =
      (a j - μ) • vertexVector y - (a i - μ) • vertexVector x := by
  apply Prod.ext
  · simp only [parameterVector, vertexVector, Prod.fst_sub, Prod.smul_fst,
      smul_eq_mul, mul_one]
    ring
  · change b j - b i = (a j - μ) • (-y) - (a i - μ) • (-x)
    calc
      b j - b i = (f y - f x) - a j • y + a i • x := by
        rw [hxi, hyj]
        module
      _ = μ • (y - x) - a j • y + a i • x := by rw [hxy]
      _ = _ := by module

/-- A homogeneous subspace containing a full-dimensional vertex star is
the entire parameter space. -/
theorem eq_top_of_contains_vertex_star (P : ConvexPolytope d)
    (hP : P.IsFullDim) {x : E d} (hx : x ∈ P.vertices)
    (M : Submodule ℝ (ℝ × E d)) (hMx : vertexVector x ∈ M)
    (hMedge : ∀ y, GeneralVertexStep P x y → vertexVector y ∈ M) : M = ⊤ := by
  have hdirections : ∀ w ∈ edgeStarSpan P x, ((0 : ℝ), w) ∈ M := by
    intro w hw
    induction hw using Submodule.span_induction with
    | mem w hw =>
      obtain ⟨y, hy, rfl⟩ := hw
      have h := M.sub_mem hMx (hMedge y hy)
      have he : vertexVector x - vertexVector y = ((0 : ℝ), y - x) := by
        apply Prod.ext
        · simp [vertexVector]
        · change -x - -y = y - x
          abel
      rwa [he] at h
    | zero => exact M.zero_mem
    | add u v hu hv ihu ihv =>
      simpa only [Prod.mk_add_mk, zero_add] using M.add_mem ihu ihv
    | smul c u hu ihu =>
      simpa only [Prod.smul_mk, smul_zero] using M.smul_mem c ihu
  have hall (w : E d) : ((0 : ℝ), w) ∈ M := by
    apply hdirections
    rw [fullDim_edgeStarSpan P hP hx]
    trivial
  apply top_unique
  rintro ⟨c, w⟩ _
  have h := M.add_mem (M.smul_mem c hMx) (hall (w + c • x))
  convert h using 1
  apply Prod.ext
  · simp [vertexVector]
  · simp only [vertexVector, Prod.snd_add, Prod.smul_snd]
    module

/-- An essential full class spans the entire quotient by the parameter
direction space, using only its noncentral vertices. -/
theorem noncentral_span_sup_direction_eq_top (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (a : I → ℝ) (b : I → E d)
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    (i : I) {x : E d} (hxi : x ∈ fullClass P f a b i)
    (hprivate : ∀ j, f x = a j • x + b j → j = i) :
    Submodule.span ℝ
        ((noncentralClass P f a b i).image vertexVector : Set (ℝ × E d)) ⊔
      parameterDirectionSpan a b = ⊤ := by
  classical
  let D := parameterDirectionSpan a b
  let S := noncentralClass P f a b i
  let A := S.image vertexVector
  let W := Submodule.span ℝ (A : Set (ℝ × E d))
  let M := W ⊔ D
  have hclass (z : E d) (hz : z ∈ fullClass P f a b i) : vertexVector z ∈ M := by
    by_cases hcentral : vertexVector z ∈ D
    · exact Submodule.mem_sup_right hcentral
    · apply Submodule.mem_sup_left
      apply Submodule.subset_span
      apply Finset.mem_image_of_mem
      exact Finset.mem_filter.mpr ⟨hz, hcentral⟩
  have hxdata := Finset.mem_filter.mp hxi
  have hMx : vertexVector x ∈ M := hclass x hxi
  have hMedge : ∀ y, GeneralVertexStep P x y → vertexVector y ∈ M := by
    intro y hxy
    by_cases hyi : y ∈ fullClass P f a b i
    · exact hclass y hyi
    obtain ⟨j, hyj⟩ := hcover y hxy.1
    obtain ⟨μ, hμ⟩ := hf x hxdata.1 y hxy.1 hxy
    have hji : j ≠ i := by
      intro he
      subst j
      exact hyi (Finset.mem_filter.mpr ⟨hxy.1, hyj⟩)
    have hne : a j - μ ≠ 0 := by
      intro he
      have hjμ : a j = μ := sub_eq_zero.mp he
      have hfxj : f x = a j • x + b j := by
        calc
          f x = f y - (f y - f x) := by abel
          _ = (a j • y + b j) - μ • (y - x) := by rw [hμ, hyj]
          _ = a j • x + b j := by rw [← hjμ]; module
      exact hji (hprivate j hfxj)
    have hdiff : parameterVector a b j - parameterVector a b i ∈ D :=
      Submodule.subset_span (Set.mem_range_self (j, i))
    have hsum := M.add_mem (Submodule.mem_sup_right hdiff)
      (M.smul_mem (a i - μ) hMx)
    rw [edge_parameter_identity f a b hxdata.2 hyj hμ, sub_add_cancel] at hsum
    have hinv := M.smul_mem (a j - μ)⁻¹ hsum
    simpa only [smul_smul, inv_mul_cancel₀ hne, one_smul] using hinv
  exact eq_top_of_contains_vertex_star P hP hxdata.1 M hMx hMedge

/-- Lemma 8 of the conditional-decomposability paper.  Every essential
full equality class contains at least the codimension of the parameter
direction space many noncentral vertices. -/
theorem class_bound (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (a : I → ℝ) (b : I → E d)
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    (i : I) {x : E d} (hxi : x ∈ fullClass P f a b i)
    (hprivate : ∀ j, f x = a j • x + b j → j = i) :
    d + 1 - finrank ℝ (parameterDirectionSpan a b) ≤
      (noncentralClass P f a b i).card := by
  classical
  let D := parameterDirectionSpan a b
  let S := noncentralClass P f a b i
  let A := S.image vertexVector
  let W := Submodule.span ℝ (A : Set (ℝ × E d))
  let M := W ⊔ D
  have htop : M = ⊤ :=
    noncentral_span_sup_direction_eq_top P hP f hf a b hcover i hxi hprivate
  have hW : finrank ℝ W ≤ S.card :=
    (finrank_span_finset_le_card (R := ℝ) A).trans
      (Finset.card_image_le (s := S) (f := vertexVector))
  have hdim := Submodule.finrank_sup_add_finrank_inf_eq W D
  change finrank ℝ M + finrank ℝ (W ⊓ D : Submodule ℝ (ℝ × E d)) = finrank ℝ W + finrank ℝ D at hdim
  rw [htop, finrank_top, Module.finrank_prod, finrank_euclideanSpace_fin] at hdim
  simp only [Module.finrank_self] at hdim
  change d + 1 - finrank ℝ D ≤ S.card
  omega

/-- The noncentral vertices form a disjoint union of the actual full
classes. Central vertices are counted only in `centralVertices`, whether
they belong to one class or several. -/
theorem vertex_count_partition [Fintype I]
    (P : ConvexPolytope d) (f : E d → E d) (a : I → ℝ) (b : I → E d)
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    (hinj : Function.Injective (parameterVector a b)) :
    P.vertices.card = (∑ i, (noncentralClass P f a b i).card) +
      (centralVertices P a b).card := by
  classical
  let C := noncentralClass P f a b
  have hdisjoint : (↑(Finset.univ : Finset I) : Set I).PairwiseDisjoint C := by
    intro i hi j hj hij
    exact noncentralClasses_disjoint P f a b hinj hij
  have hunion : Finset.univ.biUnion C =
      P.vertices.filter (fun x => vertexVector x ∉ parameterDirectionSpan a b) := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, _, hxi⟩ := Finset.mem_biUnion.mp hx
      obtain ⟨hxi, hnon⟩ := Finset.mem_filter.mp hxi
      exact Finset.mem_filter.mpr ⟨(Finset.mem_filter.mp hxi).1, hnon⟩
    · intro hx
      obtain ⟨hxP, hnon⟩ := Finset.mem_filter.mp hx
      obtain ⟨i, hxi⟩ := hcover x hxP
      apply Finset.mem_biUnion.mpr
      exact ⟨i, Finset.mem_univ i,
        Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hxP, hxi⟩, hnon⟩⟩
  have hcard :
      (P.vertices.filter (fun x => vertexVector x ∉ parameterDirectionSpan a b)).card =
        ∑ i, (noncentralClass P f a b i).card := by
    rw [← hunion, Finset.card_biUnion hdisjoint]
  have hpart := Finset.card_filter_add_card_filter_not (s := P.vertices)
    (fun x => vertexVector x ∈ parameterDirectionSpan a b)
  rw [hcard] at hpart
  change (centralVertices P a b).card +
    (∑ i, (noncentralClass P f a b i).card) = P.vertices.card at hpart
  omega

theorem essential_cover_vertex_bound [Fintype I]
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (a : I → ℝ) (b : I → E d)
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    (hprivate : ∀ i, ∃ x ∈ fullClass P f a b i,
      ∀ j, f x = a j • x + b j → j = i) :
    Fintype.card I * (d + 1 - finrank ℝ (parameterDirectionSpan a b)) +
      (centralVertices P a b).card ≤ P.vertices.card := by
  classical
  let r := d + 1 - finrank ℝ (parameterDirectionSpan a b)
  have hsum : (∑ _i : I, r) ≤ ∑ i, (noncentralClass P f a b i).card := by
    apply Finset.sum_le_sum
    intro i hi
    obtain ⟨x, hxi, hpriv⟩ := hprivate i
    exact class_bound P hP f hf a b hcover i hxi hpriv
  have hconst : (∑ _i : I, r) = Fintype.card I * r := by simp
  rw [hconst] at hsum
  have hcount := vertex_count_partition P f a b hcover
    (parameterVector_injective_of_private P f a b hprivate)
  change Fintype.card I * r + (centralVertices P a b).card ≤ P.vertices.card
  omega

/-- The exact count `N = m*r + E + s` used before the central vertices
have been shown to form a face. Each individual excess is nonnegative
because the actual class bound has already been proved. -/
theorem essential_cover_vertex_count [Fintype I]
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (a : I → ℝ) (b : I → E d)
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    (hprivate : ∀ i, ∃ x ∈ fullClass P f a b i,
      ∀ j, f x = a j • x + b j → j = i) :
    let r := d + 1 - finrank ℝ (parameterDirectionSpan a b)
    P.vertices.card = Fintype.card I * r +
      (∑ i, ((noncentralClass P f a b i).card - r)) +
      (centralVertices P a b).card := by
  classical
  dsimp only
  let r := d + 1 - finrank ℝ (parameterDirectionSpan a b)
  have hbound (i : I) : r ≤ (noncentralClass P f a b i).card := by
    obtain ⟨x, hxi, hpriv⟩ := hprivate i
    exact class_bound P hP f hf a b hcover i hxi hpriv
  have hsum : (∑ i, (noncentralClass P f a b i).card) =
      Fintype.card I * r + ∑ i, ((noncentralClass P f a b i).card - r) := by
    calc
      (∑ i, (noncentralClass P f a b i).card) =
          ∑ i, (r + ((noncentralClass P f a b i).card - r)) := by
        apply Finset.sum_congr rfl
        intro i hi
        have hi := hbound i
        omega
      _ = _ := by rw [Finset.sum_add_distrib]; simp
  have hcount := vertex_count_partition P f a b hcover
    (parameterVector_injective_of_private P f a b hprivate)
  rw [hsum] at hcount
  exact hcount

/-- The concave vertex-budget expression, throughout the entire interval
`4 ≤ m ≤ d - 1`. -/
theorem parameter_budget_inequality {d m : ℕ} (hm : 4 ≤ m) (hd : m + 1 ≤ d) :
    4 * d - 4 ≤ m * (d - m + 3) := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le hm
  obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le hd
  have hsub : 4 + a + 1 + b - (4 + a) = 1 + b := by omega
  rw [hsub]
  have he : (4 + a) * (1 + b + 3) + 4 =
      4 * (4 + a + 1 + b) + a * b := by ring
  omega

/-- The first conclusion of Proposition 12: the small vertex budget
forces full affine independence of the actual homothety parameters.
The remaining geometric alternative in that proposition is a separate
proof obligation. -/
theorem parameters_affineIndependent_of_vertex_budget [Fintype I]
    (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (a : I → ℝ) (b : I → E d)
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    (hprivate : ∀ i, ∃ x ∈ fullClass P f a b i,
      ∀ j, f x = a j • x + b j → j = i)
    (hm : 4 ≤ Fintype.card I) (hd : Fintype.card I + 1 ≤ d)
    (hN : P.vertices.card ≤ 4 * d - 5) :
    AffineIndependent ℝ (parameterVector a b) := by
  classical
  letI : Nonempty I := Fintype.card_pos_iff.mp (by omega)
  let m := Fintype.card I
  let t := finrank ℝ (parameterDirectionSpan a b)
  have ht : t + 1 ≤ m := parameter_finrank_add_one_le a b
  have hbudget := essential_cover_vertex_bound P hP f hf a b hcover hprivate
  change m * (d + 1 - t) + (centralVertices P a b).card ≤ P.vertices.card at hbudget
  have heq : t + 1 = m := by
    by_contra hne
    have ht' : t + 2 ≤ m := by omega
    have hr : d - m + 3 ≤ d + 1 - t := by omega
    have hprod : m * (d - m + 3) ≤ P.vertices.card :=
      (Nat.mul_le_mul_left m hr).trans (by
        change m * (d + 1 - t) ≤ P.vertices.card
        omega)
    have hconcave := parameter_budget_inequality hm hd
    change 4 * d - 4 ≤ m * (d - m + 3) at hconcave
    omega
  apply (affineIndependent_iff_finrank_vectorSpan_eq ℝ (parameterVector a b) heq.symm).mpr
  rw [← parameterDirectionSpan_eq_vectorSpan]

end Papers.Polytopes.HomothetyParameters

end
end
end BundlePart0

section BundlePart1
/- Source: Papers/HomothetyQuotient.lean -/






@[expose] public section

/-!
# Quotient coordinates of a minimum homothety class

The quotient is the actual quotient by the span of homothety-parameter
differences. Its basis is constructed from the noncentral vertices of a
minimum class, using the spanning result and the equality of dimensions.
The affine forms below evaluate ordinary homogeneous linear functionals
on `(1,-x)`; no projective positivity is assumed.

Development status: this new module awaits its first compiler check.
-/

noncomputable section
namespace Papers.Polytopes.HomothetyParameters

open Set Module
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {I : Type*}

def quotientVertex (a : I → ℝ) (b : I → E d) (x : E d) :
    (ℝ × E d) ⧸ parameterDirectionSpan a b :=
  (parameterDirectionSpan a b).mkQ (vertexVector x)

theorem span_quotient_noncentralClass (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (a : I → ℝ) (b : I → E d)
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    (i : I) {x : E d} (hxi : x ∈ fullClass P f a b i)
    (hprivate : ∀ j, f x = a j • x + b j → j = i) :
    Submodule.span ℝ (Set.range
      (fun u : noncentralClass P f a b i => quotientVertex a b u.val)) = ⊤ := by
  classical
  let D := parameterDirectionSpan a b
  let U := noncentralClass P f a b i
  have hrange : D.mkQ '' (U.image vertexVector : Set (ℝ × E d)) =
      Set.range (fun u : U => quotientVertex a b u.val) := by
    ext z
    constructor
    · rintro ⟨w, hw, rfl⟩
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.mp hw
      exact ⟨⟨u, hu⟩, rfl⟩
    · rintro ⟨u, rfl⟩
      exact ⟨vertexVector u.val, Finset.mem_image_of_mem _ u.property, rfl⟩
  rw [← hrange, ← Submodule.map_span]
  apply (Submodule.map_mkQ_eq_top D _).mpr
  rw [sup_comm]
  exact noncentral_span_sup_direction_eq_top P hP f hf a b hcover i hxi hprivate

/-- The basis assertion in Lemma 9, with no independence or quotient-span
assumption added to the geometric hypotheses. -/
theorem exists_classQuotientBasis (P : ConvexPolytope d) (hP : P.IsFullDim)
    (f : E d → E d) (hf : IsParallelMap P f) (a : I → ℝ) (b : I → E d)
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    (i : I) {x : E d} (hxi : x ∈ fullClass P f a b i)
    (hprivate : ∀ j, f x = a j • x + b j → j = i)
    (hcard : (noncentralClass P f a b i).card =
      d + 1 - finrank ℝ (parameterDirectionSpan a b)) :
    ∃ B : Basis (noncentralClass P f a b i) ℝ
      ((ℝ × E d) ⧸ parameterDirectionSpan a b),
      ∀ u, B u = quotientVertex a b u.val := by
  classical
  let U := noncentralClass P f a b i
  have hspan : ⊤ ≤ Submodule.span ℝ
      (Set.range (fun u : U => quotientVertex a b u.val)) := by
    rw [span_quotient_noncentralClass P hP f hf a b hcover i hxi hprivate]
  have hdim : Fintype.card U =
      finrank ℝ ((ℝ × E d) ⧸ parameterDirectionSpan a b) := by
    rw [Fintype.card_coe, quotient_finrank]
    exact hcard
  refine ⟨basisOfTopLeSpanOfCardEqFinrank
    (fun u : U => quotientVertex a b u.val) hspan hdim, ?_⟩
  intro u
  exact congrFun (coe_basisOfTopLeSpanOfCardEqFinrank _ hspan hdim) u

/-- Noncentral vertices are private once the actual parameters are
distinct; privateness is not an extra hypothesis on minimum-class vertices. -/
theorem noncentral_vertex_private (P : ConvexPolytope d) (f : E d → E d)
    (a : I → ℝ) (b : I → E d)
    (hinj : Function.Injective (parameterVector a b)) {i : I} {x : E d}
    (hx : x ∈ noncentralClass P f a b i) :
    ∀ j, f x = a j • x + b j → j = i := by
  intro j hxj
  obtain ⟨hxi, hnon⟩ := Finset.mem_filter.mp hx
  by_contra hji
  apply hnon
  exact central_of_two_distinct_parameters f a b
    (Finset.mem_filter.mp hxi).2 hxj (fun h => hji (hinj h))

/-- Restriction of a homogeneous functional to the ordinary affine chart. -/
def homogeneousForm (L : (ℝ × E d) →ₗ[ℝ] ℝ) : E d →ᵃ[ℝ] ℝ :=
  (-(L.comp (LinearMap.inr ℝ ℝ (E d)))).toAffineMap +
    AffineMap.const ℝ (E d) (L (1, 0))

theorem homogeneousForm_apply (L : (ℝ × E d) →ₗ[ℝ] ℝ) (x : E d) :
    homogeneousForm L x = L (vertexVector x) := by
  change -L (0, x) + L (1, 0) = L (1, -x)
  have he : ((1 : ℝ), -x) = (1, (0 : E d)) - (0, x) := by
    ext <;> simp
  rw [he, map_sub]
  ring

/-- The actual edge minimum principle, applied to an affine chart. -/
theorem affine_nonneg_of_zero_vertex_neighbors (P : ConvexPolytope d)
    (g : E d →ᵃ[ℝ] ℝ) {x : E d} (hx : x ∈ P.vertices) (hxg : g x = 0)
    (hneighbors : ∀ y, GeneralVertexStep P x y → 0 ≤ g y) :
    ∀ y ∈ P.toSet, 0 ≤ g y := by
  let l := g.linear.toContinuousLinearMap
  have hmax : ∀ y, GeneralVertexStep P x y → (-l) y ≤ (-l) x := by
    intro y hy
    have hn := hneighbors y hy
    rw [affine_form_apply g y] at hn
    rw [affine_form_apply g x] at hxg
    change -g.linear y ≤ -g.linear x
    linarith
  intro y hy
  have h := vertex_max_of_edge_max P (-l) hx hmax y hy
  change -g.linear y ≤ -g.linear x at h
  rw [affine_form_apply g x] at hxg
  rw [affine_form_apply g y]
  linarith

theorem affine_constant_of_vertex_neighbors (P : ConvexPolytope d)
    (g : E d →ᵃ[ℝ] ℝ) {x : E d} (hx : x ∈ P.vertices)
    (hneighbors : ∀ y, GeneralVertexStep P x y → g y = g x) :
    ∀ y ∈ P.toSet, g y = g x := by
  let l := g.linear.toContinuousLinearMap
  have hlin : ∀ y, GeneralVertexStep P x y → l y = l x := by
    intro y hy
    have h := hneighbors y hy
    rw [affine_form_apply g y, affine_form_apply g x] at h
    exact add_right_cancel h
  intro y hy
  have h := linear_constant_of_neighbors P l hx hlin y hy
  rw [affine_form_apply g y, affine_form_apply g x]
  exact congrArg (fun z => z + g 0) h

/-- A crossing neighbor lies on the same quotient ray as a private
vertex. This form of the statement supplies every dual-coordinate zero
needed by the fiber-face argument. -/
theorem crossing_functional_zero (P : ConvexPolytope d)
    (f : E d → E d) (hf : IsParallelMap P f) (a : I → ℝ) (b : I → E d)
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    {i : I} {x y : E d} (hxi : x ∈ fullClass P f a b i)
    (hprivate : ∀ j, f x = a j • x + b j → j = i)
    (hxy : GeneralVertexStep P x y) (hyi : y ∉ fullClass P f a b i)
    (L : (ℝ × E d) →ₗ[ℝ] ℝ)
    (hD : parameterDirectionSpan a b ≤ L.ker) (hxL : L (vertexVector x) = 0) :
    L (vertexVector y) = 0 := by
  obtain ⟨hxP, hxfi⟩ := Finset.mem_filter.mp hxi
  obtain ⟨j, hyj⟩ := hcover y hxy.1
  obtain ⟨μ, hμ⟩ := hf x hxP y hxy.1 hxy
  have hne : a j - μ ≠ 0 := by
    intro he
    have hjμ : a j = μ := sub_eq_zero.mp he
    have hfxj : f x = a j • x + b j := by
      calc
        f x = f y - (f y - f x) := by abel
        _ = (a j • y + b j) - μ • (y - x) := by rw [hμ, hyj]
        _ = a j • x + b j := by rw [← hjμ]; module
    have hji := hprivate j hfxj
    apply hyi
    exact Finset.mem_filter.mpr ⟨hxy.1, by simpa only [hji] using hyj⟩
  have hz : L (parameterVector a b j - parameterVector a b i) = 0 :=
    hD (Submodule.subset_span (Set.mem_range_self (j, i)))
  rw [edge_parameter_identity f a b hxfi hyj hμ, map_sub, map_smul,
    map_smul, hxL, smul_zero, sub_zero, smul_eq_mul] at hz
  exact (mul_eq_zero.mp hz).resolve_left hne

end Papers.Polytopes.HomothetyParameters

end
end
end BundlePart1

section BundlePart2
/- Source: Papers/FaceDimensionBound.lean -/




@[expose] public section

/-!
# Dimension from the edges that leave a face

At a vertex, the directions of all incident edges span the full polytope.
If only k neighbors lie outside a set containing that vertex, the set's
affine dimension is at least d-k. The case k=1 characterizes a proper
exposed face as a facet. These are the local dimension estimates used in
the fiber-face argument for conditional decomposability.
-/

noncomputable section
namespace Papers.Polytopes
open Set Module
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ}

theorem dim_le_faceDim_add_outside_neighbors (P : ConvexPolytope d)
    (hP : P.IsFullDim) {v : E d} (hv : v ∈ P.vertices)
    (F : Set (E d)) (hvF : v ∈ F) (S : Finset (E d))
    (hcover : ∀ y, GeneralVertexStep P v y → y ∈ F ∨ y ∈ S) :
    d ≤ faceDim F + S.card := by
  let A := S.image (fun y => y - v)
  let W := Submodule.span ℝ (A : Set (E d))
  have hstar : edgeStarSpan P v ≤ vectorSpan ℝ F ⊔ W := by
    apply Submodule.span_le.mpr
    rintro w ⟨y, hy, rfl⟩
    rcases hcover y hy with hyF | hyS
    · exact Submodule.mem_sup_left (vsub_mem_vectorSpan ℝ hyF hvF)
    · exact Submodule.mem_sup_right
        (Submodule.subset_span (Finset.mem_image_of_mem _ hyS))
  have htop : vectorSpan ℝ F ⊔ W = ⊤ := by
    apply top_unique
    rwa [fullDim_edgeStarSpan P hP hv] at hstar
  have hW : finrank ℝ W ≤ S.card :=
    (finrank_span_finset_le_card (R := ℝ) A).trans
      (Finset.card_image_le (s := S) (f := fun y => y - v))
  have h := Submodule.finrank_sup_add_finrank_inf_eq (vectorSpan ℝ F) W
  rw [htop, finrank_top, finrank_euclideanSpace_fin] at h
  change d ≤ finrank ℝ (vectorSpan ℝ F) + S.card
  omega

theorem faceDim_eq_dim_sub_one_of_one_outside_neighbor
    (P : ConvexPolytope d) (hP : P.IsFullDim) {F : Set (E d)}
    (hF : P.IsFace F) (hproper : F ≠ P.toSet)
    {v y : E d} (hv : v ∈ P.vertices) (hvF : v ∈ F)
    (hcover : ∀ z, GeneralVertexStep P v z → z ∈ F ∨ z = y) :
    faceDim F = d - 1 := by
  have hlow := dim_le_faceDim_add_outside_neighbors P hP hv F hvF {y}
    (by intro z hz; simpa only [Finset.mem_singleton] using hcover z hz)
  have hhigh := faceDim_lt_of_ssubset P hF (toSet_isFace P)
    (Set.ssubset_iff_subset_ne.mpr ⟨hF.1.subset, hproper⟩)
  change faceDim F < P.dim at hhigh
  rw [hP] at hhigh
  simp only [Finset.card_singleton] at hlow
  omega

end Papers.Polytopes

end
end
end BundlePart2

section BundlePart3
/- Source: Papers/HomothetyMinimumClass.lean -/





@[expose] public section

/-!
# The clique and facets of a minimum homothety class

All coordinates are dual coordinates in the actual quotient by the
homothety-parameter direction space. A basis with the required vectors
is supplied by `exists_classQuotientBasis`. This file proves the geometric
consequences: the minimum class is a clique, the coordinate forms are
nonnegative on the whole polytope, and their zero sets are actual facets.

Development status: this new module awaits its first compiler check.
-/

noncomputable section
namespace Papers.Polytopes.HomothetyParameters

open Set Module
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {I J : Type*}

def quotientCoordinate (D : Submodule ℝ (ℝ × E d))
    (B : Basis J ℝ ((ℝ × E d) ⧸ D)) (q : J) : (ℝ × E d) →ₗ[ℝ] ℝ :=
  (B.coord q).comp D.mkQ

theorem quotientCoordinate_vanishes (D : Submodule ℝ (ℝ × E d))
    (B : Basis J ℝ ((ℝ × E d) ⧸ D)) (q : J) :
    D ≤ (quotientCoordinate D B q).ker := by
  intro z hz
  change B.coord q (D.mkQ z) = 0
  have hzq : D.mkQ z = 0 := (Submodule.Quotient.mk_eq_zero D).mpr hz
  rw [hzq, map_zero]

section MinimumClass

variable (P : ConvexPolytope d) (f : E d → E d) (a : I → ℝ) (b : I → E d)
    (i : I)
    (B : Basis (noncentralClass P f a b i) ℝ
      ((ℝ × E d) ⧸ parameterDirectionSpan a b))
    (hB : ∀ u, B u = quotientVertex a b u.val)

include hB

theorem quotientCoordinate_vertex (q u : noncentralClass P f a b i) :
    quotientCoordinate (parameterDirectionSpan a b) B q (vertexVector u.val) =
      if u = q then 1 else 0 := by
  change B.coord q (quotientVertex a b u.val) = _
  rw [← hB u]
  simp only [Basis.coord_apply, Basis.repr_self_apply]

omit hB in
theorem quotientCoordinate_central (q : noncentralClass P f a b i)
    {x : E d} (hx : vertexVector x ∈ parameterDirectionSpan a b) :
    quotientCoordinate (parameterDirectionSpan a b) B q (vertexVector x) = 0 :=
  quotientCoordinate_vanishes _ B q hx

/-- Away from its own minimum-class vertex, a dual coordinate is zero
on every neighbor except possibly that vertex itself. -/
theorem quotientCoordinate_neighbor_zero (hf : IsParallelMap P f)
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    (hinj : Function.Injective (parameterVector a b))
    (q u : noncentralClass P f a b i) (huq : u ≠ q)
    {y : E d} (huy : GeneralVertexStep P u.val y) (hyq : y ≠ q.val) :
    quotientCoordinate (parameterDirectionSpan a b) B q (vertexVector y) = 0 := by
  let L := quotientCoordinate (parameterDirectionSpan a b) B q
  have huL : L (vertexVector u.val) = 0 := by
    rw [quotientCoordinate_vertex P f a b i B hB q u, if_neg huq]
  by_cases hycentral : vertexVector y ∈ parameterDirectionSpan a b
  · exact quotientCoordinate_central P f a b i B q hycentral
  by_cases hyi : y ∈ fullClass P f a b i
  · let v : noncentralClass P f a b i :=
      ⟨y, Finset.mem_filter.mpr ⟨hyi, hycentral⟩⟩
    have hvq : v ≠ q := fun he => hyq (congrArg Subtype.val he)
    exact (quotientCoordinate_vertex P f a b i B hB q v).trans (if_neg hvq)
  · exact crossing_functional_zero P f hf a b hcover
      (Finset.mem_filter.mp u.property).1
      (noncentral_vertex_private P f a b hinj u.property) huy hyi L
      (quotientCoordinate_vanishes _ B q) huL

/-- The noncentral vertices of a minimum class form an actual clique in
the edge graph. It is not merely a simplex in the quotient. -/
theorem minimumClass_clique (hf : IsParallelMap P f)
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    (hinj : Function.Injective (parameterVector a b))
    (u q : noncentralClass P f a b i) (huq : u ≠ q) :
    GeneralVertexStep P u.val q.val := by
  by_contra hnot
  let L := quotientCoordinate (parameterDirectionSpan a b) B q
  let g := homogeneousForm L
  have huP : u.val ∈ P.vertices :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp u.property).1).1
  have hqP : q.val ∈ P.vertices :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp q.property).1).1
  have hug : g u.val = 0 := by
    rw [homogeneousForm_apply]
    exact (quotientCoordinate_vertex P f a b i B hB q u).trans (if_neg huq)
  have hqg : g q.val = 1 := by
    rw [homogeneousForm_apply]
    exact (quotientCoordinate_vertex P f a b i B hB q q).trans (if_pos rfl)
  have hneighbors : ∀ y, GeneralVertexStep P u.val y → g y = g u.val := by
    intro y huy
    rw [hug, homogeneousForm_apply]
    apply quotientCoordinate_neighbor_zero P f a b i B hB hf hcover hinj q u huq huy
    intro he
    exact hnot (he ▸ huy)
  have hzero := affine_constant_of_vertex_neighbors P g huP hneighbors q.val
    (subset_convexHull ℝ _ hqP)
  rw [hug, hqg] at hzero
  exact one_ne_zero hzero

/-- Nonnegativity is derived from the actual edge minimum principle at
any other class vertex. The class has at least two vertices exactly when
this argument is needed in Lemma 9. -/
theorem minimumClass_coordinate_nonnegative (hf : IsParallelMap P f)
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    (hinj : Function.Injective (parameterVector a b))
    (hsize : 2 ≤ (noncentralClass P f a b i).card)
    (q : noncentralClass P f a b i) :
    ∀ x ∈ P.toSet,
      0 ≤ quotientCoordinate (parameterDirectionSpan a b) B q (vertexVector x) := by
  classical
  obtain ⟨v, hv, w, hw, hvw⟩ := Finset.one_lt_card.mp (by omega :
    1 < (noncentralClass P f a b i).card)
  obtain ⟨u, huq⟩ : ∃ u : noncentralClass P f a b i, u ≠ q := by
    by_cases hvq : v = q.val
    · refine ⟨⟨w, hw⟩, ?_⟩
      intro he
      exact hvw (hvq.trans (congrArg Subtype.val he).symm)
    · exact ⟨⟨v, hv⟩, fun he => hvq (congrArg Subtype.val he)⟩
  let L := quotientCoordinate (parameterDirectionSpan a b) B q
  let g := homogeneousForm L
  have huP : u.val ∈ P.vertices :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp u.property).1).1
  have hug : g u.val = 0 := by
    rw [homogeneousForm_apply]
    exact (quotientCoordinate_vertex P f a b i B hB q u).trans (if_neg huq)
  have hneighbors : ∀ y, GeneralVertexStep P u.val y → 0 ≤ g y := by
    intro y huy
    rw [homogeneousForm_apply]
    by_cases hyq : y = q.val
    · rw [hyq, quotientCoordinate_vertex P f a b i B hB q q, if_pos rfl]
      exact zero_le_one
    · rw [quotientCoordinate_neighbor_zero P f a b i B hB hf hcover hinj
        q u huq huy hyq]
  intro x hx
  have hh := affine_nonneg_of_zero_vertex_neighbors P g huP hug hneighbors x hx
  change 0 ≤ homogeneousForm L x at hh
  simpa only [homogeneousForm_apply] using hh

/-- Every coordinate hyperplane of a minimum class is an actual facet
of the original full-dimensional polytope. -/
theorem minimumClass_coordinate_facet (hP : P.IsFullDim) (hf : IsParallelMap P f)
    (hcover : ∀ y ∈ P.vertices, ∃ j, f y = a j • y + b j)
    (hinj : Function.Injective (parameterVector a b))
    (hsize : 2 ≤ (noncentralClass P f a b i).card)
    (q : noncentralClass P f a b i) :
    IsFacet P (affineZeroFace P
      (homogeneousForm (quotientCoordinate (parameterDirectionSpan a b) B q))) := by
  classical
  let L := quotientCoordinate (parameterDirectionSpan a b) B q
  let g := homogeneousForm L
  let F := affineZeroFace P g
  obtain ⟨v, hv, w, hw, hvw⟩ := Finset.one_lt_card.mp (by omega :
    1 < (noncentralClass P f a b i).card)
  obtain ⟨u, huq⟩ : ∃ u : noncentralClass P f a b i, u ≠ q := by
    by_cases hvq : v = q.val
    · refine ⟨⟨w, hw⟩, ?_⟩
      intro he
      exact hvw (hvq.trans (congrArg Subtype.val he).symm)
    · exact ⟨⟨v, hv⟩, fun he => hvq (congrArg Subtype.val he)⟩
  have huP : u.val ∈ P.vertices :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp u.property).1).1
  have hug : g u.val = 0 := by
    rw [homogeneousForm_apply]
    exact (quotientCoordinate_vertex P f a b i B hB q u).trans (if_neg huq)
  have huF : u.val ∈ F := ⟨subset_convexHull ℝ _ huP, hug⟩
  have hg : ∀ x ∈ P.toSet, 0 ≤ g x := by
    intro x hx
    rw [homogeneousForm_apply]
    exact minimumClass_coordinate_nonnegative P f a b i B hB hf hcover hinj hsize q x hx
  have hF : P.IsFace F := affineZeroFace_isFace P g hg ⟨u.val, huF⟩
  have hqg : g q.val = 1 := by
    rw [homogeneousForm_apply]
    exact (quotientCoordinate_vertex P f a b i B hB q q).trans (if_pos rfl)
  have hproper : F ≠ P.toSet :=
    affineZeroFace_ne_body_of_ne_zero P hP g q.val (by rw [hqg]; exact one_ne_zero)
  have houtside : ∀ y, GeneralVertexStep P u.val y → y ∈ F ∨ y = q.val := by
    intro y huy
    by_cases hyq : y = q.val
    · exact Or.inr hyq
    · left
      refine ⟨subset_convexHull ℝ _ huy.1, ?_⟩
      rw [homogeneousForm_apply]
      exact quotientCoordinate_neighbor_zero P f a b i B hB hf hcover hinj
        q u huq huy hyq
  have hlow := dim_le_faceDim_add_outside_neighbors P hP huP F huF {q.val}
    (by intro y hy; simpa only [Finset.mem_singleton] using houtside y hy)
  have hhigh := faceDim_lt_of_ssubset P hF (toSet_isFace P)
    (Set.ssubset_iff_subset_ne.mpr ⟨hF.1.subset, hproper⟩)
  change faceDim F < P.dim at hhigh
  simp only [Finset.card_singleton] at hlow
  refine ⟨hF, ?_⟩
  change faceDim F+1=P.dim
  rw [hP] at hhigh ⊢
  omega

end MinimumClass
end Papers.Polytopes.HomothetyParameters

end
end
end BundlePart3

section BundlePart4
/- Source: Papers/HomothetyOwnership.lean -/




@[expose] public section

/-!
# Ownership of vertices under independent homotheties

These are the parameter-space assertions used after Lemma 9 and in
Proposition 12 of the conditional-decomposability paper. Owners are the
actual indices of homotheties agreeing with the given map at a point.
An affinely independent parameter family has at most two owners at any
point. If a further homothety agrees with the map on a set of points and
is not a member of the family, the ownership sets of distinct points
are disjoint, and at most one of those points can have two owners.

The argument uses the intersection theorem for affine spans of subsets
of an affinely independent family. It does not assume a central face,
generic position of the polytope, or an unproved incidence property.

Development status: this new module awaits its first compiler check.
-/

noncomputable section
namespace Papers.Polytopes.HomothetyParameters

open Set Module
open scoped Classical
open LeanEval.Geometry.PlatonicClassification
open LeanEval.Geometry.PlatonicClassification.ConvexPolytope

variable {d : ℕ} {I : Type*}

def ownerSet (f : E d → E d) (a : I → ℝ) (b : I → E d) (x : E d) : Set I :=
  {i | f x = a i • x + b i}

def owners [Fintype I] (f : E d → E d) (a : I → ℝ) (b : I → E d)
    (x : E d) : Finset I :=
  Finset.univ.filter (fun i => f x = a i • x + b i)

theorem coe_owners [Fintype I] (f : E d → E d) (a : I → ℝ) (b : I → E d)
    (x : E d) : (owners f a b x : Set I) = ownerSet f a b x := by
  ext i
  simp [owners, ownerSet]

theorem vertexVector_ne_zero (x : E d) : vertexVector x ≠ 0 := by
  intro h
  have := congrArg Prod.fst h
  norm_num [vertexVector] at this

theorem owner_vectorSpan_le (f : E d → E d) (a : I → ℝ) (b : I → E d)
    (x : E d) :
    vectorSpan ℝ (parameterVector a b '' ownerSet f a b x) ≤
      Submodule.span ℝ {vertexVector x} := by
  rw [vectorSpan_def]
  apply Submodule.span_le.mpr
  intro w hw
  obtain ⟨u, ⟨i, hi, rfl⟩, v, ⟨j, hj, rfl⟩, rfl⟩ := Set.mem_vsub.mp hw
  change parameterVector a b i - parameterVector a b j ∈ _
  rw [parameter_difference_at_common_point f a b hj hi]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))

/-- The at-most-two assertion preceding equation (3). It holds at every
point, whether or not that point has already been shown to be central. -/
theorem owners_card_le_two [Fintype I]
    (f : E d → E d) (a : I → ℝ) (b : I → E d)
    (ha : AffineIndependent ℝ (parameterVector a b)) (x : E d) :
    (owners f a b x).card ≤ 2 := by
  classical
  by_cases hne : (owners f a b x).Nonempty
  · let J := owners f a b x
    letI : Nonempty J := ⟨⟨hne.choose, hne.choose_spec⟩⟩
    let p : J → ℝ × E d := fun i => parameterVector a b i.val
    have hind : AffineIndependent ℝ p :=
      ha.comp_embedding ⟨Subtype.val, Subtype.val_injective⟩
    have hrange : Set.range p = parameterVector a b '' ownerSet f a b x := by
      ext z
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨i.val, (Finset.mem_filter.mp i.property).2, rfl⟩
      · rintro ⟨i, hi, rfl⟩
        exact ⟨⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩⟩, rfl⟩
    have hdim := Submodule.finrank_mono (owner_vectorSpan_le f a b x)
    rw [finrank_span_singleton (vertexVector_ne_zero x), ← hrange] at hdim
    have hc := hind.finrank_vectorSpan_add_one
    rw [Fintype.card_coe] at hc
    change (owners f a b x).card ≤ 2
    change finrank ℝ (vectorSpan ℝ (Set.range p)) + 1 = (owners f a b x).card at hc
    omega
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp

theorem homothety_parameters_eq_of_two_points
    {α β : ℝ} {c e x y : E d} (hxy : x ≠ y)
    (hx : α • x + c = β • x + e)
    (hy : α • y + c = β • y + e) : (α, c) = (β, e) := by
  have hz : (α - β) • (x - y) = 0 := by
    calc
      (α - β) • (x - y) =
          (α • x + c - (β • x + e)) - (α • y + c - (β • y + e)) := by module
      _ = 0 := by rw [hx, hy]; simp
  have hα : α = β := sub_eq_zero.mp
    ((smul_eq_zero.mp hz).resolve_right (sub_ne_zero.mpr hxy))
  have hc : c = e := by rw [hα] at hx; exact add_left_cancel hx
  exact Prod.ext hα hc

/-- A new homothety cannot share the same old owner at two distinct
points where it agrees with the map. -/
theorem ownerSets_disjoint_of_new_homothety
    (f : E d → E d) (a : I → ℝ) (b : I → E d)
    {α : ℝ} {c x y : E d} (hxy : x ≠ y)
    (hnew : ∀ i, (α, c) ≠ parameterVector a b i)
    (hx : f x = α • x + c) (hy : f y = α • y + c) :
    Disjoint (ownerSet f a b x) (ownerSet f a b y) := by
  apply Set.disjoint_left.mpr
  intro i hxi hyi
  exact hnew i (homothety_parameters_eq_of_two_points hxy
    (hx.symm.trans hxi) (hy.symm.trans hyi))

theorem parameter_difference_new
    (f : E d → E d) (a : I → ℝ) (b : I → E d)
    {α : ℝ} {c x : E d} {i : I}
    (hxi : f x = a i • x + b i) (hx : f x = α • x + c) :
    (α, c) - parameterVector a b i = (α - a i) • vertexVector x := by
  have hc : c = f x - α • x := by rw [hx]; abel
  have hb : b i = f x - a i • x := by rw [hxi]; abel
  apply Prod.ext
  · simp [parameterVector, vertexVector]
  · change c - b i = (α - a i) • (-x)
    rw [hc, hb]
    module

/-- If a point has two owners, every homothety taking the same value
there lies on the actual affine line between their parameters. -/
theorem new_parameter_mem_owner_affineSpan
    (f : E d → E d) (a : I → ℝ) (b : I → E d)
    (hinj : Function.Injective (parameterVector a b))
    {α : ℝ} {c x : E d} (hx : f x = α • x + c)
    {i j : I} (hij : i ≠ j) (hi : i ∈ ownerSet f a b x)
    (hj : j ∈ ownerSet f a b x) :
    (α, c) ∈ affineSpan ℝ (parameterVector a b '' ownerSet f a b x) := by
  let S := affineSpan ℝ (parameterVector a b '' ownerSet f a b x)
  have hdiff := parameter_difference_at_common_point f a b hi hj
  have hden : a j - a i ≠ 0 := by
    intro hz
    have he : parameterVector a b j = parameterVector a b i := by
      apply sub_eq_zero.mp
      rw [hdiff, hz, zero_smul]
    exact hij (hinj he).symm
  have hnew := parameter_difference_new f a b hi hx
  have he : AffineMap.lineMap (parameterVector a b i) (parameterVector a b j)
      ((α - a i) / (a j - a i)) = (α, c) := by
    rw [AffineMap.lineMap_apply_module', hdiff, smul_smul,
      div_mul_cancel₀ _ hden, ← hnew]
    abel
  rw [← he]
  exact AffineMap.lineMap_mem _
    (subset_affineSpan ℝ _ (Set.mem_image_of_mem _ hi))
    (subset_affineSpan ℝ _ (Set.mem_image_of_mem _ hj))

/-- With independent parameters, two distinct shared points cannot both
lie on a new homothety. This is the skew-parameter-line argument in
Proposition 12, without a separate geometric general-position premise. -/
theorem at_most_one_shared_point_of_new_homothety
    (f : E d → E d) (a : I → ℝ) (b : I → E d)
    (ha : AffineIndependent ℝ (parameterVector a b))
    {α : ℝ} {c x y : E d}
    (hnew : ∀ i, (α, c) ≠ parameterVector a b i)
    (hx : f x = α • x + c) (hy : f y = α • y + c)
    (hxshared : ∃ i ∈ ownerSet f a b x, ∃ j ∈ ownerSet f a b x, i ≠ j)
    (hyshared : ∃ i ∈ ownerSet f a b y, ∃ j ∈ ownerSet f a b y, i ≠ j) :
    x = y := by
  by_contra hxy
  obtain ⟨i, hi, j, hj, hij⟩ := hxshared
  obtain ⟨k, hk, l, hl, hkl⟩ := hyshared
  have hd := ha.affineSpan_disjoint_of_disjoint
    (ownerSets_disjoint_of_new_homothety f a b hxy hnew hx hy)
  exact Set.disjoint_left.mp hd
    (new_parameter_mem_owner_affineSpan f a b ha.injective hx hij hi hj)
    (new_parameter_mem_owner_affineSpan f a b ha.injective hy hkl hk hl)

end Papers.Polytopes.HomothetyParameters

end
end
end BundlePart4

