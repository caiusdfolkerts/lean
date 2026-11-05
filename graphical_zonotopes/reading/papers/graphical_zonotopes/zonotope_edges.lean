module

public import Papers.GraphicalZonotopes.ExposedSegments
public import Mathlib.Algebra.Group.Pointwise.Set.BigOperators

@[expose] public section
noncomputable section
namespace GraphicalZonotopes
open Finset
open scoped BigOperators Pointwise

section FiniteSums
variable {E I : Type*} [AddCommGroup E] [Module ℝ E]

theorem sum_update_difference [DecidableEq I] (s : Finset I) (f : I → E)
    {i : I} (hi : i ∈ s) (x : E) :
    (∑ j ∈ s, Function.update f i x j) - ∑ j ∈ s, f j = x-f i := by
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single i]
  · simp
  · intro j hj hji
    simp [Function.update_of_ne hji]
  · exact fun hn => False.elim (hn hi)

theorem mixed_sum_mem [DecidableEq I] (s : Finset I) (K : I → Set E)
    (f : I → E) (hf : ∀ i ∈ s, f i ∈ K i) {i : I}
    (x : E) (hx : x ∈ K i) :
    (∑ j ∈ s, Function.update f i x j) ∈ ∑ j ∈ s, K j := by
  apply Set.finsetSum_mem_finsetSum
  intro j hj
  by_cases hji : j = i
  · subst j
    simpa using hx
  · simpa [Function.update_of_ne hji] using hf j hj

/-- A nondegenerate exposed edge of a finite Minkowski sum of segments is
parallel to one of the summand segments. All faces here are actual exposed
subsets of the Minkowski sum, not abstract cone coordinates. -/
theorem exposed_edge_of_sum_segments (s : Finset I) (a b : I → E)
    {p q : E} (hpq : p ≠ q) (l : E →ₗ[ℝ] ℝ) (c : ℝ)
    (hbound : ∀ x ∈ (∑ i ∈ s, segment ℝ (a i) (b i)), c ≤ l x)
    (hface : {x ∈ (∑ i ∈ s, segment ℝ (a i) (b i)) | l x = c} =
      segment ℝ p q) :
    ∃ i ∈ s, ∃ t : ℝ, t ≠ 0 ∧ q-p = t • (b i-a i) := by
  classical
  have hp : p ∈ (∑ i ∈ s, segment ℝ (a i) (b i)) ∧ l p = c := by
    exact hface.symm.subset (left_mem_segment ℝ p q)
  have hq : q ∈ (∑ i ∈ s, segment ℝ (a i) (b i)) ∧ l q = c := by
    exact hface.symm.subset (right_mem_segment ℝ p q)
  obtain ⟨f,hf,hfp⟩ := (Set.mem_finsetSum s (fun i => segment ℝ (a i) (b i)) p).mp hp.1
  obtain ⟨g,hg,hgq⟩ := (Set.mem_finsetSum s (fun i => segment ℝ (a i) (b i)) q).mp hq.1
  have hdiff : ∃ i ∈ s, f i ≠ g i := by
    by_contra hn
    push_neg at hn
    apply hpq
    rw [← hfp,← hgq]
    exact sum_congr rfl hn
  obtain ⟨i,hi,hine⟩ := hdiff
  let r := ∑ j ∈ s, Function.update f i (g i) j
  let u := ∑ j ∈ s, Function.update g i (f i) j
  have hr : r ∈ (∑ j ∈ s, segment ℝ (a j) (b j)) :=
    mixed_sum_mem s _ f (fun j hj => hf hj) (g i) (hg hi)
  have hu : u ∈ (∑ j ∈ s, segment ℝ (a j) (b j)) :=
    mixed_sum_mem s _ g (fun j hj => hg hj) (f i) (hf hi)
  have hrsub : r-p = g i-f i := by
    dsimp [r]
    rw [← hfp]
    exact sum_update_difference s f hi (g i)
  have husub : u-q = f i-g i := by
    dsimp [u]
    rw [← hgq]
    exact sum_update_difference s g hi (f i)
  have hrl : l r = c := by
    have h₁ := hbound r hr
    have h₂ := hbound u hu
    have h₃ := congrArg l hrsub
    have h₄ := congrArg l husub
    simp only [map_sub,hp.2,hq.2] at h₃ h₄
    linarith
  have hrseg : r ∈ segment ℝ p q := by
    rw [← hface]
    exact ⟨hr,hrl⟩
  have hspan : g i-f i ∈ Submodule.span ℝ {q-p} := by
    have h := vsub_mem_vectorSpan ℝ hrseg (left_mem_segment ℝ p q)
    rw [vectorSpan_segment] at h
    simpa only [vsub_eq_sub,hrsub] using h
  have hgen : g i-f i ∈ Submodule.span ℝ {b i-a i} := by
    have h := vsub_mem_vectorSpan ℝ (hg hi) (hf hi)
    rw [vectorSpan_segment] at h
    exact h
  obtain ⟨α,hα⟩ := Submodule.mem_span_singleton.mp hspan
  obtain ⟨β,hβ⟩ := Submodule.mem_span_singleton.mp hgen
  have hα0 : α ≠ 0 := by
    intro h
    rw [h,zero_smul] at hα
    exact hine (sub_eq_zero.mp hα.symm).symm
  have hβ0 : β ≠ 0 := by
    intro h
    rw [h,zero_smul] at hβ
    exact hine (sub_eq_zero.mp hβ.symm).symm
  refine ⟨i,hi,α⁻¹*β,mul_ne_zero (inv_ne_zero hα0) hβ0,?_⟩
  calc
    q-p = α⁻¹ • (α • (q-p)) := by simp [smul_smul,hα0]
    _ = α⁻¹ • (β • (b i-a i)) := by rw [hα,hβ]
    _ = (α⁻¹*β) • (b i-a i) := by rw [smul_smul]

end FiniteSums

section Graphs
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem smul_segment_eq (k : ℝ) (p q : V → ℝ) :
    k • segment ℝ p q = segment ℝ (k • p) (k • q) := by
  change (fun x : V → ℝ => k • x) '' segment ℝ p q = _
  exact image_segment ℝ ((k • (LinearMap.id : (V → ℝ) →ₗ[ℝ] (V → ℝ))).toAffineMap) p q

/-- Every exposed edge of a dilated graphical zonotope has one of the graph's
actual standard-root directions. This holds even for disconnected graphs. -/
theorem graphical_zonotope_exposed_edge (G : SimpleGraph V) (k : ℝ)
    {p q : V → ℝ} (hex : IsExposedSegment (k • graphicalZonotope G) p q) :
    ∃ u v, G.Adj u v ∧ ∃ t : ℝ, t ≠ 0 ∧
      q-p = t • (basisVector v-basisVector u) := by
  classical
  let Edge := {C : Finset V // C ∈ edgeFamily G}
  have hpairs : ∀ C : Edge, ∃ u v : V, u ≠ v ∧ C.1 = {u,v} := by
    intro C
    exact card_eq_two.mp ((mem_edgeFamily G C.1).mp C.2).1
  choose u v huv hC using hpairs
  have hsum : k • graphicalZonotope G =
      ∑ C : Edge, segment ℝ (k • basisVector (u C)) (k • basisVector (v C)) := by
    have hs : graphicalZonotope G = ∑ C : Edge, coordinateSimplex C.1 := by
      exact (Finset.sum_coe_sort (edgeFamily G) coordinateSimplex).symm
    rw [hs,Finset.smul_sum]
    apply sum_congr rfl
    intro C hmem
    rw [hC C,coordinateSimplex_pair,smul_segment_eq]
  obtain ⟨hpq,l,c,hbound,hface⟩ := hex
  rw [hsum] at hbound hface
  obtain ⟨C,hmem,t,ht,hdir⟩ := exposed_edge_of_sum_segments (univ : Finset Edge)
    (fun C => k • basisVector (u C)) (fun C => k • basisVector (v C))
    hpq l c hbound hface
  have hadj : G.Adj (u C) (v C) := by
    have hh := C.2
    rw [hC C] at hh
    exact (pair_mem_edgeFamily G (huv C)).mp hh
  have he : q-p = (t*k) • (basisVector (v C)-basisVector (u C)) := by
    simpa only [← smul_sub,smul_smul] using hdir
  have htk : t*k ≠ 0 := by
    intro hz
    rw [hz,zero_smul,sub_eq_zero] at he
    exact hpq he.symm
  exact ⟨u C,v C,hadj,t*k,htk,he⟩

/-- A nonzero standard root cannot be parallel to a root supported on a
different unordered pair. -/
theorem adjacency_of_root_parallel (G : SimpleGraph V) {u v a b : V}
    (huv : u ≠ v) (hab : G.Adj a b) {c d : ℝ} (hc : c ≠ 0)
    (h : c • (basisVector u-basisVector v) = d • (basisVector a-basisVector b)) :
    G.Adj u v := by
  have hu : u = a ∨ u = b := by
    by_contra hn
    push_neg at hn
    have he := congrFun h u
    simp [basisVector,Pi.single_apply,huv,Ne.symm huv,hn.1,hn.2,
      Ne.symm hn.1,Ne.symm hn.2] at he
    exact hc he
  have hv : v = a ∨ v = b := by
    by_contra hn
    push_neg at hn
    have he := congrFun h v
    simp [basisVector,Pi.single_apply,huv,Ne.symm huv,hn.1,hn.2,
      Ne.symm hn.1,Ne.symm hn.2] at he
    exact hc he
  rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
  · exact False.elim (huv rfl)
  · exact hab
  · exact G.adj_symm hab
  · exact False.elim (huv rfl)

theorem graphical_zonotope_actualRootEdge (G : SimpleGraph V) (k : ℝ)
    {u v : V} (h : ActualRootEdge (k • graphicalZonotope G) u v) : G.Adj u v := by
  obtain ⟨huv,p,q,hex,c,hc,hpq⟩ := h
  obtain ⟨a,b,hab,d,hd,he⟩ := graphical_zonotope_exposed_edge G k hex
  exact adjacency_of_root_parallel G huv (G.adj_symm hab) hc (hpq.symm.trans he)

end Graphs

end GraphicalZonotopes
