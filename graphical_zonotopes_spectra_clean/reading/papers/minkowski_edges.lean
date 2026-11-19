module
public import Papers.FiniteAvoidance
public import Papers.FiniteConvexGeometry
public import Mathlib.Analysis.Normed.Group.Submodule
public import Mathlib.Analysis.Normed.Operator.Bilinear
public import Mathlib.Analysis.Normed.Operator.NormedSpace
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Restrict
public import Mathlib.Topology.Algebra.Module.FiniteDimension

@[expose] public section

/-!
# Exposed edges of Minkowski summands

All sets in the theorem are actual finite convex hulls. The exposing
functional is perturbed in the annihilator of the given edge direction.
This preserves that edge and eliminates all additional independent
directions among the minimizing generators of the sum.
-/

noncomputable section
namespace Papers.Geometry
open Set
open scoped Pointwise

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def ExposesSegment (Q : Set E) (l : E →L[ℝ] ℝ) (a : ℝ) (p q : E) : Prop :=
  (∀ x ∈ Q, a ≤ l x) ∧ {x ∈ Q | l x = a} = segment ℝ p q

theorem ExposesSegment.left_mem {Q : Set E} {l : E →L[ℝ] ℝ} {a : ℝ} {p q : E}
    (h : ExposesSegment Q l a p q) : p ∈ Q ∧ l p = a := by
  change p ∈ {x ∈ Q | l x = a}
  rw [h.2]
  exact left_mem_segment ℝ p q

theorem ExposesSegment.right_mem {Q : Set E} {l : E →L[ℝ] ℝ} {a : ℝ} {p q : E}
    (h : ExposesSegment Q l a p q) : q ∈ Q ∧ l q = a := by
  change q ∈ {x ∈ Q | l x = a}
  rw [h.2]
  exact right_mem_segment ℝ p q

theorem minimizers_eq_hull (s : Finset E) (l : E →L[ℝ] ℝ) (a : ℝ)
    (hbound : ∀ v ∈ s, a ≤ l v) :
    {x ∈ convexHull ℝ (s : Set E) | l x = a} =
      convexHull ℝ {v ∈ (s : Set E) | l v = a} := by
  have hglobal := linear_lower_bound_on_convexHull (s : Set E) l a hbound
  apply Set.Subset.antisymm
  · rintro x ⟨hx, hxa⟩
    have h := mem_hull_of_minimizers s l hx (by simpa [hxa] using hglobal)
    simpa [hxa] using h
  · intro x hx
    refine ⟨convexHull_mono (by intro y hy; exact hy.1) hx, ?_⟩
    apply le_antisymm
    · have h := linear_lower_bound_on_convexHull
        {v ∈ (s : Set E) | l v = a} (-l) (-a)
        (by intro v hv; simp [hv.2]) x hx
      simpa only [ContinuousLinearMap.neg_apply, neg_le_neg_iff] using h
    · exact linear_lower_bound_on_convexHull
        {v ∈ (s : Set E) | l v = a} l a (by intro v hv; exact hv.2.ge) x hx

theorem constant_on_segment (l : E →L[ℝ] ℝ) {p q : E} (heq : l p = l q)
    {x : E} (hx : x ∈ segment ℝ p q) : l x = l p := by
  obtain ⟨a, b, _, _, hab, rfl⟩ := hx
  simp only [map_add, map_smul, smul_eq_mul, ← heq, ← add_mul, hab, one_mul]

section Perturbation

variable [FiniteDimensional ℝ E]

/-- Preserve an exposed segment of one finite hull while separating every
pair of generators of another hull whose difference is not its direction. -/
theorem perturb_exposing_segment (s t : Finset E) {p q : E}
    (l₀ : E →L[ℝ] ℝ) (a : ℝ)
    (hex : ExposesSegment (convexHull ℝ (s : Set E)) l₀ a p q) :
    ∃ l : E →L[ℝ] ℝ,
      ExposesSegment (convexHull ℝ (s : Set E)) l (l p) p q ∧
      ∀ x ∈ t, ∀ y ∈ t,
        x - y ∉ Submodule.span ℝ {q - p} → l x ≠ l y := by
  classical
  let δ := q - p
  let A : Submodule ℝ (E →L[ℝ] ℝ) :=
    (ContinuousLinearMap.apply ℝ ℝ δ).ker
  have hp := hex.left_mem
  have hq := hex.right_mem
  have hl₀ : l₀ ∈ A := by
    change l₀ (q - p) = 0
    rw [map_sub, hp.2, hq.2, sub_self]
  let I := {v : s // (v : E) ∉ segment ℝ p q}
  let U : Set A := {l | ∀ v : I, l.val p < l.val v.val.val}
  have hopen : IsOpen U := by
    have hUeq : U = ⋂ v : I, {l : A | l.val p < l.val v.val.val} := by
      ext l
      simp only [U, Set.mem_setOf_eq, Set.mem_iInter]
    rw [hUeq]
    apply isOpen_iInter_of_finite
    intro v
    exact isOpen_lt
      ((ContinuousLinearMap.apply ℝ ℝ p).continuous.comp continuous_subtype_val)
      ((ContinuousLinearMap.apply ℝ ℝ v.val.val).continuous.comp continuous_subtype_val)
  have hU : U.Nonempty := by
    refine ⟨⟨l₀, hl₀⟩, ?_⟩
    intro v
    have hv := hex.1 v.val.val (subset_convexHull ℝ _ v.val.property)
    change l₀ p < l₀ v.val.val
    rw [hp.2]
    apply lt_of_le_of_ne hv
    intro heq
    apply v.property
    exact hex.2.subset ⟨subset_convexHull ℝ _ v.val.property, heq.symm⟩
  let J := {z : t × t // (z.1 : E) - z.2 ∉ Submodule.span ℝ {δ}}
  let forms : J → A →L[ℝ] ℝ := fun z =>
    (ContinuousLinearMap.apply ℝ ℝ ((z.val.1 : E) - z.val.2)).comp A.subtypeL
  have hforms : ∀ z : J, ∃ l : A, forms z l ≠ 0 := by
    intro z
    obtain ⟨g, hgz, hgA⟩ := Submodule.exists_le_ker_of_notMem z.property
    let gc : E →L[ℝ] ℝ := g.toContinuousLinearMap
    have hgc : gc ∈ A := by
      change g δ = 0
      exact hgA (Submodule.subset_span (Set.mem_singleton δ))
    exact ⟨⟨gc, hgc⟩, hgz⟩
  obtain ⟨l, hlU, hlavoid⟩ := exists_in_open_forall_ne_zero forms hforms hopen hU
  have hlpq : l.val p = l.val q := by
    have h : (l : E →L[ℝ] ℝ) (q - p) = 0 := l.property
    rw [map_sub, sub_eq_zero] at h
    exact h.symm
  have hlgen : ∀ v ∈ s, l.val p ≤ l.val v := by
    intro v hv
    by_cases hvs : v ∈ segment ℝ p q
    · exact (constant_on_segment l.val hlpq hvs).ge
    · exact (hlU ⟨⟨v, hv⟩, hvs⟩).le
  have hlbound := linear_lower_bound_on_convexHull (s : Set E) l.val (l.val p) hlgen
  refine ⟨l.val, ⟨hlbound, ?_⟩, ?_⟩
  · rw [minimizers_eq_hull s l.val (l.val p) hlgen]
    apply Set.Subset.antisymm
    · apply convexHull_min _ (convex_segment p q)
      rintro v ⟨hv, hveq⟩
      by_contra hvs
      exact (ne_of_lt (hlU ⟨⟨v, hv⟩, hvs⟩)) hveq.symm
    · intro v hv
      have hbody : v ∈ convexHull ℝ (s : Set E) := by
        have h := hv
        rw [← hex.2] at h
        exact h.1
      have heq : l.val v = l.val p := constant_on_segment l.val hlpq hv
      rw [← minimizers_eq_hull s l.val (l.val p) hlgen]
      exact ⟨hbody, heq⟩
  · intro x hx y hy hxy heq
    let z : J := ⟨(⟨x, hx⟩, ⟨y, hy⟩), hxy⟩
    apply hlavoid z
    change (l : E →L[ℝ] ℝ) (x - y) = 0
    rw [map_sub, heq, sub_self]

end Perturbation

/-- Every nondegenerate exposed edge of a finite-hull Minkowski summand has
the direction of a nondegenerate exposed edge of the sum. The other summand
is arbitrary: its compactness or a prescribed vertex representation is not
assumed. -/
theorem minkowski_summand_exposed_edge_direction [FiniteDimensional ℝ E]
    (s t : Finset E) (ht : t.Nonempty) (R : Set E)
    (hsum : convexHull ℝ (t : Set E) = convexHull ℝ (s : Set E) + R)
    {p q : E} (hpq : p ≠ q) (l₀ : E →L[ℝ] ℝ) (a : ℝ)
    (hex : ExposesSegment (convexHull ℝ (s : Set E)) l₀ a p q) :
    ∃ x y : E, x ≠ y ∧
      (∃ l : E →L[ℝ] ℝ, ∃ b : ℝ,
        ExposesSegment (convexHull ℝ (t : Set E)) l b x y) ∧
      ∃ c : ℝ, c ≠ 0 ∧ y - x = c • (q - p) := by
  classical
  obtain ⟨l, hlex, hlavoid⟩ := perturb_exposing_segment s t l₀ a hex
  have hp := hlex.left_mem
  have hq := hlex.right_mem
  obtain ⟨w, hw, hwmin⟩ := t.exists_min_image l ht
  have hmin := linear_lower_bound_on_convexHull (t : Set E) l (l w) hwmin
  have hwbody : w ∈ convexHull ℝ (s : Set E) + R := by
    rw [← hsum]
    exact subset_convexHull ℝ _ hw
  obtain ⟨u, hu, r, hr, hur⟩ := Set.mem_add.mp hwbody
  have hprbody : p + r ∈ convexHull ℝ (t : Set E) := by
    rw [hsum]
    exact Set.mem_add.mpr ⟨p, hp.1, r, hr, rfl⟩
  have hqrbody : q + r ∈ convexHull ℝ (t : Set E) := by
    rw [hsum]
    exact Set.mem_add.mpr ⟨q, hq.1, r, hr, rfl⟩
  have hurval : l w = l u + l r := by rw [← hur, map_add]
  have huval : l u = l p := by
    have h₁ := hlex.1 u hu
    have h₂ := hmin (p + r) hprbody
    rw [map_add, hurval] at h₂
    linarith
  have hprval : l (p + r) = l w := by rw [map_add, hurval, huval]
  have hqrval : l (q + r) = l w := by rw [map_add, hq.2, hurval, huval]
  let sf : Finset E := t.filter (fun z => l z = l w)
  have hsf : sf.Nonempty := ⟨w, Finset.mem_filter.mpr ⟨hw, rfl⟩⟩
  have hface : {z ∈ convexHull ℝ (t : Set E) | l z = l w} =
      convexHull ℝ (sf : Set E) := by
    rw [minimizers_eq_hull t l (l w) hwmin]
    congr 1
    ext z
    simp [sf]
  have hparallel : ∀ x ∈ sf, ∀ y ∈ sf,
      x - y ∈ Submodule.span ℝ {q - p} := by
    intro x hx y hy
    have hx' := Finset.mem_filter.mp hx
    have hy' := Finset.mem_filter.mp hy
    by_contra hxy
    exact hlavoid x hx'.1 y hy'.1 hxy (hx'.2.trans hy'.2.symm)
  have hδ : q - p ≠ 0 := sub_ne_zero.mpr (Ne.symm hpq)
  obtain ⟨x, hx, y, hy, hsegment⟩ :=
    finite_hull_parallel_eq_segment sf hsf (q - p) hδ hparallel
  have hpr : p + r ∈ segment ℝ x y := by
    rw [← hsegment, ← hface]
    exact ⟨hprbody, hprval⟩
  have hqr : q + r ∈ segment ℝ x y := by
    rw [← hsegment, ← hface]
    exact ⟨hqrbody, hqrval⟩
  have hxy : x ≠ y := by
    intro heq
    have hp' : p + r = y := by simpa [heq] using hpr
    have hq' : q + r = y := by simpa [heq] using hqr
    exact hpq (add_right_cancel (hp'.trans hq'.symm))
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (hparallel y hy x hx)
  refine ⟨x, y, hxy, ⟨l, l w, hmin, hface.trans hsegment⟩, c, ?_, hc.symm⟩
  intro hc0
  have heq : y = x := by
    rw [hc0, zero_smul, eq_comm, sub_eq_zero] at hc
    exact hc
  exact hxy heq.symm

end Papers.Geometry
