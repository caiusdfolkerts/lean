module

public import Continuation.Fano.SegmentSimplexBundleTrianglePrimitivity

/-!
# The actual unimodular triangular face at the limiting parameter

When `a = d`, the upper end simplex has width one.  Fixing every fibre
coordinate except two at its upper bound gives a triangular extreme face.
The two negative coordinate vectors form a basis of the full integral
lattice in its real direction space.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace Unimodular.SegmentSimplexBundle

open SegmentSimplex
open scoped BigOperators Pointwise

def upperVertex (d : ℕ) (k : Option (Fin d)) : Lattice (d + 1) :=
  vertex d (d : ℤ) (true, k)

@[simp] theorem upperVertex_last (d : ℕ) (k : Option (Fin d)) :
    upperVertex d k (Fin.last d) = 1 := by simp [upperVertex]

@[simp] theorem upperVertex_castSucc (d : ℕ) (k : Option (Fin d)) (i : Fin d) :
    upperVertex d k i.castSucc = if k = some i then 0 else 1 := by
  by_cases h : k = some i <;> simp [upperVertex, vertex_castSucc, width, h]

@[simp] theorem embed_upperVertex_last (d : ℕ) (k : Option (Fin d)) :
    embed (upperVertex d k) (Fin.last d) = 1 := by simp [embed]

@[simp] theorem embed_upperVertex_castSucc (d : ℕ) (k : Option (Fin d))
    (i : Fin d) :
    embed (upperVertex d k) i.castSucc = if k = some i then 0 else 1 := by
  by_cases h : k = some i <;> simp [embed, h]

def upperTriangle (d : ℕ) (i j : Fin d) : Set (Ambient (d + 1)) :=
  {x | x ∈ Q d (d : ℤ) ∧ x (Fin.last d) = 1 ∧
    ∀ k : Fin d, k ≠ i → k ≠ j → x k.castSucc = 1}

theorem upperVertex_mem_upperTriangle (d : ℕ) (i j : Fin d)
    (k : Option (Fin d)) (hk : k = none ∨ k = some i ∨ k = some j) :
    embed (upperVertex d k) ∈ upperTriangle d i j := by
  refine ⟨vertex_mem_Q (Int.natCast_nonneg _) le_rfl _, by simp, ?_⟩
  intro l hli hlj
  rcases hk with rfl | rfl | rfl <;>
    simp [embed_upperVertex_castSucc, hli, hlj, Ne.symm hli, Ne.symm hlj]

theorem upperTriangle_convex (d : ℕ) (i j : Fin d) :
    Convex ℝ (upperTriangle d i j) := by
  intro x hx y hy s t hs ht hst
  refine ⟨Q_convex d (d : ℤ) hx.1 hy.1 hs ht hst, ?_, ?_⟩
  · change s * x (Fin.last d) + t * y (Fin.last d) = 1
    rw [hx.2.1, hy.2.1]
    simpa using hst
  · intro k hki hkj
    change s * x k.castSucc + t * y k.castSucc = 1
    rw [hx.2.2 k hki hkj, hy.2.2 k hki hkj]
    simpa using hst

private theorem coordinate_eq_one_of_open_combination
    {x y s t : ℝ} (hx : x ≤ 1) (hy : y ≤ 1) (hs : 0 < s)
    (ht : 0 < t) (hst : s + t = 1) (he : s * x + t * y = 1) : x = 1 := by
  have hm : 0 ≤ t * (1 - y) := mul_nonneg ht.le (sub_nonneg.mpr hy)
  have hge : 1 ≤ x := by
    by_contra h
    have hp : 0 < s * (1 - x) := mul_pos hs (sub_pos.mpr (lt_of_not_ge h))
    nlinarith
  exact le_antisymm hx hge

theorem upperTriangle_isExtreme (d : ℕ) (i j : Fin d) :
    IsExtreme ℝ (Q d (d : ℤ)) (upperTriangle d i j) := by
  refine ⟨fun _ hx => hx.1, ?_⟩
  intro x hx y hy z hz hseg
  rcases hseg with ⟨s, t, hs, ht, hst, he⟩
  refine ⟨hx, ?_, ?_⟩
  · apply coordinate_eq_one_of_open_combination hx.2.1 hy.2.1 hs ht hst
    have h := congrArg (fun w : Ambient (d + 1) => w (Fin.last d)) he
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hz.2.1] using h
  · intro k hki hkj
    apply coordinate_eq_one_of_open_combination (hx.2.2.1 k) (hy.2.2.1 k) hs ht hst
    have h := congrArg (fun w : Ambient (d + 1) => w k.castSucc) he
    simpa only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hz.2.2 k hki hkj] using h

theorem fibre_sum_of_except_two {d : ℕ} (i j : Fin d) (hij : i ≠ j)
    (x : Ambient (d + 1))
    (hx : ∀ k : Fin d, k ≠ i → k ≠ j → x k.castSucc = 1) :
    (∑ k : Fin d, x k.castSucc) = (d : ℝ) - 2 + x i.castSucc + x j.castSucc := by
  calc
    (∑ k : Fin d, x k.castSucc) =
        ∑ k : Fin d, (1 + (if k = i then x i.castSucc - 1 else 0) +
          (if k = j then x j.castSucc - 1 else 0)) := by
      apply Finset.sum_congr rfl
      intro k _
      by_cases hki : k = i
      · subst k
        simp [hij] <;> ring
      · by_cases hkj : k = j
        · subst k
          simp [Ne.symm hij] <;> ring
        · simp [hki, hkj, hx k hki hkj]
    _ = _ := by
      simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one, Finset.sum_ite_eq',
        Finset.mem_univ, if_true]
      ring

theorem upperTriangle_eq_hull (d : ℕ) (i j : Fin d) (hij : i ≠ j) :
    upperTriangle d i j = convexHull ℝ
      ({embed (upperVertex d none), embed (upperVertex d (some i)),
        embed (upperVertex d (some j))} : Set (Ambient (d + 1))) := by
  apply Set.Subset.antisymm
  · intro x hx
    have hsum := fibre_sum_of_except_two i j hij x hx.2.2
    have hlow : 1 ≤ x i.castSucc + x j.castSucc := by
      have h := hx.1.2.2.2
      rw [hsum, hx.2.1] at h
      norm_num only [Int.cast_natCast, mul_one] at h
      linarith
    let w : Fin 3 → ℝ :=
      ![x i.castSucc + x j.castSucc - 1, 1 - x i.castSucc, 1 - x j.castSucc]
    let v : Fin 3 → Ambient (d + 1) :=
      ![embed (upperVertex d none), embed (upperVertex d (some i)),
        embed (upperVertex d (some j))]
    have hw : ∀ k, 0 ≤ w k := by
      intro k
      fin_cases k
      · exact sub_nonneg.mpr hlow
      · exact sub_nonneg.mpr (hx.1.2.2.1 i)
      · exact sub_nonneg.mpr (hx.1.2.2.1 j)
    have hws : ∑ k, w k = 1 := by
      simp [w, Fin.sum_univ_succ] <;> ring
    apply mem_convexHull_of_exists_fintype w v hw hws
    · intro k
      fin_cases k <;> simp [v]
    · ext k
      refine Fin.lastCases ?_ (fun l => ?_) k
      · simp [w, v, Fin.sum_univ_succ, Pi.add_apply, Pi.smul_apply,
          smul_eq_mul, hx.2.1] <;> ring
      · by_cases hli : l = i
        · subst l
          simp [w, v, Fin.sum_univ_succ, Pi.add_apply, Pi.smul_apply,
            smul_eq_mul, hij, Ne.symm hij] <;> ring
        · by_cases hlj : l = j
          · subst l
            simp [w, v, Fin.sum_univ_succ, Pi.add_apply, Pi.smul_apply,
              smul_eq_mul, hij, Ne.symm hij] <;> ring
          · simp [w, v, Fin.sum_univ_succ, Pi.add_apply, Pi.smul_apply,
              smul_eq_mul, hli, hlj, Ne.symm hli, Ne.symm hlj,
              hx.2.2 l hli hlj] <;> ring
  · apply convexHull_min _ (upperTriangle_convex d i j)
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl
    · exact upperVertex_mem_upperTriangle d i j none (Or.inl rfl)
    · exact upperVertex_mem_upperTriangle d i j (some i) (Or.inr (Or.inl rfl))
    · exact upperVertex_mem_upperTriangle d i j (some j) (Or.inr (Or.inr rfl))

def twoCoordinatePlane (d : ℕ) (i j : Fin d) : Submodule ℝ (Ambient (d + 1)) where
  carrier := {x | x (Fin.last d) = 0 ∧
    ∀ k : Fin d, k ≠ i → k ≠ j → x k.castSucc = 0}
  zero_mem' := by simp
  add_mem' := by
    intro x y hx hy
    exact ⟨by simp [hx.1, hy.1], fun k hki hkj => by
      simp [hx.2 k hki hkj, hy.2 k hki hkj]⟩
  smul_mem' := by
    intro c x hx
    exact ⟨by simp [hx.1], fun k hki hkj => by simp [hx.2 k hki hkj]⟩

theorem upperTriangle_vectorSpan_le (d : ℕ) (i j : Fin d) :
    vectorSpan ℝ (upperTriangle d i j) ≤ twoCoordinatePlane d i j := by
  rw [vectorSpan_def]
  apply Submodule.span_le.mpr
  rintro _ ⟨x, hx, y, hy, rfl⟩
  constructor
  · change x (Fin.last d) - y (Fin.last d) = 0
    rw [hx.2.1, hy.2.1]
    ring
  · intro k hki hkj
    change x k.castSucc - y k.castSucc = 0
    rw [hx.2.2 k hki hkj, hy.2.2 k hki hkj]
    ring

def upperEdge (d : ℕ) (i : Fin d) : Lattice (d + 1) :=
  upperVertex d (some i) - upperVertex d none

@[simp] theorem upperEdge_last (d : ℕ) (i : Fin d) :
    upperEdge d i (Fin.last d) = 0 := by simp [upperEdge]

@[simp] theorem upperEdge_castSucc (d : ℕ) (i k : Fin d) :
    upperEdge d i k.castSucc = if k = i then -1 else 0 := by
  by_cases h : k = i
  · subst k
    simp [upperEdge]
  · simp [upperEdge, h, Ne.symm h]

theorem upperEdge_mem_vectorSpan_left (d : ℕ) (i j : Fin d) :
    embed (upperEdge d i) ∈ vectorSpan ℝ (upperTriangle d i j) := by
  have he : embed (upperEdge d i) =
      embed (upperVertex d (some i)) - embed (upperVertex d none) := by
    ext k
    simp [upperEdge, embed]
  rw [he]
  exact vsub_mem_vectorSpan ℝ
    (upperVertex_mem_upperTriangle d i j (some i) (Or.inr (Or.inl rfl)))
    (upperVertex_mem_upperTriangle d i j none (Or.inl rfl))

theorem upperEdge_mem_vectorSpan_right (d : ℕ) (i j : Fin d) :
    embed (upperEdge d j) ∈ vectorSpan ℝ (upperTriangle d i j) := by
  have he : embed (upperEdge d j) =
      embed (upperVertex d (some j)) - embed (upperVertex d none) := by
    ext k
    simp [upperEdge, embed]
  rw [he]
  exact vsub_mem_vectorSpan ℝ
    (upperVertex_mem_upperTriangle d i j (some j) (Or.inr (Or.inr rfl)))
    (upperVertex_mem_upperTriangle d i j none (Or.inl rfl))

theorem integral_upperTriangle_last (d : ℕ) (i j : Fin d)
    (x : integralSubspace (vectorSpan ℝ (upperTriangle d i j))) :
    x.val (Fin.last d) = 0 := by
  have h := (upperTriangle_vectorSpan_le d i j x.property).1
  change (x.val (Fin.last d) : ℝ) = 0 at h
  exact_mod_cast h

theorem integral_upperTriangle_other (d : ℕ) (i j : Fin d)
    (x : integralSubspace (vectorSpan ℝ (upperTriangle d i j)))
    (k : Fin d) (hki : k ≠ i) (hkj : k ≠ j) : x.val k.castSucc = 0 := by
  have h := (upperTriangle_vectorSpan_le d i j x.property).2 k hki hkj
  change (x.val k.castSucc : ℝ) = 0 at h
  exact_mod_cast h

def triangleLatticeEquiv (d : ℕ) (i j : Fin d) (hij : i ≠ j) :
    (Fin 2 → ℤ) ≃ₗ[ℤ] integralSubspace (vectorSpan ℝ (upperTriangle d i j)) where
  toFun x := x 0 • ⟨upperEdge d i, upperEdge_mem_vectorSpan_left d i j⟩ +
    x 1 • ⟨upperEdge d j, upperEdge_mem_vectorSpan_right d i j⟩
  invFun x := ![-x.val i.castSucc, -x.val j.castSucc]
  left_inv x := by
    funext k
    fin_cases k
    · change -((x 0 • upperEdge d i + x 1 • upperEdge d j) i.castSucc) = x 0
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hij, Ne.symm hij]
    · change -((x 0 • upperEdge d i + x 1 • upperEdge d j) j.castSucc) = x 1
      simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hij, Ne.symm hij]
  right_inv x := by
    apply Subtype.ext
    funext k
    change ((-x.val i.castSucc) • upperEdge d i +
      (-x.val j.castSucc) • upperEdge d j) k = x.val k
    refine Fin.lastCases ?_ (fun l => ?_) k
    · simp [Pi.add_apply, Pi.smul_apply, integral_upperTriangle_last d i j x]
    · by_cases hli : l = i
      · subst l
        simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hij, Ne.symm hij]
      · by_cases hlj : l = j
        · subst l
          simp [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hij, Ne.symm hij]
        · simp [Pi.add_apply, Pi.smul_apply, hli, hlj,
            integral_upperTriangle_other d i j x l hli hlj]
  map_add' x y := by
    simp only [Pi.add_apply, add_smul]
    abel
  map_smul' c x := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, smul_add, smul_smul]

def triangleBasis (d : ℕ) (i j : Fin d) (hij : i ≠ j) :
    Module.Basis (Fin 2) ℤ (integralSubspace (vectorSpan ℝ (upperTriangle d i j))) :=
  (Pi.basisFun ℤ (Fin 2)).map (triangleLatticeEquiv d i j hij)

theorem triangleBasis_zero (d : ℕ) (i j : Fin d) (hij : i ≠ j) :
    (triangleBasis d i j hij 0).val = upperEdge d i := by
  simp [triangleBasis, Module.Basis.map_apply, triangleLatticeEquiv,
    Pi.basisFun_apply, Pi.single_apply]

theorem triangleBasis_one (d : ℕ) (i j : Fin d) (hij : i ≠ j) :
    (triangleBasis d i j hij 1).val = upperEdge d j := by
  simp [triangleBasis, Module.Basis.map_apply, triangleLatticeEquiv,
    Pi.basisFun_apply, Pi.single_apply]

theorem upperTriangle_isUnimodular (d : ℕ) (i j : Fin d) (hij : i ≠ j) :
    IsUnimodularTriangle (upperTriangle d i j) := by
  have hd : 1 ≤ d := by have := i.is_lt; omega
  have hv (k : Option (Fin d))
      (hk : k = none ∨ k = some i ∨ k = some j) :
      embed (upperVertex d k) ∈ (upperTriangle d i j).extremePoints ℝ := by
    rw [(upperTriangle_isExtreme d i j).extremePoints_eq]
    refine ⟨upperVertex_mem_upperTriangle d i j k hk, ?_⟩
    rw [extremePoints_eq_vertexRange d (d : ℤ) hd (Int.natCast_nonneg _) le_rfl]
    exact ⟨upperVertex d k,
      Finset.mem_image.mpr ⟨(true, k), Finset.mem_univ _, rfl⟩, rfl⟩
  refine ⟨upperVertex d none, upperVertex d (some i), upperVertex d (some j),
    hv none (Or.inl rfl), hv (some i) (Or.inr (Or.inl rfl)),
    hv (some j) (Or.inr (Or.inr rfl)), upperTriangle_eq_hull d i j hij,
    triangleBasis d i j hij, triangleBasis_zero d i j hij, triangleBasis_one d i j hij⟩

theorem exists_unimodular_triangle_at_top (d : ℕ) (hd : 2 ≤ d) :
    ∃ E : Set (Ambient (d + 1)), IsExtreme ℝ (Q d (d : ℤ)) E ∧
      IsUnimodularTriangle E := by
  let i : Fin d := ⟨0, by omega⟩
  let j : Fin d := ⟨1, by omega⟩
  have hij : i ≠ j := by
    intro he
    have h := congrArg Fin.val he
    norm_num [i, j] at h
  exact ⟨upperTriangle d i j, upperTriangle_isExtreme d i j,
    upperTriangle_isUnimodular d i j hij⟩

end Unimodular.SegmentSimplexBundle

#print axioms Unimodular.SegmentSimplexBundle.upperTriangle_eq_hull
#print axioms Unimodular.SegmentSimplexBundle.triangleLatticeEquiv
#print axioms Unimodular.SegmentSimplexBundle.upperTriangle_isUnimodular
#print axioms Unimodular.SegmentSimplexBundle.exists_unimodular_triangle_at_top
