module

public import Continuation.Fano.SegmentSimplexBundle

/-! The displayed inequalities are exactly the convex hull of the two
integral end simplices.  The barycentric proof keeps all real points. -/

@[expose] public noncomputable section

set_option autoImplicit false

namespace Unimodular.SegmentSimplexBundle

open scoped BigOperators

@[simp] theorem embed_vertex_last (d : ℕ) (a : ℤ) (t : VertexIndex d) :
    embed (vertex d a t) (Fin.last d) = (height t.1 : ℝ) := by
  simp [embed]

@[simp] theorem embed_vertex_castSucc (d : ℕ) (a : ℤ) (t : VertexIndex d)
    (i : Fin d) :
    embed (vertex d a t) i.castSucc =
      1 - if t.2 = some i then (width d a t.1 : ℝ) else 0 := by
  simp [embed]

@[simp] theorem width_false_cast (d : ℕ) (a : ℤ) :
    (width d a false : ℝ) = (d : ℝ) + 1 + (a : ℝ) := by
  simp [width, height]

@[simp] theorem width_true_cast (d : ℕ) (a : ℤ) :
    (width d a true : ℝ) = (d : ℝ) + 1 - (a : ℝ) := by
  simp [width, height]

def fibreScale (d : ℕ) (a : ℤ) (x : Ambient (d + 1)) : ℝ :=
  (d : ℝ) + 1 - (a : ℝ) * x (Fin.last d)

theorem fibreScale_pos {d : ℕ} {a : ℤ} (ha : 0 ≤ a) (had : a ≤ d)
    {x : Ambient (d + 1)} (hx : x ∈ Q d a) : 0 < fibreScale d a x := by
  have haR : (0 : ℝ) ≤ a := by exact_mod_cast ha
  have hadR : (a : ℝ) ≤ d := by exact_mod_cast had
  have hm := mul_le_mul_of_nonneg_left hx.2.1 haR
  dsimp [fibreScale]
  linarith

def fibreWeights (d : ℕ) (a : ℤ) (x : Ambient (d + 1)) : Option (Fin d) → ℝ
  | none => 1 - ∑ i : Fin d, (1 - x i.castSucc) / fibreScale d a x
  | some i => (1 - x i.castSucc) / fibreScale d a x

theorem fibreWeights_sum (d : ℕ) (a : ℤ) (x : Ambient (d + 1)) :
    ∑ k : Option (Fin d), fibreWeights d a x k = 1 := by
  simp [Fintype.sum_option, fibreWeights]

theorem fibreWeights_nonneg {d : ℕ} {a : ℤ} (ha : 0 ≤ a) (had : a ≤ d)
    {x : Ambient (d + 1)} (hx : x ∈ Q d a) (k : Option (Fin d)) :
    0 ≤ fibreWeights d a x k := by
  have hc := fibreScale_pos ha had hx
  cases k with
  | some i =>
      exact div_nonneg (sub_nonneg.mpr (hx.2.2.1 i)) hc.le
  | none =>
      change 0 ≤ 1 - ∑ i : Fin d, (1 - x i.castSucc) / fibreScale d a x
      apply sub_nonneg.mpr
      rw [← Finset.sum_div]
      apply (div_le_one hc).mpr
      have hs := hx.2.2.2
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
        Fintype.card_fin, nsmul_eq_mul, mul_one]
      dsimp [fibreScale]
      linarith

def endPoint (d : ℕ) (a : ℤ) (x : Ambient (d + 1)) (b : Bool) :
    Ambient (d + 1) :=
  ∑ k : Option (Fin d), fibreWeights d a x k • embed (vertex d a (b, k))

theorem endPoint_last (d : ℕ) (a : ℤ) (x : Ambient (d + 1)) (b : Bool) :
    endPoint d a x b (Fin.last d) = (height b : ℝ) := by
  simp only [endPoint, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    embed_vertex_last]
  rw [← Finset.sum_mul, fibreWeights_sum, one_mul]

theorem endPoint_castSucc (d : ℕ) (a : ℤ) (x : Ambient (d + 1))
    (b : Bool) (i : Fin d) :
    endPoint d a x b i.castSucc =
      1 - fibreWeights d a x (some i) * (width d a b : ℝ) := by
  simp only [endPoint, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    embed_vertex_castSucc, mul_sub, mul_one, mul_ite, mul_zero,
    Finset.sum_sub_distrib]
  rw [fibreWeights_sum]
  simp

theorem endPoint_mem_hull {d : ℕ} {a : ℤ} (ha : 0 ≤ a) (had : a ≤ d)
    {x : Ambient (d + 1)} (hx : x ∈ Q d a) (b : Bool) :
    endPoint d a x b ∈ convexHull ℝ (embed '' (vertices d a : Set (Lattice (d + 1)))) := by
  apply mem_convexHull_of_exists_fintype (fibreWeights d a x)
    (fun k => embed (vertex d a (b, k)))
    (fibreWeights_nonneg ha had hx) (fibreWeights_sum d a x)
  · intro k
    exact ⟨vertex d a (b, k), Finset.mem_image.mpr ⟨(b, k), Finset.mem_univ _, rfl⟩, rfl⟩
  · rfl

theorem hull_eq_Q {d : ℕ} {a : ℤ} (ha : 0 ≤ a) (had : a ≤ d) :
    convexHull ℝ (embed '' (vertices d a : Set (Lattice (d + 1)))) = Q d a := by
  apply Set.Subset.antisymm
  · apply convexHull_min _ (Q_convex d a)
    rintro x ⟨v, hv, rfl⟩
    obtain ⟨t, _, rfl⟩ := Finset.mem_image.mp hv
    exact vertex_mem_Q ha had t
  · intro x hx
    have hc := fibreScale_pos ha had hx
    let t : ℝ := (x (Fin.last d) + 1) / 2
    have ht0 : 0 ≤ t := by dsimp [t]; linarith [hx.1]
    have ht1 : t ≤ 1 := by dsimp [t]; linarith [hx.2.1]
    have he : (1 - t) • endPoint d a x false + t • endPoint d a x true = x := by
      ext j
      refine Fin.lastCases ?_ (fun i => ?_) j
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, endPoint_last,
          height_false, height_true, Int.cast_neg, Int.cast_one]
        dsimp [t]
        ring
      · simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, endPoint_castSucc,
          width_false_cast, width_true_cast, fibreWeights]
        dsimp [t]
        field_simp [hc.ne']
        dsimp [fibreScale]
        ring
    rw [← he]
    exact (convex_convexHull ℝ _) (endPoint_mem_hull ha had hx false)
      (endPoint_mem_hull ha had hx true) (sub_nonneg.mpr ht1) ht0
      (sub_add_cancel _ _)

end Unimodular.SegmentSimplexBundle

#print axioms Unimodular.SegmentSimplexBundle.hull_eq_Q
