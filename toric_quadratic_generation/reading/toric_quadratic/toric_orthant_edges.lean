module

public import PaperVerification.ToricNormalFan
public import Mathlib.Data.Finset.Max

@[expose] public section

/-!
# Genuine edges at a supporting lattice orthant

Each coordinate ray is cut out as an actual face. A positive point on that
ray and compact finite generation give its other endpoint. Integrality of
that endpoint proves that its distance in a primitive basis direction is
a positive integer. Smoothness is not an input to these statements.
-/

noncomputable section

namespace PaperVerification.ToricGeometry.LatticePolytope

open Set
open scoped BigOperators Classical
open PaperVerification.ToricExchange PaperVerification.ToricVertexCone

variable {n : ℕ} (P : LatticePolytope n)

def coordinateRayFace (v : Ambient n) (b : Module.Basis (Fin n) ℝ (Ambient n))
    (i : Fin n) : Set (Ambient n) :=
  {x ∈ P.carrier | ∀ j, j ≠ i → b.repr (x - v) j = 0}

theorem coordinateRayFace_convex (v : Ambient n)
    (b : Module.Basis (Fin n) ℝ (Ambient n)) (i : Fin n) :
    Convex ℝ (P.coordinateRayFace v b i) := by
  intro x hx y hy r s hr hs hrs
  refine ⟨(convex_convexHull ℝ _) hx.1 hy.1 hr hs hrs, ?_⟩
  intro j hji
  have hxj := hx.2 j hji
  have hyj := hy.2 j hji
  simp only [map_sub, Finsupp.sub_apply] at hxj hyj
  simp only [map_sub, map_add, map_smul, Finsupp.sub_apply,
    Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul]
  rw [sub_eq_zero.mp hxj, sub_eq_zero.mp hyj, ← add_mul, hrs, one_mul, sub_self]

theorem coordinateRayFace_isExtreme (v : Ambient n)
    (b : Module.Basis (Fin n) ℝ (Ambient n))
    (horthant : ∀ x ∈ P.carrier, ∀ j, 0 ≤ b.repr (x - v) j) (i : Fin n) :
    IsExtreme ℝ P.carrier (P.coordinateRayFace v b i) := by
  refine ⟨fun _ hx => hx.1, ?_⟩
  intro x hx y hy z hz hseg
  obtain ⟨r, s, hr, hs, hrs, he⟩ := hseg
  refine ⟨hx, ?_⟩
  intro j hji
  have hxj := horthant x hx j
  have hyj := horthant y hy j
  have hzj := hz.2 j hji
  have he' := congrArg (fun t => b.repr t j) he
  simp only [map_sub, Finsupp.sub_apply] at hxj hyj hzj ⊢
  simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
    smul_eq_mul] at he'
  have hbalance : r * (b.repr x j - b.repr v j) +
      s * (b.repr y j - b.repr v j) = 0 := by
    calc
      r * (b.repr x j - b.repr v j) + s * (b.repr y j - b.repr v j) =
          (r * b.repr x j + s * b.repr y j) - (r + s) * b.repr v j := by ring
      _ = b.repr z j - b.repr v j := by rw [he', hrs, one_mul]
      _ = 0 := hzj
  have hrx := mul_nonneg hr.le hxj
  have hsy := mul_nonneg hs.le hyj
  have hzero : r * (b.repr x j - b.repr v j) = 0 := by
    linarith only [hbalance, hrx, hsy]
  exact (mul_eq_zero.mp hzero).resolve_left hr.ne'

theorem coordinateRayFace_point_eq (v : Ambient n)
    (b : Module.Basis (Fin n) ℝ (Ambient n)) (i : Fin n)
    {x : Ambient n} (hx : x ∈ P.coordinateRayFace v b i) :
    x = v + (b.repr (x - v) i) • b i := by
  apply b.ext_elem
  intro j
  by_cases hji : j = i
  · subst j
    simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
      Module.Basis.repr_self_apply, if_pos rfl, ite_true, smul_eq_mul, mul_one,
      map_sub, Finsupp.sub_apply]
    ring
  · have hz := hx.2 j hji
    simp only [map_sub, Finsupp.sub_apply] at hz
    simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
      Module.Basis.repr_self_apply, if_neg (Ne.symm hji), smul_eq_mul,
      mul_zero, add_zero]
    exact sub_eq_zero.mp hz

/-- Every primitive coordinate ray with a positive feasible point is an
actual edge of the given lattice polytope, with positive integral length. -/
theorem coordinateRayFace_eq_integral_edge
    (vZ : Lattice n) (hvZ : vZ ∈ P.generators)
    (b : Module.Basis (Fin n) ℤ (Lattice n))
    (horthant : ∀ x ∈ P.carrier, ∀ j,
      0 ≤ (integralBasisReal b).repr (x - embed n vZ) j)
    (i : Fin n)
    (hpositive : ∃ ε : ℝ, 0 < ε ∧
      embed n vZ + ε • integralBasisReal b i ∈ P.carrier) :
    ∃ k : ℕ, 0 < k ∧
      P.IsEdge (embed n vZ) (embed n (vZ + (k : ℤ) • b i)) ∧
      P.coordinateRayFace (embed n vZ) (integralBasisReal b) i =
        segment ℝ (embed n vZ) (embed n (vZ + (k : ℤ) • b i)) := by
  let v := embed n vZ
  let bR := integralBasisReal b
  let F := P.coordinateRayFace v bR i
  let S := P.generators.image (embed n)
  let T := faceGenerators S F
  let f : Ambient n →ₗ[ℝ] ℝ := bR.coord i
  have hcarrier : P.carrier = convexHull ℝ (S : Set (Ambient n)) := by
    simp only [carrier, S, Finset.coe_image]
  have hFconv : Convex ℝ F := P.coordinateRayFace_convex v bR i
  have hFext : IsExtreme ℝ P.carrier F :=
    P.coordinateRayFace_isExtreme v bR horthant i
  have hFhull : F = convexHull ℝ (T : Set (Ambient n)) := by
    apply convex_face_eq_convexHull_filter S F hFconv
    simpa only [← hcarrier] using hFext
  have hvP : v ∈ P.carrier := subset_convexHull ℝ _ ⟨vZ, hvZ, rfl⟩
  have hvF : v ∈ F := ⟨hvP, by intro j hji; simp⟩
  have hvT : v ∈ T := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_image.mpr ⟨vZ, hvZ, rfl⟩, hvF⟩
  obtain ⟨w, hwT, hmax⟩ := T.exists_max_image f ⟨v, hvT⟩
  have hwS : w ∈ S := (Finset.mem_filter.mp hwT).1
  have hwF : w ∈ F := (Finset.mem_filter.mp hwT).2
  have hbound (x : Ambient n) (hx : x ∈ F) : f x ≤ f w := by
    have hlow := linear_lower_bound_hull T (-f) (-f w)
      (fun z hz => neg_le_neg (hmax z hz)) x (hFhull ▸ hx)
    simpa only [LinearMap.neg_apply, neg_le_neg_iff] using hlow
  let «λ» := f (w - v)
  obtain ⟨ε, hε, hεP⟩ := hpositive
  have hεF : v + ε • bR i ∈ F := by
    refine ⟨hεP, ?_⟩
    intro j hji
    simp [bR, Module.Basis.repr_self_apply, hji, Ne.symm hji]
  have «hλ» : 0 < «λ» := by
    have hle := hbound _ hεF
    have he : f (v + ε • bR i) = f v + ε := by
      simp [f, Module.Basis.coord_apply]
    rw [he] at hle
    dsimp [«λ»]
    rw [map_sub]
    linarith
  have hwline : w = v + «λ» • bR i :=
    P.coordinateRayFace_point_eq v bR i hwF
  have hvw : v ≠ w := by
    intro he
    have hz : «λ» = 0 := by simp [«λ», ← he]
    linarith
  have hFsegment : F = segment ℝ v w := by
    apply Set.Subset.antisymm
    · intro x hx
      let μ := bR.repr (x - v) i
      have hμ0 : 0 ≤ μ := horthant x hx.1 i
      have «hμλ» : μ ≤ «λ» := by
        have hb := hbound x hx
        change f (x - v) ≤ f (w - v)
        simpa only [map_sub, sub_le_sub_iff_right] using hb
      have ht : μ / «λ» ∈ Icc (0 : ℝ) 1 :=
        ⟨div_nonneg hμ0 «hλ».le, (div_le_one «hλ»).mpr «hμλ»⟩
      have hline : AffineMap.lineMap v w (μ / «λ») = x := by
        rw [AffineMap.lineMap_apply_module', hwline, add_sub_cancel_left,
          smul_smul, div_mul_cancel₀ _ «hλ».ne']
        simpa only [add_comm] using (P.coordinateRayFace_point_eq v bR i hx).symm
      simpa only [hline] using lineMap_mem_segment ℝ v w ht
    · exact hFconv.segment_subset hvF hwF
  obtain ⟨wZ, hwZ, hew⟩ := Finset.mem_image.mp hwS
  let z : ℤ := b.repr (wZ - vZ) i
  have «hλz» : «λ» = (z : ℝ) := by
    change (integralBasisReal b).repr (w - embed n vZ) i = _
    rw [← hew, ← map_sub, integralBasisReal_repr]
  have hz : 0 < z := by exact_mod_cast («hλz» ▸ «hλ»)
  let k : ℕ := z.toNat
  have hkZ : (k : ℤ) = z := Int.toNat_of_nonneg hz.le
  have hk : 0 < k := by exact_mod_cast (hkZ.symm ▸ hz)
  have hwendpoint : w = embed n (vZ + (k : ℤ) • b i) := by
    rw [hwline, «hλz», ← hkZ, map_add, embed_int_smul, integralBasisReal_apply]
  refine ⟨k, hk, ?_, ?_⟩
  · refine ⟨?_, ?_⟩
    · simpa only [← hwendpoint] using hvw
    · simpa only [hFsegment, hwendpoint] using hFext
  · simpa only [hwendpoint] using hFsegment

end PaperVerification.ToricGeometry.LatticePolytope
