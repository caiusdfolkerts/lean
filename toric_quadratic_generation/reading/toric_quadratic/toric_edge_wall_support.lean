module

public import PaperVerification.ToricNormalBasisEdges
public import PaperVerification.ToricContractibleWalls
public import Mathlib.Tactic.Abel

@[expose] public section

/-!
# The genuine adjacent normal cone along a primitive edge

A supporting full normal basis determines the actual primitive edge basis.
At the other endpoint of one of those edges, all wall normals remain active.
The uniqueness of the opposite fan ray then identifies the remaining active
normal. This supplies the geometric part of the edge-length/degree identity.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

theorem pairing_integral_dual_basis {n : ℕ}
    (d : Module.Basis (Fin n) ℤ (Lattice n)) (u : Lattice n) (j : Fin n) :
    (dotProductEquiv ℝ (Fin n) (embed n u))
        (integralBasisReal (integralDualBasis d) j) = (d.repr u j : ℝ) := by
  have h := integralDualBasis_real_pairing d j (embed n u)
  rw [integralBasisReal_repr] at h
  rw [integralBasisReal_apply]
  change (∑ k, embed n u k * embed n (integralDualBasis d j) k) = (d.repr u j : ℝ)
  simpa only [integralBasisReal_apply, mul_comm] using h

namespace LatticePolytope

variable {n : ℕ} (P : LatticePolytope n)

/-- The negative-side wall ray in the actual normal fan supports the opposite
endpoint of the corresponding genuine basis edge. No wall/curve dictionary is
assumed in this statement. -/
theorem opposite_wall_normal_at_edge_endpoint
    (hP : P.Smooth) («Σ» : SmoothCompleteFan n)
    (hfan : «Σ».realCones = P.normalFan)
    (v : Lattice n) (d : Module.Basis (Fin n) ℤ (Lattice n))
    (hU : Finset.univ.image d ∈ «Σ».cones)
    (hcone : P.normalCone (embed n v) =
      (latticeRayCone (Finset.univ.image d) : Set (Ambient n)))
    (j : Fin n) (k : ℕ) (hk : 0 < k)
    (hedge : P.IsEdge (embed n v)
      (embed n (v + (k : ℤ) • integralDualBasis d j)))
    (e : Lattice n)
    (hecone : insert e ((Finset.univ.erase j).image d) ∈ «Σ».cones)
    (hecoord : d.repr e j < 0) :
    embed n e ∈ P.normalCone (embed n (v + (k : ℤ) • integralDualBasis d j)) := by
  let y := embed n (v + (k : ℤ) • integralDualBasis d j)
  let W := (Finset.univ.erase j).image d
  let f (u : Lattice n) : Ambient n →ₗ[ℝ] ℝ :=
    dotProductEquiv ℝ (Fin n) (embed n u)
  have hyvertex : y ∈ P.carrier.extremePoints ℝ := (P.edge_endpoints_extreme hedge).2
  have hv : embed n v ∈ P.carrier := (P.edge_endpoints_extreme hedge).1.1
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have hdisp (u : Lattice n) :
      f u (y - embed n v) = (k : ℝ) * (d.repr u j : ℝ) := by
    rw [show y - embed n v = (k : ℝ) •
      integralBasisReal (integralDualBasis d) j by
        simp only [y, map_add, embed_int_smul, Int.cast_natCast,
          integralBasisReal_apply, add_sub_cancel_left]]
    rw [map_smul, smul_eq_mul]
    congr 1
    exact pairing_integral_dual_basis d u j
  have hnormalV : P.normalCone y ∈ «Σ».realCones := by
    rw [hfan]
    exact ⟨y, hyvertex.1, rfl⟩
  obtain ⟨V, hV, hVe⟩ := hnormalV
  obtain ⟨c, hc⟩ := P.smooth_vertex_normalCone_basis hP y hyvertex
  have hVcard : V.card = n := by
    apply «Σ».card_eq_dim_of_basis_cone_le hV c
    have he : latticeRayCone (Finset.univ.image c) = latticeRayCone V :=
      SetLike.coe_injective (hc.symm.trans hVe)
    exact he.le
  have hW : W ⊆ V := by
    intro u hu
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hu
    have hij : i ≠ j := (Finset.mem_erase.mp hi).1
    have hdiU : d i ∈ Finset.univ.image d :=
      Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
    have hdi : embed n (d i) ∈ P.normalCone (embed n v) := by
      rw [hcone]
      exact latticeRayCone_generator _ hdiU
    have hdiy : embed n (d i) ∈ P.normalCone y := by
      intro x hx
      change 0 ≤ f (d i) (x - y)
      rw [show x - y = (x - embed n v) - (y - embed n v) by abel, map_sub, hdisp]
      have hh := hdi x hx
      change 0 ≤ f (d i) (x - embed n v) at hh
      simpa only [Module.Basis.repr_self_apply, if_neg hij, Int.cast_zero,
        mul_zero, sub_zero] using hh
    apply («Σ».ray_mem_cone_iff hV («Σ».ray_mem_of_mem_cone hU hdiU)).mp
    change embed n (d i) ∈ (latticeRayCone V : Set (Ambient n))
    simpa only [hVe] using hdiy
  have hnonpos (u : Lattice n) (hu : u ∈ V) : d.repr u j ≤ 0 := by
    have hnormal : embed n u ∈ P.normalCone y := by
      rw [hVe]
      exact latticeRayCone_generator V hu
    have hh := hnormal (embed n v) hv
    change 0 ≤ f u (embed n v - y) at hh
    rw [show embed n v - y = -(y - embed n v) by abel, map_neg, hdisp] at hh
    have hR : (d.repr u j : ℝ) ≤ 0 := by nlinarith
    exact_mod_cast hR
  obtain ⟨cV, hcV⟩ := «Σ».full_cone_basis hV hVcard
  have hex : ∃ i : Fin n, d.repr (cV i) j ≠ 0 := by
    by_contra hn
    have hz : ∀ i : Fin n, d.repr (cV i) j = 0 := by simpa only [not_exists, not_not] using hn
    have hh := congrArg (fun x => d.repr x j) (cV.sum_repr (d j))
    simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
      hz, smul_eq_mul, mul_zero, Finset.sum_const_zero,
      Module.Basis.repr_self_apply, if_pos rfl] at hh
    norm_num at hh
  obtain ⟨i, hi⟩ := hex
  let z := cV i
  have hzV : z ∈ V := hcV.symm ▸ Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have hzneg : d.repr z j < 0 := lt_of_le_of_ne (hnonpos z hzV) hi
  have hzW : z ∉ W := by
    intro hz
    obtain ⟨i', hi', he⟩ := Finset.mem_image.mp hz
    have hi'j := (Finset.mem_erase.mp hi').1
    rw [← he, Module.Basis.repr_self_apply, if_neg hi'j] at hzneg
    omega
  have hsubset : insert z W ⊆ V := Finset.insert_subset hzV hW
  have hcard : (insert z W).card = n := by
    rw [Finset.card_insert_of_notMem hzW, Finset.card_image_of_injective _ d.injective,
      Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_fin]
    have hn := j.isLt
    omega
  have hzcone : insert z W ∈ «Σ».cones := by
    have he : insert z W = V := Finset.eq_of_subset_of_card_le hsubset (by omega)
    exact he.symm ▸ hV
  have hez : e = z := «Σ».opposite_wall_ray_unique_of_negative d j e z
    hecone hzcone hecoord hzneg
  rw [hez, hVe]
  exact latticeRayCone_generator V hzV

end LatticePolytope

end PaperVerification.ToricGeometry
