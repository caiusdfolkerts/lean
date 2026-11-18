module

public import Continuation.Fano.SegmentSimplexBundleSmooth
public import Mathlib.Tactic.FinCases

/-! Primitivity of all three edges of a genuine unimodular triangle,
and the obstruction furnished by two vertices on one end simplex. -/

@[expose] public noncomputable section

set_option autoImplicit false

namespace Unimodular.SegmentSimplexBundle

open SegmentSimplex

theorem primitive_of_basis_coordinate_one {n : ℕ} {ι : Type*}
    (W : Submodule ℝ (Ambient n)) (B : Module.Basis ι ℤ (integralSubspace W))
    (x : integralSubspace W) (i : ι) (hx : B.repr x i = 1) :
    PrimitiveLatticeVector x.val := by
  intro k z he
  have hk : k ≠ 0 := by
    intro hk
    have hx0 : x = 0 := Subtype.ext (by simpa [hk] using he)
    simp [hx0] at hx
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have heR : embed x.val = (k : ℝ) • embed z := by
    rw [he]
    ext j
    simp [embed, Pi.smul_apply, smul_eq_mul]
  have hzW : embed z ∈ W := by
    have hm : embed x.val ∈ W := x.property
    rw [heR] at hm
    have h := W.smul_mem ((k : ℝ)⁻¹) hm
    simpa only [smul_smul, inv_mul_cancel₀ hkR, one_smul] using h
  have he' : x = k • (⟨z, hzW⟩ : integralSubspace W) := Subtype.ext he
  have h := congrArg (fun y => B.repr y i) he'
  have hm : (1 : ℤ) = k * B.repr (⟨z, hzW⟩ : integralSubspace W) i := by
    simpa only [hx, map_smulₛₗ, RingHom.id_apply, Finsupp.smul_apply,
      smul_eq_mul] using h
  exact IsUnit.of_mul_eq_one _ hm.symm

theorem triangle_primitive_edges {n : ℕ} {E : Set (Ambient n)}
    (hE : IsUnimodularTriangle E) :
    ∃ a b c : Lattice n,
      embed a ∈ E.extremePoints ℝ ∧ embed b ∈ E.extremePoints ℝ ∧
      embed c ∈ E.extremePoints ℝ ∧
      E = convexHull ℝ ({embed a, embed b, embed c} : Set (Ambient n)) ∧
      PrimitiveLatticeVector (b - a) ∧ PrimitiveLatticeVector (c - a) ∧
      PrimitiveLatticeVector (c - b) := by
  obtain ⟨a, b, c, ha, hb, hc, hE, B, hB0, hB1⟩ := hE
  refine ⟨a, b, c, ha, hb, hc, hE, ?_, ?_, ?_⟩
  · rw [← hB0]
    exact integralSubspace_basis_primitive _ B 0
  · rw [← hB1]
    exact integralSubspace_basis_primitive _ B 1
  · have hcoord : B.repr (B 1 - B 0) 1 = 1 := by simp
    have hprim := primitive_of_basis_coordinate_one _ B (B 1 - B 0) 1 hcoord
    have he : (B 1 - B 0).val = c - b := by
      simp only [Submodule.coe_sub, hB0, hB1]
      abel
    rwa [he] at hprim

theorem primitive_ne_zero {n : ℕ} {x : Lattice n}
    (hx : PrimitiveLatticeVector x) : x ≠ 0 := by
  intro h
  have hu := hx 0 0 (by simp [h])
  norm_num at hu

theorem vertex_injective {d : ℕ} {a : ℤ} (ha : 0 ≤ a) (had : a ≤ d) :
    Function.Injective (vertex d a) := by
  rintro ⟨b, k⟩ ⟨c, l⟩ h
  have hh := congrArg (fun v : Lattice (d + 1) => v (Fin.last d)) h
  simp only [vertex_last] at hh
  have hbc : b = c := by
    cases b <;> cases c
    · rfl
    · norm_num [height] at hh
    · norm_num [height] at hh
    · rfl
  subst c
  have hw := width_pos ha had b
  have hkl : k = l := by
    cases k with
    | none =>
        cases l with
        | none => rfl
        | some j =>
            have hj := congrArg (fun v : Lattice (d + 1) => v j.castSucc) h
            simp only [vertex_castSucc] at hj
            simp at hj
            omega
    | some i =>
        cases l with
        | none =>
            have hi := congrArg (fun v : Lattice (d + 1) => v i.castSucc) h
            simp only [vertex_castSucc] at hi
            simp at hi
            omega
        | some j =>
            by_cases hij : i = j
            · subst j
              rfl
            · have hi := congrArg (fun v : Lattice (d + 1) => v i.castSucc) h
              simp [vertex_castSucc, hij, Ne.symm hij] at hi
              omega
  exact Prod.ext rfl hkl

theorem embed_vertex_injective {d : ℕ} {a : ℤ} (ha : 0 ≤ a) (had : a ≤ d) :
    Function.Injective (fun t => embed (vertex d a t)) := by
  intro s t h
  exact vertex_injective ha had (LatticeHull.embed_injective h)

theorem exists_vertex_of_face_extreme {d : ℕ} {a : ℤ}
    (hd : 1 ≤ d) (ha : 0 ≤ a) (had : a ≤ d)
    {E : Set (Ambient (d + 1))} (hE : IsExtreme ℝ (Q d a) E)
    {x : Lattice (d + 1)} (hx : embed x ∈ E.extremePoints ℝ) :
    ∃ t : VertexIndex d, vertex d a t = x := by
  have hQ := hE.extremePoints_subset_extremePoints hx
  rw [extremePoints_eq_vertexRange d a hd ha had] at hQ
  obtain ⟨v, hv, he⟩ := hQ
  have hvx : v = x := LatticeHull.embed_injective he
  obtain ⟨t, _, ht⟩ := Finset.mem_image.mp hv
  exact ⟨t, ht.trans hvx⟩

theorem same_height_difference (d : ℕ) (a : ℤ) (b : Bool)
    (k l : Option (Fin d)) :
    ∃ z : Lattice (d + 1),
      vertex d a (b, l) - vertex d a (b, k) = width d a b • z := by
  let z : Lattice (d + 1) := Fin.lastCases 0
    (fun i => (if k = some i then 1 else 0) - (if l = some i then 1 else 0))
  refine ⟨z, ?_⟩
  ext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simp [z, Pi.smul_apply]
  · by_cases hk : k = some i <;> by_cases hl : l = some i <;>
      simp [vertex_castSucc, z, Pi.smul_apply, smul_eq_mul, hk, hl] <;> ring

theorem same_height_not_primitive {d : ℕ} {a : ℤ}
    (ha : 0 ≤ a) (had : a < d) (b : Bool) (k l : Option (Fin d)) :
    ¬ PrimitiveLatticeVector (vertex d a (b, l) - vertex d a (b, k)) := by
  intro h
  obtain ⟨z, hz⟩ := same_height_difference d a b k l
  have hu := h (width d a b) z hz
  have hw := width_ge_two ha had b
  rw [Int.isUnit_iff] at hu
  omega

/-- Among three vertices two have the same height. Their difference is
a multiple of a width at least two, so they cannot form a unimodular triangle. -/
theorem Q_UT_free_of_lt {d : ℕ} {a : ℤ}
    (hd : 1 ≤ d) (ha : 0 ≤ a) (had : a < d)
    (E : Set (Ambient (d + 1))) (hE : IsExtreme ℝ (Q d a) E) :
    ¬ IsUnimodularTriangle E := by
  intro htri
  obtain ⟨x, y, z, hx, hy, hz, _, hxy, hxz, hyz⟩ := triangle_primitive_edges htri
  obtain ⟨s, rfl⟩ := exists_vertex_of_face_extreme hd ha had.le hE hx
  obtain ⟨t, rfl⟩ := exists_vertex_of_face_extreme hd ha had.le hE hy
  obtain ⟨u, rfl⟩ := exists_vertex_of_face_extreme hd ha had.le hE hz
  rcases s with ⟨b, k⟩
  rcases t with ⟨c, l⟩
  rcases u with ⟨e, m⟩
  cases b <;> cases c <;> cases e
  · exact same_height_not_primitive ha had false k l hxy
  · exact same_height_not_primitive ha had false k l hxy
  · exact same_height_not_primitive ha had false k m hxz
  · exact same_height_not_primitive ha had true l m hyz
  · exact same_height_not_primitive ha had false l m hyz
  · exact same_height_not_primitive ha had true k m hxz
  · exact same_height_not_primitive ha had true k l hxy
  · exact same_height_not_primitive ha had true k l hxy

end Unimodular.SegmentSimplexBundle

#print axioms Unimodular.SegmentSimplexBundle.Q_UT_free_of_lt
