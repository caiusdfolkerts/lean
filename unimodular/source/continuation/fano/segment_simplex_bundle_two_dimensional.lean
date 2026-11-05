module

public import Continuation.Fano.SegmentSimplexBundleTrianglePrimitivity

/-! The two-dimensional family has no unimodular triangular face.
There are two fibre-corner labels; three vertices repeat one label,
and vertices with the same label differ by an even lattice vector. -/

@[expose] public noncomputable section

set_option autoImplicit false

namespace Unimodular.SegmentSimplexBundle

open SegmentSimplex

theorem same_corner_difference_even (d : ℕ) (a : ℤ) (b c : Bool)
    (k : Option (Fin d)) :
    ∃ z : Lattice (d + 1),
      vertex d a (c, k) - vertex d a (b, k) = (2 : ℤ) • z := by
  obtain ⟨q, hq⟩ : ∃ q : ℤ, height c - height b = 2 * q := by
    cases b <;> cases c
    · exact ⟨0, by norm_num [height]⟩
    · exact ⟨1, by norm_num [height]⟩
    · exact ⟨-1, by norm_num [height]⟩
    · exact ⟨0, by norm_num [height]⟩
  let z : Lattice (d + 1) :=
    Fin.lastCases q (fun i => if k = some i then a * q else 0)
  refine ⟨z, ?_⟩
  ext j
  refine Fin.lastCases ?_ (fun i => ?_) j
  · simpa [z, Pi.smul_apply, smul_eq_mul] using hq
  · by_cases hk : k = some i
    · simp only [Pi.sub_apply, vertex_castSucc, if_pos hk, Pi.smul_apply,
        smul_eq_mul, z, Fin.lastCases_castSucc]
      dsimp [width]
      nlinarith [congrArg (a * ·) hq]
    · simp [vertex_castSucc, z, hk, Pi.smul_apply]

theorem same_corner_not_primitive (d : ℕ) (a : ℤ) (b c : Bool)
    (k : Option (Fin d)) :
    ¬ PrimitiveLatticeVector (vertex d a (c, k) - vertex d a (b, k)) := by
  intro h
  obtain ⟨z, hz⟩ := same_corner_difference_even d a b c k
  have hu := h 2 z hz
  norm_num [Int.isUnit_iff] at hu

theorem Q_UT_free_dim_two {a : ℤ} (ha : 0 ≤ a) (had : a ≤ 1)
    (E : Set (Ambient 2)) (hE : IsExtreme ℝ (Q 1 a) E) :
    ¬ IsUnimodularTriangle E := by
  intro htri
  obtain ⟨x, y, z, hx, hy, hz, _, hxy, hxz, hyz⟩ := triangle_primitive_edges htri
  obtain ⟨⟨b, k⟩, rfl⟩ := exists_vertex_of_face_extreme (d := 1) (Nat.le_refl 1) ha had hE hx
  obtain ⟨⟨c, l⟩, rfl⟩ := exists_vertex_of_face_extreme (d := 1) (Nat.le_refl 1) ha had hE hy
  obtain ⟨⟨e, m⟩, rfl⟩ := exists_vertex_of_face_extreme (d := 1) (Nat.le_refl 1) ha had hE hz
  have two_values (r : Option (Fin 1)) : r = none ∨ r = some 0 := by
    cases r with
    | none => exact Or.inl rfl
    | some i => exact Or.inr (congrArg some (Subsingleton.elim i 0))
  have hrepeat : k = l ∨ k = m ∨ l = m := by
    rcases two_values k with rfl | rfl <;>
      rcases two_values l with rfl | rfl <;>
      rcases two_values m with rfl | rfl <;> simp
  rcases hrepeat with hkl | hkm | hlm
  · subst l
    exact same_corner_not_primitive 1 a b c k hxy
  · subst m
    exact same_corner_not_primitive 1 a b e k hxz
  · subst m
    exact same_corner_not_primitive 1 a c e l hyz

end Unimodular.SegmentSimplexBundle

#print axioms Unimodular.SegmentSimplexBundle.Q_UT_free_dim_two
