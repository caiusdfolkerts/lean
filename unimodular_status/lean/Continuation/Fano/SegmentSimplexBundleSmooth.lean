module

public import Continuation.Fano.SegmentSimplexBundleVertices

/-!
# Smoothness and reflexivity of the whole segment–simplex family

The local basis is given by an explicit integral change of coordinates.
At a nonconstant fibre corner, one coordinate is negated and subtracted
from the others; the last coordinate is an integral shear followed by
the cap sign.  Both inverse formulas are retained below.
-/

@[expose] public noncomputable section

set_option autoImplicit false

namespace Unimodular.SegmentSimplexBundle

open scoped BigOperators

def constantCornerEquiv (d : ℕ) (b : Bool) :
    Lattice (d + 1) ≃ₗ[ℤ] Lattice (d + 1) where
  toFun x := Fin.lastCases (height b * x (Fin.last d)) (fun i => x i.castSucc)
  invFun x := Fin.lastCases (height b * x (Fin.last d)) (fun i => x i.castSucc)
  left_inv x := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [Fin.lastCases_last]
      rw [← mul_assoc, height_sq, one_mul]
    · simp
  right_inv x := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · cases b <;> simp [height]
    · simp
  map_add' x y := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j <;> simp [mul_add]
  map_smul' c x := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j <;>
      simp [Pi.smul_apply, smul_eq_mul, mul_left_comm]

def otherCornerEquiv (d : ℕ) (a : ℤ) (b : Bool) (k : Fin d) :
    Lattice (d + 1) ≃ₗ[ℤ] Lattice (d + 1) where
  toFun x := Fin.lastCases
    (a * x k.castSucc + height b * x (Fin.last d))
    (fun i => if i = k then -x k.castSucc else x i.castSucc - x k.castSucc)
  invFun x := Fin.lastCases
    (height b * (x (Fin.last d) + a * x k.castSucc))
    (fun i => if i = k then -x k.castSucc else x i.castSucc - x k.castSucc)
  left_inv x := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · cases b <;> simp [height] <;> ring
    · by_cases hi : i = k
      · subst i
        simp
      · simp [hi]
  right_inv x := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · cases b <;> simp [height] <;> ring
    · by_cases hi : i = k
      · subst i
        simp
      · simp [hi]
  map_add' x y := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [Fin.lastCases_last, Fin.lastCases_castSucc, Pi.add_apply]
      ring
    · by_cases hi : i = k <;> simp [hi] <;> ring
  map_smul' c x := by
    funext j
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [Fin.lastCases_last, Fin.lastCases_castSucc, Pi.smul_apply,
        smul_eq_mul, RingHom.id_apply]
      ring
    · by_cases hi : i = k <;> simp [hi, Pi.smul_apply, smul_eq_mul] <;> ring

def cornerEquiv (d : ℕ) (a : ℤ) (t : VertexIndex d) :
    Lattice (d + 1) ≃ₗ[ℤ] Lattice (d + 1) :=
  match t.2 with
  | none => constantCornerEquiv d t.1
  | some k => otherCornerEquiv d a t.1 k

def localBasis (d : ℕ) (a : ℤ) (t : VertexIndex d) :
    Module.Basis (Fin (d + 1)) ℤ (Lattice (d + 1)) :=
  (Pi.basisFun ℤ (Fin (d + 1))).map (cornerEquiv d a t)

theorem localBasis_last (d : ℕ) (a : ℤ) (t : VertexIndex d) :
    localBasis d a t (Fin.last d) = capNormal d t.1 := by
  rcases t with ⟨b, k⟩
  cases k <;> ext j <;> refine Fin.lastCases ?_ (fun i => ?_) j <;>
    simp [localBasis, Module.Basis.map_apply, cornerEquiv,
      constantCornerEquiv, otherCornerEquiv, capNormal,
      Pi.basisFun_apply, Pi.single_apply]

theorem localBasis_castSucc (d : ℕ) (a : ℤ) (t : VertexIndex d) (i : Fin d) :
    localBasis d a t i.castSucc =
      if t.2 = some i then simplexNormal d a none else simplexNormal d a (some i) := by
  rcases t with ⟨b, k⟩
  cases k with
  | none =>
      ext j
      refine Fin.lastCases ?_ (fun h => ?_) j <;>
        simp [localBasis, Module.Basis.map_apply, cornerEquiv,
          constantCornerEquiv, simplexNormal, Pi.basisFun_apply, Pi.single_apply]
  | some k =>
      by_cases hik : i = k
      · subst i
        ext j
        refine Fin.lastCases ?_ (fun h => ?_) j
        · simp [localBasis, Module.Basis.map_apply, cornerEquiv,
            otherCornerEquiv, simplexNormal, Pi.basisFun_apply, Pi.single_apply]
        · by_cases hhk : h = k <;>
            simp [localBasis, Module.Basis.map_apply, cornerEquiv,
              otherCornerEquiv, simplexNormal, Pi.basisFun_apply, Pi.single_apply,
              hhk, eq_comm]
      · ext j
        refine Fin.lastCases ?_ (fun h => ?_) j
        · simp [localBasis, Module.Basis.map_apply, cornerEquiv,
            otherCornerEquiv, simplexNormal, Pi.basisFun_apply, Pi.single_apply,
            hik, Ne.symm hik]
        · by_cases hhk : h = k
          · subst h
            simp [localBasis, Module.Basis.map_apply, cornerEquiv,
              otherCornerEquiv, simplexNormal, Pi.basisFun_apply, Pi.single_apply,
              hik, Ne.symm hik]
          · simp [localBasis, Module.Basis.map_apply, cornerEquiv,
              otherCornerEquiv, simplexNormal, Pi.basisFun_apply, Pi.single_apply,
              hik, Ne.symm hik, hhk, Ne.symm hhk]

theorem localBasis_mem (d : ℕ) (a : ℤ) (t : VertexIndex d) (i : Fin (d + 1)) :
    localBasis d a t i ∈ normals d a := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [localBasis_last]
    exact capNormal_mem d a t.1
  · rw [localBasis_castSucc]
    split_ifs <;> exact simplexNormal_mem _ _ _

theorem pairing_vertex_simplex_none (d : ℕ) (a : ℤ) (t : VertexIndex d) :
    pairing (embed (vertex d a t)) (simplexNormal d a none) =
      if t.2 = none then 1 - (width d a t.1 : ℝ) else 1 := by
  rw [pairing_simplex_none, embed_vertex_last]
  have hs : (∑ i : Fin d, embed (vertex d a t) i.castSucc) =
      (d : ℝ) - if t.2 = none then 0 else (width d a t.1 : ℝ) := by
    simp only [embed]
    exact_mod_cast vertex_fibre_sum d a t
  rw [hs]
  split_ifs <;> simp [width] <;> ring

theorem localBasis_active (d : ℕ) (a : ℤ) (t : VertexIndex d) (i : Fin (d + 1)) :
    pairing (embed (vertex d a t)) (localBasis d a t i) = 1 := by
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [localBasis_last, pairing_cap, embed_vertex_last]
    exact_mod_cast height_sq t.1
  · rw [localBasis_castSucc]
    split_ifs with h
    · rw [pairing_vertex_simplex_none]
      have hn : t.2 ≠ none := by rw [h]; simp
      simp [hn]
    · rw [pairing_simplex_some, embed_vertex_castSucc]
      simp [h]

theorem all_active {d : ℕ} {a : ℤ} (ha : 0 ≤ a) (had : a ≤ d)
    (t : VertexIndex d) (u : Lattice (d + 1)) (hu : u ∈ normals d a)
    (he : pairing (embed (vertex d a t)) u = 1) :
    ∃ i : Fin (d + 1), localBasis d a t i = u := by
  have hw : (0 : ℝ) < width d a t.1 := by exact_mod_cast width_pos ha had t.1
  rcases Finset.mem_union.mp hu with hu | hu
  · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hu
    cases k with
    | none =>
        rw [pairing_vertex_simplex_none] at he
        cases h : t.2 with
        | none =>
            simp [h] at he
            exact False.elim ((ne_of_gt (width_pos ha had t.1)) he)
        | some j =>
            refine ⟨j.castSucc, ?_⟩
            simp only [localBasis_castSucc, h, ite_true]
    | some j =>
        rw [pairing_simplex_some, embed_vertex_castSucc] at he
        have h : t.2 ≠ some j := by
          intro h
          rw [if_pos h] at he
          linarith
        exact ⟨j.castSucc, by simp only [localBasis_castSucc, if_neg h]⟩
  · obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hu
    rw [pairing_cap, embed_vertex_last] at he
    have hb : b = t.1 := by
      cases b <;> cases h : t.1
      · rfl
      · norm_num [height, h] at he
      · norm_num [height, h] at he
      · rfl
    exact ⟨Fin.last d, by rw [localBasis_last, hb]⟩

theorem normals_occur {d : ℕ} (hd : 1 ≤ d) (a : ℤ)
    (u : Lattice (d + 1)) (hu : u ∈ normals d a) :
    ∃ t : VertexIndex d, ∃ i : Fin (d + 1), localBasis d a t i = u := by
  rcases Finset.mem_union.mp hu with hu | hu
  · obtain ⟨k, _, rfl⟩ := Finset.mem_image.mp hu
    cases k with
    | none =>
        let j : Fin d := ⟨0, by omega⟩
        exact ⟨(true, some j), j.castSucc, by simp [localBasis_castSucc]⟩
    | some j =>
        exact ⟨(true, none), j.castSucc, by simp [localBasis_castSucc]⟩
  · obtain ⟨b, _, rfl⟩ := Finset.mem_image.mp hu
    exact ⟨(b, none), Fin.last d, localBasis_last d a (b, none)⟩

def vertexIndex {d : ℕ} {a : ℤ} (v : {v // v ∈ vertices d a}) : VertexIndex d :=
  Classical.choose (Finset.mem_image.mp v.property)

theorem vertexIndex_spec {d : ℕ} {a : ℤ} (v : {v // v ∈ vertices d a}) :
    vertex d a (vertexIndex v) = v.val :=
  (Classical.choose_spec (Finset.mem_image.mp v.property)).2

def presentation (d : ℕ) (a : ℤ) (hd : 1 ≤ d) (ha : 0 ≤ a) (had : a ≤ d) :
    SmoothReflexivePresentation (d + 1) where
  vertices := vertices d a
  normals := normals d a
  vertices_nonempty := ⟨vertex d a (true, none),
    Finset.mem_image.mpr ⟨(true, none), Finset.mem_univ _, rfl⟩⟩
  basis v := localBasis d a (vertexIndex v)
  basis_mem v i := localBasis_mem _ _ _ _
  basis_active v i := by
    rw [← vertexIndex_spec v]
    exact localBasis_active _ _ _ _
  active_subset v u hu he := by
    rw [← vertexIndex_spec v] at he
    exact all_active ha had (vertexIndex v) u hu he
  normals_occur u hu := by
    obtain ⟨t, i, hi⟩ := normals_occur hd a u hu
    let v : {v // v ∈ vertices d a} :=
      ⟨vertex d a t, Finset.mem_image.mpr ⟨t, Finset.mem_univ _, rfl⟩⟩
    have he : pairing (embed v.val) u = 1 := by
      rw [← hi]
      exact localBasis_active d a t i
    rw [← vertexIndex_spec v] at he
    obtain ⟨j, hj⟩ := all_active ha had (vertexIndex v) u hu he
    exact ⟨v, j, hj⟩
  hull_eq := (hull_eq_Q ha had).trans (Set.ext (mem_Q_iff d a))

theorem presentation_carrier (d : ℕ) (a : ℤ) (hd : 1 ≤ d) (ha : 0 ≤ a)
    (had : a ≤ d) : (presentation d a hd ha had).carrier = Q d a :=
  hull_eq_Q ha had

theorem extremePoints_eq_vertexRange (d : ℕ) (a : ℤ) (hd : 1 ≤ d) (ha : 0 ≤ a)
    (had : a ≤ d) :
    (Q d a).extremePoints ℝ = embed '' (vertices d a : Set (Lattice (d + 1))) := by
  rw [← presentation_carrier d a hd ha had]
  exact (presentation d a hd ha had).extremePoints_eq_vertices

theorem geometricFacetNormals_eq (d : ℕ) (a : ℤ) (hd : 1 ≤ d) (ha : 0 ≤ a)
    (had : a ≤ d) :
    (presentation d a hd ha had).geometricFacetNormals = (normals d a : Set _) :=
  (presentation d a hd ha had).geometricFacetNormals_eq_normals

theorem zero_mem_interior (d : ℕ) (a : ℤ) (hd : 1 ≤ d) (ha : 0 ≤ a)
    (had : a ≤ d) : (0 : Ambient (d + 1)) ∈ interior (Q d a) := by
  rw [← presentation_carrier d a hd ha had]
  exact (presentation d a hd ha had).zero_mem_interior_carrier

theorem polar_eq_hull_normals (d : ℕ) (a : ℤ) (hd : 1 ≤ d) (ha : 0 ≤ a)
    (had : a ≤ d) :
    realPolar (Q d a) = convexHull ℝ
      (embed '' (insert 0 (normals d a : Set (Lattice (d + 1))))) := by
  rw [← presentation_carrier d a hd ha had]
  exact (presentation d a hd ha had).realPolar_eq_convexHull_normals

end Unimodular.SegmentSimplexBundle

#print axioms Unimodular.SegmentSimplexBundle.presentation
#print axioms Unimodular.SegmentSimplexBundle.extremePoints_eq_vertexRange
#print axioms Unimodular.SegmentSimplexBundle.geometricFacetNormals_eq
#print axioms Unimodular.SegmentSimplexBundle.zero_mem_interior
#print axioms Unimodular.SegmentSimplexBundle.polar_eq_hull_normals
