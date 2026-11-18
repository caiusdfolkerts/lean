module

public import Unimodular.Geometry
public import TauCeti.Geometry.Convex.Cone.Relations
public import Mathlib.Analysis.Convex.Combination

@[expose] public section

/-! ## Facets -/

noncomputable section

namespace Unimodular.SmoothReflexivePresentation

open scoped BigOperators

variable {n : ℕ} (P : SmoothReflexivePresentation n)

/-- The actual exposed face on the supporting hyperplane of a normal. -/
def normalFace (u : Lattice n) : Set (Ambient n) :=
  {p | p ∈ P.carrier ∧ pairing p u = 1}

/-- A facet is a nonempty maximal proper convex face. This definition uses
actual subsets and segments of the real polytope. -/
def IsFacet (E : Set (Ambient n)) : Prop :=
  E.Nonempty ∧ Convex ℝ E ∧ IsExtreme ℝ P.carrier E ∧ E ≠ P.carrier ∧
    ∀ F : Set (Ambient n), Convex ℝ F → IsExtreme ℝ P.carrier F →
      F ≠ P.carrier → E ⊆ F → F = E

theorem zero_mem_carrier : (0 : Ambient n) ∈ P.carrier := by
  apply (P.mem_carrier_iff _).mpr
  intro u hu
  simp [pairing]

theorem normalFace_convex (u : Lattice n) : Convex ℝ (P.normalFace u) := by
  intro x hx y hy a b ha hb hab
  refine ⟨(convex_convexHull ℝ _) hx.1 hy.1 ha hb hab, ?_⟩
  rw [pairing_add_left, pairing_smul_left, pairing_smul_left, hx.2, hy.2]
  simpa using hab

theorem normalFace_extreme (u : Lattice n) (hu : u ∈ P.normals) :
    IsExtreme ℝ P.carrier (P.normalFace u) := by
  refine ⟨fun p hp => hp.1, ?_⟩
  rintro x hx y hy z hz ⟨a, b, ha, hb, hab, he⟩
  refine ⟨hx, ?_⟩
  have hxu := (P.mem_carrier_iff _).mp hx u hu
  have hyu := (P.mem_carrier_iff _).mp hy u hu
  have h := congrArg (fun q => pairing q u) he
  rw [pairing_add_left, pairing_smul_left, pairing_smul_left, hz.2] at h
  nlinarith

theorem normalFace_nonempty (u : Lattice n) (hu : u ∈ P.normals) :
    (P.normalFace u).Nonempty := by
  obtain ⟨v, i, rfl⟩ := P.normals_occur u hu
  exact ⟨embed v.val, P.vertex_mem v, P.basis_active v i⟩

theorem normalFace_ne_carrier (u : Lattice n) : P.normalFace u ≠ P.carrier := by
  intro he
  have hz : (0 : Ambient n) ∈ P.normalFace u := he.symm ▸ P.zero_mem_carrier
  have : (0 : ℝ) = 1 := by simpa [pairing] using hz.2
  norm_num at this

/-- Every nonempty actual face contains a listed vertex. This follows from
convexity of the complement of an extreme set and the genuine hull equality. -/
theorem exists_vertex_mem_face {E : Set (Ambient n)}
    (hE : IsExtreme ℝ P.carrier E) (hne : E.Nonempty) :
    ∃ v : {v // v ∈ P.vertices}, embed v.val ∈ E := by
  by_contra h
  push_neg at h
  have hsub : P.carrier ⊆ P.carrier \ E := by
    change convexHull ℝ (embed '' (P.vertices : Set (Lattice n))) ⊆ P.carrier \ E
    apply convexHull_min
    · rintro p ⟨v, hv, rfl⟩
      exact ⟨P.vertex_mem ⟨v, hv⟩, h ⟨v, hv⟩⟩
    · exact hE.convex_sdiff (convex_convexHull ℝ _)
  obtain ⟨p, hp⟩ := hne
  exact (hsub (hE.subset hp)).2 hp

/-- For a convex face through a point, equality of its tangent cone with the
polytope tangent cone forces equality of the actual faces. -/
theorem eq_carrier_of_localCone_eq {E : Set (Ambient n)}
    (hE : Convex ℝ E) (hEP : IsExtreme ℝ P.carrier E)
    {v : Ambient n} (hv : v ∈ E)
    (he : localCone v E = localCone v P.carrier) : E = P.carrier := by
  apply Set.Subset.antisymm hEP.subset
  intro q hq
  have hd : q - v ∈ localCone v E := by
    rw [he]
    exact PointedCone.subset_hull ⟨q, hq, rfl⟩
  obtain ⟨t, ht, hpt⟩ := (mem_localCone_iff hE hv).mp hd
  let s := min t (1 / 2 : ℝ)
  have hs : 0 < s := lt_min ht (by norm_num)
  have hst : s ≤ t := min_le_left _ _
  have hs1 : s < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hp : v + s • (q - v) ∈ E :=
    convex_feasible_step_mono hE hv ht hpt hs.le hst
  apply hEP.right_mem_of_mem_openSegment (hEP.subset hv) hq hp
  refine ⟨1 - s, s, sub_pos.mpr hs1, hs, sub_add_cancel _ _, ?_⟩
  module

/-- Every nonempty proper actual face lies in one of the listed normal faces.
The proof uses the full simplicial tangent cone, not an assumed facet list. -/
theorem face_subset_normalFace {E : Set (Ambient n)}
    (hE : Convex ℝ E) (hEP : IsExtreme ℝ P.carrier E)
    (hne : E.Nonempty) (hproper : E ≠ P.carrier) :
    ∃ u ∈ P.normals, E ⊆ P.normalFace u := by
  classical
  obtain ⟨v, hv⟩ := P.exists_vertex_mem_face hEP hne
  let C := localCone (embed v.val) P.carrier
  let F := localCone (embed v.val) E
  let d := fun i => embed (inwardBasisDirection (P.basis v) i)
  have hFC : F.IsFaceOf C :=
    localCone_isFaceOf (convex_convexHull ℝ _) hE hEP hv
  have hC : C = PointedCone.hull ℝ (Set.range d) := P.localCone_eq_hull_inwardDirections v
  have hF : F = PointedCone.hull ℝ (d '' {j | d j ∈ F}) :=
    PointedCone.Face.eq_hull_image ⟨F, hFC⟩ hC
  have hmissing : ∃ i : Fin n, d i ∉ F := by
    by_contra h
    push_neg at h
    have he : F = C := by
      apply le_antisymm hFC.le
      rw [hC]
      apply Submodule.span_le.mpr
      rintro x ⟨i, rfl⟩
      exact h i
    exact hproper (P.eq_carrier_of_localCone_eq hE hEP hv he)
  obtain ⟨i, hi⟩ := hmissing
  have hzero : ∀ z ∈ F, pairing z (P.basis v i) = 0 := by
    intro z hz
    rw [hF] at hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, hj, rfl⟩ := hz
      have hij : i ≠ j := by
        intro he
        subst j
        exact hi hj
      change pairing (embed (inwardBasisDirection (P.basis v) j)) (P.basis v i) = 0
      rw [embed_inwardBasisDirection, pairing_dualCorner_basis]
      simp [Pi.single_apply, hij, Ne.symm hij]
    | zero => simp [pairing]
    | add x y _ _ hx hy => rw [pairing_add_left, hx, hy, add_zero]
    | smul c x _ hx => rw [← Nonneg.coe_smul, pairing_smul_left, hx, mul_zero]
  refine ⟨P.basis v i, P.basis_mem v i, ?_⟩
  intro p hp
  refine ⟨hEP.subset hp, ?_⟩
  have hz := hzero (p - embed v.val) (PointedCone.subset_hull ⟨p, hp, rfl⟩)
  have hadd := pairing_add_left (p - embed v.val) (embed v.val) (P.basis v i)
  rw [sub_add_cancel, hz, P.basis_active, zero_add] at hadd
  exact hadd

theorem normalFace_isFacet (u : Lattice n) (hu : u ∈ P.normals) :
    P.IsFacet (P.normalFace u) := by
  refine ⟨P.normalFace_nonempty u hu, P.normalFace_convex u,
    P.normalFace_extreme u hu, P.normalFace_ne_carrier u, ?_⟩
  intro E hE hEP hproper hsub
  obtain ⟨w, hw, hEw⟩ := P.face_subset_normalFace hE hEP
    ((P.normalFace_nonempty u hu).mono hsub) hproper
  obtain ⟨p, hpu, hpother⟩ := P.exists_only_one_active u hu
  have hpP : p ∈ P.carrier := by
    apply (P.mem_carrier_iff _).mpr
    intro z hz
    by_cases hzu : z = u
    · simpa [hzu, hpu]
    · exact (hpother z hz hzu).le
  have hpw := (hEw (hsub ⟨hpP, hpu⟩)).2
  have hwu : w = u := by
    by_contra hwu
    exact (ne_of_lt (hpother w hw hwu)) hpw
  subst w
  exact Set.Subset.antisymm hEw hsub

/-- Exact identification of the maximal proper convex faces. -/
theorem isFacet_iff_normalFace (E : Set (Ambient n)) :
    P.IsFacet E ↔ ∃ u ∈ P.normals, E = P.normalFace u := by
  constructor
  · rintro ⟨hne, hconv, hext, hproper, hmax⟩
    obtain ⟨u, hu, hsub⟩ := P.face_subset_normalFace hconv hext hne hproper
    exact ⟨u, hu, (hmax _ (P.normalFace_convex u) (P.normalFace_extreme u hu)
      (P.normalFace_ne_carrier u) hsub).symm⟩
  · rintro ⟨u, hu, rfl⟩
    exact P.normalFace_isFacet u hu

/-- Distinct listed normals give distinct actual facets. -/
theorem normalFace_injective {u w : Lattice n} (hu : u ∈ P.normals)
    (hw : w ∈ P.normals) (he : P.normalFace u = P.normalFace w) : u = w := by
  obtain ⟨p, hpu, hpother⟩ := P.exists_only_one_active u hu
  have hpP : p ∈ P.carrier := by
    apply (P.mem_carrier_iff _).mpr
    intro z hz
    by_cases hzu : z = u
    · simpa [hzu, hpu]
    · exact (hpother z hz hzu).le
  have hpw : p ∈ P.normalFace w := he ▸ (show p ∈ P.normalFace u from ⟨hpP, hpu⟩)
  by_contra huw
  exact (ne_of_lt (hpother w hw (Ne.symm huw))) hpw.2

/-- These are facets also in the dimension-based sense: their actual affine
direction spaces have dimension n−1. -/
theorem normalFace_finrank (u : Lattice n) (hu : u ∈ P.normals) :
    Module.finrank ℝ (vectorSpan ℝ (P.normalFace u)) = n - 1 := by
  classical
  obtain ⟨v, i, rfl⟩ := P.normals_occur u hu
  let d := fun j => embed (inwardBasisDirection (P.basis v) j)
  let C := localCone (embed v.val) P.carrier
  let F := localCone (embed v.val) (P.normalFace (P.basis v i))
  have hv : embed v.val ∈ P.normalFace (P.basis v i) :=
    ⟨P.vertex_mem v, P.basis_active v i⟩
  have hFC : F.IsFaceOf C :=
    localCone_isFaceOf (convex_convexHull ℝ _) (P.normalFace_convex _)
      (P.normalFace_extreme _ (P.basis_mem v i)) hv
  have hC : C = PointedCone.hull ℝ (Set.range d) := P.localCone_eq_hull_inwardDirections v
  have hmem (j : Fin n) : d j ∈ F ↔ j ≠ i := by
    constructor
    · intro hj hji
      subst j
      obtain ⟨t, ht, hp⟩ := (mem_localCone_iff (P.normalFace_convex _) hv).mp hj
      have he := hp.2
      change pairing (embed v.val + t • embed (inwardBasisDirection (P.basis v) i))
        (P.basis v i) = 1 at he
      rw [pairing_add_left, pairing_smul_left, P.basis_active,
        embed_inwardBasisDirection, pairing_dualCorner_basis] at he
      simp only [Pi.single_eq_same] at he
      nlinarith
    · intro hji
      obtain ⟨t, ht, hp⟩ := P.exists_pos_mem_edgeSlice v j
      apply (mem_localCone_iff (P.normalFace_convex _) hv).mpr
      exact ⟨t, ht, hp.1, hp.2 i (Ne.symm hji)⟩
  let G : C.Face := ⟨F, hFC⟩
  have hdim := TauCeti.finrank_span_face_eq_card_faceOrderIsoSet d
    (inwardDirections_linearIndependent (P.basis v)) hC G
  have hindices : PointedCone.faceOrderIsoSet
      (inwardDirections_linearIndependent (P.basis v)) hC G = {j | j ≠ i} := by
    rw [PointedCone.faceOrderIsoSet_apply]
    ext j
    exact hmem j
  rw [hindices] at hdim
  change Module.finrank ℝ (Submodule.span ℝ (F : Set (Ambient n))) =
    Nat.card {j : Fin n // j ≠ i} at hdim
  have hcard : Nat.card {j : Fin n // j ≠ i} = n - 1 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl]
    simp
  rw [hcard] at hdim
  have hspan : Submodule.span ℝ (F : Set (Ambient n)) =
      vectorSpan ℝ (P.normalFace (P.basis v i)) := span_localCone hv
  rw [← hspan]
  exact hdim

/-- An actual facet determines its supporting normal uniquely when its support
number is one. This also rules out any additional unlisted facet normals. -/
theorem eq_normal_of_normalFace_eq {u w : Lattice n} (hw : w ∈ P.normals)
    (he : P.normalFace u = P.normalFace w) : u = w := by
  classical
  obtain ⟨v, i, rfl⟩ := P.normals_occur w hw
  have hvw : embed v.val ∈ P.normalFace (P.basis v i) :=
    ⟨P.vertex_mem v, P.basis_active v i⟩
  have hvu : pairing (embed v.val) u = 1 := (he.symm ▸ hvw).2
  have hc (j : Fin n) (hji : j ≠ i) : (P.basis v).repr u j = 0 := by
    obtain ⟨t, ht, hp⟩ := P.exists_pos_mem_edgeSlice v j
    have hpw : embed v.val + t • embed (inwardBasisDirection (P.basis v) j) ∈
        P.normalFace (P.basis v i) := ⟨hp.1, hp.2 i (Ne.symm hji)⟩
    have hpu : pairing (embed v.val + t • embed (inwardBasisDirection (P.basis v) j)) u = 1 :=
      (he.symm ▸ hpw).2
    rw [pairing_add_left, pairing_smul_left, hvu,
      embed_inwardBasisDirection, pairing_dualCorner] at hpu
    simp only [Pi.single_apply] at hpu
    have hcoord : ((P.basis v).repr u j : ℝ) = 0 := by
      have hsum : (∑ k, (if k = j then (-1 : ℝ) else 0) *
          ((P.basis v).repr u k : ℝ)) = -((P.basis v).repr u j : ℝ) := by
        simp
      rw [hsum] at hpu
      nlinarith
    exact_mod_cast hcoord
  have hsum : (∑ j, (P.basis v).repr u j : ℤ) = 1 := by
    rw [P.vertex_eq_dualCorner_one v, pairing_dualCorner] at hvu
    simp only [one_mul] at hvu
    exact_mod_cast hvu
  have hi : (P.basis v).repr u i = 1 := by
    rwa [Finset.sum_eq_single i (fun j _ hji => hc j hji) (by simp)] at hsum
  apply (P.basis v).repr.injective
  ext j
  rw [Module.Basis.repr_self]
  by_cases hji : j = i
  · subst j
    simpa using hi
  · simp [hc j hji, Finsupp.single_apply, hji, Ne.symm hji]

/-- The normals in the presentation are precisely the primitive supporting
normals of the actual facets at lattice distance one. -/
theorem mem_normals_iff_primitive_facetNormal (u : Lattice n) :
    u ∈ P.normals ↔ PrimitiveLatticeVector u ∧
      (∀ p ∈ P.carrier, pairing p u ≤ 1) ∧ P.IsFacet (P.normalFace u) := by
  constructor
  · intro hu
    exact ⟨P.normal_primitive u hu,
      fun p hp => (P.mem_carrier_iff p).mp hp u hu, P.normalFace_isFacet u hu⟩
  · rintro ⟨_, _, hfacet⟩
    obtain ⟨w, hw, he⟩ := (P.isFacet_iff_normalFace _).mp hfacet
    exact (P.eq_normal_of_normalFace_eq hw he).symm ▸ hw

/-- The finite halfspace presentation really has the origin in its ambient
interior, so it is full dimensional rather than only relatively full dimensional. -/
theorem zero_mem_interior_carrier : (0 : Ambient n) ∈ interior P.carrier := by
  let O : Set (Ambient n) := {p | ∀ u : {u // u ∈ P.normals}, pairing p u.val < 1}
  have hO : IsOpen O := by
    have he : O = ⋂ u : {u // u ∈ P.normals}, {p | pairing p u.val < 1} := by
      ext p
      simp [O]
    rw [he]
    apply isOpen_iInter_of_finite
    intro u
    apply isOpen_lt _ continuous_const
    unfold pairing
    fun_prop
  have hz : (0 : Ambient n) ∈ O := by
    intro u
    simp [pairing]
  apply mem_interior_iff_mem_nhds.mpr
  exact Filter.mem_of_superset (hO.mem_nhds hz) fun p hp =>
    (P.mem_carrier_iff p).mpr fun u hu => (hp ⟨u, hu⟩).le

/-- Primitive outward facet normals, defined from the actual face geometry and
unit supporting inequalities rather than from the presentation's normal list. -/
def geometricFacetNormals : Set (Lattice n) :=
  {u | PrimitiveLatticeVector u ∧ (∀ p ∈ P.carrier, pairing p u ≤ 1) ∧
    P.IsFacet (P.normalFace u)}

theorem geometricFacetNormals_eq_normals :
    P.geometricFacetNormals = (P.normals : Set (Lattice n)) := by
  ext u
  exact (P.mem_normals_iff_primitive_facetNormal u).symm

/-- Corollary 6.2 with both deep monotonicity and facet normals defined by the
actual real face geometry of the polytope. All dimensions and independent full
selections of primitive normals are included. -/
theorem corollary_6_2 (hP : P.DeeplyMonotone)
    (a : Fin n → {u // u ∈ P.geometricFacetNormals})
    (ha : LinearIndependent ℝ (fun i => embed (a i).val)) :
    ∃ b : Module.Basis (Fin n) ℤ (Lattice n), ∀ i, b i = (a i).val := by
  let a' : Fin n → {u // u ∈ P.normals} := fun i =>
    ⟨(a i).val, (P.mem_normals_iff_primitive_facetNormal _).mpr (a i).property⟩
  exact P.deeplyMonotone_facetNormals_uniform hP a' ha

end Unimodular.SmoothReflexivePresentation

end

/-! Transitive axiom audit for every exported declaration in this module. -/

/-! ## SubspaceSpan -/

noncomputable section

namespace Unimodular

open scoped BigOperators

/-- The real vectors of an integral basis are a real linearly independent family. -/
theorem embed_basis_linearIndependent {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) :
    LinearIndependent ℝ (fun i => embed (b i)) := by
  apply LinearIndependent.of_comp (realCoordinates b)
  have he : (realCoordinates b) ∘ (fun i => embed (b i)) = Pi.basisFun ℝ (Fin n) := by
    funext i
    simpa only [Function.comp_apply, Pi.basisFun_apply] using realCoordinates_basis b i
  rw [he]
  exact (Pi.basisFun ℝ (Fin n)).linearIndependent

theorem basis_mem_basisFace {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (i : Fin n) (hi : i ∈ I) : embed (b i) ∈ basisFace b I := by
  classical
  refine ⟨Pi.single i 1, ?_, ?_, ?_⟩
  · intro j
    simp only [Pi.single_apply]
    split_ifs <;> norm_num
  · intro j hj
    have hji : j ≠ i := by rintro rfl; exact hj hi
    simp [Pi.single_apply, hji, Ne.symm hji]
  · simp [Pi.single_apply]

theorem span_basisFace {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)) :
    Submodule.span ℝ (basisFace b I) =
      Submodule.span ℝ (Set.range (fun i : {i // i ∈ I} => embed (b i.val))) := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro x ⟨c, hc, hzero, rfl⟩
    apply Submodule.sum_mem
    intro i _
    by_cases hi : i ∈ I
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i, hi⟩, rfl⟩)
    · rw [hzero i hi, zero_smul]
      exact Submodule.zero_mem _
  · apply Submodule.span_le.mpr
    rintro x ⟨i, rfl⟩
    exact Submodule.subset_span (basis_mem_basisFace b I i.val i.property)

theorem finrank_span_basisFace {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n)) :
    Module.finrank ℝ (Submodule.span ℝ (basisFace b I)) = I.card := by
  rw [span_basisFace]
  simpa [Function.comp_def] using finrank_span_eq_card
    ((embed_basis_linearIndependent b).comp
      (fun i : {i // i ∈ I} => i.val) Subtype.val_injective)

namespace SmoothCompleteFan

variable {n : ℕ} (fan : SmoothCompleteFan n)

/-- A rectangular version of the positive-column uniqueness argument. -/
theorem positive_coordinate_unique (hfan : fan.PositiveCoordinateCriterion)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (hb : b ∈ fan.maximal)
    (u : Lattice n) (hu : u ∈ fan.rays) {i j : Fin n}
    (hi : 0 < b.repr u i) (hj : 0 < b.repr u j) : i = j := by
  classical
  by_contra hij
  have hsum : max (b.repr u i) 0 + max (b.repr u j) 0 ≤
      ∑ k, max (b.repr u k) 0 := by
    calc
      _ = ∑ k ∈ ({i, j} : Finset (Fin n)), max (b.repr u k) 0 := by simp [hij]
      _ ≤ ∑ k, max (b.repr u k) 0 :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
          (fun k _ _ => le_max_right _ _)
  rw [max_eq_left hi.le, max_eq_left hj.le] at hsum
  have hbnd := hfan b hb u hu
  omega

/-- The first assertion of Lemma 6.4: every subspace generated by an independent
family of rays is the span of an actual cone of the fan. The dimension and the
complete real cone geometry are preserved. -/
theorem independent_ray_span_is_cone_span (hfan : fan.PositiveCoordinateCriterion)
    {k : ℕ} (a : Fin k → {u // u ∈ fan.rays})
    (ha : LinearIndependent ℝ (fun j => embed (a j).val)) :
    ∃ b ∈ fan.maximal, ∃ I : Finset (Fin n), I.card = k ∧
      Submodule.span ℝ (Set.range (fun j => embed (a j).val)) =
        Submodule.span ℝ (basisFace b I) := by
  classical
  let row := fun p : fan.maximal × Fin n => fun j : Fin k =>
    p.1.val.repr (a j).val p.2
  let J := {p : fan.maximal × Fin n // ∃ j, row p j ≠ 0}
  obtain ⟨t, ht, hgeneric⟩ := GenericWeights.exists_geometric_progression
    (fun p : J => row p.val) (fun p => p.property)
  let x : Lattice n := ∑ j : Fin k, t ^ j.val • (a j).val
  obtain ⟨b, hb, hxb⟩ := fan.complete (embed x)
  have hxcoord (i : Fin n) : 0 ≤ b.repr x i := by
    have h := (mem_basisCone_iff b (embed x)).mp hxb i
    rw [realCoordinates_embed] at h
    exact_mod_cast h
  have hformula (i : Fin n) : b.repr x i =
      ∑ j : Fin k, b.repr (a j).val i * t ^ j.val := by
    simp only [x, map_sum, map_smulₛₗ, RingHom.id_apply, Finsupp.finsetSum_apply,
      Finsupp.smul_apply, smul_eq_mul, mul_comm]
  let I : Finset (Fin n) := Finset.univ.filter (fun i => ∃ j, b.repr (a j).val i ≠ 0)
  have hI (i : Fin n) : i ∈ I ↔ ∃ j, b.repr (a j).val i ≠ 0 := by simp [I]
  have hstrict (i : Fin n) (hi : i ∈ I) : 0 < b.repr x i := by
    have hn : b.repr x i ≠ 0 := by
      rw [hformula]
      exact hgeneric ⟨(⟨b, hb⟩, i), (hI i).mp hi⟩
    exact lt_of_le_of_ne (hxcoord i) (Ne.symm hn)
  have hpos (i : {i // i ∈ I}) : ∃ j : Fin k, 0 < b.repr (a j).val i.val := by
    by_contra h
    push_neg at h
    have hnonpos : b.repr x i.val ≤ 0 := by
      rw [hformula]
      exact Finset.sum_nonpos fun j _ =>
        mul_nonpos_of_nonpos_of_nonneg (h j) (pow_nonneg ht.le _)
    exact (not_lt_of_ge hnonpos) (hstrict i.val i.property)
  choose f hf using hpos
  have hfi : Function.Injective f := by
    intro i j he
    apply Subtype.ext
    apply fan.positive_coordinate_unique hfan b hb (a (f i)).val (a (f i)).property (hf i)
    simpa only [he] using hf j
  have hcardle : I.card ≤ k := by
    have h := Fintype.card_le_of_injective f hfi
    simpa using h
  let W := Submodule.span ℝ (Set.range (fun j => embed (a j).val))
  let S := Submodule.span ℝ (basisFace b I)
  have hWS : W ≤ S := by
    apply Submodule.span_le.mpr
    rintro y ⟨j, rfl⟩
    change embed (a j).val ∈ S
    rw [← sum_basis_realCoordinates b (embed (a j).val)]
    apply Submodule.sum_mem
    intro i _
    by_cases hi : i ∈ I
    · exact Submodule.smul_mem _ _
        (Submodule.subset_span (basis_mem_basisFace b I i hi))
    · have hz : b.repr (a j).val i = 0 := by
        by_contra hz
        exact hi ((hI i).mpr ⟨j, hz⟩)
      rw [realCoordinates_embed, hz, Int.cast_zero, zero_smul]
      exact Submodule.zero_mem _
  have hdimW : Module.finrank ℝ W = k := by
    simpa [W] using finrank_span_eq_card ha
  have hdimS : Module.finrank ℝ S = I.card := finrank_span_basisFace b I
  have hcardge : k ≤ I.card := by
    rw [← hdimW, ← hdimS]
    exact Submodule.finrank_mono hWS
  have hcard : I.card = k := le_antisymm hcardle hcardge
  refine ⟨b, hb, I, hcard, ?_⟩
  exact Submodule.eq_of_le_of_finrank_eq hWS (by rw [hdimW, hdimS, hcard])

/-- Every subspace generated by any collection of rays is the span of an actual
cone of the fan. The ray collection is arbitrary; no independence assumption is
added to the paper's assertion. -/
theorem ray_generated_subspace_is_cone_span (hfan : fan.PositiveCoordinateCriterion)
    (U : Set (Lattice n)) (hU : U ⊆ fan.rays) :
    ∃ b ∈ fan.maximal, ∃ I : Finset (Fin n),
      I.card = Module.finrank ℝ (Submodule.span ℝ (embed '' U)) ∧
      Submodule.span ℝ (embed '' U) = Submodule.span ℝ (basisFace b I) := by
  classical
  obtain ⟨f, hf, hspan, hli⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq ℝ (embed '' U)
  choose u hu he using hf
  let a := fun i => (⟨u i, hU (hu i)⟩ : {u // u ∈ fan.rays})
  have hembed : (fun i => embed (a i).val) = f := funext he
  have ha : LinearIndependent ℝ (fun i => embed (a i).val) := by
    rw [hembed]
    exact hli
  obtain ⟨b, hb, I, hcard, hW⟩ := fan.independent_ray_span_is_cone_span hfan a ha
  refine ⟨b, hb, I, hcard, ?_⟩
  rw [hembed] at hW
  exact hspan.symm.trans hW

end SmoothCompleteFan
end Unimodular

end

/-! ## ConicReduction -/

noncomputable section

namespace Unimodular.ConicReduction

open scoped BigOperators

variable {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]

/-- A nonnegative conic expression can be reduced to independent support
without increasing its total coefficient mass. No minimizer or attainment
assumption is used: each step strictly decreases the finite support. -/
theorem nonnegative_independent_reduction (v : ι → V) (c : ι → ℝ) (hc : 0 ≤ c) :
    ∃ d : ι → ℝ, 0 ≤ d ∧ Function.support d ⊆ Function.support c ∧
      (∑ j, d j • v j) = ∑ j, c j • v j ∧ (∑ j, d j) ≤ ∑ j, c j ∧
      LinearIndependent ℝ (fun j : {j // d j ≠ 0} => v j.val) := by
  classical
  have aux : ∀ m : ℕ, ∀ c : ι → ℝ, 0 ≤ c → (Function.support c).ncard = m →
      ∃ d : ι → ℝ, 0 ≤ d ∧ Function.support d ⊆ Function.support c ∧
        (∑ j, d j • v j) = ∑ j, c j • v j ∧ (∑ j, d j) ≤ ∑ j, c j ∧
        LinearIndependent ℝ (fun j : {j // d j ≠ 0} => v j.val) := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro c hc hn
      by_cases hli : LinearIndependent ℝ (fun j : {j // c j ≠ 0} => v j.val)
      · exact ⟨c, hc, Set.Subset.rfl, rfl, le_rfl, hli⟩
      obtain ⟨g, hg, j₀, hj₀⟩ := Fintype.not_linearIndependent_iff.mp hli
      let k : ι → ℝ := fun j => if h : c j ≠ 0 then g ⟨j, h⟩ else 0
      have hk : ∀ j, c j = 0 → k j = 0 := fun j h => by simp [k, h]
      have hkg : ∀ j : {j // c j ≠ 0}, k j.val = g j := fun j => by simp [k, j.property]
      have hkv : ∑ j, k j • v j = 0 := by
        rw [← Fintype.sum_of_injective Subtype.val Subtype.val_injective
          (fun j : {j // c j ≠ 0} => g j • v j.val) (fun j => k j • v j)
          (by simp +contextual [k]) (by simp [hkg])]
        exact hg
      have hk0 : k j₀.val ≠ 0 := by
        rw [hkg]
        exact hj₀
      have horient : ∃ l : ι → ℝ, (∑ j, l j • v j) = 0 ∧
          (∀ j, c j = 0 → l j = 0) ∧ 0 ≤ ∑ j, l j ∧ ∃ j, l j ≠ 0 := by
        by_cases hs : 0 ≤ ∑ j, k j
        · exact ⟨k, hkv, hk, hs, j₀.val, hk0⟩
        · refine ⟨-k, ?_, ?_, ?_, j₀.val, ?_⟩
          · simpa [Pi.neg_apply, neg_smul] using congrArg Neg.neg hkv
          · intro j hj
            simp [hk j hj]
          · simpa only [Pi.neg_apply, Finset.sum_neg_distrib, neg_nonneg] using le_of_not_ge hs
          · simpa using hk0
      obtain ⟨l, hlv, hlzero, hlsum, j₁, hj₁⟩ := horient
      have hlpos : ∃ j, 0 < l j := by
        by_contra h
        push_neg at h
        have hlt : (∑ j, l j) < ∑ _j : ι, (0 : ℝ) :=
          Finset.sum_lt_sum (fun j _ => h j)
            ⟨j₁, Finset.mem_univ _, lt_of_le_of_ne (h j₁) hj₁⟩
        simp only [Finset.sum_const_zero] at hlt
        exact (not_lt_of_ge hlsum) hlt
      obtain ⟨s, hs, hu, hsub⟩ :=
        TauCeti.exists_pos_sub_smul_nonneg_support_ssubset hc (Set.toFinite _) hlzero hlpos
      obtain ⟨d, hd, hdsupp, hdv, hdmass, hdli⟩ :=
        ih _ (by rw [← hn]; exact Set.ncard_lt_ncard hsub (Set.toFinite _))
          (c - s • l) hu rfl
      have huvalue : (∑ j, (c - s • l) j • v j) = ∑ j, c j • v j := by
        simp [Pi.sub_apply, Pi.smul_apply, sub_smul, mul_smul,
          Finset.sum_sub_distrib, ← Finset.smul_sum, hlv]
      have humass : (∑ j, (c - s • l) j) ≤ ∑ j, c j := by
        simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib,
          ← Finset.mul_sum]
        exact sub_le_self _ (mul_nonneg hs.le hlsum)
      exact ⟨d, hd, hdsupp.trans hsub.subset, hdv.trans huvalue, hdmass.trans humass, hdli⟩
  exact aux _ c hc rfl

/-- Every point of a convex hull has an independent positive conic expression
using the original set and with coefficient sum at most one. -/
theorem independent_conic_expression {S : Set V} {x : V}
    (hx : x ∈ convexHull ℝ S) :
    ∃ (κ : Type) (_ : Fintype κ) (v : κ → V) (c : κ → ℝ),
      Set.range v ⊆ S ∧ LinearIndependent ℝ v ∧ (∀ j, 0 < c j) ∧
      (∑ j, c j) ≤ 1 ∧ (∑ j, c j • v j) = x := by
  classical
  obtain ⟨κ, hκ, c, v, hc, hc1, hv, hcv⟩ := mem_convexHull_iff_exists_fintype.mp hx
  letI := hκ
  obtain ⟨d, hd, _, hdv, hdmass, hli⟩ := nonnegative_independent_reduction v c hc
  let τ := {j : κ // d j ≠ 0}
  have hmass : (∑ j : τ, d j.val) = ∑ j : κ, d j := by
    exact Fintype.sum_of_injective Subtype.val Subtype.val_injective
      (fun j : τ => d j.val) d (by simp +contextual) (by simp)
  have hvalue : (∑ j : τ, d j.val • v j.val) = ∑ j : κ, d j • v j := by
    exact Fintype.sum_of_injective Subtype.val Subtype.val_injective
      (fun j : τ => d j.val • v j.val) (fun j => d j • v j)
      (by simp +contextual) (by simp)
  refine ⟨τ, inferInstance, (fun j => v j.val), (fun j => d j.val), ?_, hli,
    (fun j => lt_of_le_of_ne (hd j.val) (Ne.symm j.property)), ?_, ?_⟩
  · rintro y ⟨j, rfl⟩
    exact hv j.val
  · rw [hmass]
    exact hdmass.trans hc1.le
  · rw [hvalue, hdv]
    exact hcv

end Unimodular.ConicReduction

end

/-! ## LatticeHull -/

noncomputable section

namespace Unimodular.LatticeHull

open scoped BigOperators

variable {n : ℕ}

theorem embed_injective : Function.Injective (embed : Lattice n → Ambient n) := by
  intro x y he
  ext i
  have hi := congrFun he i
  simp only [embed] at hi
  exact Int.cast_injective hi

/-- Full-rank uniform unimodularity saturates every independent ray subset:
it extends to an actual integral basis consisting of rays of the same system. -/
theorem exists_lattice_basis_extension (U : Set (Lattice n))
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) (fun u : U => u.val))
    (hspan : Submodule.span ℝ (embed '' U) = ⊤)
    {κ : Type*} (a : κ → U)
    (ha : LinearIndependent ℝ (fun j => embed (a j).val)) :
    ∃ b : Module.Basis (Fin n) ℤ (Lattice n),
      (∀ i, b i ∈ U) ∧ ∀ j, ∃ i, b i = (a j).val := by
  classical
  let v := fun j => embed (a j).val
  have hv : Set.range v ⊆ embed '' U := by
    rintro x ⟨j, rfl⟩
    exact ⟨(a j).val, (a j).property, rfl⟩
  have htop : ⊤ ≤ Submodule.span ℝ (embed '' U) := hspan.ge
  let B := Module.Basis.extendLe ha.linearIndepOn_id hv htop
  let e := B.indexEquiv (Pi.basisFun ℝ (Fin n))
  let B' := B.reindex e
  have hB' : Set.range B' ⊆ embed '' U := by
    rw [show Set.range B' = Set.range B from B.range_reindex e]
    exact Module.Basis.extendLe_subset ha.linearIndepOn_id hv htop
  have hvB' : Set.range v ⊆ Set.range B' := by
    rw [show Set.range B' = Set.range B from B.range_reindex e]
    exact Module.Basis.subset_extendLe ha.linearIndepOn_id hv htop
  have hcol : ∀ i : Fin n, ∃ u ∈ U, embed u = B' i :=
    fun i => hB' ⟨i, rfl⟩
  choose u hu heu using hcol
  let a' : Fin n → U := fun i => ⟨u i, hu i⟩
  have hembed : (fun i => embed (a' i).val) = B' := funext heu
  have ha' : LinearIndependent ℝ (fun i => embed (a' i).val) := by
    rw [hembed]
    exact B'.linearIndependent
  obtain ⟨b, hb⟩ := (uniform_iff_real_independent_is_basis
    (fun u : U => u.val)).mp hU a' ha'
  refine ⟨b, ?_, ?_⟩
  · intro i
    rw [hb i]
    exact hu i
  intro j
  obtain ⟨i, hi⟩ := hvB' ⟨j, rfl⟩
  refine ⟨i, embed_injective ?_⟩
  rw [hb i, heu i, hi]

/-- The only lattice points in a simplex cut from an integral basis and the
origin are its vertices. This statement keeps the actual ambient lattice and
real nonnegative coefficients. -/
theorem small_basis_combination {κ : Type*} [Fintype κ]
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (s : κ → Fin n)
    (hs : Function.Injective s) (c : κ → ℝ) (hc : 0 ≤ c)
    (hmass : (∑ j, c j) ≤ 1) (x : Lattice n)
    (he : (∑ j, c j • embed (b (s j))) = embed x) :
    x = 0 ∨ ∃ j, x = b (s j) := by
  classical
  have hcoord (j : κ) : c j = (b.repr x (s j) : ℝ) := by
    have h := congrArg (fun z => realCoordinates b z (s j)) he
    simp only [map_sum, map_smul, realCoordinates_basis, Finset.sum_apply,
      Pi.smul_apply, smul_eq_mul, realCoordinates_embed] at h
    rw [Finset.sum_eq_single j] at h
    · simpa only [Pi.single_eq_same, mul_one] using h
    · intro i _ hij
      have hne : s i ≠ s j := fun he => hij (hs he)
      simp [Pi.single_apply, hne, Ne.symm hne]
    · simp
  by_cases hz : ∀ j, c j = 0
  · left
    apply embed_injective
    have hx : embed x = 0 := by simpa [hz] using he.symm
    rw [hx]
    ext i
    simp [embed]
  · push_neg at hz
    obtain ⟨j, hj⟩ := hz
    have hcpos : 0 < c j := lt_of_le_of_ne (hc j) (Ne.symm hj)
    have hzpos : 0 < b.repr x (s j) := by
      rw [hcoord j] at hcpos
      exact_mod_cast hcpos
    have hge : (1 : ℝ) ≤ c j := by
      rw [hcoord j]
      exact_mod_cast (show (1 : ℤ) ≤ b.repr x (s j) by omega)
    have hle : c j ≤ 1 :=
      (Finset.single_le_sum (fun i _ => hc i) (Finset.mem_univ j)).trans hmass
    have hcj : c j = 1 := le_antisymm hle hge
    have hother (i : κ) (hij : i ≠ j) : c i = 0 := by
      have hpair : c i + c j ≤ ∑ q, c q := by
        calc
          c i + c j = ∑ q ∈ ({i, j} : Finset κ), c q := by simp [hij]
          _ ≤ ∑ q, c q := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun q _ _ => hc q)
      have hi0 : 0 ≤ c i := hc i
      linarith
    right
    refine ⟨j, embed_injective ?_⟩
    rw [Finset.sum_eq_single j] at he
    · simpa [hcj] using he.symm
    · intro i _ hij
      rw [hother i hij, zero_smul]
    · simp

/-- The lattice-point assertion in Lemma 3.2. It holds for every spanning
uniformly unimodular ray set, even before positive spanning is imposed. -/
theorem latticePoint_convexHull_eq_zero_or_mem (U : Set (Lattice n))
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) (fun u : U => u.val))
    (hspan : Submodule.span ℝ (embed '' U) = ⊤)
    (x : Lattice n) (hx : embed x ∈ convexHull ℝ (embed '' U)) :
    x = 0 ∨ x ∈ U := by
  classical
  obtain ⟨κ, hκ, v, c, hv, hli, hc, hmass, hcombo⟩ :=
    ConicReduction.independent_conic_expression hx
  letI := hκ
  have hu : ∀ j : κ, ∃ u ∈ U, embed u = v j := fun j => hv ⟨j, rfl⟩
  choose u hu heu using hu
  let a : κ → U := fun j => ⟨u j, hu j⟩
  have hembed : (fun j => embed (a j).val) = v := funext heu
  have ha : LinearIndependent ℝ (fun j => embed (a j).val) := by
    rw [hembed]
    exact hli
  obtain ⟨b, hbU, hba⟩ := exists_lattice_basis_extension U hU hspan a ha
  choose s hs using hba
  have hsi : Function.Injective s := by
    intro i j hij
    apply hli.injective
    rw [← heu i, ← heu j]
    exact congrArg embed ((hs i).symm.trans ((congrArg b hij).trans (hs j)))
  have hcomb : (∑ j, c j • embed (b (s j))) = embed x := by
    calc
      _ = ∑ j, c j • v j := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hs j]
        change c j • embed (u j) = c j • v j
        rw [heu j]
      _ = embed x := hcombo
  rcases small_basis_combination b s hsi c (fun j => (hc j).le) hmass x hcomb with h | ⟨j, hj⟩
  · exact Or.inl h
  · exact Or.inr (hj ▸ hbU (s j))

end Unimodular.LatticeHull

end

/-! ## TerminalHull -/

noncomputable section

namespace Unimodular.LatticeHull

open scoped BigOperators

variable {n : ℕ}

/-- Removing a nonzero ray from a spanning uniformly unimodular set removes it
from the convex hull. The proof does not assume that the rays are already
vertices. -/
theorem ray_not_mem_convexHull_others (U : Set (Lattice n))
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) (fun u : U => u.val))
    (hspan : Submodule.span ℝ (embed '' U) = ⊤)
    (u : Lattice n) (hu : u ≠ 0) :
    embed u ∉ convexHull ℝ (embed '' (U \ {u})) := by
  intro hx
  have hsmall : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun v : (U \ {u} : Set (Lattice n)) => v.val) := by
    intro a
    exact hU (fun i => ⟨(a i).val, (a i).property.1⟩)
  have hspan' : Submodule.span ℝ (embed '' (U \ {u})) = ⊤ := by
    apply top_unique
    rw [← hspan]
    apply Submodule.span_le.mpr
    rintro x ⟨v, hv, rfl⟩
    by_cases he : v = u
    · subst v
      exact convexHull_min Submodule.subset_span (Submodule.convex _) hx
    · exact Submodule.subset_span ⟨v, ⟨hv, he⟩, rfl⟩
  rcases latticePoint_convexHull_eq_zero_or_mem (U \ {u}) hsmall hspan' u hx with h | h
  · exact hu h
  · exact h.2 rfl

/-- A linear functional with a unique maximum on the generating set has the
same unique maximum on its convex hull. The finite convex-combination proof is
valid even when the generating set is infinite. -/
theorem unique_max_convexHull {V : Type*} [AddCommGroup V] [Module ℝ V]
    (S : Set V) (u : V) (f : V →ₗ[ℝ] ℝ)
    (hbound : ∀ v ∈ S, f v ≤ f u)
    (hunique : ∀ v ∈ S, f v = f u → v = u)
    (x : V) (hx : x ∈ convexHull ℝ S) (he : f x = f u) : x = u := by
  classical
  obtain ⟨κ, hκ, w, v, hw, hw1, hv, hcombo⟩ := mem_convexHull_iff_exists_fintype.mp hx
  letI := hκ
  have hgap (i : κ) : 0 ≤ w i * (f u - f (v i)) :=
    mul_nonneg (hw i) (sub_nonneg.mpr (hbound _ (hv i)))
  have hsum : (∑ i, w i * (f u - f (v i))) = 0 := by
    have h := congrArg f hcombo
    simp only [map_sum, map_smul, smul_eq_mul] at h
    simp_rw [mul_sub]
    rw [Finset.sum_sub_distrib, ← Finset.sum_mul, hw1, one_mul, h, he, sub_self]
  have hterm (i : κ) : w i • v i = w i • u := by
    by_cases hz : w i = 0
    · simp [hz]
    · have hle : w i * (f u - f (v i)) ≤ 0 := by
        rw [← hsum]
        exact Finset.single_le_sum (fun j _ => hgap j) (Finset.mem_univ i)
      have hzero : w i * (f u - f (v i)) = 0 := le_antisymm hle (hgap i)
      have hval : f (v i) = f u := by
        have := (mul_eq_zero.mp hzero).resolve_left hz
        linarith
      rw [hunique _ (hv i) hval]
  calc
    x = ∑ i, w i • v i := hcombo.symm
    _ = ∑ i, w i • u := Finset.sum_congr rfl (fun i _ => hterm i)
    _ = (∑ i, w i) • u := Finset.sum_smul.symm
    _ = u := by rw [hw1, one_smul]

/-- Every ray is an actual extreme point of its finite convex hull. In
particular, the assertion that the prescribed rays are vertices of the seed
polytope is derived from uniform unimodularity rather than assumed. -/
theorem ray_mem_extremePoints (U : Set (Lattice n)) (hfin : U.Finite)
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) (fun u : U => u.val))
    (hspan : Submodule.span ℝ (embed '' U) = ⊤)
    (u : Lattice n) (hu : u ∈ U) (hu0 : u ≠ 0) :
    embed u ∈ (convexHull ℝ (embed '' U)).extremePoints ℝ := by
  classical
  have hnot := ray_not_mem_convexHull_others U hU hspan u hu0
  obtain ⟨f, c, hf, hfu⟩ := geometric_hahn_banach_closed_point
    (convex_convexHull ℝ _) (((hfin.subset Set.diff_subset).image embed).isClosed_convexHull ℝ) hnot
  have hbound : ∀ v ∈ embed '' U, f v ≤ f (embed u) := by
    rintro v ⟨v, hv, rfl⟩
    by_cases he : v = u
    · simp [he]
    · exact ((hf _ (subset_convexHull ℝ _ ⟨v, ⟨hv, he⟩, rfl⟩)).trans hfu).le
  have huniq : ∀ v ∈ embed '' U, f v = f (embed u) → v = embed u := by
    rintro v ⟨v, hv, rfl⟩ he
    by_contra h
    have hvu : v ≠ u := fun h' => h (congrArg embed h')
    have hlt := (hf _ (subset_convexHull ℝ _ ⟨v, ⟨hv, hvu⟩, rfl⟩)).trans hfu
    exact (ne_of_lt hlt) he
  have hfull : ∀ x ∈ convexHull ℝ (embed '' U), f x ≤ f (embed u) := by
    intro x hx
    change x ∈ {y | f y ≤ f (embed u)}
    apply convexHull_min (show embed '' U ⊆ {y | f y ≤ f (embed u)} from hbound) _ hx
    intro y hy z hz a b ha hb hab
    change f (a • y + b • z) ≤ f (embed u)
    rw [map_add, map_smul, map_smul]
    change a * f y + b * f z ≤ f (embed u)
    calc
      _ ≤ a * f (embed u) + b * f (embed u) :=
        add_le_add (mul_le_mul_of_nonneg_left hy ha) (mul_le_mul_of_nonneg_left hz hb)
      _ = f (embed u) := by rw [← add_mul, hab, one_mul]
  refine ⟨subset_convexHull ℝ _ ⟨u, hu, rfl⟩, ?_⟩
  rintro x hx y hy ⟨a, b, ha, hb, hab, he⟩
  have h := congrArg f he
  simp only [map_add, map_smul, smul_eq_mul] at h
  have hfx : f x = f (embed u) := by
    have hs : a * f (embed u) + b * f (embed u) = f (embed u) := by
      rw [← add_mul, hab, one_mul]
    have hp : 0 ≤ a * (f (embed u) - f x) :=
      mul_nonneg ha.le (sub_nonneg.mpr (hfull x hx))
    have hq : 0 ≤ b * (f (embed u) - f y) :=
      mul_nonneg hb.le (sub_nonneg.mpr (hfull y hy))
    have hzero : a * (f (embed u) - f x) = 0 := by nlinarith
    have := (mul_eq_zero.mp hzero).resolve_left (ne_of_gt ha)
    linarith
  exact unique_max_convexHull _ _ f.toLinearMap hbound huniq x hx hfx

theorem extremePoints_convexHull_eq_rays (U : Set (Lattice n)) (hfin : U.Finite)
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) (fun u : U => u.val))
    (hspan : Submodule.span ℝ (embed '' U) = ⊤) (hzero : 0 ∉ U) :
    (convexHull ℝ (embed '' U)).extremePoints ℝ = embed '' U := by
  apply Set.Subset.antisymm extremePoints_convexHull_subset
  rintro x ⟨u, hu, rfl⟩
  exact ray_mem_extremePoints U hfin hU hspan u hu (fun h => hzero (h ▸ hu))

end Unimodular.LatticeHull

end

/-! ## Reflexivity -/

noncomputable section

namespace Unimodular

open scoped BigOperators

theorem realPairing_comm {n : ℕ} (x y : Ambient n) :
    realPairing x y = realPairing y x := by
  simp only [realPairing, mul_comm]

/-- The ordinary real polar, with the origin and lattice unchanged. -/
def realPolar {n : ℕ} (P : Set (Ambient n)) : Set (Ambient n) :=
  {y | ∀ p ∈ P, realPairing p y ≤ 1}

namespace SmoothReflexivePresentation

variable {n : ℕ} (P : SmoothReflexivePresentation n)

/-- The polar is a genuine lattice polytope. Inserting the origin also covers
rank zero, in which the facet set is empty. The proof uses real separation, not
an assumed combinatorial duality. -/
theorem realPolar_eq_convexHull_normals :
    realPolar P.carrier =
      convexHull ℝ (embed '' (insert 0 (P.normals : Set (Lattice n)))) := by
  classical
  let S : Set (Ambient n) := embed '' (insert 0 (P.normals : Set (Lattice n)))
  have hS : S.Finite := (P.normals.finite_toSet.insert 0).image embed
  have hzero : (0 : Ambient n) ∈ S := by
    refine ⟨0, Set.mem_insert _ _, ?_⟩
    ext i
    simp [embed]
  apply Set.Subset.antisymm
  · intro y hy
    by_contra hnot
    obtain ⟨f, c, hf, hfy⟩ := geometric_hahn_banach_closed_point
      (convex_convexHull ℝ S) (hS.isClosed_convexHull ℝ) hnot
    have hc : 0 < c := by
      simpa using hf 0 (subset_convexHull ℝ S hzero)
    let z : Ambient n := fun j => f (Pi.single j 1)
    let p : Ambient n := c⁻¹ • z
    have hpair (x : Ambient n) : realPairing p x = c⁻¹ * f x := by
      rw [realPairing_smul_left, realPairing_comm]
      congr 1
      exact (linearMap_eq_realPairing f.toLinearMap x).symm
    have hp : p ∈ P.carrier := by
      apply (P.mem_carrier_iff p).mpr
      intro u hu
      change realPairing p (embed u) ≤ 1
      rw [hpair]
      have hu' := hf (embed u) (subset_convexHull ℝ S
        ⟨u, Set.mem_insert_of_mem _ hu, rfl⟩)
      calc
        c⁻¹ * f (embed u) ≤ c⁻¹ * c :=
          mul_le_mul_of_nonneg_left hu'.le (inv_nonneg.mpr hc.le)
        _ = 1 := inv_mul_cancel₀ hc.ne'
    have hb := hy p hp
    rw [hpair] at hb
    have hlt : 1 < c⁻¹ * f y := by
      calc
        1 = c⁻¹ * c := (inv_mul_cancel₀ hc.ne').symm
        _ < c⁻¹ * f y := mul_lt_mul_of_pos_left hfy (inv_pos.mpr hc)
    exact (not_lt_of_ge hb) hlt
  · apply convexHull_min
    · rintro y ⟨u, hu, rfl⟩ p hp
      rcases hu with rfl | hu
      · simp [realPairing, embed]
      · exact (P.mem_carrier_iff p).mp hp u hu
    · intro x hx y hy a b ha hb hab p hp
      rw [realPairing_comm p, realPairing_add_left,
        realPairing_smul_left, realPairing_smul_left,
        realPairing_comm x p, realPairing_comm y p]
      calc
        _ ≤ a * 1 + b * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left (hx p hp) ha)
            (mul_le_mul_of_nonneg_left (hy p hp) hb)
        _ = 1 := by simpa using hab

/-- Explicit intrinsic checks for the chosen presentation: the origin lies in
the real interior and both the polytope and its polar are convex hulls of
finite sets of actual lattice points. -/
theorem geometric_reflexivity :
    (0 : Ambient n) ∈ interior P.carrier ∧
    (∃ V : Finset (Lattice n), P.carrier = convexHull ℝ (embed '' (V : Set (Lattice n)))) ∧
    (∃ W : Finset (Lattice n), realPolar P.carrier =
      convexHull ℝ (embed '' (W : Set (Lattice n)))) := by
  refine ⟨P.zero_mem_interior_carrier, ⟨P.vertices, rfl⟩, insert 0 P.normals, ?_⟩
  simpa only [Finset.coe_insert] using P.realPolar_eq_convexHull_normals

end SmoothReflexivePresentation
end Unimodular

end

/-! ## SegmentSimplex -/

noncomputable section

namespace Unimodular.SegmentSimplex

open scoped BigOperators

/-- The six actual outward normals in Proposition 5.4. -/
def normal : Fin 6 → Lattice 4 :=
  ![![1, 0, 0, 0], ![0, 1, 0, 0], ![0, 0, 1, 0],
    ![-1, -1, -1, 2], ![0, 0, 0, 1], ![0, 0, 0, -1]]

def height (b : Bool) : ℤ := if b then 1 else -1

/-- Both end tetrahedra, including their common vertical corner. -/
def vertex (t : Bool × Fin 4) : Lattice 4 :=
  ![1 - if t.2 = 0 then 4 - 2 * height t.1 else 0,
    1 - if t.2 = 1 then 4 - 2 * height t.1 else 0,
    1 - if t.2 = 2 then 4 - 2 * height t.1 else 0,
    height t.1]

def active (t : Bool × Fin 4) : Fin 4 → Lattice 4 :=
  ![if t.2 = 0 then normal 3 else normal 0,
    if t.2 = 1 then normal 3 else normal 1,
    if t.2 = 2 then normal 3 else normal 2,
    if t.1 then normal 4 else normal 5]

def normals : Finset (Lattice 4) := Finset.univ.image normal
def vertices : Finset (Lattice 4) := Finset.univ.image vertex

/-- This is the displayed real polytope, with every inequality retained. -/
def Q : Set (Ambient 4) :=
  {x | -1 ≤ x 3 ∧ x 3 ≤ 1 ∧ x 0 ≤ 1 ∧ x 1 ≤ 1 ∧ x 2 ≤ 1 ∧
    -x 0 - x 1 - x 2 + 2 * x 3 ≤ 1}

theorem mem_Q_iff (x : Ambient 4) :
    x ∈ Q ↔ ∀ u ∈ normals, pairing x u ≤ 1 := by
  have he : (∀ u ∈ normals, pairing x u ≤ 1) ↔
      ∀ i : Fin 6, pairing x (normal i) ≤ 1 := by
    simp [normals]
  rw [he]
  constructor
  · rintro ⟨hz0,hz1,h0,h1,h2,hs⟩ i
    fin_cases i <;> norm_num [normal,pairing,Fin.sum_univ_succ] <;> linarith
  · intro h
    have h0 := h 0
    have h1 := h 1
    have h2 := h 2
    have h3 := h 3
    have h4 := h 4
    have h5 := h 5
    norm_num [normal,pairing,Fin.sum_univ_succ] at h0 h1 h2 h3 h4 h5
    exact ⟨by linarith,h4,h0,h1,h2,by linarith⟩

theorem vertex_mem_Q (t : Bool × Fin 4) : embed (vertex t) ∈ Q := by
  rcases t with ⟨b,k⟩
  cases b <;> fin_cases k <;>
    norm_num [Q, vertex, height, embed]

theorem active_pairing (t : Bool × Fin 4) (i : Fin 4) :
    pairing (embed (vertex t)) (active t i) = 1 := by
  rcases t with ⟨b,k⟩
  cases b <;> fin_cases k <;> fin_cases i <;>
    norm_num [vertex, height, active, normal, pairing, embed, Fin.sum_univ_succ]

theorem active_mem (t : Bool × Fin 4) (i : Fin 4) : active t i ∈ normals := by
  rcases t with ⟨b,k⟩
  cases b <;> fin_cases k <;> fin_cases i <;>
    simp [active, normals]

theorem all_active (t : Bool × Fin 4) (i : Fin 6)
    (hi : pairing (embed (vertex t)) (normal i) = 1) :
    ∃ j : Fin 4, active t j = normal i := by
  rcases t with ⟨b,k⟩
  cases b <;> fin_cases k <;> fin_cases i <;>
    norm_num [vertex, height, normal, pairing, embed, Fin.sum_univ_succ] at hi <;>
    first | exact ⟨0, rfl⟩ | exact ⟨1, rfl⟩ | exact ⟨2, rfl⟩ | exact ⟨3, rfl⟩

theorem active_isUnit_det (t : Bool × Fin 4) :
    IsUnit ((Pi.basisFun ℤ (Fin 4)).det (active t)) := by
  rw [Pi.basisFun_det_apply]
  rcases t with ⟨b,k⟩
  cases b <;> fin_cases k <;>
    norm_num [Int.isUnit_iff, active, normal, Matrix.det_succ_row_zero, Fin.sum_univ_succ,
      Matrix.submatrix_apply, Matrix.of_apply]

noncomputable def localBasis (t : Bool × Fin 4) : Module.Basis (Fin 4) ℤ (Lattice 4) :=
  Module.Basis.mk ((Pi.basisFun ℤ (Fin 4)).is_basis_iff_det.mpr (active_isUnit_det t)).1
    ((Pi.basisFun ℤ (Fin 4)).is_basis_iff_det.mpr (active_isUnit_det t)).2.ge

@[simp] theorem localBasis_apply (t : Bool × Fin 4) (i : Fin 4) :
    localBasis t i = active t i := Module.Basis.mk_apply _ _ _

theorem normals_occur (u : Lattice 4) (hu : u ∈ normals) :
    ∃ t : Bool × Fin 4, ∃ i : Fin 4, active t i = u := by
  obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
  fin_cases i
  · exact ⟨(true,3),0,rfl⟩
  · exact ⟨(true,3),1,rfl⟩
  · exact ⟨(true,3),2,rfl⟩
  · exact ⟨(true,0),0,rfl⟩
  · exact ⟨(true,3),3,rfl⟩
  · exact ⟨(false,3),3,rfl⟩

theorem Q_convex : Convex ℝ Q := by
  intro x hx y hy a b ha hb hab
  apply (mem_Q_iff _).mpr
  intro u hu
  rw [pairing_add_left, pairing_smul_left, pairing_smul_left]
  calc
    _ ≤ a * 1 + b * 1 := add_le_add
      (mul_le_mul_of_nonneg_left ((mem_Q_iff x).mp hx u hu) ha)
      (mul_le_mul_of_nonneg_left ((mem_Q_iff y).mp hy u hu) hb)
    _ = 1 := by simpa using hab

theorem hull_eq_Q : convexHull ℝ (embed '' (vertices : Set (Lattice 4))) = Q := by
  apply Set.Subset.antisymm
  · apply convexHull_min _ Q_convex
    rintro x ⟨v,hv,rfl⟩
    obtain ⟨t,_,rfl⟩ := Finset.mem_image.mp hv
    exact vertex_mem_Q t
  · intro x hx
    rcases hx with ⟨hz0,hz1,hx0,hx1,hx2,hsum⟩
    let c : ℝ := 4 - 2 * x 3
    have hc : 0 < c := by dsimp [c]; linarith
    let a : Fin 4 → ℝ :=
      ![(1-x 0)/c,(1-x 1)/c,(1-x 2)/c,1-((1-x 0)+(1-x 1)+(1-x 2))/c]
    have ha : ∀ i, 0 ≤ a i := by
      intro i
      fin_cases i
      · exact div_nonneg (sub_nonneg.mpr hx0) hc.le
      · exact div_nonneg (sub_nonneg.mpr hx1) hc.le
      · exact div_nonneg (sub_nonneg.mpr hx2) hc.le
      · change 0 ≤ 1 - ((1-x 0)+(1-x 1)+(1-x 2))/c
        apply sub_nonneg.mpr
        apply (div_le_one hc).mpr
        dsimp [c]
        linarith
    have ha1 : ∑ i, a i = 1 := by
      simp [a, Fin.sum_univ_succ]
      ring
    let p : Bool → Ambient 4 := fun b => ∑ i : Fin 4, a i • embed (vertex (b,i))
    have hp (b : Bool) : p b ∈ convexHull ℝ (embed '' (vertices : Set (Lattice 4))) := by
      apply mem_convexHull_of_exists_fintype a (fun i => embed (vertex (b,i))) ha ha1
      · intro i
        exact ⟨vertex (b,i), Finset.mem_image.mpr ⟨(b,i),Finset.mem_univ _,rfl⟩,rfl⟩
      · rfl
    let t : ℝ := (x 3 + 1)/2
    have ht0 : 0 ≤ t := by dsimp [t]; linarith
    have ht1 : t ≤ 1 := by dsimp [t]; linarith
    have he : (1-t) • p false + t • p true = x := by
      ext i
      fin_cases i <;>
        simp [p, a, t, vertex, height, embed, Fin.sum_univ_succ,
          Finset.sum_apply, Pi.smul_apply] <;>
        field_simp [hc.ne'] <;> dsimp [c] <;> ring
    rw [← he]
    exact (convex_convexHull ℝ _) (hp false) (hp true)
      (sub_nonneg.mpr ht1) ht0 (sub_add_cancel _ _)

noncomputable def vertexIndex (v : {v // v ∈ vertices}) : Bool × Fin 4 :=
  Classical.choose (Finset.mem_image.mp v.property)

theorem vertexIndex_spec (v : {v // v ∈ vertices}) : vertex (vertexIndex v) = v.val :=
  (Classical.choose_spec (Finset.mem_image.mp v.property)).2

noncomputable def presentation : SmoothReflexivePresentation 4 where
  vertices := vertices
  normals := normals
  vertices_nonempty := ⟨vertex (true,3), Finset.mem_image.mpr ⟨(true,3),by simp,rfl⟩⟩
  basis v := localBasis (vertexIndex v)
  basis_mem v i := by rw [localBasis_apply]; exact active_mem _ _
  basis_active v i := by
    rw [localBasis_apply, ← vertexIndex_spec v]
    exact active_pairing _ _
  active_subset v u hu he := by
    obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hu
    rw [← vertexIndex_spec v] at he
    obtain ⟨j,hj⟩ := all_active (vertexIndex v) i he
    exact ⟨j, (localBasis_apply _ _).trans hj⟩
  normals_occur u hu := by
    obtain ⟨t,i,hi⟩ := normals_occur u hu
    let v : {v // v ∈ vertices} :=
      ⟨vertex t, Finset.mem_image.mpr ⟨t,Finset.mem_univ _,rfl⟩⟩
    obtain ⟨k,_,hk⟩ := Finset.mem_image.mp hu
    have he : pairing (embed v.val) (normal k) = 1 := by
      rw [hk,← hi]
      exact active_pairing t i
    obtain ⟨j,hj⟩ := all_active (vertexIndex v) k
      (by rw [vertexIndex_spec]; exact he)
    exact ⟨v,j,(localBasis_apply _ _).trans (hj.trans hk)⟩
  hull_eq := hull_eq_Q.trans (Set.ext mem_Q_iff)

theorem presentation_carrier : presentation.carrier = Q := hull_eq_Q

/-- Every original coordinate of every genuine vertex is odd. -/
theorem vertex_odd (t : Bool × Fin 4) (i : Fin 4) : vertex t i % 2 = 1 := by
  rcases t with ⟨b,k⟩
  cases b <;> fin_cases k <;> fin_cases i <;> norm_num [vertex,height]

/-- The precise full determinant obstruction stated in the paper. -/
theorem obstructing_det :
    (Pi.basisFun ℤ (Fin 4)).det (fun i : Fin 4 => normal (Fin.castLE (by decide) i)) = 2 := by
  rw [Pi.basisFun_det_apply]
  norm_num [normal, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Matrix.submatrix_apply, Matrix.of_apply]

theorem normals_not_uniform :
    ¬ IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin 4))
      (fun u : {u // u ∈ normals} => u.val) := by
  intro h
  let a : Fin 4 → {u // u ∈ normals} := fun i =>
    ⟨normal (Fin.castLE (by decide) i), Finset.mem_image.mpr
      ⟨Fin.castLE (by decide) i,Finset.mem_univ _,rfl⟩⟩
  have hb := h a
  change |(Pi.basisFun ℤ (Fin 4)).det
    (fun i : Fin 4 => normal (Fin.castLE (by decide) i))| ≤ 1 at hb
  rw [obstructing_det] at hb
  norm_num at hb

/-- The integral lattice in an actual real vector subspace. -/
def integralSubspace {n : ℕ} (W : Submodule ℝ (Ambient n)) : Submodule ℤ (Lattice n) where
  carrier := {x | embed x ∈ W}
  zero_mem' := by
    change embed (0 : Lattice n) ∈ W
    have he : embed (0 : Lattice n) = 0 := by ext i; simp [embed]
    rw [he]
    exact W.zero_mem
  add_mem' := by
    intro x y hx hy
    change embed (x+y) ∈ W
    have he : embed (x+y) = embed x + embed y := by ext i; simp [embed]
    rw [he]
    exact W.add_mem hx hy
  smul_mem' := by
    intro k x hx
    change embed (k • x) ∈ W
    have he : embed (k • x) = (k : ℝ) • embed x := by
      ext i
      simp [embed,Pi.smul_apply,smul_eq_mul]
    rw [he]
    exact W.smul_mem (k : ℝ) hx

/-- A basis vector of the full lattice in a real subspace is primitive in the
ambient lattice as well. The saturation is proved by real division. -/
theorem integralSubspace_basis_primitive {n : ℕ} {ι : Type*}
    (W : Submodule ℝ (Ambient n)) (B : Module.Basis ι ℤ (integralSubspace W)) (i : ι) :
    PrimitiveLatticeVector (B i).val := by
  classical
  intro k z he
  have hk : k ≠ 0 := by
    intro hk
    rw [hk,zero_smul] at he
    exact B.ne_zero i (Subtype.ext he)
  have hkR : (k : ℝ) ≠ 0 := by exact_mod_cast hk
  have hze : embed (B i).val = (k : ℝ) • embed z := by
    rw [he]
    ext j
    simp [embed,Pi.smul_apply,smul_eq_mul]
  have hzW : embed z ∈ W := by
    have hmem : embed (B i).val ∈ W := (B i).property
    rw [hze] at hmem
    have h := W.smul_mem ((k : ℝ)⁻¹) hmem
    simpa only [smul_smul,inv_mul_cancel₀ hkR,one_smul] using h
  have he' : B i = k • (⟨z,hzW⟩ : integralSubspace W) := Subtype.ext he
  have h := congrArg (fun v => B.repr v i) he'
  have hm : (1 : ℤ) = k * B.repr (⟨z,hzW⟩ : integralSubspace W) i := by
    simpa only [Module.Basis.repr_self,Finsupp.single_eq_same,map_smulₛₗ,
      RingHom.id_apply,Finsupp.smul_apply,smul_eq_mul] using h
  exact IsUnit.of_mul_eq_one _ hm.symm

/-- A geometric unimodular triangle has three actual vertices and its two
edge differences form a basis of the full integral lattice of its plane. -/
def IsUnimodularTriangle {n : ℕ} (E : Set (Ambient n)) : Prop :=
  ∃ a b c : Lattice n,
    embed a ∈ E.extremePoints ℝ ∧ embed b ∈ E.extremePoints ℝ ∧
    embed c ∈ E.extremePoints ℝ ∧
    E = convexHull ℝ ({embed a,embed b,embed c} : Set (Ambient n)) ∧
    ∃ B : Module.Basis (Fin 2) ℤ (integralSubspace (vectorSpan ℝ E)),
      (B 0).val = b-a ∧ (B 1).val = c-a

theorem unimodular_triangle_has_primitive_edge {n : ℕ} {E : Set (Ambient n)}
    (hE : IsUnimodularTriangle E) :
    ∃ a b : Lattice n, embed a ∈ E.extremePoints ℝ ∧
      embed b ∈ E.extremePoints ℝ ∧ PrimitiveLatticeVector (b-a) := by
  obtain ⟨a,b,c,ha,hb,hc,he,B,hB0,hB1⟩ := hE
  refine ⟨a,b,ha,hb,?_⟩
  rw [← hB0]
  exact integralSubspace_basis_primitive _ B 0

theorem vertex_difference_even (s t : Bool × Fin 4) :
    ∃ w : Lattice 4, vertex t - vertex s = (2 : ℤ) • w := by
  let w : Lattice 4 := fun i => (vertex t i - vertex s i) / 2
  refine ⟨w,?_⟩
  ext i
  have hs := vertex_odd s i
  have ht := vertex_odd t i
  change vertex t i - vertex s i = 2 * ((vertex t i - vertex s i) / 2)
  omega

/-- Every two-dimensional face of the displayed polytope fails to be a
unimodular triangle. The proof uses actual extreme points and full lattice
primitivity, not a combinatorial assertion about its face type. -/
theorem Q_UT_free (E : Set (Ambient 4))
    (hE : IsExtreme ℝ Q E) : ¬ IsUnimodularTriangle E := by
  intro htri
  obtain ⟨a,b,ha,hb,hprim⟩ := unimodular_triangle_has_primitive_edge htri
  have hvertices : Q.extremePoints ℝ = embed '' (vertices : Set (Lattice 4)) := by
    rw [← presentation_carrier]
    exact presentation.extremePoints_eq_vertices
  have haQ := hE.extremePoints_subset_extremePoints ha
  have hbQ := hE.extremePoints_subset_extremePoints hb
  rw [hvertices] at haQ hbQ
  obtain ⟨a',ha',hea⟩ := haQ
  obtain ⟨b',hb',heb⟩ := hbQ
  have ea : a' = a := LatticeHull.embed_injective hea
  have eb : b' = b := LatticeHull.embed_injective heb
  subst a'
  subst b'
  obtain ⟨s,_,hs⟩ := Finset.mem_image.mp ha'
  obtain ⟨t,_,ht⟩ := Finset.mem_image.mp hb'
  obtain ⟨w,hw⟩ := vertex_difference_even s t
  rw [hs,ht] at hw
  have hunit : IsUnit (2 : ℤ) := hprim 2 w hw
  norm_num [Int.isUnit_iff] at hunit

theorem normals_card : normals.card = 6 := by decide

/-- The complete four-dimensional assertion of Proposition 5.4, with an
actual smooth reflexive presentation, its displayed real carrier, all six
geometric facet normals, genuine UT-freeness, and the determinant obstruction. -/
theorem proposition_5_4 :
    presentation.carrier = Q ∧
    (0 : Ambient 4) ∈ interior presentation.carrier ∧
    realPolar Q = convexHull ℝ
      (embed '' (insert 0 (normals : Set (Lattice 4)))) ∧
    presentation.geometricFacetNormals = (normals : Set (Lattice 4)) ∧
    normals.card = 6 ∧
    (∀ E : Set (Ambient 4), IsExtreme ℝ Q E → ¬ IsUnimodularTriangle E) ∧
    ¬ IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin 4))
      (fun u : {u // u ∈ presentation.geometricFacetNormals} => u.val) := by
  refine ⟨presentation_carrier,presentation.zero_mem_interior_carrier,?_,
    presentation.geometricFacetNormals_eq_normals,normals_card,Q_UT_free,?_⟩
  · rw [← presentation_carrier]
    exact presentation.realPolar_eq_convexHull_normals
  · intro h
    apply normals_not_uniform
    intro a
    exact h (fun i => ⟨(a i).val,
      presentation.geometricFacetNormals_eq_normals.symm ▸ (a i).property⟩)

end Unimodular.SegmentSimplex

end

/-! Transitive axiom audit of all extension declarations. -/
#print axioms Unimodular.SmoothReflexivePresentation.normalFace
#print axioms Unimodular.SmoothReflexivePresentation.IsFacet
#print axioms Unimodular.SmoothReflexivePresentation.zero_mem_carrier
#print axioms Unimodular.SmoothReflexivePresentation.normalFace_convex
#print axioms Unimodular.SmoothReflexivePresentation.normalFace_extreme
#print axioms Unimodular.SmoothReflexivePresentation.normalFace_nonempty
#print axioms Unimodular.SmoothReflexivePresentation.normalFace_ne_carrier
#print axioms Unimodular.SmoothReflexivePresentation.exists_vertex_mem_face
#print axioms Unimodular.SmoothReflexivePresentation.eq_carrier_of_localCone_eq
#print axioms Unimodular.SmoothReflexivePresentation.face_subset_normalFace
#print axioms Unimodular.SmoothReflexivePresentation.normalFace_isFacet
#print axioms Unimodular.SmoothReflexivePresentation.isFacet_iff_normalFace
#print axioms Unimodular.SmoothReflexivePresentation.normalFace_injective
#print axioms Unimodular.SmoothReflexivePresentation.normalFace_finrank
#print axioms Unimodular.SmoothReflexivePresentation.eq_normal_of_normalFace_eq
#print axioms Unimodular.SmoothReflexivePresentation.mem_normals_iff_primitive_facetNormal
#print axioms Unimodular.SmoothReflexivePresentation.zero_mem_interior_carrier
#print axioms Unimodular.SmoothReflexivePresentation.geometricFacetNormals
#print axioms Unimodular.SmoothReflexivePresentation.geometricFacetNormals_eq_normals
#print axioms Unimodular.SmoothReflexivePresentation.corollary_6_2
#print axioms Unimodular.embed_basis_linearIndependent
#print axioms Unimodular.basis_mem_basisFace
#print axioms Unimodular.span_basisFace
#print axioms Unimodular.finrank_span_basisFace
#print axioms Unimodular.SmoothCompleteFan.positive_coordinate_unique
#print axioms Unimodular.SmoothCompleteFan.independent_ray_span_is_cone_span
#print axioms Unimodular.SmoothCompleteFan.ray_generated_subspace_is_cone_span
#print axioms Unimodular.ConicReduction.nonnegative_independent_reduction
#print axioms Unimodular.ConicReduction.independent_conic_expression
#print axioms Unimodular.LatticeHull.embed_injective
#print axioms Unimodular.LatticeHull.exists_lattice_basis_extension
#print axioms Unimodular.LatticeHull.small_basis_combination
#print axioms Unimodular.LatticeHull.latticePoint_convexHull_eq_zero_or_mem
#print axioms Unimodular.LatticeHull.ray_not_mem_convexHull_others
#print axioms Unimodular.LatticeHull.unique_max_convexHull
#print axioms Unimodular.LatticeHull.ray_mem_extremePoints
#print axioms Unimodular.LatticeHull.extremePoints_convexHull_eq_rays
#print axioms Unimodular.realPairing_comm
#print axioms Unimodular.realPolar
#print axioms Unimodular.SmoothReflexivePresentation.realPolar_eq_convexHull_normals
#print axioms Unimodular.SmoothReflexivePresentation.geometric_reflexivity
#print axioms Unimodular.SegmentSimplex.normal
#print axioms Unimodular.SegmentSimplex.height
#print axioms Unimodular.SegmentSimplex.vertex
#print axioms Unimodular.SegmentSimplex.active
#print axioms Unimodular.SegmentSimplex.normals
#print axioms Unimodular.SegmentSimplex.vertices
#print axioms Unimodular.SegmentSimplex.Q
#print axioms Unimodular.SegmentSimplex.mem_Q_iff
#print axioms Unimodular.SegmentSimplex.vertex_mem_Q
#print axioms Unimodular.SegmentSimplex.active_pairing
#print axioms Unimodular.SegmentSimplex.active_mem
#print axioms Unimodular.SegmentSimplex.all_active
#print axioms Unimodular.SegmentSimplex.active_isUnit_det
#print axioms Unimodular.SegmentSimplex.localBasis
#print axioms Unimodular.SegmentSimplex.localBasis_apply
#print axioms Unimodular.SegmentSimplex.normals_occur
#print axioms Unimodular.SegmentSimplex.Q_convex
#print axioms Unimodular.SegmentSimplex.hull_eq_Q
#print axioms Unimodular.SegmentSimplex.vertexIndex
#print axioms Unimodular.SegmentSimplex.vertexIndex_spec
#print axioms Unimodular.SegmentSimplex.presentation
#print axioms Unimodular.SegmentSimplex.presentation_carrier
#print axioms Unimodular.SegmentSimplex.vertex_odd
#print axioms Unimodular.SegmentSimplex.obstructing_det
#print axioms Unimodular.SegmentSimplex.normals_not_uniform
#print axioms Unimodular.SegmentSimplex.integralSubspace
#print axioms Unimodular.SegmentSimplex.integralSubspace_basis_primitive
#print axioms Unimodular.SegmentSimplex.IsUnimodularTriangle
#print axioms Unimodular.SegmentSimplex.unimodular_triangle_has_primitive_edge
#print axioms Unimodular.SegmentSimplex.vertex_difference_even
#print axioms Unimodular.SegmentSimplex.Q_UT_free
#print axioms Unimodular.SegmentSimplex.normals_card
#print axioms Unimodular.SegmentSimplex.proposition_5_4
#check Unimodular.SmoothReflexivePresentation.corollary_6_2
#check Unimodular.SmoothCompleteFan.ray_generated_subspace_is_cone_span
#check Unimodular.LatticeHull.latticePoint_convexHull_eq_zero_or_mem

#check @Unimodular.SmoothReflexivePresentation.corollary_6_2
#print Unimodular.SmoothReflexivePresentation.IsFacet
#print Unimodular.SmoothReflexivePresentation.geometricFacetNormals

#check @Unimodular.SegmentSimplex.proposition_5_4
#print Unimodular.SegmentSimplex.Q
#print Unimodular.SegmentSimplex.IsUnimodularTriangle
#print Unimodular.SegmentSimplex.integralSubspace
