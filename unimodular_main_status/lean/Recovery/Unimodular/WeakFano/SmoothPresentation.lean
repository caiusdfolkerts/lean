module

public import Recovery.Unimodular.WeakFano.HeightChoice

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
attribute [local instance] Classical.propDecidable

namespace Unimodular.WeightedPolytopes

variable {n : ℕ}

/-- A finite integral halfspace presentation with exactly an integral basis
of active normals at every displayed vertex. The normal fan is not assumed. -/
structure SmoothPresentation (n : ℕ) where
  vertices : Finset (Lattice n)
  normals : Finset (Lattice n)
  height : Lattice n → ℤ
  vertices_nonempty : vertices.Nonempty
  basis : {v // v ∈ vertices} → Module.Basis (Fin n) ℤ (Lattice n)
  basis_mem : ∀ v i, basis v i ∈ normals
  basis_active : ∀ v i, pairing (embed v.val) (basis v i) = height (basis v i)
  active_subset : ∀ v u, u ∈ normals → pairing (embed v.val) u = height u →
    ∃ i, basis v i = u
  hull_eq : convexHull ℝ (embed '' (vertices : Set (Lattice n))) =
    WeightedPolytopes.carrier normals (fun u => (height u : ℝ))

namespace SmoothPresentation

variable (P : SmoothPresentation n)

def carrier : Set (Ambient n) := convexHull ℝ (embed '' (P.vertices : Set (Lattice n)))

theorem mem_carrier_iff (x : Ambient n) :
    x ∈ P.carrier ↔ ∀ u ∈ P.normals, pairing x u ≤ P.height u := by
  rw [carrier, P.hull_eq]
  rfl

theorem vertex_mem (v : {v // v ∈ P.vertices}) : embed v.val ∈ P.carrier :=
  subset_convexHull ℝ _ ⟨v.val, v.property, rfl⟩

theorem exists_max_vertex (x : Ambient n) :
    ∃ v : {v // v ∈ P.vertices}, ∀ p ∈ P.carrier,
      realPairing p x ≤ realPairing (embed v.val) x := by
  classical
  obtain ⟨v, hv, hmax⟩ := P.vertices.exists_max_image
    (fun v => realPairing (embed v) x) P.vertices_nonempty
  refine ⟨⟨v, hv⟩, ?_⟩
  change convexHull ℝ (embed '' (P.vertices : Set (Lattice n))) ⊆
    {p | realPairing p x ≤ realPairing (embed v) x}
  apply convexHull_min
  · rintro p ⟨w, hw, rfl⟩
    exact hmax w hw
  · intro p hp q hq a b ha hb hab
    change realPairing (a • p + b • q) x ≤ realPairing (embed v) x
    rw [realPairing_add_left, realPairing_smul_left, realPairing_smul_left]
    calc
      a * realPairing p x + b * realPairing q x ≤
          a * realPairing (embed v) x + b * realPairing (embed v) x :=
        add_le_add (mul_le_mul_of_nonneg_left hp ha) (mul_le_mul_of_nonneg_left hq hb)
      _ = realPairing (embed v) x := by rw [← add_mul, hab, one_mul]

/-- The ordinary normal cone is defined by maximization on the actual polytope. -/
def normalConeAt (v : {v // v ∈ P.vertices}) : Set (Ambient n) :=
  {x | ∀ p ∈ P.carrier, realPairing p x ≤ realPairing (embed v.val) x}

theorem basisCone_maximizes (v : {v // v ∈ P.vertices}) {x : Ambient n}
    (hx : x ∈ basisCone (P.basis v)) : x ∈ P.normalConeAt v := by
  intro p hp
  have hx' := (mem_basisCone_iff (P.basis v) x).1 hx
  rw [realPairing_eq_coordinates (P.basis v), realPairing_eq_coordinates (P.basis v)]
  apply Finset.sum_le_sum
  intro i hi
  rw [P.basis_active]
  exact mul_le_mul_of_nonneg_left
    ((P.mem_carrier_iff p).1 hp _ (P.basis_mem v i)) (hx' i)

/-- Active integral-basis cones equal the actual normal cones; a negative
basis coefficient gives an explicit feasible improving direction. -/
theorem basisCone_eq_normalConeAt (v : {v // v ∈ P.vertices}) :
    basisCone (P.basis v) = P.normalConeAt v := by
  apply Set.Subset.antisymm (fun _ hx => P.basisCone_maximizes v hx)
  intro x hx
  apply (mem_basisCone_iff (P.basis v) x).2
  intro i
  by_contra hi
  have hneg : realCoordinates (P.basis v) x i < 0 := lt_of_not_ge hi
  let d : Ambient n := dualCorner (P.basis v) (Pi.single i (-1))
  have hd : realPairing d x = -realCoordinates (P.basis v) x i := by
    rw [realPairing_dualCorner]
    simp [Pi.single_apply]
  obtain ⟨t, ht, htall⟩ := exists_pos_feasible_step P.normals
    (fun u => (P.height u : ℝ) - pairing (embed v.val) u) (fun u => pairing d u)
    (fun u hu => sub_nonneg.mpr ((P.mem_carrier_iff _).1 (P.vertex_mem v) u hu))
    (by
      intro u hu he
      obtain ⟨j, rfl⟩ := P.active_subset v u hu (sub_eq_zero.mp he).symm
      rw [pairing_dualCorner_basis]
      simp [Pi.single_apply]
      split_ifs <;> norm_num)
  have hp : embed v.val + t • d ∈ P.carrier := by
    apply (P.mem_carrier_iff _).2
    intro u hu
    rw [pairing_add_left, pairing_smul_left]
    linarith [htall u hu]
  have hmax := hx _ hp
  rw [realPairing_add_left, realPairing_smul_left, hd] at hmax
  have hpositive : 0 < t * (-realCoordinates (P.basis v) x i) := mul_pos ht (neg_pos.mpr hneg)
  linarith

theorem exists_nonnegative_basis_coordinates (x : Ambient n) :
    ∃ v : {v // v ∈ P.vertices}, ∀ i, 0 ≤ realCoordinates (P.basis v) x i := by
  obtain ⟨v, hv⟩ := P.exists_max_vertex x
  refine ⟨v, (mem_basisCone_iff _ _).1 ?_⟩
  rw [P.basisCone_eq_normalConeAt]
  exact hv

def commonActive (v w : {v // v ∈ P.vertices}) : Finset (Fin n) := by
  classical
  exact Finset.univ.filter (fun i =>
    pairing (embed w.val) (P.basis v i) = P.height (P.basis v i))

@[simp] theorem mem_commonActive (v w : {v // v ∈ P.vertices}) (i : Fin n) :
    i ∈ P.commonActive v w ↔
      pairing (embed w.val) (P.basis v i) = P.height (P.basis v i) := by
  classical
  simp [commonActive]

/-- Intersections are the genuine common-active-normal faces. -/
theorem basisCone_intersection (v w : {v // v ∈ P.vertices}) :
    basisCone (P.basis v) ∩ basisCone (P.basis w) =
      basisFace (P.basis v) (P.commonActive v w) := by
  classical
  ext x
  constructor
  · rintro ⟨hxv, hxw⟩
    have hcoeff := (mem_basisCone_iff (P.basis v) x).1 hxv
    have he : realPairing (embed v.val) x = realPairing (embed w.val) x :=
      le_antisymm (P.basisCone_maximizes w hxw _ (P.vertex_mem v))
        (P.basisCone_maximizes v hxv _ (P.vertex_mem w))
    have hnonneg (i : Fin n) : 0 ≤ realCoordinates (P.basis v) x i *
        ((P.height (P.basis v i) : ℝ) - pairing (embed w.val) (P.basis v i)) :=
      mul_nonneg (hcoeff i)
        (sub_nonneg.mpr ((P.mem_carrier_iff _).1 (P.vertex_mem w) _ (P.basis_mem v i)))
    have hsum : ∑ i, realCoordinates (P.basis v) x i *
        ((P.height (P.basis v i) : ℝ) - pairing (embed w.val) (P.basis v i)) = 0 := by
      simp_rw [mul_sub]
      rw [Finset.sum_sub_distrib]
      have hv : realPairing (embed v.val) x =
          ∑ i, realCoordinates (P.basis v) x i * (P.height (P.basis v i) : ℝ) := by
        rw [realPairing_eq_coordinates (P.basis v)]
        simp only [P.basis_active]
      rw [← hv, ← realPairing_eq_coordinates (P.basis v), he, sub_self]
    refine ⟨realCoordinates (P.basis v) x, hcoeff, ?_, sum_basis_realCoordinates _ _⟩
    intro i hi
    have hzero := (Finset.sum_eq_zero_iff_of_nonneg (fun j hj => hnonneg j)).1 hsum i
      (Finset.mem_univ i)
    have hneq : (P.height (P.basis v i) : ℝ) - pairing (embed w.val) (P.basis v i) ≠ 0 := by
      intro hz
      apply hi
      exact (P.mem_commonActive v w i).2 (sub_eq_zero.mp hz).symm
    exact (mul_eq_zero.mp hzero).resolve_right hneq
  · rintro ⟨c, hc, hsupport, hcx⟩
    refine ⟨⟨c, hc, hcx⟩, ?_⟩
    rw [P.basisCone_eq_normalConeAt]
    intro p hp
    rw [← hcx]
    have hpv := P.basisCone_maximizes v (x := ∑ i, c i • embed (P.basis v i)) ⟨c, hc, rfl⟩ p hp
    have he : realPairing (embed v.val) (∑ i, c i • embed (P.basis v i)) =
        realPairing (embed w.val) (∑ i, c i • embed (P.basis v i)) := by
      rw [realPairing_eq_coordinates (P.basis v), realPairing_eq_coordinates (P.basis v)]
      simp only [realCoordinates_sum_basis]
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hact : i ∈ P.commonActive v w
      · rw [P.basis_active, (P.mem_commonActive v w i).1 hact]
      · simp [hsupport i hact]
    exact hpv.trans_eq he

/-- Construct the complete smooth coordinate fan from actual vertex normal cones. -/
def coordinateFan : SmoothCompleteFan n where
  maximal := P.vertices.attach.image P.basis
  complete := by
    intro x
    obtain ⟨v, hv⟩ := P.exists_nonnegative_basis_coordinates x
    exact ⟨P.basis v, Finset.mem_image.2 ⟨v, by simp, rfl⟩,
      (mem_basisCone_iff (P.basis v) x).2 hv⟩
  intersection := by
    intro b hb c hc
    obtain ⟨v, _, rfl⟩ := Finset.mem_image.1 hb
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.1 hc
    exact ⟨P.commonActive v w, P.commonActive w v, P.basisCone_intersection v w,
      by rw [Set.inter_comm]; exact P.basisCone_intersection w v⟩

end SmoothPresentation

/-- Convert the actual weighted polytope, with all properties proved above,
into the normal-cone presentation. -/
def smoothPresentation (U : Finset (Lattice n)) (h : Lattice n → ℤ)
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun u : (U : Set (Lattice n)) => u.val))
    (hpos : PointedCone.hull ℝ (embed '' (U : Set (Lattice n))) = ⊤)
    (hh : RegularHeight U h) : SmoothPresentation n := by
  classical
  have hvertex (v : {v // v ∈ vertices U h}) :
      ∃ b : RayBasis U, latticeCorner b.val h = v.val := ((mem_vertices U h _).1 v.property).1
  let B (v : {v // v ∈ vertices U h}) : RayBasis U := Classical.choose (hvertex v)
  have hB (v : {v // v ∈ vertices U h}) : latticeCorner (B v).val h = v.val :=
    Classical.choose_spec (hvertex v)
  exact {
    vertices := vertices U h
    normals := U
    height := h
    vertices_nonempty := by
      have hz : (0 : Ambient n) ∈ carrier U (fun u => (h u : ℝ)) := by
        apply interior_subset (zero_mem_interior U _ ?_)
        intro u hu
        exact_mod_cast hh.positive u hu
      rw [carrier_eq_convexHull_vertices U h hU hpos] at hz
      obtain ⟨x, ⟨u, hu, rfl⟩⟩ := (convexHull_nonempty_iff (𝕜 := ℝ)).1 ⟨0, hz⟩
      exact ⟨u, hu⟩
    basis := fun v => (B v).val
    basis_mem := fun v i => (B v).property i
    basis_active := by
      intro v i
      rw [← hB v, pairing_latticeCorner_basis]
    active_subset := by
      intro v u hu ha
      apply hh.active_exact (B v) u hu
      rwa [hB v]
    hull_eq := (carrier_eq_convexHull_vertices U h hU hpos).symm }

end Unimodular.WeightedPolytopes

#print axioms Unimodular.WeightedPolytopes.SmoothPresentation.basisCone_eq_normalConeAt
#print axioms Unimodular.WeightedPolytopes.SmoothPresentation.basisCone_intersection
#print axioms Unimodular.WeightedPolytopes.SmoothPresentation.coordinateFan
#print axioms Unimodular.WeightedPolytopes.smoothPresentation
#check Unimodular.WeightedPolytopes.smoothPresentation
