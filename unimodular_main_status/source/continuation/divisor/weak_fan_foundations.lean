module

public import Mathlib.Analysis.Convex.Function
public import Mathlib.Topology.Order.Basic
public import Mathlib.Topology.Order.Lattice
public import Recovery.Unimodular.WeakFano.SmoothPresentation
public import Unimodular.Extensions
public import Unimodular.FanBridge
public import Unimodular.FanMaximalCones
public import Unimodular.FanProducts

@[expose] public section
set_option maxRecDepth 4096

section Exact_Recovery_Unimodular_NativePort_NormalFanGeometry


@[expose] public section

/-! Actual full normal-fan geometry. Verification status is recorded in the native audit, not inferred from this source. -/

/- Exact owned draft: FanFullIntersections. -/
section NormalFanGeometry_FanFullIntersections



/-!
UNVERIFIED EXTENSION DRAFT. A cone of a finite complete fan is exactly the
intersection of all its full-dimensional supercones. This derives the full
normal-fan correspondence from maximal-cone support data, rather than silently
identifying only maximal cones and assuming the proper-face conclusion.
-/

set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Filter
open scoped Topology

namespace Unimodular.FanFullIntersections

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {ι : N →+ V} (Φ : TauCeti.Toric.Fan ι)

/-- Every point sufficiently near a face-detecting point can belong only to
fan cones containing that face. This is proved from finite closedness. -/
theorem star_neighborhood {D : PointedCone ℝ V} (hD : D ∈ Φ.cones) :
    ∃ x ∈ D, ∃ U : Set V, IsOpen U ∧ x ∈ U ∧
      ∀ C ∈ Φ.cones, ∀ z ∈ U, z ∈ C → D ≤ C := by
  classical
  obtain ⟨x,hxD,hdetect⟩ := FanProducts.exists_face_detecting_point D (Φ.isToricCone hD).fg
  let Bad := {C : Φ.cones // ¬D ≤ C.val}
  let U : Set V := (⋃ C : Bad, (C.val.val : Set V))ᶜ
  have hU : IsOpen U := (isClosed_iUnion_of_finite
    (fun C : Bad => ConeInterior.isClosed_of_fg (Φ.isToricCone C.val.property).fg)).isOpen_compl
  have hxU : x ∈ U := by
    intro hx
    obtain ⟨C,hxC⟩ := Set.mem_iUnion.mp hx
    exact C.property ((hdetect _ (Φ.inf_isFaceOf_left hD C.val.property)
      ⟨hxD,hxC⟩).trans inf_le_right)
  refine ⟨x,hxD,U,hU,hxU,?_⟩
  intro C hC z hz hzC
  by_contra hnot
  exact hz (Set.mem_iUnion.mpr ⟨⟨⟨C,hC⟩,hnot⟩,hzC⟩)

/-- Exact intersection characterization, including non-simplicial cones and
the zero cone. There is no generic-point or local-completeness premise. -/
theorem mem_iff_full_supercones (hcomplete : Φ.IsComplete)
    {D : PointedCone ℝ V} (hD : D ∈ Φ.cones) (y : V) :
    y ∈ D ↔ ∀ C ∈ Φ.cones, Submodule.span ℝ (C : Set V) = ⊤ → D ≤ C → y ∈ C := by
  constructor
  · intro hy C hC hfull hDC
    exact hDC hy
  · intro hy
    obtain ⟨x,hxD,U,hU,hxU,hstar⟩ := star_neighborhood Φ hD
    have hc : Continuous (fun t : ℝ => x - t • y) :=
      continuous_const.sub (continuous_id.smul continuous_const)
    have ht : Tendsto (fun t : ℝ => x - t • y) (𝓝 0) (𝓝 x) := by
      simpa using hc.tendsto 0
    have hnear : ∀ᶠ t : ℝ in 𝓝 0, x - t • y ∈ U :=
      ht.eventually (hU.mem_nhds hxU)
    have hnear' : ∀ᶠ t : ℝ in 𝓝[>] 0, x - t • y ∈ U :=
      hnear.filter_mono nhdsWithin_le_nhds
    have hpos : ∀ᶠ t : ℝ in 𝓝[>] 0, 0 < t := self_mem_nhdsWithin
    obtain ⟨t,htpos,htnear⟩ := (hpos.and hnear').exists
    obtain ⟨C,hC,hfull,hzC⟩ := FanMaximalCones.full_cones_cover Φ hcomplete (x - t • y)
    have hDC : D ≤ C := hstar C hC _ htnear hzC
    have hyC : y ∈ C := hy C hC hfull hDC
    have hface : D.IsFaceOf C := Φ.isFaceOf_of_le hC hD hDC
    apply hface.mem_of_smul_add_mem hyC hzC htpos
    simpa only [sub_eq_add_neg,add_assoc,add_left_comm,add_comm,add_neg_cancel,
      zero_add,add_zero] using hxD

#print axioms star_neighborhood
#print axioms mem_iff_full_supercones

end Unimodular.FanFullIntersections
end

end NormalFanGeometry_FanFullIntersections

/- Exact owned draft: NormalFanSupport. -/
section NormalFanGeometry_NormalFanSupport



/-!
UNVERIFIED EXTENSION DRAFT. The ordinary normal cone is defined by actual
maximization of linear functionals on a finite convex hull in the dual vector
space. Exact normal cones at full cones imply equality of the WHOLE fan with
all normal cones at all points of the polytope. Proper faces are proved, not
supplied as an additional condition. This is a general supporting theorem;
the A3 strict support-height data must still be constructed separately.
-/

set_option maxHeartbeats 0
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set
open scoped BigOperators

namespace Unimodular.NormalFanSupport

section Linear

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The genuine normal cone in V of a point q of a set in the dual space. -/
def normalCone (Q : Set (Module.Dual ℝ V)) (q : Module.Dual ℝ V) : PointedCone ℝ V where
  carrier := {y | ∀ z ∈ Q, z y ≤ q y}
  zero_mem' := by intro z hz; simp
  add_mem' := by
    intro x y hx hy z hz
    simpa only [map_add] using add_le_add (hx z hz) (hy z hz)
  smul_mem' := by
    intro a x hx z hz
    change z (a • x) ≤ q (a • x)
    rw [← Nonneg.coe_smul,map_smul,map_smul]
    exact mul_le_mul_of_nonneg_left (hx z hz) a.property

@[simp] theorem mem_normalCone (Q : Set (Module.Dual ℝ V)) (q : Module.Dual ℝ V) (y : V) :
    y ∈ normalCone Q q ↔ ∀ z ∈ Q, z y ≤ q y := Iff.rfl

/-- A smaller normal cone is an actual cone face of a larger one. -/
theorem normalCone_isFaceOf_of_le {Q : Set (Module.Dual ℝ V)}
    {p q : Module.Dual ℝ V} (hp : p ∈ Q) (hq : q ∈ Q)
    (hle : normalCone Q q ≤ normalCone Q p) :
    (normalCone Q q).IsFaceOf (normalCone Q p) := by
  refine ⟨hle,?_⟩
  intro x y a hx hy ha hxy
  have hxq := hx q hq
  have hyq := hy q hq
  have hsum := hxy p hp
  simp only [map_add,map_smul,smul_eq_mul] at hsum
  have he : p x = q x := by nlinarith
  intro z hz
  exact (hx z hz).trans_eq he

/-- The normal cone of a positive barycenter is exactly the intersection of
the normal cones at the points having positive coefficient. -/
theorem normalCone_barycenter_iff {I : Type*} [Fintype I]
    (Q : Set (Module.Dual ℝ V)) (p : I → Module.Dual ℝ V)
    (hp : ∀ i, p i ∈ Q) (w : I → ℝ) (hw : ∀ i, 0 ≤ w i)
    (hs : ∑ i, w i = 1) (y : V) :
    y ∈ normalCone Q (∑ i, w i • p i) ↔
      ∀ i, 0 < w i → y ∈ normalCone Q (p i) := by
  let q := ∑ i, w i • p i
  have hq : q y = ∑ i, w i * p i y := by
    simp only [q,LinearMap.sum_apply,LinearMap.smul_apply,smul_eq_mul]
  constructor
  · intro hy i hi z hz
    have hnonneg (j : I) : 0 ≤ w j * (q y - p j y) :=
      mul_nonneg (hw j) (sub_nonneg.mpr (hy (p j) (hp j)))
    have hzero : ∑ j, w j * (q y - p j y) = 0 := by
      simp only [mul_sub,Finset.sum_sub_distrib,← Finset.sum_mul,hs,one_mul]
      rw [← hq,sub_self]
    have he := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hnonneg j)).mp
      hzero i (Finset.mem_univ i)
    have hdiff : q y - p i y = 0 := (mul_eq_zero.mp he).resolve_left hi.ne'
    exact (hy z hz).trans_eq (sub_eq_zero.mp hdiff)
  · intro h z hz
    change z y ≤ q y
    calc
      z y = ∑ i, w i * z y := by rw [← Finset.sum_mul,hs,one_mul]
      _ ≤ ∑ i, w i * p i y := by
        apply Finset.sum_le_sum
        intro i hi
        by_cases hw0 : w i = 0
        · simp [hw0]
        · exact mul_le_mul_of_nonneg_left
            (h i (lt_of_le_of_ne (hw i) (Ne.symm hw0)) z hz) (hw i)
      _ = q y := hq.symm

/-- Every point of a finite convex hull has genuine nonnegative coefficients
on its original indexed family, even if the family has repeated points. -/
theorem mem_convexHull_range_iff {I : Type*} [Fintype I]
    (p : I → Module.Dual ℝ V) (q : Module.Dual ℝ V) :
    q ∈ convexHull ℝ (Set.range p) ↔ ∃ w : I → ℝ,
      (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧ (∑ i, w i • p i) = q := by
  classical
  constructor
  · intro hq
    rw [convexHull_range_eq_exists_affineCombination] at hq
    obtain ⟨s,w,hw,hs,hp⟩ := hq
    let c : I → ℝ := fun i => if i ∈ s then w i else 0
    refine ⟨c,?_,?_,?_⟩
    · intro i
      by_cases hi : i ∈ s <;> simp only [c,hi,ite_true,ite_false]
      · exact hw i hi
      · exact le_rfl
    · simpa [c] using hs
    · rw [Finset.affineCombination_eq_linear_combination _ _ _ hs] at hp
      simpa [c] using hp
  · rintro ⟨w,hw,hs,hq⟩
    exact mem_convexHull_of_exists_fintype w p hw hs (fun i => ⟨i,rfl⟩) hq

/-- Testing maximization on a finite generating family tests it on its whole
actual convex hull. -/
theorem mem_normalCone_hull_range_iff {I : Type*} (p : I → Module.Dual ℝ V)
    (q : Module.Dual ℝ V) (y : V) :
    y ∈ normalCone (convexHull ℝ (Set.range p)) q ↔ ∀ i, p i y ≤ q y := by
  constructor
  · intro h i
    exact h (p i) (subset_convexHull ℝ _ ⟨i,rfl⟩)
  · intro h z hz
    apply convexHull_min (t := {r : Module.Dual ℝ V | r y ≤ q y}) ?_ ?_ hz
    · rintro r ⟨i,rfl⟩
      exact h i
    · intro a ha b hb s t hs ht hst
      change s * a y + t * b y ≤ q y
      calc
        _ ≤ s * q y + t * q y := add_le_add
          (mul_le_mul_of_nonneg_left ha hs) (mul_le_mul_of_nonneg_left hb ht)
        _ = q y := by rw [← add_mul,hst,one_mul]

end Linear

section Fans

variable {N V : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {ι : N →+ V} (Φ : TauCeti.Toric.Fan ι)

abbrev FullCone := {C : Φ.cones // Submodule.span ℝ (C.val : Set V) = ⊤}

/-- Exact full normal-fan correspondence from genuine maximal normal cones.
Every proper cone is realized by an explicit barycenter of dual points. -/
theorem cones_iff_normalCone_of_full (hcomplete : Φ.IsComplete)
    (p : FullCone Φ → Module.Dual ℝ V)
    (hnormal : ∀ C, normalCone (convexHull ℝ (Set.range p)) (p C) = C.val.val)
    (D : PointedCone ℝ V) :
    D ∈ Φ.cones ↔ ∃ q ∈ convexHull ℝ (Set.range p),
      D = normalCone (convexHull ℝ (Set.range p)) q := by
  classical
  letI : Fintype (FullCone Φ) := Fintype.ofFinite _
  let Q := convexHull ℝ (Set.range p)
  have hp (C : FullCone Φ) : p C ∈ Q := subset_convexHull ℝ _ ⟨C,rfl⟩
  constructor
  · intro hD
    let J := {C : FullCone Φ // D ≤ C.val.val}
    have hJ : Nonempty J := by
      obtain ⟨C,hC,hfull,hDC⟩ := FanMaximalCones.exists_full_supercone Φ hcomplete hD
      exact ⟨⟨⟨⟨C,hC⟩,hfull⟩,hDC.le⟩⟩
    letI : Nonempty J := hJ
    letI : Fintype J := Fintype.ofFinite _
    let w : J → ℝ := fun _ => (Fintype.card J : ℝ)⁻¹
    have hwpos (j : J) : 0 < w j := inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
    have hwsum : ∑ j, w j = 1 := by
      simp only [w,Finset.sum_const,Finset.card_univ,nsmul_eq_mul]
      exact mul_inv_cancel₀ (ne_of_gt (Nat.cast_pos.mpr Fintype.card_pos))
    let q : Module.Dual ℝ V := ∑ j : J, w j • p j.val
    have hq : q ∈ Q := mem_convexHull_of_exists_fintype w (fun j : J => p j.val)
      (fun j => (hwpos j).le) hwsum (fun j => ⟨j.val,rfl⟩) rfl
    refine ⟨q,hq,?_⟩
    ext y
    rw [normalCone_barycenter_iff Q (fun j : J => p j.val) (fun j => hp j.val)
      w (fun j => (hwpos j).le) hwsum]
    constructor
    · intro hy j hj
      rw [hnormal]
      exact j.property hy
    · intro hy
      apply (FanFullIntersections.mem_iff_full_supercones Φ hcomplete hD y).mpr
      intro C hC hfull hDC
      let j : J := ⟨⟨⟨C,hC⟩,hfull⟩,hDC⟩
      have h := hy j (hwpos j)
      change y ∈ normalCone (convexHull ℝ (Set.range p)) (p j.val) at h
      rw [hnormal] at h
      exact h
  · rintro ⟨q,hq,rfl⟩
    obtain ⟨w,hw,hs,hpoint⟩ := (mem_convexHull_range_iff p q).mp hq
    have hpos : ∃ C : FullCone Φ, 0 < w C := by
      by_contra h
      push_neg at h
      have hz : ∀ C, w C = 0 := fun C => le_antisymm (h C) (hw C)
      simpa only [hz,Finset.sum_const_zero,zero_ne_one] using hs
    obtain ⟨C,hCpos⟩ := hpos
    have hle : normalCone Q q ≤ normalCone Q (p C) := by
      intro y hy
      rw [← hpoint] at hy
      exact (normalCone_barycenter_iff Q p hp w hw hs y).mp hy C hCpos
    have hface := normalCone_isFaceOf_of_le (hp C) hq hle
    rw [hnormal C] at hface
    exact Φ.mem_of_isFaceOf C.val.property hface

/-- A finite polytope witnesses the whole actual normal fan. This is the
geometric definition, stated with its finite original point set. -/
def HasPolytopeNormalFan : Prop := ∃ s : Finset (Module.Dual ℝ V),
  ∀ D : PointedCone ℝ V, D ∈ Φ.cones ↔
    ∃ q ∈ convexHull ℝ (s : Set (Module.Dual ℝ V)),
      D = normalCone (convexHull ℝ (s : Set (Module.Dual ℝ V))) q

theorem hasPolytopeNormalFan_of_full (hcomplete : Φ.IsComplete)
    (p : FullCone Φ → Module.Dual ℝ V)
    (hnormal : ∀ C, normalCone (convexHull ℝ (Set.range p)) (p C) = C.val.val) :
    HasPolytopeNormalFan Φ := by
  classical
  letI : Fintype (FullCone Φ) := Fintype.ofFinite _
  refine ⟨Finset.univ.image p,?_⟩
  intro D
  simpa only [Finset.coe_image,Finset.coe_univ,Set.image_univ] using
    cones_iff_normalCone_of_full Φ hcomplete p hnormal D

end Fans

#print axioms normalCone_isFaceOf_of_le
#print axioms normalCone_barycenter_iff
#print axioms cones_iff_normalCone_of_full
#print axioms hasPolytopeNormalFan_of_full

end Unimodular.NormalFanSupport
end

end NormalFanGeometry_NormalFanSupport

end
end Exact_Recovery_Unimodular_NativePort_NormalFanGeometry

section Exact_Recovery_Unimodular_WeakFano_GeneratingNormalFan


@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
open Set TauCeti.Toric

namespace Unimodular.NormalFanSupport

variable {N V I : Type*} [AddCommGroup N] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] {ι : N →+ V} [Fintype I]

/-- A finite generating family of genuine normal cones determines every
cone of the normal fan, including all proper faces and the zero cone. The
polytope is the actual convex hull of the original displayed points. -/
theorem cones_iff_normalCone_of_generators (Φ : Fan ι) (hcomplete : Φ.IsComplete)
    (p : I → Module.Dual ℝ V)
    (hmem : ∀ i, normalCone (convexHull ℝ (Set.range p)) (p i) ∈ Φ.cones)
    (hcover : ∀ C : FullCone Φ, ∃ i,
      C.val.val = normalCone (convexHull ℝ (Set.range p)) (p i))
    (D : PointedCone ℝ V) :
    D ∈ Φ.cones ↔ ∃ q ∈ convexHull ℝ (Set.range p),
      D = normalCone (convexHull ℝ (Set.range p)) q := by
  classical
  let Q := convexHull ℝ (Set.range p)
  have hp (i : I) : p i ∈ Q := subset_convexHull ℝ _ ⟨i, rfl⟩
  constructor
  · intro hD
    let J := {C : FullCone Φ // D ≤ C.val.val}
    have hJ : Nonempty J := by
      obtain ⟨C, hC, hfull, hDC⟩ := FanMaximalCones.exists_full_supercone Φ hcomplete hD
      exact ⟨⟨⟨⟨C, hC⟩, hfull⟩, hDC.le⟩⟩
    letI : Nonempty J := hJ
    letI : Fintype J := Fintype.ofFinite _
    choose index hindex using hcover
    let w : J → ℝ := fun _ => (Fintype.card J : ℝ)⁻¹
    have hwpos (j : J) : 0 < w j := inv_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
    have hwsum : ∑ j, w j = 1 := by
      simp only [w, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      exact mul_inv_cancel₀ (ne_of_gt (Nat.cast_pos.mpr Fintype.card_pos))
    let q : Module.Dual ℝ V := ∑ j : J, w j • p (index j.val)
    have hq : q ∈ Q := mem_convexHull_of_exists_fintype w
      (fun j : J => p (index j.val)) (fun j => (hwpos j).le) hwsum
      (fun j => ⟨index j.val, rfl⟩) rfl
    refine ⟨q, hq, ?_⟩
    ext y
    rw [normalCone_barycenter_iff Q (fun j : J => p (index j.val))
      (fun j => hp (index j.val)) w (fun j => (hwpos j).le) hwsum]
    constructor
    · intro hy j hj
      rw [← hindex]
      exact j.property hy
    · intro hy
      apply (FanFullIntersections.mem_iff_full_supercones Φ hcomplete hD y).mpr
      intro C hC hfull hDC
      let j : J := ⟨⟨⟨C, hC⟩, hfull⟩, hDC⟩
      have h := hy j (hwpos j)
      change y ∈ normalCone (convexHull ℝ (Set.range p)) (p (index j.val)) at h
      rw [← hindex] at h
      exact h
  · rintro ⟨q, hq, rfl⟩
    obtain ⟨w, hw, hs, hpoint⟩ := (mem_convexHull_range_iff p q).mp hq
    have hpos : ∃ i : I, 0 < w i := by
      by_contra h
      push_neg at h
      have hz : ∀ i, w i = 0 := fun i => le_antisymm (h i) (hw i)
      simpa only [hz, Finset.sum_const_zero, zero_ne_one] using hs
    obtain ⟨i, hipos⟩ := hpos
    have hle : normalCone Q q ≤ normalCone Q (p i) := by
      intro y hy
      rw [← hpoint] at hy
      exact (normalCone_barycenter_iff Q p hp w hw hs y).mp hy i hipos
    have hface := normalCone_isFaceOf_of_le (hp i) hq hle
    exact Φ.mem_of_isFaceOf (hmem i) hface

end Unimodular.NormalFanSupport

#print axioms Unimodular.NormalFanSupport.cones_iff_normalCone_of_generators
#check Unimodular.NormalFanSupport.cones_iff_normalCone_of_generators
end
end
end Exact_Recovery_Unimodular_WeakFano_GeneratingNormalFan

section Exact_Recovery_Unimodular_WeakFano_SmoothNormalFan


@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
open Set TauCeti.Toric
attribute [local instance] Classical.propDecidable

namespace Unimodular.WeightedPolytopes

variable {n : ℕ}

/-- The actual pointed cone of an integral basis. -/
def basisConePointed (b : Module.Basis (Fin n) ℤ (Lattice n)) :
    PointedCone ℝ (Ambient n) := PointedCone.hull ℝ (Set.range (fun i => embed (b i)))

theorem basisFace_eq_hull (b : Module.Basis (Fin n) ℤ (Lattice n))
    (A : Finset (Fin n)) :
    basisFace b A = (PointedCone.hull ℝ
      ((fun i => embed (b i)) '' (A : Set (Fin n))) : Set (Ambient n)) := by
  classical
  ext x
  constructor
  · rintro ⟨c, hc, hA, rfl⟩
    apply Submodule.sum_mem
    intro i hi
    by_cases hm : i ∈ A
    · exact PointedCone.smul_mem _ (hc i) (PointedCone.subset_hull ⟨i, hm, rfl⟩)
    · rw [hA i hm, zero_smul]
      exact Submodule.zero_mem _
  · intro hx
    obtain ⟨c, hcA, hc, he⟩ := PointedCone.mem_hull_image_iff_linearCombination.1 hx
    refine ⟨fun i => c i, hc, ?_, ?_⟩
    · intro i hi
      by_contra hn
      exact hi ((Finsupp.mem_supported _ _).1 hcA (Finsupp.mem_support_iff.2 hn))
    · rw [← he, Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)]

theorem basisCone_eq_pointed (b : Module.Basis (Fin n) ℤ (Lattice n)) :
    basisCone b = (basisConePointed b : Set (Ambient n)) := by
  calc
    basisCone b = basisFace b Finset.univ := by
      ext x
      constructor
      · rintro ⟨c, hc, he⟩
        exact ⟨c, hc, by simp, he⟩
      · rintro ⟨c, hc, hA, he⟩
        exact ⟨c, hc, he⟩
    _ = _ := by rw [basisFace_eq_hull]; simp [basisConePointed]

theorem basisConePointed_regular (b : Module.Basis (Fin n) ℤ (Lattice n)) :
    IsRegularCone (FanBridge.standardEmbedding n) (basisConePointed b) := by
  simpa [basisConePointed, Set.image_univ, ← Set.range_comp, Function.comp_def,
    FanBridge.standardEmbedding] using
    isRegularCone_hull_image_basis (FanBridge.standardEmbedding_isIntegralLattice n) b Set.univ

theorem basisConePointed_full (b : Module.Basis (Fin n) ℤ (Lattice n)) :
    Submodule.span ℝ (basisConePointed b : Set (Ambient n)) = ⊤ := by
  apply top_unique
  intro x hx
  rw [← sum_basis_realCoordinates b x]
  apply Submodule.sum_mem
  intro i hi
  exact Submodule.smul_mem _ _
    (Submodule.subset_span (PointedCone.subset_hull ⟨i, rfl⟩))

theorem embed_basis_ne_zero (b : Module.Basis (Fin n) ℤ (Lattice n)) (i : Fin n) :
    embed (b i) ≠ 0 := by
  intro he
  have hz : embed (0 : Lattice n) = 0 := by ext j; simp [embed]
  exact b.ne_zero i (LatticeHull.embed_injective (he.trans hz.symm))

namespace SmoothPresentation

variable (P : SmoothPresentation n)

def generatingCones : Set (PointedCone ℝ (Ambient n)) :=
  Set.range (fun v : {v // v ∈ P.vertices} => basisConePointed (P.basis v))

theorem generatingCones_intersection {C D : PointedCone ℝ (Ambient n)}
    (hC : C ∈ P.generatingCones) (hD : D ∈ P.generatingCones) :
    (C ⊓ D).IsFaceOf C := by
  obtain ⟨v, rfl⟩ := hC
  obtain ⟨w, rfl⟩ := hD
  have he : basisConePointed (P.basis v) ⊓ basisConePointed (P.basis w) =
      PointedCone.hull ℝ ((fun i => embed (P.basis v i)) '' (P.commonActive v w : Set (Fin n))) := by
    apply SetLike.coe_injective
    simpa only [← basisCone_eq_pointed, Submodule.coe_inf, ← basisFace_eq_hull] using
      P.basisCone_intersection v w
  rw [he]
  exact PointedCone.isFaceOf_hull_image
    ((FanBridge.standardEmbedding_isIntegralLattice n).linearIndependent_basis (P.basis v))
    rfl (P.commonActive v w : Set (Fin n))

/-- The actual finite toric fan of all faces of the vertex normal cones. -/
def normalFan : Fan (FanBridge.standardEmbedding n) :=
  Fan.ofCones (FanBridge.standardEmbedding_isIntegralLattice n) P.generatingCones
    (Set.finite_range _) (by
      rintro C ⟨v, rfl⟩
      exact (basisConePointed_regular (P.basis v)).toIsToricCone)
    (fun C D hC hD => P.generatingCones_intersection hC hD)

theorem mem_normalFan_cones (C : PointedCone ℝ (Ambient n)) :
    C ∈ P.normalFan.cones ↔ ∃ v : {v // v ∈ P.vertices},
      C.IsFaceOf (basisConePointed (P.basis v)) := by
  unfold normalFan
  rw [Fan.mem_ofCones_cones]
  constructor
  · rintro ⟨D, ⟨v, rfl⟩, hC⟩
    exact ⟨v, hC⟩
  · rintro ⟨v, hC⟩
    exact ⟨_, ⟨v, rfl⟩, hC⟩

theorem basisCone_mem_normalFan (v : {v // v ∈ P.vertices}) :
    basisConePointed (P.basis v) ∈ P.normalFan.cones :=
  (P.mem_normalFan_cones _).2 ⟨v, PointedCone.IsFaceOf.refl _⟩

theorem normalFan_complete : P.normalFan.IsComplete := by
  apply (Fan.isComplete_iff _).2
  intro x
  obtain ⟨v, hv⟩ := P.exists_nonnegative_basis_coordinates x
  refine ⟨_, P.basisCone_mem_normalFan v, ?_⟩
  change x ∈ (basisConePointed (P.basis v) : Set (Ambient n))
  rw [← basisCone_eq_pointed]
  exact (mem_basisCone_iff _ _).2 hv

theorem normalFan_regular : P.normalFan.IsRegular := by
  apply Fan.isRegular_iff.2
  intro C hC
  obtain ⟨v, hC⟩ := (P.mem_normalFan_cones C).1 hC
  exact (basisConePointed_regular (P.basis v)).of_isFaceOf hC

/-- A full cone of the constructed fan is one of the actual vertex cones. -/
theorem fullCone_eq_basisCone (C : NormalFanSupport.FullCone P.normalFan) :
    ∃ v : {v // v ∈ P.vertices}, C.val.val = basisConePointed (P.basis v) := by
  obtain ⟨v, hC⟩ := (P.mem_normalFan_cones _).1 C.val.property
  refine ⟨v, ?_⟩
  exact (FanMaximalCones.full_iff_maximal P.normalFan P.normalFan_complete C.val.property).1
    C.property _ (P.basisCone_mem_normalFan v) hC.le

/-- Exact ray equality once every original normal occurs at a vertex. -/
theorem normalFan_hasRays
    (hoccur : ∀ u ∈ P.normals, ∃ v : {v // v ∈ P.vertices}, ∃ i, P.basis v i = u) :
    AllowedBlocks.HasRays (FanBridge.standardEmbedding n)
      (fun u : {u // u ∈ P.normals} => u.val) P.normalFan := by
  classical
  intro R
  constructor
  · rintro ⟨hR, hdim⟩
    obtain ⟨v, hRD⟩ := (P.mem_normalFan_cones _).1 hR
    let ρ : ToricRay R := ⟨⟨R, PointedCone.IsFaceOf.refl _⟩, hdim⟩
    have hgen : R = PointedCone.hull ℝ
        ((fun i => embed (P.basis v i)) '' {i | embed (P.basis v i) ∈ R}) :=
      (show (basisConePointed (P.basis v)).Face from ⟨R, hRD⟩).eq_hull_image rfl
    have hex : ∃ i, embed (P.basis v i) ∈ R := by
      by_contra! h
      have hs : {i | embed (P.basis v i) ∈ R} = (∅ : Set (Fin n)) := by ext i; simp [h i]
      have hz : R = ⊥ := by rw [hgen, hs]; simp
      exact ρ.toPointedCone_ne_bot hz
    obtain ⟨i, hi⟩ := hex
    refine ⟨⟨P.basis v i, P.basis_mem v i⟩, ?_⟩
    exact ρ.eq_hull_singleton
      ((basisConePointed_regular (P.basis v)).toIsToricCone.salient.anti hRD.le) hi
      (embed_basis_ne_zero (P.basis v) i)
  · rintro ⟨u, rfl⟩
    obtain ⟨v, i, hi⟩ := hoccur u.val u.property
    have hface : (PointedCone.hull ℝ {embed (P.basis v i)}).IsFaceOf
        (basisConePointed (P.basis v)) := by
      simpa [Set.image_singleton, basisConePointed, FanBridge.standardEmbedding] using PointedCone.isFaceOf_hull_image
        ((FanBridge.standardEmbedding_isIntegralLattice n).linearIndependent_basis (P.basis v))
        rfl ({i} : Set (Fin n))
    change (PointedCone.hull ℝ {embed u.val}) ∈ P.normalFan.cones ∧
      Module.finrank ℝ (Submodule.span ℝ ((PointedCone.hull ℝ {embed u.val}) : Set (Ambient n))) = 1
    rw [← hi]
    exact ⟨P.normalFan.mem_of_isFaceOf (P.basisCone_mem_normalFan v) hface,
      PointedCone.finrank_span_coe_hull_singleton (embed_basis_ne_zero (P.basis v) i)⟩

/-- The actual dual functional represented by a real coordinate point. -/
def pointDual (p : Ambient n) : Module.Dual ℝ (Ambient n) where
  toFun x := realPairing p x
  map_add' x y := by simp [realPairing, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' a x := by
    simp [realPairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_left_comm]

theorem mem_normalConeAt_iff_vertices (v : {v // v ∈ P.vertices}) (x : Ambient n) :
    x ∈ P.normalConeAt v ↔ ∀ w : {v // v ∈ P.vertices},
      realPairing (embed w.val) x ≤ realPairing (embed v.val) x := by
  constructor
  · intro hx w
    exact hx _ (P.vertex_mem w)
  · intro hx
    change convexHull ℝ (embed '' (P.vertices : Set (Lattice n))) ⊆
      {p | realPairing p x ≤ realPairing (embed v.val) x}
    apply convexHull_min
    · rintro p ⟨w, hw, rfl⟩
      exact hx ⟨w, hw⟩
    · intro p hp q hq a b ha hb hab
      change realPairing (a • p + b • q) x ≤ realPairing (embed v.val) x
      rw [realPairing_add_left, realPairing_smul_left, realPairing_smul_left]
      calc
        _ ≤ a * realPairing (embed v.val) x + b * realPairing (embed v.val) x :=
          add_le_add (mul_le_mul_of_nonneg_left hp ha) (mul_le_mul_of_nonneg_left hq hb)
        _ = _ := by rw [← add_mul, hab, one_mul]

theorem normalCone_vertex_eq_basis (v : {v // v ∈ P.vertices}) :
    NormalFanSupport.normalCone
      (convexHull ℝ (Set.range (fun w : {v // v ∈ P.vertices} => pointDual (embed w.val))))
      (pointDual (embed v.val)) = basisConePointed (P.basis v) := by
  ext x
  rw [NormalFanSupport.mem_normalCone_hull_range_iff]
  change (∀ w : {v // v ∈ P.vertices}, realPairing (embed w.val) x ≤ realPairing (embed v.val) x) ↔
    x ∈ (basisConePointed (P.basis v) : Set (Ambient n))
  rw [← basisCone_eq_pointed, P.basisCone_eq_normalConeAt, P.mem_normalConeAt_iff_vertices]

/-- Projectivity is witnessed by a finite set of actual integral dual points
and equality of every actual fan cone with every actual normal cone. -/
theorem integral_normalFan :
    ∃ S : Finset (Module.Dual ℝ (Ambient n)),
      (∀ p ∈ S, ∀ x : Lattice n, ∃ z : ℤ, p (embed x) = (z : ℝ)) ∧
      ∀ C : PointedCone ℝ (Ambient n), C ∈ P.normalFan.cones ↔
        ∃ q ∈ convexHull ℝ (S : Set (Module.Dual ℝ (Ambient n))),
          C = NormalFanSupport.normalCone (convexHull ℝ (S : Set (Module.Dual ℝ (Ambient n)))) q := by
  classical
  let p : {v // v ∈ P.vertices} → Module.Dual ℝ (Ambient n) := fun v => pointDual (embed v.val)
  let S : Finset (Module.Dual ℝ (Ambient n)) := Finset.univ.image p
  have hS : (S : Set (Module.Dual ℝ (Ambient n))) = Set.range p := by simp [S]
  refine ⟨S, ?_, ?_⟩
  · intro q hq x
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hq
    refine ⟨∑ i, v.val i * x i, ?_⟩
    simp [p, pointDual, embed, realPairing, Int.cast_sum, Int.cast_mul]
  · intro C
    rw [hS]
    apply NormalFanSupport.cones_iff_normalCone_of_generators P.normalFan P.normalFan_complete p
    · intro v
      rw [P.normalCone_vertex_eq_basis]
      exact P.basisCone_mem_normalFan v
    · intro C
      obtain ⟨v, hv⟩ := P.fullCone_eq_basisCone C
      exact ⟨v, hv.trans (P.normalCone_vertex_eq_basis v).symm⟩

end SmoothPresentation
end Unimodular.WeightedPolytopes

#print axioms Unimodular.WeightedPolytopes.SmoothPresentation.normalFan_complete
#print axioms Unimodular.WeightedPolytopes.SmoothPresentation.normalFan_regular
#print axioms Unimodular.WeightedPolytopes.SmoothPresentation.normalFan_hasRays
#print axioms Unimodular.WeightedPolytopes.SmoothPresentation.integral_normalFan
#check Unimodular.WeightedPolytopes.SmoothPresentation.integral_normalFan
end
end
end Exact_Recovery_Unimodular_WeakFano_SmoothNormalFan

section Exact_Recovery_Unimodular_WeakFano_AnticanonicalSupport


@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators
open Set TauCeti.Toric
attribute [local instance] Classical.propDecidable

namespace Unimodular.WeightedPolytopes

variable {n : ℕ}

namespace SmoothPresentation

variable (P : SmoothPresentation n)

theorem vertex_eq_latticeCorner (v : {v // v ∈ P.vertices}) :
    embed v.val = embed (latticeCorner (P.basis v) P.height) := by
  rw [embed_latticeCorner]
  have hc : dualCoordinates (P.basis v) (embed v.val) =
      fun i => (P.height (P.basis v i) : ℝ) := by
    ext i
    exact P.basis_active v i
  rw [← hc, dualCorner_dualCoordinates]

/-- Every unit-height corner of this actual smooth fan satisfies all original
unit inequalities. This is the concrete convex anticanonical condition. -/
def UnitCornerFeasible : Prop :=
  ∀ v : {v // v ∈ P.vertices},
    dualCorner (P.basis v) (fun _ => 1) ∈
      WeightedPolytopes.carrier P.normals (fun _ => 1)

/-- No original nonzero ray can disappear: an integral point in a basis
cone with nonnegative coordinate sum at most one must be a basis vector. -/
theorem normals_occur (hweak : P.UnitCornerFeasible)
    (hzero : (0 : Lattice n) ∉ P.normals) (u : Lattice n) (hu : u ∈ P.normals) :
    ∃ v : {v // v ∈ P.vertices}, ∃ i, P.basis v i = u := by
  obtain ⟨v, hv⟩ := P.exists_nonnegative_basis_coordinates (embed u)
  have hmass : (∑ i, realCoordinates (P.basis v) (embed u) i) ≤ 1 := by
    have h := hweak v u hu
    rw [pairing_dualCorner] at h
    simpa only [one_mul, realCoordinates_embed] using h
  rcases LatticeHull.small_basis_combination (P.basis v) (fun i => i)
    Function.injective_id (fun i => realCoordinates (P.basis v) (embed u) i)
    hv hmass u (sum_basis_realCoordinates (P.basis v) (embed u)) with h | ⟨i, hi⟩
  · exact (hzero (h ▸ hu)).elim
  · exact ⟨v, i, hi.symm⟩

/-- The integral anticanonical linear form on a maximal cone. -/
def unitDual (v : {v // v ∈ P.vertices}) : Module.Dual ℝ (Ambient n) :=
  pointDual (embed (latticeDualVertex (P.basis v)))

theorem unitDual_integral (v : {v // v ∈ P.vertices}) (x : Lattice n) :
    ∃ z : ℤ, P.unitDual v (embed x) = (z : ℝ) := by
  refine ⟨∑ i, latticeDualVertex (P.basis v) i * x i, ?_⟩
  simp [unitDual, pointDual, embed, realPairing, Int.cast_sum, Int.cast_mul]

theorem unitDual_basis (v : {v // v ∈ P.vertices}) (i : Fin n) :
    P.unitDual v (embed (P.basis v i)) = 1 := by
  change pairing (embed (latticeDualVertex (P.basis v))) (P.basis v i) = 1
  rw [embed_latticeDualVertex, pairing_dualCorner_basis]

theorem unitDual_max_on_basis (hweak : P.UnitCornerFeasible)
    (v w : {v // v ∈ P.vertices}) (x : Ambient n) (hx : x ∈ basisCone (P.basis v)) :
    P.unitDual w x ≤ P.unitDual v x := by
  change realPairing (embed (latticeDualVertex (P.basis w))) x ≤
    realPairing (embed (latticeDualVertex (P.basis v))) x
  rw [realPairing_eq_coordinates (P.basis v), realPairing_eq_coordinates (P.basis v)]
  apply Finset.sum_le_sum
  intro i hi
  rw [embed_latticeDualVertex (P.basis v), pairing_dualCorner_basis]
  have hw := hweak w (P.basis v i) (P.basis_mem v i)
  rw [← embed_latticeDualVertex] at hw
  exact mul_le_mul_of_nonneg_left hw ((mem_basisCone_iff _ _).1 hx i)

/-- The actual anticanonical support function is a finite maximum of integral
linear forms. -/
def antiSupport (x : Ambient n) : ℝ :=
  P.vertices.attach.sup' (by simpa using P.vertices_nonempty) (fun v => P.unitDual v x)

theorem unitDual_le_antiSupport (v : {v // v ∈ P.vertices}) (x : Ambient n) :
    P.unitDual v x ≤ P.antiSupport x :=
  Finset.le_sup' (fun v => P.unitDual v x) (by simp)

theorem antiSupport_on_basis (hweak : P.UnitCornerFeasible)
    (v : {v // v ∈ P.vertices}) (x : Ambient n) (hx : x ∈ basisCone (P.basis v)) :
    P.antiSupport x = P.unitDual v x := by
  apply le_antisymm
  · apply (Finset.sup'_le_iff _ _).2
    intro w hw
    exact P.unitDual_max_on_basis hweak v w x hx
  · exact P.unitDual_le_antiSupport v x

theorem antiSupport_continuous : Continuous P.antiSupport := by
  apply Continuous.finset_sup'_apply
  intro v hv
  exact (P.unitDual v).continuous_of_finiteDimensional

theorem antiSupport_convex : ConvexOn ℝ Set.univ P.antiSupport := by
  refine ⟨convex_univ, ?_⟩
  intro x hx y hy a b ha hb hab
  apply (Finset.sup'_le_iff _ _).2
  intro v hv
  change P.unitDual v (a • x + b • y) ≤ a * P.antiSupport x + b * P.antiSupport y
  rw [map_add, map_smul, map_smul]
  exact add_le_add (mul_le_mul_of_nonneg_left (P.unitDual_le_antiSupport v x) ha)
    (mul_le_mul_of_nonneg_left (P.unitDual_le_antiSupport v y) hb)

theorem antiSupport_ray (hweak : P.UnitCornerFeasible)
    (hzero : (0 : Lattice n) ∉ P.normals) (u : Lattice n) (hu : u ∈ P.normals) :
    P.antiSupport (embed u) = 1 := by
  obtain ⟨v, i, rfl⟩ := P.normals_occur hweak hzero u hu
  have hx : embed (P.basis v i) ∈ basisCone (P.basis v) := by
    rw [basisCone_eq_pointed]
    exact PointedCone.subset_hull ⟨i, rfl⟩
  rw [P.antiSupport_on_basis hweak v _ hx, P.unitDual_basis]

/-- Linearity is certified on every actual cone, with a form from the actual
dual lattice; it is not merely a condition on listed maximal cones. -/
theorem antiSupport_on_cone (hweak : P.UnitCornerFeasible)
    (C : PointedCone ℝ (Ambient n)) (hC : C ∈ P.normalFan.cones) :
    ∃ f : Module.Dual ℝ (Ambient n),
      (∀ x : Lattice n, ∃ z : ℤ, f (embed x) = (z : ℝ)) ∧
      ∀ x ∈ C, P.antiSupport x = f x := by
  obtain ⟨v, hv⟩ := (P.mem_normalFan_cones C).1 hC
  refine ⟨P.unitDual v, P.unitDual_integral v, ?_⟩
  intro x hx
  apply P.antiSupport_on_basis hweak v x
  rw [basisCone_eq_pointed]
  exact hv.le hx

/-- The anticanonical polytope has full-dimensional real interior. -/
theorem zero_mem_interior_unitPolytope :
    (0 : Ambient n) ∈ interior (WeightedPolytopes.carrier P.normals (fun _ => 1)) :=
  WeightedPolytopes.zero_mem_interior P.normals _ (fun u hu => zero_lt_one)

/-- A maximal cone of the smooth fan is contained in the actual unit
polytope's normal cone at its unit dual corner. -/
theorem unitCorner_maximizes
    (v : {v // v ∈ P.vertices}) (x : Ambient n) (hx : x ∈ basisCone (P.basis v))
    (p : Ambient n) (hp : p ∈ WeightedPolytopes.carrier P.normals (fun _ => 1)) :
    realPairing p x ≤ P.unitDual v x := by
  change realPairing p x ≤ realPairing (embed (latticeDualVertex (P.basis v))) x
  rw [realPairing_eq_coordinates (P.basis v), realPairing_eq_coordinates (P.basis v)]
  apply Finset.sum_le_sum
  intro i hi
  rw [embed_latticeDualVertex, pairing_dualCorner_basis]
  exact mul_le_mul_of_nonneg_left (hp _ (P.basis_mem v i)) ((mem_basisCone_iff _ _).1 hx i)

end SmoothPresentation

/-- The finite height construction proves the anticanonical support
inequalities for the constructed smooth presentation. -/
theorem smoothPresentation_unit_feasible (U : Finset (Lattice n)) (h : Lattice n → ℤ)
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun u : (U : Set (Lattice n)) => u.val))
    (hpos : PointedCone.hull ℝ (embed '' (U : Set (Lattice n))) = ⊤)
    (hh : RegularHeight U h) : (smoothPresentation U h hU hpos hh).UnitCornerFeasible := by
  let P := smoothPresentation U h hU hpos hh
  intro v
  let b : RayBasis U := ⟨P.basis v, P.basis_mem v⟩
  apply hh.unit_feasible b
  change embed (latticeCorner (P.basis v) P.height) ∈
    WeightedPolytopes.carrier P.normals (fun u => (P.height u : ℝ))
  rw [← P.vertex_eq_latticeCorner]
  exact (P.mem_carrier_iff _).1 (P.vertex_mem v)

end Unimodular.WeightedPolytopes

#print axioms Unimodular.WeightedPolytopes.SmoothPresentation.normals_occur
#print axioms Unimodular.WeightedPolytopes.SmoothPresentation.antiSupport_continuous
#print axioms Unimodular.WeightedPolytopes.SmoothPresentation.antiSupport_convex
#print axioms Unimodular.WeightedPolytopes.SmoothPresentation.antiSupport_on_cone
#print axioms Unimodular.WeightedPolytopes.SmoothPresentation.antiSupport_ray
#print axioms Unimodular.WeightedPolytopes.smoothPresentation_unit_feasible
#check Unimodular.WeightedPolytopes.smoothPresentation_unit_feasible
end
end
end Exact_Recovery_Unimodular_WeakFano_AnticanonicalSupport

#print axioms Unimodular.WeightedPolytopes.SmoothPresentation.normalFan_complete
#print axioms Unimodular.WeightedPolytopes.SmoothPresentation.normalFan_regular
#print axioms Unimodular.WeightedPolytopes.smoothPresentation_unit_feasible
