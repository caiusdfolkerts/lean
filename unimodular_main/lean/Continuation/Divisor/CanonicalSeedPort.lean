module

public import Unimodular.ConeBases
public import Continuation.Divisor.SeedConvexity
public import Continuation.Runtime.TypeARecovered
public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic.FunProp

@[expose] public section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0

/-! The actual canonical terminal reflexive seed. Recovered proof bodies are retained with explicit fan-membership and
primitive-generator API rewrites recorded in the provenance audit. -/



section CanonicalSeedRecovered0


/-!
# Compactness and interior of the polar of a positively spanning finite system

No integrality of vertices, smoothness, or pre-existing polytope presentation
is assumed. Positive spanning is the equality of the actual nonnegative cone
with the entire real ambient space.
-/

open Set
open scoped BigOperators

noncomputable section

namespace Unimodular.GenericReflexivity

/-- The actual intersection of the unit halfspaces of the given lattice vectors. -/
def polarCarrier {n : ℕ} (U : Finset (Lattice n)) : Set (Ambient n) :=
  {x | ∀ u ∈ U, pairing x u ≤ 1}

@[simp] theorem mem_polarCarrier {n : ℕ} (U : Finset (Lattice n)) (x : Ambient n) :
    x ∈ polarCarrier U ↔ ∀ u ∈ U, pairing x u ≤ 1 := Iff.rfl

theorem polarCarrier_convex {n : ℕ} (U : Finset (Lattice n)) :
    Convex ℝ (polarCarrier U) := by
  intro x hx y hy a b ha hb hab u hu
  rw [pairing_add_left, pairing_smul_left, pairing_smul_left]
  calc
    a * pairing x u + b * pairing y u ≤ a * 1 + b * 1 :=
      add_le_add (mul_le_mul_of_nonneg_left (hx u hu) ha)
        (mul_le_mul_of_nonneg_left (hy u hu) hb)
    _ = 1 := by simpa only [mul_one] using hab

theorem pairing_continuous {n : ℕ} (u : Lattice n) :
    Continuous (fun x : Ambient n => pairing x u) := by
  unfold pairing
  fun_prop

theorem polarCarrier_isClosed {n : ℕ} (U : Finset (Lattice n)) :
    IsClosed (polarCarrier U) := by
  simp only [polarCarrier, setOf_forall]
  exact isClosed_iInter fun u => isClosed_iInter fun _ =>
    isClosed_le (pairing_continuous u) continuous_const

theorem zero_mem_polarCarrier {n : ℕ} (U : Finset (Lattice n)) :
    (0 : Ambient n) ∈ polarCarrier U := by
  intro u hu
  simp [pairing]

/-- The origin satisfies every defining inequality strictly, and the finite
intersection of these strict halfspaces is an open neighborhood. -/
theorem zero_mem_interior_polarCarrier {n : ℕ} (U : Finset (Lattice n)) :
    (0 : Ambient n) ∈ interior (polarCarrier U) := by
  let O : Set (Ambient n) := {x | ∀ u ∈ U, pairing x u < 1}
  have hO : IsOpen O := by
    simp only [O, setOf_forall]
    exact isOpen_biInter_finset fun u hu =>
      isOpen_lt (pairing_continuous u) continuous_const
  have hzero : (0 : Ambient n) ∈ O := by
    intro u hu
    simp [pairing]
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (hO.mem_nhds hzero)
  intro x hx u hu
  exact (hx u hu).le

/-- Every vector in the nonnegative cone has a uniform upper bound as a
functional on the polar. The bound is constructed through cone-span induction,
using only the defining inequalities and nonnegative scalar multiplication. -/
theorem exists_pairing_bound_of_mem_hull {n : ℕ} (U : Finset (Lattice n))
    (y : Ambient n) (hy : y ∈ PointedCone.hull ℝ (embed '' (U : Set (Lattice n)))) :
    ∃ C : ℝ, ∀ x ∈ polarCarrier U, realPairing x y ≤ C := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, hu, rfl⟩ := hy
    exact ⟨1, fun x hx => hx u hu⟩
  | zero =>
    exact ⟨0, fun x hx => by simp [realPairing]⟩
  | add y z hy hz ihy ihz =>
    obtain ⟨C, hC⟩ := ihy
    obtain ⟨D, hD⟩ := ihz
    refine ⟨C + D, fun x hx => ?_⟩
    have h := add_le_add (hC x hx) (hD x hx)
    simpa only [realPairing, Pi.add_apply, mul_add, Finset.sum_add_distrib] using h
  | smul c y hy ih =>
    obtain ⟨C, hC⟩ := ih
    refine ⟨(c : ℝ) * C, fun x hx => ?_⟩
    have h := mul_le_mul_of_nonneg_left (hC x hx) c.property
    simpa only [← Nonneg.coe_smul, realPairing, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum, mul_left_comm] using h

/-- Positive spanning bounds both signs of every coordinate. The polar is a
closed subset of the resulting compact coordinate box. -/
theorem polarCarrier_isCompact {n : ℕ} (U : Finset (Lattice n))
    (hpos : PointedCone.hull ℝ (embed '' (U : Set (Lattice n))) = ⊤) :
    IsCompact (polarCarrier U) := by
  classical
  have hmem (y : Ambient n) :
      y ∈ PointedCone.hull ℝ (embed '' (U : Set (Lattice n))) := by
    rw [hpos]
    trivial
  choose upper hupper using fun i : Fin n =>
    exists_pairing_bound_of_mem_hull U (Pi.single i 1) (hmem _)
  choose lower hlower using fun i : Fin n =>
    exists_pairing_bound_of_mem_hull U (-Pi.single i 1) (hmem _)
  apply (isCompact_Icc (a := fun i => -lower i) (b := upper)).of_isClosed_subset
    (polarCarrier_isClosed U)
  intro x hx
  constructor
  · intro i
    have h := hlower i x hx
    have heq : realPairing x (-Pi.single i 1) = -x i := by
      simp [realPairing, Pi.single_apply]
    rw [heq] at h
    linarith
  · intro i
    have h := hupper i x hx
    simpa [realPairing, Pi.single_apply] using h

#print axioms Unimodular.GenericReflexivity.zero_mem_interior_polarCarrier
#print axioms Unimodular.GenericReflexivity.polarCarrier_isCompact

end Unimodular.GenericReflexivity
end

end CanonicalSeedRecovered0

section CanonicalSeedRecovered1


noncomputable section

namespace Unimodular.GenericReflexivity

open scoped BigOperators Topology

variable {n : ℕ}

/-- The active normals at an actual point of the actual polar. -/
def activeNormals (U : Finset (Lattice n)) (x : Ambient n) : Set (Lattice n) :=
  {u | u ∈ U ∧ pairing x u = 1}

/-- An extreme point of the polar is determined by spanning active normals.
If the active span were proper, a nonzero annihilating direction would permit
both a positive and a negative feasible step, contradicting extremality. -/
theorem activeNormals_span (U : Finset (Lattice n)) {x : Ambient n}
    (hx : x ∈ (polarCarrier U).extremePoints ℝ) :
    Submodule.span ℝ (embed '' activeNormals U x) = ⊤ := by
  classical
  by_contra hspan
  obtain ⟨f,hf,hker⟩ := (Submodule.span ℝ (embed '' activeNormals U x)).exists_le_ker_of_lt_top
    (lt_top_iff_ne_top.mpr hspan)
  let d : Ambient n := fun j => f (Pi.single j 1)
  have hd : d ≠ 0 := by
    intro hd0
    apply hf
    apply LinearMap.ext
    intro z
    change f z = 0
    rw [linearMap_eq_realPairing f z]
    change realPairing z d = 0
    rw [hd0]
    simp [realPairing]
  have hactive (u : Lattice n) (hu : u ∈ U) (ha : pairing x u = 1) :
      pairing d u = 0 := by
    have hh : f (embed u) = 0 :=
      hker (Submodule.subset_span ⟨u,⟨hu,ha⟩,rfl⟩)
    rw [linearMap_eq_realPairing f] at hh
    change realPairing d (embed u) = 0
    change realPairing (embed u) d = 0 at hh
    rwa [realPairing_comm] at hh
  obtain ⟨t,ht,hstep⟩ := exists_pos_feasible_step U
    (fun u => 1 - pairing x u) (fun u => |pairing d u|)
    (fun u hu => sub_nonneg.mpr (hx.1 u hu)) (by
      intro u hu he
      simpa only [hactive u hu (by linarith),abs_zero] using (le_refl (0 : ℝ)))
  have hp : x + t • d ∈ polarCarrier U := by
    intro u hu
    rw [pairing_add_left,pairing_smul_left]
    have hh := (mul_le_mul_of_nonneg_left (le_abs_self (pairing d u)) ht.le).trans
      (hstep u hu)
    linarith
  have hm : x + t • (-d) ∈ polarCarrier U := by
    intro u hu
    rw [pairing_add_left,pairing_smul_left]
    have hneg : pairing (-d) u = -pairing d u := by
      simp [pairing,Finset.sum_neg_distrib]
    rw [hneg]
    have hh := (mul_le_mul_of_nonneg_left (neg_le_abs (pairing d u)) ht.le).trans
      (hstep u hu)
    linarith
  have he : x + t • d = x := hx.2 hp hm
    ⟨(1 / 2 : ℝ),(1 / 2 : ℝ),by norm_num,by norm_num,by norm_num,by module⟩
  have hz : t • d = 0 := add_left_cancel (he.trans (add_zero x).symm)
  exact hd ((smul_eq_zero.1 hz).resolve_left ht.ne')

/-- Actual integral bases selected from the given finite configuration. -/
def RayBasis (U : Finset (Lattice n)) :=
  {b : Module.Basis (Fin n) ℤ (Lattice n) // ∀ j, b j ∈ U}

instance rayBasis_finite (U : Finset (Lattice n)) : Finite (RayBasis U) := by
  let f : RayBasis U → (Fin n → {u : Lattice n // u ∈ U}) :=
    fun b j => ⟨b.val j,b.property j⟩
  apply Finite.of_injective f
  intro b c he
  apply Subtype.ext
  apply DFunLike.coe_injective
  funext j
  exact congrArg Subtype.val (congrFun he j)

/-- Every genuine polar vertex is the integral dual corner of an active ray
basis. No integrality or finiteness of the polar vertices is assumed. -/
theorem extreme_eq_dual_vertex (U : Finset (Lattice n))
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun u : (U : Set (Lattice n)) => u.val))
    {x : Ambient n} (hx : x ∈ (polarCarrier U).extremePoints ℝ) :
    ∃ b : RayBasis U, x = embed (latticeDualVertex b.val) := by
  classical
  have hA : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun u : activeNormals U x => u.val) := by
    intro a
    exact hU (fun j => ⟨(a j).val,(a j).property.1⟩)
  let a : Empty → activeNormals U x := fun e => e.elim
  obtain ⟨b,hb,_⟩ := LatticeHull.exists_lattice_basis_extension (activeNormals U x)
    hA (activeNormals_span U hx) a
    (linearIndependent_empty_type : LinearIndependent ℝ (fun j => embed (a j).val))
  refine ⟨⟨b,fun j => (hb j).1⟩,?_⟩
  have hcoord : dualCoordinates b x = fun _ => 1 := by
    funext j
    exact (hb j).2
  rw [embed_latticeDualVertex]
  calc
    x = dualCorner b (dualCoordinates b x) := (dualCorner_dualCoordinates b x).symm
    _ = dualCorner b (fun _ => 1) := by rw [hcoord]

/-- The true polar is the convex hull of finitely many actual lattice points.
Compactness comes from positive spanning, and the active-basis argument proves
integrality of every extreme point before Krein--Milman is applied. -/
theorem polarCarrier_lattice_polytope (U : Finset (Lattice n))
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun u : (U : Set (Lattice n)) => u.val))
    (hpos : PointedCone.hull ℝ (embed '' (U : Set (Lattice n))) = ⊤) :
    ∃ W : Finset (Lattice n), polarCarrier U =
      convexHull ℝ (embed '' (W : Set (Lattice n))) := by
  classical
  letI : Fintype (RayBasis U) := Fintype.ofFinite _
  let W := ((Finset.univ : Finset (RayBasis U)).image
    (fun b => latticeDualVertex b.val)).filter (fun w => embed w ∈ polarCarrier U)
  have hW : embed '' (W : Set (Lattice n)) ⊆ polarCarrier U := by
    rintro z ⟨w,hw,rfl⟩
    exact (Finset.mem_filter.1 hw).2
  have hext : (polarCarrier U).extremePoints ℝ ⊆ embed '' (W : Set (Lattice n)) := by
    intro x hx
    obtain ⟨b,hb⟩ := extreme_eq_dual_vertex U hU hx
    refine ⟨latticeDualVertex b.val,Finset.mem_filter.2 ⟨?_,?_⟩,hb.symm⟩
    · exact Finset.mem_image.2 ⟨b,Finset.mem_univ _,rfl⟩
    · rw [← hb]
      exact hx.1
  refine ⟨W,Set.Subset.antisymm ?_ (convexHull_min hW (polarCarrier_convex U))⟩
  rw [← closure_convexHull_extremePoints (polarCarrier_isCompact U hpos)
    (polarCarrier_convex U)]
  apply closure_minimal
  · exact convexHull_min (fun x hx => subset_convexHull ℝ _ (hext hx))
      (convex_convexHull ℝ _)
  · exact (W.finite_toSet.image embed).isClosed_convexHull ℝ

/-- The ordinary geometric polar of the ray hull is exactly its displayed
finite family of unit inequalities. -/
theorem realPolar_hull_eq_polarCarrier (U : Finset (Lattice n)) :
    realPolar (convexHull ℝ (embed '' (U : Set (Lattice n)))) = polarCarrier U := by
  ext x
  constructor
  · intro hx u hu
    have hh := hx (embed u) (subset_convexHull ℝ _ ⟨u,hu,rfl⟩)
    change realPairing x (embed u) ≤ 1
    rwa [realPairing_comm] at hh
  · intro hx y hy
    apply convexHull_min (t := {y | realPairing y x ≤ 1}) ?_ ?_ hy
    · rintro z ⟨u,hu,rfl⟩
      change realPairing (embed u) x ≤ 1
      rw [realPairing_comm]
      exact hx u hu
    · intro a ha b hb t s ht hs hts
      change realPairing (t • a + s • b) x ≤ 1
      rw [realPairing_add_left,realPairing_smul_left,realPairing_smul_left]
      calc
        _ ≤ t * 1 + s * 1 := add_le_add (mul_le_mul_of_nonneg_left ha ht)
          (mul_le_mul_of_nonneg_left hb hs)
        _ = 1 := by simpa using hts

/-- A positive-spanning nonempty finite family has the origin in its actual
convex hull, by a strictly positive dependence and normalization of its mass. -/
theorem zero_mem_hull (U : Finset (Lattice n)) (hne : U.Nonempty)
    (hpos : PointedCone.hull ℝ (embed '' (U : Set (Lattice n))) = ⊤) :
    (0 : Ambient n) ∈ convexHull ℝ (embed '' (U : Set (Lattice n))) := by
  classical
  let v : {u : Lattice n // u ∈ U} → Ambient n := fun u => embed u.val
  have hrange : Set.range v = embed '' (U : Set (Lattice n)) := by
    ext x
    constructor
    · rintro ⟨u,rfl⟩
      exact ⟨u.val,u.property,rfl⟩
    · rintro ⟨u,hu,rfl⟩
      exact ⟨⟨u,hu⟩,rfl⟩
  have hcone : PointedCone.hull ℝ (Set.range v) = ⊤ := by rw [hrange]; exact hpos
  obtain ⟨_,c,hc,hrel⟩ := (FlowOrientations.hull_top_iff_span_and_positive_relation v).1 hcone
  letI : Nonempty {u : Lattice n // u ∈ U} := hne.to_subtype
  let mass : ℝ := ∑ u, c u
  have hmass : 0 < mass := Finset.sum_pos (fun u _ => hc u) Finset.univ_nonempty
  have hw : ∑ u, c u / mass = 1 := by
    rw [← Finset.sum_div]
    exact div_self hmass.ne'
  have he : (∑ u, (c u / mass) • v u) = 0 := by
    simp_rw [div_eq_mul_inv,mul_comm (c _),mul_smul]
    rw [← Finset.smul_sum,hrel,smul_zero]
  have hh := (convex_convexHull ℝ (embed '' (U : Set (Lattice n)))).sum_mem
    (fun u _ => div_nonneg (hc u).le hmass.le) hw
    (fun u _ => subset_convexHull ℝ _ ⟨u.val,u.property,rfl⟩)
  exact he ▸ hh

/-- The bipolar identity is proved by real separation in the original ambient
lattice coordinates. It does not assume any polytope duality theorem. -/
theorem realPolar_polarCarrier (U : Finset (Lattice n))
    (hzero : (0 : Ambient n) ∈ convexHull ℝ (embed '' (U : Set (Lattice n)))) :
    realPolar (polarCarrier U) = convexHull ℝ (embed '' (U : Set (Lattice n))) := by
  classical
  let S : Set (Ambient n) := embed '' (U : Set (Lattice n))
  have hS : S.Finite := U.finite_toSet.image embed
  apply Set.Subset.antisymm
  · intro y hy
    by_contra hnot
    obtain ⟨f,c,hf,hfy⟩ := geometric_hahn_banach_closed_point
      (convex_convexHull ℝ S) (hS.isClosed_convexHull ℝ) hnot
    have hc : 0 < c := by simpa using hf 0 hzero
    let z : Ambient n := fun j => f (Pi.single j 1)
    let p : Ambient n := c⁻¹ • z
    have hpair (x : Ambient n) : realPairing p x = c⁻¹ * f x := by
      rw [realPairing_smul_left,realPairing_comm]
      congr 1
      exact (linearMap_eq_realPairing f.toLinearMap x).symm
    have hp : p ∈ polarCarrier U := by
      intro u hu
      change realPairing p (embed u) ≤ 1
      rw [hpair]
      have hh := hf (embed u) (subset_convexHull ℝ S ⟨u,hu,rfl⟩)
      calc
        c⁻¹ * f (embed u) ≤ c⁻¹ * c :=
          mul_le_mul_of_nonneg_left hh.le (inv_nonneg.mpr hc.le)
        _ = 1 := inv_mul_cancel₀ hc.ne'
    have hb := hy p hp
    rw [hpair] at hb
    have hlt : 1 < c⁻¹ * f y := by
      calc
        1 = c⁻¹ * c := (inv_mul_cancel₀ hc.ne').symm
        _ < c⁻¹ * f y := mul_lt_mul_of_pos_left hfy (inv_pos.mpr hc)
    exact (not_lt_of_ge hb) hlt
  · apply convexHull_min
    · rintro y ⟨u,hu,rfl⟩ p hp
      exact hp u hu
    · intro x hx y hy a b ha hb hab p hp
      rw [realPairing_comm p,realPairing_add_left,realPairing_smul_left,
        realPairing_smul_left,realPairing_comm x p,realPairing_comm y p]
      calc
        _ ≤ a * 1 + b * 1 := add_le_add (mul_le_mul_of_nonneg_left (hx p hp) ha)
          (mul_le_mul_of_nonneg_left (hy p hp) hb)
        _ = 1 := by simpa using hab

/-- Full-dimensionality, polar integrality, exact vertices, and the exact lattice
point statement of Lemma3.2, with the paper's global positive-rank convention.
The subsequent canonical projective radial-fan assertion is a separate endpoint. -/
theorem terminal_reflexive_hull (hn : 0 < n) (U : Finset (Lattice n))
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun u : (U : Set (Lattice n)) => u.val))
    (hpos : PointedCone.hull ℝ (embed '' (U : Set (Lattice n))) = ⊤)
    (hzero : (0 : Lattice n) ∉ U) :
    let P := convexHull ℝ (embed '' (U : Set (Lattice n)))
    (0 : Ambient n) ∈ interior P ∧
      (∃ W : Finset (Lattice n), realPolar P = convexHull ℝ (embed '' (W : Set (Lattice n)))) ∧
      P.extremePoints ℝ = embed '' (U : Set (Lattice n)) ∧
      (∀ x : Lattice n, embed x ∈ P ↔ x = 0 ∨ x ∈ U) := by
  classical
  letI : Nonempty (Fin n) := ⟨⟨0,hn⟩⟩
  have hne : U.Nonempty := by
    by_contra h
    have he : U = ∅ := Finset.not_nonempty_iff_eq_empty.1 h
    simpa [he] using hpos
  have hz := zero_mem_hull U hne hpos
  have hspan : Submodule.span ℝ (embed '' (U : Set (Lattice n))) = ⊤ := by
    apply top_unique
    intro x _
    apply PointedCone.hull_le_span ℝ (embed '' (U : Set (Lattice n)))
    rw [hpos]
    trivial
  obtain ⟨W,hW⟩ := polarCarrier_lattice_polytope U hU hpos
  have hpolar := realPolar_hull_eq_polarCarrier U
  have hbi := realPolar_polarCarrier U hz
  have hPW : convexHull ℝ (embed '' (U : Set (Lattice n))) = polarCarrier W := by
    rw [← hbi,hW,realPolar_hull_eq_polarCarrier]
  refine ⟨?_,⟨W,hpolar.trans hW⟩,
    LatticeHull.extremePoints_convexHull_eq_rays (U : Set (Lattice n))
      U.finite_toSet hU hspan hzero,?_⟩
  · rw [hPW]
    exact zero_mem_interior_polarCarrier W
  · intro x
    constructor
    · exact LatticeHull.latticePoint_convexHull_eq_zero_or_mem _ hU hspan x
    · rintro (rfl | hx)
      · simpa [embed] using hz
      · exact subset_convexHull ℝ _ ⟨x,hx,rfl⟩

#print axioms Unimodular.GenericReflexivity.terminal_reflexive_hull

end Unimodular.GenericReflexivity

end

end CanonicalSeedRecovered1

section CanonicalSeedRecovered2


noncomputable section

open scoped BigOperators

namespace Unimodular.GenericProjectivity

open GenericReflexivity

variable {n : ℕ}

private theorem pairing_add_right (z x y : Ambient n) :
    realPairing z (x + y) = realPairing z x + realPairing z y := by
  rw [realPairing_comm z,realPairing_add_left,realPairing_comm x z,
    realPairing_comm y z]

private theorem pairing_smul_right (a : ℝ) (z x : Ambient n) :
    realPairing z (a • x) = a * realPairing z x := by
  rw [realPairing_comm z,realPairing_smul_left,realPairing_comm x z]

/-- The ordinary normal cone at a point of a convex set: its directions are
exactly the linear functionals maximized at that point. -/
def normalCone (Q : Set (Ambient n)) (q : Ambient n) : PointedCone ℝ (Ambient n) where
  carrier := {y | ∀ z ∈ Q, realPairing z y ≤ realPairing q y}
  zero_mem' := by intro z hz; simp [realPairing]
  add_mem' := by
    intro x y hx hy z hz
    rw [pairing_add_right,pairing_add_right]
    exact add_le_add (hx z hz) (hy z hz)
  smul_mem' := by
    intro a x hx z hz
    change realPairing z (a • x) ≤ realPairing q (a • x)
    simp only [← Nonneg.coe_smul,pairing_smul_right]
    exact mul_le_mul_of_nonneg_left (hx z hz) a.property

@[simp] theorem mem_normalCone (Q : Set (Ambient n)) (q y : Ambient n) :
    y ∈ normalCone Q q ↔ ∀ z ∈ Q, realPairing z y ≤ realPairing q y := Iff.rfl

private theorem pairing_self_pos {y : Ambient n} (hy : y ≠ 0) :
    0 < realPairing y y := by
  classical
  have hex : ∃ j, y j ≠ 0 := by
    by_contra h
    push_neg at h
    exact hy (funext h)
  obtain ⟨j,hj⟩ := hex
  apply Finset.sum_pos' (fun i _ => mul_self_nonneg (y i))
  exact ⟨j,Finset.mem_univ _,mul_self_pos.mpr hj⟩

/-- A nonzero normal direction has strictly positive support value on the
polar, since its origin is interior. Here a feasible positive step gives the
interior argument directly from the finite unit inequalities. -/
theorem normal_value_pos (U : Finset (Lattice n)) (q : Ambient n)
    {y : Ambient n} (hy : y ∈ normalCone (polarCarrier U) q) (hne : y ≠ 0) :
    0 < realPairing q y := by
  obtain ⟨t,ht,hstep⟩ := exists_pos_feasible_step U (fun _ => 1)
    (fun u => pairing y u) (by intros; norm_num) (by intros; norm_num at *)
  have hty : t • y ∈ polarCarrier U := by
    intro u hu
    rw [pairing_smul_left]
    exact hstep u hu
  have hh := hy (t • y) hty
  rw [realPairing_smul_left] at hh
  exact lt_of_lt_of_le (mul_pos ht (pairing_self_pos hne)) hh

/-- The cone over an exposed level-one face of the actual ray hull is exactly
an actual normal cone of the actual polar. The equality proves the geometric
normal-fan interpretation; no projectivity assertion is assumed. -/
theorem normalCone_eq_radial_hull (U : Finset (Lattice n)) (q : Lattice n)
    (hzero : (0 : Ambient n) ∈ convexHull ℝ (embed '' (U : Set (Lattice n)))) :
    normalCone (polarCarrier U) (embed q) =
      PointedCone.hull ℝ
        {x | x ∈ convexHull ℝ (embed '' (U : Set (Lattice n))) ∧ pairing x q = 1} := by
  apply le_antisymm
  · intro y hy
    by_cases hy0 : y = 0
    · subst y
      exact (PointedCone.hull ℝ _).zero_mem
    let s := realPairing (embed q) y
    have hs : 0 < s := normal_value_pos U (embed q) hy hy0
    let x : Ambient n := s⁻¹ • y
    have hpolar : x ∈ realPolar (polarCarrier U) := by
      intro z hz
      change realPairing z (s⁻¹ • y) ≤ 1
      rw [pairing_smul_right]
      calc
        s⁻¹ * realPairing z y ≤ s⁻¹ * s :=
          mul_le_mul_of_nonneg_left (hy z hz) (inv_nonneg.mpr hs.le)
        _ = 1 := inv_mul_cancel₀ hs.ne'
    have hx : x ∈ convexHull ℝ (embed '' (U : Set (Lattice n))) := by
      rw [← realPolar_polarCarrier U hzero]
      exact hpolar
    have hlevel : pairing x q = 1 := by
      change realPairing (s⁻¹ • y) (embed q) = 1
      rw [realPairing_smul_left,realPairing_comm y (embed q)]
      exact inv_mul_cancel₀ hs.ne'
    have hcone := (PointedCone.hull ℝ
      {x | x ∈ convexHull ℝ (embed '' (U : Set (Lattice n))) ∧ pairing x q = 1}).smul_mem
      hs.le (PointedCone.subset_hull ⟨hx,hlevel⟩)
    simpa only [x,smul_smul,mul_inv_cancel₀ hs.ne',one_smul] using hcone
  · apply Submodule.span_le.2
    intro x hx z hz
    have hz' : z ∈ realPolar (convexHull ℝ (embed '' (U : Set (Lattice n)))) := by
      rw [realPolar_hull_eq_polarCarrier]
      exact hz
    have hh := hz' x hx.1
    rw [realPairing_comm z x,realPairing_comm (embed q) x]
    change realPairing x z ≤ pairing x q
    rw [hx.2]
    exact hh

/-- Consequently every integral point of the polar gives the same geometric
cone in the radial-face and normal-functional constructions. -/
theorem normalCone_mem_eq_radial (U : Finset (Lattice n)) (q : Lattice n)
    (hzero : (0 : Ambient n) ∈ convexHull ℝ (embed '' (U : Set (Lattice n))))
    (_hq : embed q ∈ polarCarrier U) (y : Ambient n) :
    (∀ z ∈ polarCarrier U, realPairing z y ≤ realPairing (embed q) y) ↔
      y ∈ PointedCone.hull ℝ
        {x | x ∈ convexHull ℝ (embed '' (U : Set (Lattice n))) ∧ pairing x q = 1} := by
  change y ∈ normalCone (polarCarrier U) (embed q) ↔ _
  rw [normalCone_eq_radial_hull U q hzero]

#print axioms normalCone_eq_radial_hull

/-- The same actual normal-cone identity for every real point. This form is
needed to identify all normal cones, including those at nonintegral relative
interior points of positive-dimensional faces of the polar. -/
theorem normalCone_eq_radial_hull_real (U : Finset (Lattice n)) (q : Ambient n)
    (hzero : (0 : Ambient n) ∈ convexHull ℝ (embed '' (U : Set (Lattice n)))) :
    normalCone (polarCarrier U) q =
      PointedCone.hull ℝ
        {x | x ∈ convexHull ℝ (embed '' (U : Set (Lattice n))) ∧ realPairing x q = 1} := by
  apply le_antisymm
  · intro y hy
    by_cases hy0 : y = 0
    · subst y
      exact (PointedCone.hull ℝ _).zero_mem
    let s := realPairing q y
    have hs : 0 < s := normal_value_pos U q hy hy0
    let x : Ambient n := s⁻¹ • y
    have hpolar : x ∈ realPolar (polarCarrier U) := by
      intro z hz
      change realPairing z (s⁻¹ • y) ≤ 1
      rw [pairing_smul_right]
      calc
        s⁻¹ * realPairing z y ≤ s⁻¹ * s :=
          mul_le_mul_of_nonneg_left (hy z hz) (inv_nonneg.mpr hs.le)
        _ = 1 := inv_mul_cancel₀ hs.ne'
    have hx : x ∈ convexHull ℝ (embed '' (U : Set (Lattice n))) := by
      rw [← realPolar_polarCarrier U hzero]
      exact hpolar
    have hlevel : realPairing x q = 1 := by
      change realPairing (s⁻¹ • y) q = 1
      rw [realPairing_smul_left,realPairing_comm y q]
      exact inv_mul_cancel₀ hs.ne'
    have hcone := (PointedCone.hull ℝ
      {x | x ∈ convexHull ℝ (embed '' (U : Set (Lattice n))) ∧ realPairing x q = 1}).smul_mem
      hs.le (PointedCone.subset_hull ⟨hx,hlevel⟩)
    simpa only [x,smul_smul,mul_inv_cancel₀ hs.ne',one_smul] using hcone
  · apply Submodule.span_le.2
    intro x hx z hz
    have hz' : z ∈ realPolar (convexHull ℝ (embed '' (U : Set (Lattice n)))) := by
      rw [realPolar_hull_eq_polarCarrier]
      exact hz
    have hh := hz' x hx.1
    rw [realPairing_comm z x,realPairing_comm q x,hx.2]
    exact hh

#print axioms normalCone_eq_radial_hull_real

end Unimodular.GenericProjectivity

end

end CanonicalSeedRecovered2

section CanonicalSeedRecovered3


/-!
# The actual radial seed fan of the terminal reflexive ray hull

The cones are generated by genuine supporting faces of the ray hull. Their
lattice rationality, salience, pairwise intersections, and complete coverage
are established before the fan is constructed.
-/

open Set
open scoped BigOperators

noncomputable section

namespace Unimodular.GenericReflexivity

open TauCeti.Toric

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

/-- The ordinary real convex hull of the given lattice rays. -/
def rayHull (U : Finset (Lattice n)) : Set (Ambient n) :=
  convexHull ℝ (embed '' (U : Set (Lattice n)))

/-- The linear support functional supplied by a lattice point of the polar. -/
def polarFunctional (q : Lattice n) : Ambient n →ₗ[ℝ] ℝ where
  toFun x := pairing x q
  map_add' x y := pairing_add_left x y q
  map_smul' c x := pairing_smul_left c x q

@[simp] theorem polarFunctional_apply (q : Lattice n) (x : Ambient n) :
    polarFunctional q x = pairing x q := rfl

/-- The genuine exposed supporting face, including the possibility of emptiness. -/
def polarFace (U : Finset (Lattice n)) (q : Lattice n) : Set (Ambient n) :=
  {x | x ∈ rayHull U ∧ pairing x q = 1}

/-- The original lattice vectors lying on the supporting hyperplane. -/
def faceGenerators (U : Finset (Lattice n)) (q : Lattice n) : Finset (Lattice n) :=
  U.filter (fun u => pairing (embed u) q = 1)

@[simp] theorem mem_faceGenerators (U : Finset (Lattice n)) (q u : Lattice n) :
    u ∈ faceGenerators U q ↔ u ∈ U ∧ pairing (embed u) q = 1 := by
  simp [faceGenerators]

/-- The radial cone is the actual nonnegative cone of the geometric face. -/
def radialCone (U : Finset (Lattice n)) (q : Lattice n) :
    PointedCone ℝ (Ambient n) := PointedCone.hull ℝ (polarFace U q)

theorem rayHull_eq_polarCarrier (U W : Finset (Lattice n))
    (hW : polarCarrier U = convexHull ℝ (embed '' (W : Set (Lattice n))))
    (hz : (0 : Ambient n) ∈ rayHull U) : rayHull U = polarCarrier W := by
  change convexHull ℝ (embed '' (U : Set (Lattice n))) = _
  rw [← realPolar_polarCarrier U hz, hW, realPolar_hull_eq_polarCarrier]

theorem polar_vertex_mem (U W : Finset (Lattice n))
    (hW : polarCarrier U = convexHull ℝ (embed '' (W : Set (Lattice n))))
    {q : Lattice n} (hq : q ∈ W) : embed q ∈ polarCarrier U := by
  rw [hW]
  exact subset_convexHull ℝ _ ⟨q, hq, rfl⟩

theorem pairing_le_one_on_rayHull (U : Finset (Lattice n)) (q : Lattice n)
    (hq : embed q ∈ polarCarrier U) {x : Ambient n} (hx : x ∈ rayHull U) :
    pairing x q ≤ 1 := by
  have hp : embed q ∈ realPolar (rayHull U) := by
    rw [rayHull, realPolar_hull_eq_polarCarrier]
    exact hq
  exact hp x hx

theorem polarFace_convex (U : Finset (Lattice n)) (q : Lattice n) :
    Convex ℝ (polarFace U q) := by
  intro x hx y hy a b ha hb hab
  refine ⟨(convex_convexHull ℝ _) hx.1 hy.1 ha hb hab, ?_⟩
  rw [pairing_add_left, pairing_smul_left, pairing_smul_left, hx.2, hy.2]
  simpa using hab

theorem polarFace_extreme (U : Finset (Lattice n)) (q : Lattice n)
    (hq : embed q ∈ polarCarrier U) :
    IsExtreme ℝ (rayHull U) (polarFace U q) := by
  refine ⟨fun _ hx => hx.1, ?_⟩
  rintro x hx y hy z hz ⟨a, b, ha, hb, hab, he⟩
  refine ⟨hx, ?_⟩
  have hxl := pairing_le_one_on_rayHull U q hq hx
  have hyl := pairing_le_one_on_rayHull U q hq hy
  have hh := congrArg (fun p => pairing p q) he
  rw [pairing_add_left, pairing_smul_left, pairing_smul_left, hz.2] at hh
  nlinarith

/-- An exposed face is generated by exactly the original rays it contains. -/
theorem polarFace_eq_convexHull (U : Finset (Lattice n)) (q : Lattice n)
    (hq : embed q ∈ polarCarrier U) :
    polarFace U q = convexHull ℝ
      (embed '' (faceGenerators U q : Set (Lattice n))) := by
  rw [SeedConvexity.convex_face_eq_hull_generators
    (embed '' (U : Set (Lattice n))) (polarFace U q)
    (polarFace_convex U q) (polarFace_extreme U q hq)]
  congr 1
  ext x
  constructor
  · rintro ⟨⟨u, hu, rfl⟩, hface⟩
    exact ⟨u, (mem_faceGenerators U q u).2 ⟨hu, hface.2⟩, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨hu, he⟩ := (mem_faceGenerators U q u).1 hu
    exact ⟨⟨u, hu, rfl⟩, subset_convexHull ℝ _ ⟨u, hu, rfl⟩, he⟩

theorem radialCone_eq_hull_generators (U : Finset (Lattice n)) (q : Lattice n)
    (hq : embed q ∈ polarCarrier U) :
    radialCone U q = PointedCone.hull ℝ
      (embed '' (faceGenerators U q : Set (Lattice n))) := by
  rw [radialCone, polarFace_eq_convexHull U q hq]
  apply le_antisymm
  · exact Submodule.span_le.2 (convexHull_min PointedCone.subset_hull
      (PointedCone.hull ℝ (embed '' (faceGenerators U q : Set (Lattice n)))).convex)
  · exact Submodule.span_mono (subset_convexHull ℝ _)

/-- Both lattice rationality and salience are proved for the actual cone. -/
theorem radialCone_toric (U : Finset (Lattice n)) (q : Lattice n)
    (hq : embed q ∈ polarCarrier U) :
    IsToricCone (FanBridge.standardEmbedding n) (radialCone U q) := by
  refine ⟨isLatticeRational_iff.2 ⟨faceGenerators U q, ?_⟩, ?_⟩
  · exact radialCone_eq_hull_generators U q hq
  · exact NormalizedConeFaces.hull_salient (polarFace U q) (polarFunctional q)
      (fun _ hx => hx.2)

/-- The intersection of two supporting faces is a genuine face of either. -/
theorem polarFace_inter_extreme (U : Finset (Lattice n)) (q r : Lattice n)
    (hr : embed r ∈ polarCarrier U) :
    IsExtreme ℝ (polarFace U q) (polarFace U q ∩ polarFace U r) := by
  refine ⟨Set.inter_subset_left, ?_⟩
  intro x hx y hy z hz hseg
  exact ⟨hx, (polarFace_extreme U r hr).left_mem_of_mem_openSegment
    hx.1 hy.1 hz.2 hseg⟩

/-- Supporting levels force the radial scales on an intersection to agree. -/
theorem radialCone_inter_isFaceOf (U : Finset (Lattice n)) (q r : Lattice n)
    (hq : embed q ∈ polarCarrier U) (hr : embed r ∈ polarCarrier U) :
    (radialCone U q ⊓ radialCone U r).IsFaceOf (radialCone U q) := by
  have he := NormalizedConeFaces.hull_inter (polarFace U q) (polarFace U r)
    (polarFace_convex U q) (polarFace_convex U r)
    (polarFunctional q) (polarFunctional r)
    (fun _ hx => hx.2) (fun _ hx => hx.2)
    (fun _ hx => pairing_le_one_on_rayHull U q hq hx.1)
    (fun _ hx => pairing_le_one_on_rayHull U r hr hx.1)
  change (PointedCone.hull ℝ (polarFace U q) ⊓
    PointedCone.hull ℝ (polarFace U r)).IsFaceOf _
  rw [← he]
  exact NormalizedConeFaces.hull_isFaceOf (polarFace U q)
    (polarFace U q ∩ polarFace U r) (polarFace_convex U q)
    ((polarFace_convex U q).inter (polarFace_convex U r))
    (polarFace_inter_extreme U q r hr) (polarFunctional q) (fun _ hx => hx.2)

/-- The actual finite rational fan consisting of all faces of the radial cones
exposed by a finite lattice presentation of the polar. -/
def seedFan (U W : Finset (Lattice n))
    (hW : polarCarrier U = convexHull ℝ (embed '' (W : Set (Lattice n)))) :
    Fan (FanBridge.standardEmbedding n) :=
  Fan.ofCones (FanBridge.standardEmbedding_isIntegralLattice n)
    (radialCone U '' (W : Set (Lattice n)))
    (W.finite_toSet.image (radialCone U))
    (by
      rintro C ⟨q, hq, rfl⟩
      exact radialCone_toric U q (polar_vertex_mem U W hW hq))
    (by
      rintro C D ⟨q, hq, rfl⟩ ⟨r, hr, rfl⟩
      exact radialCone_inter_isFaceOf U q r
        (polar_vertex_mem U W hW hq) (polar_vertex_mem U W hW hr))

theorem mem_seedFan_cones (U W : Finset (Lattice n))
    (hW : polarCarrier U = convexHull ℝ (embed '' (W : Set (Lattice n))))
    (C : PointedCone ℝ (Ambient n)) :
    C ∈ (seedFan U W hW).cones ↔ ∃ q ∈ W, C.IsFaceOf (radialCone U q) := by
  unfold seedFan
  rw [TauCeti.Toric.Fan.mem_ofCones_cones]
  constructor
  · rintro ⟨D, ⟨q, hq, rfl⟩, hC⟩
    exact ⟨q, hq, hC⟩
  · rintro ⟨q, hq, hC⟩
    exact ⟨radialCone U q, ⟨q, hq, rfl⟩, hC⟩

theorem radialCone_mem_seedFan (U W : Finset (Lattice n))
    (hW : polarCarrier U = convexHull ℝ (embed '' (W : Set (Lattice n))))
    {q : Lattice n} (hq : q ∈ W) : radialCone U q ∈ (seedFan U W hW).cones :=
  (mem_seedFan_cones U W hW _).2 ⟨q, hq, PointedCone.IsFaceOf.refl _⟩

/-- Maximizing over the finite polar vertices normalizes every nonzero direction
to an actual supporting face. A positive feasible step from the origin proves
that the maximizing level is strictly positive. -/
theorem exists_radial_normalization (U W : Finset (Lattice n))
    (hW : polarCarrier U = convexHull ℝ (embed '' (W : Set (Lattice n))))
    (hz : (0 : Ambient n) ∈ rayHull U) {x : Ambient n} (hx : x ≠ 0) :
    ∃ q ∈ W, ∃ t : ℝ, 0 < t ∧ ∃ y ∈ polarFace U q, x = t • y := by
  classical
  have hWne : W.Nonempty := by
    by_contra h
    have he : W = ∅ := Finset.not_nonempty_iff_eq_empty.1 h
    have h0 := zero_mem_polarCarrier U
    rw [hW, he] at h0
    simpa using h0
  obtain ⟨q, hq, hmax⟩ := W.exists_max_image (fun q => pairing x q) hWne
  have hmaxQ : ∀ p ∈ polarCarrier U, realPairing p x ≤ pairing x q := by
    rw [hW]
    change convexHull ℝ (embed '' (W : Set (Lattice n))) ⊆
      {p | realPairing p x ≤ pairing x q}
    apply convexHull_min
    · rintro p ⟨w, hw, rfl⟩
      change realPairing (embed w) x ≤ pairing x q
      have he : realPairing (embed w) x = pairing x w := realPairing_comm _ _
      rw [he]
      exact hmax w hw
    · intro a ha b hb t s ht hs hts
      change realPairing (t • a + s • b) x ≤ pairing x q
      rw [realPairing_add_left, realPairing_smul_left, realPairing_smul_left]
      calc
        _ ≤ t * pairing x q + s * pairing x q :=
          add_le_add (mul_le_mul_of_nonneg_left ha ht)
            (mul_le_mul_of_nonneg_left hb hs)
        _ = pairing x q := by rw [← add_mul, hts, one_mul]
  obtain ⟨ε, hε, hstep⟩ := exists_pos_feasible_step U
    (fun _ => (1 : ℝ)) (fun u => pairing x u)
    (by intros; norm_num) (by intros; norm_num at *)
  have hεx : ε • x ∈ polarCarrier U := by
    intro u hu
    rw [pairing_smul_left]
    exact hstep u hu
  have hself : 0 < realPairing x x := by
    obtain ⟨i, hi⟩ : ∃ i, x i ≠ 0 := by
      by_contra h
      push_neg at h
      exact hx (funext h)
    exact Finset.sum_pos' (fun j _ => mul_self_nonneg (x j))
      ⟨i, Finset.mem_univ _, mul_self_pos.2 hi⟩
  have hlevel : 0 < pairing x q := by
    have hh := hmaxQ (ε • x) hεx
    rw [realPairing_smul_left] at hh
    exact (mul_pos hε hself).trans_le hh
  let y : Ambient n := (pairing x q)⁻¹ • x
  have hy : y ∈ polarFace U q := by
    refine ⟨?_, ?_⟩
    · rw [rayHull_eq_polarCarrier U W hW hz]
      intro w hw
      change pairing ((pairing x q)⁻¹ • x) w ≤ 1
      rw [pairing_smul_left]
      calc
        _ ≤ (pairing x q)⁻¹ * pairing x q :=
          mul_le_mul_of_nonneg_left (hmax w hw) (inv_nonneg.2 hlevel.le)
        _ = 1 := inv_mul_cancel₀ hlevel.ne'
    · change pairing ((pairing x q)⁻¹ • x) q = 1
      rw [pairing_smul_left, inv_mul_cancel₀ hlevel.ne']
  refine ⟨q, hq, pairing x q, hlevel, y, hy, ?_⟩
  dsimp only [y]
  rw [smul_smul, mul_inv_cancel₀ hlevel.ne', one_smul]

/-- The radial seed is complete, as a genuine fan, with no covering assumption. -/
theorem seedFan_complete (U W : Finset (Lattice n))
    (hW : polarCarrier U = convexHull ℝ (embed '' (W : Set (Lattice n))))
    (hz : (0 : Ambient n) ∈ rayHull U) : (seedFan U W hW).IsComplete := by
  apply ((seedFan U W hW).isComplete_iff).2
  intro x
  by_cases hx : x = 0
  · have hWne : W.Nonempty := by
      by_contra h
      have he : W = ∅ := Finset.not_nonempty_iff_eq_empty.1 h
      have h0 := zero_mem_polarCarrier U
      rw [hW, he] at h0
      simpa using h0
    obtain ⟨q, hq⟩ := hWne
    exact ⟨radialCone U q, radialCone_mem_seedFan U W hW hq,
      by simpa only [hx] using (radialCone U q).zero_mem⟩
  · obtain ⟨q, hq, t, ht, y, hy, rfl⟩ := exists_radial_normalization U W hW hz hx
    exact ⟨radialCone U q, radialCone_mem_seedFan U W hW hq,
      (radialCone U q).smul_mem ht.le (PointedCone.subset_hull hy)⟩

#print axioms Unimodular.GenericReflexivity.radialCone_toric
#print axioms Unimodular.GenericReflexivity.seedFan_complete

end Unimodular.GenericReflexivity
end

end CanonicalSeedRecovered3

section CanonicalSeedRecovered4


noncomputable section

namespace Unimodular.GenericReflexivity

open TauCeti.Toric
open scoped BigOperators

variable {n : ℕ}

/-- A point of a convex subset with exactly its universally active inequalities.
This is finite midpoint averaging in the actual halfspace intersection. -/
theorem exists_common_active_point (W : Finset (Lattice n)) {E : Set (Ambient n)}
    (hE : Convex ℝ E) (hEP : E ⊆ polarCarrier W) (hne : E.Nonempty) :
    ∃ p ∈ E, ∀ u ∈ W, pairing p u = 1 → ∀ x ∈ E, pairing x u = 1 := by
  classical
  have aux : ∀ s : Finset (Lattice n), s ⊆ W →
      ∃ p ∈ E, ∀ u ∈ s, pairing p u = 1 → ∀ x ∈ E, pairing x u = 1 := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      intro hs
      obtain ⟨p,hp⟩ := hne
      exact ⟨p,hp,by simp⟩
    | @insert a s ha ih =>
      intro hs
      obtain ⟨p,hp,hpa⟩ := ih (fun u hu => hs (Finset.mem_insert_of_mem hu))
      by_cases hall : ∀ x ∈ E, pairing x a = 1
      · refine ⟨p,hp,?_⟩
        intro u hu he
        rcases Finset.mem_insert.1 hu with rfl | hu
        · exact hall
        · exact hpa u hu he
      · push_neg at hall
        obtain ⟨q,hq,hqa⟩ := hall
        let r : Ambient n := (1 / 2 : ℝ) • p + (1 / 2 : ℝ) • q
        have hr : r ∈ E := hE hp hq (by norm_num) (by norm_num) (by norm_num)
        refine ⟨r,hr,?_⟩
        intro u hu he
        have hpu := hEP hp u (hs hu)
        have hqu := hEP hq u (hs hu)
        have he' : (1 / 2 : ℝ) * pairing p u + (1 / 2 : ℝ) * pairing q u = 1 := by
          simpa only [r,pairing_add_left,pairing_smul_left] using he
        rcases Finset.mem_insert.1 hu with rfl | hu
        · exfalso
          apply hqa
          linarith
        · apply hpa u hu
          linarith
  exact aux W (fun u hu => hu)

/-- Every nonempty proper geometric face lies in one of the actual supporting
faces indexed by the displayed lattice points of the polar. -/
theorem proper_face_subset_polarFace (U W : Finset (Lattice n))
    (hW : polarCarrier U = convexHull ℝ (embed '' (W : Set (Lattice n))))
    (hz : (0 : Ambient n) ∈ rayHull U) {E : Set (Ambient n)}
    (hE : Convex ℝ E) (he : IsExtreme ℝ (rayHull U) E)
    (hne : E.Nonempty) (hproper : E ≠ rayHull U) :
    ∃ q ∈ W, E ⊆ polarFace U q := by
  have hP := rayHull_eq_polarCarrier U W hW hz
  have hEW : E ⊆ polarCarrier W := fun x hx => hP ▸ he.subset hx
  obtain ⟨p,hp,hpa⟩ := exists_common_active_point W hE hEW hne
  have hactive : ∃ q ∈ W, pairing p q = 1 := by
    by_contra h
    push_neg at h
    apply hproper
    apply Set.Subset.antisymm he.subset
    intro x hx
    obtain ⟨t,ht,hstep⟩ := exists_pos_feasible_step W
      (fun u => 1 - pairing p u) (fun u => pairing (p - x) u)
      (fun u hu => sub_nonneg.2 (hEW hp u hu)) (by
        intro u hu hzero
        exact False.elim (h u hu (by linarith)))
    let y : Ambient n := p + t • (p - x)
    have hy : y ∈ rayHull U := by
      rw [hP]
      intro u hu
      dsimp [y]
      rw [pairing_add_left,pairing_smul_left]
      linarith [hstep u hu]
    apply he.left_mem_of_mem_openSegment hx hy hp
    have hden : 0 < 1 + t := by linarith
    refine ⟨t / (1 + t),1 / (1 + t),div_pos ht hden,div_pos zero_lt_one hden,?_,?_⟩
    · field_simp <;> ring
    · ext i
      simp only [y,Pi.add_apply,Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
      field_simp <;> ring
  obtain ⟨q,hq,hpq⟩ := hactive
  exact ⟨q,hq,fun x hx => ⟨he.subset hx,hpa q hq hpq x hx⟩⟩

/-- The polar's finite lattice presentation is nonempty, because it contains 0. -/
theorem polar_hull_nonempty (U W : Finset (Lattice n))
    (hW : polarCarrier U = convexHull ℝ (embed '' (W : Set (Lattice n)))) : W.Nonempty := by
  have hh : (convexHull ℝ (embed '' (W : Set (Lattice n)))).Nonempty :=
    ⟨0,hW ▸ zero_mem_polarCarrier U⟩
  obtain ⟨z,⟨w,hw,rfl⟩⟩ := (convexHull_nonempty_iff (𝕜 := ℝ)).1 hh
  exact ⟨w,hw⟩

/-- Literal identification of every seed cone with a cone over an actual
proper convex extreme face, including the empty face and the zero cone. -/
theorem seedFan_cones_iff_proper_faces (U W : Finset (Lattice n))
    (hW : polarCarrier U = convexHull ℝ (embed '' (W : Set (Lattice n))))
    (hz : (0 : Ambient n) ∈ rayHull U) (C : PointedCone ℝ (Ambient n)) :
    C ∈ (seedFan U W hW).cones ↔
      ∃ E : Set (Ambient n), Convex ℝ E ∧ IsExtreme ℝ (rayHull U) E ∧
        E ≠ rayHull U ∧ C = PointedCone.hull ℝ E := by
  constructor
  · intro hC
    obtain ⟨q,hq,hCq⟩ := (mem_seedFan_cones U W hW C).1 hC
    have hqQ : embed q ∈ polarCarrier U := by
      rw [hW]
      exact subset_convexHull ℝ _ ⟨q,hq,rfl⟩
    have hc := polarFace_convex U q
    have hf := polarFace_extreme U q hqQ
    obtain ⟨hEc,hEf⟩ := NormalizedConeFaces.section_is_face (polarFace U q) hc hCq
    refine ⟨polarFace U q ∩ (C : Set (Ambient n)),hEc,hf.trans hEf,?_,?_⟩
    · intro heq
      have hh : (0 : Ambient n) ∈ polarFace U q := (heq.symm ▸ hz).1
      have hbad := hh.2
      simpa [pairing] using hbad
    · exact (NormalizedConeFaces.hull_section (polarFace U q) hc (polarFunctional q)
        (fun x hx => hx.2) hCq).symm
  · rintro ⟨E,hEc,hEf,hproper,rfl⟩
    apply (mem_seedFan_cones U W hW _).2
    rcases E.eq_empty_or_nonempty with rfl | hne
    · obtain ⟨q,hq⟩ := polar_hull_nonempty U W hW
      exact ⟨q,hq,by simpa using
        (radialCone_toric U q (polar_vertex_mem U W hW hq)).salient.bot_isFaceOf⟩
    · obtain ⟨q,hq,hsub⟩ := proper_face_subset_polarFace U W hW hz hEc hEf hne hproper
      have hqQ : embed q ∈ polarCarrier U := by
        rw [hW]
        exact subset_convexHull ℝ _ ⟨q,hq,rfl⟩
      have hface : IsExtreme ℝ (polarFace U q) E :=
        ⟨hsub,fun _ hx _ hy _ he hseg =>
          hEf.left_mem_of_mem_openSegment hx.1 hy.1 he hseg⟩
      exact ⟨q,hq,NormalizedConeFaces.hull_isFaceOf (polarFace U q) E
        (polarFace_convex U q) hEc hface (polarFunctional q) (fun _ hx => hx.2)⟩

/-- The radial seed is independent of the finite lattice presentation chosen
for the polar; both fans have exactly the same intrinsic proper-face cones. -/
theorem seedFan_independent_of_polar_presentation (U W W' : Finset (Lattice n))
    (hW : polarCarrier U = convexHull ℝ (embed '' (W : Set (Lattice n))))
    (hW' : polarCarrier U = convexHull ℝ (embed '' (W' : Set (Lattice n))))
    (hz : (0 : Ambient n) ∈ rayHull U) : seedFan U W hW = seedFan U W' hW' := by
  apply Fan.ext
  ext C
  exact (seedFan_cones_iff_proper_faces U W hW hz C).trans
    (seedFan_cones_iff_proper_faces U W' hW' hz C).symm

/-- Every ray of the canonical seed is one of the original nonzero lattice
vectors, and every original vertex supplies its singleton face and hence its ray. -/
theorem seedFan_hasRays (U W : Finset (Lattice n))
    (hW : polarCarrier U = convexHull ℝ (embed '' (W : Set (Lattice n))))
    (hz : (0 : Ambient n) ∈ rayHull U)
    (hzero : (0 : Lattice n) ∉ U)
    (hvertices : (rayHull U).extremePoints ℝ = embed '' (U : Set (Lattice n))) :
    AllowedBlocks.HasRays (FanBridge.standardEmbedding n)
      (fun u : (U : Set (Lattice n)) => u.val) (seedFan U W hW) := by
  classical
  intro R
  constructor
  · rintro ⟨hR,hdim⟩
    obtain ⟨E,hEc,hEf,hproper,hRE⟩ := (seedFan_cones_iff_proper_faces U W hW hz R).1 hR
    let G : Set (Ambient n) := (embed '' (U : Set (Lattice n))) ∩ E
    have hEgen : E = convexHull ℝ G :=
      SeedConvexity.convex_face_eq_hull_generators _ E hEc hEf
    have hRG : R = PointedCone.hull ℝ G := by
      rw [hRE,hEgen]
      apply le_antisymm
      · exact Submodule.span_le.2 (convexHull_min PointedCone.subset_hull
          (PointedCone.hull ℝ G).convex)
      · exact Submodule.span_mono (subset_convexHull ℝ G)
    let ρ : ToricRay R := ⟨⟨R,PointedCone.IsFaceOf.refl _⟩,hdim⟩
    have hne : G.Nonempty := by
      by_contra h
      have he : G = ∅ := Set.not_nonempty_iff_eq_empty.1 h
      apply ρ.toPointedCone_ne_bot
      change R = ⊥
      rw [hRG,he]
      simp
    obtain ⟨v,⟨u,hu,rfl⟩,huE⟩ := hne
    have hu0 : embed u ≠ 0 := by
      intro he
      have hu0 : u = 0 := LatticeHull.embed_injective (by simpa [embed] using he)
      exact hzero (hu0 ▸ hu)
    have hv : embed u ∈ R := by rw [hRE]; exact PointedCone.subset_hull huE
    refine ⟨⟨u,hu⟩,?_⟩
    exact ρ.eq_hull_singleton ((seedFan U W hW).isToricCone hR).salient hv hu0
  · rintro ⟨u,rfl⟩
    have hu0 : embed u.val ≠ 0 := by
      intro he
      have hu : u.val = 0 := LatticeHull.embed_injective (by simpa [embed] using he)
      exact hzero (hu ▸ u.property)
    have huv : embed u.val ∈ (rayHull U).extremePoints ℝ := by
      rw [hvertices]
      exact ⟨u.val,u.property,rfl⟩
    refine ⟨(seedFan_cones_iff_proper_faces U W hW hz _).2
      ⟨{embed u.val},convex_singleton _,isExtreme_singleton.2 huv,?_,rfl⟩,
      PointedCone.finrank_span_coe_hull_singleton hu0⟩
    intro he
    have hh : (0 : Ambient n) = embed u.val := Set.mem_singleton_iff.1 (he.symm ▸ hz)
    exact hu0 hh.symm

/-- The oriented ray equality is also equality of the actual primitive lattice
vectors, not merely equality after arbitrary positive rescaling. -/
theorem seedFan_isRay_iff (U W : Finset (Lattice n))
    (hW : polarCarrier U = convexHull ℝ (embed '' (W : Set (Lattice n))))
    (hz : (0 : Ambient n) ∈ rayHull U)
    (hzero : (0 : Lattice n) ∉ U)
    (hvertices : (rayHull U).extremePoints ℝ = embed '' (U : Set (Lattice n)))
    (hprimitive : ∀ u ∈ U, PrimitiveLatticeVector u) (u : Lattice n) :
    ConeBases.IsRay (seedFan U W hW) u ↔ u ∈ U := by
  let Φ := seedFan U W hW
  have hrays := seedFan_hasRays U W hW hz hzero hvertices
  constructor
  · rintro ⟨C,hC,ρ,hu⟩
    have hρ : ρ.toPointedCone ∈ Φ.cones := Φ.mem_of_isFaceOf hC ρ.val.isFaceOf
    obtain ⟨v,hv⟩ := (hrays ρ.toPointedCone).1 ⟨hρ,ρ.property⟩
    have hvgen : IsPrimitiveGenerator (FanBridge.standardEmbedding n) ρ v.val := by
      refine isPrimitiveGenerator_iff.2 ⟨?_,(primitiveLatticeVector_iff_isPrimitive v.val).1 (hprimitive v.val v.property)⟩
      change embed v.val ∈ ρ.toPointedCone
      rw [hv]
      exact PointedCone.subset_hull (Set.mem_singleton _)
    have he : u = v.val := IsPrimitiveGenerator.unique Φ.lattice
      ((Φ.isToricCone hC).salient.anti ρ.val.isFaceOf.le) hu hvgen
    exact he.symm ▸ v.property
  · intro hu
    let R := AllowedBlocks.ray (embed u)
    obtain ⟨hR,hd⟩ := (hrays R).2 ⟨⟨u,hu⟩,rfl⟩
    let ρ : ToricRay R := ⟨⟨R,PointedCone.IsFaceOf.refl R⟩,hd⟩
    refine ⟨R,hR,ρ,isPrimitiveGenerator_iff.2 ⟨?_,(primitiveLatticeVector_iff_isPrimitive u).1 (hprimitive u hu)⟩⟩
    exact PointedCone.subset_hull (Set.mem_singleton _)

/-- The same fan has the literal normal-fan presentation of the actual integral
polar polytope. This records the projective fan geometry without assuming it. -/
theorem seedFan_cones_iff_normal_cones (U W : Finset (Lattice n))
    (hW : polarCarrier U = convexHull ℝ (embed '' (W : Set (Lattice n))))
    (hz : (0 : Ambient n) ∈ rayHull U) (C : PointedCone ℝ (Ambient n)) :
    C ∈ (seedFan U W hW).cones ↔ ∃ q ∈ W,
      C.IsFaceOf (GenericProjectivity.normalCone (polarCarrier U) (embed q)) := by
  simpa only [GenericProjectivity.normalCone_eq_radial_hull U _ hz,
    radialCone,polarFace,rayHull] using mem_seedFan_cones U W hW C

/-- Existence of the canonical complete radial seed, exact ray equality, and
its finite integral normal-cone presentation. The all-point normal-fan
correspondence is proved separately in `GenericNormalFan`. -/
theorem canonical_seed (hn : 0 < n) (U : Finset (Lattice n))
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun u : (U : Set (Lattice n)) => u.val))
    (hpos : PointedCone.hull ℝ (embed '' (U : Set (Lattice n))) = ⊤)
    (hzero : (0 : Lattice n) ∉ U) :
    ∃ (W : Finset (Lattice n))
      (hW : polarCarrier U = convexHull ℝ (embed '' (W : Set (Lattice n)))),
      (seedFan U W hW).IsComplete ∧
      AllowedBlocks.HasRays (FanBridge.standardEmbedding n)
        (fun u : (U : Set (Lattice n)) => u.val) (seedFan U W hW) ∧
      (∀ C, C ∈ (seedFan U W hW).cones ↔
        ∃ E : Set (Ambient n), Convex ℝ E ∧ IsExtreme ℝ (rayHull U) E ∧
          E ≠ rayHull U ∧ C = PointedCone.hull ℝ E) ∧
      (∀ C, C ∈ (seedFan U W hW).cones ↔ ∃ q ∈ W,
        C.IsFaceOf (GenericProjectivity.normalCone (polarCarrier U) (embed q))) := by
  have ht := terminal_reflexive_hull hn U hU hpos hzero
  have hz : (0 : Ambient n) ∈ rayHull U := interior_subset ht.1
  obtain ⟨W,hW⟩ := polarCarrier_lattice_polytope U hU hpos
  exact ⟨W,hW,seedFan_complete U W hW hz,seedFan_hasRays U W hW hz hzero ht.2.2.1,
    seedFan_cones_iff_proper_faces U W hW hz,seedFan_cones_iff_normal_cones U W hW hz⟩

#print axioms Unimodular.GenericReflexivity.canonical_seed

end Unimodular.GenericReflexivity

end

end CanonicalSeedRecovered4

section CanonicalSeedRecovered5


/-!
# Every proper face is exposed by an actual point of the polar

The supporting point is the average of the finite polar normals that are
active on the whole face. The proof identifies the face with their full
intersection before taking this average; no exposed-face hypothesis is assumed.
-/

open Set
open scoped BigOperators

noncomputable section

namespace Unimodular.GenericReflexivity

attribute [local instance] Classical.propDecidable

variable {n : ℕ}

/-- The finite polar inequalities that are active on the entire subset. -/
def commonPolarNormals (W : Finset (Lattice n)) (E : Set (Ambient n)) :
    Finset (Lattice n) := W.filter (fun q => ∀ x ∈ E, pairing x q = 1)

@[simp] theorem mem_commonPolarNormals (W : Finset (Lattice n))
    (E : Set (Ambient n)) (q : Lattice n) :
    q ∈ commonPolarNormals W E ↔ q ∈ W ∧ ∀ x ∈ E, pairing x q = 1 := by
  simp [commonPolarNormals]

/-- A nonempty actual face is exactly the intersection of all the polar
inequalities active throughout it. The reverse inclusion extends a segment
through a common active point and uses the defining extreme-set property. -/
theorem face_eq_commonPolarNormals (U W : Finset (Lattice n))
    (hW : polarCarrier U = convexHull ℝ (embed '' (W : Set (Lattice n))))
    (hz : (0 : Ambient n) ∈ rayHull U) {E : Set (Ambient n)}
    (hEc : Convex ℝ E) (hEf : IsExtreme ℝ (rayHull U) E) (hne : E.Nonempty) :
    E = {x | x ∈ rayHull U ∧ ∀ q ∈ commonPolarNormals W E, pairing x q = 1} := by
  have hP := rayHull_eq_polarCarrier U W hW hz
  have hEW : E ⊆ polarCarrier W := fun x hx => hP ▸ hEf.subset hx
  apply Set.Subset.antisymm
  · intro x hx
    exact ⟨hEf.subset hx, fun q hq => ((mem_commonPolarNormals W E q).1 hq).2 x hx⟩
  · rintro x ⟨hx, hxa⟩
    obtain ⟨p, hp, hpa⟩ := exists_common_active_point W hEc hEW hne
    obtain ⟨t, ht, hstep⟩ := exists_pos_feasible_step W
      (fun q => 1 - pairing p q) (fun q => pairing (p - x) q)
      (fun q hq => sub_nonneg.2 (hEW hp q hq))
      (by
        intro q hq hzero
        have hpq : pairing p q = 1 := by linarith
        have hxq : pairing x q = 1 := hxa q
          ((mem_commonPolarNormals W E q).2 ⟨hq, hpa q hq hpq⟩)
        rw [pairing_sub_left, hpq, hxq]
        norm_num)
    let y : Ambient n := p + t • (p - x)
    have hy : y ∈ rayHull U := by
      rw [hP]
      intro q hq
      dsimp [y]
      rw [pairing_add_left, pairing_smul_left]
      linarith [hstep q hq]
    apply hEf.left_mem_of_mem_openSegment hx hy hp
    have hden : 0 < 1 + t := by linarith
    refine ⟨t / (1 + t), 1 / (1 + t), div_pos ht hden,
      div_pos zero_lt_one hden, ?_, ?_⟩
    · field_simp <;> ring
    · ext i
      simp only [y, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
      field_simp <;> ring

/-- A nonempty proper face has at least one common supporting inequality. -/
theorem commonPolarNormals_nonempty (U W : Finset (Lattice n))
    (hW : polarCarrier U = convexHull ℝ (embed '' (W : Set (Lattice n))))
    (hz : (0 : Ambient n) ∈ rayHull U) {E : Set (Ambient n)}
    (hEc : Convex ℝ E) (hEf : IsExtreme ℝ (rayHull U) E)
    (hne : E.Nonempty) (hproper : E ≠ rayHull U) :
    (commonPolarNormals W E).Nonempty := by
  obtain ⟨q, hq, hsub⟩ := proper_face_subset_polarFace U W hW hz hEc hEf hne hproper
  exact ⟨q, (mem_commonPolarNormals W E q).2 ⟨hq, fun x hx => (hsub hx).2⟩⟩

/-- Every proper convex extreme face is exactly the level-one face of some
actual point of the polar. The empty face is exposed by the origin. The
nonempty case uses a strictly positive average of its common active normals. -/
theorem proper_face_exposed (U W : Finset (Lattice n))
    (hW : polarCarrier U = convexHull ℝ (embed '' (W : Set (Lattice n))))
    (hz : (0 : Ambient n) ∈ rayHull U) {E : Set (Ambient n)}
    (hEc : Convex ℝ E) (hEf : IsExtreme ℝ (rayHull U) E)
    (hproper : E ≠ rayHull U) :
    ∃ z ∈ polarCarrier U, E = {x | x ∈ rayHull U ∧ realPairing x z = 1} := by
  classical
  rcases E.eq_empty_or_nonempty with rfl | hne
  · refine ⟨0, zero_mem_polarCarrier U, ?_⟩
    ext x
    simp [realPairing]
  let A := commonPolarNormals W E
  have hA : A.Nonempty := commonPolarNormals_nonempty U W hW hz hEc hEf hne hproper
  have hcard : (0 : ℝ) < A.card := by exact_mod_cast Finset.card_pos.2 hA
  let c : ℝ := (A.card : ℝ)⁻¹
  have hc : 0 < c := inv_pos.2 hcard
  have hweights : (∑ q ∈ A, c) = 1 := by
    simp only [c, Finset.sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ hcard.ne'
  let z : Ambient n := ∑ q ∈ A, c • embed q
  have hzQ : z ∈ polarCarrier U :=
    (polarCarrier_convex U).sum_mem (fun q hq => hc.le) hweights
      (fun q hq => polar_vertex_mem U W hW ((mem_commonPolarNormals W E q).1 hq).1)
  have hpair (x : Ambient n) : realPairing x z = ∑ q ∈ A, c * pairing x q := by
    rw [realPairing_comm x z]
    simp only [z, realPairing, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Finset.sum_mul]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro q hq
    simp only [pairing, embed, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hP := rayHull_eq_polarCarrier U W hW hz
  have hEeq := face_eq_commonPolarNormals U W hW hz hEc hEf hne
  refine ⟨z, hzQ, Set.Subset.antisymm ?_ ?_⟩
  · intro x hx
    have hxA := hEeq.subset hx
    refine ⟨hxA.1, ?_⟩
    rw [hpair]
    calc
      (∑ q ∈ A, c * pairing x q) = ∑ q ∈ A, c := by
        apply Finset.sum_congr rfl
        intro q hq
        rw [hxA.2 q hq, mul_one]
      _ = 1 := hweights
  · rintro x ⟨hx, hxlevel⟩
    apply hEeq.symm.subset
    refine ⟨hx, ?_⟩
    intro q hq
    have hxW : x ∈ polarCarrier W := hP ▸ hx
    have hterm : ∀ r ∈ A, c * pairing x r ≤ c := by
      intro r hr
      simpa only [mul_one] using
        mul_le_mul_of_nonneg_left
          (hxW r ((mem_commonPolarNormals W E r).1 hr).1) hc.le
    have hsum : (∑ r ∈ A, c * pairing x r) = ∑ r ∈ A, c :=
      (hpair x).symm.trans (hxlevel.trans hweights.symm)
    have heq := (Finset.sum_eq_sum_iff_of_le hterm).1 hsum q hq
    apply mul_left_cancel₀ hc.ne'
    simpa only [mul_one] using heq

#print axioms Unimodular.GenericReflexivity.proper_face_exposed

end Unimodular.GenericReflexivity
end

end CanonicalSeedRecovered5

section CanonicalSeedRecovered6


noncomputable section

namespace Unimodular.GenericReflexivity

open TauCeti.Toric
open GenericProjectivity

variable {n : ℕ}

/-- The seed is the whole ordinary normal fan of the actual polar polytope:
normal cones at all points of that polytope are exactly its fan cones. This is
stronger than matching only a displayed finite list of candidate vertex cones. -/
theorem seedFan_cones_iff_normalCone (U W : Finset (Lattice n))
    (hW : polarCarrier U = convexHull ℝ (embed '' (W : Set (Lattice n))))
    (hz : (0 : Ambient n) ∈ rayHull U) (C : PointedCone ℝ (Ambient n)) :
    C ∈ (seedFan U W hW).cones ↔
      ∃ z ∈ polarCarrier U, C = normalCone (polarCarrier U) z := by
  constructor
  · intro hC
    obtain ⟨E,hEc,hEf,hproper,hCE⟩ := (seedFan_cones_iff_proper_faces U W hW hz C).1 hC
    obtain ⟨z,hzQ,hE⟩ := proper_face_exposed U W hW hz hEc hEf hproper
    refine ⟨z,hzQ,?_⟩
    simpa only [hE,rayHull,normalCone_eq_radial_hull_real U z hz] using hCE
  · rintro ⟨z,hzQ,rfl⟩
    have hb : ∀ x ∈ rayHull U, realPairing x z ≤ 1 := by
      have hh : z ∈ realPolar (rayHull U) := by
        rw [show rayHull U = convexHull ℝ (embed '' (U : Set (Lattice n))) from rfl,
          realPolar_hull_eq_polarCarrier]
        exact hzQ
      exact hh
    let E : Set (Ambient n) := {x | x ∈ rayHull U ∧ realPairing x z = 1}
    have hEc : Convex ℝ E := by
      intro x hx y hy a b ha hb hab
      refine ⟨(convex_convexHull ℝ _) hx.1 hy.1 ha hb hab,?_⟩
      rw [realPairing_add_left,realPairing_smul_left,realPairing_smul_left,hx.2,hy.2]
      simpa using hab
    have hEf : IsExtreme ℝ (rayHull U) E := by
      refine ⟨fun _ hx => hx.1,?_⟩
      rintro x hx y hy p hp ⟨a,b,ha,hb',hab,he⟩
      refine ⟨hx,?_⟩
      have hpx := hb x hx
      have hpy := hb y hy
      have hh := congrArg (fun v => realPairing v z) he
      rw [realPairing_add_left,realPairing_smul_left,realPairing_smul_left,hp.2] at hh
      nlinarith
    apply (seedFan_cones_iff_proper_faces U W hW hz _).2
    refine ⟨E,hEc,hEf,?_,normalCone_eq_radial_hull_real U z hz⟩
    intro he
    have hh : (0 : Ambient n) ∈ E := he.symm ▸ hz
    have hbad := hh.2
    simpa [realPairing] using hbad

/-- The complete geometric assertion of Lemma3.2 on the standard integral
lattice: terminal reflexivity, exact vertices and lattice points, and a genuine
complete radial fan which is exactly the normal fan of the integral polar.
No fan, vertex list, boundedness, integrality, or projectivity is a hypothesis. -/
theorem lemma_3_2 (hn : 0 < n) (U : Finset (Lattice n))
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun u : (U : Set (Lattice n)) => u.val))
    (hpos : PointedCone.hull ℝ (embed '' (U : Set (Lattice n))) = ⊤)
    (hzero : (0 : Lattice n) ∉ U) :
    (0 : Ambient n) ∈ interior (rayHull U) ∧
      (∃ W : Finset (Lattice n), realPolar (rayHull U) =
        convexHull ℝ (embed '' (W : Set (Lattice n)))) ∧
      (rayHull U).extremePoints ℝ = embed '' (U : Set (Lattice n)) ∧
      (∀ x : Lattice n, embed x ∈ rayHull U ↔ x = 0 ∨ x ∈ U) ∧
      ∃ Φ : Fan (FanBridge.standardEmbedding n), Φ.IsComplete ∧
        AllowedBlocks.HasRays (FanBridge.standardEmbedding n)
          (fun u : (U : Set (Lattice n)) => u.val) Φ ∧
        (∀ u : Lattice n, ConeBases.IsRay Φ u ↔ u ∈ U) ∧
        (∀ C, C ∈ Φ.cones ↔ ∃ E : Set (Ambient n), Convex ℝ E ∧
          IsExtreme ℝ (rayHull U) E ∧ E ≠ rayHull U ∧ C = PointedCone.hull ℝ E) ∧
        (∀ C, C ∈ Φ.cones ↔ ∃ z ∈ realPolar (rayHull U),
          C = normalCone (realPolar (rayHull U)) z) := by
  have ht := terminal_reflexive_hull hn U hU hpos hzero
  have hz : (0 : Ambient n) ∈ rayHull U := interior_subset ht.1
  obtain ⟨W,hW⟩ := polarCarrier_lattice_polytope U hU hpos
  have hspan : Submodule.span ℝ (embed '' (U : Set (Lattice n))) = ⊤ := by
    apply top_unique
    intro x _
    apply PointedCone.hull_le_span ℝ (embed '' (U : Set (Lattice n)))
    rw [hpos]
    trivial
  have hprimitive : ∀ u ∈ U, PrimitiveLatticeVector u := by
    intro u hu
    exact FlowOrientations.configuration_vector_primitive (U : Set (Lattice n)) hU hspan
      hu (fun he => hzero (he ▸ hu))
  refine ⟨ht.1,ht.2.1,ht.2.2.1,ht.2.2.2,seedFan U W hW,
    seedFan_complete U W hW hz,seedFan_hasRays U W hW hz hzero ht.2.2.1,
    seedFan_isRay_iff U W hW hz hzero ht.2.2.1 hprimitive,
    seedFan_cones_iff_proper_faces U W hW hz,?_⟩
  intro C
  simpa only [rayHull,realPolar_hull_eq_polarCarrier] using
    seedFan_cones_iff_normalCone U W hW hz C

#print axioms Unimodular.GenericReflexivity.lemma_3_2

end Unimodular.GenericReflexivity

end

end CanonicalSeedRecovered6

#print axioms Unimodular.GenericReflexivity.seedFan_cones_iff_normalCone
#print axioms Unimodular.GenericReflexivity.lemma_3_2
#check Unimodular.GenericReflexivity.lemma_3_2
