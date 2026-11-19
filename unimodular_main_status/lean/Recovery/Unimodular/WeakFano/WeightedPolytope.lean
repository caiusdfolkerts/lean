module

public import Unimodular.Extensions
public import Mathlib.Analysis.Convex.KreinMilman
public import Mathlib.Topology.Order.Compact
public import Mathlib.Tactic.FunProp

@[expose] public section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open scoped BigOperators Topology

namespace Unimodular.WeightedPolytopes

variable {n : ℕ}

/-- The literal finite intersection of weighted ray halfspaces. -/
def carrier (U : Finset (Lattice n)) (h : Lattice n → ℝ) : Set (Ambient n) :=
  {x | ∀ u ∈ U, pairing x u ≤ h u}

theorem carrier_convex (U : Finset (Lattice n)) (h : Lattice n → ℝ) :
    Convex ℝ (carrier U h) := by
  intro x hx y hy a b ha hb hab u hu
  rw [pairing_add_left, pairing_smul_left, pairing_smul_left]
  calc
    a * pairing x u + b * pairing y u ≤ a * h u + b * h u :=
      add_le_add (mul_le_mul_of_nonneg_left (hx u hu) ha)
        (mul_le_mul_of_nonneg_left (hy u hu) hb)
    _ = h u := by rw [← add_mul, hab, one_mul]

theorem pairing_continuous (u : Lattice n) :
    Continuous (fun x : Ambient n => pairing x u) := by
  unfold pairing
  fun_prop

theorem carrier_isClosed (U : Finset (Lattice n)) (h : Lattice n → ℝ) :
    IsClosed (carrier U h) := by
  simp only [carrier, Set.setOf_forall]
  exact isClosed_iInter fun u => isClosed_iInter fun _ =>
    isClosed_le (pairing_continuous u) continuous_const

theorem zero_mem_interior (U : Finset (Lattice n)) (h : Lattice n → ℝ)
    (hh : ∀ u ∈ U, 0 < h u) : (0 : Ambient n) ∈ interior (carrier U h) := by
  let O : Set (Ambient n) := {x | ∀ u ∈ U, pairing x u < h u}
  have hO : IsOpen O := by
    simp only [O, Set.setOf_forall]
    exact isOpen_biInter_finset fun u hu =>
      isOpen_lt (pairing_continuous u) continuous_const
  have hzero : (0 : Ambient n) ∈ O := by
    intro u hu
    simpa [pairing] using hh u hu
  apply mem_interior_iff_mem_nhds.mpr
  apply Filter.mem_of_superset (hO.mem_nhds hzero)
  exact fun x hx u hu => (hx u hu).le

theorem exists_pairing_bound (U : Finset (Lattice n)) (h : Lattice n → ℝ)
    (y : Ambient n) (hy : y ∈ PointedCone.hull ℝ (embed '' (U : Set (Lattice n)))) :
    ∃ C : ℝ, ∀ x ∈ carrier U h, realPairing x y ≤ C := by
  induction hy using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, hu, rfl⟩ := hy
    exact ⟨h u, fun x hx => hx u hu⟩
  | zero => exact ⟨0, fun x hx => by simp [realPairing]⟩
  | add y z hy hz ihy ihz =>
    obtain ⟨C, hC⟩ := ihy
    obtain ⟨D, hD⟩ := ihz
    refine ⟨C + D, fun x hx => ?_⟩
    simpa only [realPairing, Pi.add_apply, mul_add, Finset.sum_add_distrib] using
      add_le_add (hC x hx) (hD x hx)
  | smul c y hy ih =>
    obtain ⟨C, hC⟩ := ih
    refine ⟨(c : ℝ) * C, fun x hx => ?_⟩
    simpa only [← Nonneg.coe_smul, realPairing, Pi.smul_apply, smul_eq_mul,
      Finset.mul_sum, mul_left_comm] using
      mul_le_mul_of_nonneg_left (hC x hx) c.property

theorem carrier_isCompact (U : Finset (Lattice n)) (h : Lattice n → ℝ)
    (hpos : PointedCone.hull ℝ (embed '' (U : Set (Lattice n))) = ⊤) :
    IsCompact (carrier U h) := by
  classical
  have hmem (y : Ambient n) : y ∈ PointedCone.hull ℝ (embed '' (U : Set (Lattice n))) := by
    rw [hpos]
    trivial
  choose upper hupper using fun i : Fin n =>
    exists_pairing_bound U h (Pi.single i 1) (hmem _)
  choose lower hlower using fun i : Fin n =>
    exists_pairing_bound U h (-Pi.single i 1) (hmem _)
  apply (isCompact_Icc (a := fun i => -lower i) (b := upper)).of_isClosed_subset
    (carrier_isClosed U h)
  intro x hx
  constructor
  · intro i
    have hh := hlower i x hx
    have heq : realPairing x (-Pi.single i 1) = -x i := by
      simp [realPairing, Pi.single_apply]
    rw [heq] at hh
    linarith
  · intro i
    simpa [realPairing, Pi.single_apply] using hupper i x hx

def activeNormals (U : Finset (Lattice n)) (h : Lattice n → ℝ)
    (x : Ambient n) : Set (Lattice n) := {u | u ∈ U ∧ pairing x u = h u}

/-- The actual active normals at every extreme point span the whole space. -/
theorem activeNormals_span (U : Finset (Lattice n)) (h : Lattice n → ℝ)
    {x : Ambient n} (hx : x ∈ (carrier U h).extremePoints ℝ) :
    Submodule.span ℝ (embed '' activeNormals U h x) = ⊤ := by
  classical
  by_contra hspan
  obtain ⟨f, hf, hker⟩ :=
    (Submodule.span ℝ (embed '' activeNormals U h x)).exists_le_ker_of_lt_top
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
  have hactive (u : Lattice n) (hu : u ∈ U) (ha : pairing x u = h u) :
      pairing d u = 0 := by
    have hh : f (embed u) = 0 := hker (Submodule.subset_span ⟨u, ⟨hu, ha⟩, rfl⟩)
    rw [linearMap_eq_realPairing f] at hh
    change realPairing d (embed u) = 0
    change realPairing (embed u) d = 0 at hh
    rwa [realPairing_comm] at hh
  obtain ⟨t, ht, hstep⟩ := exists_pos_feasible_step U
    (fun u => h u - pairing x u) (fun u => |pairing d u|)
    (fun u hu => sub_nonneg.mpr (hx.1 u hu)) (by
      intro u hu he
      simp only [hactive u hu (by linarith), abs_zero, le_refl])
  have hp : x + t • d ∈ carrier U h := by
    intro u hu
    rw [pairing_add_left, pairing_smul_left]
    have hh := (mul_le_mul_of_nonneg_left (le_abs_self (pairing d u)) ht.le).trans
      (hstep u hu)
    linarith
  have hm : x + t • (-d) ∈ carrier U h := by
    intro u hu
    rw [pairing_add_left, pairing_smul_left]
    have hneg : pairing (-d) u = -pairing d u := by
      simp [pairing, Finset.sum_neg_distrib]
    rw [hneg]
    have hh := (mul_le_mul_of_nonneg_left (neg_le_abs (pairing d u)) ht.le).trans
      (hstep u hu)
    linarith
  have he : x + t • d = x := hx.2 hp hm
    ⟨(1 / 2 : ℝ), (1 / 2 : ℝ), by norm_num, by norm_num, by norm_num, by module⟩
  have hz : t • d = 0 := add_left_cancel (he.trans (add_zero x).symm)
  exact hd ((smul_eq_zero.1 hz).resolve_left ht.ne')

/-- Every ordered integral basis selected from the original rays. -/
def RayBasis (U : Finset (Lattice n)) :=
  {b : Module.Basis (Fin n) ℤ (Lattice n) // ∀ j, b j ∈ U}

instance rayBasis_finite (U : Finset (Lattice n)) : Finite (RayBasis U) := by
  let f : RayBasis U → (Fin n → {u : Lattice n // u ∈ U}) :=
    fun b j => ⟨b.val j, b.property j⟩
  apply Finite.of_injective f
  intro b c he
  apply Subtype.ext
  apply DFunLike.coe_injective
  funext j
  exact congrArg Subtype.val (congrFun he j)

/-- The integral dual corner for any integer height assignment. -/
def latticeCorner (b : Module.Basis (Fin n) ℤ (Lattice n))
    (h : Lattice n → ℤ) : Lattice n :=
  fun j => ∑ i, h (b i) * b.repr (Pi.single j 1) i

@[simp] theorem embed_latticeCorner (b : Module.Basis (Fin n) ℤ (Lattice n))
    (h : Lattice n → ℤ) :
    embed (latticeCorner b h) = dualCorner b (fun i => (h (b i) : ℝ)) := by
  ext j
  simp [embed, latticeCorner, dualCorner]

@[simp] theorem pairing_latticeCorner_basis (b : Module.Basis (Fin n) ℤ (Lattice n))
    (h : Lattice n → ℤ) (i : Fin n) :
    pairing (embed (latticeCorner b h)) (b i) = h (b i) := by
  rw [embed_latticeCorner, pairing_dualCorner_basis]

/-- An actual extreme point is the corner of an active integral ray basis. -/
theorem extreme_eq_latticeCorner (U : Finset (Lattice n)) (h : Lattice n → ℤ)
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun u : (U : Set (Lattice n)) => u.val))
    {x : Ambient n} (hx : x ∈ (carrier U (fun u => (h u : ℝ))).extremePoints ℝ) :
    ∃ b : RayBasis U, x = embed (latticeCorner b.val h) := by
  classical
  have hA : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun u : activeNormals U (fun u => (h u : ℝ)) x => u.val) := by
    intro a
    exact hU (fun j => ⟨(a j).val, (a j).property.1⟩)
  let a : Empty → activeNormals U (fun u => (h u : ℝ)) x := fun e => e.elim
  obtain ⟨b, hb, _⟩ := LatticeHull.exists_lattice_basis_extension _ hA
    (activeNormals_span U _ hx) a
    (linearIndependent_empty_type : LinearIndependent ℝ (fun j => embed (a j).val))
  refine ⟨⟨b, fun j => (hb j).1⟩, ?_⟩
  have hcoord : dualCoordinates b x = fun i => (h (b i) : ℝ) := by
    funext j
    exact (hb j).2
  rw [embed_latticeCorner]
  calc
    x = dualCorner b (dualCoordinates b x) := (dualCorner_dualCoordinates b x).symm
    _ = dualCorner b (fun i => (h (b i) : ℝ)) := by rw [hcoord]

/-- The finite list contains exactly those basis corners that satisfy all inequalities. -/
def vertices (U : Finset (Lattice n)) (h : Lattice n → ℤ) : Finset (Lattice n) := by
  classical
  letI : Fintype (RayBasis U) := Fintype.ofFinite _
  exact ((Finset.univ : Finset (RayBasis U)).image
    (fun b => latticeCorner b.val h)).filter
    (fun w => embed w ∈ carrier U (fun u => (h u : ℝ)))

@[simp] theorem mem_vertices (U : Finset (Lattice n)) (h : Lattice n → ℤ)
    (w : Lattice n) : w ∈ vertices U h ↔
    (∃ b : RayBasis U, latticeCorner b.val h = w) ∧
      embed w ∈ carrier U (fun u => (h u : ℝ)) := by
  classical
  simp [vertices]

/-- Weighted unimodular halfspaces form an actual lattice polytope, with no
simplicity, vertex integrality, or finite-vertex hypothesis. -/
theorem carrier_eq_convexHull_vertices (U : Finset (Lattice n)) (h : Lattice n → ℤ)
    (hU : IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun u : (U : Set (Lattice n)) => u.val))
    (hpos : PointedCone.hull ℝ (embed '' (U : Set (Lattice n))) = ⊤) :
    carrier U (fun u => (h u : ℝ)) =
      convexHull ℝ (embed '' (vertices U h : Set (Lattice n))) := by
  classical
  have hW : embed '' (vertices U h : Set (Lattice n)) ⊆ carrier U (fun u => (h u : ℝ)) := by
    rintro z ⟨w, hw, rfl⟩
    exact ((mem_vertices U h w).1 hw).2
  have hext : (carrier U (fun u => (h u : ℝ))).extremePoints ℝ ⊆
      embed '' (vertices U h : Set (Lattice n)) := by
    intro x hx
    obtain ⟨b, hb⟩ := extreme_eq_latticeCorner U h hU hx
    refine ⟨latticeCorner b.val h, (mem_vertices U h _).2 ⟨⟨b, rfl⟩, ?_⟩, hb.symm⟩
    rw [← hb]
    exact hx.1
  apply Set.Subset.antisymm
  · rw [← closure_convexHull_extremePoints (carrier_isCompact U _ hpos) (carrier_convex U _)]
    apply closure_minimal
    · exact convexHull_min (fun x hx => subset_convexHull ℝ _ (hext hx))
        (convex_convexHull ℝ _)
    · exact ((vertices U h).finite_toSet.image embed).isClosed_convexHull ℝ
  · exact convexHull_min hW (carrier_convex U _)

end Unimodular.WeightedPolytopes

#print axioms Unimodular.WeightedPolytopes.zero_mem_interior
#print axioms Unimodular.WeightedPolytopes.carrier_isCompact
#print axioms Unimodular.WeightedPolytopes.activeNormals_span
#print axioms Unimodular.WeightedPolytopes.extreme_eq_latticeCorner
#print axioms Unimodular.WeightedPolytopes.carrier_eq_convexHull_vertices
#check Unimodular.WeightedPolytopes.carrier_eq_convexHull_vertices
