module

public import Lean.Elab.BuiltinEvalCommand
public meta import Lean.Elab.BuiltinEvalCommand
public import Lean.Elab.Tactic.Omega
public import Lean.Util.CollectAxioms
public meta import Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public meta import Lean.Util.FoldConsts
public import Mathlib.Algebra.Order.Floor.Ring
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.LinearAlgebra.Basis.Prod
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.LinearAlgebra.Matrix.Dual
public import Mathlib.LinearAlgebra.Transvection.Basic
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Ring
public import Mathlib.Topology.MetricSpace.Basic
public import paper_verification.toric002

@[expose] public section


-- BEGIN ORIGINAL PaperVerification.ToricNormalConeIntersection
section Source_ToricNormalConeIntersection

-- original header: module
-- original header: public import PaperVerification.ToricNormalConeFaces
-- original header: public import Mathlib.Tactic.Push
-- original header: public import Mathlib.Tactic.Abel
-- original header: public import Mathlib.Tactic.NormNum
-- original header: @[expose] public section
/-!
# Common primitive supporting normals at smooth vertices

An integral supporting coordinate at one smooth vertex, if it vanishes at
another, is exactly one of the second vertex's primitive supporting coordinates.
The proof uses positive edge lengths and integral change-of-basis coefficients;
no face-lattice or normal-fan intersection property is assumed.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

/-- Evaluate a linear functional in genuine basis coordinates. -/
theorem linear_apply_basis_coordinates {E ι : Type*}
    [AddCommGroup E] [Module ℝ E] [Fintype ι]
    (f : E →ₗ[ℝ] ℝ) (b : Module.Basis ι ℝ E) (x : E) :
    f x = ∑ i, b.repr x i * f (b i) := by
  have h := congrArg f (b.sum_repr x)
  simpa only [map_sum, map_smul, smul_eq_mul] using h.symm

/-- A positive coefficient in a nonnegative dual expansion forces its
corresponding coordinate to vanish whenever the whole functional vanishes. -/
theorem coordinate_zero_of_positive_dual_coefficient {E ι : Type*}
    [AddCommGroup E] [Module ℝ E] [Fintype ι]
    (f : E →ₗ[ℝ] ℝ) (b : Module.Basis ι ℝ E) (x : E)
    (hx : ∀ i, 0 ≤ b.repr x i) (hf : ∀ i, 0 ≤ f (b i))
    (hzero : f x = 0) (j : ι) (hj : 0 < f (b j)) : b.repr x j = 0 := by
  have hsum : (∑ i, b.repr x i * f (b i)) = 0 := by
    rw [← linear_apply_basis_coordinates f b x, hzero]
  have hle := Finset.single_le_sum (f := fun i => b.repr x i * f (b i))
    (fun i _ => mul_nonneg (hx i) (hf i)) (Finset.mem_univ j)
  rw [hsum] at hle
  have he : b.repr x j * f (b j) = 0 :=
    le_antisymm hle (mul_nonneg (hx j) (hf j))
  exact (mul_eq_zero.mp he).resolve_right hj.ne'

/-- A primitive supporting coordinate shared by two smooth vertices is one
of the second vertex's primitive supporting coordinates. -/
theorem shared_supporting_coordinate {n : ℕ} (P : Set (Ambient n))
    (v w : Ambient n) (hv : v ∈ P) (hw : w ∈ P)
    (b c : Module.Basis (Fin n) ℤ (Lattice n))
    (lb lc : Fin n → ℝ) (hlb : ∀ i, 0 < lb i) (hlc : ∀ i, 0 < lc i)
    (hedgeb : ∀ i, v + lb i • integralBasisReal b i ∈ P)
    (hedgec : ∀ i, w + lc i • integralBasisReal c i ∈ P)
    (hconeb : ∀ x ∈ P, ∀ i, 0 ≤ (integralBasisReal b).repr (x - v) i)
    (hconec : ∀ x ∈ P, ∀ i, 0 ≤ (integralBasisReal c).repr (x - w) i)
    (i : Fin n) (hzero : (integralBasisReal b).repr (w - v) i = 0) :
    ∃ j : Fin n, (integralBasisReal c).coord j = (integralBasisReal b).coord i := by
  let bR := integralBasisReal b
  let cR := integralBasisReal c
  let f : Ambient n →ₗ[ℝ] ℝ := bR.coord i
  have hfzero : f (w - v) = 0 := hzero
  have hbeta (k : Fin n) : 0 ≤ f (cR k) := by
    have h := hconeb (w + lc k • cR k) (hedgec k) i
    have he : w + lc k • cR k - v = (w - v) + lc k • cR k := by abel
    change 0 ≤ f (w + lc k • cR k - v) at h
    rw [he, map_add, map_smul, hfzero, zero_add, smul_eq_mul] at h
    exact nonneg_of_mul_nonneg_right h (hlc k)
  have hbetapos : ∃ j : Fin n, 0 < f (cR j) := by
    by_contra hnot
    push_neg at hnot
    have hall (j : Fin n) : f (cR j) = 0 := le_antisymm (hnot j) (hbeta j)
    have hf : f = 0 := by
      apply cR.ext
      intro j
      simp only [LinearMap.zero_apply, hall]
    have hself : f (bR i) = 1 := by simp [f, Module.Basis.coord_apply]
    rw [hf, LinearMap.zero_apply] at hself
    norm_num at hself
  obtain ⟨j, hj⟩ := hbetapos
  let g : Ambient n →ₗ[ℝ] ℝ := cR.coord j
  have hforce (x : Ambient n) (hx : x ∈ P) (hfx : f (x - w) = 0) :
      g (x - w) = 0 :=
    coordinate_zero_of_positive_dual_coefficient f cR (x - w) (hconec x hx)
      hbeta hfx j hj
  have hfv : f (v - w) = 0 := by
    have he : v - w = -(w - v) := by abel
    rw [he, map_neg, hfzero, neg_zero]
  have hgv : g (v - w) = 0 := hforce v hv hfv
  have hother (k : Fin n) (hki : k ≠ i) : g (bR k) = 0 := by
    have hfk : f (bR k) = 0 := by
      simp [f, Module.Basis.coord_apply, hki, Ne.symm hki]
    have hpoint : f (v + lb k • bR k - w) = 0 := by
      have he : v + lb k • bR k - w = (v - w) + lb k • bR k := by abel
      rw [he, map_add, map_smul, hfv, hfk]
      simp
    have hg := hforce (v + lb k • bR k) (hedgeb k) hpoint
    have he : v + lb k • bR k - w = (v - w) + lb k • bR k := by abel
    rw [he, map_add, map_smul, hgv, zero_add, smul_eq_mul] at hg
    exact (mul_eq_zero.mp hg).resolve_left (hlb k).ne'
  have hlinear : g = g (bR i) • f := by
    apply bR.ext
    intro k
    by_cases hki : k = i
    · subst k
      simp [f, Module.Basis.coord_apply]
    · simp [hother k hki, f, Module.Basis.coord_apply, hki, Ne.symm hki]
  have hproduct : g (bR i) * f (cR j) = 1 := by
    have h := congrArg (fun l : Ambient n →ₗ[ℝ] ℝ => l (cR j)) hlinear
    have hself : g (cR j) = 1 := by simp [g, Module.Basis.coord_apply]
    simpa only [LinearMap.smul_apply, smul_eq_mul, hself] using h.symm
  have ha : g (bR i) = (c.repr (b i) j : ℝ) := by
    change (integralBasisReal c).repr (integralBasisReal b i) j = _
    rw [integralBasisReal_apply, integralBasisReal_repr]
  have hb : f (cR j) = (b.repr (c j) i : ℝ) := by
    change (integralBasisReal b).repr (integralBasisReal c j) i = _
    rw [integralBasisReal_apply, integralBasisReal_repr]
  have hab : c.repr (b i) j * b.repr (c j) i = 1 := by
    rw [ha, hb] at hproduct
    exact_mod_cast hproduct
  have hbetaZ : 0 < b.repr (c j) i := by
    rw [hb] at hj
    exact_mod_cast hj
  have haone : c.repr (b i) j = 1 := by
    rcases Int.eq_one_or_neg_one_of_mul_eq_one hab with h | h
    · exact h
    · rw [h] at hab
      omega
  have hgcoef : g (bR i) = 1 := by rw [ha, haone]; norm_num
  refine ⟨j, ?_⟩
  change g = f
  simpa only [hgcoef, one_smul] using hlinear

/-- Equality of primitive integer normal vectors is equivalent to equality of
the associated real supporting coordinate functionals. -/
theorem integralDualBasis_eq_iff_real_coord_eq {n : ℕ}
    (b c : Module.Basis (Fin n) ℤ (Lattice n)) (i j : Fin n) :
    integralDualBasis b i = integralDualBasis c j ↔
      (integralBasisReal b).coord i = (integralBasisReal c).coord j := by
  constructor
  · intro h
    apply LinearMap.ext
    intro x
    have he := congrArg (fun z : Lattice n => ∑ k, embed n z k * x k) h
    simpa only [integralDualBasis_real_pairing, Module.Basis.coord_apply] using he
  · intro h
    apply embed_injective n
    rw [embed_integralDualBasis, embed_integralDualBasis, h]

namespace LatticePolytope

variable {n : ℕ} (P : LatticePolytope n)

/-- Two actual smooth vertex normal cones intersect in the cone on their
literal common primitive integer rays. This proves the fan intersection
property from polytope geometry. -/
theorem normalCone_basis_common_rays
    (vZ wZ : Lattice n) (hv : embed n vZ ∈ P.carrier) (hw : embed n wZ ∈ P.carrier)
    (b c : Module.Basis (Fin n) ℤ (Lattice n)) (lb lc : Fin n → ℕ)
    (hedgeb : ∀ i, 0 < lb i ∧
      P.IsEdge (embed n vZ) (embed n (vZ + (lb i : ℤ) • b i)))
    (hedgec : ∀ i, 0 < lc i ∧
      P.IsEdge (embed n wZ) (embed n (wZ + (lc i : ℤ) • c i)))
    (hconeb : ∀ x ∈ P.carrier, ∀ i,
      0 ≤ (integralBasisReal b).repr (x - embed n vZ) i)
    (hconec : ∀ x ∈ P.carrier, ∀ i,
      0 ≤ (integralBasisReal c).repr (x - embed n wZ) i) :
    latticeRayCone (Finset.univ.image (integralDualBasis b)) ⊓
      latticeRayCone (Finset.univ.image (integralDualBasis c)) =
      latticeRayCone ((Finset.univ.image (integralDualBasis b)) ∩
        (Finset.univ.image (integralDualBasis c))) := by
  classical
  let I := Finset.univ.filter (fun i : Fin n =>
    (integralBasisReal b).repr (embed n wZ - embed n vZ) i = 0)
  have hpointb (i : Fin n) :
      embed n vZ + (lb i : ℝ) • integralBasisReal b i ∈ P.carrier := by
    have h := (P.edge_endpoints_extreme (hedgeb i).2).2.1
    simpa only [map_add, embed_int_smul, Int.cast_natCast,
      integralBasisReal_apply] using h
  have hpointc (i : Fin n) :
      embed n wZ + (lc i : ℝ) • integralBasisReal c i ∈ P.carrier := by
    have h := (P.edge_endpoints_extreme (hedgec i).2).2.1
    simpa only [map_add, embed_int_smul, Int.cast_natCast,
      integralBasisReal_apply] using h
  have hactive : I.image (integralDualBasis b) =
      (Finset.univ.image (integralDualBasis b)) ∩
        (Finset.univ.image (integralDualBasis c)) := by
    ext z
    constructor
    · intro hz
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      have hi0 := (Finset.mem_filter.mp hi).2
      obtain ⟨j, hj⟩ := shared_supporting_coordinate P.carrier
        (embed n vZ) (embed n wZ) hv hw b c
        (fun i => lb i) (fun i => lc i)
        (fun i => by exact_mod_cast (hedgeb i).1)
        (fun i => by exact_mod_cast (hedgec i).1)
        hpointb hpointc hconeb hconec i hi0
      refine Finset.mem_inter.mpr ⟨Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩,
        Finset.mem_image.mpr ⟨j, Finset.mem_univ j, ?_⟩⟩
      exact (integralDualBasis_eq_iff_real_coord_eq c b j i).mpr hj
    · intro hz
      obtain ⟨hzb, hzc⟩ := Finset.mem_inter.mp hz
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hzb
      obtain ⟨j, hj, hji⟩ := Finset.mem_image.mp hzc
      have hcoord := (integralDualBasis_eq_iff_real_coord_eq c b j i).mp hji
      have hb0 := hconeb (embed n wZ) hw i
      have hc0 := hconec (embed n vZ) hv j
      change 0 ≤ (integralBasisReal c).coord j (embed n vZ - embed n wZ) at hc0
      rw [hcoord] at hc0
      have he : embed n vZ - embed n wZ = -(embed n wZ - embed n vZ) := by abel
      rw [he, map_neg] at hc0
      change 0 ≤ -(integralBasisReal b).repr (embed n wZ - embed n vZ) i at hc0
      have hi0 : (integralBasisReal b).repr (embed n wZ - embed n vZ) i = 0 := by
        linarith
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi0⟩, rfl⟩
  have hvcone := P.normalCone_eq_latticeRayCone vZ b lb hedgeb hconeb
  have hwcone := P.normalCone_eq_latticeRayCone wZ c lc hedgec hconec
  have hinter := P.normalCone_inter_eq_dual_coordinate_face vZ (embed n wZ) hv hw
    b lb hedgeb hconeb
  apply SetLike.coe_injective
  change ((latticeRayCone (Finset.univ.image (integralDualBasis b)) : Set (Ambient n)) ∩
      (latticeRayCone (Finset.univ.image (integralDualBasis c)) : Set (Ambient n))) = _
  rw [← hvcone, ← hwcone, hinter]
  change (latticeRayCone (I.image (integralDualBasis b)) : Set (Ambient n)) = _
  rw [hactive]

end LatticePolytope

end PaperVerification.ToricGeometry
end
end Source_ToricNormalConeIntersection
-- END ORIGINAL PaperVerification.ToricNormalConeIntersection


-- BEGIN ORIGINAL PaperVerification.ToricFanConstruction
section Source_ToricFanConstruction

-- original header: module
-- original header: public import PaperVerification.ToricNormalConeIntersection
-- original header: public import PaperVerification.ToricNormalConeRealization
-- original header: public import PaperVerification.ToricNormalConeAverages
-- original header: public import PaperVerification.ToricBasisBoxFamily
-- original header: @[expose] public section
/-!
# The finite smooth complete fan of a smooth lattice polytope

The fan is built from all subsets of the genuine primitive normal basis at each
actual vertex. Its cone intersection and completeness fields are derived from
the actual normal cones of the polytope.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

/-- Indices of the basis vectors belonging to a specified ray set. -/
def basisRayIndices {n : ℕ} (b : Module.Basis (Fin n) ℤ (Lattice n))
    (s : Finset (Lattice n)) : Finset (Fin n) :=
  Finset.univ.filter (fun i => b i ∈ s)

theorem image_basisRayIndices {n : ℕ} (b : Module.Basis (Fin n) ℤ (Lattice n))
    (s : Finset (Lattice n)) (hs : s ⊆ Finset.univ.image b) :
    (basisRayIndices b s).image b = s := by
  ext v
  constructor
  · intro hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    exact (Finset.mem_filter.mp hi).2
  · intro hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hs hv)
    exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, hv⟩, rfl⟩

/-- Subcones generated by subsets of one integral basis intersect exactly in
their common rays. -/
theorem latticeRayCone_inter_of_subsets_basis {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (s t : Finset (Lattice n))
    (hs : s ⊆ Finset.univ.image b) (ht : t ⊆ Finset.univ.image b) :
    latticeRayCone s ⊓ latticeRayCone t = latticeRayCone (s ∩ t) := by
  let I := basisRayIndices b s
  let J := basisRayIndices b t
  have hI : I.image b = s := image_basisRayIndices b s hs
  have hJ : J.image b = t := image_basisRayIndices b t ht
  have hIJ : (I ∩ J).image b = s ∩ t := by
    ext v
    constructor
    · intro hv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨hiI, hiJ⟩ := Finset.mem_inter.mp hi
      exact Finset.mem_inter.mpr ⟨(Finset.mem_filter.mp hiI).2,
        (Finset.mem_filter.mp hiJ).2⟩
    · intro hv
      obtain ⟨hvs, hvt⟩ := Finset.mem_inter.mp hv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hs hvs)
      exact Finset.mem_image.mpr ⟨i, Finset.mem_inter.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ i, hvs⟩,
          Finset.mem_filter.mpr ⟨Finset.mem_univ i, hvt⟩⟩, rfl⟩
  calc
    latticeRayCone s ⊓ latticeRayCone t =
        latticeRayCone (I.image b) ⊓ latticeRayCone (J.image b) := by
      rw [hI, hJ]
    _ = latticeRayCone ((I ∩ J).image b) := by
      ext x
      simp only [Submodule.mem_inf, mem_latticeRayCone_basis_iff]
      constructor
      · rintro ⟨⟨hpos, hIz⟩, ⟨_, hJz⟩⟩
        refine ⟨hpos, ?_⟩
        intro i hi
        by_cases hiI : i ∈ I
        · exact hJz i (fun hiJ => hi (Finset.mem_inter.mpr ⟨hiI, hiJ⟩))
        · exact hIz i hiI
      · rintro ⟨hpos, hIJz⟩
        refine ⟨⟨hpos, ?_⟩, ⟨hpos, ?_⟩⟩
        · intro i hi
          exact hIJz i (fun h => hi (Finset.mem_inter.mp h).1)
        · intro i hi
          exact hIJz i (fun h => hi (Finset.mem_inter.mp h).2)
    _ = latticeRayCone (s ∩ t) := by rw [hIJ]

section BasisFamily

variable {n : ℕ} {J : Type*} [Fintype J]

/-- All subsets of a finite family's full integral bases. -/
def basisFamilyCones (b : J → Module.Basis (Fin n) ℤ (Lattice n)) :
    Finset (Finset (Lattice n)) :=
  Finset.univ.biUnion (fun j => (Finset.univ.image (b j)).powerset)

theorem mem_basisFamilyCones (b : J → Module.Basis (Fin n) ℤ (Lattice n))
    (s : Finset (Lattice n)) :
    s ∈ basisFamilyCones b ↔ ∃ j, s ⊆ Finset.univ.image (b j) := by
  simp [basisFamilyCones]

/-- A covering basis family whose full cones have the true common-ray
intersection property produces a genuine finite smooth complete fan. -/
def fanOfBasisFamily (b : J → Module.Basis (Fin n) ℤ (Lattice n))
    (hinter : ∀ j k,
      latticeRayCone (Finset.univ.image (b j)) ⊓ latticeRayCone (Finset.univ.image (b k)) =
        latticeRayCone ((Finset.univ.image (b j)) ∩ (Finset.univ.image (b k))))
    (hcover : ∀ x : Ambient n, ∃ j, x ∈ latticeRayCone (Finset.univ.image (b j))) :
    SmoothCompleteFan n where
  cones := basisFamilyCones b
  smooth := by
    intro s hs
    obtain ⟨j, hj⟩ := (mem_basisFamilyCones b s).mp hs
    exact ⟨b j, basisRayIndices (b j) s, (image_basisRayIndices (b j) s hj).symm⟩
  downward := by
    intro s hs t hts
    obtain ⟨j, hj⟩ := (mem_basisFamilyCones b s).mp hs
    exact (mem_basisFamilyCones b t).mpr ⟨j, hts.trans hj⟩
  intersection := by
    intro s hs t ht
    obtain ⟨j, hsj⟩ := (mem_basisFamilyCones b s).mp hs
    obtain ⟨k, htk⟩ := (mem_basisFamilyCones b t).mp ht
    let U := Finset.univ.image (b j)
    let V := Finset.univ.image (b k)
    have hsets : (s ∩ (U ∩ V)) ∩ t = s ∩ t := by
      ext v
      simp only [Finset.mem_inter]
      constructor
      · rintro ⟨⟨hvs, hvU, hvV⟩, hvt⟩
        exact ⟨hvs, hvt⟩
      · rintro ⟨hvs, hvt⟩
        exact ⟨⟨hvs, hsj hvs, htk hvt⟩, hvt⟩
    ext x
    constructor
    · rintro ⟨hxs, hxt⟩
      have hxUV : x ∈ latticeRayCone (U ∩ V) := by
        rw [← hinter j k]
        exact ⟨latticeRayCone_mono hsj hxs, latticeRayCone_mono htk hxt⟩
      have hxmid : x ∈ latticeRayCone (s ∩ (U ∩ V)) := by
        rw [← latticeRayCone_inter_of_subsets_basis (b j) s (U ∩ V) hsj
          Finset.inter_subset_left]
        exact ⟨hxs, hxUV⟩
      have hmidV : s ∩ (U ∩ V) ⊆ V :=
        Finset.inter_subset_right.trans Finset.inter_subset_right
      have hxfin : x ∈ latticeRayCone ((s ∩ (U ∩ V)) ∩ t) := by
        rw [← latticeRayCone_inter_of_subsets_basis (b k) (s ∩ (U ∩ V)) t hmidV htk]
        exact ⟨hxmid, hxt⟩
      simpa only [hsets] using hxfin
    · intro h
      exact ⟨latticeRayCone_mono Finset.inter_subset_left h,
        latticeRayCone_mono Finset.inter_subset_right h⟩
  complete := by
    intro x
    obtain ⟨j, hj⟩ := hcover x
    exact ⟨Finset.univ.image (b j), (mem_basisFamilyCones b _).mpr ⟨j, Finset.Subset.refl _⟩, hj⟩

theorem fanOfBasisFamily_isPure (b : J → Module.Basis (Fin n) ℤ (Lattice n))
    (hinter : ∀ j k,
      latticeRayCone (Finset.univ.image (b j)) ⊓ latticeRayCone (Finset.univ.image (b k)) =
        latticeRayCone ((Finset.univ.image (b j)) ∩ (Finset.univ.image (b k))))
    (hcover : ∀ x : Ambient n, ∃ j, x ∈ latticeRayCone (Finset.univ.image (b j))) :
    (fanOfBasisFamily b hinter hcover).IsPure := by
  intro s hs
  obtain ⟨j, hj⟩ := (mem_basisFamilyCones b s).mp hs
  refine ⟨Finset.univ.image (b j),
    (mem_basisFamilyCones b _).mpr ⟨j, Finset.Subset.refl _⟩, hj, ?_⟩
  rw [Finset.card_image_of_injective _ (b j).injective, Finset.card_fin]

end BasisFamily

namespace LatticePolytope

variable {n : ℕ} (P : LatticePolytope n)

/-- A smooth lattice polytope determines a finite smooth complete fan from its
actual vertex cones. The fan's intersection and completeness properties are
proved, not included as assumptions on the polytope. -/
theorem exists_smooth_complete_normal_fan_exact_pure (hP : P.Smooth) :
    ∃ «Σ» : SmoothCompleteFan n, «Σ».realCones = P.normalFan ∧ «Σ».IsPure := by
  classical
  let J := P.carrier.extremePoints ℝ
  letI : Fintype J := P.finite_vertices.fintype
  have hdata (v : J) := P.smooth_vertex_basis_cone hP v v.property
  choose vZ b lengths hvZ hedges hcone using hdata
  let d : J → Module.Basis (Fin n) ℤ (Lattice n) := fun v => integralDualBasis (b v)
  have hedges' (v : J) : ∀ i, 0 < lengths v i ∧
      P.IsEdge (embed n (vZ v)) (embed n (vZ v + (lengths v i : ℤ) • b v i)) := by
    simpa only [hvZ v] using hedges v
  have hcone' (v : J) : ∀ x ∈ P.carrier, ∀ i,
      0 ≤ (integralBasisReal (b v)).repr (x - embed n (vZ v)) i := by
    simpa only [hvZ v] using hcone v
  have hnormal (v : J) : P.normalCone v =
      (latticeRayCone (Finset.univ.image (d v)) : Set (Ambient n)) := by
    simpa only [hvZ v] using
      P.normalCone_eq_latticeRayCone (vZ v) (b v) (lengths v) (hedges' v) (hcone' v)
  have hinter (v w : J) :
      latticeRayCone (Finset.univ.image (d v)) ⊓ latticeRayCone (Finset.univ.image (d w)) =
        latticeRayCone ((Finset.univ.image (d v)) ∩ (Finset.univ.image (d w))) := by
    apply P.normalCone_basis_common_rays (vZ v) (vZ w)
      (by simpa only [hvZ v] using v.property.1)
      (by simpa only [hvZ w] using w.property.1)
      (b v) (b w) (lengths v) (lengths w) (hedges' v) (hedges' w) (hcone' v) (hcone' w)
  have hcover (u : Ambient n) : ∃ v : J, u ∈ latticeRayCone (Finset.univ.image (d v)) := by
    let f : Ambient n →ₗ[ℝ] ℝ := dotProductEquiv ℝ (Fin n) u
    obtain ⟨v, hv, hmin⟩ := P.exists_minimizing_vertex f
    refine ⟨⟨v, hv⟩, ?_⟩
    change u ∈ (latticeRayCone (Finset.univ.image (d ⟨v, hv⟩)) : Set (Ambient n))
    rw [← hnormal ⟨v, hv⟩]
    intro x hx
    change 0 ≤ f (x - v)
    rw [map_sub]
    exact sub_nonneg.mpr (hmin x hx)
  let «Σ» := fanOfBasisFamily d hinter hcover
  refine ⟨«Σ», ?_, fanOfBasisFamily_isPure d hinter hcover⟩
  ext C
  constructor
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨j, hj⟩ := (mem_basisFamilyCones d s).mp hs
    let I := basisRayIndices (d j) s
    have hI : I.image (d j) = s := image_basisRayIndices (d j) s hj
    have h := P.subbasis_mem_normalFan (vZ j)
      (by simpa only [hvZ j] using j.property.1)
      (b j) (lengths j) (hedges' j) (hcone' j) I
    change (latticeRayCone (I.image (d j)) : Set (Ambient n)) ∈ P.normalFan at h
    simpa only [hI] using h
  · rintro ⟨x, hx, rfl⟩
    have hrange : Set.range (fun j : J => (j : Ambient n)) = P.carrier.extremePoints ℝ := by
      ext y
      constructor
      · rintro ⟨j, rfl⟩
        exact j.property
      · intro hy
        exact ⟨⟨y, hy⟩, rfl⟩
    have hxhull : x ∈ convexHull ℝ (Set.range (fun j : J => (j : Ambient n))) := by
      rw [hrange, P.hull_vertices]
      exact hx
    obtain ⟨p, hp, hpsum, hpm⟩ :=
      PaperVerification.Toric.exists_probability_of_mem_convexHull_range
        (fun j : J => (j : Ambient n)) hxhull
    let K := Finset.univ.filter (fun j : J => 0 < p j)
    have hK : K.Nonempty := by
      have hpos : 0 < ∑ j, p j := by rw [hpsum]; norm_num
      obtain ⟨j, hj, hpj⟩ :=
        (Finset.sum_pos_iff_of_nonneg (fun j _ => hp j)).mp hpos
      exact ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hpj⟩⟩
    have hcones (j : J) (hj : j ∈ K) : Finset.univ.image (d j) ∈ «Σ».cones :=
      (mem_basisFamilyCones d _).mpr ⟨j, Finset.Subset.refl _⟩
    obtain ⟨s, hs, hspec⟩ := «Σ».exists_cone_finite_intersection K
      (fun j => Finset.univ.image (d j)) hK hcones
    refine ⟨s, hs, ?_⟩
    ext u
    rw [← hpm, P.mem_normalCone_convex_average (fun j : J => (j : Ambient n)) p
      (fun j => j.property.1) hp hpsum u]
    change (∀ j : J, 0 < p j → u ∈ P.normalCone (j : Ambient n)) ↔
      u ∈ latticeRayCone s
    rw [hspec u]
    simp only [hnormal, K, Finset.mem_filter, Finset.mem_univ, true_and]
    rfl

/-- The exact normal-fan identification, with purity available separately
from the stronger construction theorem above. -/
theorem exists_smooth_complete_normal_fan_exact (hP : P.Smooth) :
    ∃ «Σ» : SmoothCompleteFan n, «Σ».realCones = P.normalFan := by
  obtain ⟨«Σ», «hΣ», hpure⟩ := P.exists_smooth_complete_normal_fan_exact_pure hP
  exact ⟨«Σ», «hΣ»⟩

/-- In particular every actual vertex normal cone is one of the cones of the
constructed finite smooth complete fan. -/
theorem exists_smooth_complete_normal_fan (hP : P.Smooth) :
    ∃ «Σ» : SmoothCompleteFan n,
      ∀ v ∈ P.carrier.extremePoints ℝ,
        ∃ s ∈ «Σ».cones, P.normalCone v = (latticeRayCone s : Set (Ambient n)) := by
  obtain ⟨«Σ», «hΣ»⟩ := P.exists_smooth_complete_normal_fan_exact hP
  refine ⟨«Σ», ?_⟩
  intro v hv
  have h : P.normalCone v ∈ P.normalFan := ⟨v, hv.1, rfl⟩
  rw [← «hΣ»] at h
  exact h

end LatticePolytope

end PaperVerification.ToricGeometry
end
end Source_ToricFanConstruction
-- END ORIGINAL PaperVerification.ToricFanConstruction


-- BEGIN ORIGINAL PaperVerification.ToricPrimitiveOverlap
section Source_ToricPrimitiveOverlap

-- original header: module

-- original header: public import PaperVerification.ToricPrimitiveRelations

-- original header: @[expose] public section

/-!
# Primitive collections meeting a contraction focus

The replacement condition forbids a different primitive collection from
containing the entire focus and also a positive ray of the contraction.
This is a finite-cone argument, independent of scheme contractions.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan.PrimitiveRelation

variable {n : ℕ} {«Σ» : SmoothCompleteFan n} (R : «Σ».PrimitiveRelation)

/-- Every cone over the focus can be filled with all positive rays except
one ray which it already omits. -/
theorem fill_cone_with_positive_except (hR : R.IsCombinatoriallyContractible)
    {C : Finset (Lattice n)} (hC : C ∈ «Σ».cones) (hNC : R.negative ⊆ C)
    {u : Lattice n} (hu : u ∈ R.positive) (huC : u ∉ C) :
    R.positive.erase u ∪ C ∈ «Σ».cones := by
  let ν := C \ (R.positive ∪ R.negative)
  have hν : ν ∈ «Σ».cones := «Σ».downward C hC ν Finset.sdiff_subset
  have hdisj : Disjoint ν (R.positive ∪ R.negative) := by
    apply Finset.disjoint_left.mpr
    intro v hv hPN
    exact (Finset.mem_sdiff.mp hv).2 hPN
  have hNν : R.negative ∪ ν ∈ «Σ».cones :=
    «Σ».downward C hC _ (Finset.union_subset hNC Finset.sdiff_subset)
  have hreplace := hR ν hν hdisj hNν u hu
  apply «Σ».downward _ hreplace _
  intro v hv
  rcases Finset.mem_union.mp hv with hv | hv
  · exact Finset.mem_union_left _ (Finset.mem_union_left _ hv)
  · by_cases hvP : v ∈ R.positive
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_erase.mpr ⟨fun he => huC (he ▸ hv), hvP⟩))
    · by_cases hvN : v ∈ R.negative
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hvN)
      · exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
          ⟨hv, by simpa only [Finset.mem_union, not_or] using And.intro hvP hvN⟩)

theorem positive_disjoint_of_focus_subset_primitive
    (hR : R.IsCombinatoriallyContractible)
    {Q : Finset (Lattice n)} (hQ : «Σ».IsPrimitiveCollection Q)
    (hNQ : R.negative ⊆ Q) (hneq : R.positive ≠ Q) :
    Disjoint R.positive Q := by
  have hnot : ¬ R.positive ⊆ Q := by
    intro hsubset
    exact R.primitive.2.1 (hQ.2.2 R.positive
      (Finset.ssubset_iff_subset_ne.mpr ⟨hsubset, hneq⟩))
  obtain ⟨u, hu, huQ⟩ := Finset.not_subset.mp hnot
  apply Finset.disjoint_left.mpr
  intro x hxP hxQ
  let C := Q.erase x
  have hC : C ∈ «Σ».cones := hQ.2.2 C (Finset.erase_ssubset hxQ)
  have hNC : R.negative ⊆ C := by
    intro v hv
    have hvx : v ≠ x := by
      intro he
      exact Finset.disjoint_left.mp R.disjoint hxP (he ▸ hv)
    exact Finset.mem_erase.mpr ⟨hvx, hNQ hv⟩
  let ν := C \ (R.positive ∪ R.negative)
  have hνC : ν ⊆ C := Finset.sdiff_subset
  have hν : ν ∈ «Σ».cones := «Σ».downward C hC ν hνC
  have hdisj : Disjoint ν (R.positive ∪ R.negative) := by
    apply Finset.disjoint_left.mpr
    intro v hv hPN
    exact (Finset.mem_sdiff.mp hv).2 hPN
  have hNν : R.negative ∪ ν ∈ «Σ».cones :=
    «Σ».downward C hC _ (Finset.union_subset hNC hνC)
  have hreplace := hR ν hν hdisj hNν u hu
  apply hQ.2.1
  apply «Σ».downward _ hreplace Q
  intro v hv
  by_cases hvP : v ∈ R.positive
  · have hvu : v ≠ u := fun he => huQ (he ▸ hv)
    exact Finset.mem_union_left _
      (Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨hvu, hvP⟩))
  · by_cases hvN : v ∈ R.negative
    · exact Finset.mem_union_left _ (Finset.mem_union_right _ hvN)
    · have hvx : v ≠ x := fun he => hvP (he.symm ▸ hxP)
      exact Finset.mem_union_right _ (Finset.mem_sdiff.mpr
        ⟨Finset.mem_erase.mpr ⟨hvx, hv⟩, by
          simpa only [Finset.mem_union, not_or] using And.intro hvP hvN⟩)

end SmoothCompleteFan.PrimitiveRelation

end PaperVerification.ToricGeometry
end
end Source_ToricPrimitiveOverlap
-- END ORIGINAL PaperVerification.ToricPrimitiveOverlap


-- BEGIN ORIGINAL PaperVerification.ToricBundleFanCoordinates
section Source_ToricBundleFanCoordinates

-- original header: module

-- original header: public import PaperVerification.ToricFanConstruction
-- original header: public import PaperVerification.ToricContractionCones
-- original header: public import PaperVerification.ToricPrimitiveOverlap
-- original header: public import Mathlib.LinearAlgebra.Basis.Prod
-- original header: public import Mathlib.Data.Fintype.EquivFin


-- original header: @[expose] public section
/-!
# Saturated quotient coordinates for a smooth cone

Deleting coordinates of an integral basis gives the actual free quotient by
the lattice generated by a smooth cone.  All maps here are explicit linear
maps, with an integral section.  Changing the basis containing that cone
gives an integral equivalence of the resulting quotients.  This supplies the
lattice, rather than only real-vector-space, part of the bundle construction.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

section Coordinates

variable {ι E R : Type*} [Fintype ι] [DecidableEq ι]
  [CommRing R] [AddCommGroup E] [Module R E]

/-- The coordinates complementary to a specified basis subset. -/
abbrev ComplementaryIndex (I : Finset ι) := {i : ι // i ∉ I}

/-- Restriction of basis coordinates to the complementary indices. -/
def basisProjection (b : Module.Basis ι R E) (I : Finset ι) :
    E →ₗ[R] (ComplementaryIndex I → R) where
  toFun x j := b.repr x j
  map_add' x y := by ext j; simp
  map_smul' a x := by ext j; simp

def complementaryExtension (I : Finset ι) :
    (ComplementaryIndex I → R) →ₗ[R] (ι → R) where
  toFun x i := if hi : i ∈ I then 0 else x ⟨i, hi⟩
  map_add' x y := by
    ext i
    by_cases hi : i ∈ I <;> simp [hi]
  map_smul' a x := by
    ext i
    by_cases hi : i ∈ I <;> simp [hi]

/-- The section sets all deleted coordinates to zero. -/
def basisSection (b : Module.Basis ι R E) (I : Finset ι) :
    (ComplementaryIndex I → R) →ₗ[R] E :=
  b.equivFun.symm.toLinearMap.comp (complementaryExtension I)

@[simp] theorem basisProjection_apply (b : Module.Basis ι R E)
    (I : Finset ι) (x : E) (j : ComplementaryIndex I) :
    basisProjection b I x j = b.repr x j := rfl

@[simp] theorem basisSection_repr (b : Module.Basis ι R E)
    (I : Finset ι) (x : ComplementaryIndex I → R) (i : ι) :
    b.repr (basisSection b I x) i = if hi : i ∈ I then 0 else x ⟨i, hi⟩ := by
  change b.equivFun (b.equivFun.symm (complementaryExtension I x)) i = _
  rw [b.equivFun.apply_symm_apply]
  rfl

@[simp] theorem basisProjection_section (b : Module.Basis ι R E)
    (I : Finset ι) (x : ComplementaryIndex I → R) :
    basisProjection b I (basisSection b I x) = x := by
  ext j
  simp only [basisProjection_apply, basisSection_repr, dif_neg j.property]

theorem basisProjection_surjective (b : Module.Basis ι R E) (I : Finset ι) :
    Function.Surjective (basisProjection b I) :=
  fun x => ⟨basisSection b I x, basisProjection_section b I x⟩

theorem basisProjection_basis_mem (b : Module.Basis ι R E) (I : Finset ι)
    {i : ι} (hi : i ∈ I) : basisProjection b I (b i) = 0 := by
  ext j
  have hij : i ≠ j := fun he => j.property (he ▸ hi)
  simp [Module.Basis.repr_self_apply, hij]

theorem basisProjection_basis_not_mem (b : Module.Basis ι R E)
    (I : Finset ι) (j : ComplementaryIndex I) :
    basisProjection b I (b j) = Pi.single j 1 := by
  ext k
  simp [Module.Basis.repr_self_apply, Finsupp.single_apply,
    Pi.single_apply, Subtype.ext_iff, eq_comm]

@[simp] theorem basisSection_single (b : Module.Basis ι R E)
    (I : Finset ι) (j : ComplementaryIndex I) :
    basisSection b I (Pi.single j 1) = b j := by
  apply b.equivFun.injective
  funext i
  rw [Module.Basis.equivFun_apply, basisSection_repr,
    Module.Basis.equivFun_apply, Module.Basis.repr_self_apply]
  by_cases hi : i ∈ I
  · have hji : (j : ι) ≠ i := fun he => j.property (he.symm ▸ hi)
    simp [hi, hji]
  · simp [hi, Pi.single_apply, Subtype.ext_iff, eq_comm]

/-- The omitted part is exactly a linear combination of the deleted basis
vectors; there is no finite-index discrepancy. -/
theorem basisSection_projection_decomposition (b : Module.Basis ι R E)
    (I : Finset ι) (x : E) :
    basisSection b I (basisProjection b I x) +
      ∑ i ∈ I, b.repr x i • b i = x := by
  apply b.equivFun.injective
  funext i
  simp only [map_add, Module.Basis.equivFun_apply, basisSection_repr,
    Finsupp.add_apply, map_sum, map_smul, Finsupp.finsetSum_apply,
    Finsupp.smul_apply, Module.Basis.repr_self_apply, smul_eq_mul]
  by_cases hi : i ∈ I <;> simp [Finsupp.single_apply, hi]

theorem basisProjection_eq_zero_iff (b : Module.Basis ι R E)
    (I : Finset ι) (x : E) :
    basisProjection b I x = 0 ↔ ∀ i ∉ I, b.repr x i = 0 := by
  constructor
  · intro h i hi
    exact congrFun h ⟨i, hi⟩
  · intro h
    ext j
    exact h j j.property

theorem map_basisSection_projection {F : Type*} [AddCommGroup F] [Module R F]
    (b : Module.Basis ι R E) (I : Finset ι) (q : E →ₗ[R] F)
    (hq : ∀ i ∈ I, q (b i) = 0) (x : E) :
    q (basisSection b I (basisProjection b I x)) = q x := by
  have h := congrArg q (basisSection_projection_decomposition b I x)
  simp only [map_add, map_sum, map_smul] at h
  have hz : (∑ i ∈ I, b.repr x i • q (b i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [hq i hi, smul_zero]
  simpa only [hz, add_zero] using h

theorem basisProjection_of_mem_image (b : Module.Basis ι R E)
    (I : Finset ι) {v : E} (hv : v ∈ I.image b) :
    basisProjection b I v = 0 := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
  exact basisProjection_basis_mem b I hi

/-- Changing the full basis containing the same deleted ray set changes
quotient coordinates by a unimodular transformation. -/
def basisQuotientTransition (b c : Module.Basis ι R E) (I J : Finset ι)
    (hIJ : I.image b = J.image c) :
    (ComplementaryIndex I → R) ≃ₗ[R] (ComplementaryIndex J → R) where
  toFun x := basisProjection c J (basisSection b I x)
  invFun y := basisProjection b I (basisSection c J y)
  left_inv x := by
    change basisProjection b I
      (basisSection c J (basisProjection c J (basisSection b I x))) = x
    rw [map_basisSection_projection c J (basisProjection b I) ?_]
    · exact basisProjection_section b I x
    · intro j hj
      apply basisProjection_of_mem_image b I
      rw [hIJ]
      exact Finset.mem_image.mpr ⟨j, hj, rfl⟩
  right_inv y := by
    change basisProjection c J
      (basisSection b I (basisProjection b I (basisSection c J y))) = y
    rw [map_basisSection_projection b I (basisProjection c J) ?_]
    · exact basisProjection_section c J y
    · intro i hi
      apply basisProjection_of_mem_image c J
      rw [← hIJ]
      exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  map_add' x y := by simp only [map_add]
  map_smul' a x := by simp only [map_smul, RingHom.id_apply]

theorem basisQuotientTransition_projection (b c : Module.Basis ι R E)
    (I J : Finset ι) (hIJ : I.image b = J.image c) (x : E) :
    basisQuotientTransition b c I J hIJ (basisProjection b I x) =
      basisProjection c J x := by
  apply map_basisSection_projection b I (basisProjection c J)
  intro i hi
  apply basisProjection_of_mem_image c J
  rw [← hIJ]
  exact Finset.mem_image.mpr ⟨i, hi, rfl⟩

/-- The projections of complementary vectors of any integral basis
containing the same cone form a basis of the free quotient lattice. -/
def descendedQuotientBasis (b c : Module.Basis ι R E) (I J : Finset ι)
    (hIJ : I.image b = J.image c) :
    Module.Basis (ComplementaryIndex J) R (ComplementaryIndex I → R) :=
  (Pi.basisFun R (ComplementaryIndex J)).map
    (basisQuotientTransition b c I J hIJ).symm

@[simp] theorem descendedQuotientBasis_apply (b c : Module.Basis ι R E)
    (I J : Finset ι) (hIJ : I.image b = J.image c) (j : ComplementaryIndex J) :
    descendedQuotientBasis b c I J hIJ j = basisProjection b I (c j) := by
  simp only [descendedQuotientBasis, Module.Basis.map_apply, Pi.basisFun_apply,
    basisQuotientTransition]
  change basisProjection b I (basisSection c J (Pi.single j 1)) = _
  rw [basisSection_single]

end Coordinates

section IntegralCoordinates

variable {n : ℕ}

/-- The quotient index has exactly the codimension of the deleted cone. -/
theorem complementaryIndex_card (I : Finset (Fin n)) :
    Fintype.card (ComplementaryIndex I) = n - I.card := by
  rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]

def quotientIndexEquivFin (I : Finset (Fin n)) :
    ComplementaryIndex I ≃ Fin (n - I.card) :=
  Fintype.equivFinOfCardEq (complementaryIndex_card I)

def quotientCoordinateFinEquiv (R : Type*) [CommRing R]
    (I : Finset (Fin n)) :
    (ComplementaryIndex I → R) ≃ₗ[R] (Fin (n - I.card) → R) where
  toFun x j := x ((quotientIndexEquivFin I).symm j)
  invFun y i := y (quotientIndexEquivFin I i)
  left_inv x := by ext i; simp
  right_inv y := by ext i; simp
  map_add' x y := rfl
  map_smul' a x := rfl

/-- Explicit integral quotient map onto the standard coordinate lattice. -/
def coneQuotientLattice (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) : Lattice n →ₗ[ℤ] Lattice (n - I.card) :=
  (quotientCoordinateFinEquiv ℤ I).toLinearMap.comp (basisProjection b I)

/-- Its real extension uses the same integral basis coordinates. -/
def coneQuotientReal (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) : Ambient n →ₗ[ℝ] Ambient (n - I.card) :=
  (quotientCoordinateFinEquiv ℝ I).toLinearMap.comp
    (basisProjection (integralBasisReal b) I)

def coneQuotientSectionLattice (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) : Lattice (n - I.card) →ₗ[ℤ] Lattice n :=
  (basisSection b I).comp (quotientCoordinateFinEquiv ℤ I).symm.toLinearMap

def coneQuotientSectionReal (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) : Ambient (n - I.card) →ₗ[ℝ] Ambient n :=
  (basisSection (integralBasisReal b) I).comp
    (quotientCoordinateFinEquiv ℝ I).symm.toLinearMap

@[simp] theorem coneQuotient_section_lattice (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) (z : Lattice (n - I.card)) :
    coneQuotientLattice b I (coneQuotientSectionLattice b I z) = z := by
  simp [coneQuotientLattice, coneQuotientSectionLattice, basisProjection_section]

@[simp] theorem coneQuotient_section_real (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) (x : Ambient (n - I.card)) :
    coneQuotientReal b I (coneQuotientSectionReal b I x) = x := by
  simp [coneQuotientReal, coneQuotientSectionReal, basisProjection_section]

theorem coneQuotient_decomposition (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) (x : Ambient n) :
    coneQuotientSectionReal b I (coneQuotientReal b I x) +
      ∑ i ∈ I, (integralBasisReal b).repr x i • integralBasisReal b i = x := by
  change basisSection (integralBasisReal b) I
      ((quotientCoordinateFinEquiv ℝ I).symm
        ((quotientCoordinateFinEquiv ℝ I)
          (basisProjection (integralBasisReal b) I x))) +
      ∑ i ∈ I, (integralBasisReal b).repr x i • integralBasisReal b i = x
  rw [LinearEquiv.symm_apply_apply]
  exact basisSection_projection_decomposition (integralBasisReal b) I x

@[simp] theorem coneQuotient_compatible (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) (z : Lattice n) :
    coneQuotientReal b I (embed n z) =
      embed (n - I.card) (coneQuotientLattice b I z) := by
  funext j
  exact integralBasisReal_repr b z ((quotientIndexEquivFin I).symm j)

@[simp] theorem coneQuotientSection_compatible
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (z : Lattice (n - I.card)) :
    coneQuotientSectionReal b I (embed (n - I.card) z) =
      embed n (coneQuotientSectionLattice b I z) := by
  apply (integralBasisReal b).repr.injective
  ext i
  rw [integralBasisReal_repr]
  simp only [coneQuotientSectionReal, coneQuotientSectionLattice,
    LinearMap.comp_apply, basisSection_repr]
  by_cases hi : i ∈ I <;>
    simp [hi, quotientCoordinateFinEquiv, embed]

theorem coneQuotientLattice_of_mem (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) {v : Lattice n} (hv : v ∈ I.image b) :
    coneQuotientLattice b I v = 0 := by
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
  change quotientCoordinateFinEquiv ℤ I (basisProjection b I (b i)) = 0
  rw [basisProjection_basis_mem b I hi, map_zero]

theorem coneQuotientReal_of_mem (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) {v : Lattice n} (hv : v ∈ I.image b) :
    coneQuotientReal b I (embed n v) = 0 := by
  rw [coneQuotient_compatible, coneQuotientLattice_of_mem b I hv, map_zero]

/-- The deleted lattice is saturated: a real zero quotient of an integer
vector is already zero in the integral quotient. -/
theorem coneQuotient_zero_iff (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) (z : Lattice n) :
    coneQuotientReal b I (embed n z) = 0 ↔ coneQuotientLattice b I z = 0 := by
  rw [coneQuotient_compatible]
  constructor
  · intro h
    apply embed_injective (n - I.card)
    simpa only [map_zero] using h
  · intro h
    rw [h, map_zero]

end IntegralCoordinates

end PaperVerification.ToricGeometry
end
end Source_ToricBundleFanCoordinates
-- END ORIGINAL PaperVerification.ToricBundleFanCoordinates


-- BEGIN ORIGINAL PaperVerification.ToricBundleFanQuotient
section Source_ToricBundleFanQuotient

-- original header: module

-- original header: public import PaperVerification.ToricBundleFanCoordinates


-- original header: @[expose] public section
/-!
# Actual cones in a saturated quotient

The fan intersection property descends through a smooth cone.  The proof
lifts two equal quotient vectors and adds nonnegative combinations of the
common cone rays to make the lifts equal.  Smoothness descends through the
explicit integral quotient basis from `ToricBundleFanCoordinates`.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

theorem finiteRayCone_image_linear {E F : Type*}
    [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (s : Finset E) (f : E →ₗ[ℝ] F) :
    finiteRayCone (s.image f) = (finiteRayCone s).map f := by
  rw [finiteRayCone_eq_hull, finiteRayCone_eq_hull]
  change Submodule.span (Nonneg ℝ) ((s.image f : Finset F) : Set F) =
    Submodule.map (f : E →ₗ[Nonneg ℝ] F) (Submodule.span (Nonneg ℝ) (s : Set E))
  rw [Finset.coe_image]
  exact Submodule.span_image (f : E →ₗ[Nonneg ℝ] F)

variable {n : ℕ}

theorem latticeRayCone_image_quotient
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (s : Finset (Lattice n)) :
    latticeRayCone (s.image (coneQuotientLattice b I)) =
      (latticeRayCone s).map (coneQuotientReal b I) := by
  unfold latticeRayCone
  rw [← finiteRayCone_image_linear]
  congr 1
  simp only [Finset.image_image]
  ext x
  simp only [Finset.mem_image, Function.comp_apply]
  constructor
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, coneQuotient_compatible b I v⟩
  · rintro ⟨v, hv, rfl⟩
    exact ⟨v, hv, (coneQuotient_compatible b I v).symm⟩

theorem coneQuotient_zero_on_cone
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    {x : Ambient n} (hx : x ∈ latticeRayCone (I.image b)) :
    coneQuotientReal b I x = 0 := by
  have hcoord := (mem_latticeRayCone_basis_iff b I x).mp hx
  change quotientCoordinateFinEquiv ℝ I
    (basisProjection (integralBasisReal b) I x) = 0
  rw [(basisProjection_eq_zero_iff (integralBasisReal b) I x).mpr hcoord.2, map_zero]

/-- Two lifts of one quotient vector become identical after adding vectors
in the same actual cone on the deleted basis rays. -/
theorem coneQuotient_common_lift
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    {x y : Ambient n} (hxy : coneQuotientReal b I x = coneQuotientReal b I y) :
    ∃ a ∈ latticeRayCone (I.image b), ∃ c ∈ latticeRayCone (I.image b),
      x + a = y + c := by
  let β := integralBasisReal b
  let d : Fin n → ℝ := fun i => β.repr (y - x) i
  have hproj : basisProjection β I (y - x) = 0 := by
    apply (quotientCoordinateFinEquiv ℝ I).injective
    change coneQuotientReal b I (y - x) = quotientCoordinateFinEquiv ℝ I 0
    rw [map_sub, hxy, sub_self, map_zero]
  have hsum : (∑ i ∈ I, d i • β i) = y - x := by
    have h := basisSection_projection_decomposition β I (y - x)
    rw [hproj, map_zero, zero_add] at h
    exact h
  let a := ∑ i ∈ I, max (d i) 0 • β i
  let c := ∑ i ∈ I, (max (d i) 0 - d i) • β i
  have ha : a ∈ latticeRayCone (I.image b) := by
    rw [latticeRayCone_basis]
    exact Submodule.sum_mem _ (fun i hi => PointedCone.smul_mem _
      (le_max_right _ _) (finiteRayCone_generator _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)))
  have hc : c ∈ latticeRayCone (I.image b) := by
    rw [latticeRayCone_basis]
    exact Submodule.sum_mem _ (fun i hi => PointedCone.smul_mem _
      (sub_nonneg.mpr (le_max_left _ _))
      (finiteRayCone_generator _ (Finset.mem_image.mpr ⟨i, hi, rfl⟩)))
  have hac : a - c = y - x := by
    change (∑ i ∈ I, max (d i) 0 • β i) -
      (∑ i ∈ I, (max (d i) 0 - d i) • β i) = _
    rw [← Finset.sum_sub_distrib]
    simp only [← sub_smul, sub_sub_cancel]
    exact hsum
  refine ⟨a, ha, c, hc, ?_⟩
  calc
    x + a = x + (a - c) + c := by abel
    _ = x + (y - x) + c := by rw [hac]
    _ = y + c := by abel

namespace SmoothCompleteFan

variable («Σ» : SmoothCompleteFan n)

/-- Projecting genuine cones containing a common smooth cone preserves
their genuine geometric intersections. -/
theorem coneQuotient_intersection
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    {s t : Finset (Lattice n)} (hs : s ∈ «Σ».cones) (ht : t ∈ «Σ».cones)
    (hIs : I.image b ⊆ s) (hIt : I.image b ⊆ t) :
    (latticeRayCone s).map (coneQuotientReal b I) ⊓
      (latticeRayCone t).map (coneQuotientReal b I) =
        (latticeRayCone (s ∩ t)).map (coneQuotientReal b I) := by
  apply le_antisymm
  · rintro z ⟨⟨x, hx, hxz⟩, ⟨y, hy, hyz⟩⟩
    obtain ⟨a, ha, c, hc, he⟩ := coneQuotient_common_lift b I (hxz.trans hyz.symm)
    have has : a ∈ latticeRayCone s := latticeRayCone_mono hIs ha
    have hct : c ∈ latticeRayCone t := latticeRayCone_mono hIt hc
    have hboth : x + a ∈ latticeRayCone (s ∩ t) := by
      rw [← «Σ».intersection s hs t ht]
      refine ⟨Submodule.add_mem _ hx has, ?_⟩
      rw [he]
      exact Submodule.add_mem _ hy hct
    refine ⟨x + a, hboth, ?_⟩
    change coneQuotientReal b I x = z at hxz
    change coneQuotientReal b I (x + a) = z
    rw [map_add, coneQuotient_zero_on_cone b I ha, add_zero, hxz]
  · rintro z ⟨x, hx, rfl⟩
    exact ⟨⟨x, latticeRayCone_mono Finset.inter_subset_left hx, rfl⟩,
      ⟨x, latticeRayCone_mono Finset.inter_subset_right hx, rfl⟩⟩

end SmoothCompleteFan

/-- Removing the rays killed by the quotient does not change the image cone. -/
theorem latticeRayCone_quotient_sdiff
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (s : Finset (Lattice n)) :
    latticeRayCone ((s \ I.image b).image (coneQuotientLattice b I)) =
      (latticeRayCone s).map (coneQuotientReal b I) := by
  rw [← latticeRayCone_image_quotient]
  apply le_antisymm
  · exact latticeRayCone_mono (Finset.image_subset_image Finset.sdiff_subset)
  · rw [latticeRayCone, finiteRayCone_eq_hull]
    apply Submodule.span_le.mpr
    intro x hx
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    by_cases hwI : w ∈ I.image b
    · rw [coneQuotientLattice_of_mem b I hwI, map_zero]
      exact Submodule.zero_mem _
    · exact latticeRayCone_generator _ (Finset.mem_image.mpr
        ⟨w, Finset.mem_sdiff.mpr ⟨hw, hwI⟩, rfl⟩)

theorem basis_image_card_eq {b c : Module.Basis (Fin n) ℤ (Lattice n)}
    {I J : Finset (Fin n)} (hIJ : I.image b = J.image c) : I.card = J.card := by
  have h := congrArg Finset.card hIJ
  simpa only [Finset.card_image_of_injective _ b.injective,
    Finset.card_image_of_injective _ c.injective] using h

/-- A full integral basis of the quotient, constructed from any full basis
containing the deleted rays. -/
def coneQuotientBasis (b c : Module.Basis (Fin n) ℤ (Lattice n))
    (I J : Finset (Fin n)) (hIJ : I.image b = J.image c) :
    Module.Basis (Fin (n - I.card)) ℤ (Lattice (n - I.card)) :=
  ((descendedQuotientBasis b c I J
      (by simpa only [Finset.ext_iff, Finset.mem_image] using hIJ)).map
    (quotientCoordinateFinEquiv ℤ I)).reindex
    (Fintype.equivFinOfCardEq (by
      rw [complementaryIndex_card, basis_image_card_eq hIJ]))

theorem coneQuotientBasis_range (b c : Module.Basis (Fin n) ℤ (Lattice n))
    (I J : Finset (Fin n)) (hIJ : I.image b = J.image c)
    (j : ComplementaryIndex J) :
    coneQuotientLattice b I (c j) ∈
      (Finset.univ : Finset (Fin (n - I.card))).image (coneQuotientBasis b c I J hIJ) := by
  let e : ComplementaryIndex J ≃ Fin (n - I.card) :=
    Fintype.equivFinOfCardEq (by rw [complementaryIndex_card, basis_image_card_eq hIJ])
  refine Finset.mem_image.mpr ⟨e j, Finset.mem_univ _, ?_⟩
  simp only [coneQuotientBasis, Module.Basis.reindex_apply, Module.Basis.map_apply]
  change quotientCoordinateFinEquiv ℤ I
    (descendedQuotientBasis b c I J
      (by simpa only [Finset.ext_iff, Finset.mem_image] using hIJ) (e.symm (e j))) = _
  rw [e.symm_apply_apply, descendedQuotientBasis_apply]
  rfl

namespace SmoothCompleteFan

variable («Σ» : SmoothCompleteFan n)

/-- Smoothness survives in the saturated quotient, with an actual integral
basis of the target lattice. -/
theorem coneQuotient_smooth
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    {s : Finset (Lattice n)} (hs : s ∈ «Σ».cones) (hIs : I.image b ⊆ s) :
    ∃ (β : Module.Basis (Fin (n - I.card)) ℤ (Lattice (n - I.card)))
      (K : Finset (Fin (n - I.card))),
      (s \ I.image b).image (coneQuotientLattice b I) = K.image β := by
  obtain ⟨c, L, hL⟩ := «Σ».smooth s hs
  let J := basisRayIndices c (I.image b)
  have hJ : J.image c = I.image b := image_basisRayIndices c _ (by
    intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hL ▸ hIs hv)
    exact Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
  let β := coneQuotientBasis b c I J hJ.symm
  let T := (s \ I.image b).image (coneQuotientLattice b I)
  have hT : T ⊆ Finset.univ.image β := by
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hwS, hwF⟩ := Finset.mem_sdiff.mp hw
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hL ▸ hwS)
    have hiJ : i ∉ J := by
      intro hij
      exact hwF (hJ ▸ Finset.mem_image.mpr ⟨i, hij, rfl⟩)
    exact coneQuotientBasis_range b c I J hJ.symm ⟨i, hiJ⟩
  exact ⟨β, basisRayIndices β T, (image_basisRayIndices β T hT).symm⟩

theorem coneQuotient_nonzero_ray
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    {s : Finset (Lattice n)} (hs : s ∈ «Σ».cones) (hIs : I.image b ⊆ s)
    {v : Lattice n} (hv : v ∈ s \ I.image b) : coneQuotientLattice b I v ≠ 0 := by
  obtain ⟨β, K, hK⟩ := «Σ».coneQuotient_smooth b I hs hIs
  have hmem : coneQuotientLattice b I v ∈ K.image β :=
    hK ▸ Finset.mem_image.mpr ⟨v, hv, rfl⟩
  obtain ⟨j, hj, he⟩ := Finset.mem_image.mp hmem
  rw [← he]
  exact β.ne_zero j

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricBundleFanQuotient
-- END ORIGINAL PaperVerification.ToricBundleFanQuotient


-- BEGIN ORIGINAL PaperVerification.ToricBundleFanStar
section Source_ToricBundleFanStar

-- original header: module

-- original header: public import PaperVerification.ToricBundleFanQuotient


-- original header: @[expose] public section
/-!
# The fan of projected cones over a smooth cone

The only input to completeness in this construction is the literal covering
of quotient vectors by projected cones.  Smoothness, finiteness, intersections,
faces, purity, and uniqueness of ray lifts are proved from the original fan.
The empty-focus bundle case proves this covering in `ToricBundleFan`.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem coneQuotient_injective_star_rays
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    {s t : Finset (Lattice n)} (hs : s ∈ «Σ».cones) (ht : t ∈ «Σ».cones)
    (hIs : I.image b ⊆ s) (hIt : I.image b ⊆ t)
    {v w : Lattice n} (hv : v ∈ s \ I.image b) (hw : w ∈ t \ I.image b)
    (he : coneQuotientLattice b I v = coneQuotientLattice b I w) : v = w := by
  by_contra hvw
  let F := I.image b
  let S := insert v F
  let T := insert w F
  have hS : S ∈ «Σ».cones := «Σ».downward s hs S (by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact (Finset.mem_sdiff.mp hv).1
    · exact hIs ha)
  have hT : T ∈ «Σ».cones := «Σ».downward t ht T (by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact (Finset.mem_sdiff.mp hw).1
    · exact hIt ha)
  have hST : S ∩ T = F := by
    ext a
    constructor
    · intro ha
      obtain ⟨haS, haT⟩ := Finset.mem_inter.mp ha
      rcases Finset.mem_insert.mp haS with rfl | haF
      · rcases Finset.mem_insert.mp haT with heq | haF
        · exact (hvw heq).elim
        · exact haF
      · exact haF
    · intro ha
      exact Finset.mem_inter.mpr ⟨Finset.mem_insert_of_mem ha, Finset.mem_insert_of_mem ha⟩
  have hm : embed (n - I.card) (coneQuotientLattice b I v) ∈
      (latticeRayCone S).map (coneQuotientReal b I) ⊓
        (latticeRayCone T).map (coneQuotientReal b I) := by
    refine ⟨⟨embed n v, latticeRayCone_generator S (Finset.mem_insert_self v F),
      coneQuotient_compatible b I v⟩, ?_⟩
    refine ⟨embed n w, latticeRayCone_generator T (Finset.mem_insert_self w F), ?_⟩
    change coneQuotientReal b I (embed n w) =
      embed (n - I.card) (coneQuotientLattice b I v)
    rw [coneQuotient_compatible, he]
  rw [«Σ».coneQuotient_intersection b I hS hT
    (Finset.subset_insert v F) (Finset.subset_insert w F), hST] at hm
  obtain ⟨x, hx, hxe⟩ := hm
  change coneQuotientReal b I x =
    embed (n - I.card) (coneQuotientLattice b I v) at hxe
  have hz : coneQuotientLattice b I v = 0 := by
    apply embed_injective (n - I.card)
    rw [← hxe, coneQuotient_zero_on_cone b I hx, map_zero]
  exact «Σ».coneQuotient_nonzero_ray b I hs hIs hv hz

/-- Literal finite family of all quotient cones over the deleted cone. -/
def quotientStarCones (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) : Finset (Finset (Lattice (n - I.card))) :=
  («Σ».cones.filter (fun s => I.image b ⊆ s)).image
    (fun s => (s \ I.image b).image (coneQuotientLattice b I))

theorem mem_quotientStarCones (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) (t : Finset (Lattice (n - I.card))) :
    t ∈ «Σ».quotientStarCones b I ↔
      ∃ s ∈ «Σ».cones, I.image b ⊆ s ∧
        t = (s \ I.image b).image (coneQuotientLattice b I) := by
  simp only [quotientStarCones, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨s, ⟨hs, hIs⟩, he⟩
    exact ⟨s, hs, hIs, he.symm⟩
  · rintro ⟨s, hs, hIs, he⟩
    exact ⟨s, ⟨hs, hIs⟩, he.symm⟩

theorem quotientStarCones_downward (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) {s t : Finset (Lattice (n - I.card))}
    (hs : s ∈ «Σ».quotientStarCones b I) (hts : t ⊆ s) :
    t ∈ «Σ».quotientStarCones b I := by
  obtain ⟨S, hS, hIS, rfl⟩ := («Σ».mem_quotientStarCones b I s).mp hs
  let D := S.filter (fun v => v ∉ I.image b ∧ coneQuotientLattice b I v ∈ t)
  have hD : I.image b ∪ D ⊆ S := Finset.union_subset hIS (Finset.filter_subset _ _)
  refine («Σ».mem_quotientStarCones b I t).mpr
    ⟨I.image b ∪ D, «Σ».downward S hS _ hD, Finset.subset_union_left, ?_⟩
  ext v
  constructor
  · intro hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp (hts hv)
    obtain ⟨hwS, hwI⟩ := Finset.mem_sdiff.mp hw
    exact Finset.mem_image.mpr ⟨w,
      Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _
        (Finset.mem_filter.mpr ⟨hwS, hwI, hv⟩), hwI⟩, rfl⟩
  · intro hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hwU, hwI⟩ := Finset.mem_sdiff.mp hw
    rcases Finset.mem_union.mp hwU with hwF | hwD
    · exact (hwI hwF).elim
    · exact (Finset.mem_filter.mp hwD).2.2

theorem quotientStarCones_intersection (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) {s t : Finset (Lattice (n - I.card))}
    (hs : s ∈ «Σ».quotientStarCones b I) (ht : t ∈ «Σ».quotientStarCones b I) :
    latticeRayCone s ⊓ latticeRayCone t = latticeRayCone (s ∩ t) := by
  obtain ⟨S, hS, hIS, rfl⟩ := («Σ».mem_quotientStarCones b I s).mp hs
  obtain ⟨T, hT, hIT, rfl⟩ := («Σ».mem_quotientStarCones b I t).mp ht
  apply le_antisymm
  · rw [latticeRayCone_quotient_sdiff, latticeRayCone_quotient_sdiff,
      «Σ».coneQuotient_intersection b I hS hT hIS hIT,
      ← latticeRayCone_quotient_sdiff]
    apply latticeRayCone_mono
    intro v hv
    obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hv
    obtain ⟨hwST, hwI⟩ := Finset.mem_sdiff.mp hw
    obtain ⟨hwS, hwT⟩ := Finset.mem_inter.mp hwST
    exact Finset.mem_inter.mpr
      ⟨Finset.mem_image.mpr ⟨w, Finset.mem_sdiff.mpr ⟨hwS, hwI⟩, rfl⟩,
        Finset.mem_image.mpr ⟨w, Finset.mem_sdiff.mpr ⟨hwT, hwI⟩, rfl⟩⟩
  · exact le_inf (latticeRayCone_mono Finset.inter_subset_left)
      (latticeRayCone_mono Finset.inter_subset_right)

/-- The actual smooth complete fan in the saturated quotient.  Its covering
input is an ordinary statement about real images of actual cones. -/
def quotientStarFan (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n))
    (hcover : ∀ y : Ambient (n - I.card), ∃ s ∈ «Σ».cones,
      I.image b ⊆ s ∧ y ∈ (latticeRayCone s).map (coneQuotientReal b I)) :
    SmoothCompleteFan (n - I.card) where
  cones := «Σ».quotientStarCones b I
  smooth := by
    intro s hs
    obtain ⟨S, hS, hIS, rfl⟩ := («Σ».mem_quotientStarCones b I s).mp hs
    exact «Σ».coneQuotient_smooth b I hS hIS
  downward := by
    intro s hs t hts
    exact «Σ».quotientStarCones_downward b I hs hts
  intersection := by
    intro s hs t ht
    exact «Σ».quotientStarCones_intersection b I hs ht
  complete := by
    intro y
    obtain ⟨S, hS, hIS, hy⟩ := hcover y
    refine ⟨(S \ I.image b).image (coneQuotientLattice b I),
      («Σ».mem_quotientStarCones b I _).mpr ⟨S, hS, hIS, rfl⟩, ?_⟩
    rw [latticeRayCone_quotient_sdiff]
    exact hy

theorem quotientStarFan_isPure (hpure : «Σ».IsPure)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hcover : ∀ y : Ambient (n - I.card), ∃ s ∈ «Σ».cones,
      I.image b ⊆ s ∧ y ∈ (latticeRayCone s).map (coneQuotientReal b I)) :
    («Σ».quotientStarFan b I hcover).IsPure := by
  intro s hs
  obtain ⟨S, hS, hIS, rfl⟩ := («Σ».mem_quotientStarCones b I s).mp hs
  obtain ⟨T, hT, hST, hcard⟩ := hpure S hS
  have hIT : I.image b ⊆ T := hIS.trans hST
  refine ⟨(T \ I.image b).image (coneQuotientLattice b I),
    («Σ».mem_quotientStarCones b I _).mpr ⟨T, hT, hIT, rfl⟩, ?_, ?_⟩
  · exact Finset.image_subset_image (Finset.sdiff_subset_sdiff_left (I.image b) hST)
  · rw [Finset.card_image_of_injOn, Finset.card_sdiff_of_subset hIT,
      Finset.card_image_of_injective I b.injective, hcard]
    intro v hv w hw he
    exact «Σ».coneQuotient_injective_star_rays b I hT hT hIT hIT hv hw he

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricBundleFanStar
-- END ORIGINAL PaperVerification.ToricBundleFanStar


-- BEGIN ORIGINAL PaperVerification.ToricQuotientStarCovering
section Source_ToricQuotientStarCovering

-- original header: module

-- original header: public import PaperVerification.ToricBundleFanStar
-- original header: public import Mathlib.Topology.MetricSpace.Basic

-- original header: @[expose] public section

/-!
# Completeness of the actual quotient star

The sum of the deleted cone's primitive rays lies in no cone which fails
to contain that cone. A finite union of closed basis cones stays away from
that point. Small perturbations in any quotient direction therefore lie
in cones containing the deleted cone, and projection followed by positive
rescaling proves completeness in the saturated quotient.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators Classical

theorem isClosed_finiteRayCone_basis {n : ℕ}
    (b : Module.Basis (Fin n) ℝ (Ambient n)) (I : Finset (Fin n)) :
    IsClosed (finiteRayCone (I.image b) : Set (Ambient n)) := by
  have he : (finiteRayCone (I.image b) : Set (Ambient n)) =
      (⋂ i, {x : Ambient n | 0 ≤ b.coord i x}) ∩
      (⋂ i, ⋂ (_ : i ∉ I), {x : Ambient n | b.coord i x = 0}) := by
    have hI : I.image b =
        @Finset.image (Fin n) (Ambient n)
          (fun (x y : Ambient n) => Classical.propDecidable (x = y)) b I := by
      ext y
      simp only [Finset.mem_image]
    ext x
    change (x ∈ finiteRayCone (I.image b)) ↔ _
    rw [hI]
    simpa only [Set.mem_inter_iff, Set.mem_iInter, Set.mem_setOf_eq,
      Module.Basis.coord_apply] using (mem_finiteRayCone_basis_iff b I x)
  rw [he]
  apply IsClosed.inter
  · apply isClosed_iInter
    intro i
    exact isClosed_le continuous_const (b.coord i).continuous_of_finiteDimensional
  · apply isClosed_iInter
    intro i
    apply isClosed_iInter
    intro hi
    exact isClosed_eq (b.coord i).continuous_of_finiteDimensional continuous_const

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem isClosed_latticeRayCone {s : Finset (Lattice n)} (hs : s ∈ «Σ».cones) :
    IsClosed (latticeRayCone s : Set (Ambient n)) := by
  obtain ⟨b, I, rfl⟩ := «Σ».smooth s hs
  rw [latticeRayCone_basis]
  exact isClosed_finiteRayCone_basis (integralBasisReal b) I

/-- Every real direction admits a positive small perturbation of the ray
sum inside an actual cone containing the original cone. -/
theorem exists_small_perturbation_in_containing_cone
    {F : Finset (Lattice n)} (hF : F ∈ «Σ».cones) (x : Ambient n) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ s ∈ «Σ».cones, F ⊆ s ∧
      (∑ u ∈ F, embed n u) + ε • x ∈ latticeRayCone s := by
  let w : Ambient n := ∑ u ∈ F, embed n u
  let bad := «Σ».cones.filter (fun s => ¬ F ⊆ s)
  let Z : Set (Ambient n) := ⋃ s ∈ bad, (latticeRayCone s : Set (Ambient n))
  have hclosed : IsClosed Z := by
    apply isClosed_biUnion_finset
    intro s hs
    exact «Σ».isClosed_latticeRayCone (Finset.mem_filter.mp hs).1
  have hw : w ∉ Z := by
    intro hw
    obtain ⟨s, hs, hws⟩ := Set.mem_iUnion₂.mp hw
    exact (Finset.mem_filter.mp hs).2
      («Σ».sum_mem_cone_implies_subset hF (Finset.mem_filter.mp hs).1 hws)
  let φ : ℝ → Ambient n := fun ε => w + ε • x
  have hφ : Continuous φ := continuous_const.add (continuous_id.smul continuous_const)
  have hopen : IsOpen (φ ⁻¹' Zᶜ) := hclosed.isOpen_compl.preimage hφ
  have hzero : (0 : ℝ) ∈ φ ⁻¹' Zᶜ := by
    change w + (0 : ℝ) • x ∉ Z
    simpa only [zero_smul, add_zero] using hw
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen 0 hzero
  let ε : ℝ := δ / 2
  have hε : 0 < ε := div_pos hδ (by norm_num)
  have hεball : ε ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hε]
    dsimp only [ε]
    linarith
  have houtside : φ ε ∉ Z := hball hεball
  obtain ⟨s, hs, hφs⟩ := «Σ».complete (φ ε)
  have hFs : F ⊆ s := by
    by_contra hn
    apply houtside
    exact Set.mem_iUnion₂.mpr ⟨s, Finset.mem_filter.mpr ⟨hs, hn⟩, hφs⟩
  exact ⟨ε, hε, s, hs, hFs, hφs⟩

/-- The literal projected-cover statement required by `quotientStarFan`,
proved for every actual smooth cone, including the empty cone. -/
theorem coneQuotient_projected_cover
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hF : I.image b ∈ «Σ».cones) :
    ∀ y : Ambient (n - I.card), ∃ s ∈ «Σ».cones,
      I.image b ⊆ s ∧ y ∈ (latticeRayCone s).map (coneQuotientReal b I) := by
  intro y
  let F := I.image b
  let w : Ambient n := ∑ u ∈ F, embed n u
  let bad := «Σ».cones.filter (fun s => ¬ F ⊆ s)
  let Z : Set (Ambient n) := ⋃ s ∈ bad, (latticeRayCone s : Set (Ambient n))
  have hclosed : IsClosed Z := by
    apply isClosed_biUnion_finset
    intro s hs
    exact «Σ».isClosed_latticeRayCone (Finset.mem_filter.mp hs).1
  have hw : w ∉ Z := by
    intro hw
    obtain ⟨s, hs, hws⟩ := Set.mem_iUnion₂.mp hw
    have hscone := (Finset.mem_filter.mp hs).1
    have hnsub := (Finset.mem_filter.mp hs).2
    exact hnsub («Σ».sum_mem_cone_implies_subset hF hscone hws)
  let φ : ℝ → Ambient n := fun ε => w + ε • coneQuotientSectionReal b I y
  have hφ : Continuous φ := continuous_const.add (continuous_id.smul continuous_const)
  have hopen : IsOpen (φ ⁻¹' Zᶜ) := hclosed.isOpen_compl.preimage hφ
  have hzero : (0 : ℝ) ∈ φ ⁻¹' Zᶜ := by
    change w + (0 : ℝ) • coneQuotientSectionReal b I y ∉ Z
    simpa only [zero_smul, add_zero] using hw
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hopen 0 hzero
  let ε : ℝ := δ / 2
  have hε : 0 < ε := div_pos hδ (by norm_num)
  have hεball : ε ∈ Metric.ball (0 : ℝ) δ := by
    rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hε]
    dsimp only [ε]
    linarith
  have houtside : φ ε ∉ Z := hball hεball
  obtain ⟨s, hs, hφs⟩ := «Σ».complete (φ ε)
  have hFs : F ⊆ s := by
    by_contra hn
    apply houtside
    exact Set.mem_iUnion₂.mpr ⟨s, Finset.mem_filter.mpr ⟨hs, hn⟩, hφs⟩
  have hwcone : w ∈ latticeRayCone (I.image b) := by
    apply Submodule.sum_mem
    intro u hu
    exact latticeRayCone_generator _ hu
  have hproj : coneQuotientReal b I (φ ε) = ε • y := by
    change coneQuotientReal b I (w + ε • coneQuotientSectionReal b I y) = ε • y
    rw [map_add, coneQuotient_zero_on_cone b I hwcone,
      map_smul, coneQuotient_section_real, zero_add]
  have hmem : ε • y ∈ (latticeRayCone s).map (coneQuotientReal b I) :=
    ⟨φ ε, hφs, hproj⟩
  have hscaled := PointedCone.smul_mem
    ((latticeRayCone s).map (coneQuotientReal b I)) (inv_nonneg.mpr hε.le) hmem
  refine ⟨s, hs, hFs, ?_⟩
  simpa only [smul_smul, inv_mul_cancel₀ (ne_of_gt hε), one_smul] using hscaled

/-- The actual saturated quotient star of any cone of a smooth complete
fan is a smooth complete fan, with no completeness premise left over. -/
def completeQuotientStarFan
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hF : I.image b ∈ «Σ».cones) : SmoothCompleteFan (n - I.card) :=
  «Σ».quotientStarFan b I («Σ».coneQuotient_projected_cover b I hF)

theorem completeQuotientStarFan_isPure (hpure : «Σ».IsPure)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (hF : I.image b ∈ «Σ».cones) : («Σ».completeQuotientStarFan b I hF).IsPure :=
  «Σ».quotientStarFan_isPure hpure b I («Σ».coneQuotient_projected_cover b I hF)

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricQuotientStarCovering
-- END ORIGINAL PaperVerification.ToricQuotientStarCovering


-- BEGIN ORIGINAL PaperVerification.ToricBundleFan
section Source_ToricBundleFan

-- original header: module

-- original header: public import PaperVerification.ToricBundleFanStar
-- original header: public import PaperVerification.ToricQuotientStarCovering


-- original header: @[expose] public section
/-!
# The fan of a projective-space bundle from a zero-focus relation

The lattice splitting and the exact product description of cones are derived
from the primitive relation and its cone replacement property.  In particular,
no bundle, contraction morphism, or quotient-fan conclusion is included in the
input data.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan.PrimitiveRelation

variable {n : ℕ} {«Σ» : SmoothCompleteFan n} (R : «Σ».PrimitiveRelation)

/-- A choice of an integral basis extending all but one positive ray.
This contains only coordinate choices, not a quotient-fan assertion. -/
structure BundleCoordinates where
  omitted : Lattice n
  omitted_mem : omitted ∈ R.positive
  basis : Module.Basis (Fin n) ℤ (Lattice n)
  fiberIndices : Finset (Fin n)
  fiber_ray_set : fiberIndices.image basis = R.positive.erase omitted

theorem bundleCoordinates_nonempty : Nonempty R.BundleCoordinates := by
  obtain ⟨u, hu⟩ := «Σ».primitiveCollection_nonempty R.primitive
  obtain ⟨b, I, hI⟩ := «Σ».smooth (R.positive.erase u)
    (R.primitive.2.2 _ (Finset.erase_ssubset hu))
  exact ⟨⟨u, hu, b, I, hI.symm⟩⟩

def bundleCoordinates : R.BundleCoordinates := Classical.choice R.bundleCoordinates_nonempty

namespace BundleCoordinates

variable {R} (c : R.BundleCoordinates)

theorem fiberIndices_card : c.fiberIndices.card = R.fiberDimension := by
  rw [← Finset.card_image_of_injective c.fiberIndices c.basis.injective,
    c.fiber_ray_set, Finset.card_erase_of_mem c.omitted_mem]
  rfl

theorem fiber_cone : c.fiberIndices.image c.basis ∈ «Σ».cones := by
  rw [c.fiber_ray_set]
  exact R.primitive.2.2 _ (Finset.erase_ssubset c.omitted_mem)

theorem fiber_subset_positive : c.fiberIndices.image c.basis ⊆ R.positive := by
  rw [c.fiber_ray_set]
  exact Finset.erase_subset _ _

abbrev quotientLattice : Lattice n →ₗ[ℤ] Lattice (n - c.fiberIndices.card) :=
  coneQuotientLattice c.basis c.fiberIndices

abbrev quotientReal : Ambient n →ₗ[ℝ] Ambient (n - c.fiberIndices.card) :=
  coneQuotientReal c.basis c.fiberIndices

/-- The genuine smooth complete base fan in the saturated quotient lattice. -/
def baseFan : SmoothCompleteFan (n - c.fiberIndices.card) :=
  «Σ».completeQuotientStarFan c.basis c.fiberIndices c.fiber_cone

theorem baseFan_isPure (hpure : «Σ».IsPure) : c.baseFan.IsPure :=
  «Σ».completeQuotientStarFan_isPure hpure c.basis c.fiberIndices c.fiber_cone

theorem base_dimension : n - c.fiberIndices.card = n - R.fiberDimension := by
  rw [c.fiberIndices_card]

theorem omitted_eq_negative_sum (hN : R.negative = ∅) :
    c.omitted = -(∑ i ∈ c.fiberIndices, c.basis i) := by
  have hsum : (∑ v ∈ R.positive.erase c.omitted, v) + c.omitted = 0 := by
    calc
      (∑ v ∈ R.positive.erase c.omitted, v) + c.omitted =
          ∑ v ∈ R.positive, v :=
        Finset.sum_erase_add R.positive (fun v : Lattice n => v) c.omitted_mem
      _ = 0 := by
        rw [R.equation, hN]
        simp
  have he : (∑ v ∈ R.positive.erase c.omitted, v) =
      ∑ i ∈ c.fiberIndices, c.basis i := by
    rw [← c.fiber_ray_set, Finset.sum_image]
    exact fun i _ j _ hij => c.basis.injective hij
  rw [he] at hsum
  apply eq_neg_iff_add_eq_zero.mpr
  simpa only [add_comm] using hsum

theorem omitted_coordinate (hN : R.negative = ∅) (i : Fin n) :
    c.basis.repr c.omitted i = if i ∈ c.fiberIndices then -1 else 0 := by
  rw [c.omitted_eq_negative_sum hN]
  by_cases hi : i ∈ c.fiberIndices <;>
    simp [map_sum, Module.Basis.repr_self_apply, Finsupp.single_apply, hi]

theorem quotient_omitted (hN : R.negative = ∅) : c.quotientLattice c.omitted = 0 := by
  rw [c.omitted_eq_negative_sum hN, map_neg, map_sum]
  have hz : (∑ i ∈ c.fiberIndices, c.quotientLattice (c.basis i)) = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    exact coneQuotientLattice_of_mem c.basis c.fiberIndices
      (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
  rw [hz, neg_zero]

theorem quotient_positive (hN : R.negative = ∅) {v : Lattice n}
    (hv : v ∈ R.positive) : c.quotientLattice v = 0 := by
  by_cases hvu : v = c.omitted
  · rw [hvu, c.quotient_omitted hN]
  · apply coneQuotientLattice_of_mem c.basis c.fiberIndices
    rw [c.fiber_ray_set]
    exact Finset.mem_erase.mpr ⟨hvu, hv⟩

theorem omitted_not_mem_over_fiber {s : Finset (Lattice n)}
    (hs : s ∈ «Σ».cones) (hF : c.fiberIndices.image c.basis ⊆ s) :
    c.omitted ∉ s := by
  intro hu
  apply R.primitive.2.1
  apply «Σ».downward s hs R.positive
  intro v hv
  by_cases hvu : v = c.omitted
  · simpa only [hvu] using hu
  · apply hF
    rw [c.fiber_ray_set]
    exact Finset.mem_erase.mpr ⟨hvu, hv⟩

theorem over_fiber_sdiff_eq {s : Finset (Lattice n)}
    (hs : s ∈ «Σ».cones) (hF : c.fiberIndices.image c.basis ⊆ s) :
    s \ c.fiberIndices.image c.basis = s \ R.positive := by
  ext v
  constructor
  · intro hv
    obtain ⟨hvs, hvF⟩ := Finset.mem_sdiff.mp hv
    refine Finset.mem_sdiff.mpr ⟨hvs, ?_⟩
    intro hvP
    by_cases hvu : v = c.omitted
    · exact c.omitted_not_mem_over_fiber hs hF (hvu ▸ hvs)
    · apply hvF
      rw [c.fiber_ray_set]
      exact Finset.mem_erase.mpr ⟨hvu, hvP⟩
  · intro hv
    obtain ⟨hvs, hvP⟩ := Finset.mem_sdiff.mp hv
    exact Finset.mem_sdiff.mpr ⟨hvs, fun hvF => hvP (c.fiber_subset_positive hvF)⟩

/-- Every base-ray cone combines with every proper projective-fiber cone. -/
theorem fill_nonfiber_cone (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) {D : Finset (Lattice n)}
    (hD : D ∈ «Σ».cones) (hDP : Disjoint D R.positive) :
    c.fiberIndices.image c.basis ∪ D ∈ «Σ».cones := by
  rw [c.fiber_ray_set]
  exact R.fill_cone_with_positive_except hR hD
    (by rw [hN]; exact Finset.empty_subset _) c.omitted_mem
    (fun hu => Finset.disjoint_left.mp hDP hu c.omitted_mem)

theorem quotient_injective_nonfiber (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) {v w : Lattice n}
    (hv : v ∈ «Σ».rays \ R.positive) (hw : w ∈ «Σ».rays \ R.positive)
    (he : c.quotientLattice v = c.quotientLattice w) : v = w := by
  have hvs := «Σ».singleton_mem_of_mem_rays (Finset.mem_sdiff.mp hv).1
  have hws := «Σ».singleton_mem_of_mem_rays (Finset.mem_sdiff.mp hw).1
  have hDv : Disjoint ({v} : Finset (Lattice n)) R.positive := by
    simpa only [Finset.disjoint_singleton_left] using (Finset.mem_sdiff.mp hv).2
  have hDw : Disjoint ({w} : Finset (Lattice n)) R.positive := by
    simpa only [Finset.disjoint_singleton_left] using (Finset.mem_sdiff.mp hw).2
  exact «Σ».coneQuotient_injective_star_rays c.basis c.fiberIndices
    (c.fill_nonfiber_cone hR hN hvs hDv) (c.fill_nonfiber_cone hR hN hws hDw)
    Finset.subset_union_left Finset.subset_union_left
    (Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ (Finset.mem_singleton_self v),
      fun h => (Finset.mem_sdiff.mp hv).2 (c.fiber_subset_positive h)⟩)
    (Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ (Finset.mem_singleton_self w),
      fun h => (Finset.mem_sdiff.mp hw).2 (c.fiber_subset_positive h)⟩) he

theorem union_fiber_sdiff {D : Finset (Lattice n)}
    (hDP : Disjoint D R.positive) :
    (c.fiberIndices.image c.basis ∪ D) \ c.fiberIndices.image c.basis = D := by
  ext v
  constructor
  · intro hv
    obtain ⟨hvU, hvF⟩ := Finset.mem_sdiff.mp hv
    rcases Finset.mem_union.mp hvU with hvF' | hvD
    · exact (hvF hvF').elim
    · exact hvD
  · intro hvD
    exact Finset.mem_sdiff.mpr ⟨Finset.mem_union_right _ hvD,
      fun hvF => Finset.disjoint_left.mp hDP hvD (c.fiber_subset_positive hvF)⟩

/-- The base cones are precisely the images of cones on nonfiber rays.
The reverse direction uses the proved uniqueness of actual ray lifts. -/
theorem nonfiber_cone_iff_projected_cone (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) {D : Finset (Lattice n)}
    (hDrays : D ⊆ «Σ».rays) (hDP : Disjoint D R.positive) :
    D ∈ «Σ».cones ↔ D.image c.quotientLattice ∈
      «Σ».quotientStarCones c.basis c.fiberIndices := by
  constructor
  · intro hD
    apply («Σ».mem_quotientStarCones c.basis c.fiberIndices _).mpr
    refine ⟨c.fiberIndices.image c.basis ∪ D,
      c.fill_nonfiber_cone hR hN hD hDP, Finset.subset_union_left, ?_⟩
    rw [c.union_fiber_sdiff hDP]
  · intro hD
    obtain ⟨S, hS, hFS, he⟩ :=
      («Σ».mem_quotientStarCones c.basis c.fiberIndices _).mp hD
    have hDS : D = S \ c.fiberIndices.image c.basis := by
      ext v
      constructor
      · intro hv
        have himage : c.quotientLattice v ∈
            (S \ c.fiberIndices.image c.basis).image c.quotientLattice := by
          rw [← he]
          exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
        obtain ⟨w, hw, hwe⟩ := Finset.mem_image.mp himage
        have hwP : w ∉ R.positive := by
          rw [c.over_fiber_sdiff_eq hS hFS] at hw
          exact (Finset.mem_sdiff.mp hw).2
        have hvw := c.quotient_injective_nonfiber hR hN
          (Finset.mem_sdiff.mpr ⟨hDrays hv, fun hvP => Finset.disjoint_left.mp hDP hv hvP⟩)
          (Finset.mem_sdiff.mpr ⟨(«Σ».mem_rays_iff w).mpr
            ⟨S, hS, (Finset.mem_sdiff.mp hw).1⟩, hwP⟩) hwe.symm
        simpa only [hvw] using hw
      · intro hv
        have himage : c.quotientLattice v ∈ D.image c.quotientLattice := by
          rw [he]
          exact Finset.mem_image.mpr ⟨v, hv, rfl⟩
        obtain ⟨w, hw, hwe⟩ := Finset.mem_image.mp himage
        have hvP : v ∉ R.positive := by
          rw [c.over_fiber_sdiff_eq hS hFS] at hv
          exact (Finset.mem_sdiff.mp hv).2
        have hvw := c.quotient_injective_nonfiber hR hN
          (Finset.mem_sdiff.mpr ⟨(«Σ».mem_rays_iff v).mpr
            ⟨S, hS, (Finset.mem_sdiff.mp hv).1⟩, hvP⟩)
          (Finset.mem_sdiff.mpr ⟨hDrays hw, fun hwP => Finset.disjoint_left.mp hDP hw hwP⟩)
          hwe.symm
        simpa only [hvw] using hw
    rw [hDS]
    exact «Σ».downward S hS _ Finset.sdiff_subset

end BundleCoordinates

/-- Literal projective-fiber/base cone product.  The condition `J≠P`
means exactly that `J` is a proper cone of the projective-space fan. -/
theorem cone_union_fiber_iff (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) {J D : Finset (Lattice n)}
    (hJP : J ⊆ R.positive) (hDP : Disjoint D R.positive) :
    J ∪ D ∈ «Σ».cones ↔ J ≠ R.positive ∧ D ∈ «Σ».cones := by
  constructor
  · intro hcone
    refine ⟨?_, «Σ».downward _ hcone D Finset.subset_union_right⟩
    intro he
    exact R.primitive.2.1
      («Σ».downward _ hcone R.positive (he ▸ Finset.subset_union_left))
  · rintro ⟨hJ, hD⟩
    have hnot : ¬ R.positive ⊆ J := fun h => hJ (Finset.Subset.antisymm hJP h)
    obtain ⟨u, hu, huJ⟩ := Finset.not_subset.mp hnot
    have huD : u ∉ D := fun hud => Finset.disjoint_left.mp hDP hud hu
    have hfill := R.fill_cone_with_positive_except hR hD
      (by rw [hN]; exact Finset.empty_subset _) hu huD
    apply «Σ».downward _ hfill (J ∪ D)
    apply Finset.union_subset_union_left
    intro v hv
    exact Finset.mem_erase.mpr ⟨fun he => huJ (he ▸ hv), hJP hv⟩

namespace BundleCoordinates

variable {R} (c : R.BundleCoordinates)

/-- Complete cone correspondence with the actual quotient fan. -/
theorem cone_iff_fiber_and_base (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) {s : Finset (Lattice n)} (hsrays : s ⊆ «Σ».rays) :
    s ∈ «Σ».cones ↔ (s ∩ R.positive ≠ R.positive) ∧
      (s \ R.positive).image c.quotientLattice ∈
        «Σ».quotientStarCones c.basis c.fiberIndices := by
  have hpart : (s ∩ R.positive) ∪ (s \ R.positive) = s := by
    ext v
    simp only [Finset.mem_union, Finset.mem_inter, Finset.mem_sdiff]
    tauto
  have hdisjoint : Disjoint (s \ R.positive) R.positive := by
    exact Finset.disjoint_left.mpr (fun v hv hvP => (Finset.mem_sdiff.mp hv).2 hvP)
  rw [← c.nonfiber_cone_iff_projected_cone hR hN
    (Finset.sdiff_subset.trans hsrays) hdisjoint,
    ← R.cone_union_fiber_iff hR hN Finset.inter_subset_right hdisjoint, hpart]

theorem base_ray_iff (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (q : Lattice (n - c.fiberIndices.card)) :
    q ∈ c.baseFan.rays ↔ ∃ v ∈ «Σ».rays \ R.positive, c.quotientLattice v = q := by
  constructor
  · intro hq
    obtain ⟨D, hD, hqD⟩ := (c.baseFan.mem_rays_iff q).mp hq
    obtain ⟨S, hS, hFS, rfl⟩ :=
      («Σ».mem_quotientStarCones c.basis c.fiberIndices D).mp hD
    obtain ⟨v, hv, he⟩ := Finset.mem_image.mp hqD
    have hvP : v ∉ R.positive := by
      rw [c.over_fiber_sdiff_eq hS hFS] at hv
      exact (Finset.mem_sdiff.mp hv).2
    exact ⟨v, Finset.mem_sdiff.mpr ⟨(«Σ».mem_rays_iff v).mpr
      ⟨S, hS, (Finset.mem_sdiff.mp hv).1⟩, hvP⟩, he⟩
  · rintro ⟨v, hv, rfl⟩
    have hvcone := «Σ».singleton_mem_of_mem_rays (Finset.mem_sdiff.mp hv).1
    have hvdisj : Disjoint ({v} : Finset (Lattice n)) R.positive := by
      simpa only [Finset.disjoint_singleton_left] using (Finset.mem_sdiff.mp hv).2
    have hbasecone := (c.nonfiber_cone_iff_projected_cone hR hN
      (Finset.singleton_subset_iff.mpr (Finset.mem_sdiff.mp hv).1) hvdisj).mp hvcone
    exact (c.baseFan.mem_rays_iff _).mpr
      ⟨({v} : Finset (Lattice n)).image c.quotientLattice, hbasecone,
        Finset.mem_image.mpr ⟨v, Finset.mem_singleton_self v, rfl⟩⟩

/-- Projection identifies nonfiber primitive rays with base primitive rays.
Primitivity in the quotient follows from the integral smooth quotient basis. -/
def baseRayEquiv (hR : R.IsCombinatoriallyContractible) (hN : R.negative = ∅) :
    ↥(«Σ».rays \ R.positive) ≃ ↥c.baseFan.rays :=
  Equiv.ofBijective
    (fun v => ⟨c.quotientLattice v, (c.base_ray_iff hR hN _).mpr ⟨v, v.property, rfl⟩⟩)
    ⟨by
      intro v w he
      apply Subtype.ext
      exact c.quotient_injective_nonfiber hR hN v.property w.property
        (congrArg Subtype.val he), by
      intro q
      obtain ⟨v, hv, he⟩ := (c.base_ray_iff hR hN q).mp q.property
      exact ⟨⟨v, hv⟩, Subtype.ext he⟩⟩

@[simp] theorem baseRayEquiv_apply (hR : R.IsCombinatoriallyContractible)
    (hN : R.negative = ∅) (v : ↥(«Σ».rays \ R.positive)) :
    (c.baseRayEquiv hR hN v : Lattice (n - c.fiberIndices.card)) =
      c.quotientLattice v := rfl

/-- The unique actual nonfiber ray above a base ray, extended by zero away
from the base fan's rays solely to obtain a total coefficient function. -/
def baseRayLift (hR : R.IsCombinatoriallyContractible) (hN : R.negative = ∅)
    (q : Lattice (n - c.fiberIndices.card)) : Lattice n :=
  if hq : q ∈ c.baseFan.rays then
    ((c.baseRayEquiv hR hN).symm ⟨q, hq⟩ : Lattice n) else 0

theorem baseRayLift_mem (hR : R.IsCombinatoriallyContractible) (hN : R.negative = ∅)
    {q : Lattice (n - c.fiberIndices.card)} (hq : q ∈ c.baseFan.rays) :
    c.baseRayLift hR hN q ∈ «Σ».rays \ R.positive := by
  simp only [baseRayLift, dif_pos hq]
  exact ((c.baseRayEquiv hR hN).symm ⟨q, hq⟩).property

theorem quotient_baseRayLift (hR : R.IsCombinatoriallyContractible) (hN : R.negative = ∅)
    {q : Lattice (n - c.fiberIndices.card)} (hq : q ∈ c.baseFan.rays) :
    c.quotientLattice (c.baseRayLift hR hN q) = q := by
  simp only [baseRayLift, dif_pos hq]
  have h := congrArg Subtype.val ((c.baseRayEquiv hR hN).apply_symm_apply ⟨q, hq⟩)
  exact h

theorem baseRayLift_quotient (hR : R.IsCombinatoriallyContractible) (hN : R.negative = ∅)
    {v : Lattice n} (hv : v ∈ «Σ».rays \ R.positive) :
    c.baseRayLift hR hN (c.quotientLattice v) = v := by
  have hq := (c.base_ray_iff hR hN _).mpr ⟨v, hv, rfl⟩
  apply c.quotient_injective_nonfiber hR hN (c.baseRayLift_mem hR hN hq) hv
  exact c.quotient_baseRayLift hR hN hq

end BundleCoordinates

end SmoothCompleteFan.PrimitiveRelation

end PaperVerification.ToricGeometry
end
end Source_ToricBundleFan
-- END ORIGINAL PaperVerification.ToricBundleFan


-- BEGIN ORIGINAL PaperVerification.ToricNefCone
section Source_ToricNefCone

-- original header: module
-- original header: public import PaperVerification.ToricPrimitiveRelations
-- original header: public import Mathlib.Tactic.Linarith
-- original header: @[expose] public section
/-!
# Convex support data on actual smooth complete fans

Nefness is stated as feasibility of genuine linear supporting functions on
every actual cone. Strict support records strict inequalities on precisely
the rays outside that cone. Neither definition includes a primitive-relation
criterion; its forward implication is proved below, and its converse requires
a separate terminating reduction argument.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

/-- Convex support coefficients: each cone admits a real linear function
agreeing on that cone's primitive rays and bounded above on all fan rays. -/
def IsNef (a : Lattice n → ℝ) : Prop :=
  ∀ s ∈ «Σ».cones, ∃ ℓ : Ambient n →ₗ[ℝ] ℝ,
    (∀ v ∈ s, ℓ (embed n v) = a v) ∧
    (∀ v ∈ «Σ».rays, ℓ (embed n v) ≤ a v)

/-- Strict convex support on every actual cone. Rays outside that cone have
strict supporting slack. This is independent of primitive relations. -/
def IsStrictSupport (a : Lattice n → ℝ) : Prop :=
  ∀ s ∈ «Σ».cones, ∃ ℓ : Ambient n →ₗ[ℝ] ℝ,
    (∀ v ∈ s, ℓ (embed n v) = a v) ∧
    (∀ v ∈ «Σ».rays, v ∉ s → ℓ (embed n v) < a v)

theorem ray_mem_of_mem_cone {s : Finset (Lattice n)} (hs : s ∈ «Σ».cones)
    {v : Lattice n} (hv : v ∈ s) : v ∈ «Σ».rays :=
  («Σ».mem_rays_iff v).mpr ⟨s, hs, hv⟩

theorem IsStrictSupport.isNef {a : Lattice n → ℝ}
    (ha : «Σ».IsStrictSupport a) : «Σ».IsNef a := by
  intro s hs
  obtain ⟨ℓ, he, hlt⟩ := ha s hs
  refine ⟨ℓ, he, ?_⟩
  intro v hv
  by_cases hvs : v ∈ s
  · exact (he v hvs).le
  · exact (hlt v hv hvs).le

theorem IsStrictSupport.smul {a : Lattice n → ℝ}
    (ha : «Σ».IsStrictSupport a) {t : ℝ} (ht : 0 < t) :
    «Σ».IsStrictSupport (t • a) := by
  intro s hs
  obtain ⟨ℓ, he, hlt⟩ := ha s hs
  refine ⟨t • ℓ, ?_, ?_⟩
  · intro v hv
    simp only [LinearMap.smul_apply, Pi.smul_apply, he v hv]
  · intro v hv hvs
    exact mul_lt_mul_of_pos_left (hlt v hv hvs) ht

theorem isNef_zero : «Σ».IsNef (0 : Lattice n → ℝ) := by
  intro s hs
  exact ⟨0, by simp, by simp⟩

theorem IsNef.add {a b : Lattice n → ℝ}
    (ha : «Σ».IsNef a) (hb : «Σ».IsNef b) : «Σ».IsNef (a + b) := by
  intro s hs
  obtain ⟨ℓ, he, hle⟩ := ha s hs
  obtain ⟨k, ke, kle⟩ := hb s hs
  refine ⟨ℓ + k, ?_, ?_⟩
  · intro v hv
    simp only [LinearMap.add_apply, Pi.add_apply, he v hv, ke v hv]
  · intro v hv
    exact add_le_add (hle v hv) (kle v hv)

theorem IsNef.smul {a : Lattice n → ℝ} (ha : «Σ».IsNef a)
    {t : ℝ} (ht : 0 ≤ t) : «Σ».IsNef (t • a) := by
  intro s hs
  obtain ⟨ℓ, he, hle⟩ := ha s hs
  refine ⟨t • ℓ, ?_, ?_⟩
  · intro v hv
    simp only [LinearMap.smul_apply, Pi.smul_apply, he v hv]
  · intro v hv
    exact mul_le_mul_of_nonneg_left (hle v hv) ht

theorem isNef_linear (ℓ : Ambient n →ₗ[ℝ] ℝ) :
    «Σ».IsNef (fun v => ℓ (embed n v)) := by
  intro s hs
  exact ⟨ℓ, fun _ _ => rfl, fun _ _ => le_rfl⟩

namespace PrimitiveRelation

variable {«Σ»} (R : «Σ».PrimitiveRelation)

/-- A genuine balanced primitive relation annihilates every global linear
function, by applying that function to its lattice equation. -/
theorem degree_linear (ℓ : Ambient n →ₗ[ℝ] ℝ) :
    R.degree (fun v => ℓ (embed n v)) = 0 := by
  have he := congrArg ℓ (congrArg (embed n) R.equation)
  have hsum : (∑ v ∈ R.positive, ℓ (embed n v)) =
      ∑ v ∈ R.negative, (R.coefficient v : ℝ) * ℓ (embed n v) := by
    simpa only [map_sum, embed_int_smul, Int.cast_natCast, map_smul,
      smul_eq_mul] using he
  exact sub_eq_zero.mpr hsum

/-- Once a linear support is chosen on the focus cone, the primitive degree
is the sum of its actual supporting slacks on the positive collection. -/
theorem degree_eq_sum_slack (a : Lattice n → ℝ)
    (ℓ : Ambient n →ₗ[ℝ] ℝ)
    (he : ∀ v ∈ R.negative, ℓ (embed n v) = a v) :
    R.degree a = ∑ v ∈ R.positive, (a v - ℓ (embed n v)) := by
  have hz := R.degree_linear ℓ
  have hn : (∑ v ∈ R.negative,
      (R.coefficient v : ℝ) * ℓ (embed n v)) =
      ∑ v ∈ R.negative, (R.coefficient v : ℝ) * a v := by
    apply Finset.sum_congr rfl
    intro v hv
    rw [he v hv]
  simp only [degree] at hz ⊢
  rw [Finset.sum_sub_distrib]
  rw [hn] at hz
  linarith

/-- Convex support is nonnegative on every primitive relation. -/
theorem degree_nonneg_of_nef {a : Lattice n → ℝ} (ha : «Σ».IsNef a) :
    0 ≤ R.degree a := by
  obtain ⟨ℓ, he, hle⟩ := ha R.negative R.negative_cone
  rw [R.degree_eq_sum_slack a ℓ he]
  apply Finset.sum_nonneg
  intro v hv
  exact sub_nonneg.mpr (hle v (R.primitive.1 hv))

/-- Strict support has strictly positive degree on every primitive relation.
Disjointness of the two ray sets is used as a proved theorem. -/
theorem degree_pos_of_strictSupport {a : Lattice n → ℝ}
    (ha : «Σ».IsStrictSupport a) : 0 < R.degree a := by
  obtain ⟨ℓ, he, hlt⟩ := ha R.negative R.negative_cone
  rw [R.degree_eq_sum_slack a ℓ he]
  apply Finset.sum_pos
  · intro v hv
    apply sub_pos.mpr
    exact hlt v (R.primitive.1 hv)
      (fun hneg => Finset.disjoint_left.mp R.disjoint hv hneg)
  · exact «Σ».primitiveCollection_nonempty R.primitive

end PrimitiveRelation

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricNefCone
-- END ORIGINAL PaperVerification.ToricNefCone


-- BEGIN ORIGINAL PaperVerification.ToricEffectiveCone
section Source_ToricEffectiveCone

-- original header: module
-- original header: public import PaperVerification.ToricNefCone
-- original header: public import Mathlib.Data.Finset.Powerset
-- original header: public import Mathlib.Data.Set.Finite.Lemmas
-- original header: @[expose] public section

/-!
# The actual dual effective cone and extremal primitive relations

The effective cone is the cone of balanced ray coefficients nonnegative on
all genuinely convex support functions. Extremality means that the ordinary
nonnegative ray is a face of this cone, using Mathlib's face definition.

The replacement theorem is proved directly: a hypothetical missing cone
contains a primitive collection Q; both its relation and the difference from
the original relation are effective. Extremality forces proportionality,
which contradicts the omitted positive coefficient.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

/-- Sum an indicator over a larger finite set without changing its value. -/
theorem sum_indicator_of_subset {α E : Type*} [DecidableEq α] [AddCommMonoid E]
    {s t : Finset α} (hst : s ⊆ t) (f : α → E) :
    (∑ v ∈ t, if v ∈ s then f v else 0) = ∑ v ∈ s, f v := by
  rw [← Finset.sum_filter]
  apply Finset.sum_congr
  · ext v
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hst h, h⟩⟩
  · intro v hv
    rfl

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

/-- Real coefficients on precisely the finite set of actual primitive rays. -/
abbrev RaySpace := {v : Lattice n // v ∈ «Σ».rays} → ℝ

/-- The genuine vector represented by finite real ray coefficients. -/
def rayCombination : «Σ».RaySpace →ₗ[ℝ] Ambient n where
  toFun c := ∑ v : «Σ».rays, c v • embed n (v : Lattice n)
  map_add' c d := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' t c := by simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum,
    RingHom.id_apply]

/-- The ordinary finite divisor-relation pairing. -/
def rayPairing (a : Lattice n → ℝ) : «Σ».RaySpace →ₗ[ℝ] ℝ where
  toFun c := ∑ v : «Σ».rays, c v * a v
  map_add' c d := by simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' t c := by
    simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum, RingHom.id_apply]

/-- The dual cone to genuine nef support data, inside the space of balanced
relations. No primitive-generation assertion is built into this definition. -/
def effectiveCone : PointedCone ℝ «Σ».RaySpace :=
  PointedCone.ofConeComb
    {c | «Σ».rayCombination c = 0 ∧ ∀ a, «Σ».IsNef a → 0 ≤ «Σ».rayPairing a c}
    ⟨0, by simp, by simp⟩ (by
      rintro c ⟨hc, hcp⟩ d ⟨hd, hdp⟩ t ht u hu
      refine ⟨by simp only [map_add, map_smul, hc, hd, smul_zero, add_zero], ?_⟩
      intro a ha
      simp only [map_add, map_smul, smul_eq_mul]
      exact add_nonneg (mul_nonneg ht (hcp a ha)) (mul_nonneg hu (hdp a ha)))

theorem mem_effectiveCone_iff (c : «Σ».RaySpace) :
    c ∈ «Σ».effectiveCone ↔
      «Σ».rayCombination c = 0 ∧ ∀ a, «Σ».IsNef a → 0 ≤ «Σ».rayPairing a c := Iff.rfl

/-- A balanced relation whose negative coefficients are confined to a single
actual cone is effective. This is the convex-support proof of Casagrande 1.4. -/
theorem effective_of_negative_support_in_cone (c : «Σ».RaySpace)
    (hbalance : «Σ».rayCombination c = 0) (s : Finset (Lattice n))
    (hs : s ∈ «Σ».cones) (hpositive : ∀ v : «Σ».rays, (v : Lattice n) ∉ s → 0 ≤ c v) :
    c ∈ «Σ».effectiveCone := by
  refine ⟨hbalance, ?_⟩
  intro a ha
  obtain ⟨ℓ, he, hle⟩ := ha s hs
  have hz : (∑ v : «Σ».rays, c v * ℓ (embed n v)) = 0 := by
    have h := congrArg ℓ hbalance
    simpa only [rayCombination, LinearMap.coe_mk, AddHom.coe_mk, map_sum,
      map_smul, smul_eq_mul, map_zero] using h
  have hp : «Σ».rayPairing a c =
      ∑ v : «Σ».rays, c v * (a v - ℓ (embed n v)) := by
    simp only [rayPairing, LinearMap.coe_mk, AddHom.coe_mk,
      mul_sub, Finset.sum_sub_distrib, hz, sub_zero]
  rw [hp]
  apply Finset.sum_nonneg
  intro v hv
  by_cases hvs : (v : Lattice n) ∈ s
  · rw [he v hvs, sub_self, mul_zero]
  · exact mul_nonneg (hpositive v hvs) (sub_nonneg.mpr (hle v v.property))

/-- Every noncone finite ray set contains a genuine primitive collection. -/
theorem exists_primitiveCollection_subset {s : Finset (Lattice n)}
    (hsrays : s ⊆ «Σ».rays) (hs : s ∉ «Σ».cones) :
    ∃ Q, Q ⊆ s ∧ «Σ».IsPrimitiveCollection Q := by
  let T := s.powerset.filter (fun Q => Q ∉ «Σ».cones)
  have hsT : s ∈ T := by simp [T, hs]
  obtain ⟨Q, hQT, hmin⟩ := Set.exists_min_image (T : Set (Finset (Lattice n)))
    Finset.card T.finite_toSet ⟨s, hsT⟩
  obtain ⟨hQs, hQnot⟩ := Finset.mem_filter.mp hQT
  have hQsub : Q ⊆ s := Finset.mem_powerset.mp hQs
  refine ⟨Q, hQsub, hQsub.trans hsrays, hQnot, ?_⟩
  intro U hU
  by_contra hUnot
  have hUT : U ∈ T := Finset.mem_filter.mpr
    ⟨Finset.mem_powerset.mpr (Finset.Subset.trans (Finset.ssubset_iff_subset_ne.mp hU).1 hQsub),
      hUnot⟩
  exact (not_le_of_gt (Finset.card_lt_card hU)) (hmin U hUT)

namespace PrimitiveRelation

variable {«Σ»} (R : «Σ».PrimitiveRelation)

/-- The actual coefficient vector of the displayed primitive relation. -/
def vector : «Σ».RaySpace := fun v =>
  (if (v : Lattice n) ∈ R.positive then 1 else 0) -
  if (v : Lattice n) ∈ R.negative then (R.coefficient v : ℝ) else 0

theorem vector_eq_one {v : «Σ».rays} (hv : (v : Lattice n) ∈ R.positive) :
    R.vector v = 1 := by
  have hn : (v : Lattice n) ∉ R.negative :=
    fun h => Finset.disjoint_left.mp R.disjoint hv h
  simp only [vector, if_pos hv, if_neg hn, sub_zero]

theorem vector_le_one (v : «Σ».rays) : R.vector v ≤ 1 := by
  simp only [vector]
  split_ifs <;> have h := Nat.cast_nonneg (α := ℝ) (R.coefficient v) <;> linarith

theorem vector_nonpos_of_not_positive {v : «Σ».rays}
    (hv : (v : Lattice n) ∉ R.positive) : R.vector v ≤ 0 := by
  simp only [vector, if_neg hv, zero_sub]
  split_ifs <;> simp

theorem vector_ne_zero : R.vector ≠ 0 := by
  obtain ⟨v, hv⟩ := «Σ».primitiveCollection_nonempty R.primitive
  let j : «Σ».rays := ⟨v, R.primitive.1 hv⟩
  intro he
  have h := congrFun he j
  rw [R.vector_eq_one hv] at h
  norm_num at h

/-- The coefficient-vector pairing equals the displayed primitive degree. -/
theorem vector_sum {E : Type*} [AddCommGroup E] [Module ℝ E]
    (f : Lattice n → E) :
    (∑ v : «Σ».rays, R.vector v • f v) =
      (∑ v ∈ R.positive, f v) -
        ∑ v ∈ R.negative, (R.coefficient v : ℝ) • f v := by
  simp only [vector, sub_smul, ite_smul, one_smul, zero_smul,
    Finset.sum_sub_distrib]
  have hsum (g : Lattice n → E) :
      (∑ v : «Σ».rays, g v) = ∑ v ∈ «Σ».rays, g v :=
    (Finset.sum_subtype «Σ».rays (fun _ => Iff.rfl) g).symm
  rw [hsum (fun v => if v ∈ R.positive then f v else 0),
    hsum (fun v => if v ∈ R.negative then (R.coefficient v : ℝ) • f v else 0),
    sum_indicator_of_subset R.primitive.1]
  congr 1
  exact sum_indicator_of_subset
    (fun v hv => «Σ».ray_mem_of_mem_cone R.negative_cone hv)
    (fun v => (R.coefficient v : ℝ) • f v)

theorem vector_balanced : «Σ».rayCombination R.vector = 0 := by
  change (∑ v : «Σ».rays, R.vector v • embed n v) = 0
  rw [R.vector_sum]
  apply sub_eq_zero.mpr
  have h := congrArg (embed n) R.equation
  simpa only [map_sum, embed_int_smul, Int.cast_natCast] using h

theorem vector_pairing (a : Lattice n → ℝ) :
    «Σ».rayPairing a R.vector = R.degree a := by
  exact R.vector_sum a

theorem vector_effective : R.vector ∈ «Σ».effectiveCone := by
  refine ⟨R.vector_balanced, ?_⟩
  intro a ha
  rw [R.vector_pairing]
  exact R.degree_nonneg_of_nef ha

/-- Extremality is the literal Mathlib face property of the genuine
nonnegative ray in the dual effective cone. -/
def IsExtremal : Prop :=
  (PointedCone.hull ℝ ({R.vector} : Set «Σ».RaySpace)).IsFaceOf «Σ».effectiveCone

/-- Every extremal primitive relation satisfies the full Casagrande cone
replacement condition. No contraction geometry is assumed in this proof. -/
theorem combinatoriallyContractible_of_extremal (hR : R.IsExtremal) :
    R.IsCombinatoriallyContractible := by
  intro ν hν hdis hfocus x hx
  let s := R.positive.erase x ∪ R.negative ∪ ν
  by_contra hs
  have hsrays : s ⊆ «Σ».rays := by
    intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · rcases Finset.mem_union.mp hv with hv | hv
      · exact R.primitive.1 (Finset.mem_of_mem_erase hv)
      · exact «Σ».ray_mem_of_mem_cone R.negative_cone hv
    · exact «Σ».ray_mem_of_mem_cone hν hv
  obtain ⟨Q, hQs, hQ⟩ := «Σ».exists_primitiveCollection_subset hsrays hs
  obtain ⟨S, hSQ⟩ := «Σ».exists_primitiveRelation hQ
  have hSsub : S.positive ⊆ s := by simpa only [hSQ] using hQs
  have hbalance : «Σ».rayCombination (R.vector - S.vector) = 0 := by
    rw [map_sub, R.vector_balanced, S.vector_balanced, sub_self]
  have heff : R.vector - S.vector ∈ «Σ».effectiveCone := by
    apply «Σ».effective_of_negative_support_in_cone _ hbalance (R.negative ∪ ν) hfocus
    intro v hv
    have hvneg : (v : Lattice n) ∉ R.negative :=
      fun h => hv (Finset.mem_union_left _ h)
    by_cases hvpos : (v : Lattice n) ∈ R.positive
    · change 0 ≤ R.vector v - S.vector v
      rw [R.vector_eq_one hvpos]
      exact sub_nonneg.mpr (S.vector_le_one v)
    · have hvS : (v : Lattice n) ∉ S.positive := by
        intro h
        rcases Finset.mem_union.mp (hSsub h) with h | h
        · rcases Finset.mem_union.mp h with h | h
          · exact hvpos (Finset.mem_of_mem_erase h)
          · exact hvneg h
        · exact hv (Finset.mem_union_right _ h)
      have hz : R.vector v = 0 := by simp only [vector, if_neg hvpos, if_neg hvneg, sub_self]
      change 0 ≤ R.vector v - S.vector v
      rw [hz]
      linarith [S.vector_nonpos_of_not_positive hvS]
  have hsum : S.vector + (R.vector - S.vector) ∈
      PointedCone.hull ℝ ({R.vector} : Set «Σ».RaySpace) := by
    have heq : S.vector + (R.vector - S.vector) = R.vector := by abel
    rw [heq]
    exact PointedCone.subset_hull (Set.mem_singleton R.vector)
  have hSin := hR.mem_of_add_mem_left S.vector_effective heff hsum
  obtain ⟨t, ht, he⟩ := PointedCone.mem_hull_singleton.mp hSin
  have hxneg : x ∉ R.negative := fun h => Finset.disjoint_left.mp R.disjoint hx h
  have hxν : x ∉ ν := by
    intro h
    exact Finset.disjoint_left.mp hdis h (Finset.mem_union_left _ hx)
  have hxS : x ∉ S.positive := by
    intro h
    have hsx := hSsub h
    simp only [s, Finset.mem_union, Finset.mem_erase, ne_eq, not_true_eq_false,
      false_and, hxneg, hxν, or_self] at hsx
  let j : «Σ».rays := ⟨x, R.primitive.1 hx⟩
  have hcoord := congrFun he j
  have hnonpos := S.vector_nonpos_of_not_positive (v := j) hxS
  simp only [Pi.smul_apply, smul_eq_mul, R.vector_eq_one (v := j) hx, mul_one] at hcoord
  have ht0 : t = 0 := by linarith
  rw [ht0, zero_smul] at he
  exact S.vector_ne_zero he.symm

end PrimitiveRelation

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricEffectiveCone
-- END ORIGINAL PaperVerification.ToricEffectiveCone


-- BEGIN ORIGINAL PaperVerification.ToricPrimitiveReduction
section Source_ToricPrimitiveReduction

-- original header: module
-- original header: public import PaperVerification.ToricEffectiveCone
-- original header: public import Mathlib.Algebra.Order.Floor.Ring
-- original header: public import Lean.Elab.Tactic.Omega
-- original header: @[expose] public section

/-!
# Terminating primitive reductions

A nonnegative integral ray combination with noncone support can be reduced by
one genuine primitive relation. Integral strict support gives a decreasing
integer cost bounded below by a global supporting linear function. Thus the
reduction terminates in a cone, while every coefficient function nonnegative
on primitive relations has nonincreasing cost.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

def countSupport (c : Lattice n → ℕ) : Finset (Lattice n) :=
  «Σ».rays.filter (fun v => 0 < c v)

def countVector (c : Lattice n → ℕ) : Lattice n :=
  ∑ v ∈ «Σ».rays, (c v : ℤ) • v

def countCost (a : Lattice n → ℝ) (c : Lattice n → ℕ) : ℝ :=
  ∑ v ∈ «Σ».rays, (c v : ℝ) * a v

def countIntegerCost (H : Lattice n → ℤ) (c : Lattice n → ℕ) : ℤ :=
  ∑ v ∈ «Σ».rays, (c v : ℤ) * H v

theorem cast_countIntegerCost (H : Lattice n → ℤ) (c : Lattice n → ℕ) :
    («Σ».countIntegerCost H c : ℝ) = «Σ».countCost (fun v => (H v : ℝ)) c := by
  simp only [countIntegerCost, countCost, Int.cast_sum, Int.cast_mul, Int.cast_natCast]

/-- A globally supporting linear function gives a lower bound on the cost of
every nonnegative integral representation of a fixed lattice vector. -/
theorem countCost_lower_bound (a : Lattice n → ℝ)
    (ℓ : Ambient n →ₗ[ℝ] ℝ) (hℓ : ∀ v ∈ «Σ».rays, ℓ (embed n v) ≤ a v)
    (c : Lattice n → ℕ) :
    ℓ (embed n («Σ».countVector c)) ≤ «Σ».countCost a c := by
  have he : ℓ (embed n («Σ».countVector c)) =
      ∑ v ∈ «Σ».rays, (c v : ℝ) * ℓ (embed n v) := by
    simp only [countVector, map_sum, embed_int_smul, Int.cast_natCast,
      map_smul, smul_eq_mul]
  rw [he]
  exact Finset.sum_le_sum (fun v hv =>
    mul_le_mul_of_nonneg_left (hℓ v hv) (Nat.cast_nonneg _))

namespace PrimitiveRelation

variable {«Σ»} (R : «Σ».PrimitiveRelation)

/-- Replace one copy of each positive ray by its integral focus expansion. -/
def reduceCounts (c : Lattice n → ℕ) (v : Lattice n) : ℕ :=
  c v - (if v ∈ R.positive then 1 else 0) +
    if v ∈ R.negative then R.coefficient v else 0

theorem cast_reduceCounts {A : Type*} [Ring A] (c : Lattice n → ℕ)
    (hc : ∀ v ∈ R.positive, 0 < c v) (v : Lattice n) :
    (R.reduceCounts c v : A) = (c v : A) -
      (if v ∈ R.positive then 1 else 0) +
      if v ∈ R.negative then (R.coefficient v : A) else 0 := by
  have hsub : (if v ∈ R.positive then 1 else 0) ≤ c v := by
    split_ifs with hv
    · exact Nat.succ_le_of_lt (hc v hv)
    · exact Nat.zero_le _
  simp only [reduceCounts, Nat.cast_add, Nat.cast_sub hsub, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero]

/-- A primitive reduction preserves the actual lattice vector. -/
theorem countVector_reduceCounts (c : Lattice n → ℕ)
    (hc : ∀ v ∈ R.positive, 0 < c v) :
    «Σ».countVector (R.reduceCounts c) = «Σ».countVector c := by
  unfold countVector
  simp only [R.cast_reduceCounts c hc, add_smul, sub_smul, ite_smul,
    one_smul, zero_smul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [sum_indicator_of_subset R.primitive.1,
    sum_indicator_of_subset (fun v hv => «Σ».ray_mem_of_mem_cone R.negative_cone hv)]
  rw [R.equation]
  abel

/-- The cost drops by exactly the primitive relation degree. -/
theorem countCost_reduceCounts (a : Lattice n → ℝ) (c : Lattice n → ℕ)
    (hc : ∀ v ∈ R.positive, 0 < c v) :
    «Σ».countCost a (R.reduceCounts c) = «Σ».countCost a c - R.degree a := by
  unfold countCost degree
  simp only [R.cast_reduceCounts c hc, add_mul, sub_mul, ite_mul,
    one_mul, zero_mul, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [sum_indicator_of_subset R.primitive.1,
    sum_indicator_of_subset (fun v hv => «Σ».ray_mem_of_mem_cone R.negative_cone hv)]
  ring

theorem countIntegerCost_reduceCounts_lt (H : Lattice n → ℤ)
    (hH : «Σ».IsStrictSupport (fun v => (H v : ℝ))) (c : Lattice n → ℕ)
    (hc : ∀ v ∈ R.positive, 0 < c v) :
    «Σ».countIntegerCost H (R.reduceCounts c) < «Σ».countIntegerCost H c := by
  have he := R.countCost_reduceCounts (fun v => (H v : ℝ)) c hc
  have hp := R.degree_pos_of_strictSupport hH
  rw [← «Σ».cast_countIntegerCost H (R.reduceCounts c),
    ← «Σ».cast_countIntegerCost H c] at he
  have hreal : («Σ».countIntegerCost H (R.reduceCounts c) : ℝ) <
      («Σ».countIntegerCost H c : ℝ) := by linarith
  exact_mod_cast hreal

end PrimitiveRelation

/-- Integral strict support makes all primitive reductions terminate. The
terminal cone representation is no more expensive for any coefficient
function nonnegative on every primitive relation. -/
theorem exists_cone_reduction (H : Lattice n → ℤ)
    (hH : «Σ».IsStrictSupport (fun v => (H v : ℝ)))
    (a : Lattice n → ℝ) (ha : ∀ R : «Σ».PrimitiveRelation, 0 ≤ R.degree a)
    (c : Lattice n → ℕ) :
    ∃ d : Lattice n → ℕ, «Σ».countVector d = «Σ».countVector c ∧
      «Σ».countSupport d ∈ «Σ».cones ∧ «Σ».countCost a d ≤ «Σ».countCost a c := by
  let z := «Σ».countVector c
  obtain ⟨ℓ, hzero, hℓ⟩ :=
    IsStrictSupport.isNef «Σ» hH ∅ «Σ».empty_mem
  let lower : ℤ := ⌊ℓ (embed n z)⌋
  let measure (d : Lattice n → ℕ) : ℕ := («Σ».countIntegerCost H d - lower).toNat
  have hbounded (d : Lattice n → ℕ) (hd : «Σ».countVector d = z) :
      lower ≤ «Σ».countIntegerCost H d := by
    have hb := «Σ».countCost_lower_bound (fun v => (H v : ℝ)) ℓ hℓ d
    rw [hd, ← «Σ».cast_countIntegerCost H d] at hb
    have hf : (lower : ℝ) ≤ («Σ».countIntegerCost H d : ℝ) :=
      (Int.floor_le (ℓ (embed n z))).trans hb
    exact_mod_cast hf
  have hrec : ∀ k : ℕ, ∀ d : Lattice n → ℕ,
      «Σ».countVector d = z → measure d = k →
      ∃ e : Lattice n → ℕ, «Σ».countVector e = «Σ».countVector d ∧
        «Σ».countSupport e ∈ «Σ».cones ∧ «Σ».countCost a e ≤ «Σ».countCost a d := by
    intro k
    induction k using Nat.strong_induction_on with
    | h k ih =>
      intro d hd hmeasure
      by_cases hs : «Σ».countSupport d ∈ «Σ».cones
      · exact ⟨d, rfl, hs, le_rfl⟩
      · obtain ⟨Q, hQsub, hQ⟩ := «Σ».exists_primitiveCollection_subset
          (Finset.filter_subset _ _) hs
        obtain ⟨R, hRpos⟩ := «Σ».exists_primitiveRelation hQ
        have hpositive : ∀ v ∈ R.positive, 0 < d v := by
          intro v hv
          rw [hRpos] at hv
          exact (Finset.mem_filter.mp (hQsub hv)).2
        let d' := R.reduceCounts d
        have hvector : «Σ».countVector d' = «Σ».countVector d :=
          R.countVector_reduceCounts d hpositive
        have hd'z : «Σ».countVector d' = z := hvector.trans hd
        have hless : «Σ».countIntegerCost H d' < «Σ».countIntegerCost H d :=
          R.countIntegerCost_reduceCounts_lt H hH d hpositive
        have hmeasure' : measure d' < k := by
          rw [← hmeasure]
          change («Σ».countIntegerCost H d' - lower).toNat <
            («Σ».countIntegerCost H d - lower).toNat
          have hlow := hbounded d' hd'z
          exact (Int.toNat_lt_toNat (by omega)).mpr (by omega)
        obtain ⟨e, hevec, hecone, hecost⟩ := ih (measure d') hmeasure' d' hd'z rfl
        refine ⟨e, hevec.trans hvector, hecone, hecost.trans ?_⟩
        have hcost := R.countCost_reduceCounts a d hpositive
        change «Σ».countCost a (R.reduceCounts d) ≤ «Σ».countCost a d
        rw [hcost]
        exact sub_le_self _ (ha R)
  exact hrec (measure c) c rfl rfl

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricPrimitiveReduction
-- END ORIGINAL PaperVerification.ToricPrimitiveReduction


-- BEGIN ORIGINAL PaperVerification.ToricNefCriterion
section Source_ToricNefCriterion

-- original header: module

-- original header: public import PaperVerification.ToricPrimitiveReduction

-- original header: @[expose] public section

/-!
# The primitive-relation criterion for genuine nef support

The converse uses the terminating reductions, not a definition of nefness by
primitive inequalities. For a full smooth cone and an arbitrary ray v, add
enough copies of every basis ray that the sum remains in the full cone after
adding v. Reduce this nonnegative integral representation. Fan intersection
forces the terminal support back into that same cone, so cost monotonicity
gives the required Cartier inequality at v.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

theorem countVector_add (c d : Lattice n → ℕ) :
    «Σ».countVector (c + d) = «Σ».countVector c + «Σ».countVector d := by
  simp only [countVector, Pi.add_apply, Nat.cast_add, add_smul, Finset.sum_add_distrib]

theorem countCost_add (a : Lattice n → ℝ) (c d : Lattice n → ℕ) :
    «Σ».countCost a (c + d) = «Σ».countCost a c + «Σ».countCost a d := by
  simp only [countCost, Pi.add_apply, Nat.cast_add, add_mul, Finset.sum_add_distrib]

theorem countVector_single {v : Lattice n} (hv : v ∈ «Σ».rays) :
    «Σ».countVector (Pi.single v 1) = v := by
  simp [countVector, Pi.single_apply, Nat.cast_ite, ite_smul, hv]

theorem countCost_single (a : Lattice n → ℝ) {v : Lattice n} (hv : v ∈ «Σ».rays) :
    «Σ».countCost a (Pi.single v 1) = a v := by
  simp [countCost, Pi.single_apply, Nat.cast_ite, ite_mul, hv]

theorem countVector_indicator (t : Finset (Lattice n)) (ht : t ⊆ «Σ».rays) (N : ℕ) :
    «Σ».countVector (fun v => if v ∈ t then N else 0) = (N : ℤ) • ∑ v ∈ t, v := by
  simp only [countVector, Nat.cast_ite, Nat.cast_zero, ite_smul, zero_smul]
  rw [sum_indicator_of_subset ht]
  exact (Finset.smul_sum).symm

/-- Terms outside the genuine positive support contribute zero. -/
theorem embed_countVector_eq_sum_support (c : Lattice n → ℕ) :
    embed n («Σ».countVector c) =
      ∑ v ∈ «Σ».countSupport c, (c v : ℝ) • embed n v := by
  simp only [countVector, map_sum, embed_int_smul, Int.cast_natCast,
    countSupport, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hcv : 0 < c v
  · simp only [if_pos hcv]
  · have hzero : c v = 0 := Nat.eq_zero_of_not_pos hcv
    simp only [if_neg hcv, hzero, Nat.cast_zero, zero_smul, ite_self]

/-- If coefficients are positive on a cone and their actual sum lies in
another fan cone, every support ray belongs to the latter cone. -/
theorem countSupport_subset_of_vector_mem (c : Lattice n → ℕ)
    (hc : «Σ».countSupport c ∈ «Σ».cones) {t : Finset (Lattice n)} (ht : t ∈ «Σ».cones)
    (hvec : embed n («Σ».countVector c) ∈ latticeRayCone t) :
    «Σ».countSupport c ⊆ t := by
  apply «Σ».positive_sum_mem_cone_implies_subset hc ht (fun v => (c v : ℝ))
  · intro v hv
    exact_mod_cast (Finset.mem_filter.mp hv).2
  · rwa [← «Σ».embed_countVector_eq_sum_support c]

/-- If a linear function agrees with all active coefficients, pairing the
actual vector computes the cost exactly. -/
theorem countCost_eq_linear (a : Lattice n → ℝ) (c : Lattice n → ℕ)
    (ℓ : Ambient n →ₗ[ℝ] ℝ)
    (he : ∀ v ∈ «Σ».countSupport c, ℓ (embed n v) = a v) :
    «Σ».countCost a c = ℓ (embed n («Σ».countVector c)) := by
  simp only [countCost, countVector, map_sum, embed_int_smul, Int.cast_natCast,
    map_smul, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro v hv
  by_cases hc : 0 < c v
  · rw [he v (Finset.mem_filter.mpr ⟨hv, hc⟩)]
  · rw [Nat.eq_zero_of_not_pos hc]
    simp

/-- Large integral translations along all rays of a full smooth cone keep
the translated arbitrary lattice vector in that actual cone. -/
theorem exists_positive_basis_translation
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (v : Lattice n) :
    ∃ N : ℕ, 0 < N ∧
      embed n ((N : ℤ) • (∑ i, b i) + v) ∈
        latticeRayCone (Finset.univ.image b) := by
  let N : ℕ := 1 + ∑ i, (b.repr v i).natAbs
  refine ⟨N, by omega, ?_⟩
  rw [mem_latticeRayCone_basis_iff]
  refine ⟨?_, by simp⟩
  intro i
  rw [integralBasisReal_repr]
  have hsum : b.repr (∑ j, b j) i = 1 := by
    simp [map_sum, Finsupp.finsetSum_apply, Module.Basis.repr_self_apply,
      Finsupp.single_apply]
  have hcoord : b.repr ((N : ℤ) • (∑ j, b j) + v) i = (N : ℤ) + b.repr v i := by
    simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply,
      smul_eq_mul, hsum, mul_one]
  rw [hcoord]
  have hbound : (b.repr v i).natAbs ≤ ∑ j, (b.repr v j).natAbs :=
    Finset.single_le_sum (f := fun j : Fin n => (b.repr v j).natAbs)
      (fun j _ => Nat.zero_le _) (Finset.mem_univ i)
  have hboundZ : ((b.repr v i).natAbs : ℤ) ≤
      ((∑ j, (b.repr v j).natAbs : ℕ) : ℤ) := by exact_mod_cast hbound
  have hneg : -(b.repr v i) ≤ ((b.repr v i).natAbs : ℤ) := by
    simpa only [Int.natAbs_neg] using (Int.le_natAbs (a := -(b.repr v i)))
  have hcoord0 : (0 : ℤ) ≤ (N : ℤ) + b.repr v i := by
    dsimp [N]
    omega
  exact_mod_cast hcoord0

/-- Primitive nonnegativity forces the actual supporting inequalities of
the Cartier functional at a full smooth cone. -/
theorem full_cone_linear_support_of_primitive_nonneg
    (H : Lattice n → ℤ) (hH : «Σ».IsStrictSupport (fun v => (H v : ℝ)))
    (a : Lattice n → ℝ) (ha : ∀ R : «Σ».PrimitiveRelation, 0 ≤ R.degree a)
    (t : Finset (Lattice n)) (ht : t ∈ «Σ».cones)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (htb : t = Finset.univ.image b)
    (ℓ : Ambient n →ₗ[ℝ] ℝ) (hℓ : ∀ v ∈ t, ℓ (embed n v) = a v) :
    ∀ v ∈ «Σ».rays, ℓ (embed n v) ≤ a v := by
  intro v hv
  obtain ⟨N, hN, htranslate⟩ := exists_positive_basis_translation b v
  let cbase : Lattice n → ℕ := fun u => if u ∈ t then N else 0
  let c : Lattice n → ℕ := cbase + Pi.single v 1
  have htrays : t ⊆ «Σ».rays := fun u hu => «Σ».ray_mem_of_mem_cone ht hu
  have hsumt : (∑ u ∈ t, u) = ∑ i, b i := by
    rw [htb, Finset.sum_image]
    exact fun i _ j _ hij => b.injective hij
  have hbase : «Σ».countVector cbase = (N : ℤ) • ∑ i, b i := by
    rw [«Σ».countVector_indicator t htrays N, hsumt]
  have hcvec : «Σ».countVector c = «Σ».countVector cbase + v := by
    rw [countVector_add, «Σ».countVector_single hv]
  have hccost : «Σ».countCost a c = «Σ».countCost a cbase + a v := by
    rw [countCost_add, «Σ».countCost_single a hv]
  obtain ⟨d, hdvec, hdcone, hdcost⟩ := «Σ».exists_cone_reduction H hH a ha c
  have hdmem : embed n («Σ».countVector d) ∈ latticeRayCone t := by
    rw [hdvec, hcvec, hbase, htb]
    exact htranslate
  have hdsub := «Σ».countSupport_subset_of_vector_mem d hdcone ht hdmem
  have hdlinear := «Σ».countCost_eq_linear a d ℓ (fun u hu => hℓ u (hdsub hu))
  have hbaselinear : «Σ».countCost a cbase = ℓ (embed n («Σ».countVector cbase)) := by
    apply «Σ».countCost_eq_linear a cbase ℓ
    intro u hu
    have hpos := (Finset.mem_filter.mp hu).2
    have hut : u ∈ t := by
      by_contra h
      simp only [cbase, if_neg h, lt_self_iff_false] at hpos
    exact hℓ u hut
  rw [hdlinear, hdvec, hcvec, map_add, map_add, hccost, hbaselinear] at hdcost
  linarith

/-- The full primitive-relation criterion, derived from actual support data
and terminating reductions. Purity is independently supplied by the literal
normal fan construction and is preserved by the proved star subdivision. -/
theorem isNef_iff_primitive_nonneg (hpure : «Σ».IsPure)
    (H : Lattice n → ℤ) (hH : «Σ».IsStrictSupport (fun v => (H v : ℝ)))
    (a : Lattice n → ℝ) :
    «Σ».IsNef a ↔ ∀ R : «Σ».PrimitiveRelation, 0 ≤ R.degree a := by
  constructor
  · intro ha R
    exact R.degree_nonneg_of_nef ha
  · intro ha s hs
    obtain ⟨t, ht, hst, hdim⟩ := hpure s hs
    obtain ⟨b, htb⟩ := «Σ».full_cone_basis ht hdim
    let ℓ : Ambient n →ₗ[ℝ] ℝ :=
      (integralBasisReal b).constr ℝ (fun i => a (b i))
    have hℓ : ∀ v ∈ t, ℓ (embed n v) = a v := by
      intro v hv
      rw [htb] at hv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
      rw [← integralBasisReal_apply]
      exact (integralBasisReal b).constr_basis ℝ _ i
    refine ⟨ℓ, fun v hv => hℓ v (hst hv), ?_⟩
    exact «Σ».full_cone_linear_support_of_primitive_nonneg H hH a ha t ht b htb ℓ hℓ

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricNefCriterion
-- END ORIGINAL PaperVerification.ToricNefCriterion


-- BEGIN ORIGINAL PaperVerification.ToricPrimitiveFinite
section Source_ToricPrimitiveFinite

-- original header: module

-- original header: public import PaperVerification.ToricNefCriterion

-- original header: @[expose] public section

/-!
# A genuine finite family of all primitive relation vectors

PrimitiveRelation allows arbitrary coefficient values away from its focus,
so that structure itself need not be a finite type. The displayed relation
vector, however, is uniquely determined by its positive primitive collection.
This is proved by integral basis coordinates before taking a finite family.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} {«Σ» : SmoothCompleteFan n}

namespace PrimitiveRelation

variable (R S : «Σ».PrimitiveRelation)

/-- Positive integral coefficients in the actual smooth focus cone are
uniquely determined by the lattice vector. -/
theorem coefficient_eq_of_positive_eq (hpos : R.positive = S.positive)
    {v : Lattice n} (hv : v ∈ R.negative) : R.coefficient v = S.coefficient v := by
  have hneg := R.negative_unique S hpos
  obtain ⟨b, I, hI⟩ := «Σ».smooth R.negative R.negative_cone
  obtain ⟨i, hi, hiv⟩ := Finset.mem_image.mp (hI ▸ hv)
  subst v
  have hcoord (c : Lattice n → ℕ) :
      b.repr (∑ v ∈ I.image b, (c v : ℤ) • v) i = (c (b i) : ℤ) := by
    rw [Finset.sum_image]
    · simp only [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
        Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul, mul_ite,
        mul_one, mul_zero]
      simp [hi]
    · exact fun j _ k _ hjk => b.injective hjk
  have hR : b.repr (∑ v ∈ R.positive, v) i = (R.coefficient (b i) : ℤ) := by
    rw [R.equation, hI]
    exact hcoord R.coefficient
  have hS : b.repr (∑ v ∈ S.positive, v) i = (S.coefficient (b i) : ℤ) := by
    rw [S.equation, ← hneg, hI]
    exact hcoord S.coefficient
  rw [hpos] at hR
  exact_mod_cast hR.symm.trans hS

/-- The actual relation vector is unique, regardless of unused coefficient
values outside its focus cone. -/
theorem vector_eq_of_positive_eq (hpos : R.positive = S.positive) :
    R.vector = S.vector := by
  have hneg := R.negative_unique S hpos
  funext v
  by_cases hv : (v : Lattice n) ∈ R.negative
  · have hvS : (v : Lattice n) ∈ S.negative := hneg ▸ hv
    have hc := R.coefficient_eq_of_positive_eq S hpos hv
    simp only [vector, hpos, if_pos hv, if_pos hvS, hc]
  · have hvS : (v : Lattice n) ∉ S.negative := by simpa only [← hneg] using hv
    simp only [vector, hpos, if_neg hv, if_neg hvS]

end PrimitiveRelation

variable («Σ»)

/-- All genuine primitive collections form a subset of the finite ray powerset. -/
def primitiveCollections : Finset (Finset (Lattice n)) :=
  «Σ».rays.powerset.filter «Σ».IsPrimitiveCollection

theorem mem_primitiveCollections (Q : Finset (Lattice n)) :
    Q ∈ «Σ».primitiveCollections ↔ «Σ».IsPrimitiveCollection Q := by
  simp only [primitiveCollections, Finset.mem_filter, Finset.mem_powerset]
  exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩

/-- One actual primitive relation for each primitive collection. -/
def canonicalPrimitive (Q : «Σ».primitiveCollections) : «Σ».PrimitiveRelation :=
  Classical.choose («Σ».exists_primitiveRelation
    ((«Σ».mem_primitiveCollections Q).mp Q.property))

theorem canonicalPrimitive_positive (Q : «Σ».primitiveCollections) :
    («Σ».canonicalPrimitive Q).positive = (Q : Finset (Lattice n)) :=
  Classical.choose_spec («Σ».exists_primitiveRelation
    ((«Σ».mem_primitiveCollections Q).mp Q.property))

/-- This finite family contains every primitive relation vector exactly up
to the proved equality, rather than by a bounded-coefficient restriction. -/
theorem exists_canonicalPrimitive_vector (R : «Σ».PrimitiveRelation) :
    ∃ Q : «Σ».primitiveCollections, R.vector = («Σ».canonicalPrimitive Q).vector := by
  let Q : «Σ».primitiveCollections :=
    ⟨R.positive, («Σ».mem_primitiveCollections R.positive).mpr R.primitive⟩
  refine ⟨Q, R.vector_eq_of_positive_eq («Σ».canonicalPrimitive Q) ?_⟩
  exact («Σ».canonicalPrimitive_positive Q).symm

/-- The finite primitive inequality family is equivalent to the unrestricted
primitive criterion and hence to genuine convex support. -/
theorem isNef_iff_canonicalPrimitive_nonneg (hpure : «Σ».IsPure)
    (H : Lattice n → ℤ) (hH : «Σ».IsStrictSupport (fun v => (H v : ℝ)))
    (a : Lattice n → ℝ) :
    «Σ».IsNef a ↔ ∀ Q : «Σ».primitiveCollections,
      0 ≤ («Σ».canonicalPrimitive Q).degree a := by
  rw [«Σ».isNef_iff_primitive_nonneg hpure H hH a]
  constructor
  · intro ha Q
    exact ha («Σ».canonicalPrimitive Q)
  · intro ha R
    obtain ⟨Q, hQ⟩ := «Σ».exists_canonicalPrimitive_vector R
    rw [← R.vector_pairing, hQ, («Σ».canonicalPrimitive Q).vector_pairing]
    exact ha Q

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricPrimitiveFinite
-- END ORIGINAL PaperVerification.ToricPrimitiveFinite


-- BEGIN ORIGINAL PaperVerification.ToricFiniteDuality
section Source_ToricFiniteDuality

-- original header: module

-- original header: public import PaperVerification.ToricPrimitiveFinite
-- original header: public import Mathlib.Analysis.LocallyConvex.Separation
-- original header: public import Mathlib.Analysis.Convex.Topology
-- original header: public import Mathlib.LinearAlgebra.Dual.Lemmas

-- original header: @[expose] public section

/-!
# Finite cone duality from a strictly positive normalizing functional

The finite generating vectors admit a common strictly positive functional.
Their normalized convex hull is compact. Separating a normalized candidate
from this finite hull proves the relevant dual-cone theorem directly from
Hahn--Banach, including the zero and empty-family cases.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators Classical

section FiniteDuality

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [Finite ι]
    (v : ι → E) (H : E →ₗ[ℝ] ℝ) (hH : ∀ i, 0 < H (v i))

include hH

/-- In the dual of a finite inequality family, the zero slice of a strictly
positive normalizing functional consists only of the zero vector. -/
theorem finite_dual_zero_of_pairing_zero (c : E)
    (hc : ∀ f : E →ₗ[ℝ] ℝ, (∀ i, 0 ≤ f (v i)) → 0 ≤ f c)
    (hzero : H c = 0) : c = 0 := by
  apply (Module.forall_dual_apply_eq_zero_iff ℝ c).mp
  intro f
  obtain ⟨M, hM⟩ := (Set.finite_range (fun i => |f (v i)| / H (v i))).bddAbove
  have hbound (i : ι) : |f (v i)| ≤ M * H (v i) :=
    (div_le_iff₀ (hH i)).mp (hM (Set.mem_range_self i))
  have hplus : ∀ i, 0 ≤ (M • H + f) (v i) := by
    intro i
    have hb := hbound i
    have hf := neg_abs_le (f (v i))
    change 0 ≤ M * H (v i) + f (v i)
    linarith
  have hminus : ∀ i, 0 ≤ (M • H - f) (v i) := by
    intro i
    have hb := hbound i
    have hf := le_abs_self (f (v i))
    change 0 ≤ M * H (v i) - f (v i)
    linarith
  have hp := hc (M • H + f) hplus
  have hm := hc (M • H - f) hminus
  change 0 ≤ M * H c + f c at hp
  change 0 ≤ M * H c - f c at hm
  rw [hzero, mul_zero, zero_add] at hp
  rw [hzero, mul_zero, zero_sub] at hm
  linarith

theorem finite_dual_pairing_pos (c : E)
    (hc : ∀ f : E →ₗ[ℝ] ℝ, (∀ i, 0 ≤ f (v i)) → 0 ≤ f c)
    (hne : c ≠ 0) : 0 < H c := by
  have hnonneg := hc H (fun i => (hH i).le)
  exact lt_of_le_of_ne hnonneg (fun he =>
    hne (finite_dual_zero_of_pairing_zero v H hH c hc he.symm))

/-- Every nonzero point in the dual of the finite inequalities normalizes
into the actual convex hull of the normalized generating vectors. -/
theorem finite_dual_normalized_mem_convexHull (c : E)
    (hc : ∀ f : E →ₗ[ℝ] ℝ, (∀ i, 0 ≤ f (v i)) → 0 ≤ f c)
    (hne : c ≠ 0) :
    (H c)⁻¹ • c ∈ convexHull ℝ (Set.range (fun i => (H (v i))⁻¹ • v i)) := by
  have hcp := finite_dual_pairing_pos v H hH c hc hne
  by_contra hnot
  obtain ⟨f, t, hct, ht⟩ := geometric_hahn_banach_point_closed
    (convex_convexHull ℝ (Set.range (fun i => (H (v i))⁻¹ • v i)))
    ((Set.finite_range (fun i => (H (v i))⁻¹ • v i)).isClosed_convexHull ℝ) hnot
  have hgenerators : ∀ i, 0 ≤ (f.toLinearMap - t • H) (v i) := by
    intro i
    have hi := ht ((H (v i))⁻¹ • v i)
      (subset_convexHull ℝ _ (Set.mem_range_self i))
    have he : f ((H (v i))⁻¹ • v i) = f (v i) / H (v i) := by
      simp only [map_smul, smul_eq_mul, div_eq_mul_inv, mul_comm]
    rw [he] at hi
    change 0 ≤ f (v i) - t * H (v i)
    exact (sub_pos.mpr ((lt_div_iff₀ (hH i)).mp hi)).le
  have hdual := hc (f.toLinearMap - t • H) hgenerators
  have he : f ((H c)⁻¹ • c) = f c / H c := by
    simp only [map_smul, smul_eq_mul, div_eq_mul_inv, mul_comm]
  rw [he] at hct
  have hlt := (div_lt_iff₀ hcp).mp hct
  change 0 ≤ f c - t * H c at hdual
  linarith

/-- The needed finite conic bipolar theorem, with the strictly positive
normalizing functional explicitly justified by the mathematical application. -/
theorem mem_finite_cone_of_nonnegative_on_dual (c : E)
    (hc : ∀ f : E →ₗ[ℝ] ℝ, (∀ i, 0 ≤ f (v i)) → 0 ≤ f c) :
    c ∈ PointedCone.hull ℝ (Set.range v) := by
  by_cases hzero : c = 0
  · subst c
    exact Submodule.zero_mem _
  · let C := PointedCone.hull ℝ (Set.range v)
    have hnorm := finite_dual_normalized_mem_convexHull v H hH c hc hzero
    have hsub : convexHull ℝ (Set.range (fun i => (H (v i))⁻¹ • v i)) ⊆ C := by
      apply convexHull_min
      · rintro _ ⟨i, rfl⟩
        exact PointedCone.smul_mem C (inv_nonneg.mpr (hH i).le)
          (PointedCone.subset_hull (Set.mem_range_self i))
      · exact C.convex
    have hcp := finite_dual_pairing_pos v H hH c hc hzero
    have hscaled := PointedCone.smul_mem C hcp.le (hsub hnorm)
    simpa only [smul_smul, mul_inv_cancel₀ (ne_of_gt hcp), one_smul] using hscaled

end FiniteDuality

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

/-- Coefficients representing an arbitrary linear functional on the finite
ray coefficient space. Values away from actual rays are irrelevant and zero. -/
def functionalCoefficients (f : «Σ».RaySpace →ₗ[ℝ] ℝ) (v : Lattice n) : ℝ :=
  if hv : v ∈ «Σ».rays then f (Pi.single ⟨v, hv⟩ 1) else 0

theorem rayPairing_functionalCoefficients (f : «Σ».RaySpace →ₗ[ℝ] ℝ) (c : «Σ».RaySpace) :
    «Σ».rayPairing («Σ».functionalCoefficients f) c = f c := by
  have he := congrArg f ((Pi.basisFun ℝ «Σ».rays).sum_repr c)
  simpa [rayPairing, functionalCoefficients, map_sum, map_smul, smul_eq_mul,
    Pi.basisFun_repr, Pi.basisFun_apply] using he

/-- Nefness detects precisely the nonnegative linear functionals on the
finite canonical primitive family. -/
theorem isNef_functionalCoefficients_iff (hpure : «Σ».IsPure)
    (H : Lattice n → ℤ) (hH : «Σ».IsStrictSupport (fun v => (H v : ℝ)))
    (f : «Σ».RaySpace →ₗ[ℝ] ℝ) :
    «Σ».IsNef («Σ».functionalCoefficients f) ↔
      ∀ Q : «Σ».primitiveCollections, 0 ≤ f («Σ».canonicalPrimitive Q).vector := by
  rw [«Σ».isNef_iff_canonicalPrimitive_nonneg hpure H hH]
  apply forall_congr'
  intro Q
  rw [← («Σ».canonicalPrimitive Q).vector_pairing,
    «Σ».rayPairing_functionalCoefficients]

/-- An effective relation is nonnegative on every linear functional
nonnegative on the actual finite primitive family. -/
theorem effective_nonnegative_on_finite_dual (hpure : «Σ».IsPure)
    (H : Lattice n → ℤ) (hH : «Σ».IsStrictSupport (fun v => (H v : ℝ)))
    {c : «Σ».RaySpace} (hc : c ∈ «Σ».effectiveCone) :
    ∀ f : «Σ».RaySpace →ₗ[ℝ] ℝ,
      (∀ Q : «Σ».primitiveCollections, 0 ≤ f («Σ».canonicalPrimitive Q).vector) → 0 ≤ f c := by
  intro f hf
  have hnef := («Σ».isNef_functionalCoefficients_iff hpure H hH f).mpr hf
  have h := hc.2 («Σ».functionalCoefficients f) hnef
  rwa [«Σ».rayPairing_functionalCoefficients] at h

/-- The genuine dual effective cone is generated by the finite primitive
relation family. This is proved, not inserted into a fan or nef definition. -/
theorem effectiveCone_eq_primitive_hull (hpure : «Σ».IsPure)
    (H : Lattice n → ℤ) (hH : «Σ».IsStrictSupport (fun v => (H v : ℝ))) :
    «Σ».effectiveCone = PointedCone.hull ℝ
      (Set.range (fun Q : «Σ».primitiveCollections => («Σ».canonicalPrimitive Q).vector)) := by
  apply le_antisymm
  · intro c hc
    exact mem_finite_cone_of_nonnegative_on_dual
      (fun Q : «Σ».primitiveCollections => («Σ».canonicalPrimitive Q).vector)
      («Σ».rayPairing (fun v => (H v : ℝ)))
      (fun Q => by
        rw [(«Σ».canonicalPrimitive Q).vector_pairing]
        exact («Σ».canonicalPrimitive Q).degree_pos_of_strictSupport hH)
      c («Σ».effective_nonnegative_on_finite_dual hpure H hH hc)
  · apply Submodule.span_le.mpr
    rintro _ ⟨Q, rfl⟩
    exact («Σ».canonicalPrimitive Q).vector_effective

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricFiniteDuality
-- END ORIGINAL PaperVerification.ToricFiniteDuality


-- BEGIN ORIGINAL PaperVerification.ToricExtremalCriterion
section Source_ToricExtremalCriterion

-- original header: module

-- original header: public import PaperVerification.ToricFiniteDuality
-- original header: public import PaperVerification.ToricVertexCone

-- original header: @[expose] public section

/-!
# Extremal primitive rays detect all nef inequalities

The compact normalized primitive hull has genuine extreme points. Each such
point is one of the normalized primitive vectors, and its nonnegative ray is
a Mathlib face of the actual dual effective cone. Taking the convex hull of
these extreme points proves the criterion using only extremal primitive
relations. Together with the proved replacement theorem this gives the
contractible-relation corner criterion.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators Classical
open PaperVerification.ToricVertexCone

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

def normalizedPrimitive (H : Lattice n → ℤ) (Q : «Σ».primitiveCollections) : «Σ».RaySpace :=
  ((«Σ».canonicalPrimitive Q).degree (fun v => (H v : ℝ)))⁻¹ •
    («Σ».canonicalPrimitive Q).vector

def primitiveBase (H : Lattice n → ℤ) : Set «Σ».RaySpace :=
  convexHull ℝ (Set.range («Σ».normalizedPrimitive H))

theorem effective_height_pos (hpure : «Σ».IsPure)
    (H : Lattice n → ℤ) (hH : «Σ».IsStrictSupport (fun v => (H v : ℝ)))
    {c : «Σ».RaySpace} (hc : c ∈ «Σ».effectiveCone) (hne : c ≠ 0) :
    0 < «Σ».rayPairing (fun v => (H v : ℝ)) c := by
  exact finite_dual_pairing_pos
    (fun Q : «Σ».primitiveCollections => («Σ».canonicalPrimitive Q).vector)
    («Σ».rayPairing (fun v => (H v : ℝ)))
    (fun Q => by
      rw [(«Σ».canonicalPrimitive Q).vector_pairing]
      exact («Σ».canonicalPrimitive Q).degree_pos_of_strictSupport hH)
    c («Σ».effective_nonnegative_on_finite_dual hpure H hH hc) hne

theorem effective_normalized_mem_base (hpure : «Σ».IsPure)
    (H : Lattice n → ℤ) (hH : «Σ».IsStrictSupport (fun v => (H v : ℝ)))
    {c : «Σ».RaySpace} (hc : c ∈ «Σ».effectiveCone) (hne : c ≠ 0) :
    («Σ».rayPairing (fun v => (H v : ℝ)) c)⁻¹ • c ∈ «Σ».primitiveBase H := by
  have h := finite_dual_normalized_mem_convexHull
    (fun Q : «Σ».primitiveCollections => («Σ».canonicalPrimitive Q).vector)
    («Σ».rayPairing (fun v => (H v : ℝ)))
    (fun Q => by rw [(«Σ».canonicalPrimitive Q).vector_pairing]
                 exact («Σ».canonicalPrimitive Q).degree_pos_of_strictSupport hH)
    c («Σ».effective_nonnegative_on_finite_dual hpure H hH hc) hne
  change («Σ».rayPairing (fun v => (H v : ℝ)) c)⁻¹ • c ∈
    convexHull ℝ (Set.range (fun Q : «Σ».primitiveCollections =>
      ((«Σ».canonicalPrimitive Q).degree (fun v => (H v : ℝ)))⁻¹ •
        («Σ».canonicalPrimitive Q).vector))
  simpa only [PrimitiveRelation.vector_pairing] using h

/-- A genuine extreme point of the normalized base gives an actual
extremal ray of the dual effective cone. -/
theorem primitive_extremal_of_normalized_extreme (hpure : «Σ».IsPure)
    (H : Lattice n → ℤ) (hH : «Σ».IsStrictSupport (fun v => (H v : ℝ)))
    (R : «Σ».PrimitiveRelation)
    (hR : (R.degree (fun v => (H v : ℝ)))⁻¹ • R.vector ∈
      («Σ».primitiveBase H).extremePoints ℝ) : R.IsExtremal := by
  let F := «Σ».rayPairing (fun v => (H v : ℝ))
  have hFr : 0 < F R.vector := by
    rw [show F R.vector = R.degree (fun v => (H v : ℝ)) from R.vector_pairing _]
    exact R.degree_pos_of_strictSupport hH
  have hR' : (F R.vector)⁻¹ • R.vector ∈ («Σ».primitiveBase H).extremePoints ℝ := by
    simpa only [F, R.vector_pairing] using hR
  refine ⟨Submodule.span_le.mpr ?_, ?_⟩
  · rintro _ rfl
    exact R.vector_effective
  · intro c d α hc hd hα hsum
    by_cases hc0 : c = 0
    · subst c
      exact Submodule.zero_mem _
    obtain ⟨t, ht, he⟩ := PointedCone.mem_hull_singleton.mp hsum
    by_cases hd0 : d = 0
    · apply PointedCone.mem_hull_singleton.mpr
      refine ⟨α⁻¹ * t, mul_nonneg (inv_nonneg.mpr hα.le) ht, ?_⟩
      have hh := congrArg (fun z : «Σ».RaySpace => α⁻¹ • z) he
      simpa only [hd0, add_zero, smul_smul, inv_mul_cancel₀ (ne_of_gt hα), one_smul] using hh
    have hFc : 0 < F c := «Σ».effective_height_pos hpure H hH hc hc0
    have hFd : 0 < F d := «Σ».effective_height_pos hpure H hH hd hd0
    have hcn := «Σ».effective_normalized_mem_base hpure H hH hc hc0
    have hdn := «Σ».effective_normalized_mem_base hpure H hH hd hd0
    have hFt : t * F R.vector = α * F c + F d := by
      have hh := congrArg F he
      simpa only [map_add, map_smul, smul_eq_mul] using hh
    let D : ℝ := α * F c + F d
    have hD : 0 < D := add_pos (mul_pos hα hFc) hFd
    have htpos : 0 < t := by nlinarith
    let p : ℝ := α * F c / D
    let q : ℝ := F d / D
    have hp : 0 < p := div_pos (mul_pos hα hFc) hD
    have hq : 0 < q := div_pos hFd hD
    have hpq : p + q = 1 := by
      dsimp [p, q]
      rw [← add_div]
      exact div_self (ne_of_gt hD)
    have hpc : p * (F c)⁻¹ = D⁻¹ * α := by
      dsimp [p]
      field_simp
    have hqd : q * (F d)⁻¹ = D⁻¹ := by
      dsimp [q]
      field_simp
    have hDr : D⁻¹ * t = (F R.vector)⁻¹ := by
      rw [show D = t * F R.vector from hFt.symm]
      field_simp
    have hcombo : p • ((F c)⁻¹ • c) + q • ((F d)⁻¹ • d) =
        (F R.vector)⁻¹ • R.vector := by
      calc
        p • ((F c)⁻¹ • c) + q • ((F d)⁻¹ • d) = D⁻¹ • (α • c + d) := by
          simp only [smul_smul, smul_add, hpc, hqd]
        _ = D⁻¹ • (t • R.vector) := by rw [← he]
        _ = (F R.vector)⁻¹ • R.vector := by rw [smul_smul, hDr]
    have hnorm : (F c)⁻¹ • c = (F R.vector)⁻¹ • R.vector :=
      hR'.2 hcn hdn ⟨p, q, hp, hq, hpq, hcombo⟩
    apply PointedCone.mem_hull_singleton.mpr
    refine ⟨F c * (F R.vector)⁻¹,
      mul_nonneg hFc.le (inv_nonneg.mpr hFr.le), ?_⟩
    have hh := congrArg (fun z : «Σ».RaySpace => F c • z) hnorm
    simpa only [smul_smul, mul_inv_cancel₀ (ne_of_gt hFc), one_smul] using hh.symm

/-- The convex hull of the actual extreme points is the whole normalized
primitive base, including the empty-base case. -/
theorem primitiveBase_hull_extremePoints (H : Lattice n → ℤ) :
    convexHull ℝ ((«Σ».primitiveBase H).extremePoints ℝ) = «Σ».primitiveBase H := by
  let s := Finset.univ.image («Σ».normalizedPrimitive H)
  have he : (s : Set «Σ».RaySpace) = Set.range («Σ».normalizedPrimitive H) := by
    simp [s]
  have h := finite_hull_eq_hull_extremePoints s
  simpa only [he, primitiveBase] using h

/-- All actual nef inequalities are detected by primitive relations spanning
genuine extremal effective rays. -/
theorem isNef_iff_extremal_primitive_nonneg (hpure : «Σ».IsPure)
    (H : Lattice n → ℤ) (hH : «Σ».IsStrictSupport (fun v => (H v : ℝ)))
    (a : Lattice n → ℝ) :
    «Σ».IsNef a ↔ ∀ R : «Σ».PrimitiveRelation, R.IsExtremal → 0 ≤ R.degree a := by
  constructor
  · intro ha R hR
    exact R.degree_nonneg_of_nef ha
  · intro ha
    apply («Σ».isNef_iff_canonicalPrimitive_nonneg hpure H hH a).mpr
    intro Q
    let R := «Σ».canonicalPrimitive Q
    let f := «Σ».rayPairing a
    have hnonneg : ∀ x ∈ («Σ».primitiveBase H).extremePoints ℝ, 0 ≤ f x := by
      intro x hx
      obtain ⟨S, hS⟩ := extremePoints_convexHull_subset hx
      subst x
      have hsext := «Σ».primitive_extremal_of_normalized_extreme hpure H hH
        («Σ».canonicalPrimitive S) hx
      have hdeg := ha («Σ».canonicalPrimitive S) hsext
      have hheight := («Σ».canonicalPrimitive S).degree_pos_of_strictSupport hH
      change 0 ≤ f ((«Σ».normalizedPrimitive H) S)
      simp only [normalizedPrimitive, map_smul, smul_eq_mul,
        PrimitiveRelation.vector_pairing, f]
      exact mul_nonneg (inv_nonneg.mpr hheight.le) hdeg
    have hmem : «Σ».normalizedPrimitive H Q ∈ «Σ».primitiveBase H :=
      subset_convexHull ℝ _ (Set.mem_range_self Q)
    have hconv : Convex ℝ {x : «Σ».RaySpace | 0 ≤ f x} :=
      (convex_Ici (0 : ℝ)).linear_preimage f
    have hbase : «Σ».primitiveBase H ⊆ {x : «Σ».RaySpace | 0 ≤ f x} := by
      rw [← «Σ».primitiveBase_hull_extremePoints H]
      exact convexHull_min hnonneg hconv
    have hvalue := hbase hmem
    have hheight := R.degree_pos_of_strictSupport hH
    change 0 ≤ f («Σ».normalizedPrimitive H Q) at hvalue
    have hvalue' : 0 ≤ (R.degree (fun v => (H v : ℝ)))⁻¹ * R.degree a := by
      simpa only [normalizedPrimitive, map_smul, smul_eq_mul, f,
        PrimitiveRelation.vector_pairing, R] using hvalue
    exact nonneg_of_mul_nonneg_right hvalue' (inv_pos.mpr hheight)

/-- The numerical contractible-relation bound forces genuine nefness after
every selected cone-divisor subtraction. This is the support-function core
of the corner-box criterion. -/
theorem nef_sub_cone_selection_of_contractible_degrees (hpure : «Σ».IsPure)
    (H : Lattice n → ℤ) (hH : «Σ».IsStrictSupport (fun v => (H v : ℝ)))
    (a : Lattice n → ℝ) (side : ℝ) (hside : 0 ≤ side)
    (hdegree : ∀ R : «Σ».PrimitiveRelation, R.IsCombinatoriallyContractible →
      side * R.fiberDimension ≤ R.degree a)
    {s t : Finset (Lattice n)} (hs : s ∈ «Σ».cones) (ht : t ⊆ s) :
    «Σ».IsNef (a - side • (fun v => if v ∈ t then 1 else 0)) := by
  apply («Σ».isNef_iff_extremal_primitive_nonneg hpure H hH _).mpr
  intro R hR
  exact R.degree_sub_corner_selection_nonneg hs ht a side hside
    (hdegree R (R.combinatoriallyContractible_of_extremal hR))

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
end Source_ToricExtremalCriterion
-- END ORIGINAL PaperVerification.ToricExtremalCriterion


-- BEGIN ORIGINAL PaperVerification.ToricPolytopeSupport
section Source_ToricPolytopeSupport

-- original header: module
-- original header: public import PaperVerification.ToricNefCone
-- original header: public import PaperVerification.ToricNormalFan
-- original header: public import Mathlib.LinearAlgebra.Matrix.Dual
-- original header: @[expose] public section

/-!
# Integral strict support from a genuine lattice polytope

The support coefficients are negatives of actual minima over the polytope.
Every minimum occurs at a genuine lattice vertex, so those coefficients are
integers. Equality of the actual normal fans then supplies strict support on
every cone, including its lower-dimensional cones.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace LatticePolytope

variable {n : ℕ} (P : LatticePolytope n)

/-- The negative minimum of a primitive integral linear functional is an
integer, and its equality locus is its actual normal-cone incidence locus. -/
theorem exists_integral_support_value (u : Lattice n) :
    ∃ a : ℤ, ∀ x ∈ P.carrier,
      -(dotProductEquiv ℝ (Fin n) (embed n u)) x ≤ (a : ℝ) ∧
      (-(dotProductEquiv ℝ (Fin n) (embed n u)) x = (a : ℝ) ↔
        embed n u ∈ P.normalCone x) := by
  let f : Ambient n →ₗ[ℝ] ℝ := dotProductEquiv ℝ (Fin n) (embed n u)
  obtain ⟨v, hv, hmin⟩ := P.exists_minimizing_vertex f
  obtain ⟨z, hz, hze⟩ := P.extreme_integral hv
  let a : ℤ := -(∑ i, u i * z i)
  have ha : (a : ℝ) = -f v := by
    rw [← hze]
    simp [a, f, dotProductEquiv, dotProduct, embed]
  refine ⟨a, ?_⟩
  intro x hx
  have hnormal : embed n u ∈ P.normalCone x ↔ ∀ y ∈ P.carrier, f x ≤ f y := by
    change (∀ y ∈ P.carrier, 0 ≤ f (y - x)) ↔ _
    simp only [map_sub, sub_nonneg]
  constructor
  · rw [ha]
    exact neg_le_neg (hmin x hx)
  · rw [ha, neg_inj, hnormal]
    constructor
    · intro he y hy
      rw [he]
      exact hmin y hy
    · intro he
      exact le_antisymm (he v hv.1) (hmin x hx)

/-- Canonical chosen integral support coefficients, defined by actual minima. -/
def integralSupport (u : Lattice n) : ℤ :=
  Classical.choose (P.exists_integral_support_value u)

theorem integralSupport_spec (u : Lattice n) (x : Ambient n) (hx : x ∈ P.carrier) :
    -(dotProductEquiv ℝ (Fin n) (embed n u)) x ≤ (P.integralSupport u : ℝ) ∧
    (-(dotProductEquiv ℝ (Fin n) (embed n u)) x = (P.integralSupport u : ℝ) ↔
      embed n u ∈ P.normalCone x) :=
  Classical.choose_spec (P.exists_integral_support_value u) x hx

/-- The normal fan of an actual lattice polytope has integral strict convex
support. This conclusion follows from literal equality of cone sets. -/
theorem integralSupport_isStrictSupport («Σ» : SmoothCompleteFan n)
    (hfan : «Σ».realCones = P.normalFan) :
    «Σ».IsStrictSupport (fun u => (P.integralSupport u : ℝ)) := by
  intro s hs
  have hmem : (latticeRayCone s : Set (Ambient n)) ∈ «Σ».realCones := ⟨s, hs, rfl⟩
  rw [hfan] at hmem
  obtain ⟨x, hx, hcone⟩ := hmem
  let ℓ : Ambient n →ₗ[ℝ] ℝ := -(dotProductEquiv ℝ (Fin n) x)
  have hpair (u : Lattice n) :
      ℓ (embed n u) = -(dotProductEquiv ℝ (Fin n) (embed n u)) x := by
    simp only [ℓ, LinearMap.neg_apply]
    congr 1
    change (∑ i, x i * embed n u i) = ∑ i, embed n u i * x i
    exact Finset.sum_congr rfl (fun i _ => mul_comm _ _)
  refine ⟨ℓ, ?_, ?_⟩
  · intro u hu
    rw [hpair]
    apply (P.integralSupport_spec u x hx).2.mpr
    rw [← hcone]
    exact latticeRayCone_generator s hu
  · intro u hu hus
    rw [hpair]
    apply lt_of_le_of_ne (P.integralSupport_spec u x hx).1
    intro he
    have hnormal := (P.integralSupport_spec u x hx).2.mp he
    rw [← hcone] at hnormal
    exact hus ((«Σ».ray_mem_cone_iff hs hu).mp hnormal)

end LatticePolytope

end PaperVerification.ToricGeometry
end
end Source_ToricPolytopeSupport
-- END ORIGINAL PaperVerification.ToricPolytopeSupport


-- BEGIN ORIGINAL PaperVerification.ToricStarBoxCoordinates
section Source_ToricStarBoxCoordinates

-- original header: module
-- original header: public import PaperVerification.ToricIntegralBasis
-- original header: public import Mathlib.LinearAlgebra.Transvection.Basic
-- original header: public import Mathlib.Tactic.Abel
-- original header: public import Mathlib.Tactic.Linarith
-- original header: public import Mathlib.Tactic.Ring
-- original header: @[expose] public section
/-!
# Integral basis changes and normal heights in a star-subdivision chart

The basis in equation (10) is constructed as an integral transvection.
The height formula and the displacement bounds are then consequences of
its actual vectors, including all tangent directions left unchanged.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

section BasisShear

variable {R E ι : Type*} [CommRing R] [AddCommGroup E] [Module R E]
    [Fintype ι] [DecidableEq ι]

/-- The normal-coordinate functional of the integral shear. -/
def starShearFunctional (b : Module.Basis ι R E) (I : Finset ι) (j : ι) :
    E →ₗ[R] R := -∑ i ∈ I.erase j, b.coord i

theorem starShearFunctional_basis (b : Module.Basis ι R E)
    (I : Finset ι) (j k : ι) :
    starShearFunctional b I j (b k) = if k ∈ I.erase j then -1 else 0 := by
  simp [starShearFunctional, Module.Basis.coord_apply, Module.Basis.repr_self_apply,
    Finsupp.single_apply]
  split_ifs <;> simp

theorem starShearFunctional_pivot (b : Module.Basis ι R E)
    (I : Finset ι) (j : ι) : starShearFunctional b I j (b j) = 0 := by
  simp [starShearFunctional_basis]

/-- The genuine integral basis whose normal vectors are `e_j` and
`e_l-e_j`, with every other direction unchanged. -/
def starShearBasis (b : Module.Basis ι R E) (I : Finset ι) (j : ι) :
    Module.Basis ι R E :=
  b.map (LinearEquiv.transvection (starShearFunctional_pivot b I j))

theorem starShearBasis_apply (b : Module.Basis ι R E)
    (I : Finset ι) (j k : ι) :
    starShearBasis b I j k = if k ∈ I.erase j then b k - b j else b k := by
  simp only [starShearBasis, Module.Basis.map_apply,
    LinearEquiv.transvection.apply, starShearFunctional_basis]
  split_ifs <;> simp [sub_eq_add_neg]

@[simp] theorem starShearBasis_pivot (b : Module.Basis ι R E)
    (I : Finset ι) (j : ι) : starShearBasis b I j j = b j := by
  simp [starShearBasis_apply]

theorem starShearBasis_tangent (b : Module.Basis ι R E)
    (I : Finset ι) (j k : ι) (hk : k ∉ I) :
    starShearBasis b I j k = b k := by
  rw [starShearBasis_apply, if_neg (fun h => hk (Finset.mem_of_mem_erase h))]

/-- The complete box-coordinate sum after the shear. -/
theorem sum_smul_starShearBasis (b : Module.Basis ι R E)
    (I : Finset ι) (j : ι) (a : ι → R) :
    (∑ k, a k • starShearBasis b I j k) =
      (∑ k, a k • b k) - (∑ k ∈ I.erase j, a k) • b j := by
  calc
    (∑ k, a k • starShearBasis b I j k) =
        ∑ k, (a k • b k - (if k ∈ I.erase j then a k else 0) • b j) := by
      apply Finset.sum_congr rfl
      intro k _
      rw [starShearBasis_apply]
      split_ifs <;> simp [smul_sub]
    _ = (∑ k, a k • b k) - (∑ k ∈ I.erase j, a k) • b j := by
      simp only [Finset.sum_sub_distrib, ← Finset.sum_smul, Finset.sum_ite_mem_eq]

/-- All old coordinates of a shifted box, including the special pivot
height, as an exact algebraic identity. -/
theorem coord_shifted_star_box (b : Module.Basis ι R E)
    (I : Finset ι) (j i : ι) (t : R) (a : ι → R) :
    b.coord i (t • b j + ∑ k, a k • starShearBasis b I j k) =
      a i + (if i = j then t - ∑ k ∈ I.erase j, a k else 0) := by
  rw [sum_smul_starShearBasis]
  simp only [map_add, map_sub, map_smul, map_sum,
    Module.Basis.coord_apply, Module.Basis.repr_self_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst i
    simp
    ring
  · simp [hij, Ne.symm hij]

/-- The sum of the old normal heights is precisely `t+a_j`. -/
theorem sum_normal_coords_shifted_star_box (b : Module.Basis ι R E)
    (I : Finset ι) (j : ι) (hj : j ∈ I) (t : R) (a : ι → R) :
    (∑ i ∈ I, b.coord i (t • b j + ∑ k, a k • starShearBasis b I j k)) =
      t + a j := by
  simp only [coord_shifted_star_box, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', if_pos hj]
  rw [← Finset.add_sum_erase I a hj]
  ring

end BasisShear

/-- Extending the integral star-chart basis to the reals gives exactly the
same vectors as performing the real shear. Thus the geometric coordinates
come from a full basis of the ambient integer lattice. -/
theorem integralBasisReal_starShearBasis {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) (j : Fin n) :
    integralBasisReal (starShearBasis b I j) =
      starShearBasis (integralBasisReal b) I j := by
  apply Module.Basis.eq_of_apply_eq
  intro k
  rw [integralBasisReal_apply, starShearBasis_apply, starShearBasis_apply]
  split_ifs
  · simp only [map_sub, integralBasisReal_apply]
  · exact (integralBasisReal_apply b k).symm

/-- The new normal heights of every point of a side-`w` shifted box are
nonnegative if the shift is at least `w(q-1)`. Their total lies in
`[t,t+w]`. These are exactly the height bounds used in Section 6.2. -/
theorem shifted_star_box_normal_heights {n : ℕ}
    (b : Module.Basis (Fin n) ℝ (Ambient n))
    (I : Finset (Fin n)) (j : Fin n) (hj : j ∈ I)
    (w t : ℝ) (hw : 0 ≤ w) (ht : w * (I.card - 1 : ℕ) ≤ t)
    (a : Fin n → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ w) :
    (∀ i ∈ I, 0 ≤ b.coord i
      (t • b j + ∑ k, a k • starShearBasis b I j k)) ∧
    t ≤ (∑ i ∈ I, b.coord i
      (t • b j + ∑ k, a k • starShearBasis b I j k)) ∧
    (∑ i ∈ I, b.coord i
      (t • b j + ∑ k, a k • starShearBasis b I j k)) ≤ t + w := by
  have hsum : (∑ k ∈ I.erase j, a k) ≤ w * (I.card - 1 : ℕ) := by
    calc
      (∑ k ∈ I.erase j, a k) ≤ ∑ _k ∈ I.erase j, w :=
        Finset.sum_le_sum (fun k _ => (ha k).2)
      _ = w * (I.card - 1 : ℕ) := by
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_erase_of_mem hj]
        ring
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    rw [coord_shifted_star_box]
    by_cases hij : i = j
    · rw [if_pos hij]
      have h := (ha i).1
      linarith
    · rw [if_neg hij, add_zero]
      exact (ha i).1
  · rw [sum_normal_coords_shifted_star_box b I j hj]
    exact le_add_of_nonneg_right (ha j).1
  · rw [sum_normal_coords_shifted_star_box b I j hj]
    exact add_le_add le_rfl (ha j).2

end PaperVerification.ToricGeometry
end
end Source_ToricStarBoxCoordinates
-- END ORIGINAL PaperVerification.ToricStarBoxCoordinates


