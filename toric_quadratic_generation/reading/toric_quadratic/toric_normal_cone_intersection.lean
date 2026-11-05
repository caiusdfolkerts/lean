module
public import PaperVerification.ToricNormalConeFaces
public import Mathlib.Tactic.Push
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.NormNum
@[expose] public section
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
