module

public import Unimodular
public import Mathlib.LinearAlgebra.Matrix.Nonsingular
public import Mathlib.Analysis.Convex.Hull
public import Mathlib.Data.Finset.Max
public import Mathlib.Analysis.Convex.Extreme
public import Mathlib.Analysis.Convex.Topology
public import Mathlib.Analysis.LocallyConvex.Separation
public import TauCeti.Geometry.Toric.Algebraic.Ray.Face
public import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
public import Mathlib.Tactic.Module

@[expose] public section

/-! ## RealIndependence -/

namespace Unimodular

/-- Real linear independence and integer linear independence agree for a square
family of lattice vectors. The proof transports the actual determinant along the
injective integer-to-real ring homomorphism. -/
theorem real_independent_iff_integer_independent {n : ℕ} (u : Fin n → Lattice n) :
    LinearIndependent ℝ (fun i => embed (u i)) ↔ LinearIndependent ℤ u := by
  change LinearIndependent ℝ (Matrix.of (fun i => embed (u i))).row ↔
    LinearIndependent ℤ (Matrix.of u).row
  rw [Matrix.linearIndependent_row_iff, Matrix.linearIndependent_row_iff,
    Matrix.nonsingular_iff_det_ne_zero, Matrix.nonsingular_iff_det_ne_zero]
  change ((Matrix.of u).map (fun z : ℤ => (z : ℝ))).det ≠ 0 ↔ (Matrix.of u).det ≠ 0
  rw [← Int.cast_det]
  exact Int.cast_ne_zero

/-- The determinant definition of uniform unimodularity is equivalent to the
paper's geometric statement: each real-independent full-rank selection is an
actual integral lattice basis. -/
theorem uniform_iff_real_independent_is_basis {n : ℕ} {E : Type*} (U : E → Lattice n) :
    IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n)) U ↔
      ∀ a : Fin n → E, LinearIndependent ℝ (fun i => embed (U (a i))) →
        ∃ b : Module.Basis (Fin n) ℤ (Lattice n), ∀ i, b i = U (a i) := by
  rw [IntegralRigidity.uniform_iff_independent_spans]
  constructor
  · intro h a ha
    have hi : LinearIndependent ℤ (U ∘ a) :=
      (real_independent_iff_integer_independent (U ∘ a)).mp ha
    let b := Module.Basis.mk hi (h a hi).ge
    refine ⟨b, ?_⟩
    intro i
    exact Module.Basis.mk_apply hi (h a hi).ge i
  · intro h a ha
    obtain ⟨b, hb⟩ := h a ((real_independent_iff_integer_independent (U ∘ a)).mpr ha)
    have he : U ∘ a = b := funext fun i => (hb i).symm
    rw [he]
    exact b.span_eq

namespace SmoothCompleteFan

variable {n : ℕ} (fan : SmoothCompleteFan n)

/-- Lemma 6.1 with the conclusion stated directly in terms of real-independent
ray selections and integral lattice bases. -/
theorem real_independent_rays_form_lattice_basis (hfan : fan.PositiveCoordinateCriterion)
    (a : Fin n → fan.rays)
    (ha : LinearIndependent ℝ (fun i => embed ((a i).val))) :
    ∃ b : Module.Basis (Fin n) ℤ (Lattice n), ∀ i, b i = (a i).val :=
  (uniform_iff_real_independent_is_basis (fun u : fan.rays => u.val)).mp
    (fan.uniformlyUnimodular_of_positiveCoordinateCriterion hfan) a ha

end SmoothCompleteFan
end Unimodular

/-! ## GlobalRigidity -/

noncomputable section

namespace Unimodular.IntegralRigidity

variable {ι E M M' : Type*} [Fintype ι] [DecidableEq ι]
  [AddCommGroup M] [Module ℤ M] [AddCommGroup M'] [Module ℤ M']

theorem det_eq_mul_det (b g : Module.Basis ι ℤ M) (u : ι → M) :
    b.det u = b.det g * g.det u := by
  have h := congrArg (fun f : M [⋀^ι]→ₗ[ℤ] ℤ => f u) (b.det.eq_smul_basis_det g)
  simpa only [AlternatingMap.smul_apply, smul_eq_mul] using h

theorem ambient_replace_det (b g : Module.Basis ι ℤ M) (U : E → M)
    (labels : ι → E) (hg : ∀ i, U (labels i) = g i) (e : E) (j : ι) :
    b.det (U ∘ Function.update labels j e) = b.det g * g.repr (U e) j := by
  have he : U ∘ Function.update labels j e = Function.update g j (U e) := by
    funext i
    by_cases hij : i = j
    · subst i
      simp
    · simp [Function.comp_def, hij, hg]
  rw [he, det_eq_mul_det b g, det_replace_basis]

/-- Global signs may differ by one orientation unit. Unlike the normalised
version, this statement starts with arbitrary ambient bases and only asks that
the ray family have full rank. It constructs the common labelled integral bases. -/
theorem exists_unique_lattice_equiv_of_chirotope
    (b : Module.Basis ι ℤ M) (b' : Module.Basis ι ℤ M')
    (U : E → M) (V : E → M') (hU : Uniform b U) (hV : Uniform b' V)
    (hfull : ∃ labels : ι → E, b.det (U ∘ labels) ≠ 0)
    (ε : ℤˣ)
    (hchi : ∀ a : ι → E, (b'.det (V ∘ a)).sign =
      (ε : ℤ) * (b.det (U ∘ a)).sign) :
    ∃! φ : M ≃ₗ[ℤ] M', ∀ e, φ (U e) = V e := by
  have hdet (a : ι → E) : b'.det (V ∘ a) = (ε : ℤ) * b.det (U ∘ a) := by
    have h := hchi a
    rwa [sign_eq_self_of_abs_le_one (hU a), sign_eq_self_of_abs_le_one (hV a)] at h
  obtain ⟨labels, hlabels⟩ := hfull
  have hunitU : IsUnit (b.det (U ∘ labels)) := by
    apply Int.isUnit_iff_abs_eq.mpr
    have hpos : 0 < |b.det (U ∘ labels)| := abs_pos.mpr hlabels
    have hbound := hU labels
    omega
  have hunitV : IsUnit (b'.det (V ∘ labels)) := by
    rw [hdet]
    exact ε.isUnit.mul hunitU
  have hbU := b.is_basis_iff_det.mpr hunitU
  have hbV := b'.is_basis_iff_det.mpr hunitV
  let g : Module.Basis ι ℤ M := Module.Basis.mk hbU.1 hbU.2.ge
  let g' : Module.Basis ι ℤ M' := Module.Basis.mk hbV.1 hbV.2.ge
  have hg : ∀ i, U (labels i) = g i := by
    intro i
    exact (Module.Basis.mk_apply hbU.1 hbU.2.ge i).symm
  have hg' : ∀ i, V (labels i) = g' i := by
    intro i
    exact (Module.Basis.mk_apply hbV.1 hbV.2.ge i).symm
  have hgdet : b.det g = b.det (U ∘ labels) := by
    congr 1
    exact funext fun i => (hg i).symm
  have hg'det : b'.det g' = (ε : ℤ) * b.det g := by
    rw [hgdet, ← hdet]
    congr 1
    exact funext fun i => (hg' i).symm
  have hcoef : (ε : ℤ) * b.det g ≠ 0 :=
    mul_ne_zero (Units.ne_zero ε) (by rwa [hgdet])
  have hrepr (e : E) : g.repr (U e) = g'.repr (V e) := by
    ext j
    have h := hdet (Function.update labels j e)
    rw [ambient_replace_det b g U labels hg e j,
      ambient_replace_det b' g' V labels hg' e j, hg'det] at h
    apply mul_left_cancel₀ hcoef
    simpa only [mul_assoc] using h.symm
  let φ : M ≃ₗ[ℤ] M' := g.repr.trans g'.repr.symm
  have hφ : ∀ e, φ (U e) = V e := by
    intro e
    apply g'.repr.injective
    change g'.repr (g'.repr.symm (g.repr (U e))) = g'.repr (V e)
    rw [g'.repr.apply_symm_apply]
    exact hrepr e
  refine ⟨φ, hφ, ?_⟩
  intro ψ hψ
  apply LinearEquiv.toLinearMap_injective
  apply g.ext
  intro i
  change ψ (g i) = φ (g i)
  rw [← hg i, hψ, hφ]

theorem chirotope_of_lattice_equiv
    (b : Module.Basis ι ℤ M) (b' : Module.Basis ι ℤ M')
    (U : E → M) (V : E → M') (φ : M ≃ₗ[ℤ] M')
    (hφ : ∀ e, φ (U e) = V e) :
    ∃ ε : ℤˣ, ∀ a : ι → E, (b'.det (V ∘ a)).sign =
      (ε : ℤ) * (b.det (U ∘ a)).sign := by
  have hunit : IsUnit (b'.det (b.map φ)) := b'.isUnit_det (b.map φ)
  refine ⟨hunit.unit, ?_⟩
  intro a
  have he : φ.symm ∘ (V ∘ a) = U ∘ a := by
    funext i
    simp only [Function.comp_def, ← hφ, φ.symm_apply_apply]
  rw [det_eq_mul_det b' (b.map φ), b.det_map, he, Int.sign_mul,
    sign_eq_self_of_abs_le_one (Int.isUnit_iff_abs_eq.mp hunit).le,
    hunit.unit_spec]

/-- Labelled oriented configuration equivalence, allowing the one global
orientation reversal, is exactly integral lattice equivalence for full-rank
uniformly unimodular configurations. -/
theorem lattice_equiv_iff_chirotope
    (b : Module.Basis ι ℤ M) (b' : Module.Basis ι ℤ M')
    (U : E → M) (V : E → M') (hU : Uniform b U) (hV : Uniform b' V)
    (hfull : ∃ labels : ι → E, b.det (U ∘ labels) ≠ 0) :
    (∃ φ : M ≃ₗ[ℤ] M', ∀ e, φ (U e) = V e) ↔
      ∃ ε : ℤˣ, ∀ a : ι → E, (b'.det (V ∘ a)).sign =
        (ε : ℤ) * (b.det (U ∘ a)).sign := by
  constructor
  · rintro ⟨φ, hφ⟩
    exact chirotope_of_lattice_equiv b b' U V φ hφ
  · rintro ⟨ε, hε⟩
    exact (exists_unique_lattice_equiv_of_chirotope b b' U V hU hV hfull ε hε).exists

end Unimodular.IntegralRigidity

end

/-! ## PolytopeCriterion -/

noncomputable section

namespace Unimodular

open scoped BigOperators

def realPairing {n : ℕ} (x y : Ambient n) : ℝ := ∑ i, x i * y i

theorem realPairing_add_left {n : ℕ} (x y z : Ambient n) :
    realPairing (x + y) z = realPairing x z + realPairing y z := by
  simp [realPairing, add_mul, Finset.sum_add_distrib]

theorem realPairing_smul_left {n : ℕ} (a : ℝ) (x y : Ambient n) :
    realPairing (a • x) y = a * realPairing x y := by
  simp [realPairing, Finset.mul_sum, mul_assoc]

theorem pairing_add_left {n : ℕ} (x y : Ambient n) (u : Lattice n) :
    pairing (x + y) u = pairing x u + pairing y u := by
  exact realPairing_add_left x y (embed u)

theorem pairing_smul_left {n : ℕ} (a : ℝ) (x : Ambient n) (u : Lattice n) :
    pairing (a • x) u = a * pairing x u := by
  exact realPairing_smul_left a x (embed u)

theorem realPairing_dualCorner {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (t x : Ambient n) :
    realPairing (dualCorner b t) x = ∑ i, t i * realCoordinates b x i := by
  simp only [realPairing, dualCorner, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [realCoordinates, Finset.mul_sum, mul_assoc]

theorem pairing_dualCorner_basis {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (t : Ambient n) (i : Fin n) :
    pairing (dualCorner b t) (b i) = t i := by
  rw [pairing_dualCorner]
  simp [Module.Basis.repr_self, Finsupp.single_apply]

def dualCoordinates {n : ℕ} (b : Module.Basis (Fin n) ℤ (Lattice n)) :
    Ambient n →ₗ[ℝ] Ambient n where
  toFun x i := pairing x (b i)
  map_add' x y := funext fun i => pairing_add_left x y (b i)
  map_smul' a x := funext fun i => pairing_smul_left a x (b i)

theorem dualCoordinates_dualCorner {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (t : Ambient n) :
    dualCoordinates b (dualCorner b t) = t := by
  ext i
  exact pairing_dualCorner_basis b t i

theorem dualCorner_dualCoordinates {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (x : Ambient n) :
    dualCorner b (dualCoordinates b x) = x := by
  have hsurj : Function.Surjective (dualCoordinates b) :=
    fun t => ⟨dualCorner b t, dualCoordinates_dualCorner b t⟩
  apply LinearMap.injective_iff_surjective.mpr hsurj
  exact dualCoordinates_dualCorner b (dualCoordinates b x)

theorem dualCorner_sub {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (s t : Ambient n) :
    dualCorner b (s - t) = dualCorner b s - dualCorner b t := by
  ext j
  simp [dualCorner, sub_mul, Finset.sum_sub_distrib]

/-- Finitely many linear inequalities admit a common positive step whenever every active
inequality has nonpositive derivative. This is an elementary local feasibility theorem. -/
theorem exists_pos_feasible_step {ι : Type*} (s : Finset ι) (gap deriv : ι → ℝ)
    (hgap : ∀ i ∈ s, 0 ≤ gap i)
    (hactive : ∀ i ∈ s, gap i = 0 → deriv i ≤ 0) :
    ∃ t : ℝ, 0 < t ∧ ∀ i ∈ s, t * deriv i ≤ gap i := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert a s ha ih =>
    obtain ⟨t, ht, hts⟩ := ih
      (fun i hi => hgap i (Finset.mem_insert_of_mem hi))
      (fun i hi => hactive i (Finset.mem_insert_of_mem hi))
    by_cases hd : deriv a ≤ 0
    · refine ⟨t, ht, ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with he | hi
      · subst i
        exact (mul_nonpos_of_nonneg_of_nonpos ht.le hd).trans
          (hgap a (Finset.mem_insert_self _ _))
      · exact hts i hi
    · have hdp : 0 < deriv a := lt_of_not_ge hd
      have hgp : 0 < gap a := by
        have hg := hgap a (Finset.mem_insert_self _ _)
        by_contra hn
        have he : gap a = 0 := le_antisymm (le_of_not_gt hn) hg
        exact hd (hactive a (Finset.mem_insert_self _ _) he)
      let t' := min t (gap a / deriv a)
      have ht' : 0 < t' := lt_min ht (div_pos hgp hdp)
      refine ⟨t', ht', ?_⟩
      intro i hi
      rcases Finset.mem_insert.mp hi with he | hi
      · subst i
        calc
          t' * deriv a ≤ (gap a / deriv a) * deriv a :=
            mul_le_mul_of_nonneg_right (min_le_right _ _) hdp.le
          _ = gap a := div_mul_cancel₀ _ hdp.ne'
      · by_cases hdi : 0 ≤ deriv i
        · exact (mul_le_mul_of_nonneg_right (min_le_left _ _) hdi).trans (hts i hi)
        · exact (mul_nonpos_of_nonneg_of_nonpos ht'.le (le_of_lt (lt_of_not_ge hdi))).trans
            (hgap i (Finset.mem_insert_of_mem hi))

/-- A finite vertex/facet presentation of a smooth reflexive lattice polytope.

The equality is with an actual real convex hull. At each listed lattice vertex the active
primitive facet normals are exactly an integral basis. No normal-fan completeness or
determinant conclusion is a field of this structure. -/
structure SmoothReflexivePresentation (n : ℕ) where
  vertices : Finset (Lattice n)
  normals : Finset (Lattice n)
  vertices_nonempty : vertices.Nonempty
  basis : {v // v ∈ vertices} → Module.Basis (Fin n) ℤ (Lattice n)
  basis_mem : ∀ v i, basis v i ∈ normals
  basis_active : ∀ v i, pairing (embed v.val) (basis v i) = 1
  active_subset : ∀ v u, u ∈ normals → pairing (embed v.val) u = 1 →
    ∃ i, basis v i = u
  normals_occur : ∀ u ∈ normals, ∃ v i, basis v i = u
  hull_eq : convexHull ℝ (embed '' (vertices : Set (Lattice n))) =
    {x : Ambient n | ∀ u ∈ normals, pairing x u ≤ 1}

namespace SmoothReflexivePresentation

variable {n : ℕ} (P : SmoothReflexivePresentation n)

def carrier : Set (Ambient n) := convexHull ℝ (embed '' (P.vertices : Set (Lattice n)))

theorem mem_carrier_iff (x : Ambient n) :
    x ∈ P.carrier ↔ ∀ u ∈ P.normals, pairing x u ≤ 1 := by
  rw [carrier, P.hull_eq]
  rfl

theorem vertex_mem (v : {v // v ∈ P.vertices}) : embed v.val ∈ P.carrier :=
  subset_convexHull ℝ _ ⟨v.val, v.property, rfl⟩

theorem vertex_eq_dualCorner_one (v : {v // v ∈ P.vertices}) :
    embed v.val = dualCorner (P.basis v) (fun _ => 1) := by
  have h : dualCoordinates (P.basis v) (embed v.val) = (fun _ => 1) := by
    ext i
    exact P.basis_active v i
  rw [← h, dualCorner_dualCoordinates]

/-- Every real functional is maximised at a listed vertex, on the whole convex hull. -/
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

/-- The vertex normal-basis cones cover the real ambient space. This follows from
maximisation and finite local feasibility, not from an assumed fan structure. -/
theorem exists_nonnegative_basis_coordinates (x : Ambient n) :
    ∃ v : {v // v ∈ P.vertices}, ∀ i, 0 ≤ realCoordinates (P.basis v) x i := by
  classical
  obtain ⟨v, hv⟩ := P.exists_max_vertex x
  refine ⟨v, ?_⟩
  intro i
  by_contra hi
  have hneg : realCoordinates (P.basis v) x i < 0 := lt_of_not_ge hi
  let d : Ambient n := dualCorner (P.basis v) (Pi.single i (-1))
  have hd : realPairing d x = -realCoordinates (P.basis v) x i := by
    rw [realPairing_dualCorner]
    simp [Pi.single_apply]
  have hfeasible : ∃ t : ℝ, 0 < t ∧ embed v.val + t • d ∈ P.carrier := by
    obtain ⟨t, ht, htall⟩ := exists_pos_feasible_step P.normals
      (fun u => 1 - pairing (embed v.val) u) (fun u => pairing d u)
      (fun u hu => sub_nonneg.mpr ((P.mem_carrier_iff _).mp (P.vertex_mem v) u hu))
      (by
        intro u hu he
        obtain ⟨j, rfl⟩ := P.active_subset v u hu (sub_eq_zero.mp he).symm
        rw [pairing_dualCorner_basis]
        simp [Pi.single_apply]
        split_ifs <;> norm_num)
    refine ⟨t, ht, (P.mem_carrier_iff _).mpr ?_⟩
    intro u hu
    rw [pairing_add_left, pairing_smul_left]
    linarith [htall u hu]
  obtain ⟨t, ht, hp⟩ := hfeasible
  have hmax := hv _ hp
  rw [realPairing_add_left, realPairing_smul_left, hd] at hmax
  have hpos : 0 < t * (-realCoordinates (P.basis v) x i) :=
    mul_pos ht (neg_pos.mpr hneg)
  linarith

/-- The inward unit corner at each vertex, using the negative dual normal basis. -/
def UnitCornersContained : Prop :=
  ∀ v : {v // v ∈ P.vertices}, ∀ t : Ambient n,
    (∀ i, 0 ≤ t i ∧ t i ≤ 1) →
      embed v.val - dualCorner (P.basis v) t ∈ P.carrier

theorem positive_coordinate_bound (hP : P.UnitCornersContained)
    (v : {v // v ∈ P.vertices}) (u : Lattice n) (hu : u ∈ P.normals) :
    ∑ i, max ((P.basis v).repr u i) 0 ≤ 1 := by
  apply (cube_bound_iff_positive_mass (fun i => (P.basis v).repr u i)).mp
  intro t ht
  let s : Ambient n := fun i => 1 - t i
  have hs : ∀ i, 0 ≤ s i ∧ s i ≤ 1 := by
    intro i
    dsimp [s]
    constructor <;> linarith [(ht i).1, (ht i).2]
  have hm := hP v s hs
  have he : embed v.val - dualCorner (P.basis v) s = dualCorner (P.basis v) t := by
    rw [P.vertex_eq_dualCorner_one, ← dualCorner_sub]
    congr 1
    ext i
    simp [s]
  rw [he] at hm
  have hb := (P.mem_carrier_iff _).mp hm u hu
  rwa [pairing_dualCorner] at hb

/-- All independent full-rank selections of primitive facet normals are lattice bases
when every primitive inward unit corner is contained in the smooth reflexive polytope. -/
theorem uniformlyUnimodular_of_unitCornersContained (hP : P.UnitCornersContained) :
    IntegralRigidity.Uniform (Pi.basisFun ℤ (Fin n))
      (fun u : {u // u ∈ P.normals} => u.val) := by
  apply BasisCover.uniform_of_basis_cover P.basis
  · intro x
    obtain ⟨v, hv⟩ := P.exists_nonnegative_basis_coordinates (embed x)
    refine ⟨v, ?_⟩
    intro i
    have hi := hv i
    rw [realCoordinates_embed] at hi
    exact_mod_cast hi
  · intro v u
    exact P.positive_coordinate_bound hP v u.val u.property

end SmoothReflexivePresentation
end Unimodular

end

/-! ## PolytopeEdges -/

noncomputable section

namespace Unimodular

open scoped BigOperators

def integerPairing {n : ℕ} (x y : Lattice n) : ℤ := ∑ j, x j * y j

theorem pairing_embed {n : ℕ} (x y : Lattice n) :
    pairing (embed x) y = (integerPairing x y : ℤ) := by
  simp [pairing, embed, integerPairing]

def inwardBasisDirection {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (i : Fin n) : Lattice n :=
  fun j => -(b.repr (Pi.single j 1) i)

theorem embed_inwardBasisDirection {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (i : Fin n) :
    embed (inwardBasisDirection b i) = dualCorner b (Pi.single i (-1)) := by
  ext j
  simp [inwardBasisDirection, embed, dualCorner, Pi.single_apply]

theorem integerPairing_inwardBasisDirection {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (i j : Fin n) :
    integerPairing (inwardBasisDirection b i) (b j) = if i = j then -1 else 0 := by
  have h := pairing_dualCorner_basis b (Pi.single i (-1)) j
  rw [← embed_inwardBasisDirection, pairing_embed] at h
  have he : (integerPairing (inwardBasisDirection b i) (b j) : ℝ) =
      ((if i = j then -1 else 0 : ℤ) : ℝ) := by
    simpa [Pi.single_apply, eq_comm] using h
  exact_mod_cast he

/-- A lattice vector is primitive when its only integer divisors are units. -/
def PrimitiveLatticeVector {n : ℕ} (x : Lattice n) : Prop :=
  ∀ k : ℤ, ∀ z : Lattice n, x = k • z → IsUnit k

theorem inwardBasisDirection_primitive {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (i : Fin n) :
    PrimitiveLatticeVector (inwardBasisDirection b i) := by
  intro k z hz
  have h := integerPairing_inwardBasisDirection b i i
  simp only [ite_true] at h
  rw [hz] at h
  have hmul : k * integerPairing z (b i) = -1 := by
    simpa [integerPairing, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, mul_assoc] using h
  apply IsUnit.of_mul_eq_one (a := k) (-integerPairing z (b i))
  linarith

namespace SmoothReflexivePresentation

variable {n : ℕ} (P : SmoothReflexivePresentation n)

/-- The listed points really are vertices of the real polytope. -/
theorem vertex_isExtremePoint (v : {v // v ∈ P.vertices}) :
    embed v.val ∈ P.carrier.extremePoints ℝ := by
  refine ⟨P.vertex_mem v, ?_⟩
  rintro x hx y hy ⟨a, b, ha, hb, hab, he⟩
  have hsurj : Function.Surjective (dualCoordinates (P.basis v)) :=
    fun s => ⟨dualCorner (P.basis v) s, dualCoordinates_dualCorner _ _⟩
  apply LinearMap.injective_iff_surjective.mpr hsurj
  ext i
  change pairing x (P.basis v i) = pairing (embed v.val) (P.basis v i)
  rw [P.basis_active]
  have hxj := (P.mem_carrier_iff x).mp hx (P.basis v i) (P.basis_mem v i)
  have hyj := (P.mem_carrier_iff y).mp hy (P.basis v i) (P.basis_mem v i)
  have he' := congrArg (fun z => pairing z (P.basis v i)) he
  rw [pairing_add_left, pairing_smul_left, pairing_smul_left, P.basis_active] at he'
  nlinarith

/-- There are no unlisted vertices: this is the exact extreme-point set. -/
theorem extremePoints_eq_vertices :
    P.carrier.extremePoints ℝ = embed '' (P.vertices : Set (Lattice n)) := by
  apply Set.Subset.antisymm
  · exact extremePoints_convexHull_subset
  · rintro x ⟨v, hv, rfl⟩
    exact P.vertex_isExtremePoint ⟨v, hv⟩

/-- Actual feasible directions at a vertex are precisely the negative orthant in
the dual normal-basis coordinates. This identifies the full tangent cone. -/
theorem exists_pos_feasible_iff (v : {v // v ∈ P.vertices}) (d : Ambient n) :
    (∃ t : ℝ, 0 < t ∧ embed v.val + t • d ∈ P.carrier) ↔
      ∀ i, pairing d (P.basis v i) ≤ 0 := by
  constructor
  · rintro ⟨t, ht, hp⟩ i
    have hi := (P.mem_carrier_iff _).mp hp (P.basis v i) (P.basis_mem v i)
    rw [pairing_add_left, pairing_smul_left, P.basis_active] at hi
    nlinarith
  · intro hd
    obtain ⟨t, ht, htall⟩ := exists_pos_feasible_step P.normals
      (fun u => 1 - pairing (embed v.val) u) (fun u => pairing d u)
      (fun u hu => sub_nonneg.mpr ((P.mem_carrier_iff _).mp (P.vertex_mem v) u hu))
      (by
        intro u hu he
        obtain ⟨i, rfl⟩ := P.active_subset v u hu (sub_eq_zero.mp he).symm
        exact hd i)
    refine ⟨t, ht, (P.mem_carrier_iff _).mpr ?_⟩
    intro u hu
    rw [pairing_add_left, pairing_smul_left]
    linarith [htall u hu]

def edgeSlice (v : {v // v ∈ P.vertices}) (i : Fin n) : Set (Ambient n) :=
  {p | p ∈ P.carrier ∧ ∀ j, j ≠ i → pairing p (P.basis v j) = 1}

theorem vertex_mem_edgeSlice (v : {v // v ∈ P.vertices}) (i : Fin n) :
    embed v.val ∈ P.edgeSlice v i :=
  ⟨P.vertex_mem v, fun j _ => P.basis_active v j⟩

theorem edgeSlice_isExtreme (v : {v // v ∈ P.vertices}) (i : Fin n) :
    IsExtreme ℝ P.carrier (P.edgeSlice v i) := by
  refine ⟨fun _ hp => hp.1, ?_⟩
  rintro x hx y hy z hz ⟨a, b, ha, hb, hab, rfl⟩
  refine ⟨hx, ?_⟩
  intro j hji
  have hzj := hz.2 j hji
  have hxj := (P.mem_carrier_iff x).mp hx (P.basis v j) (P.basis_mem v j)
  have hyj := (P.mem_carrier_iff y).mp hy (P.basis v j) (P.basis_mem v j)
  rw [pairing_add_left, pairing_smul_left, pairing_smul_left] at hzj
  nlinarith

theorem edgeSlice_convex (v : {v // v ∈ P.vertices}) (i : Fin n) :
    Convex ℝ (P.edgeSlice v i) := by
  intro x hx y hy a b ha hb hab
  refine ⟨(convex_convexHull ℝ _ ) hx.1 hy.1 ha hb hab, ?_⟩
  intro j hji
  rw [pairing_add_left, pairing_smul_left, pairing_smul_left, hx.2 j hji, hy.2 j hji]
  simpa using hab

/-- The face obtained by retaining the other n−1 active facets lies on the inward
half-line generated by the negative dual basis vector. -/
theorem edgeSlice_subset_ray (v : {v // v ∈ P.vertices}) (i : Fin n)
    {p : Ambient n} (hp : p ∈ P.edgeSlice v i) :
    ∃ t : ℝ, 0 ≤ t ∧ p = embed v.val + t • embed (inwardBasisDirection (P.basis v) i) := by
  let t := 1 - pairing p (P.basis v i)
  have ht : 0 ≤ t := sub_nonneg.mpr
    ((P.mem_carrier_iff _).mp hp.1 (P.basis v i) (P.basis_mem v i))
  refine ⟨t, ht, ?_⟩
  have hsurj : Function.Surjective (dualCoordinates (P.basis v)) :=
    fun s => ⟨dualCorner (P.basis v) s, dualCoordinates_dualCorner _ _⟩
  apply LinearMap.injective_iff_surjective.mpr hsurj
  ext j
  change pairing p (P.basis v j) = pairing _ (P.basis v j)
  rw [pairing_add_left, pairing_smul_left, P.basis_active,
    embed_inwardBasisDirection, pairing_dualCorner_basis]
  by_cases hji : j = i
  · subst j
    simp [Pi.single_apply, t]
  · simp [Pi.single_apply, hji, Ne.symm hji, hp.2 j hji]

/-- Each such face contains a nontrivial initial segment in the primitive inward
direction. Together with `edgeSlice_subset_ray` this proves that it is an edge. -/
theorem exists_pos_mem_edgeSlice (v : {v // v ∈ P.vertices}) (i : Fin n) :
    ∃ t : ℝ, 0 < t ∧
      embed v.val + t • embed (inwardBasisDirection (P.basis v) i) ∈ P.edgeSlice v i := by
  let d := embed (inwardBasisDirection (P.basis v) i)
  have hd (j : Fin n) : pairing d (P.basis v j) = if i = j then -1 else 0 := by
    change pairing (embed (inwardBasisDirection (P.basis v) i)) (P.basis v j) = _
    rw [embed_inwardBasisDirection, pairing_dualCorner_basis]
    simp [Pi.single_apply, eq_comm]
  obtain ⟨t, ht, htall⟩ := exists_pos_feasible_step P.normals
    (fun u => 1 - pairing (embed v.val) u) (fun u => pairing d u)
    (fun u hu => sub_nonneg.mpr ((P.mem_carrier_iff _).mp (P.vertex_mem v) u hu))
    (by
      intro u hu he
      obtain ⟨j, rfl⟩ := P.active_subset v u hu (sub_eq_zero.mp he).symm
      rw [hd]
      split_ifs <;> norm_num)
  refine ⟨t, ht, (P.mem_carrier_iff _).mpr ?_, ?_⟩
  · intro u hu
    rw [pairing_add_left, pairing_smul_left]
    linarith [htall u hu]
  · intro j hji
    rw [pairing_add_left, pairing_smul_left, P.basis_active, hd]
    simp [Ne.symm hji]

end SmoothReflexivePresentation
end Unimodular

end

/-! ## StrictSupport -/

namespace Unimodular

open scoped BigOperators

theorem sum_nonpos_of_positive_mass_le_one {ι : Type*} [Fintype ι] [DecidableEq ι]
    (a : ι → ℤ) (ha : ∑ i, max (a i) 0 ≤ 1)
    (hne : ∀ i, a ≠ Pi.single i 1) : ∑ i, a i ≤ 0 := by
  classical
  by_cases hpos : ∃ i, 0 < a i
  · obtain ⟨i, hi⟩ := hpos
    let T : Matrix ι ι ℤ := fun j _ => a j
    have hT : PositiveCoordinates.PositiveCoordinateBound T := fun _ => ha
    have hai : a i = 1 := PositiveCoordinates.positive_entry_eq_one hT
      (i := i) (j := i) hi
    have hother : ∀ j, j ≠ i → a j ≤ 0 := by
      intro j hji
      by_contra hj
      exact hji (PositiveCoordinates.positive_entry_unique hT
        (i := j) (k := i) (j := i) (lt_of_not_ge hj) hi)
    have hex : ∃ j, j ≠ i ∧ a j < 0 := by
      by_contra! h
      apply hne i
      ext j
      by_cases hji : j = i
      · subst j
        simp [hai]
      · have hz : a j = 0 := le_antisymm (hother j hji) (h j hji)
        simp [Pi.single_apply, hji, Ne.symm hji, hz]
    obtain ⟨j, hji, hj⟩ := hex
    have hs : (∑ k, a k) < ∑ k : ι, if k = i then (1 : ℤ) else 0 := by
      apply Finset.sum_lt_sum
      · intro k _
        by_cases hki : k = i
        · subst k
          simp [hai]
        · simpa [hki] using hother k hki
      · exact ⟨j, Finset.mem_univ _, by simpa [hji] using hj⟩
    have hu : (∑ k : ι, if k = i then (1 : ℤ) else 0) = 1 := by simp
    rw [hu] at hs
    omega
  · push_neg at hpos
    exact Finset.sum_nonpos fun i _ => hpos i

namespace SmoothCompleteFan

variable {n : ℕ} (fan : SmoothCompleteFan n)

theorem coordinate_sum_nonpos_of_not_basis_ray (hfan : fan.PositiveCoordinateCriterion)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (hb : b ∈ fan.maximal)
    (u : Lattice n) (hu : u ∈ fan.rays) (hne : ∀ i, b i ≠ u) :
    ∑ i, b.repr u i ≤ 0 := by
  apply sum_nonpos_of_positive_mass_le_one _ (hfan b hb u hu)
  intro i he
  apply hne i
  apply b.repr.injective
  ext j
  have hej := congrFun he j
  simpa [Module.Basis.repr_self, Pi.single_apply, Finsupp.single_apply, eq_comm] using hej.symm

/-- The all-ones dual vector supports exactly the rays of this maximal cone;
every other ray has pairing at most zero. This is strict convexity at each
maximal cone, with an integral gap. -/
theorem strict_support_at_basis (hfan : fan.PositiveCoordinateCriterion)
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (hb : b ∈ fan.maximal)
    (u : Lattice n) (hu : u ∈ fan.rays) :
    pairing (dualCorner b (fun _ => 1)) u ≤ 1 ∧
      (pairing (dualCorner b (fun _ => 1)) u = 1 ↔ ∃ i, b i = u) := by
  classical
  by_cases he : ∃ i, b i = u
  · obtain ⟨i, rfl⟩ := he
    have hp : pairing (dualCorner b (fun _ => 1)) (b i) = 1 := by
      rw [pairing_dualCorner]
      simp [Module.Basis.repr_self, Finsupp.single_apply]
    exact ⟨hp.le, by simp [hp]⟩
  · have hne : ∀ i, b i ≠ u := by simpa using he
    have hs := fan.coordinate_sum_nonpos_of_not_basis_ray hfan b hb u hu hne
    have hp : pairing (dualCorner b (fun _ => 1)) u ≤ 0 := by
      rw [pairing_dualCorner]
      simp only [one_mul]
      exact_mod_cast hs
    constructor
    · linarith
    · constructor
      · intro h
        linarith
      · exact fun h => (he h).elim

end SmoothCompleteFan
end Unimodular

/-! ## PolarPolytope -/

noncomputable section

namespace Unimodular

open scoped BigOperators

def latticeDualVertex {n : ℕ} (b : Module.Basis (Fin n) ℤ (Lattice n)) : Lattice n :=
  fun j => ∑ i, b.repr (Pi.single j 1) i

theorem embed_latticeDualVertex {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) :
    embed (latticeDualVertex b) = dualCorner b (fun _ => 1) := by
  ext j
  simp [embed, latticeDualVertex, dualCorner]

theorem realPairing_eq_coordinates {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (p x : Ambient n) :
    realPairing p x = ∑ i, realCoordinates b x i * pairing p (b i) := by
  conv_lhs => rw [← sum_basis_realCoordinates b x]
  simp only [realPairing, Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
    Finset.mul_sum, embed]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  simp [pairing, Finset.mul_sum, Finset.sum_mul, mul_comm, mul_left_comm, mul_assoc]

theorem linearMap_eq_realPairing {n : ℕ} (f : Ambient n →ₗ[ℝ] ℝ) (x : Ambient n) :
    f x = realPairing x (fun j => f (Pi.single j 1)) := by
  have hx : x = ∑ j, x j • Pi.single j (1 : ℝ) := by
    ext k
    simp [Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
  conv_lhs => rw [hx]
  simp [map_sum, map_smul, realPairing]

namespace SmoothCompleteFan

variable {n : ℕ} (fan : SmoothCompleteFan n)

def rayFinset : Finset (Lattice n) :=
  fan.maximal.biUnion fun b => Finset.univ.image b

@[simp] theorem mem_rayFinset (u : Lattice n) : u ∈ fan.rayFinset ↔ u ∈ fan.rays := by
  simp [rayFinset, rays]

def dualVertices : Finset (Lattice n) := fan.maximal.image latticeDualVertex

theorem dualVertices_nonempty : fan.dualVertices.Nonempty := by
  obtain ⟨b, hb, _⟩ := fan.complete 0
  exact ⟨latticeDualVertex b, Finset.mem_image.mpr ⟨b, hb, rfl⟩⟩

/-- The polar ray inequalities are exactly the convex hull of the integral
all-ones dual vertices. Separation is applied only to an actual finite convex hull. -/
theorem polar_eq_convexHull_dualVertices (hfan : fan.PositiveCoordinateCriterion) :
    fan.rayPolytope = convexHull ℝ (embed '' (fan.dualVertices : Set (Lattice n))) := by
  classical
  apply Set.Subset.antisymm
  · intro p hp
    by_contra hnot
    have hfinite : (embed '' (fan.dualVertices : Set (Lattice n))).Finite :=
      fan.dualVertices.finite_toSet.image embed
    obtain ⟨f, c, hf, hfp⟩ := geometric_hahn_banach_closed_point
      (convex_convexHull ℝ _) (hfinite.isClosed_convexHull ℝ) hnot
    let x : Ambient n := fun j => f (Pi.single j 1)
    obtain ⟨b, hb, hx⟩ := fan.complete x
    have hc : ∀ i, 0 ≤ realCoordinates b x i := (mem_basisCone_iff b x).mp hx
    have hbound : f p ≤ f (embed (latticeDualVertex b)) := by
      change f.toLinearMap p ≤ f.toLinearMap (embed (latticeDualVertex b))
      rw [linearMap_eq_realPairing f.toLinearMap p,
        linearMap_eq_realPairing f.toLinearMap (embed (latticeDualVertex b))]
      change realPairing p x ≤ realPairing (embed (latticeDualVertex b)) x
      rw [realPairing_eq_coordinates b, realPairing_eq_coordinates b]
      apply Finset.sum_le_sum
      intro i _
      rw [embed_latticeDualVertex, pairing_dualCorner_basis]
      apply mul_le_mul_of_nonneg_left _ (hc i)
      exact hp (b i) ⟨b, hb, i, rfl⟩
    have hvertex : embed (latticeDualVertex b) ∈
        convexHull ℝ (embed '' (fan.dualVertices : Set (Lattice n))) := by
      apply subset_convexHull
      exact ⟨latticeDualVertex b, Finset.mem_image.mpr ⟨b, hb, rfl⟩, rfl⟩
    exact (not_lt_of_ge hbound) ((hf _ hvertex).trans hfp)
  · apply convexHull_min
    · rintro p ⟨v, hv, rfl⟩
      obtain ⟨b, hb, rfl⟩ := Finset.mem_image.mp hv
      intro u hu
      rw [embed_latticeDualVertex]
      exact (fan.strict_support_at_basis hfan b hb u hu).1
    · intro p hp q hq a b ha hb hab u hu
      rw [pairing_add_left, pairing_smul_left, pairing_smul_left]
      calc
        a * pairing p u + b * pairing q u ≤ a * 1 + b * 1 :=
          add_le_add (mul_le_mul_of_nonneg_left (hp u hu) ha)
            (mul_le_mul_of_nonneg_left (hq u hu) hb)
        _ = 1 := by simpa using hab

def vertexBasis (v : {v // v ∈ fan.dualVertices}) :
    Module.Basis (Fin n) ℤ (Lattice n) :=
  Classical.choose (Finset.mem_image.mp v.property)

theorem vertexBasis_mem (v : {v // v ∈ fan.dualVertices}) :
    fan.vertexBasis v ∈ fan.maximal :=
  (Classical.choose_spec (Finset.mem_image.mp v.property)).1

theorem latticeDualVertex_vertexBasis (v : {v // v ∈ fan.dualVertices}) :
    latticeDualVertex (fan.vertexBasis v) = v.val :=
  (Classical.choose_spec (Finset.mem_image.mp v.property)).2

theorem vertex_eq_dualCorner (v : {v // v ∈ fan.dualVertices}) :
    embed v.val = dualCorner (fan.vertexBasis v) (fun _ => 1) := by
  rw [← fan.latticeDualVertex_vertexBasis v, embed_latticeDualVertex]

/-- A smooth reflexive lattice presentation constructed from the coordinate
criterion. Its facet normals are exactly the original fan rays. -/
def polarPresentation (hfan : fan.PositiveCoordinateCriterion) :
    SmoothReflexivePresentation n where
  vertices := fan.dualVertices
  normals := fan.rayFinset
  vertices_nonempty := fan.dualVertices_nonempty
  basis := fan.vertexBasis
  basis_mem v i := (fan.mem_rayFinset _).mpr
    ⟨fan.vertexBasis v, fan.vertexBasis_mem v, i, rfl⟩
  basis_active v i := by
    rw [fan.vertex_eq_dualCorner, pairing_dualCorner_basis]
  active_subset v u hu he := by
    rw [fan.vertex_eq_dualCorner] at he
    exact (fan.strict_support_at_basis hfan (fan.vertexBasis v)
      (fan.vertexBasis_mem v) u ((fan.mem_rayFinset _).mp hu)).2.mp he
  normals_occur u hu := by
    obtain ⟨b, hb, i, rfl⟩ := (fan.mem_rayFinset _).mp hu
    let v : {v // v ∈ fan.dualVertices} :=
      ⟨latticeDualVertex b, Finset.mem_image.mpr ⟨b, hb, rfl⟩⟩
    refine ⟨v, ?_⟩
    apply (fan.strict_support_at_basis hfan (fan.vertexBasis v)
      (fan.vertexBasis_mem v) (b i) ⟨b, hb, i, rfl⟩).2.mp
    rw [← fan.vertex_eq_dualCorner v]
    change pairing (embed (latticeDualVertex b)) (b i) = 1
    rw [embed_latticeDualVertex, pairing_dualCorner_basis]
  hull_eq := by
    rw [← fan.polar_eq_convexHull_dualVertices hfan]
    ext p
    simp only [rayPolytope, Set.mem_setOf_eq, fan.mem_rayFinset]

theorem polarPresentation_unitCornersContained (hfan : fan.PositiveCoordinateCriterion) :
    (fan.polarPresentation hfan).UnitCornersContained := by
  intro v t ht
  change {v // v ∈ fan.dualVertices} at v
  apply ((fan.polarPresentation hfan).mem_carrier_iff _).mpr
  intro u hu
  change u ∈ fan.rayFinset at hu
  change pairing (embed v.val - dualCorner (fan.vertexBasis v) t) u ≤ 1
  rw [fan.vertex_eq_dualCorner, ← dualCorner_sub, pairing_dualCorner]
  apply (cube_bound_iff_positive_mass
    (fun i => (fan.vertexBasis v).repr u i)).mpr
    (hfan (fan.vertexBasis v) (fan.vertexBasis_mem v) u ((fan.mem_rayFinset _).mp hu))
  intro i
  change 0 ≤ 1 - t i ∧ 1 - t i ≤ 1
  constructor <;> linarith [(ht i).1, (ht i).2]

end SmoothCompleteFan
end Unimodular

end

/-! ## FacetGeometry -/

noncomputable section

namespace Unimodular.SmoothReflexivePresentation

open scoped BigOperators

variable {n : ℕ} (P : SmoothReflexivePresentation n)

theorem normal_primitive (u : Lattice n) (hu : u ∈ P.normals) : PrimitiveLatticeVector u := by
  obtain ⟨v, i, rfl⟩ := P.normals_occur u hu
  intro k z he
  have h := congrArg (fun x => (P.basis v).repr x i) he
  simp only [Module.Basis.repr_self, Finsupp.single_eq_same, map_smulₛₗ,
    RingHom.id_apply, Finsupp.smul_apply, smul_eq_mul] at h
  exact IsUnit.of_mul_eq_one ((P.basis v).repr z i) h.symm

/-- Every listed inequality is genuinely indispensable. In particular, the
normal list cannot hide redundant vectors that are not facet normals. -/
theorem normal_irredundant (u : Lattice n) (hu : u ∈ P.normals) :
    ∃ p : Ambient n, (∀ w ∈ P.normals, w ≠ u → pairing p w ≤ 1) ∧ 1 < pairing p u := by
  classical
  obtain ⟨v, i, hbi⟩ := P.normals_occur u hu
  let d := dualCorner (P.basis v) (Pi.single i 1)
  have hdu : pairing d u = 1 := by
    rw [← hbi, pairing_dualCorner_basis]
    simp
  obtain ⟨t, ht, htall⟩ := exists_pos_feasible_step (P.normals.erase u)
    (fun w => 1 - pairing (embed v.val) w) (fun w => pairing d w)
    (fun w hw => sub_nonneg.mpr
      ((P.mem_carrier_iff _).mp (P.vertex_mem v) w (Finset.mem_erase.mp hw).2))
    (by
      intro w hw he
      obtain ⟨hwu, hwn⟩ := Finset.mem_erase.mp hw
      obtain ⟨j, hbj⟩ := P.active_subset v w hwn (sub_eq_zero.mp he).symm
      have hij : i ≠ j := by
        intro hij
        exact hwu (hbj.symm.trans (hij ▸ hbi))
      rw [← hbj, pairing_dualCorner_basis]
      simp [Pi.single_apply, hij])
  refine ⟨embed v.val + t • d, ?_, ?_⟩
  · intro w hw hwu
    have h := htall w (Finset.mem_erase.mpr ⟨hwu, hw⟩)
    rw [pairing_add_left, pairing_smul_left]
    linarith
  · rw [pairing_add_left, pairing_smul_left, hdu, ← hbi, P.basis_active]
    linarith

/-- Every facet has a point at which precisely its own normal inequality is
active. This supplies a relative interior witness in its supporting hyperplane. -/
theorem exists_only_one_active (u : Lattice n) (hu : u ∈ P.normals) :
    ∃ p : Ambient n, pairing p u = 1 ∧
      ∀ w ∈ P.normals, w ≠ u → pairing p w < 1 := by
  classical
  obtain ⟨v, i, hbi⟩ := P.normals_occur u hu
  let a : Ambient n := fun j => if i = j then 0 else -1
  let d := dualCorner (P.basis v) a
  have hdu : pairing d u = 0 := by
    rw [← hbi, pairing_dualCorner_basis]
    simp [a]
  obtain ⟨t, ht, htall⟩ := exists_pos_feasible_step P.normals
    (fun w => (1 - pairing (embed v.val) w) / 2) (fun w => pairing d w)
    (fun w hw => div_nonneg
      (sub_nonneg.mpr ((P.mem_carrier_iff _).mp (P.vertex_mem v) w hw)) (by norm_num))
    (by
      intro w hw he
      have hpw : pairing (embed v.val) w = 1 := by linarith
      obtain ⟨j, rfl⟩ := P.active_subset v w hw hpw
      rw [pairing_dualCorner_basis]
      dsimp [a]
      split_ifs <;> norm_num)
  refine ⟨embed v.val + t • d, ?_, ?_⟩
  · rw [pairing_add_left, pairing_smul_left, hdu, mul_zero, add_zero, ← hbi, P.basis_active]
  · intro w hw hwu
    have hpw := (P.mem_carrier_iff _).mp (P.vertex_mem v) w hw
    rw [pairing_add_left, pairing_smul_left]
    by_cases he : pairing (embed v.val) w = 1
    · obtain ⟨j, hbj⟩ := P.active_subset v w hw he
      have hij : i ≠ j := by
        intro hij
        exact hwu (hbj.symm.trans (hij ▸ hbi))
      have hdw : pairing d w = -1 := by
        rw [← hbj, pairing_dualCorner_basis]
        simp [a, hij]
      rw [he, hdw]
      linarith
    · have hlt : pairing (embed v.val) w < 1 := lt_of_le_of_ne hpw he
      linarith [htall w hw]

end Unimodular.SmoothReflexivePresentation

end

/-! ## TangentFaces -/

noncomputable section

namespace Unimodular

open scoped BigOperators Pointwise

/-- The divisor definition of primitivity agrees with the existing basis-free
integer-linear-functional definition in the pinned toric library. -/
theorem primitiveLatticeVector_iff_isPrimitive {n : ℕ} (x : Lattice n) :
    PrimitiveLatticeVector x ↔ TauCeti.IsPrimitive x := by
  constructor
  · intro hx
    have hx0 : x ≠ 0 := by
      intro he
      have hunit := hx 0 0 (by simp [he])
      exact not_isUnit_zero hunit
    obtain ⟨d, w, hd, hw, he⟩ := TauCeti.exists_eq_zsmul_isPrimitive hx0
    have hunit := hx d w he
    have hd1 : d = 1 := by
      have ha := Int.isUnit_iff_abs_eq.mp hunit
      rwa [abs_of_pos hd] at ha
    rw [he, hd1, one_smul]
    exact hw
  · intro hx k z he
    obtain ⟨f, hf⟩ := TauCeti.isPrimitive_def.mp hx
    have hm : k * f z = 1 := by
      have h : f (k • z) = 1 := by rwa [← he]
      rw [map_smul] at h
      simpa only [smul_eq_mul] using h
    exact IsUnit.of_mul_eq_one (f z) hm

def localCone {n : ℕ} (v : Ambient n) (E : Set (Ambient n)) : PointedCone ℝ (Ambient n) :=
  PointedCone.hull ℝ ((fun p => p - v) '' E)

theorem mem_localCone_iff {n : ℕ} {v d : Ambient n} {E : Set (Ambient n)}
    (hE : Convex ℝ E) (hv : v ∈ E) :
    d ∈ localCone v E ↔ ∃ t : ℝ, 0 < t ∧ v + t • d ∈ E := by
  have htranslate : Convex ℝ ((fun p => p - v) '' E) := by
    rintro x ⟨p, hp, rfl⟩ y ⟨q, hq, rfl⟩ a b ha hb hab
    refine ⟨a • p + b • q, hE hp hq ha hb hab, ?_⟩
    calc
      a • p + b • q - v = a • p + b • q - (a + b) • v := by rw [hab, one_smul]
      _ = a • (p - v) + b • (q - v) := by module
  constructor
  · intro hd
    have hz : (0 : Ambient n) ∈ ConvexCone.hull ℝ ((fun p => p - v) '' E) :=
      ConvexCone.subset_hull ⟨v, hv, sub_self v⟩
    have hle : localCone v E ≤
        (ConvexCone.hull ℝ ((fun p => p - v) '' E)).toPointedCone hz :=
      Submodule.span_le.mpr ConvexCone.subset_hull
    obtain ⟨r, hr, z, hzE, hzd⟩ := (ConvexCone.mem_hull_of_convex htranslate).mp (hle hd)
    obtain ⟨p, hp, rfl⟩ := hzE
    refine ⟨r⁻¹, inv_pos.mpr hr, ?_⟩
    rw [← hzd, smul_smul, inv_mul_cancel₀ hr.ne', one_smul]
    simpa only [add_sub_cancel] using hp
  · rintro ⟨t, ht, hp⟩
    have hm : (v + t • d) - v ∈ localCone v E := PointedCone.subset_hull ⟨_, hp, rfl⟩
    have hs := PointedCone.smul_mem (localCone v E) (inv_nonneg.mpr ht.le) hm
    simpa [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ ht.ne'] using hs

theorem convex_feasible_step_mono {n : ℕ} {v d : Ambient n} {E : Set (Ambient n)}
    (hE : Convex ℝ E) (hv : v ∈ E) {s t : ℝ} (hs : 0 < s)
    (hp : v + s • d ∈ E) (ht : 0 ≤ t) (hts : t ≤ s) : v + t • d ∈ E := by
  have hdiv : t / s ≤ 1 := (div_le_one hs).mpr hts
  have hm := hE hv hp (sub_nonneg.mpr hdiv) (div_nonneg ht hs.le)
    (sub_add_cancel (1 : ℝ) (t / s))
  have he : (1 - t / s) • v + (t / s) • (v + s • d) = v + t • d := by
    calc
      (1 - t / s) • v + (t / s) • (v + s • d) =
          ((1 - t / s) + t / s) • v + ((t / s) * s) • d := by module
      _ = v + t • d := by simp [div_mul_cancel₀ _ hs.ne']
  rwa [he] at hm

/-- A face through a point induces a genuine face of the tangent cone. -/
theorem localCone_isFaceOf {n : ℕ} {v : Ambient n} {E P : Set (Ambient n)}
    (hP : Convex ℝ P) (hE : Convex ℝ E) (hEP : IsExtreme ℝ P E) (hv : v ∈ E) :
    (localCone v E).IsFaceOf (localCone v P) := by
  apply PointedCone.IsFaceOf.of_mem_of_add_mem_left
  · exact Submodule.span_mono (Set.image_mono hEP.subset)
  · intro x y hx hy hxy
    obtain ⟨sx, hsx, hpx⟩ := (mem_localCone_iff hP (hEP.subset hv)).mp hx
    obtain ⟨sy, hsy, hpy⟩ := (mem_localCone_iff hP (hEP.subset hv)).mp hy
    obtain ⟨se, hse, hpe⟩ := (mem_localCone_iff hE hv).mp hxy
    let t := min sx (min sy se)
    have ht : 0 < t := lt_min hsx (lt_min hsy hse)
    have htx : t ≤ sx := min_le_left _ _
    have hty : t ≤ sy := (min_le_right _ _).trans (min_le_left _ _)
    have hte : t ≤ se := (min_le_right _ _).trans (min_le_right _ _)
    have hxP := convex_feasible_step_mono hP (hEP.subset hv) hsx hpx ht.le htx
    have hyP := convex_feasible_step_mono hP (hEP.subset hv) hsy hpy ht.le hty
    have hmE : v + (t / 2) • (x + y) ∈ E :=
      convex_feasible_step_mono hE hv hse hpe (by positivity) (by linarith)
    have hmseg : v + (t / 2) • (x + y) ∈
        openSegment ℝ (v + t • x) (v + t • y) := by
      refine ⟨1 / 2, 1 / 2, by norm_num, by norm_num, by norm_num, ?_⟩
      module
    have hxE := hEP.left_mem_of_mem_openSegment hxP hyP hmE hmseg
    exact (mem_localCone_iff hE hv).mpr ⟨t, ht, hxE⟩

theorem span_localCone {n : ℕ} {v : Ambient n} {E : Set (Ambient n)} (hv : v ∈ E) :
    Submodule.span ℝ (localCone v E : Set (Ambient n)) = vectorSpan ℝ E := by
  rw [vectorSpan_eq_span_vsub_set_right ℝ hv]
  change Submodule.span ℝ (PointedCone.hull ℝ ((fun p => p - v) '' E) : Set (Ambient n)) =
    Submodule.span ℝ ((fun p => p - v) '' E)
  apply le_antisymm
  · exact Submodule.span_le.mpr (PointedCone.hull_le_span ℝ _)
  · exact Submodule.span_mono PointedCone.subset_hull

theorem inwardDirections_linearIndependent {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) :
    LinearIndependent ℝ (fun i => embed (inwardBasisDirection b i)) := by
  apply LinearIndependent.of_comp (-dualCoordinates b)
  have he : (-dualCoordinates b) ∘ (fun i => embed (inwardBasisDirection b i)) =
      (Pi.basisFun ℝ (Fin n)) := by
    funext i
    ext j
    simp [Function.comp_def, dualCoordinates, embed_inwardBasisDirection,
      pairing_dualCorner_basis, Pi.single_apply, Pi.basisFun_apply]
    split_ifs <;> norm_num
  rw [he]
  exact (Pi.basisFun ℝ (Fin n)).linearIndependent

namespace SmoothReflexivePresentation

variable {n : ℕ} (P : SmoothReflexivePresentation n)

theorem localCone_eq_hull_inwardDirections (v : {v // v ∈ P.vertices}) :
    localCone (embed v.val) P.carrier =
      PointedCone.hull ℝ (Set.range (fun i => embed (inwardBasisDirection (P.basis v) i))) := by
  let dir := fun i => embed (inwardBasisDirection (P.basis v) i)
  have hmem (d : Ambient n) : d ∈ localCone (embed v.val) P.carrier ↔
      ∀ i, pairing d (P.basis v i) ≤ 0 := by
    have hconv : Convex ℝ P.carrier := convex_convexHull ℝ _
    exact (mem_localCone_iff hconv (P.vertex_mem v)).trans (P.exists_pos_feasible_iff v d)
  apply le_antisymm
  · intro d hd
    have hc : ∀ i, 0 ≤ -pairing d (P.basis v i) := fun i => neg_nonneg.mpr ((hmem d).mp hd i)
    have he : (∑ i, (-pairing d (P.basis v i)) • dir i) = d := by
      have hsurj : Function.Surjective (dualCoordinates (P.basis v)) :=
        fun s => ⟨dualCorner (P.basis v) s, dualCoordinates_dualCorner _ _⟩
      apply LinearMap.injective_iff_surjective.mpr hsurj
      rw [map_sum]
      simp only [map_smul]
      ext j
      simp [dir, dualCoordinates, embed_inwardBasisDirection, pairing_dualCorner_basis,
        Finset.sum_apply, Pi.smul_apply, Pi.single_apply]
    rw [← he]
    apply Submodule.sum_mem
    intro i _
    exact PointedCone.smul_mem _ (hc i) (PointedCone.subset_hull ⟨i, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro d ⟨i, rfl⟩
    apply (hmem _).mpr
    intro j
    change pairing (embed (inwardBasisDirection (P.basis v) i)) (P.basis v j) ≤ 0
    rw [embed_inwardBasisDirection, pairing_dualCorner_basis]
    simp [Pi.single_apply]
    split_ifs <;> norm_num

/-- Every actual one-dimensional convex face through a vertex has one of the
listed primitive inward directions. This is the exhaustiveness needed for the
geometric definition of the unit corner. -/
theorem edge_directions_exhaustive (v : {v // v ∈ P.vertices})
    (E : Set (Ambient n)) (hE : Convex ℝ E) (hEP : IsExtreme ℝ P.carrier E)
    (hv : embed v.val ∈ E) (hdim : Module.finrank ℝ (vectorSpan ℝ E) = 1) :
    ∃ i : Fin n, ∀ p ∈ E, ∃ t : ℝ, 0 ≤ t ∧
      p = embed v.val + t • embed (inwardBasisDirection (P.basis v) i) := by
  let C := localCone (embed v.val) P.carrier
  let F := localCone (embed v.val) E
  have hFC : F.IsFaceOf C := localCone_isFaceOf (convex_convexHull ℝ _) hE hEP hv
  have hdimF : Module.finrank ℝ (Submodule.span ℝ (F : Set (Ambient n))) = 1 := by
    rw [show (Submodule.span ℝ (F : Set (Ambient n))) = vectorSpan ℝ E from span_localCone hv]
    exact hdim
  let ρ : TauCeti.Toric.ToricRay C := ⟨⟨F, hFC⟩, hdimF⟩
  let dir := fun i => embed (inwardBasisDirection (P.basis v) i)
  have hli : LinearIndependent ℝ dir := inwardDirections_linearIndependent (P.basis v)
  have hC : C = PointedCone.hull ℝ (Set.range dir) := P.localCone_eq_hull_inwardDirections v
  let i := TauCeti.Toric.toricRayEquivOfLinearIndependent dir hli hC ρ
  have hi : dir i ∈ ρ :=
    (TauCeti.Toric.apply_mem_iff_toricRayEquivOfLinearIndependent dir hli hC ρ i).mpr rfl
  have hsalC : (C : ConvexCone ℝ (Ambient n)).Salient := by
    rw [hC]
    exact PointedCone.salient_hull_range hli
  have hsalF : (ρ.toPointedCone : ConvexCone ℝ (Ambient n)).Salient := hsalC.anti hFC.le
  have hF : F = PointedCone.hull ℝ {dir i} :=
    ρ.eq_hull_singleton hsalF hi (hli.ne_zero i)
  refine ⟨i, ?_⟩
  intro p hp
  have hm : p - embed v.val ∈ F := PointedCone.subset_hull ⟨p, hp, rfl⟩
  rw [hF] at hm
  obtain ⟨t, ht, he⟩ := PointedCone.mem_hull_singleton.mp hm
  refine ⟨t, ht, ?_⟩
  change p = embed v.val + t • dir i
  rw [he]
  abel

theorem edgeSlice_finrank (v : {v // v ∈ P.vertices}) (i : Fin n) :
    Module.finrank ℝ (vectorSpan ℝ (P.edgeSlice v i)) = 1 := by
  let d := embed (inwardBasisDirection (P.basis v) i)
  have hd : d ≠ 0 := (inwardDirections_linearIndependent (P.basis v)).ne_zero i
  have hspan : vectorSpan ℝ (P.edgeSlice v i) = ℝ ∙ d := by
    rw [vectorSpan_eq_span_vsub_set_right ℝ (P.vertex_mem_edgeSlice v i)]
    apply le_antisymm
    · apply Submodule.span_le.mpr
      rintro x ⟨p, hp, rfl⟩
      obtain ⟨t, ht, he⟩ := P.edgeSlice_subset_ray v i hp
      apply Submodule.mem_span_singleton.mpr
      refine ⟨t, ?_⟩
      change t • d = p - embed v.val
      rw [he]
      abel
    · apply Submodule.span_le.mpr
      rintro x (rfl : x = d)
      obtain ⟨t, ht, hp⟩ := P.exists_pos_mem_edgeSlice v i
      have hm : t • d ∈ Submodule.span ℝ ((fun p => p - embed v.val) '' P.edgeSlice v i) := by
        apply Submodule.subset_span
        refine ⟨embed v.val + t • d, hp, ?_⟩
        abel
      have hs := Submodule.smul_mem
        (Submodule.span ℝ ((fun p => p - embed v.val) '' P.edgeSlice v i)) t⁻¹ hm
      simpa [smul_smul, inv_mul_cancel₀ ht.ne'] using hs
  rw [hspan]
  exact finrank_span_singleton hd

/-- The geometric primitive inward edge directions, defined through actual
one-dimensional convex faces and actual positive feasible segments. -/
def primitiveEdgeDirections (v : {v // v ∈ P.vertices}) : Set (Lattice n) :=
  {d | PrimitiveLatticeVector d ∧ ∃ E : Set (Ambient n),
    Convex ℝ E ∧ IsExtreme ℝ P.carrier E ∧ embed v.val ∈ E ∧
    Module.finrank ℝ (vectorSpan ℝ E) = 1 ∧
    ∃ t : ℝ, 0 < t ∧ embed v.val + t • embed d ∈ E}

theorem inwardBasisDirection_mem_primitiveEdgeDirections
    (v : {v // v ∈ P.vertices}) (i : Fin n) :
    inwardBasisDirection (P.basis v) i ∈ P.primitiveEdgeDirections v :=
  ⟨inwardBasisDirection_primitive _ _, P.edgeSlice v i, P.edgeSlice_convex v i,
    P.edgeSlice_isExtreme v i, P.vertex_mem_edgeSlice v i, P.edgeSlice_finrank v i,
    P.exists_pos_mem_edgeSlice v i⟩

/-- There are exactly n primitive inward edge directions, with no additional
directions omitted by the unit-corner definition. -/
theorem primitiveEdgeDirections_eq_range (v : {v // v ∈ P.vertices}) :
    P.primitiveEdgeDirections v = Set.range (inwardBasisDirection (P.basis v)) := by
  apply Set.Subset.antisymm
  · rintro d ⟨hd, E, hE, hEP, hv, hdim, t, ht, htd⟩
    obtain ⟨i, hi⟩ := P.edge_directions_exhaustive v E hE hEP hv hdim
    obtain ⟨s, hs, he⟩ := hi _ htd
    let k : ℤ := -integerPairing d (P.basis v i)
    have hcoord (j : Fin n) :
        t * pairing (embed d) (P.basis v j) = s * (if i = j then -1 else 0) := by
      have h := congrArg (fun p => pairing p (P.basis v j)) he
      simp only [pairing_add_left, pairing_smul_left] at h
      rw [embed_inwardBasisDirection, pairing_dualCorner_basis] at h
      simpa [Pi.single_apply, eq_comm] using (add_left_cancel h)
    have hkreal : (0 : ℝ) ≤ (k : ℝ) := by
      have h := hcoord i
      simp only [ite_true] at h
      rw [pairing_embed] at h
      dsimp [k]
      push_cast
      nlinarith
    have hk : 0 ≤ k := by exact_mod_cast hkreal
    have hdeq : d = k • inwardBasisDirection (P.basis v) i := by
      have hsurj : Function.Surjective (dualCoordinates (P.basis v)) :=
        fun a => ⟨dualCorner (P.basis v) a, dualCoordinates_dualCorner _ _⟩
      have hembed : embed d = embed (k • inwardBasisDirection (P.basis v) i) := by
        apply LinearMap.injective_iff_surjective.mpr hsurj
        ext j
        change pairing (embed d) (P.basis v j) = pairing _ (P.basis v j)
        have hembed' : embed (k • inwardBasisDirection (P.basis v) i) =
            (k : ℝ) • embed (inwardBasisDirection (P.basis v) i) := by
          ext l
          simp [embed, Pi.smul_apply, smul_eq_mul]
        rw [hembed', pairing_smul_left, embed_inwardBasisDirection, pairing_dualCorner_basis]
        by_cases hij : i = j
        · subst j
          simp [Pi.single_apply, k, pairing_embed]
        · have h := hcoord j
          simp only [hij, ↓reduceIte, mul_zero] at h
          have hz : pairing (embed d) (P.basis v j) = 0 :=
            (mul_eq_zero.mp h).resolve_left ht.ne'
          simp [Pi.single_apply, hij, hz]
      ext j
      have hj := congrFun hembed j
      simp only [embed] at hj
      exact Int.cast_injective hj
    have hunit := hd k (inwardBasisDirection (P.basis v) i) hdeq
    have habs := Int.isUnit_iff_abs_eq.mp hunit
    have hkone : k = 1 := by rwa [abs_of_nonneg hk] at habs
    refine ⟨i, ?_⟩
    simpa [hkone] using hdeq.symm
  · rintro d ⟨i, rfl⟩
    exact P.inwardBasisDirection_mem_primitiveEdgeDirections v i

theorem sum_smul_inwardDirections (v : {v // v ∈ P.vertices}) (t : Ambient n) :
    (∑ i, t i • embed (inwardBasisDirection (P.basis v) i)) =
      -dualCorner (P.basis v) t := by
  have hsurj : Function.Surjective (dualCoordinates (P.basis v)) :=
    fun a => ⟨dualCorner (P.basis v) a, dualCoordinates_dualCorner _ _⟩
  apply LinearMap.injective_iff_surjective.mpr hsurj
  rw [map_sum, map_neg, dualCoordinates_dualCorner]
  simp only [map_smul]
  ext j
  simp [dualCoordinates, embed_inwardBasisDirection, pairing_dualCorner_basis,
    Finset.sum_apply, Pi.smul_apply, Pi.single_apply]

/-- The coordinate cube definition is precisely containment of the parallelepiped
spanned by all actual primitive inward edge directions at each vertex. -/
theorem unitCornersContained_iff_inwardParallelepiped :
    P.UnitCornersContained ↔
      ∀ v : {v // v ∈ P.vertices}, ∀ t : Ambient n,
        (∀ i, 0 ≤ t i ∧ t i ≤ 1) →
          embed v.val + (∑ i, t i • embed (inwardBasisDirection (P.basis v) i)) ∈ P.carrier := by
  simp only [UnitCornersContained, P.sum_smul_inwardDirections, ← sub_eq_add_neg]

end SmoothReflexivePresentation
end Unimodular

end

/-! ## DeepMonotone -/

noncomputable section

namespace Unimodular.SmoothReflexivePresentation

open scoped BigOperators

variable {n : ℕ} (P : SmoothReflexivePresentation n)

theorem primitiveEdgeDirections_finite (v : {v // v ∈ P.vertices}) :
    (P.primitiveEdgeDirections v).Finite := by
  rw [P.primitiveEdgeDirections_eq_range]
  exact Set.finite_range _

def primitiveEdgeFinset (v : {v // v ∈ P.vertices}) : Finset (Lattice n) :=
  (P.primitiveEdgeDirections_finite v).toFinset

theorem primitiveEdgeFinset_eq_image (v : {v // v ∈ P.vertices}) :
    P.primitiveEdgeFinset v = Finset.univ.image (inwardBasisDirection (P.basis v)) := by
  ext d
  simp [primitiveEdgeFinset, P.primitiveEdgeDirections_eq_range]

theorem inwardBasisDirection_injective (v : {v // v ∈ P.vertices}) :
    Function.Injective (inwardBasisDirection (P.basis v)) := by
  intro i j hij
  exact (inwardDirections_linearIndependent (P.basis v)).injective (congrArg embed hij)

/-- The corner is defined as the Minkowski sum of the unit segments along all
actual primitive inward edge vectors, translated to the vertex. -/
def geometricUnitCorner (v : {v // v ∈ P.vertices}) : Set (Ambient n) :=
  {p | ∃ c : Lattice n → ℝ,
    (∀ d ∈ P.primitiveEdgeFinset v, 0 ≤ c d ∧ c d ≤ 1) ∧
    embed v.val + ∑ d ∈ P.primitiveEdgeFinset v, c d • embed d = p}

def DeeplyMonotone : Prop :=
  ∀ v : {v // v ∈ P.vertices}, P.geometricUnitCorner v ⊆ P.carrier

/-- Formal equivalence of the geometric definition of deep monotonicity with
the dual coordinate cube used in the all-rank determinant proof. -/
theorem deeplyMonotone_iff_unitCornersContained : P.DeeplyMonotone ↔ P.UnitCornersContained := by
  rw [P.unitCornersContained_iff_inwardParallelepiped]
  constructor
  · intro h v t ht
    let f := inwardBasisDirection (P.basis v)
    let c : Lattice n → ℝ := Function.extend f t (fun _ => 0)
    have hf : Function.Injective f := P.inwardBasisDirection_injective v
    have hc (i : Fin n) : c (inwardBasisDirection (P.basis v) i) = t i :=
      hf.extend_apply t (fun _ => 0) i
    apply h v
    refine ⟨c, ?_, ?_⟩
    · intro d hd
      rw [P.primitiveEdgeFinset_eq_image] at hd
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hd
      simpa only [hc] using ht i
    · rw [P.primitiveEdgeFinset_eq_image, Finset.sum_image]
      · simp only [hc]
      · exact fun i _ j _ hij => hf hij
  · intro h v p hp
    obtain ⟨c, hc, rfl⟩ := hp
    rw [P.primitiveEdgeFinset_eq_image, Finset.sum_image]
    · apply h v
      intro i
      apply hc
      rw [P.primitiveEdgeFinset_eq_image]
      exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, rfl⟩
    · exact fun i _ j _ hij => P.inwardBasisDirection_injective v hij

/-- Corollary 6.2 in its geometric lattice-basis form. The hypothesis is actual
containment of the unit parallelepiped of all primitive inward edges. -/
theorem deeplyMonotone_facetNormals_uniform (hP : P.DeeplyMonotone)
    (a : Fin n → {u // u ∈ P.normals})
    (ha : LinearIndependent ℝ (fun i => embed (a i).val)) :
    ∃ b : Module.Basis (Fin n) ℤ (Lattice n), ∀ i, b i = (a i).val :=
  (uniform_iff_real_independent_is_basis (fun u : {u // u ∈ P.normals} => u.val)).mp
    (P.uniformlyUnimodular_of_unitCornersContained
      (P.deeplyMonotone_iff_unitCornersContained.mp hP)) a ha

end Unimodular.SmoothReflexivePresentation

namespace Unimodular.SmoothCompleteFan

variable {n : ℕ} (fan : SmoothCompleteFan n)

/-- The coordinate criterion produces an actual deeply monotone smooth
reflexive polytope with exactly the given primitive normals. -/
theorem polarPresentation_deeplyMonotone (hfan : fan.PositiveCoordinateCriterion) :
    (fan.polarPresentation hfan).DeeplyMonotone :=
  (fan.polarPresentation hfan).deeplyMonotone_iff_unitCornersContained.mpr
    (fan.polarPresentation_unitCornersContained hfan)

end Unimodular.SmoothCompleteFan

end

/-! Transitive axiom audit of every named declaration in this checking unit. -/
#print axioms Unimodular.real_independent_iff_integer_independent
#print axioms Unimodular.uniform_iff_real_independent_is_basis
#print axioms Unimodular.SmoothCompleteFan.real_independent_rays_form_lattice_basis
#print axioms Unimodular.IntegralRigidity.det_eq_mul_det
#print axioms Unimodular.IntegralRigidity.ambient_replace_det
#print axioms Unimodular.IntegralRigidity.exists_unique_lattice_equiv_of_chirotope
#print axioms Unimodular.IntegralRigidity.chirotope_of_lattice_equiv
#print axioms Unimodular.IntegralRigidity.lattice_equiv_iff_chirotope
#print axioms Unimodular.realPairing
#print axioms Unimodular.realPairing_add_left
#print axioms Unimodular.realPairing_smul_left
#print axioms Unimodular.pairing_add_left
#print axioms Unimodular.pairing_smul_left
#print axioms Unimodular.realPairing_dualCorner
#print axioms Unimodular.pairing_dualCorner_basis
#print axioms Unimodular.dualCoordinates
#print axioms Unimodular.dualCoordinates_dualCorner
#print axioms Unimodular.dualCorner_dualCoordinates
#print axioms Unimodular.dualCorner_sub
#print axioms Unimodular.exists_pos_feasible_step
#print axioms Unimodular.SmoothReflexivePresentation
#print axioms Unimodular.SmoothReflexivePresentation.carrier
#print axioms Unimodular.SmoothReflexivePresentation.mem_carrier_iff
#print axioms Unimodular.SmoothReflexivePresentation.vertex_mem
#print axioms Unimodular.SmoothReflexivePresentation.vertex_eq_dualCorner_one
#print axioms Unimodular.SmoothReflexivePresentation.exists_max_vertex
#print axioms Unimodular.SmoothReflexivePresentation.exists_nonnegative_basis_coordinates
#print axioms Unimodular.SmoothReflexivePresentation.UnitCornersContained
#print axioms Unimodular.SmoothReflexivePresentation.positive_coordinate_bound
#print axioms Unimodular.SmoothReflexivePresentation.uniformlyUnimodular_of_unitCornersContained
#print axioms Unimodular.integerPairing
#print axioms Unimodular.pairing_embed
#print axioms Unimodular.inwardBasisDirection
#print axioms Unimodular.embed_inwardBasisDirection
#print axioms Unimodular.integerPairing_inwardBasisDirection
#print axioms Unimodular.PrimitiveLatticeVector
#print axioms Unimodular.inwardBasisDirection_primitive
#print axioms Unimodular.SmoothReflexivePresentation.vertex_isExtremePoint
#print axioms Unimodular.SmoothReflexivePresentation.extremePoints_eq_vertices
#print axioms Unimodular.SmoothReflexivePresentation.exists_pos_feasible_iff
#print axioms Unimodular.SmoothReflexivePresentation.edgeSlice
#print axioms Unimodular.SmoothReflexivePresentation.vertex_mem_edgeSlice
#print axioms Unimodular.SmoothReflexivePresentation.edgeSlice_isExtreme
#print axioms Unimodular.SmoothReflexivePresentation.edgeSlice_convex
#print axioms Unimodular.SmoothReflexivePresentation.edgeSlice_subset_ray
#print axioms Unimodular.SmoothReflexivePresentation.exists_pos_mem_edgeSlice
#print axioms Unimodular.sum_nonpos_of_positive_mass_le_one
#print axioms Unimodular.SmoothCompleteFan.coordinate_sum_nonpos_of_not_basis_ray
#print axioms Unimodular.SmoothCompleteFan.strict_support_at_basis
#print axioms Unimodular.latticeDualVertex
#print axioms Unimodular.embed_latticeDualVertex
#print axioms Unimodular.realPairing_eq_coordinates
#print axioms Unimodular.linearMap_eq_realPairing
#print axioms Unimodular.SmoothCompleteFan.rayFinset
#print axioms Unimodular.SmoothCompleteFan.mem_rayFinset
#print axioms Unimodular.SmoothCompleteFan.dualVertices
#print axioms Unimodular.SmoothCompleteFan.dualVertices_nonempty
#print axioms Unimodular.SmoothCompleteFan.polar_eq_convexHull_dualVertices
#print axioms Unimodular.SmoothCompleteFan.vertexBasis
#print axioms Unimodular.SmoothCompleteFan.vertexBasis_mem
#print axioms Unimodular.SmoothCompleteFan.latticeDualVertex_vertexBasis
#print axioms Unimodular.SmoothCompleteFan.vertex_eq_dualCorner
#print axioms Unimodular.SmoothCompleteFan.polarPresentation
#print axioms Unimodular.SmoothCompleteFan.polarPresentation_unitCornersContained
#print axioms Unimodular.SmoothReflexivePresentation.normal_primitive
#print axioms Unimodular.SmoothReflexivePresentation.normal_irredundant
#print axioms Unimodular.SmoothReflexivePresentation.exists_only_one_active
#print axioms Unimodular.primitiveLatticeVector_iff_isPrimitive
#print axioms Unimodular.localCone
#print axioms Unimodular.mem_localCone_iff
#print axioms Unimodular.convex_feasible_step_mono
#print axioms Unimodular.localCone_isFaceOf
#print axioms Unimodular.span_localCone
#print axioms Unimodular.inwardDirections_linearIndependent
#print axioms Unimodular.SmoothReflexivePresentation.localCone_eq_hull_inwardDirections
#print axioms Unimodular.SmoothReflexivePresentation.edge_directions_exhaustive
#print axioms Unimodular.SmoothReflexivePresentation.edgeSlice_finrank
#print axioms Unimodular.SmoothReflexivePresentation.primitiveEdgeDirections
#print axioms Unimodular.SmoothReflexivePresentation.inwardBasisDirection_mem_primitiveEdgeDirections
#print axioms Unimodular.SmoothReflexivePresentation.primitiveEdgeDirections_eq_range
#print axioms Unimodular.SmoothReflexivePresentation.sum_smul_inwardDirections
#print axioms Unimodular.SmoothReflexivePresentation.unitCornersContained_iff_inwardParallelepiped
#print axioms Unimodular.SmoothReflexivePresentation.primitiveEdgeDirections_finite
#print axioms Unimodular.SmoothReflexivePresentation.primitiveEdgeFinset
#print axioms Unimodular.SmoothReflexivePresentation.primitiveEdgeFinset_eq_image
#print axioms Unimodular.SmoothReflexivePresentation.inwardBasisDirection_injective
#print axioms Unimodular.SmoothReflexivePresentation.geometricUnitCorner
#print axioms Unimodular.SmoothReflexivePresentation.DeeplyMonotone
#print axioms Unimodular.SmoothReflexivePresentation.deeplyMonotone_iff_unitCornersContained
#print axioms Unimodular.SmoothReflexivePresentation.deeplyMonotone_facetNormals_uniform
#print axioms Unimodular.SmoothCompleteFan.polarPresentation_deeplyMonotone

#check Unimodular.IntegralRigidity.lattice_equiv_iff_chirotope
#check Unimodular.SmoothCompleteFan.real_independent_rays_form_lattice_basis
#check Unimodular.SmoothReflexivePresentation.deeplyMonotone_facetNormals_uniform
#check Unimodular.SmoothCompleteFan.polarPresentation_deeplyMonotone

/-! Statement and definition audit: all arguments remain visible. -/
#check @Unimodular.SmoothReflexivePresentation.mk
#check @Unimodular.SmoothCompleteFan.real_independent_rays_form_lattice_basis
#check @Unimodular.SmoothReflexivePresentation.deeplyMonotone_facetNormals_uniform
#print Unimodular.PrimitiveLatticeVector
#print Unimodular.SmoothReflexivePresentation.primitiveEdgeDirections
#print Unimodular.SmoothReflexivePresentation.geometricUnitCorner
#print Unimodular.SmoothReflexivePresentation.DeeplyMonotone
