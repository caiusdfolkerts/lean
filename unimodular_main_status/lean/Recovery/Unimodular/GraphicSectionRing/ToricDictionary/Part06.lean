module

public import Recovery.Unimodular.GraphicSectionRing.ToricDictionary.Part05
public import Mathlib.Geometry.Convex.Cone.Face.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Tactic.Ring
public import Mathlib.Data.Finset.Powerset
public import Mathlib.Data.Set.Finite.Lemmas
public import Mathlib.Algebra.Order.Floor.Ring
public import Lean.Elab.Tactic.Omega

@[expose] public section
set_option autoImplicit false

section
-- BEGIN PaperVerification.ToricFanFoundations
/-!
# Actual finite smooth complete fans

Cones are genuine nonnegative real spans of finite lattice-vector sets.
The intersection axiom is equality of those actual cones, and smoothness
means that the ray generators form a subset of an integral basis. The
definition carries no primitive-relation or contraction conclusion.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical
open Set

section FiniteCones

variable {E ι : Type*} [AddCommGroup E] [Module ℝ E] [Fintype ι]

/-- The genuine nonnegative real span of a finite vector family. -/
def finiteRayCone (s : Finset E) : PointedCone ℝ E :=
  PointedCone.ofConeComb
    {x | ∃ c : E → ℝ, (∀ v ∈ s, 0 ≤ c v) ∧ ∑ v ∈ s, c v • v = x}
    ⟨0, fun _ => 0, by simp⟩ (by
      rintro x ⟨c, hc, hcx⟩ y ⟨d, hd, hdy⟩ a ha b hb
      refine ⟨fun v => a * c v + b * d v, ?_, ?_⟩
      · intro v hv
        exact add_nonneg (mul_nonneg ha (hc v hv)) (mul_nonneg hb (hd v hv))
      · simp only [add_smul, mul_smul, Finset.sum_add_distrib, ← Finset.smul_sum,
          hcx, hdy])

theorem finiteRayCone_generator (s : Finset E) {v : E} (hv : v ∈ s) :
    v ∈ finiteRayCone s := by
  classical
  refine ⟨Pi.single v (1 : ℝ), ?_, ?_⟩
  · intro w hw
    by_cases hwv : w = v <;> simp [Pi.single_apply, hwv]
  · simp [Pi.single_apply, ite_smul, hv]

/-- The explicit finite-combination definition agrees with Mathlib's conic hull. -/
theorem finiteRayCone_eq_hull (s : Finset E) :
    finiteRayCone s = PointedCone.hull ℝ (s : Set E) := by
  apply le_antisymm
  · rintro x ⟨c, hc, hcx⟩
    rw [← hcx]
    exact Submodule.sum_mem _ (fun v hv =>
      PointedCone.smul_mem _ (hc v hv) (PointedCone.subset_hull hv))
  · exact Submodule.span_le.mpr (fun v hv => finiteRayCone_generator s hv)

theorem finiteRayCone_mono {s t : Finset E} (hst : s ⊆ t) :
    finiteRayCone s ≤ finiteRayCone t := by
  rw [finiteRayCone_eq_hull, finiteRayCone_eq_hull]
  exact Submodule.span_mono hst

@[simp] theorem finiteRayCone_empty : finiteRayCone (∅ : Finset E) = ⊥ := by
  rw [finiteRayCone_eq_hull, Finset.coe_empty]
  exact Submodule.span_empty (R := Nonneg ℝ) (M := E)

/-- Coordinates in a cone on a basis subset are nonnegative and vanish exactly
outside that subset. -/
theorem mem_finiteRayCone_basis_iff (b : Module.Basis ι ℝ E) (I : Finset ι) (x : E) :
    x ∈ finiteRayCone (I.image b) ↔
      (∀ i, 0 ≤ b.repr x i) ∧ (∀ i ∉ I, b.repr x i = 0) := by
  classical
  constructor
  · rintro ⟨c, hc, hcx⟩
    have hcoord (i : ι) : b.repr x i = if i ∈ I then c (b i) else 0 := by
      rw [← hcx, Finset.sum_image]
      · simp [map_sum, map_smul, Finsupp.finsetSum_apply, Finsupp.smul_apply,
          Finsupp.single_apply, smul_eq_mul]
      · exact fun a _ b' _ hab => b.injective hab
    constructor
    · intro i
      rw [hcoord]
      split_ifs with hi
      · exact hc (b i) (Finset.mem_image.mpr ⟨i, hi, rfl⟩)
      · exact le_rfl
    · intro i hi
      rw [hcoord, if_neg hi]
  · rintro ⟨hxpos, hxzero⟩
    let c : E → ℝ := fun z => ∑ j, b.repr x j * b.repr z j
    have hc (i : ι) : c (b i) = b.repr x i := by
      simp [c, Finsupp.single_apply, mul_ite]
    refine ⟨c, ?_, ?_⟩
    · rintro z hz
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hz
      rw [hc]
      exact hxpos i
    · rw [Finset.sum_image]
      · simp only [hc]
        calc
          (∑ i ∈ I, b.repr x i • b i) = ∑ i, b.repr x i • b i := by
            apply Finset.sum_subset (Finset.subset_univ I)
            intro i _ hi
            rw [hxzero i hi, zero_smul]
          _ = x := b.sum_repr x
      · exact fun a _ b' _ hab => b.injective hab

/-- Every coordinate subcone is an actual face of the larger basis cone. -/
theorem finiteRayCone_basis_isFaceOf (b : Module.Basis ι ℝ E)
    {I J : Finset ι} (hIJ : I ⊆ J) :
    (finiteRayCone (I.image b)).IsFaceOf (finiteRayCone (J.image b)) := by
  refine ⟨finiteRayCone_mono (Finset.image_subset_image hIJ), ?_⟩
  intro x y a hx hy ha hxy
  obtain ⟨hxpos, hxzero⟩ := (mem_finiteRayCone_basis_iff b J x).mp hx
  obtain ⟨hypos, hyzero⟩ := (mem_finiteRayCone_basis_iff b J y).mp hy
  obtain ⟨hxypos, hxyzero⟩ := (mem_finiteRayCone_basis_iff b I (a • x + y)).mp hxy
  apply (mem_finiteRayCone_basis_iff b I x).mpr
  refine ⟨hxpos, ?_⟩
  intro i hi
  have hz := hxyzero i hi
  simp only [map_add, map_smul, Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at hz
  have hxi := hxpos i
  have hyi := hypos i
  nlinarith

/-- Intersections of coordinate cones in one basis are exactly the cones on
their common coordinates. -/
theorem finiteRayCone_basis_inter (b : Module.Basis ι ℝ E) (I J : Finset ι) :
    finiteRayCone (I.image b) ⊓ finiteRayCone (J.image b) =
      finiteRayCone ((I ∩ J).image b) := by
  ext x
  simp only [Submodule.mem_inf, mem_finiteRayCone_basis_iff]
  constructor
  · rintro ⟨⟨hx, hI⟩, ⟨_, hJ⟩⟩
    refine ⟨hx, ?_⟩
    intro i hi
    by_cases hiI : i ∈ I
    · exact hJ i (fun hiJ => hi (Finset.mem_inter.mpr ⟨hiI, hiJ⟩))
    · exact hI i hiI
  · rintro ⟨hx, hIJ⟩
    refine ⟨⟨hx, ?_⟩, ⟨hx, ?_⟩⟩
    · intro i hi
      exact hIJ i (fun h => hi (Finset.mem_inter.mp h).1)
    · intro i hi
      exact hIJ i (fun h => hi (Finset.mem_inter.mp h).2)

end FiniteCones

/-- The actual real cone generated by a finite set of integer rays. -/
def latticeRayCone {n : ℕ} (s : Finset (Lattice n)) : PointedCone ℝ (Ambient n) :=
  finiteRayCone (s.image (embed n))

theorem latticeRayCone_generator {n : ℕ} (s : Finset (Lattice n))
    {v : Lattice n} (hv : v ∈ s) : embed n v ∈ latticeRayCone s :=
  finiteRayCone_generator _ (Finset.mem_image.mpr ⟨v, hv, rfl⟩)

theorem latticeRayCone_mono {n : ℕ} {s t : Finset (Lattice n)} (hst : s ⊆ t) :
    latticeRayCone s ≤ latticeRayCone t :=
  finiteRayCone_mono (Finset.image_subset_image hst)

@[simp] theorem latticeRayCone_empty {n : ℕ} :
    latticeRayCone (∅ : Finset (Lattice n)) = ⊥ := by
  simp [latticeRayCone]

theorem latticeRayCone_basis {n : ℕ} (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)) :
    latticeRayCone (I.image b) = finiteRayCone (I.image (integralBasisReal b)) := by
  change finiteRayCone ((I.image b).image (embed n)) = _
  congr 1
  ext x
  simp only [Finset.mem_image]
  constructor
  · rintro ⟨z, ⟨i, hi, rfl⟩, rfl⟩
    exact ⟨i, hi, integralBasisReal_apply b i⟩
  · rintro ⟨i, hi, rfl⟩
    exact ⟨b i, ⟨i, hi, rfl⟩, (integralBasisReal_apply b i).symm⟩

/-- Membership in a cone on an integral basis is exactly nonnegativity of
the real coordinates, with zero coordinates outside the chosen subset. -/
theorem mem_latticeRayCone_basis_iff {n : ℕ}
    (b : Module.Basis (Fin n) ℤ (Lattice n)) (I : Finset (Fin n))
    (x : Ambient n) :
    x ∈ latticeRayCone (I.image b) ↔
      (∀ i, 0 ≤ (integralBasisReal b).repr x i) ∧
        (∀ i ∉ I, (integralBasisReal b).repr x i = 0) := by
  rw [latticeRayCone_basis]
  have hI : I.image (integralBasisReal b) =
      @Finset.image (Fin n) (Ambient n)
        (fun (a b : Ambient n) => Classical.propDecidable (a = b))
        (integralBasisReal b) I := by
    ext y
    simp only [Finset.mem_image]
  rw [hI]
  exact mem_finiteRayCone_basis_iff (integralBasisReal b) I x

/-- A finite smooth complete fan, stated entirely in terms of actual lattice
rays and actual cones. Every cone is a subset of a genuine integral basis;
intersections agree with their common-ray faces, and all real vectors are covered. -/
structure SmoothCompleteFan (n : ℕ) where
  cones : Finset (Finset (Lattice n))
  smooth : ∀ s ∈ cones, ∃ (b : Module.Basis (Fin n) ℤ (Lattice n))
    (I : Finset (Fin n)), s = I.image b
  downward : ∀ s ∈ cones, ∀ t, t ⊆ s → t ∈ cones
  intersection : ∀ s ∈ cones, ∀ t ∈ cones,
    latticeRayCone s ⊓ latticeRayCone t = latticeRayCone (s ∩ t)
  complete : ∀ x : Ambient n, ∃ s ∈ cones, x ∈ latticeRayCone s

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

/-- Every cone is contained in a cone with the full ambient number of rays.
This property is derived for normal fans and preserved by subdivision; it
is not included as extra data in `SmoothCompleteFan`. -/
def IsPure : Prop :=
  ∀ s ∈ «Σ».cones, ∃ u ∈ «Σ».cones, s ⊆ u ∧ u.card = n

/-- A full-dimensional smooth cone has the whole of a genuine integral
basis as its ray set. -/
theorem full_cone_basis {s : Finset (Lattice n)}
    (hs : s ∈ «Σ».cones) (hcard : s.card = n) :
    ∃ b : Module.Basis (Fin n) ℤ (Lattice n), s = Finset.univ.image b := by
  obtain ⟨b, I, rfl⟩ := «Σ».smooth s hs
  rw [Finset.card_image_of_injective I b.injective] at hcard
  have hI : I = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ I)
    simpa only [Finset.card_fin, hcard] using (le_rfl : n ≤ n)
  exact ⟨b, by rw [hI]⟩

/-- The actual collection of real cones represented by the finite fan. -/
def realCones : Set (Set (Ambient n)) :=
  {C | ∃ s ∈ «Σ».cones, C = (latticeRayCone s : Set (Ambient n))}

/-- The finite set of primitive ray generators occurring in the fan. -/
def rays : Finset (Lattice n) := «Σ».cones.biUnion id

theorem mem_rays_iff (v : Lattice n) :
    v ∈ «Σ».rays ↔ ∃ s ∈ «Σ».cones, v ∈ s := by
  classical
  simp [rays]

theorem empty_mem : (∅ : Finset (Lattice n)) ∈ «Σ».cones := by
  obtain ⟨s, hs, hx⟩ := «Σ».complete 0
  exact «Σ».downward s hs ∅ (Finset.empty_subset s)

theorem singleton_mem_of_mem_rays {v : Lattice n} (hv : v ∈ «Σ».rays) :
    {v} ∈ «Σ».cones := by
  obtain ⟨s, hs, hvs⟩ := («Σ».mem_rays_iff v).mp hv
  exact «Σ».downward s hs {v} (Finset.singleton_subset_iff.mpr hvs)

/-- Every nonempty finite intersection of actual fan cones is an actual cone
of the same fan. The nonempty condition avoids introducing the whole ambient
space as an extra cone. -/
theorem exists_cone_finite_intersection {κ : Type*}
    (K : Finset κ) (t : κ → Finset (Lattice n)) :
    K.Nonempty → (∀ i ∈ K, t i ∈ «Σ».cones) →
      ∃ s ∈ «Σ».cones, ∀ x : Ambient n,
        x ∈ latticeRayCone s ↔ ∀ i ∈ K, x ∈ latticeRayCone (t i) := by
  classical
  induction K using Finset.induction_on with
  | empty => simp
  | @insert i K hi ih =>
    intro hne hmem
    have hti : t i ∈ «Σ».cones := hmem i (Finset.mem_insert_self i K)
    by_cases hK : K.Nonempty
    · obtain ⟨s, hs, hspec⟩ := ih hK
        (fun j hj => hmem j (Finset.mem_insert_of_mem hj))
      refine ⟨t i ∩ s, «Σ».downward (t i) hti _ Finset.inter_subset_left, ?_⟩
      intro x
      rw [← «Σ».intersection (t i) hti s hs]
      simp only [Submodule.mem_inf, hspec x, Finset.forall_mem_insert]
    · have hempty : K = ∅ := Finset.not_nonempty_iff_eq_empty.mp hK
      subst K
      exact ⟨t i, hti, by simp⟩

theorem ray_ne_zero {v : Lattice n} (hv : v ∈ «Σ».rays) : v ≠ 0 := by
  obtain ⟨s, hs, hvs⟩ := («Σ».mem_rays_iff v).mp hv
  obtain ⟨b, I, rfl⟩ := «Σ».smooth s hs
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hvs
  exact b.ne_zero i

/-- Every listed ray is primitive in the actual ambient integer lattice. -/
theorem ray_gcd_eq_one {v : Lattice n} (hv : v ∈ «Σ».rays) :
    Finset.univ.gcd (fun i : Fin n => (v i).natAbs) = 1 := by
  obtain ⟨s, hs, hvs⟩ := («Σ».mem_rays_iff v).mp hv
  obtain ⟨b, I, rfl⟩ := «Σ».smooth s hs
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hvs
  exact lattice_basis_vector_gcd_one b i

/-- A subset of the rays of a smooth cone generates an actual face of it. -/
theorem cone_subset_isFaceOf {s t : Finset (Lattice n)}
    (hs : s ∈ «Σ».cones) (hts : t ⊆ s) :
    PointedCone.IsFaceOf (R := ℝ) (M := Ambient n)
      (latticeRayCone t) (latticeRayCone s) := by
  classical
  obtain ⟨b, I, rfl⟩ := «Σ».smooth s hs
  let J := I.filter (fun i => b i ∈ t)
  have hJ : J.image b = t := by
    ext v
    constructor
    · rintro hv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
      exact (Finset.mem_filter.mp hi).2
    · intro hv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp (hts hv)
      exact Finset.mem_image.mpr ⟨i, Finset.mem_filter.mpr ⟨hi, hv⟩, rfl⟩
  have hK (K : Finset (Fin n)) :
      finiteRayCone (@Finset.image (Fin n) (Ambient n)
        (fun (x y : Ambient n) => Classical.propDecidable (x = y))
        (integralBasisReal b) K) = latticeRayCone (K.image b) := by
    ext x
    exact (mem_finiteRayCone_basis_iff (integralBasisReal b) K x).trans
      (mem_latticeRayCone_basis_iff b K x).symm
  have hface := finiteRayCone_basis_isFaceOf (integralBasisReal b)
    (I := J) (J := I) (Finset.filter_subset (fun i => b i ∈ t) I)
  rw [hK J, hK I, hJ] at hface
  exact hface

/-- A ray of the fan lies in a fan cone precisely when it is one of that
cone's listed primitive rays. This follows from actual cone intersections. -/
theorem ray_mem_cone_iff {s : Finset (Lattice n)} (hs : s ∈ «Σ».cones)
    {v : Lattice n} (hv : v ∈ «Σ».rays) : embed n v ∈ latticeRayCone s ↔ v ∈ s := by
  constructor
  · intro hvin
    by_contra hnot
    have hsing := «Σ».singleton_mem_of_mem_rays hv
    have hmeet : embed n v ∈ latticeRayCone ({v} ∩ s) := by
      rw [← «Σ».intersection {v} hsing s hs]
      exact ⟨latticeRayCone_generator {v} (Finset.mem_singleton_self v), hvin⟩
    have hempty : ({v} : Finset (Lattice n)) ∩ s = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro w hw
      obtain ⟨hwv, hws⟩ := Finset.mem_inter.mp hw
      exact hnot ((Finset.mem_singleton.mp hwv) ▸ hws)
    rw [hempty, latticeRayCone_empty] at hmeet
    have hz : embed n v = 0 := (Submodule.mem_bot (Nonneg ℝ)).mp hmeet
    exact «Σ».ray_ne_zero hv ((embed_injective n) (by simpa using hz))
  · exact latticeRayCone_generator s

/-- The positive sum of all rays of a fan cone can lie in another cone only
when every one of those rays lies in the other cone. -/
theorem sum_mem_cone_implies_subset {s t : Finset (Lattice n)}
    (hs : s ∈ «Σ».cones) (ht : t ∈ «Σ».cones)
    (hsum : (∑ v ∈ s, embed n v) ∈ latticeRayCone t) : s ⊆ t := by
  classical
  have hsumS : (∑ v ∈ s, embed n v) ∈ latticeRayCone s :=
    Submodule.sum_mem _ (fun v hv => latticeRayCone_generator s hv)
  have hmeet : (∑ v ∈ s, embed n v) ∈ latticeRayCone (s ∩ t) := by
    rw [← «Σ».intersection s hs t ht]
    exact ⟨hsumS, hsum⟩
  have hface := «Σ».cone_subset_isFaceOf hs (Finset.inter_subset_left : s ∩ t ⊆ s)
  intro v hv
  have hvmeet : embed n v ∈ latticeRayCone (s ∩ t) := by
    have hrest : (∑ w ∈ s.erase v, embed n w) ∈ latticeRayCone s :=
      Submodule.sum_mem _ (fun w hw =>
        latticeRayCone_generator s (Finset.mem_of_mem_erase hw))
    apply hface.mem_of_add_mem_left (latticeRayCone_generator s hv) hrest
    simpa only [Finset.add_sum_erase s (fun w => embed n w) hv] using hmeet
  have hvrays : v ∈ «Σ».rays := («Σ».mem_rays_iff v).mpr ⟨s, hs, hv⟩
  have hvin : v ∈ s ∩ t := («Σ».ray_mem_cone_iff
    («Σ».downward s hs (s ∩ t) Finset.inter_subset_left) hvrays).mp hvmeet
  exact (Finset.mem_inter.mp hvin).2

/-- The same support implication for every strictly positive real weighting
of the source cone's rays. This characterizes its relative interior support. -/
theorem positive_sum_mem_cone_implies_subset {s t : Finset (Lattice n)}
    (hs : s ∈ «Σ».cones) (ht : t ∈ «Σ».cones) (c : Lattice n → ℝ)
    (hc : ∀ v ∈ s, 0 < c v)
    (hsum : (∑ v ∈ s, c v • embed n v) ∈ latticeRayCone t) : s ⊆ t := by
  classical
  have hsumS : (∑ v ∈ s, c v • embed n v) ∈ latticeRayCone s :=
    Submodule.sum_mem _ (fun v hv =>
      PointedCone.smul_mem _ (hc v hv).le (latticeRayCone_generator s hv))
  have hmeet : (∑ v ∈ s, c v • embed n v) ∈ latticeRayCone (s ∩ t) := by
    rw [← «Σ».intersection s hs t ht]
    exact ⟨hsumS, hsum⟩
  have hface := «Σ».cone_subset_isFaceOf hs (Finset.inter_subset_left : s ∩ t ⊆ s)
  intro v hv
  have hvmeet : embed n v ∈ latticeRayCone (s ∩ t) := by
    have hrest : (∑ w ∈ s.erase v, c w • embed n w) ∈ latticeRayCone s :=
      Submodule.sum_mem _ (fun w hw =>
        PointedCone.smul_mem _ (hc w (Finset.mem_of_mem_erase hw)).le
          (latticeRayCone_generator s (Finset.mem_of_mem_erase hw)))
    apply hface.mem_of_smul_add_mem (latticeRayCone_generator s hv) hrest (hc v hv)
    simpa only [Finset.add_sum_erase s (fun w => c w • embed n w) hv] using hmeet
  have hvrays : v ∈ «Σ».rays := («Σ».mem_rays_iff v).mpr ⟨s, hs, hv⟩
  have hvin : v ∈ s ∩ t := («Σ».ray_mem_cone_iff
    («Σ».downward s hs (s ∩ t) Finset.inter_subset_left) hvrays).mp hvmeet
  exact (Finset.mem_inter.mp hvin).2

/-- Every integer vector has a positive integral expansion on the rays of
some cone. The cone may be the zero cone. Integrality follows from an actual
integral basis; completeness alone would only supply real coefficients. -/
theorem exists_positive_integral_cone_expansion (z : Lattice n) :
    ∃ t ∈ «Σ».cones, ∃ c : Lattice n → ℕ,
      (∀ v ∈ t, 0 < c v) ∧ ∑ v ∈ t, (c v : ℤ) • v = z := by
  classical
  obtain ⟨s, hs, hz⟩ := «Σ».complete (embed n z)
  obtain ⟨b, I, hI⟩ := «Σ».smooth s hs
  have hz' : embed n z ∈ latticeRayCone (I.image b) := by
    rw [← hI]
    exact hz
  obtain ⟨hpos, hzero⟩ := (mem_latticeRayCone_basis_iff b I (embed n z)).mp hz'
  have hposZ (i : Fin n) : 0 ≤ b.repr z i := by
    have h := hpos i
    rw [integralBasisReal_repr] at h
    exact_mod_cast h
  have hzeroZ (i : Fin n) (hi : i ∉ I) : b.repr z i = 0 := by
    have h := hzero i hi
    rw [integralBasisReal_repr] at h
    exact Int.cast_eq_zero.mp h
  have hcast (i : Fin n) : ((b.repr z i).toNat : ℤ) = b.repr z i :=
    Int.toNat_of_nonneg (hposZ i)
  let J := I.filter (fun i => 0 < b.repr z i)
  let t := J.image b
  let c : Lattice n → ℕ := fun v => ∑ i, (b.repr z i).toNat * (b.repr v i).toNat
  have hc (i : Fin n) : c (b i) = (b.repr z i).toNat := by
    simp [c, Finsupp.single_apply, apply_ite, mul_ite]
  have ht : t ∈ «Σ».cones := by
    apply «Σ».downward s hs t
    rw [hI]
    exact Finset.image_subset_image (Finset.filter_subset _ _)
  refine ⟨t, ht, c, ?_, ?_⟩
  · intro v hv
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hv
    rw [hc]
    have h := (Finset.mem_filter.mp hi).2
    omega
  · rw [Finset.sum_image]
    · simp only [hc, hcast]
      calc
        (∑ i ∈ J, b.repr z i • b i) = ∑ i, b.repr z i • b i := by
          apply Finset.sum_subset (Finset.subset_univ J)
          intro i _ hi
          have hzi : b.repr z i = 0 := by
            by_cases hiI : i ∈ I
            · have hnot : ¬ 0 < b.repr z i := by
                intro hp
                exact hi (Finset.mem_filter.mpr ⟨hiI, hp⟩)
              exact le_antisymm (le_of_not_gt hnot) (hposZ i)
            · exact hzeroZ i hiI
          rw [hzi, zero_smul]
        _ = z := b.sum_repr z
    · exact fun i _ j _ hij => b.injective hij

/-- Smooth cones have at most the ambient dimension many rays. -/
theorem card_cone_le {s : Finset (Lattice n)} (hs : s ∈ «Σ».cones) : s.card ≤ n := by
  obtain ⟨b, I, rfl⟩ := «Σ».smooth s hs
  rw [Finset.card_image_of_injective I b.injective]
  calc
    I.card ≤ (Finset.univ : Finset (Fin n)).card := Finset.card_le_card (Finset.subset_univ I)
    _ = n := Finset.card_fin n

/-- A primitive collection is an inclusion-minimal collection of rays that
does not generate a cone of the fan. -/
def IsPrimitiveCollection (P : Finset (Lattice n)) : Prop :=
  P ⊆ «Σ».rays ∧ P ∉ «Σ».cones ∧ ∀ S, S ⊂ P → S ∈ «Σ».cones

theorem primitiveCollection_nonempty {P : Finset (Lattice n)}
    (hP : «Σ».IsPrimitiveCollection P) : P.Nonempty := by
  by_contra h
  have hzero := Finset.not_nonempty_iff_eq_empty.mp h
  exact hP.2.1 (hzero.symm ▸ «Σ».empty_mem)

theorem primitiveCollection_card_bounds {P : Finset (Lattice n)}
    (hP : «Σ».IsPrimitiveCollection P) : 2 ≤ P.card ∧ P.card ≤ n + 1 := by
  classical
  obtain ⟨v, hv⟩ := «Σ».primitiveCollection_nonempty hP
  have herase : P.erase v ∈ «Σ».cones := hP.2.2 _ (Finset.erase_ssubset hv)
  have hcard := «Σ».card_cone_le herase
  have hneone : P.card ≠ 1 := by
    intro hone
    obtain ⟨w, hw⟩ := Finset.card_eq_one.mp hone
    have hwrays : w ∈ «Σ».rays := hP.1 (hw.symm ▸ Finset.mem_singleton_self w)
    exact hP.2.1 (hw.symm ▸ «Σ».singleton_mem_of_mem_rays hwrays)
  have hpos := Finset.card_pos.mpr ⟨v, hv⟩
  rw [Finset.card_erase_of_mem hv] at hcard
  omega

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
-- END PaperVerification.ToricFanFoundations
end

section
-- BEGIN PaperVerification.ToricPrimitiveRelations
/-!
# Primitive relations in actual smooth complete fans

A primitive relation is obtained by expanding the sum of a minimal noncone
collection in the unique positive cone of the fan. Positivity and integrality
are proved from completeness and smoothness. Disjointness of its positive and
negative rays is a theorem, not part of the definition.

The combinatorial contractibility condition below is precisely the cone
replacement condition in Casagrande, Theorem 2.2(ii). No equivalence with a
scheme-level contraction is asserted here without a separate proof.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open scoped BigOperators Classical

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

/-- A primitive relation with genuine positive integral coefficients in its
focus cone. The ray sets need not be assumed disjoint. -/
structure PrimitiveRelation where
  positive : Finset (Lattice n)
  negative : Finset (Lattice n)
  coefficient : Lattice n → ℕ
  primitive : «Σ».IsPrimitiveCollection positive
  negative_cone : negative ∈ «Σ».cones
  coefficient_pos : ∀ v ∈ negative, 0 < coefficient v
  equation : ∑ v ∈ positive, v = ∑ v ∈ negative, (coefficient v : ℤ) • v

/-- Every primitive collection has a primitive relation; no relation is
postulated independently of the actual lattice vectors. -/
theorem exists_primitiveRelation {P : Finset (Lattice n)}
    (hP : «Σ».IsPrimitiveCollection P) :
    ∃ R : «Σ».PrimitiveRelation, R.positive = P := by
  obtain ⟨t, ht, c, hc, he⟩ := «Σ».exists_positive_integral_cone_expansion (∑ v ∈ P, v)
  exact ⟨⟨P, t, c, hP, ht, hc, he.symm⟩, rfl⟩

namespace PrimitiveRelation

variable {«Σ»} (R : «Σ».PrimitiveRelation)

/-- A primitive collection is disjoint from the focus of its relation
(Batyrev's primitive-collection disjointness lemma). -/
theorem disjoint : Disjoint R.positive R.negative := by
  classical
  apply Finset.disjoint_left.mpr
  intro x hxP hxT
  let P' := R.positive.erase x
  have hP' : P' ∈ «Σ».cones := R.primitive.2.2 _ (Finset.erase_ssubset hxP)
  let d : Lattice n → ℝ := fun v =>
    (R.coefficient v : ℝ) - if v = x then 1 else 0
  have hd (v : Lattice n) (hv : v ∈ R.negative) : 0 ≤ d v := by
    by_cases hvx : v = x
    · subst v
      have hx : (1 : ℝ) ≤ R.coefficient x := by exact_mod_cast R.coefficient_pos x hxT
      simp only [d, if_pos rfl, ite_true]
      linarith
    · simp only [d, if_neg hvx, sub_zero]
      exact Nat.cast_nonneg _
  have he : (∑ v ∈ R.negative, (R.coefficient v : ℝ) • embed n v) =
      ∑ v ∈ R.positive, embed n v := by
    have h := congrArg (embed n) R.equation
    simpa only [map_sum, embed_int_smul, Int.cast_natCast] using h.symm
  have hdsum : (∑ v ∈ R.negative, d v • embed n v) = ∑ v ∈ P', embed n v := by
    calc
      (∑ v ∈ R.negative, d v • embed n v) =
          (∑ v ∈ R.negative, (R.coefficient v : ℝ) • embed n v) - embed n x := by
        simp [d, sub_smul, Finset.sum_sub_distrib, ite_smul, hxT]
      _ = (∑ v ∈ R.positive, embed n v) - embed n x := by rw [he]
      _ = ∑ v ∈ P', embed n v := by
        rw [← Finset.sum_erase_add R.positive (fun v => embed n v) hxP]
        simp [P']
  have hsumCone : (∑ v ∈ P', embed n v) ∈ latticeRayCone R.negative := by
    rw [← hdsum]
    exact Submodule.sum_mem _ (fun v hv =>
      PointedCone.smul_mem _ (hd v hv) (latticeRayCone_generator R.negative hv))
  have hsubset : P' ⊆ R.negative :=
    «Σ».sum_mem_cone_implies_subset hP' R.negative_cone hsumCone
  have hall : R.positive ⊆ R.negative := by
    intro v hv
    by_cases hvx : v = x
    · simpa only [hvx] using hxT
    · exact hsubset (Finset.mem_erase.mpr ⟨hvx, hv⟩)
  exact R.primitive.2.1 («Σ».downward R.negative R.negative_cone R.positive hall)

/-- The positive focus cone is uniquely determined by the primitive collection. -/
theorem negative_unique (S : «Σ».PrimitiveRelation) (hPS : R.positive = S.positive) :
    R.negative = S.negative := by
  have hincl (R S : «Σ».PrimitiveRelation) (hPS : R.positive = S.positive) :
      R.negative ⊆ S.negative := by
    have he : (∑ v ∈ R.negative, (R.coefficient v : ℝ) • embed n v) =
        ∑ v ∈ S.negative, (S.coefficient v : ℝ) • embed n v := by
      have hZ : (∑ v ∈ R.negative, (R.coefficient v : ℤ) • v) =
          ∑ v ∈ S.negative, (S.coefficient v : ℤ) • v := by
        rw [← R.equation, ← S.equation, hPS]
      simpa only [map_sum, embed_int_smul, Int.cast_natCast] using congrArg (embed n) hZ
    apply «Σ».positive_sum_mem_cone_implies_subset R.negative_cone S.negative_cone
      (fun v => (R.coefficient v : ℝ)) (fun v hv => by exact_mod_cast R.coefficient_pos v hv)
    rw [he]
    exact Submodule.sum_mem _ (fun v hv => PointedCone.smul_mem _ (Nat.cast_nonneg _)
      (latticeRayCone_generator S.negative hv))
  exact Finset.Subset.antisymm (hincl R S hPS) (hincl S R hPS.symm)

/-- The positive integer coefficients on the focus are unique as well.
They are read off in a genuine integral basis containing that cone. -/
theorem coefficient_unique_on_negative (S : «Σ».PrimitiveRelation)
    (hPS : R.positive = S.positive) {v : Lattice n} (hv : v ∈ R.negative) :
    R.coefficient v = S.coefficient v := by
  have hN := R.negative_unique S hPS
  obtain ⟨b, I, hI⟩ := «Σ».smooth R.negative R.negative_cone
  obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp (hI ▸ hv)
  have hsum (c : Lattice n → ℕ) :
      b.repr (∑ v ∈ R.negative, (c v : ℤ) • v) j = (c (b j) : ℤ) := by
    rw [hI, Finset.sum_image]
    · simp only [map_sum, LinearEquiv.map_smul, Finsupp.finsetSum_apply,
        Finsupp.smul_apply, Module.Basis.repr_self_apply]
      simp [hj, smul_eq_mul]
    · exact fun i _ k _ hik => b.injective hik
  have he : (∑ v ∈ R.negative, (R.coefficient v : ℤ) • v) =
      ∑ v ∈ R.negative, (S.coefficient v : ℤ) • v := by
    rw [R.equation.symm, hN, S.equation.symm, hPS]
  have hc := congrArg (fun z : Lattice n => b.repr z j) he
  rw [hsum, hsum] at hc
  exact_mod_cast hc

/-- The number `r` in the manuscript's relation `x₀+...+xᵣ = Σ aⱼyⱼ`. -/
def fiberDimension : ℕ := R.positive.card - 1

theorem fiberDimension_pos : 1 ≤ R.fiberDimension := by
  have h := («Σ».primitiveCollection_card_bounds R.primitive).1
  unfold fiberDimension
  omega

/-- The exact combinatorial replacement condition used in the contraction
theorem. It is a condition on all actual cones of the fan. -/
def IsCombinatoriallyContractible : Prop :=
  ∀ ν ∈ «Σ».cones, Disjoint ν (R.positive ∪ R.negative) →
    R.negative ∪ ν ∈ «Σ».cones → ∀ x ∈ R.positive,
      (R.positive.erase x) ∪ R.negative ∪ ν ∈ «Σ».cones

/-- The core negative rays and all but one positive ray form a genuine cone
for every combinatorially contractible relation. -/
theorem contractible_core_cone (hR : R.IsCombinatoriallyContractible)
    {x : Lattice n} (hx : x ∈ R.positive) :
    R.positive.erase x ∪ R.negative ∈ «Σ».cones := by
  simpa only [Finset.union_empty] using
    hR ∅ «Σ».empty_mem (Finset.disjoint_empty_left _) (by simpa using R.negative_cone) x hx

/-- The dimension inequality `r+q≤n` follows from a genuine smooth cone and
the proved disjointness, rather than being included as relation data. -/
theorem contractible_dimension_bound (hR : R.IsCombinatoriallyContractible) :
    R.fiberDimension + R.negative.card ≤ n := by
  obtain ⟨x, hx⟩ := «Σ».primitiveCollection_nonempty R.primitive
  have h := «Σ».card_cone_le (R.contractible_core_cone hR hx)
  rw [Finset.card_union_of_disjoint
    (R.disjoint.mono_left (Finset.erase_subset x R.positive)),
    Finset.card_erase_of_mem hx] at h
  exact h

/-- No cone contains the entire positive primitive collection. Consequently
it contains at most `r` positive rays. -/
theorem positive_rays_in_cone_bound {s : Finset (Lattice n)} (hs : s ∈ «Σ».cones) :
    (R.positive ∩ s).card ≤ R.fiberDimension := by
  have hproper : R.positive ∩ s ⊂ R.positive := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.inter_subset_left, ?_⟩
    intro heq
    have hsub : R.positive ⊆ s := by
      rw [← heq]
      exact Finset.inter_subset_right
    exact R.primitive.2.1 («Σ».downward s hs R.positive hsub)
  have hcard := Finset.card_lt_card hproper
  unfold fiberDimension
  omega

/-- Pairing the primitive relation with arbitrary real invariant divisor
coefficients. This is the actual displayed coefficient pairing. -/
def degree (a : Lattice n → ℝ) : ℝ :=
  (∑ v ∈ R.positive, a v) - ∑ v ∈ R.negative, (R.coefficient v : ℝ) * a v

theorem degree_unique (S : «Σ».PrimitiveRelation) (hP : R.positive = S.positive)
    (a : Lattice n → ℝ) : R.degree a = S.degree a := by
  have hN := R.negative_unique S hP
  have hsum : (∑ v ∈ R.negative, (R.coefficient v : ℝ) * a v) =
      ∑ v ∈ R.negative, (S.coefficient v : ℝ) * a v := by
    apply Finset.sum_congr rfl
    intro v hv
    rw [R.coefficient_unique_on_negative S hP hv]
  unfold degree
  rw [hsum, hP, hN]

theorem degree_add (a b : Lattice n → ℝ) : R.degree (a + b) = R.degree a + R.degree b := by
  simp only [degree, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  ring

theorem degree_sub (a b : Lattice n → ℝ) : R.degree (a - b) = R.degree a - R.degree b := by
  simp only [degree, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]
  ring

theorem degree_smul (t : ℝ) (a : Lattice n → ℝ) :
    R.degree (t • a) = t * R.degree a := by
  simp only [degree, Pi.smul_apply, smul_eq_mul, mul_sub, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro v hv
  ring

/-- A selection of invariant divisors from a cone has relation degree at most
`r`: the cone omits at least one positive ray, and all negative contributions
can only lower the degree. This is the numerical bound in Lemma 3.1. -/
theorem degree_cone_selection_le {s t : Finset (Lattice n)}
    (hs : s ∈ «Σ».cones) (hts : t ⊆ s) :
    R.degree (fun v => if v ∈ t then 1 else 0) ≤ R.fiberDimension := by
  have hnegative : 0 ≤ ∑ v ∈ R.negative,
      (R.coefficient v : ℝ) * (if v ∈ t then 1 else 0) := by
    apply Finset.sum_nonneg
    intro v hv
    split_ifs <;> simp
  have hpos : (∑ v ∈ R.positive, if v ∈ t then (1 : ℝ) else 0) =
      ((R.positive ∩ t).card : ℝ) := by
    rw [Finset.sum_boole]
    congr 1
  have hcard : (R.positive ∩ t).card ≤ R.fiberDimension :=
    (Finset.card_le_card (Finset.inter_subset_inter_left hts)).trans
      (R.positive_rays_in_cone_bound hs)
  have hcardR : ((R.positive ∩ t).card : ℝ) ≤ R.fiberDimension := by exact_mod_cast hcard
  unfold degree
  rw [hpos]
  linarith

/-- The corner-criterion hypothesis makes every selected-divisor subtraction
nonnegative on that primitive relation. -/
theorem degree_sub_corner_selection_nonneg {s t : Finset (Lattice n)}
    (hs : s ∈ «Σ».cones) (hts : t ⊆ s) (a : Lattice n → ℝ) (side : ℝ)
    (hside : 0 ≤ side) (hdegree : side * R.fiberDimension ≤ R.degree a) :
    0 ≤ R.degree (a - side • (fun v => if v ∈ t then 1 else 0)) := by
  rw [R.degree_sub, R.degree_smul]
  have hbound := mul_le_mul_of_nonneg_left (R.degree_cone_selection_le hs hts) hside
  linarith

end PrimitiveRelation

end SmoothCompleteFan

end PaperVerification.ToricGeometry
end
-- END PaperVerification.ToricPrimitiveRelations
end

section
-- BEGIN PaperVerification.ToricNefCone
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
-- END PaperVerification.ToricNefCone
end

section
-- BEGIN PaperVerification.ToricEffectiveCone

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
-- END PaperVerification.ToricEffectiveCone
end

section
-- BEGIN PaperVerification.ToricPrimitiveReduction

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
    | ind k ih =>
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
-- END PaperVerification.ToricPrimitiveReduction
end

section
-- BEGIN PaperVerification.ToricNefCriterion



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
-- END PaperVerification.ToricNefCriterion
end

section
-- BEGIN PaperVerification.ToricPrimitiveFinite



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
-- END PaperVerification.ToricPrimitiveFinite
end

#eval "TORIC_DICTIONARY_PART_06_EOF"
