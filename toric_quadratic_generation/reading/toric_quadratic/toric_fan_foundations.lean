module
public import PaperVerification.ToricIntegralBasis
public import Mathlib.Geometry.Convex.Cone.Face.Basic
public import Mathlib.Tactic.Linarith
@[expose] public section
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
