module

public import PaperVerification.ToricCornerCriterion
public import PaperVerification.ToricFiniteSupportPerturbation
public import Mathlib.Analysis.Convex.Intrinsic

@[expose] public section

/-!
# Actual polytopes of nef support functions

The halfspaces are the literal primitive-ray inequalities. Their Cartier
points are explicit dual-basis sums. Completeness of the actual fan proves
the convex-hull description, including lower-dimensional nef polytopes.
Minkowski addition is then proved for the same actual subsets.
-/

noncomputable section

namespace PaperVerification.ToricGeometry

open Set
open scoped BigOperators Classical Pointwise

namespace SmoothCompleteFan

variable {n : ℕ} («Σ» : SmoothCompleteFan n)

def fullCones : Finset (Finset (Lattice n)) :=
  «Σ».cones.filter (fun s => s.card = n)

theorem fullCones_mem (s : «Σ».fullCones) : (s : Finset (Lattice n)) ∈ «Σ».cones :=
  (Finset.mem_filter.mp s.property).1

theorem fullCones_card (s : «Σ».fullCones) : (s : Finset (Lattice n)).card = n :=
  (Finset.mem_filter.mp s.property).2

def fullConeBasis (s : «Σ».fullCones) : Module.Basis (Fin n) ℤ (Lattice n) :=
  Classical.choose («Σ».full_cone_basis («Σ».fullCones_mem s) («Σ».fullCones_card s))

theorem fullConeBasis_ray_set (s : «Σ».fullCones) :
    (s : Finset (Lattice n)) = Finset.univ.image («Σ».fullConeBasis s) :=
  Classical.choose_spec («Σ».full_cone_basis («Σ».fullCones_mem s) («Σ».fullCones_card s))

/-- The ordinary closed polytope cut out by all primitive-ray support
inequalities, with no nefness built into its definition. -/
def fanPolytope (a : Lattice n → ℝ) : Set (Ambient n) :=
  {x | ∀ u ∈ «Σ».rays, -a u ≤ (dotProductEquiv ℝ (Fin n) (embed n u)) x}

theorem fanPolytope_eq_normalHalfspaces (a : Lattice n → ℝ) :
    «Σ».fanPolytope a = normalHalfspaces
      (fun u : «Σ».rays => dotProductEquiv ℝ (Fin n) (embed n u))
      (fun u : «Σ».rays => -a u) := by
  ext x
  exact ⟨fun h u => h u u.property, fun h u hu => h ⟨u, hu⟩⟩

theorem convex_fanPolytope (a : Lattice n → ℝ) : Convex ℝ («Σ».fanPolytope a) := by
  rw [«Σ».fanPolytope_eq_normalHalfspaces]
  exact convex_normalHalfspaces _ _

/-- The Cartier point is the explicit dual-basis solution of all active
primitive support equalities. -/
def cartierPoint (a : Lattice n → ℝ) (s : «Σ».fullCones) : Ambient n :=
  -∑ i, a («Σ».fullConeBasis s i) •
    integralBasisReal (integralDualBasis («Σ».fullConeBasis s)) i

def cartierBasis (s : «Σ».fullCones) : Module.Basis (Fin n) ℝ (Ambient n) :=
  integralBasisReal (integralDualBasis («Σ».fullConeBasis s))

def activeRay (s : «Σ».fullCones) (i : Fin n) : «Σ».rays :=
  ⟨«Σ».fullConeBasis s i, «Σ».ray_mem_of_mem_cone («Σ».fullCones_mem s)
    ((«Σ».fullConeBasis_ray_set s).symm ▸ Finset.mem_image.mpr
      ⟨i, Finset.mem_univ i, rfl⟩)⟩

theorem activeRay_dual (s : «Σ».fullCones) (i : Fin n) (x : Ambient n) :
    (dotProductEquiv ℝ (Fin n) (embed n («Σ».activeRay s i))) x =
      («Σ».cartierBasis s).repr x i := by
  have h := integralDualBasis_real_pairing (integralDualBasis («Σ».fullConeBasis s)) i x
  change (∑ j, embed n («Σ».fullConeBasis s i) j * x j) =
    («Σ».cartierBasis s).repr x i
  simpa only [integralDualBasis_involutive, cartierBasis] using h

theorem cartierPoint_active (a : Lattice n → ℝ) (s : «Σ».fullCones) (i : Fin n) :
    (dotProductEquiv ℝ (Fin n) (embed n («Σ».activeRay s i))) («Σ».cartierPoint a s) =
      -a («Σ».activeRay s i) := by
  rw [«Σ».activeRay_dual]
  simp [cartierPoint, cartierBasis, activeRay, map_sum, map_smul,
    Finsupp.finsetSum_apply, Finsupp.smul_apply, Module.Basis.repr_self_apply,
    Finsupp.single_apply, smul_eq_mul]

/-- Completeness gives a vertex basis on which any real linear form is
nonnegative. This is a property of the original fan, not an extra support
function hypothesis. -/
theorem exists_cartierBasis_nonnegative (hpure : «Σ».IsPure)
    (f : Ambient n →ₗ[ℝ] ℝ) : ∃ s : «Σ».fullCones, ∀ i, 0 ≤ f («Σ».cartierBasis s i) := by
  obtain ⟨t, ht, hft⟩ := «Σ».complete (dualVector f)
  obtain ⟨s, hs, hts, hscard⟩ := hpure t ht
  let s' : «Σ».fullCones := ⟨s, Finset.mem_filter.mpr ⟨hs, hscard⟩⟩
  have hfs : dualVector f ∈ latticeRayCone s := latticeRayCone_mono hts hft
  rw [show s = Finset.univ.image («Σ».fullConeBasis s') from
    «Σ».fullConeBasis_ray_set s'] at hfs
  have hcoords := ((mem_latticeRayCone_basis_iff («Σ».fullConeBasis s')
    Finset.univ (dualVector f)).mp hfs).1
  refine ⟨s', ?_⟩
  intro i
  have hp := integralDualBasis_real_repr (integralDualBasis («Σ».fullConeBasis s'))
    (dualVector f) i
  rw [integralDualBasis_involutive] at hp
  have hf : (∑ j, dualVector f j * «Σ».cartierBasis s' i j) = f («Σ».cartierBasis s' i) := by
    simpa only [Pi.zero_apply, sub_zero, sub_zero] using
      dualVector_pairing f (0 : Ambient n) («Σ».cartierBasis s' i)
  have hi := hcoords i
  rw [hp, show integralBasisReal (integralDualBasis («Σ».fullConeBasis s')) i =
      «Σ».cartierBasis s' i from rfl, hf] at hi
  exact hi

/-- Genuine nefness places each actual Cartier point in every ray
halfspace. -/
theorem cartierPoint_mem_of_nef {a : Lattice n → ℝ} (ha : «Σ».IsNef a)
    (s : «Σ».fullCones) : «Σ».cartierPoint a s ∈ «Σ».fanPolytope a := by
  obtain ⟨ℓ, he, hle⟩ := ha s («Σ».fullCones_mem s)
  let q : Ambient n →ₗ[ℝ] ℝ := -(dotProductEquiv ℝ (Fin n) («Σ».cartierPoint a s))
  have hq (u : Lattice n) :
      q (embed n u) = -(dotProductEquiv ℝ (Fin n) (embed n u)) («Σ».cartierPoint a s) := by
    change -(«Σ».cartierPoint a s ⬝ᵥ embed n u) =
      -(embed n u ⬝ᵥ «Σ».cartierPoint a s)
    rw [dotProduct_comm]
  have hℓq : ℓ = q := by
    apply (integralBasisReal («Σ».fullConeBasis s)).ext
    intro i
    rw [integralBasisReal_apply, he _
      ((«Σ».fullConeBasis_ray_set s).symm ▸ Finset.mem_image.mpr
        ⟨i, Finset.mem_univ i, rfl⟩), hq]
    have h := «Σ».cartierPoint_active a s i
    change (dotProductEquiv ℝ (Fin n) (embed n («Σ».fullConeBasis s i)))
      («Σ».cartierPoint a s) = -a («Σ».fullConeBasis s i) at h
    rw [h, neg_neg]
  intro u hu
  have h := hle u hu
  rw [hℓq, hq] at h
  linarith

/-- The exact nef polytope/Cartier-point dictionary, with no dimension
assumption on the resulting polytope. -/
theorem fanPolytope_eq_convexHull_cartier (hpure : «Σ».IsPure)
    (a : Lattice n → ℝ) (ha : «Σ».IsNef a) :
    «Σ».fanPolytope a = convexHull ℝ (Set.range («Σ».cartierPoint a)) := by
  rw [«Σ».fanPolytope_eq_normalHalfspaces]
  apply shifted_halfspaces_eq_convexHull _ _ («Σ».cartierBasis) («Σ».activeRay)
    («Σ».cartierPoint a)
  · exact «Σ».activeRay_dual
  · exact «Σ».exists_cartierBasis_nonnegative hpure
  · exact «Σ».cartierPoint_active a
  · intro s
    rw [← «Σ».fanPolytope_eq_normalHalfspaces]
    exact «Σ».cartierPoint_mem_of_nef ha s

theorem cartierPoint_add (a b : Lattice n → ℝ) (s : «Σ».fullCones) :
    «Σ».cartierPoint (a + b) s = «Σ».cartierPoint a s + «Σ».cartierPoint b s := by
  simp only [cartierPoint, Pi.add_apply, add_smul, Finset.sum_add_distrib, neg_add]

/-- The Minkowski identity for all genuine nef support functions,
including those whose polytopes have smaller affine dimension. -/
theorem fanPolytope_add (hpure : «Σ».IsPure)
    (a b : Lattice n → ℝ) (ha : «Σ».IsNef a) (hb : «Σ».IsNef b) :
    «Σ».fanPolytope (a + b) = «Σ».fanPolytope a + «Σ».fanPolytope b := by
  apply Set.Subset.antisymm
  · rw [«Σ».fanPolytope_eq_convexHull_cartier hpure (a + b) (IsNef.add «Σ» ha hb)]
    apply convexHull_min
    · rintro _ ⟨s, rfl⟩
      rw [«Σ».cartierPoint_add]
      exact Set.add_mem_add («Σ».cartierPoint_mem_of_nef ha s) («Σ».cartierPoint_mem_of_nef hb s)
    · exact («Σ».convex_fanPolytope a).add («Σ».convex_fanPolytope b)
  · rintro x ⟨y, hy, z, hz, rfl⟩ u hu
    have hyu := hy u hu
    have hzu := hz u hu
    change -(a u + b u) ≤ _
    rw [map_add]
    linarith

/-- Nef support plus a positive strictly convex support has strict support
on every actual cone. -/
theorem isStrictSupport_add_of_nef {a b : Lattice n → ℝ}
    (ha : «Σ».IsNef a) (hb : «Σ».IsStrictSupport b) : «Σ».IsStrictSupport (a + b) := by
  intro s hs
  obtain ⟨ℓ, he, hle⟩ := ha s hs
  obtain ⟨k, ke, klt⟩ := hb s hs
  refine ⟨ℓ + k, ?_, ?_⟩
  · intro u hu
    simp only [LinearMap.add_apply, Pi.add_apply, he u hu, ke u hu]
  · intro u hu hus
    exact add_lt_add_of_le_of_lt (hle u hu) (klt u hu hus)

/-- Strict positivity on actual extremal primitive rays gives strict
support. A finite positive perturbation reduces it to the proved nef
criterion; strict support is not defined by those ray inequalities. -/
theorem isStrictSupport_of_extremal_primitive_pos (hpure : «Σ».IsPure)
    (H : Lattice n → ℤ) (hH : «Σ».IsStrictSupport (fun u => (H u : ℝ)))
    (a : Lattice n → ℝ)
    (ha : ∀ R : «Σ».PrimitiveRelation, R.IsExtremal → 0 < R.degree a) :
    «Σ».IsStrictSupport a := by
  let I := Finset.univ.filter (fun Q : «Σ».primitiveCollections =>
    («Σ».canonicalPrimitive Q).IsExtremal)
  let f := fun Q : «Σ».primitiveCollections => («Σ».canonicalPrimitive Q).degree a
  let g := fun Q : «Σ».primitiveCollections =>
    -(«Σ».canonicalPrimitive Q).degree (fun u => (H u : ℝ))
  obtain ⟨ε, hε, hsmall⟩ := finite_strict_perturbation I f g
    (fun Q hQ => ha _ (Finset.mem_filter.mp hQ).2)
  have hnef : «Σ».IsNef (a - ε • (fun u => (H u : ℝ))) := by
    apply («Σ».isNef_iff_extremal_primitive_nonneg hpure H hH _).mpr
    intro R hR
    obtain ⟨Q, hQ'⟩ := «Σ».exists_canonicalPrimitive_vector R
    have hQ := hQ'.symm
    have hcanon : («Σ».canonicalPrimitive Q).IsExtremal := by
      change (PointedCone.hull ℝ {(«Σ».canonicalPrimitive Q).vector}).IsFaceOf «Σ».effectiveCone
      rw [hQ]
      exact hR
    have hmem : Q ∈ I := Finset.mem_filter.mpr ⟨Finset.mem_univ Q, hcanon⟩
    have h := (hsmall Q hmem).le
    have hdeg (c : Lattice n → ℝ) : («Σ».canonicalPrimitive Q).degree c = R.degree c := by
      rw [← («Σ».canonicalPrimitive Q).vector_pairing, hQ, R.vector_pairing]
    rw [PrimitiveRelation.degree_sub, PrimitiveRelation.degree_smul]
    dsimp only [f, g] at h
    rw [hdeg, hdeg] at h
    linarith
  have hs := «Σ».isStrictSupport_add_of_nef hnef (IsStrictSupport.smul «Σ» hH hε)
  convert hs using 1
  ext u
  simp

end SmoothCompleteFan

namespace LatticePolytope

theorem fanPolytope_integralSupport_eq {n : ℕ} (P : LatticePolytope n)
    («Σ» : SmoothCompleteFan n) (hfan : «Σ».realCones = P.normalFan) :
    «Σ».fanPolytope (fun u => (P.integralSupport u : ℝ)) = P.carrier := by
  ext x
  rw [P.mem_carrier_iff_normal_ray_inequalities «Σ» hfan]
  change (∀ u ∈ «Σ».rays, -(P.integralSupport u : ℝ) ≤
    (dotProductEquiv ℝ (Fin n) (embed n u)) x) ↔ _
  constructor <;> intro h u hu <;> have hh := h u hu <;> linarith

end LatticePolytope

end PaperVerification.ToricGeometry
