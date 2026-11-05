module

public import PaperVerification.ToricProjectiveVertexMonoids
public import PaperVerification.ToricRationalConvexRelations
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import Mathlib.RingTheory.Ideal.Operations
public import Lean.Elab.Tactic.Omega

@[expose] public section

/-!
# The actual monomial Proj is covered by its vertex charts

All homogeneous coordinate charts first give the usual Proj cover.
An integral homogeneous relation expresses a power of every coordinate
as a product of vertex coordinates. Hence each coordinate chart lies in
a vertex chart. The finite family of vertex charts therefore covers the
actual projective scheme, with no assumed orbit-face correspondence.
-/

noncomputable section

namespace PaperVerification.ToricCharacters

open Set AddMonoidAlgebra AlgebraicGeometry CategoryTheory
open PaperVerification.ToricGeometry PaperVerification.ToricVertexCone
open PaperVerification.ToricRationalGeometry
open scoped BigOperators Classical

variable {ι M : Type*} [AddCommGroup M] (a : ι → M)
    (k : Type*) [CommRing k]

theorem homogeneousWeightCharacter_adjoin :
    Algebra.adjoin (homogeneousWeightGrading a k 0)
      (Set.range (homogeneousWeightCharacter a k))=⊤ := by
  let A := Algebra.adjoin (homogeneousWeightGrading a k 0)
    (Set.range (homogeneousWeightCharacter a k))
  have hchar (p : homogeneousWeightMonoid a) : single p (1 : k)∈A := by
    refine AddSubmonoid.closure_induction
      (motive := fun x hx => single (⟨x,hx⟩ : homogeneousWeightMonoid a) (1 : k)∈A)
      ?_ ?_ ?_ p.property
    · intro x hx
      obtain ⟨i,rfl⟩ := hx
      exact Algebra.subset_adjoin (Set.mem_range_self i)
    · change (1 : AddMonoidAlgebra k (homogeneousWeightMonoid a))∈A
      exact A.one_mem
    · intro x y hx hy ihx ihy
      change single ((⟨x,hx⟩ : homogeneousWeightMonoid a)+⟨y,hy⟩) (1 : k)∈A
      simpa only [single_mul_single,mul_one] using A.mul_mem ihx ihy
  apply top_unique
  intro f hf
  clear hf
  induction f using AddMonoidAlgebra.induction_on with
  | of p => exact hchar p
  | add f g hf hg => exact A.add_mem hf hg
  | smul r f hf =>
      have hr : algebraMap k (AddMonoidAlgebra k (homogeneousWeightMonoid a)) r∈A := by
        exact A.algebraMap_mem (homogeneousWeightZeroMap a k r)
      rw [Algebra.smul_def]
      exact A.mul_mem hr hf

theorem monomialProjective_coordinate_cover :
    (⨆ i,Proj.basicOpen (homogeneousWeightGrading a k)
      (homogeneousWeightCharacter a k i))=⊤ :=
  Proj.iSup_basicOpen_eq_top' _ _
    (fun i=>⟨1,homogeneousWeightCharacter_homogeneous a k i⟩)
    (homogeneousWeightCharacter_adjoin a k)

theorem homogeneousWeightCharacter_relation {κ : Type*} [Fintype κ]
    (j : ι) (v : κ → ι) (N : ℕ) (c : κ → ℕ)
    (hsum : ∑ i,c i=N) (hweight : ∑ i,c i • a (v i)=N • a j) :
    homogeneousWeightCharacter a k j ^ N=
      ∏ i,homogeneousWeightCharacter a k (v i) ^ c i := by
  have he : N • homogeneousWeight a j=∑ i,c i • homogeneousWeight a (v i) := by
    apply Subtype.ext
    apply Prod.ext
    · simpa [homogeneousWeight,Prod.fst_sum] using hsum.symm
    · simpa [homogeneousWeight,Prod.snd_sum] using hweight.symm
  simp [homogeneousWeightCharacter,single_pow,prod_single,he]

theorem basicOpen_le_vertex_cover_of_relation {κ : Type*} [Fintype κ]
    (j : ι) (v : κ → ι) (N : ℕ) (hN : 0<N) (c : κ → ℕ)
    (hsum : ∑ i,c i=N) (hweight : ∑ i,c i • a (v i)=N • a j) :
    Proj.basicOpen (homogeneousWeightGrading a k) (homogeneousWeightCharacter a k j)≤
      ⨆ i,Proj.basicOpen (homogeneousWeightGrading a k)
        (homogeneousWeightCharacter a k (v i)) := by
  have hcpos : ∃ i,0<c i := by
    by_contra h
    push_neg at h
    have hzero : ∀ i,c i=0 := fun i=>Nat.eq_zero_of_le_zero (h i)
    have : N=0 := by simpa [hzero] using hsum.symm
    omega
  obtain ⟨i,hi⟩ := hcpos
  have hdiv : homogeneousWeightCharacter a k (v i)∣homogeneousWeightCharacter a k j ^ N := by
    rw [homogeneousWeightCharacter_relation a k j v N c hsum hweight]
    exact (dvd_pow_self _ (ne_of_gt hi)).trans
      (Finset.dvd_prod_of_mem (fun i=>homogeneousWeightCharacter a k (v i)^c i)
        (Finset.mem_univ i))
  have h := Proj.basicOpen_mono (homogeneousWeightGrading a k) _ _ hdiv
  rw [Proj.basicOpen_pow _ _ N hN] at h
  exact h.trans (le_iSup_of_le i le_rfl)

variable [Fintype ι] {n : ℕ}

def vertexWeightIndices (a : ι → Lattice n) : Finset ι :=
  Finset.univ.filter (fun i=>embed n (a i)∈
    (convexHull ℝ (Set.range (fun j=>embed n (a j)))).extremePoints ℝ)

theorem range_vertexWeightIndices (a : ι → Lattice n) :
    Set.range (fun i : vertexWeightIndices a=>embed n (a i.val))=
      (convexHull ℝ (Set.range (fun i=>embed n (a i)))).extremePoints ℝ := by
  ext x
  constructor
  · rintro ⟨i,rfl⟩
    exact (Finset.mem_filter.mp i.property).2
  · intro hx
    obtain ⟨i,rfl⟩ := extremePoints_convexHull_subset hx
    exact ⟨⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ i,hx⟩⟩,rfl⟩

theorem hull_vertexWeightIndices (a : ι → Lattice n) :
    convexHull ℝ (Set.range (fun i : vertexWeightIndices a=>embed n (a i.val)))=
      convexHull ℝ (Set.range (fun i=>embed n (a i))) := by
  rw [range_vertexWeightIndices]
  simpa using finite_hull_eq_hull_extremePoints
    (Finset.univ.image (fun i=>embed n (a i)))

/-- Actual vertex-coordinate basic opens cover the actual Proj of the
homogeneous monomial algebra. -/
theorem monomialProjective_vertex_cover (a : ι → Lattice n) :
    (⨆ i : vertexWeightIndices a,Proj.basicOpen (homogeneousWeightGrading a k)
      (homogeneousWeightCharacter a k i.val))=⊤ := by
  apply top_le_iff.mp
  rw [← monomialProjective_coordinate_cover a k]
  apply iSup_le
  intro j
  have hj : embed n (a j)∈convexHull ℝ
      (Set.range (fun i : vertexWeightIndices a=>embed n (a i.val))) := by
    rw [hull_vertexWeightIndices]
    exact subset_convexHull ℝ _ (Set.mem_range_self j)
  obtain ⟨N,hN,c,hsum,hweight⟩ := integral_relation_of_mem_convexHull_range
    (fun i : vertexWeightIndices a=>a i.val) (a j) hj
  exact basicOpen_le_vertex_cover_of_relation a k j Subtype.val N hN c hsum hweight

end PaperVerification.ToricCharacters

#print axioms PaperVerification.ToricCharacters.monomialProjective_vertex_cover
