module

public import PaperVerification.AlternatingFormsBarLeadingExact
public import PaperVerification.AlternatingFormsFilteredComparison

/-!
# The actual internal grading of the odd normalized bar complex

The degree of a tensor is the sum of the degrees of its actual positive
standard-product factors. The multiplication coefficients already proved
for the original quotient preserve this degree. Consequently the genuine
normalized bar complex, and not only its cut model, splits into these
internal-degree subcomplexes.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical BigOperators

namespace PaperVerification.AlternatingForms.BarDegrees

open PaperVerification.ReducedBarBasis PaperVerification.AugmentedAlgebraBasis

variable {K A C : Type*} [CommRing K] [Ring A] [Algebra K A]
  (B : Module.Basis (Option C) K A) (δ : C → ℕ)

def totalDegree (L : List C) : ℕ := (L.map δ).sum

@[simp] theorem totalDegree_nil : totalDegree δ []=0 := rfl

@[simp] theorem totalDegree_cons (c : C) (L : List C) :
    totalDegree δ (c::L)=δ c+totalDegree δ L := rfl

theorem totalDegree_append (L T : List C) :
    totalDegree δ (L++T)=totalDegree δ L+totalDegree δ T := by
  simp only [totalDegree,List.map_append,List.sum_append]

def degreePiece (N : ℕ) : Submodule K (List C →₀ K) :=
  Finsupp.supported K K {L | totalDegree δ L=N}

theorem degreePiece_eq_span (N : ℕ) :
    degreePiece (K := K) δ N=Submodule.span K
      ((fun L : List C ↦ Finsupp.single L (1 : K)) '' {L | totalDegree δ L=N}) :=
  Finsupp.supported_eq_span_single K _

theorem prefix_mem_degreePiece (c : C) {N : ℕ} (z : List C →₀ K)
    (hz : z∈degreePiece δ N) : prepend c z∈degreePiece δ (δ c+N) := by
  rw [degreePiece_eq_span] at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨L,hL,rfl⟩ := hz
    rw [prefix_single]
    apply Finsupp.single_mem_supported K 1
    change totalDegree δ (c::L)=δ c+N
    change totalDegree δ L=N at hL
    rw [totalDegree_cons,hL]
  | zero => simpa only [map_zero] using (degreePiece (K := K) δ (δ c+N)).zero_mem
  | add z w hz hw ihz ihw =>
    simpa only [map_add] using (degreePiece (K := K) δ (δ c+N)).add_mem ihz ihw
  | smul a z hz ih =>
    simpa only [map_smul] using (degreePiece (K := K) δ (δ c+N)).smul_mem a ih

variable (hδ : ∀ a b c,productCoefficients B a b c≠0 → δ c=δ a+δ b)

include hδ in
theorem product_appendTail_mem_degreePiece (a b : C) (L : List C) :
    appendTail L (productCoefficients B a b)∈degreePiece δ (δ a+δ b+totalDegree δ L) := by
  rw [appendTail,Finsupp.linearCombination_apply,Finsupp.sum]
  apply Submodule.sum_mem
  intro c hc
  apply Submodule.smul_mem
  apply Finsupp.single_mem_supported K 1
  change totalDegree δ (c::L)=δ a+δ b+totalDegree δ L
  rw [totalDegree_cons,hδ a b c (Finsupp.mem_support_iff.mp hc)]

include hδ in
theorem differentialBasis_mem_degreePiece (L : List C) :
    differentialBasis B L∈degreePiece δ (totalDegree δ L) := by
  induction L with
  | nil => exact Submodule.zero_mem _
  | cons a L ih =>
    cases L with
    | nil =>
      simp only [differentialBasis,merge_single,mergeBasis,smul_zero,map_zero,sub_zero]
      exact Submodule.zero_mem _
    | cons b L =>
      rw [differentialBasis]
      apply Submodule.sub_mem
      · rw [merge_single,one_smul,mergeBasis]
        simpa only [totalDegree_cons,Nat.add_assoc] using
          product_appendTail_mem_degreePiece B δ hδ a b L
      · exact prefix_mem_degreePiece δ a _ ih

include hδ in
theorem differential_mem_degreePiece {N : ℕ} (z : List C →₀ K)
    (hz : z∈degreePiece δ N) : differential B z∈degreePiece δ N := by
  rw [degreePiece_eq_span] at hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨L,hL,rfl⟩ := hz
    rw [differential_single,one_smul]
    change totalDegree δ L=N at hL
    simpa only [hL] using differentialBasis_mem_degreePiece B δ hδ L
  | zero => simpa only [map_zero] using (degreePiece (K := K) δ N).zero_mem
  | add z w hz hw ihz ihw =>
    simpa only [map_add] using (degreePiece (K := K) δ N).add_mem ihz ihw
  | smul a z hz ih =>
    simpa only [map_smul] using (degreePiece (K := K) δ N).smul_mem a ih

end PaperVerification.AlternatingForms.BarDegrees

namespace PaperVerification.AlternatingForms

open BarCompositions BarDegrees PaperVerification.ReducedBarBasis
open CategoryTheory

universe u
variable {K : Type u} [Field K] [CharZero K]
  (k t : ℕ) (hs : t+2≤k+1)

local notation "C" => OddPositiveStandardIndex (K := K) k t hs
local notation "B" => oddAugmentedBasis (K := K) k t hs
local notation "e" => oddPositiveWordEquiv (K := K) k t hs
local notation "δ" => oddPositiveDegree (K := K) k t hs

theorem oddBarWord_length_eq_degree (L : List C) :
    (flattenBarWord e L).length=totalDegree δ L := by
  induction L with
  | nil => rfl
  | cons a L ih =>
    change ((e a).val++flattenBarWord e L).length=δ a+totalDegree δ L
    rw [List.length_append,oddPositiveWord_degree,ih]

theorem oddInternalDegreePiece_eq_inf (r N : ℕ) :
    internalDegreePiece (K := K) e r N=
      BarFree.lengthPiece C K r ⊓ degreePiece δ N := by
  ext z
  change ((z.support : Set (List C))⊆{L : List C | L.length=r ∧ (flattenBarWord e L).length=N}) ↔
    ((z.support : Set (List C))⊆{L : List C | L.length=r}) ∧
      ((z.support : Set (List C))⊆{L : List C | totalDegree δ L=N})
  simp only [Set.subset_def,Set.mem_setOf_eq,oddBarWord_length_eq_degree]
  constructor
  · intro h
    exact ⟨fun L hL ↦ (h L hL).1,fun L hL ↦ (h L hL).2⟩
  · rintro ⟨h₁,h₂⟩ L hL
    exact ⟨h₁ L hL,h₂ L hL⟩

theorem oddReducedDifferential_mem_internalDegree {r N : ℕ} (z : List C →₀ K)
    (hz : z∈internalDegreePiece (K := K) e (r+1) N) :
    differential B z∈internalDegreePiece (K := K) e r N := by
  rw [oddInternalDegreePiece_eq_inf] at hz ⊢
  exact ⟨BarFree.reducedDifferential_mem_lengthPiece B z hz.1,
    differential_mem_degreePiece B δ (odd_productCoefficient_degree k t hs) z hz.2⟩

/-- The sign is the actual sign after tensoring the free bar resolution
with the augmentation residue. -/
def oddBigradedDifferential (r N : ℕ) :
    internalDegreePiece (K := K) e (r+1) N →ₗ[K]
      internalDegreePiece (K := K) e r N :=
  LinearMap.codRestrict _
    ((-differential B).comp (internalDegreePiece (K := K) e (r+1) N).subtype)
    (fun z ↦ Submodule.neg_mem _
      (oddReducedDifferential_mem_internalDegree k t hs z.val z.property))

@[simp] theorem oddBigradedDifferential_val (r N : ℕ)
    (z : internalDegreePiece (K := K) e (r+1) N) :
    (oddBigradedDifferential (K := K) k t hs r N z).val=-differential B z.val := rfl

theorem oddBigradedDifferential_squared (r N : ℕ) :
    (oddBigradedDifferential (K := K) k t hs r N).comp
      (oddBigradedDifferential (K := K) k t hs (r+1) N)=0 := by
  apply LinearMap.ext
  intro z
  apply Subtype.ext
  change -differential B (-differential B z.val)=0
  rw [map_neg,neg_neg,differential_squared (oddAugmentation (K := K) k t) B
    (oddAugmentedBasis_none (K := K) k t hs) (oddAugmentation_positive (K := K) k t hs)]

def oddInternalDegreeInclusion (r N : ℕ) :
    internalDegreePiece (K := K) e r N →ₗ[K] BarFree.lengthPiece C K r :=
  Submodule.inclusion (by
    rw [oddInternalDegreePiece_eq_inf]
    exact inf_le_left)

theorem oddInternalDegreeInclusion_differential (r N : ℕ) :
    (oddInternalDegreeInclusion k t hs r N).comp (oddBigradedDifferential (K := K) k t hs r N)=
      (BarFree.negativeReducedDegreeDifferential B r).comp
        (oddInternalDegreeInclusion k t hs (r+1) N) := by
  apply LinearMap.ext
  intro z
  rfl

def oddInternalDegreeBasis (r N : ℕ) :
    Module.Basis (InternalDegreeIndex e r N) K (internalDegreePiece (K := K) e r N) :=
  .ofRepr (internalDegreeCoordinates e r N)

def oddInternalDegreeComplex (N : ℕ) : ChainComplex (ModuleCat K) ℕ :=
  ChainComplex.of (fun r ↦ ModuleCat.of K (internalDegreePiece (K := K) e r N))
    (fun r ↦ ModuleCat.ofHom (oddBigradedDifferential (K := K) k t hs r N))
    (fun r ↦ ModuleCat.hom_ext (oddBigradedDifferential_squared k t hs r N))

@[simp] theorem oddInternalDegreeComplex_d (r N : ℕ) :
    (oddInternalDegreeComplex (K := K) k t hs N).d (r+1) r=
      ModuleCat.ofHom (oddBigradedDifferential (K := K) k t hs r N) := by
  simp [oddInternalDegreeComplex]

/-- This is the actual inclusion into the complex computing ordinary
Tor, with its original differential and coefficient field. -/
def oddInternalDegreeInclusionChain (N : ℕ) :
    oddInternalDegreeComplex (K := K) k t hs N ⟶
      BarFree.reducedComplex (oddAugmentation (K := K) k t) B
        (oddAugmentedBasis_none (K := K) k t hs) (oddAugmentation_positive (K := K) k t hs) where
  f r := ModuleCat.ofHom (oddInternalDegreeInclusion k t hs r N)
  comm' i j hij := by
    change j+1=i at hij
    subst i
    rw [oddInternalDegreeComplex_d,BarFree.reducedComplex_d]
    apply ModuleCat.hom_ext
    exact (oddInternalDegreeInclusion_differential k t hs j N).symm

end PaperVerification.AlternatingForms
