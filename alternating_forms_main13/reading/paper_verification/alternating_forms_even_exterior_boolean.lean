module

public import PaperVerification.AlternatingFormsEvenDegreeBlocks
public import PaperVerification.AlternatingFormsBooleanDuality
public import PaperVerification.AlternatingFormsDuality
public import Mathlib.LinearAlgebra.Quotient.Pi
public import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# The actual even exterior quotient as a product of Boolean quotient pieces

This is a decomposition of the genuine degree quotient by the ideal generated
by the two given matching forms.  Every summand is a homogeneous piece of an
ordinary polynomial quotient by squares and the two restricted linear forms.
The index equation retains the original degree exactly.  Both inclusions of
the relation spaces are proved from literal exterior multiplication.
-/

@[expose] public section
set_option autoImplicit false
noncomputable section
open scoped Classical

namespace PaperVerification.AlternatingForms.EvenSingletons

open scoped BigOperators

variable {K M ι : Type*} [Field K] [AddCommGroup M] [Module K M]
  [LinearOrder ι] [Fintype ι]
local notation "E" => ExteriorAlgebra K M

def blockRelations (a c : ι → K) (s : ℕ) (J : DegreeBlock ι s) :
    Submodule K (BlockSubsets J → K) :=
  BooleanQuotient.relations (fun i : Available J.val.1 => a i.val)
    (fun i : Available J.val.1 => c i.val) J.val.2.val

def coordinateRelations (a c : ι → K) (s : ℕ) :
    Submodule K ((J : DegreeBlock ι s) → BlockSubsets J → K) :=
  Submodule.pi Set.univ (blockRelations a c s)

theorem blockEvaluation_mem_relationIdeal (b : Module.Basis (ι ⊕ ι) K M)
    (a c : ι → K) (S : SingletonState ι) (q : ℕ)
    (v : FixedSubsets (Available S) q → K)
    (hv : v ∈ BooleanQuotient.relations (fun i : Available S => a i.val)
      (fun i : Available S => c i.val) q) :
    blockEvaluation b S q v ∈ exteriorRelationIdeal (matchingForm b a) (matchingForm b c) := by
  cases q with
  | zero =>
      have hz : v = 0 := by
        simpa only [BooleanQuotient.relations_zero, Submodule.mem_bot] using hv
      rw [hz, map_zero]
      exact Ideal.zero_mem _
  | succ q =>
      rw [BooleanQuotient.relations_succ] at hv
      obtain ⟨x, ⟨u, rfl⟩, y, ⟨w, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hv
      rw [map_add, ← matching_mul_blockEvaluation b a S q u,
        ← matching_mul_blockEvaluation b c S q w]
      apply Ideal.add_mem
      · apply Ideal.mul_mem_right
        exact Ideal.subset_span (by simp)
      · apply Ideal.mul_mem_right
        exact Ideal.subset_span (by simp)

theorem degreeCoordinates_symm_mem_relations (b : Module.Basis (ι ⊕ ι) K M)
    (a c : ι → K) (s : ℕ)
    (v : (J : DegreeBlock ι s) → BlockSubsets J → K)
    (hv : v ∈ coordinateRelations a c s) :
    (degreeCoordinates b s).symm v ∈
      exteriorDegreeRelations (matchingForm b a) (matchingForm b c) s := by
  rw [degreeCoordinates_symm]
  apply Submodule.sum_mem
  intro J hJ
  change blockEvaluation b J.val.1 J.val.2.val (v J) ∈
    exteriorRelationIdeal (matchingForm b a) (matchingForm b c)
  exact blockEvaluation_mem_relationIdeal b a c J.val.1 J.val.2.val (v J) (hv J trivial)

def successorBlock (t : ℕ) (T : DegreeState ι t) : DegreeBlock ι (2 + t) :=
  ⟨(T.val.1, ⟨T.val.2.card + 1, by
      have h := T.property
      change singletonDegree T.val.1 + 2 * T.val.2.card = t at h
      omega⟩), by
    have h := T.property
    change singletonDegree T.val.1 + 2 * T.val.2.card = t at h
    change singletonDegree T.val.1 + 2 * (T.val.2.card + 1) = 2 + t
    omega⟩

theorem matching_wedge_basis_eq_block (b : Module.Basis (ι ⊕ ι) K M)
    (a : ι → K) (t : ℕ) (T : DegreeState ι t) :
    exteriorPower.wedge K M 2 t (matchingForm b a) (stateDegreeBasis b t T) =
      blockIntoDegree b (2 + t) (successorBlock t T)
        (weightedInclusionOperator (fun i : Available T.val.1 => a i.val) T.val.2.card
          (Pi.single (⟨T.val.2, rfl⟩ : FixedSubsets (Available T.val.1) T.val.2.card) 1)) := by
  apply Subtype.ext
  change (matchingForm b a : E) * (stateDegreeBasis b t T : E) =
    blockEvaluation b T.val.1 (T.val.2.card + 1) _
  rw [stateDegreeBasis_coe,
    ← blockEvaluation_single b T.val.1 T.val.2.card ⟨T.val.2, rfl⟩,
    matching_mul_blockEvaluation]

def coordinateImageRelations (a : ι → K) (s : ℕ) :
    Submodule K ((J : DegreeBlock ι s) → BlockSubsets J → K) :=
  Submodule.pi Set.univ (fun J =>
    (BooleanQuotient.relationMap (fun i : Available J.val.1 => a i.val) J.val.2.val).range)

theorem matching_wedge_coordinates_mem (b : Module.Basis (ι ⊕ ι) K M)
    (a : ι → K) (t : ℕ) (x : ⋀[K]^t M) :
    degreeCoordinates b (2 + t) (exteriorPower.wedge K M 2 t (matchingForm b a) x) ∈
      coordinateImageRelations a (2 + t) := by
  rw [← (stateDegreeBasis b t).sum_repr x]
  simp only [map_sum, map_smul]
  apply Submodule.sum_mem
  intro T hT
  apply Submodule.smul_mem
  rw [matching_wedge_basis_eq_block]
  erw [degreeCoordinates_block]
  apply Submodule.le_comap_single_pi
  change weightedInclusionOperator (fun i : Available T.val.1 => a i.val) T.val.2.card
      (Pi.single (⟨T.val.2, rfl⟩ : FixedSubsets (Available T.val.1) T.val.2.card) 1) ∈
    (BooleanQuotient.relationMap (fun i : Available T.val.1 => a i.val)
      (T.val.2.card + 1)).range
  rw [BooleanQuotient.relationMap_range_succ]
  exact LinearMap.mem_range_self _ _

theorem coordinateImageRelations_le_left (a c : ι → K) (s : ℕ) :
    coordinateImageRelations a s ≤ coordinateRelations a c s := by
  intro v hv J hJ
  exact (show (BooleanQuotient.relationMap (fun i : Available J.val.1 => a i.val)
    J.val.2.val).range ≤ blockRelations a c s J from le_sup_left) (hv J hJ)

theorem coordinateImageRelations_le_right (a c : ι → K) (s : ℕ) :
    coordinateImageRelations c s ≤ coordinateRelations a c s := by
  intro v hv J hJ
  exact (show (BooleanQuotient.relationMap (fun i : Available J.val.1 => c i.val)
    J.val.2.val).range ≤ blockRelations a c s J from le_sup_right) (hv J hJ)

theorem degreeCoordinates_mem_relations (b : Module.Basis (ι ⊕ ι) K M)
    (a c : ι → K) (s : ℕ) (x : ⋀[K]^s M)
    (hx : x ∈ exteriorDegreeRelations (matchingForm b a) (matchingForm b c) s) :
    degreeCoordinates b s x ∈ coordinateRelations a c s := by
  by_cases hs : s < 2
  · rw [exteriorDegreeRelations_eq_bot _ _ hs] at hx
    have hz : x = 0 := (Submodule.mem_bot K).mp hx
    rw [hz, map_zero]
    exact Submodule.zero_mem _
  · obtain ⟨t, rfl⟩ : ∃ t, s = 2 + t := ⟨s - 2, by omega⟩
    rw [exteriorDegreeRelations_eq_images] at hx
    obtain ⟨u, ⟨y, rfl⟩, v, ⟨z, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hx
    rw [map_add]
    apply Submodule.add_mem
    · exact coordinateImageRelations_le_left a c (2 + t)
        (matching_wedge_coordinates_mem b a t y)
    · exact coordinateImageRelations_le_right a c (2 + t)
        (matching_wedge_coordinates_mem b c t z)

/-- Exact equality of the transported actual generated-ideal relations and
the product of the ordinary Boolean relation spaces. -/
theorem degreeCoordinates_map_relations (b : Module.Basis (ι ⊕ ι) K M)
    (a c : ι → K) (s : ℕ) :
    (exteriorDegreeRelations (matchingForm b a) (matchingForm b c) s).map
      (degreeCoordinates b s).toLinearMap = coordinateRelations a c s := by
  ext v
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact degreeCoordinates_mem_relations b a c s x hx
  · intro hv
    exact ⟨(degreeCoordinates b s).symm v,
      degreeCoordinates_symm_mem_relations b a c s v hv,
      (degreeCoordinates b s).apply_symm_apply v⟩

/-- The full even matching quotient decomposition, in every exterior degree. -/
def exteriorQuotientEquivBooleanPieces (b : Module.Basis (ι ⊕ ι) K M)
    (a c : ι → K) (s : ℕ) :
    ExteriorQuotientDegree (matchingForm b a) (matchingForm b c) s ≃ₗ[K]
      ((J : DegreeBlock ι s) → BooleanQuotient.piece
        (fun i : Available J.val.1 => a i.val) (fun i : Available J.val.1 => c i.val)
        J.val.2.val) :=
  (Submodule.Quotient.equiv _ _ (degreeCoordinates b s)
    (degreeCoordinates_map_relations b a c s)).trans
      ((Submodule.quotientPi (blockRelations a c s)).trans
        (LinearEquiv.piCongrRight (fun J => BooleanQuotient.cokernelEquivPiece
          (fun i : Available J.val.1 => a i.val) (fun i : Available J.val.1 => c i.val)
          J.val.2.val)))

theorem finrank_exteriorQuotient_eq_sum_booleanPieces (b : Module.Basis (ι ⊕ ι) K M)
    (a c : ι → K) (s : ℕ) :
    Module.finrank K (ExteriorQuotientDegree (matchingForm b a) (matchingForm b c) s) =
      ∑ J : DegreeBlock ι s, Module.finrank K (BooleanQuotient.piece
        (fun i : Available J.val.1 => a i.val) (fun i : Available J.val.1 => c i.val)
        J.val.2.val) := by
  letI : ∀ J : DegreeBlock ι s, Module.Free K (BooleanQuotient.piece
      (fun i : Available J.val.1 => a i.val) (fun i : Available J.val.1 => c i.val)
      J.val.2.val) := fun J => Module.Free.of_divisionRing K _
  letI : ∀ J : DegreeBlock ι s, Module.Finite K (BooleanQuotient.piece
      (fun i : Available J.val.1 => a i.val) (fun i : Available J.val.1 => c i.val)
      J.val.2.val) := fun J => BooleanQuotient.finiteDimensional_piece _ _ _
  rw [(exteriorQuotientEquivBooleanPieces b a c s).finrank_eq,
    Module.finrank_pi_fintype]

end PaperVerification.AlternatingForms.EvenSingletons
