module

public import PaperVerification.E6TranslationClasses
public import PaperVerification.E6Normalization
public import Mathlib.SetTheory.Cardinal.Finite


@[expose] public section
noncomputable section

namespace PaperVerification.ColdSpots

theorem e6PhysicalPoint_add (z w : TriTriple) :
    e6PhysicalPoint (z+w)=e6PhysicalPoint z+e6PhysicalPoint w := by
  funext j
  refine Fin.addCases (m:=3) (n:=3) (fun i ↦ ?_) (fun i ↦ ?_) j <;>
    simp [e6PhysicalPoint,scaleVec,triTripleFlatten, -Fin.natAdd_eq_addNat] <;> ring

def e6PhysicalAddHom : TriTriple →+ (Fin 6 → ℝ) where
  toFun := e6PhysicalPoint
  map_zero' := e6PhysicalPoint_zero
  map_add' := e6PhysicalPoint_add

theorem e6PhysicalPoint_injective : Function.Injective e6PhysicalPoint :=
  (scaleVec_injective (Real.sqrt 2) (by positivity)).comp triTripleEuclideanEquiv.injective

def e6AddSubgroup : AddSubgroup (Fin 6 → ℝ) := l6AddSubgroup.map e6PhysicalAddHom

theorem e6AddSubgroup_coe : (e6AddSubgroup : Set (Fin 6 → ℝ))=e6Set := by
  ext x
  constructor
  · rintro ⟨z,hz,rfl⟩
    exact ⟨triTripleFlatten z,⟨z,hz,rfl⟩,rfl⟩
  · rintro ⟨y,⟨z,hz,rfl⟩,rfl⟩
    exact ⟨z,hz,rfl⟩

theorem e6Physical_difference_mem (z w : TriTriple) :
    e6PhysicalPoint z-e6PhysicalPoint w ∈ e6Set ↔ z-w ∈ l6Set := by
  rw [← e6AddSubgroup_coe]
  change e6PhysicalAddHom z-e6PhysicalAddHom w ∈ e6AddSubgroup ↔ z-w ∈ l6Set
  rw [← map_sub e6PhysicalAddHom]
  constructor
  · rintro ⟨l,hl,he⟩
    exact e6PhysicalPoint_injective he ▸ hl
  · intro h
    exact ⟨z-w,h,rfl⟩

def e6CanonicalHole (b : Bool) : Fin 6 → ℝ :=
  e6PhysicalPoint (if b then -e6HoleWitness else e6HoleWitness)

theorem e6CanonicalHole_deep (b : Bool) : IsDeepHole e6Set (e6CanonicalHole b) := by
  have h : E6BalancedPhases (if b then -e6HoleWitness else e6HoleWitness) := by
    cases b
    · exact e6HoleWitness_balanced
    · exact e6NegativeWitness_balanced
  exact (e6_deep_hole_description _).mpr ((e6BalancedPhases_iff_paper _).mp h)

theorem e6CanonicalHole_distinct (b c : Bool) :
    e6CanonicalHole b-e6CanonicalHole c ∈ e6Set ↔ b=c := by
  unfold e6CanonicalHole
  rw [e6Physical_difference_mem]
  cases b <;> cases c
  · simp [show (0:TriTriple)∈l6Set from l6AddSubgroup.zero_mem]
  · constructor
    · intro h
      exact (e6_two_classes_distinct h).elim
    · intro h
      cases h
  · have h : -e6HoleWitness-e6HoleWitness ∉ l6Set := by
      intro hm
      apply e6_two_classes_distinct
      have hn : -(-e6HoleWitness-e6HoleWitness) ∈ l6Set := l6AddSubgroup.neg_mem hm
      rwa [show -(-e6HoleWitness-e6HoleWitness) =
        e6HoleWitness-(-e6HoleWitness) by abel] at hn
    constructor
    · intro hm
      exact (h hm).elim
    · intro he
      cases he
  · simp [show (0:TriTriple)∈l6Set from l6AddSubgroup.zero_mem]

theorem e6DeepHole_class_coverage {x : Fin 6 → ℝ} (hx : IsDeepHole e6Set x) :
    ∃ b : Bool, x-e6CanonicalHole b ∈ e6Set := by
  obtain ⟨z,rfl⟩ := e6PhysicalPoint_surjective x
  have hz : E6BalancedPhases z :=
    (e6BalancedPhases_iff_paper z).mpr ((e6_deep_hole_description z).mp hx)
  rcases e6_two_translation_classes hz with h | h
  · exact ⟨false,(e6Physical_difference_mem _ _).mpr h⟩
  · exact ⟨true,(e6Physical_difference_mem _ _).mpr h⟩

def E6DeepTranslationClasses :=
  {C : (Fin 6 → ℝ) ⧸ e6AddSubgroup // ∃ x : Fin 6 → ℝ,
    IsDeepHole e6Set x ∧ (x : (Fin 6 → ℝ) ⧸ e6AddSubgroup)=C}

def e6DeepClassMap (b : Bool) : E6DeepTranslationClasses :=
  ⟨(e6CanonicalHole b : (Fin 6 → ℝ) ⧸ e6AddSubgroup),
    e6CanonicalHole b,e6CanonicalHole_deep b,rfl⟩

theorem e6DeepClassMap_bijective : Function.Bijective e6DeepClassMap := by
  constructor
  · intro b c h
    apply (e6CanonicalHole_distinct b c).mp
    rw [← e6AddSubgroup_coe]
    exact QuotientAddGroup.eq_iff_sub_mem.mp (congrArg Subtype.val h)
  · rintro ⟨C,x,hx,hC⟩
    obtain ⟨b,hb⟩ := e6DeepHole_class_coverage hx
    rw [← e6AddSubgroup_coe] at hb
    exact ⟨b,Subtype.ext ((QuotientAddGroup.eq_iff_sub_mem.mpr hb).symm.trans hC)⟩

def e6DeepClassEquiv : Bool ≃ E6DeepTranslationClasses :=
  Equiv.ofBijective e6DeepClassMap e6DeepClassMap_bijective

/-- Exactly two classes in the actual root-normalized E₆ lattice quotient. -/
theorem e6_deep_translation_class_count : Nat.card E6DeepTranslationClasses=2 := by
  rw [← Nat.card_congr e6DeepClassEquiv,Nat.card_eq_fintype_card]
  norm_num

end PaperVerification.ColdSpots
