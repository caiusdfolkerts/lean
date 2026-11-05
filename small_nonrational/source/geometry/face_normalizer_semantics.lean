module

public import RawFaceNormalizers
public import RootedFacetCoverage

@[expose] public section

/-!
# Checked common-face normalizers are complete

Packed permutations are checked in both directions. Every proper face is
represented in the raw list, including the empty face and all vertices.
Consequently the small table check covers all geometrically possible
common faces, without making any assumption about a candidate universe.
-/

noncomputable section
namespace Papers.RationalityTen.FaceNormalizerSemantics

open Finset
open MatroidChecked.FacetBoundaryEncoding
open RawFacePlacement RawFaceNormalizers
open RawFacetEmbeddingSemantics LiteralMaskGeometry
open FacePlacementGeometry

theorem permutation_spec {n forward inverse : Nat}
    (h : permutationCheck n forward inverse = true) (i : Fin n) :
    digit forward i.val < n ∧ digit inverse i.val < n ∧
      digit inverse (digit forward i.val) = i.val ∧
      digit forward (digit inverse i.val) = i.val := by
  exact of_decide_eq_true
    (List.all_eq_true.mp h i.val (List.mem_range.mpr i.isLt))

def checkedPermutation (n forward inverse : Nat)
    (h : permutationCheck n forward inverse = true) : Equiv.Perm (Fin n) where
  toFun i := ⟨digit forward i.val, (permutation_spec h i).1⟩
  invFun i := ⟨digit inverse i.val, (permutation_spec h i).2.1⟩
  left_inv i := Fin.ext (permutation_spec h i).2.2.1
  right_inv i := Fin.ext (permutation_spec h i).2.2.2

def checkedBlock {m : Nat} (B : RawFacePlacement.Block)
    (h : blockValidCheck m B = true) : FacePlacementCodes.Block m where
  shared := B.shared
  outside := B.outside
  shared_le := (of_decide_eq_true (Bool.and_eq_true_iff.mp h).1).1
  remaining_le := (of_decide_eq_true (Bool.and_eq_true_iff.mp h).1).2.1
  target_le := (of_decide_eq_true (Bool.and_eq_true_iff.mp h).1).2.2
  source := checkedPermutation m B.sourceForward B.sourceInverse
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).1
  target := checkedPermutation 10 B.targetForward B.targetInverse
    (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp h).2).2

theorem checkedBlock_representation {m : Nat} (B : RawFacePlacement.Block)
    (h : blockValidCheck m B = true) :
    RootedFacetCoverage.Representation (checkedBlock B h) B := by
  exact ⟨rfl, rfl, fun _ => rfl, fun _ => rfl⟩

theorem normalization_sound {m sourceFace rootFace rootVertices : Nat}
    (B : RawFacePlacement.Block) (hvalid : blockValidCheck m B = true)
    (h : normalizationCheck m sourceFace rootFace rootVertices B = true) :
    Normalizes (checkedBlock B hvalid) (localMaskSet m sourceFace)
      (localMaskSet 10 rootFace) (localMaskSet 10 rootVertices) := by
  obtain ⟨_, h⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hs, h⟩ := Bool.and_eq_true_iff.mp h
  obtain ⟨hi, ho⟩ := Bool.and_eq_true_iff.mp h
  refine ⟨?_, ?_, ?_⟩
  · intro i
    have hh := of_decide_eq_true
      (List.all_eq_true.mp hs i.val (List.mem_range.mpr i.isLt))
    rw [mem_localMaskSet]
    change sourceFace.testBit (digit B.sourceForward i.val) = true ↔ i.val < B.shared
    rw [hh, decide_eq_true_eq]
  · intro i
    have hh := of_decide_eq_true
      (List.all_eq_true.mp hi i.val (List.mem_range.mpr i.isLt))
    rw [mem_localMaskSet]
    change rootFace.testBit (digit B.targetForward i.val) = true ↔ i.val < B.shared
    rw [hh, decide_eq_true_eq]
  · intro i
    have hh := of_decide_eq_true
      (List.all_eq_true.mp ho i.val (List.mem_range.mpr i.isLt))
    rw [mem_localMaskSet]
    change ¬ rootVertices.testBit (digit B.targetForward i.val) = true ↔
      B.shared ≤ i.val ∧ i.val < B.shared + B.outside
    cases hbit : rootVertices.testBit (digit B.targetForward i.val) <;>
      by_cases hp : B.shared ≤ i.val ∧ i.val < B.shared + B.outside <;>
      simp [hbit, hp] at hh ⊢

theorem elements_toFinset (m mask : Nat) :
    (FiniteMaskSets.elements m mask).toFinset = localMaskSet m mask := by
  ext i
  simp only [List.mem_toFinset, FiniteMaskSets.mem_elements, mem_localMaskSet]

theorem localMaskSet_card (m mask : Nat) :
    (localMaskSet m mask).card = FiniteMaskSets.card m mask := by
  rw [← elements_toFinset]
  exact List.toFinset_card_of_nodup (FiniteMaskSets.elements_nodup m mask)

theorem localMaskSet_zero (m : Nat) : localMaskSet m 0 = ∅ := by
  ext i
  simp only [mem_localMaskSet, Nat.zero_testBit, Bool.false_eq_true,
    Finset.notMem_empty]

theorem localMaskSet_singleton {m : Nat} (i : Fin m) :
    localMaskSet m (2 ^ i.val) = {i} := by
  ext j
  simp only [mem_localMaskSet, Nat.testBit_two_pow, decide_eq_true_eq,
    Finset.mem_singleton, Fin.ext_iff]
  exact eq_comm

/-- The raw list contains a representative of every proper decoded face. -/
theorem face_has_mask (m : Nat) (C : ConcreteGrowth.Cell)
    (S : Finset (Fin m)) (hS : S ∈ (decodeTemplate m C).properFaces) :
    ∃ mask ∈ faces m C, localMaskSet m mask = S := by
  simp only [Cell.properFaces, Finset.mem_union, Finset.mem_singleton,
    Finset.mem_image, decodeTemplate] at hS
  rcases hS with ((hempty | hvertex) | hedge) | hridge
  · refine ⟨0, ?_, ?_⟩
    · simp only [faces, List.mem_append, List.mem_cons, List.not_mem_nil,
        or_false, true_or]
    · exact (localMaskSet_zero m).trans hempty.symm
  · obtain ⟨i, hi, hSi⟩ := hvertex
    refine ⟨2 ^ i.val, ?_, (localMaskSet_singleton i).trans hSi⟩
    simp only [faces, List.mem_append]
    exact Or.inr (Or.inl (List.mem_map.mpr
      ⟨i, (FiniteMaskSets.mem_elements i).mpr ((mem_localMaskSet _ _ _).mp hi), rfl⟩))
  · obtain ⟨mask, hm, heq⟩ := hedge
    refine ⟨mask, ?_, heq⟩
    simp only [faces, List.mem_append]
    exact Or.inr (Or.inr (Or.inl (List.mem_toFinset.mp hm)))
  · obtain ⟨mask, hm, heq⟩ := hridge
    refine ⟨mask, ?_, heq⟩
    simp only [faces, List.mem_append]
    exact Or.inr (Or.inr (Or.inr (List.mem_toFinset.mp hm)))

/-- A finite face-pair check supplies the full quantified normalizer premise
of the geometric coverage theorem. -/
theorem completeCheck_sound {m b : Nat} (template root : ConcreteGrowth.Cell)
    (blocks : Fin b → RawFacePlacement.Block)
    (hvalid : ∀ i, blockValidCheck m (blocks i) = true)
    (witness : Nat → Nat → Fin b)
    (hcomplete : completeCheck m template root blocks witness = true) :
    CompleteBlocks (decodeTemplate m template) (decodeCell root)
      (fun i => checkedBlock (blocks i) (hvalid i)) := by
  intro S hS R hR hcard hcapacity
  obtain ⟨s, hs, hseq⟩ := face_has_mask m template S hS
  obtain ⟨r, hr, hreq⟩ := face_has_mask 10 root R hR
  have hf : pairFits m template root s r := by
    change FiniteMaskSets.card m s = FiniteMaskSets.card 10 r ∧
      m - FiniteMaskSets.card m s ≤ 10 - FiniteMaskSets.card 10 root.vertices
    rw [← localMaskSet_card, ← localMaskSet_card, ← localMaskSet_card, hseq, hreq]
    exact ⟨hcard, hcapacity⟩
  have hh := List.all_eq_true.mp (List.all_eq_true.mp hcomplete s hs) r hr
  rw [if_pos hf] at hh
  refine ⟨witness s r, ?_⟩
  have hroot : localMaskSet 10 root.vertices = (decodeCell root).vertices := rfl
  simpa only [hseq, hreq, hroot] using
    normalization_sound (blocks (witness s r)) (hvalid (witness s r)) hh

end Papers.RationalityTen.FaceNormalizerSemantics
