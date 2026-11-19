module
public import Papers.RationalityTenBasisCertificates

@[expose] public section
noncomputable section

/-!
# Efficient, exact finite basis-certificate checks

These adapters retain the original propositions. Exchange witnesses are
searched among the positive literals of the supplied clause. Relabelings are
checked on natural-number masks and then decoded to the same finite sets.
Every adapter below is an ordinary theorem; no executable result is trusted.
-/

namespace Papers.RationalityTen.MatroidChecked.FastSemanticChecks

open Finset BasisFamilies BasisReconstruction BasisCertificates BasisExtensionCNF

def PositiveBasis {k : ℕ} (U : Fin k → Finset (Fin 8))
    (S : Finset (Fin 8)) : Sat.Literal → Prop
  | .pos i => if hi : i < k then U ⟨i,hi⟩ = S else False
  | .neg _ => False

instance {k : ℕ} (U : Fin k → Finset (Fin 8)) (S : Finset (Fin 8))
    (l : Sat.Literal) : Decidable (PositiveBasis U S l) := by
  cases l <;> unfold PositiveBasis <;> infer_instance

def FastOrigin {k t l : ℕ} (U : Fin k → Finset (Fin 8)) (e : Fin 8)
    (old : Finset (Finset (Fin 8))) (newIndex : Fin t → Fin k)
    (models : Fin l → ℕ) : Origin k l → List Sat.Literal → Prop
  | .exchange a b x,c =>
      x ∈ U a ∧ x ∉ U b ∧ Sat.Literal.neg a.val ∈ c ∧ Sat.Literal.neg b.val ∈ c ∧
      ∀ y ∈ U b, y ∉ U a → ∃ z ∈ c, PositiveBasis U (insert y ((U a).erase x)) z
  | .fixed i,c => ValidOrigin U e old newIndex models (.fixed i) c
  | .newPoint,c => ValidOrigin U e old newIndex models .newPoint c
  | .excluded w,c => ValidOrigin U e old newIndex models (.excluded w) c

instance {k t l : ℕ} (U : Fin k → Finset (Fin 8)) (e : Fin 8)
    (old : Finset (Finset (Fin 8))) (newIndex : Fin t → Fin k)
    (models : Fin l → ℕ) (o : Origin k l) (c : List Sat.Literal) :
    Decidable (FastOrigin U e old newIndex models o c) := by
  cases o <;> unfold FastOrigin <;> infer_instance

theorem fastOrigin_sound {k t l : ℕ} (U : Fin k → Finset (Fin 8)) (e : Fin 8)
    (old : Finset (Finset (Fin 8))) (newIndex : Fin t → Fin k)
    (models : Fin l → ℕ) (o : Origin k l) (c : List Sat.Literal)
    (h : FastOrigin U e old newIndex models o c) :
    ValidOrigin U e old newIndex models o c := by
  cases o with
  | fixed i => exact h
  | newPoint => exact h
  | excluded w => exact h
  | exchange a b x =>
    rcases h with ⟨hxa,hxb,hla,hlb,hy⟩
    refine ⟨hxa,hxb,hla,hlb,?_⟩
    intro y hyb hya
    obtain ⟨z,hz,hs⟩ := hy y hyb hya
    cases z with
    | neg i => exact False.elim hs
    | pos i =>
      dsimp only [PositiveBasis] at hs
      split at hs
      · rename_i hi
        exact ⟨⟨i,hi⟩,hs,hz⟩
      · exact False.elim hs

theorem fastOrigins_sound {k t l : ℕ} (U : Fin k → Finset (Fin 8)) (e : Fin 8)
    (old : Finset (Finset (Fin 8))) (newIndex : Fin t → Fin k)
    (models : Fin l → ℕ) (cs : List (Origin k l × List Sat.Literal))
    (h : ∀ oc ∈ cs, FastOrigin U e old newIndex models oc.1 oc.2) :
    ∀ oc ∈ cs, ValidOrigin U e old newIndex models oc.1 oc.2 := by
  intro oc hoc
  exact fastOrigin_sound U e old newIndex models oc.1 oc.2 (h oc hoc)

theorem maskPoints_or (a b : ℕ) : maskPoints (a ||| b) = maskPoints a ∪ maskPoints b := by
  ext i
  simp [maskPoints, Nat.testBit_or]

theorem maskPoints_pow (i : Fin 8) : maskPoints (2 ^ i.val) = {i} := by
  ext j
  simp only [maskPoints, mem_filter, mem_univ, true_and, Nat.testBit_two_pow,
    decide_eq_true_eq, mem_singleton]
  exact ⟨fun h => Fin.ext h.symm, fun h => (congrArg Fin.val h).symm⟩

def pointsMask (L : List (Fin 8)) : ℕ :=
  L.foldr (fun i a => (2 ^ i.val) ||| a) 0

theorem maskPoints_pointsMask (L : List (Fin 8)) : maskPoints (pointsMask L) = L.toFinset := by
  induction L with
  | nil => simp [pointsMask, maskPoints]
  | cons i L ih =>
    simp only [pointsMask, List.foldr_cons, maskPoints_or, maskPoints_pow]
    change {i} ∪ maskPoints (pointsMask L) = (i :: L).toFinset
    rw [ih]
    ext j
    simp

theorem toFinset_map_image {α β : Type*} [DecidableEq α] [DecidableEq β]
    (L : List α) (f : α → β) : (L.map f).toFinset = L.toFinset.image f := by
  ext b
  simp

def maskLabels (m : ℕ) : List (Fin 8) :=
  (List.finRange 8).filter fun i => m.testBit i.val

theorem maskLabels_toFinset (m : ℕ) : (maskLabels m).toFinset = maskPoints m := by
  ext i
  simp [maskLabels, maskPoints]

def permutedMask (code m : ℕ) : ℕ :=
  pointsMask ((maskLabels m).map (permutationFunction code))

theorem maskPoints_permutedMask (code m : ℕ) :
    maskPoints (permutedMask code m) = (maskPoints m).image (permutationFunction code) := by
  rw [permutedMask, maskPoints_pointsMask, toFinset_map_image, maskLabels_toFinset]

theorem familyOfMasks_permuted (code : ℕ) (L : List ℕ) :
    familyOfMasks (L.map (permutedMask code)) =
      (familyOfMasks L).image (fun S => S.image (permutationFunction code)) := by
  simp only [familyOfMasks, toFinset_map_image, Finset.image_image, Function.comp_def,
    maskPoints_permutedMask]

def extensionMasks {k t : ℕ} (old : List ℕ) (grid : Fin k → ℕ)
    (newIndex : Fin t → Fin k) (code : ℕ) : List ℕ :=
  old ++ (((List.finRange t).filter fun j => code.testBit j.val).map
    fun j => grid (newIndex j))

theorem familyOfMasks_extensionMasks {k t : ℕ} (old : List ℕ) (grid : Fin k → ℕ)
    (newIndex : Fin t → Fin k) (code : ℕ) :
    familyOfMasks (extensionMasks old grid newIndex code) =
      extensionFamily (familyOfMasks old) (fun i => maskPoints (grid i)) newIndex code := by
  ext S
  simp only [familyOfMasks, extensionMasks, extensionFamily, mem_union, mem_image,
    List.mem_toFinset, List.mem_append, List.mem_map, List.mem_filter, List.mem_finRange,
    mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨m,hm,heq⟩
    rcases hm with hm | ⟨j,hj,rfl⟩
    · exact Or.inl ⟨m,hm,heq⟩
    · exact Or.inr ⟨j,hj,heq⟩
  · rintro (⟨m,hm,heq⟩ | ⟨j,hj,heq⟩)
    · exact ⟨m,Or.inl hm,heq⟩
    · exact ⟨grid (newIndex j),Or.inr ⟨j,hj,rfl⟩,heq⟩

def RawWitness {k t : ℕ} (n : ℕ) (old : List ℕ) (grid : Fin k → ℕ)
    (newIndex : Fin t → Fin k) (model : ℕ) (target : List ℕ) (permutation : ℕ) : Prop :=
  ValidPermutation n permutation ∧
    ((extensionMasks old grid newIndex model).map (permutedMask permutation)).toFinset =
      target.toFinset

instance {k t : ℕ} (n : ℕ) (old : List ℕ) (grid : Fin k → ℕ)
    (newIndex : Fin t → Fin k) (model : ℕ) (target : List ℕ) (permutation : ℕ) :
    Decidable (RawWitness n old grid newIndex model target permutation) := by
  unfold RawWitness
  infer_instance

theorem rawWitness_sound {k t : ℕ} (n : ℕ) (old : List ℕ) (grid : Fin k → ℕ)
    (newIndex : Fin t → Fin k) (model : ℕ) (target : List ℕ) (permutation : ℕ)
    (h : RawWitness n old grid newIndex model target permutation) :
    ValidWitness n
      (extensionFamily (familyOfMasks old) (fun i => maskPoints (grid i)) newIndex model)
      (familyOfMasks target) permutation := by
  refine ⟨h.1,?_⟩
  rw [← familyOfMasks_extensionMasks, ← familyOfMasks_permuted]
  exact congrArg (fun S : Finset ℕ => S.image maskPoints) h.2

end Papers.RationalityTen.MatroidChecked.FastSemanticChecks
