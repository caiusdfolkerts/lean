module
public import MatroidChecked.BitsetOrigins

@[expose] public section
noncomputable section

/-!
# Basis-exchange checks directly on finite masks

The bit operations below describe the same subsets of `Fin 8` as
`maskPoints`.  A checked mask equality is transported to the actual finite
sets by `maskOrigin_sound`.  The exported certificate propositions continue
to use `ValidOrigin`, with its original basis-exchange meaning.
-/

namespace Papers.RationalityTen.MatroidChecked.MaskOrigins

open Finset BasisReconstruction BasisCertificates BasisExtensionCNF FastSemanticChecks BitsetOrigins

theorem lowMask_testBit : ∀ i : Fin 8, (255 : ℕ).testBit i.val = true := by
  decide +kernel

theorem maskPoints_and_low (m : ℕ) : maskPoints (m &&& 255) = maskPoints m := by
  ext i
  simp [maskPoints, Nat.testBit_and, lowMask_testBit]

theorem maskPoints_erase_mask (m : ℕ) (x : Fin 8) :
    maskPoints (m &&& (255 ^^^ 2 ^ x.val)) = (maskPoints m).erase x := by
  ext i
  by_cases h : i = x
  · subst i
    simp [maskPoints, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow,
      lowMask_testBit]
  · have hv : i.val ≠ x.val := fun he => h (Fin.ext he)
    simp [maskPoints, Nat.testBit_and, Nat.testBit_xor, Nat.testBit_two_pow,
      lowMask_testBit, h, hv, Ne.symm h, Ne.symm hv]

def exchangeMask (m : ℕ) (x y : Fin 8) : ℕ :=
  (m &&& (255 ^^^ 2 ^ x.val)) ||| 2 ^ y.val

theorem maskPoints_exchangeMask (m : ℕ) (x y : Fin 8) :
    maskPoints (exchangeMask m x y) = insert y ((maskPoints m).erase x) := by
  rw [exchangeMask, maskPoints_or, maskPoints_erase_mask, maskPoints_pow]
  simp only [Finset.union_singleton]

def MaskPositiveBasis {k : ℕ} (grid : Fin k → ℕ) (wanted : ℕ) : Sat.Literal → Prop
  | .pos i => if hi : i < k then grid ⟨i, hi⟩ &&& 255 = wanted else False
  | .neg _ => False

instance {k : ℕ} (grid : Fin k → ℕ) (wanted : ℕ) (z : Sat.Literal) :
    Decidable (MaskPositiveBasis grid wanted z) := by
  cases z <;> unfold MaskPositiveBasis <;> infer_instance

theorem maskPositiveBasis_sound {k : ℕ} (grid : Fin k → ℕ) (wanted : ℕ)
    (z : Sat.Literal) (h : MaskPositiveBasis grid wanted z) :
    PositiveBasis (fun i => maskPoints (grid i)) (maskPoints wanted) z := by
  cases z with
  | neg i => exact False.elim h
  | pos i =>
    by_cases hi : i < k
    · simp only [MaskPositiveBasis, PositiveBasis, dif_pos hi] at h ⊢
      have he := congrArg maskPoints h
      simpa only [maskPoints_and_low] using he
    · simpa only [MaskPositiveBasis, PositiveBasis, dif_neg hi] using h

def MaskOrigin {k t l : ℕ} (grid : Fin k → ℕ) (e : Fin 8)
    (old : Finset (Finset (Fin 8))) (newIndex : Fin t → Fin k)
    (models : Fin l → ℕ) : Origin k l → List Sat.Literal → Prop
  | .exchange a b x, c =>
      (grid a).testBit x.val = true ∧ (grid b).testBit x.val = false ∧
      Sat.Literal.neg a.val ∈ c ∧ Sat.Literal.neg b.val ∈ c ∧
      ∀ y : Fin 8, (grid b).testBit y.val = true → (grid a).testBit y.val = false →
        ∃ z ∈ c, MaskPositiveBasis grid (exchangeMask (grid a) x y) z
  | .fixed i, c => BitsetOrigin (fun j => maskPoints (grid j)) e old newIndex models (.fixed i) c
  | .newPoint, c => BitsetOrigin (fun j => maskPoints (grid j)) e old newIndex models .newPoint c
  | .excluded w, c => BitsetOrigin (fun j => maskPoints (grid j)) e old newIndex models (.excluded w) c

instance {k t l : ℕ} (grid : Fin k → ℕ) (e : Fin 8)
    (old : Finset (Finset (Fin 8))) (newIndex : Fin t → Fin k)
    (models : Fin l → ℕ) (o : Origin k l) (c : List Sat.Literal) :
    Decidable (MaskOrigin grid e old newIndex models o c) := by
  cases o <;> unfold MaskOrigin <;> infer_instance

theorem maskOrigin_sound {k t l : ℕ} (grid : Fin k → ℕ) (e : Fin 8)
    (old : Finset (Finset (Fin 8))) (newIndex : Fin t → Fin k)
    (models : Fin l → ℕ) (o : Origin k l) (c : List Sat.Literal)
    (h : MaskOrigin grid e old newIndex models o c) :
    ValidOrigin (fun i => maskPoints (grid i)) e old newIndex models o c := by
  cases o with
  | fixed i => exact bitsetOrigin_sound _ e old newIndex models (.fixed i) c h
  | newPoint => exact bitsetOrigin_sound _ e old newIndex models .newPoint c h
  | excluded w => exact bitsetOrigin_sound _ e old newIndex models (.excluded w) c h
  | exchange a b x =>
    apply fastOrigin_sound
    rcases h with ⟨hxa, hxb, hna, hnb, hy⟩
    refine ⟨?_, ?_, hna, hnb, ?_⟩
    · simpa only [maskPoints, mem_filter, mem_univ, true_and] using hxa
    · simp [maskPoints, hxb]
    · intro y hyb hya
      have hb : (grid b).testBit y.val = true := by
        simpa only [maskPoints, mem_filter, mem_univ, true_and] using hyb
      have ha : (grid a).testBit y.val = false := by
        cases hbit : (grid a).testBit y.val with
        | false => rfl
        | true =>
          exfalso
          apply hya
          simpa only [maskPoints, mem_filter, mem_univ, true_and] using hbit
      obtain ⟨z, hz, hmask⟩ := hy y hb ha
      refine ⟨z, hz, ?_⟩
      have hs := maskPositiveBasis_sound grid (exchangeMask (grid a) x y) z hmask
      simpa only [maskPoints_exchangeMask] using hs

theorem maskOrigins_sound {k t l : ℕ} (grid : Fin k → ℕ) (e : Fin 8)
    (old : Finset (Finset (Fin 8))) (newIndex : Fin t → Fin k)
    (models : Fin l → ℕ) (cs : List (Origin k l × List Sat.Literal))
    (h : ∀ oc ∈ cs, MaskOrigin grid e old newIndex models oc.1 oc.2) :
    ∀ oc ∈ cs, ValidOrigin (fun i => maskPoints (grid i)) e old newIndex models oc.1 oc.2 := by
  intro oc hoc
  exact maskOrigin_sound grid e old newIndex models oc.1 oc.2 (h oc hoc)

end Papers.RationalityTen.MatroidChecked.MaskOrigins
