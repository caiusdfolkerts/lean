module

public import PaperVerification.AlternatingFormsPrefixSelection
public import Mathlib.Data.List.FinRange

/-!
# The original increasing word and its complete prefix decomposition

The selected even and odd prefix vertices, followed by every remaining
vertex, form a permutation of the original increasing tuple.  The exterior
identity retains the resulting nonzero scalar.  Thus no suffix, order, or
coordinate factor is suppressed when applying the prefix inverse.
-/

@[expose] public section
set_option autoImplicit false

noncomputable section

namespace PaperVerification.AlternatingForms

open scoped BigOperators

variable {k s h : ℕ}

def oddPrefixLeft (hk : h≤k) (i : Fin h) : Fin (2*k+1) :=
  oddPathFirstLeft (Fin.castLE hk i)

def oddPrefixRight (hk : h≤k) (i : Fin h) : Fin (2*k+1) :=
  oddPathMiddle (Fin.castLE hk i)

@[simp] theorem oddPrefixLeft_val (hk : h≤k) (i : Fin h) :
    (oddPrefixLeft hk i).val=2*i.val := rfl

@[simp] theorem oddPrefixRight_val (hk : h≤k) (i : Fin h) :
    (oddPrefixRight hk i).val=2*i.val+1 := rfl

theorem oddPrefixLeft_injective (hk : h≤k) : Function.Injective (oddPrefixLeft hk) := by
  intro a b hab
  have he := congrArg Fin.val hab
  simp only [oddPrefixLeft_val] at he
  apply Fin.ext
  omega

theorem oddPrefixRight_injective (hk : h≤k) : Function.Injective (oddPrefixRight hk) := by
  intro a b hab
  have he := congrArg Fin.val hab
  simp only [oddPrefixRight_val] at he
  apply Fin.ext
  omega

def tuplePrefixSuffix (I : Fin s → Fin (2*k+1)) (h : ℕ) : Finset (Fin (2*k+1)) :=
  (Finset.univ.image I).filter (fun q => 2*h≤q.val)

theorem mem_tuplePrefixSuffix (I : Fin s → Fin (2*k+1)) (h : ℕ)
    (q : Fin (2*k+1)) :
    q∈tuplePrefixSuffix I h ↔ (∃ i,I i=q) ∧ 2*h≤q.val := by
  simp only [tuplePrefixSuffix,Finset.mem_filter,Finset.mem_image,Finset.mem_univ,
    true_and]

def tuplePrefixWord (I : Fin s → Fin (2*k+1)) (hI : StrictMono I) (hk : h≤k) :
    List (Fin (2*k+1)) :=
  ((tuplePrefixLeft I hI h).toList.map (oddPrefixLeft hk) ++
    (tuplePrefixRight I hI h).toList.map (oddPrefixRight hk)) ++
      (tuplePrefixSuffix I h).toList

theorem mem_tuplePrefixWord (I : Fin s → Fin (2*k+1)) (hI : StrictMono I)
    (hk : h≤k) (q : Fin (2*k+1)) :
    q∈tuplePrefixWord I hI hk ↔ ∃ i,I i=q := by
  simp only [tuplePrefixWord,List.mem_append,List.mem_map,Finset.mem_toList,
    mem_tuplePrefixLeft,mem_tuplePrefixRight,mem_tuplePrefixSuffix]
  constructor
  · rintro ((⟨a,⟨i,hi⟩,ha⟩ | ⟨a,⟨i,hi⟩,ha⟩) | ⟨hi,hq⟩)
    · exact ⟨i,(Fin.ext hi).trans ha⟩
    · exact ⟨i,(Fin.ext hi).trans ha⟩
    · exact hi
  · rintro ⟨i,hi⟩
    by_cases hq : 2*h≤q.val
    · exact Or.inr ⟨⟨i,hi⟩,hq⟩
    · have hlt : q.val<2*h := by omega
      let q' : Fin (2*h) := ⟨q.val,hlt⟩
      have he := (evenOddPrefixEquiv h).apply_symm_apply q'
      rcases hc : (evenOddPrefixEquiv h).symm q' with a | a
      · rw [hc] at he
        have hev := congrArg Fin.val he
        have hi' : (I i).val=2*a.val := by
          simpa only [hi,evenOddPrefixEquiv_inl] using hev.symm
        exact Or.inl (Or.inl ⟨a,⟨i,hi'⟩,Fin.ext (by
          simpa only [oddPrefixLeft_val,evenOddPrefixEquiv_inl] using hev)⟩)
      · rw [hc] at he
        have hev := congrArg Fin.val he
        have hi' : (I i).val=2*a.val+1 := by
          simpa only [hi,evenOddPrefixEquiv_inr] using hev.symm
        exact Or.inl (Or.inr ⟨a,⟨i,hi'⟩,Fin.ext (by
          simpa only [oddPrefixRight_val,evenOddPrefixEquiv_inr] using hev)⟩)

theorem tuplePrefixWord_nodup (I : Fin s → Fin (2*k+1)) (hI : StrictMono I)
    (hk : h≤k) : (tuplePrefixWord I hI hk).Nodup := by
  unfold tuplePrefixWord
  apply List.nodup_append.mpr
  refine ⟨List.nodup_append.mpr ⟨?_,?_,?_⟩,(tuplePrefixSuffix I h).nodup_toList,?_⟩
  · exact List.Nodup.map (oddPrefixLeft_injective hk) (Finset.nodup_toList _)
  · exact List.Nodup.map (oddPrefixRight_injective hk) (Finset.nodup_toList _)
  · intro a ha b hb hab
    obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hb
    have he := congrArg Fin.val hab
    simp only [oddPrefixLeft_val,oddPrefixRight_val] at he
    omega
  · intro a ha b hb hab
    have hb' := (mem_tuplePrefixSuffix I h b).mp (Finset.mem_toList.mp hb)
    rcases List.mem_append.mp ha with ha | ha
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
      have he := congrArg Fin.val hab
      simp only [oddPrefixLeft_val] at he
      have := i.isLt
      omega
    · obtain ⟨i,hi,rfl⟩ := List.mem_map.mp ha
      have he := congrArg Fin.val hab
      simp only [oddPrefixRight_val] at he
      have := i.isLt
      omega

theorem tuplePrefixWord_perm (I : Fin s → Fin (2*k+1)) (hI : StrictMono I)
    (hk : h≤k) : (tuplePrefixWord I hI hk).Perm (List.ofFn I) := by
  apply (List.perm_ext_iff_of_nodup (tuplePrefixWord_nodup I hI hk)
    (List.nodup_ofFn.mpr hI.injective)).mpr
  intro q
  rw [mem_tuplePrefixWord,List.mem_ofFn']
  rfl

theorem tuplePrefixWord_length (I : Fin s → Fin (2*k+1)) (hI : StrictMono I)
    (hk : h≤k) : (tuplePrefixWord I hI hk).length=s := by
  simpa only [List.length_ofFn] using (tuplePrefixWord_perm I hI hk).length_eq

theorem tuplePrefixWord_weight {A : Type*} [AddCommMonoid A]
    (I : Fin s → Fin (2*k+1)) (hI : StrictMono I) (hk : h≤k)
    (w : Fin (2*k+1) → A) :
    ((tuplePrefixWord I hI hk).map w).sum=∑ i,w (I i) := by
  rw [((tuplePrefixWord_perm I hI hk).map w).sum_eq,List.map_ofFn,List.sum_ofFn]
  rfl

variable {K : Type*} [Field K]

theorem totalExteriorPluckerCoordinates_ofFn (I : PluckerIndex s (2*k+1)) :
    totalExteriorPluckerCoordinates (K := K) s (2*k+1)
      (indexExteriorWord (List.ofFn I.val))=MvPolynomial.X I := by
  have he : indexExteriorWord (K := K) (List.ofFn I.val)=
      (exteriorPluckerBasis (K := K) s (2*k+1) I : ExteriorAlgebra K (Fin (2*k+1) → K)) := by
    rw [exteriorPluckerBasis_apply]
    simp only [indexExteriorWord,exteriorPower.ιMulti_apply_coe,
      ExteriorAlgebra.ιMulti_apply,List.ofFn_comp',List.map_map,Function.comp_def]
  rw [he,totalExteriorPluckerCoordinates_coe,exteriorPluckerCoordinates_basis]

/-- The actual full prefix word gives the original Plücker variable with
its genuine nonzero exterior permutation scalar. -/
theorem tuplePrefixWord_coordinates (I : PluckerIndex s (2*k+1)) (hk : h≤k) :
    ∃ ε : K,ε≠0 ∧
      totalExteriorPluckerCoordinates (K := K) s (2*k+1)
        (indexExteriorWord (tuplePrefixWord I.val I.property hk))=
          ε • MvPolynomial.X I := by
  obtain ⟨ε,hε,he⟩ := exterior_word_permutation (K := K)
    ((tuplePrefixWord_perm I.val I.property hk).map (Pi.basisFun K (Fin (2*k+1))))
  have he' : indexExteriorWord (K := K) (tuplePrefixWord I.val I.property hk)=
      ε • indexExteriorWord (List.ofFn I.val) := by
    simpa only [indexExteriorWord,List.map_map,Function.comp_def] using he
  exact ⟨ε,hε,by rw [he',map_smul,totalExteriorPluckerCoordinates_ofFn]⟩

end PaperVerification.AlternatingForms
