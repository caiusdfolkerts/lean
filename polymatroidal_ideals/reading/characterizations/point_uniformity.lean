import Characterizations.FiniteUniform

/-! # Uniform distribution of pointed final triples -/

noncomputable section
namespace Characterizations
open Classical Finset
variable {V : Type*} [Fintype V] [DecidableEq V]

def PointedTriple.map (σ : Equiv.Perm V) (P : PointedTriple V) : PointedTriple V :=
  ⟨σ P.1, ⟨P.2.val.map σ.toEmbedding, by
    intro x hx
    obtain ⟨y,hy,rfl⟩ := mem_map.mp hx
    exact mem_erase.mpr ⟨fun he => (mem_erase.mp (P.2.property.1 hy)).1 (σ.injective he), mem_univ _⟩,
    by simpa using P.2.property.2⟩⟩

theorem CoversPoint.map {o : VariableOrder V} {P : PointedTriple V}
    (h : CoversPoint o P) (σ : Equiv.Perm V) :
    CoversPoint (σ.symm.trans o) (P.map σ) := by
  obtain ⟨i,q,hiq,hA,hf⟩ := h
  refine ⟨σ i,σ q,fun he => hiq (σ.injective he),?_,?_,?_,?_⟩
  · simp [PointedTriple.map,hA]
  · simpa [PointedTriple.map] using hf.1
  · simpa [PointedTriple.map] using hf.2.1
  · intro x hxi hxq hxj
    have hxi' : σ.symm x ≠ i := fun he => hxi (by simpa using congrArg σ he)
    have hxq' : σ.symm x ≠ q := fun he => hxq (by simpa using congrArg σ he)
    have hxj' : σ.symm x ≠ P.1 := fun he => hxj (by simpa [PointedTriple.map] using congrArg σ he)
    simpa using hf.2.2 (σ.symm x) hxi' hxq' hxj'

theorem exists_order_covering_point (P : PointedTriple V) :
    ∃ o : VariableOrder V, CoversPoint o P := by
  obtain ⟨i,q,hiq,hA⟩ := card_eq_two.mp P.2.property.2
  have hij : i ≠ P.1 := (mem_erase.mp (P.2.property.1 (by simp [hA]))).1
  have hqj : q ≠ P.1 := (mem_erase.mp (P.2.property.1 (by simp [hA]))).1
  obtain ⟨o,ho⟩ := exists_finalTriple i q P.1 hiq hij hqj
  exact ⟨o,i,q,hiq,hA,ho⟩

def pointFiberEquiv (P Q : PointedTriple V) :
    {o : VariableOrder V // CoversPoint o P} ≃ {o : VariableOrder V // CoversPoint o Q} := by
  let oP := (exists_order_covering_point P).choose
  have hP : CoversPoint oP P := (exists_order_covering_point P).choose_spec
  let oQ := (exists_order_covering_point Q).choose
  have hQ : CoversPoint oQ Q := (exists_order_covering_point Q).choose_spec
  let σ : Equiv.Perm V := oP.trans oQ.symm
  have hmap : P.map σ = Q := by
    apply coversPoint_unique _ hQ
    have hh := hP.map σ
    have he : σ.symm.trans oP = oQ := by ext x; simp [σ]
    simpa only [he] using hh
  have hmapinv : Q.map σ.symm = P := by
    apply coversPoint_unique _ hP
    have hh := hQ.map σ.symm
    have he : σ.trans oQ = oP := by ext x; simp [σ]
    simpa only [Equiv.symm_symm,he] using hh
  refine {
    toFun := fun o => ⟨σ.symm.trans o.val, hmap ▸ o.property.map σ⟩
    invFun := fun o => ⟨σ.trans o.val, ?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · simpa only [Equiv.symm_symm] using (hmapinv ▸ o.property.map σ.symm)
  · intro o; apply Subtype.ext; ext x; simp
  · intro o; apply Subtype.ext; ext x; simp

theorem exists_point_covered (hcard : 3 ≤ Fintype.card V) (o : VariableOrder V) :
    ∃ P : PointedTriple V, CoversPoint o P := by
  let i := o.symm ⟨Fintype.card V-3,by omega⟩
  let q := o.symm ⟨Fintype.card V-2,by omega⟩
  let j := o.symm ⟨Fintype.card V-1,by omega⟩
  have hi : (o i).val = Fintype.card V-3 := by simp [i]
  have hq : (o q).val = Fintype.card V-2 := by simp [q]
  have hj : (o j).val = Fintype.card V-1 := by simp [j]
  have hiq : i ≠ q := by intro he; rw [he] at hi; omega
  have hij : i ≠ j := by intro he; rw [he] at hi; omega
  have hqj : q ≠ j := by intro he; rw [he] at hq; omega
  let P : PointedTriple V := ⟨j,⟨{i,q},by simp [insert_subset_iff,hij,hqj],by simp [hiq]⟩⟩
  refine ⟨P,i,q,hiq,rfl,?_,?_,?_⟩
  · change (o i).val < (o j).val
    omega
  · change (o q).val < (o j).val
    omega
  · intro x hxi hxq hxj
    have hn1 : (o x).val ≠ (o i).val := fun he => hxi (o.injective (Fin.ext he))
    have hn2 : (o x).val ≠ (o q).val := fun he => hxq (o.injective (Fin.ext he))
    have hn3 : (o x).val ≠ (o j).val := fun he => hxj (o.injective (Fin.ext he))
    have hxlt := (o x).isLt
    change (o x).val < (o i).val ∧ (o x).val < (o q).val
    omega

def finalPoint (hcard : 3 ≤ Fintype.card V) (o : VariableOrder V) : PointedTriple V :=
  (exists_point_covered hcard o).choose

theorem finalPoint_spec (hcard : 3 ≤ Fintype.card V) (o : VariableOrder V) :
    CoversPoint o (finalPoint hcard o) := (exists_point_covered hcard o).choose_spec

theorem finalPoint_eq_iff (hcard : 3 ≤ Fintype.card V) (o : VariableOrder V) (P : PointedTriple V) :
    finalPoint hcard o = P ↔ CoversPoint o P :=
  ⟨fun h => h ▸ finalPoint_spec hcard o, fun h => coversPoint_unique (finalPoint_spec hcard o) h⟩

theorem pointedTriple_probability (hcard : 3 ≤ Fintype.card V) (P : PointedTriple V) :
    finiteFraction (fun o : VariableOrder V => CoversPoint o P) =
      1 / (Fintype.card V * (Fintype.card V - 1).choose 2 : ℕ) := by
  letI : Nonempty (VariableOrder V) := ⟨Fintype.equivFin V⟩
  let c := Nat.card {o : VariableOrder V // CoversPoint o P}
  have hc (Q : PointedTriple V) : Nat.card {o : VariableOrder V // finalPoint hcard o = Q} = c := by
    calc
      _ = Nat.card {o : VariableOrder V // CoversPoint o Q} :=
        Nat.card_congr (Equiv.subtypeEquivRight (fun o => finalPoint_eq_iff hcard o Q))
      _ = c := Nat.card_congr (pointFiberEquiv Q P)
  have hh := fraction_preimage_of_constant_fiber (finalPoint hcard) (fun Q => Q = P) c hc
  have he : (fun o : VariableOrder V => finalPoint hcard o = P) = (fun o => CoversPoint o P) :=
    funext (fun o => propext (finalPoint_eq_iff hcard o P))
  rw [he] at hh
  simpa [finiteFraction,Nat.card_eq_fintype_card,card_pointedTriple] using hh

end Characterizations
