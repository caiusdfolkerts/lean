module
public import shared_results.part008

set_option Elab.async false
set_option maxRecDepth 4096
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

@[expose] public section

/- BEGIN EXACT BODY: FourPapers.Sublattice.FixedFaceGrading -/
section

/-! # Exact exterior-degree shifts under a fixed face factor

Unlike the residue-grading consequence, these lemmas retain the exact
natural homological degree. They are used to identify the coefficients
of the exterior factor in Lemma 6.1.
-/

section
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 20000
set_option synthInstance.maxHeartbeats 5000
set_option maxRecDepth 4096
noncomputable section
namespace FourPapers.Sublattice
open Classical CommAlg CommAlg.Koszul CommAlg.Polymatroid
universe u
variable {V k : Type u} [Fintype V] [LinearOrder V] [CommRing k]

lemma fixedFaceFactorEquiv_mem_degree
    (S : V → Prop) (A : Finset V) (Q : Finset V → Prop)
    (hA : ∀ v ∈ A, S v) (hQ : ∀ G, Q G → ∀ v ∈ G, ¬S v)
    (p : ℕ) (x : TotalFaceModule (k := k) Q)
    (hx : x ∈ totalFacePiece Q p) :
    fixedFaceFactorEquiv S A Q hA hQ x ∈
      totalFacePiece (splitFacePredicate S (fun F => F=A) Q) (p+A.card) := by
  have hm : totalFacePiece (k := k) Q p ≤
      (totalFacePiece (splitFacePredicate S (fun F => F=A) Q) (p+A.card)).comap
        (fixedFaceFactorEquiv S A Q hA hQ).toLinearMap := by
    rw [totalFacePiece_eq_basis_span]
    apply Submodule.span_le.mpr
    rintro y ⟨G,hG,rfl⟩
    change fixedFaceFactorEquiv (k := k) S A Q hA hQ (totalFaceBasis Q G) ∈
      totalFacePiece (k := k) (splitFacePredicate S (fun F => F=A) Q) (p+A.card)
    rw [fixedFaceFactorEquiv,signedBasisEquiv_basis,totalFacePiece_eq_basis_span]
    rw [Units.smul_def, ← Int.cast_smul_eq_zsmul k]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    refine ⟨fixedFaceIndexEquiv S A Q hA hQ G,?_,rfl⟩
    change (fixedFaceIndexEquiv S A Q hA hQ G).val.card = p+A.card
    rw [fixedFaceIndexEquiv_card,hG,Nat.add_comm]
  exact hm hx

lemma fixedFaceFactorEquiv_symm_mem_degree
    (S : V → Prop) (A : Finset V) (Q : Finset V → Prop)
    (hA : ∀ v ∈ A, S v) (hQ : ∀ G, Q G → ∀ v ∈ G, ¬S v)
    (p : ℕ) (x : TotalFaceModule (k := k) (splitFacePredicate S (fun F => F=A) Q))
    (hx : x ∈ totalFacePiece (splitFacePredicate S (fun F => F=A) Q) (p+A.card)) :
    (fixedFaceFactorEquiv S A Q hA hQ).symm x ∈ totalFacePiece Q p := by
  have hm : totalFacePiece (k := k) (splitFacePredicate S (fun F => F=A) Q) (p+A.card) ≤
      (totalFacePiece Q p).comap (fixedFaceFactorEquiv S A Q hA hQ).symm.toLinearMap := by
    rw [totalFacePiece_eq_basis_span]
    apply Submodule.span_le.mpr
    rintro y ⟨F,hF,rfl⟩
    change (fixedFaceFactorEquiv (k := k) S A Q hA hQ).symm (totalFaceBasis _ F) ∈
      totalFacePiece (k := k) Q p
    rw [fixedFaceFactorEquiv,signedBasisEquiv_symm_basis,totalFacePiece_eq_basis_span]
    rw [Units.smul_def, ← Int.cast_smul_eq_zsmul k]
    apply Submodule.smul_mem
    apply Submodule.subset_span
    let G := (fixedFaceIndexEquiv S A Q hA hQ).symm F
    refine ⟨G,?_,rfl⟩
    have hc := fixedFaceIndexEquiv_card S A Q hA hQ G
    rw [(fixedFaceIndexEquiv S A Q hA hQ).apply_symm_apply] at hc
    change F.val.card = p+A.card at hF
    change G.val.card = p
    omega
  exact hm hx

/-- Below the size of the forced face, the entire chain module vanishes. -/
lemma fixedFacePiece_eq_zero_of_lt
    (S : V → Prop) (A : Finset V) (Q : Finset V → Prop)
    (hA : ∀ v ∈ A, S v) (hQ : ∀ G, Q G → ∀ v ∈ G, ¬S v)
    (p : ℕ) (hp : p < A.card)
    (x : TotalFaceModule (k := k) (splitFacePredicate S (fun F => F=A) Q))
    (hx : x ∈ totalFacePiece (splitFacePredicate S (fun F => F=A) Q) p) : x = 0 := by
  have hb : totalFacePiece (k := k) (splitFacePredicate S (fun F => F=A) Q) p ≤ ⊥ := by
    rw [totalFacePiece_eq_basis_span]
    apply Submodule.span_le.mpr
    rintro y ⟨F,hF,rfl⟩
    let G := (fixedFaceIndexEquiv S A Q hA hQ).symm F
    have hc := fixedFaceIndexEquiv_card S A Q hA hQ G
    rw [(fixedFaceIndexEquiv S A Q hA hQ).apply_symm_apply] at hc
    change F.val.card = p at hF
    exact False.elim (by omega)
  exact hb hx

end FourPapers.Sublattice

end
end
end


end
