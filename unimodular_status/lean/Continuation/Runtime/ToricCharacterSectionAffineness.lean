module

public import Continuation.Runtime.ToricRegularCoaction
public import Continuation.Runtime.CartierRatioOpenGeometry
public import Continuation.Runtime.ToricOpenRationalTransport

/-!
# Affineness of invariant character-section opens

Suppose an actual Cartier section with affine nonvanishing open is a
finite sum of character sections with distinct original exponents. On
an invariant character open, division by that character gives a finite
sum of actual regular monomials; its distinguished coefficient is one.
The faithful-flat Laurent criterion proves that character open affine.

All hypotheses concern the original Cartier sheaf, its ordinary sections,
their actual rational values, and the actual group-scheme action.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open AlgebraicGeometry CategoryTheory TopologicalSpace
open MonoidalCategory CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

namespace PaperVerification.ToricSchemes.SplitToricEmbedding

variable {k : Type u} [Field k] {n : ℕ}
    {X : Over (Spec (CommRingCat.of k))}
    [ModObj (splitTorusOver k (Fin n → ℤ)) X]
    [IsIntegral X.left] [Smooth X.hom] [NoetherianSpace X.left]
    (T : SplitToricEmbedding k n X)

/-- The ordinary quotient of two Laurent character values has the
original exponent difference and coefficient quotient. -/
theorem laurentValue_single_div (i j : Fin n → ℤ) (a b : k) (hb : b ≠ 0) :
    openTorusRationalAlgHom k n X.left T.torus.left
        (AddMonoidAlgebra.single (i - j) (a / b)) =
      openTorusRationalAlgHom k n X.left T.torus.left (AddMonoidAlgebra.single i a) /
        openTorusRationalAlgHom k n X.left T.torus.left (AddMonoidAlgebra.single j b) := by
  let value := openTorusRationalAlgHom k n X.left T.torus.left
  have hden : value (AddMonoidAlgebra.single j b) ≠ 0 :=
    (map_ne_zero_iff value (openTorusRationalAlgHom_injective k n X.left T.torus.left)).mpr
      (AddMonoidAlgebra.single_ne_zero.mpr hb)
  apply (eq_div_iff hden).mpr
  rw [← map_mul, AddMonoidAlgebra.single_mul_single, sub_add_cancel,
    div_mul_cancel₀ _ hb]

/-- An invariant nonvanishing character section is affine once the
ordinary equation section has affine nonvanishing open. -/
theorem isAffine_characterSectionOpen
    {index : Type u} [Fintype index]
    (C : RationalCartierCocycle X.left) (s : Γ(C.sheaf, ⊤))
    (t : index → Γ(C.sheaf, ⊤)) (w : index → Fin n → ℤ)
    (hw : Function.Injective w) (c : index → k)
    (hvalue : ∀ j, C.toCartierData.sectionValue ⊤ (t j) =
      openTorusRationalAlgHom k n X.left T.torus.left
        (AddMonoidAlgebra.single (w j) (c j)))
    (hsum : C.toCartierData.sectionValue ⊤ s =
      ∑ j, C.toCartierData.sectionValue ⊤ (t j))
    (hD : IsAffineOpen (C.nonvanishingOpen s))
    (m : index) (hcm : c m ≠ 0)
    (hInv : (γ[splitTorusOver k (Fin n → ℤ),X]).left ⁻¹ᵁ C.nonvanishingOpen (t m) =
      (snd (splitTorusOver k (Fin n → ℤ)) X).left ⁻¹ᵁ C.nonvanishingOpen (t m))
    (hT : T.torusOpen ≤ C.nonvanishingOpen (t m)) :
    IsAffineOpen (C.nonvanishingOpen (t m)) := by
  classical
  let G := splitTorusOver k (Fin n → ℤ)
  let V := C.nonvanishingOpen (t m)
  let Z := GroupAction.openOver X V
  letI : Nonempty V := by
    let z := genericPoint G.left
    exact ⟨⟨T.torus.left z, hT ⟨z, rfl⟩⟩⟩
  letI : IsIntegral V.toScheme := isIntegral_of_isOpenImmersion V.ι
  letI : IsIntegral Z.left := inferInstanceAs (IsIntegral V.toScheme)
  letI : IsIntegral (GroupAction.openOver X V).left := inferInstanceAs (IsIntegral V.toScheme)
  letI : IsDominant (GroupAction.openInclusion X V).left := inferInstanceAs (IsDominant V.ι)
  letI : NoetherianSpace (GroupAction.openOver X V).left := by
    change NoetherianSpace (V : Set X.left)
    infer_instance
  letI := GroupAction.restrictedModObj X G V hInv
  letI : Smooth Z.hom := by
    change Smooth (V.ι ≫ X.hom)
    infer_instance
  let S := T.restrictToInvariantOpen V hInv hT
  let r : index → Γ(V.toScheme, ⊤) := fun j => C.ratioGlobalSection (t j) (t m)
  let r₀ : Γ(V.toScheme, ⊤) := C.ratioGlobalSection s (t m)
  let weight : index → Fin n → ℤ := fun j => w j - w m
  let coeff : index → k := fun j => c j / c m
  have hweight : Function.Injective weight := by
    intro i j hij
    apply hw
    have he := congrArg (fun q => q + w m) hij
    simpa only [weight, sub_add_cancel] using he
  have hr : ∀ j, V.toScheme.germToFunctionField ⊤ (r j) =
      openTorusRationalAlgHom k n Z.left S.torus.left
        (AddMonoidAlgebra.single (weight j) (coeff j)) := by
    intro j
    rw [show r j = C.ratioGlobalSection (t j) (t m) from rfl,
      C.ratioGlobalSection_value, hvalue j, hvalue m,
      ← T.laurentValue_single_div (w j) (w m) (c j) (c m) hcm]
    exact T.laurentValue_pullback S (GroupAction.openInclusion X V)
      (T.restrictToInvariantOpen_torus V hInv hT) _
  have hsumr : r₀ = ∑ j, r j := by
    apply V.toScheme.germToFunctionField_injective ⊤
    rw [map_sum]
    dsimp only [r, r₀]
    have hratio (q : Γ(C.sheaf, ⊤)) :
        V.toScheme.germToFunctionField ⊤ (C.ratioGlobalSection q (t m)) =
          dominantFunctionFieldMap V.ι (C.toCartierData.sectionValue ⊤ q / C.toCartierData.sectionValue ⊤ (t m)) :=
      C.ratioGlobalSection_value q (t m)
    simp only [hratio]
    rw [← map_sum, ← Finset.sum_div, ← hsum]
  have hm : r m = 1 := C.ratioGlobalSection_self (t m)
  have hDsum : IsAffineOpen (V.toScheme.basicOpen (∑ j, r j)) := by
    rw [← hsumr]
    exact C.ratioGlobalSection_basicOpen_isAffine s (t m) hD
  exact S.isAffine_of_regular_monomial_sum weight hweight coeff r hr m hm hDsum

end PaperVerification.ToricSchemes.SplitToricEmbedding

#print axioms PaperVerification.ToricSchemes.SplitToricEmbedding.isAffine_characterSectionOpen
