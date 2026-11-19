module

public import ToricPower.SerrePairingDifferential
public import ToricPower.LinearHomComplexPrecomp

/-!
# Naturality of the signed pairing of actual Hom cochains

Both identities concern the literal precomposition and postcomposition
maps of the signed Hom complexes. The target identity permits different
finite supports, so the pairing is independent of a chosen common
bounding interval.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CochainComplex
open CochainComplex.HomComplex

namespace ToricPower.SerrePairing

universe u v r
variable (k : Type r) [Field k]
variable {A : Type u} [Category.{v} A] [Abelian A] [Linear k A]
variable (T : A ⥤ A) [T.Additive]

theorem finiteCochainPairingEquiv_source_naturality
    (J : CochainComplex A ℤ) (pairing : ∀ q, CodomainPairing k T (J.X q))
    {E F : CochainComplex A ℤ} (h : E ⟶ F)
    (support : Finset ℤ) (outside : ∀ q, q ∉ support → IsZero (J.X q))
    (n : ℤ) (f : Cochain F J n) (g : Cochain (mappedCochainComplex T J) E (-n)) :
    finiteCochainPairingEquiv k T J pairing E support outside n
        (homCochainPrecomp k h J n f) g =
      finiteCochainPairingEquiv k T J pairing F support outside n f
        (homCochainPostcomp k (mappedCochainComplex T J) h (-n) g) := by
  rw [finiteCochainPairingEquiv_eq_finsum, finiteCochainPairingEquiv_eq_finsum]
  apply finsum_congr
  intro q
  unfold cochainPairingTerm
  rw [homCochainPrecomp_v, homCochainPostcomp_v]
  exact congrArg (fun x : k => q.negOnePow • x)
    ((pairing q).naturality (h.f (q - n)) _ _)

theorem finiteCochainPairingEquiv_target_naturality
    (J K : CochainComplex A ℤ)
    (pairingJ : ∀ q, CodomainPairing k T (J.X q))
    (pairingK : ∀ q, CodomainPairing k T (K.X q))
    (h : J ⟶ K)
    (compatible : ∀ q, Compatible k (pairingJ q) (pairingK q) (h.f q))
    (E : CochainComplex A ℤ)
    (supportJ : Finset ℤ) (outsideJ : ∀ q, q ∉ supportJ → IsZero (J.X q))
    (supportK : Finset ℤ) (outsideK : ∀ q, q ∉ supportK → IsZero (K.X q))
    (n : ℤ) (f : Cochain E J n) (g : Cochain (mappedCochainComplex T K) E (-n)) :
    finiteCochainPairingEquiv k T K pairingK E supportK outsideK n
        (homCochainPostcomp k E h n f) g =
      finiteCochainPairingEquiv k T J pairingJ E supportJ outsideJ n f
        (homCochainPrecomp k ((T.mapHomologicalComplex (.up ℤ)).map h) E (-n) g) := by
  rw [finiteCochainPairingEquiv_eq_finsum, finiteCochainPairingEquiv_eq_finsum]
  apply finsum_congr
  intro q
  unfold cochainPairingTerm
  rw [homCochainPostcomp_v, homCochainPrecomp_v]
  exact congrArg (fun x : k => q.negOnePow • x)
    (compatible q (E.X (q - n)) (f.v (q - n) q (by omega))
      (g.v q (q - n) (by omega)))

theorem finiteCochainPairingEquiv_support_independent
    (J : CochainComplex A ℤ) (pairing : ∀ q, CodomainPairing k T (J.X q))
    (E : CochainComplex A ℤ)
    (support support' : Finset ℤ)
    (outside : ∀ q, q ∉ support → IsZero (J.X q))
    (outside' : ∀ q, q ∉ support' → IsZero (J.X q)) (n : ℤ) :
    finiteCochainPairingEquiv k T J pairing E support outside n =
      finiteCochainPairingEquiv k T J pairing E support' outside' n := by
  apply LinearEquiv.ext
  intro f
  apply LinearMap.ext
  intro g
  rw [finiteCochainPairingEquiv_eq_finsum, finiteCochainPairingEquiv_eq_finsum]

end ToricPower.SerrePairing

end
