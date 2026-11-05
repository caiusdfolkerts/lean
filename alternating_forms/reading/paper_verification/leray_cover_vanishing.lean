module

public import TauCeti.Topology.Sheaves.Leray
public import TauCeti.CategoryTheory.Sites.SheafCohomology.FreeYoneda

/-!
# Acyclic and sectionless finite covers

If an abelian sheaf has zero cohomology in every degree on every nonempty
finite intersection of a finite open cover, then it has zero global cohomology.
The proof uses the genuine Čech–Leray comparison and the actual section groups.
The cover need not consist of affine opens. In particular it applies to the
preimages of an affine frame cover under a projective-line bundle.
-/

@[expose] public section
noncomputable section

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open TauCeti.CategoryTheory

namespace PaperVerification.LerayCoverVanishing

variable {X : TopCat.{u}} {ι : Type u} [Finite ι]
  (U : ι → Opens X) (hU : iSup U = ⊤)
  (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})

include hU

/-- A finite cover whose every intersection is acyclic in all degrees
forces global acyclicity, including degree zero. -/
theorem cohomology_subsingleton
    (hF : ∀ s : Finset ι, s.Nonempty → ∀ q, Subsingleton (F.H' q (s.inf U)))
    (q : ℕ) : Subsingleton (Sheaf.H F q) := by
  classical
  let K := (cechComplexFunctor U).obj F.obj
  have hsections (n : ℕ) (a : Fin (n + 1) → ι) :
      Subsingleton (F.obj.obj (op (∏ᶜ fun j ↦ U (a j)))) := by
    have heq : (∏ᶜ fun j ↦ U (a j)) = (Finset.univ.image a).inf U :=
      CompleteLattice.finite_product_eq_finset_image_inf U a
    have hzero : Subsingleton (F.H' 0 (∏ᶜ fun j ↦ U (a j))) := by
      rw [heq]
      exact hF _ (Finset.univ_nonempty.image a) 0
    letI := hzero
    exact (cohomologyZeroSectionsEquiv F _).symm.injective.subsingleton
  have hterm (n : ℕ) : IsZero (K.X n) := by
    change IsZero (∏ᶜ fun a : Fin (n + 1) → ι ↦
      F.obj.obj (op (∏ᶜ fun j ↦ U (a j))))
    apply (IsZero.iff_id_eq_zero _).mpr
    apply Pi.hom_ext
    intro a
    letI := hsections n a
    exact (AddCommGrpCat.isZero_of_subsingleton _).eq_of_tgt _ _
  have hhomology : IsZero (K.homology q) :=
    (K.sc q).isZero_homology_of_isZero_X₂ (hterm q)
  let e := TauCeti.Topology.homologyCechComplexIsoH U hU F
    (fun s hs k ↦ hF s hs (k + 1)) q
  exact AddCommGrpCat.subsingleton_of_isZero (hhomology.of_iso e.symm)

end PaperVerification.LerayCoverVanishing
