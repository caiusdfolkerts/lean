module
import all Mathlib.AlgebraicGeometry.Modules.Sheaf
import all Mathlib.RingTheory.OreLocalization.Basic
import all Mathlib.Algebra.MonoidAlgebra.Defs
public import SegreVerified.Stage001
import all SegreVerified.Stage001
public import SegreVerified.Stage002
import all SegreVerified.Stage002
public import SegreVerified.Stage003
import all SegreVerified.Stage003
public import SegreVerified.Stage004
import all SegreVerified.Stage004
public import SegreVerified.Stage005
import all SegreVerified.Stage005
public import SegreVerified.Stage006
import all SegreVerified.Stage006
public import SegreVerified.Stage007
import all SegreVerified.Stage007
public import SegreVerified.Stage008
import all SegreVerified.Stage008
public import SegreVerified.Stage009
import all SegreVerified.Stage009
public import SegreVerified.Stage010
import all SegreVerified.Stage010
public import SegreVerified.Stage011
import all SegreVerified.Stage011
public import SegreVerified.Stage012
import all SegreVerified.Stage012
public import SegreVerified.Stage013
import all SegreVerified.Stage013
public import SegreVerified.Stage014
import all SegreVerified.Stage014
public import SegreVerified.Stage015
import all SegreVerified.Stage015
public import SegreVerified.Stage016
import all SegreVerified.Stage016
public import SegreVerified.Stage017
import all SegreVerified.Stage017
public import SegreVerified.Stage018
import all SegreVerified.Stage018
public import SegreVerified.Stage019
import all SegreVerified.Stage019
public import SegreVerified.Stage020
import all SegreVerified.Stage020
public import SegreVerified.Stage021
import all SegreVerified.Stage021
public import SegreVerified.Stage022
import all SegreVerified.Stage022
public import SegreVerified.Stage023
import all SegreVerified.Stage023
public import SegreVerified.Stage024
import all SegreVerified.Stage024

public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.LinearAlgebra.Matrix.Hermitian
public import Mathlib.LinearAlgebra.Matrix.Rank
public import Mathlib.Data.Matrix.ColumnRowPartitioned
public import Mathlib.FieldTheory.Finiteness
public import Mathlib.LinearAlgebra.LinearIndependent.BaseChange
public import Mathlib.Algebra.MvPolynomial.Funext
public import Mathlib.Tactic.Push
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fin.Basic
public import Lean.Elab.Tactic.Omega
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.NormNum
public import Mathlib.Algebra.Group.Finsupp
public import Mathlib.RingTheory.MvPolynomial.Basic
public import Mathlib.LinearAlgebra.Basis.Basic
public import Mathlib.RingTheory.MvPolynomial.WeightedHomogeneous
public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.RingTheory.Polynomial.ContentIdeal
public import Mathlib.Algebra.BigOperators.Ring.Finset
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Field.Defs
public import Mathlib.Combinatorics.SimpleGraph.Basic
public import Mathlib.RingTheory.IntegralClosure.IsIntegral.Basic
public import Mathlib.RingTheory.Artinian.Module
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.Finiteness.Ideal
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.Data.Fin.Tuple.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Data.Fintype.Basic
public import Mathlib.Data.Sym.Basic
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Data.Finset.NatAntidiagonal
public import Mathlib.Data.Finsupp.Multiset
public import Mathlib.Data.Fintype.EquivFin
public import Mathlib.Data.List.FinRange
public import Mathlib.Logic.Equiv.Fin.Basic
public import Mathlib.Data.Fintype.Perm
public import Mathlib.LinearAlgebra.PiTensorProduct.Finite
public import Mathlib.LinearAlgebra.TensorPower.Symmetric
public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.Data.Sym.Card
public import Mathlib.LinearAlgebra.PiTensorProduct.Basis
public import Mathlib.LinearAlgebra.Trace
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basic
public import Mathlib.RingTheory.Ideal.Maps
public import Mathlib.LinearAlgebra.Basis.VectorSpace
public import Mathlib.LinearAlgebra.Isomorphisms
public import Mathlib.RingTheory.FilteredAlgebra.Basic
public import Mathlib.Algebra.DirectSum.Internal
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.MvPolynomial.Homogeneous
public import Mathlib.LinearAlgebra.Dimension.Finrank
public import Mathlib.LinearAlgebra.InvariantBasisNumber
public import Mathlib.Algebra.Order.Antidiag.FinsuppEquiv
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Algebra.MvPolynomial.Division
public import Mathlib.Algebra.MvPolynomial.Equiv
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.Data.Sym.NatCard
public import Mathlib.RingTheory.GradedAlgebra.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
public import Mathlib.Tactic.LinearCombination
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.LinearAlgebra.Matrix.BilinearForm
public import Mathlib.LinearAlgebra.BilinearForm.Properties
public import Mathlib.LinearAlgebra.AffineSpace.Combination
public import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Basic
public import Mathlib.Algebra.Ring.Invertible
public import Mathlib.Algebra.Group.Subgroup.Ker
public import Mathlib.Data.Matrix.Basic
public import Mathlib.Data.Matrix.Basis
public import Mathlib.Algebra.CharP.Defs
public import Mathlib.LinearAlgebra.Matrix.Trace
public import Mathlib.SetTheory.Cardinal.Finite
public import Mathlib.LinearAlgebra.Dimension.RankNullity
public import Mathlib.LinearAlgebra.FiniteDimensional.Basic
public import Mathlib.LinearAlgebra.Finsupp.LinearCombination
public import Mathlib.Algebra.BigOperators.Option
public import Mathlib.Combinatorics.SimpleGraph.Maps
public import Mathlib.Data.Fintype.Sum
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Tactic.FinCases
public import Mathlib.Data.Finset.Option
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.Fin.Basic
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.Tactic.Linarith
public import Mathlib.Order.Sym2
public import Mathlib.LinearAlgebra.Dimension.OrzechProperty
public import Mathlib.Algebra.MvPolynomial.CommRing
public import Mathlib.Algebra.MvPolynomial.Rename
public import Mathlib.LinearAlgebra.LinearIndependent.Basic
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Data.Fintype.Fin
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
public import Mathlib.LinearAlgebra.Pi
public import Mathlib.LinearAlgebra.Finsupp.Defs
public import Mathlib.Algebra.MonoidAlgebra.Basic
public import Mathlib.Algebra.MvPolynomial.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import Mathlib.RingTheory.Localization.Algebra
public import Mathlib.Algebra.MonoidAlgebra.Grading
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Maps
public import Mathlib.RingTheory.GradedAlgebra.TensorProduct
public import Mathlib.RingTheory.IsTensorProduct
public import Mathlib.RingTheory.GradedAlgebra.HomogeneousLocalization
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Functor
public import Mathlib.RingTheory.GradedAlgebra.Radical
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Algebra.GroupWithZero.Action.Defs
public import Mathlib.Data.Nat.Find
public import Mathlib.Topology.QuasiSeparated
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.EpiMono
public import Mathlib.CategoryTheory.Sites.LeftExact
public import Mathlib.Algebra.Category.Grp.Abelian
public import Mathlib.Algebra.Category.Grp.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.Exact
public import Mathlib.Topology.Sheaves.SheafCondition.Sites
public import Mathlib.Algebra.Group.End
public import Mathlib.Algebra.Ring.Parity
public import Mathlib.Logic.Equiv.Fin.Rotate
public import Mathlib.Order.Interval.Finset.Fin
public import Mathlib.Order.SuccPred.Fin
public import Mathlib.Order.SuccPred.IntervalSucc
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Algebra.Group.Fin.Basic
public import Mathlib.AlgebraicTopology.CechNerve
public import Mathlib.AlgebraicTopology.ExtraDegeneracy
public import Mathlib.AlgebraicTopology.SimplicialObject.Homotopy
public import Mathlib.CategoryTheory.Limits.FormalCoproducts.ExtraDegeneracy
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Sites.IsSheafFor
public import Mathlib.Algebra.Homology.Opposite
public import Mathlib.Algebra.Homology.SingleHomology
public import Mathlib.AlgebraicTopology.SimplicialObject.ChainHomotopy
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology
public import Mathlib.Algebra.Homology.ShortComplex.Preadditive
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryBiproducts
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Kernels
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.KernelCokernelComp
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Subobject.Limits
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Linear
public import Mathlib.Algebra.Category.Grp.Adjunctions
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.CategoryTheory.Limits.Shapes.BinaryProducts.BinaryProducts
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Abelian.Refinements
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequenceLemmas
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
public import Mathlib.Algebra.Homology.HomologicalComplexBiprod
public import Mathlib.Algebra.Category.Grp.Biproducts
public import Mathlib.CategoryTheory.Limits.Lattice
public import Mathlib.Algebra.Category.Grp.ForgetCorepresentable
public import Mathlib.Algebra.Homology.ShortComplex.FunctorEquivalence
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Shapes.Products
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.Data.Fintype.Lattice
public import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing
public import Mathlib.CategoryTheory.Limits.FunctorCategory.EpiMono
public import Mathlib.Topology.Sheaves.Functors
public import Mathlib.Algebra.Homology.Single
public import Mathlib.Algebra.Category.ModuleCat.Kernels
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Basic
public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Generator
public import Mathlib.CategoryTheory.Localization.Monoidal.Basic
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import Mathlib.CategoryTheory.Sites.LocallyBijective
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Localization
public import Mathlib.CategoryTheory.Localization.Monoidal.Braided
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.OfCommRing
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import Mathlib.LinearAlgebra.StdBasis
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.PreservesLocallyBijective
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.CategoryTheory.Adjunction.FullyFaithfulLimits
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
public import Mathlib.CategoryTheory.Abelian.Subobject
public import Mathlib.CategoryTheory.Adjunction.AdjointFunctorTheorems
public import Mathlib.CategoryTheory.Monoidal.Closed.Basic
public import Mathlib.CategoryTheory.Monoidal.Closed.Braided
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import Mathlib.Basic.Finite.Sum
public import Mathlib.CategoryTheory.Monoidal.Limits.Cokernels
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.PushforwardZeroMonoidal
public import Mathlib.CategoryTheory.Localization.Monoidal.Functor
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.CategoryTheory.Monoidal.Subcategory
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Adjunction
public import Mathlib.CategoryTheory.Sites.LocalProperties
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Functor.TwoSquare
public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackFree
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
public import Mathlib.CategoryTheory.Monoidal.CoherenceLemmas
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Jointly
public import Mathlib.Algebra.Module.Projective
public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.RingTheory.Finiteness.Basic
public import Mathlib.RingTheory.Localization.BaseChange
public import Mathlib.Algebra.Homology.CommSq
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Biproducts
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
public import Mathlib.CategoryTheory.ObjectProperty.FiniteProducts
public import Mathlib.CategoryTheory.Sites.CoversTop.Over
public import Mathlib.AlgebraicGeometry.Properties
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.CategoryTheory.Linear.FunctorCategory
public import Mathlib.LinearAlgebra.TensorProduct.Pi
public import Mathlib.LinearAlgebra.TensorProduct.Tower
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.Algebra.FiveLemma
public import Mathlib.RingTheory.Flat.Equalizer
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.CategoryTheory.Monoidal.Rigid.Basic
public import Mathlib.CategoryTheory.Monoidal.Linear
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.Algebra.Category.ModuleCat.Adjunctions
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.CategoryTheory.Monoidal.Rigid.OfEquivalence
public import Mathlib.Algebra.Homology.ComplexShapeSigns
public import Mathlib.Algebra.Homology.Embedding.Basic
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.HomologySequence
public import Mathlib.Algebra.Homology.Embedding.HomEquiv
public import Mathlib.Algebra.Homology.TotalComplexSymmetry
public import Mathlib.CategoryTheory.GradedObject.Monoidal
public import Mathlib.CategoryTheory.Sites.SheafCohomology.ExactSequences
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.LinearAlgebra.Prod
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Topology.Sheaves.Skyscraper
public import Mathlib.Algebra.Homology.HomotopyCategory
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.AlgebraicGeometry.Group.Affine
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.RingTheory.LocalProperties.FinitePresentation
public import Mathlib.RingTheory.Finiteness.Finsupp
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Morphisms.Separated
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Category.Grp.Colimits
public import Mathlib.CategoryTheory.Preadditive.Injective.Resolution
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapAdjunction
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.Topology.Sheaves.Over
public import Mathlib.Topology.Category.TopCat.Opens
public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.Algebra.Homology.Homotopy
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.RingTheory.SimpleModule.Basic
public import Mathlib.Algebra.Homology.Bifunctor
public import Mathlib.Algebra.Homology.BifunctorHomotopy
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.CategoryTheory.Monoidal.Opposite
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomologicalBicomplex
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.CategoryTheory.Limits.Preserves.Opposites
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.LinearAlgebra.CliffordAlgebra.Conjugation
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.LinearAlgebra.CliffordAlgebra.Contraction
public import Mathlib.LinearAlgebra.CliffordAlgebra.Grading
public import Mathlib.LinearAlgebra.ExteriorPower.Basis
public import Mathlib.Order.Fin.Tuple
public import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
public import Mathlib.LinearAlgebra.TensorProduct.Associator
public import Mathlib.Algebra.Category.ModuleCat.ExteriorPower
public import Mathlib.RingTheory.Ideal.Colon
public import Mathlib.Algebra.Module.Torsion.Basic
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Module
public import Mathlib.RingTheory.KrullDimension.NonZeroDivisors
public import Mathlib.RingTheory.Nakayama
public import Mathlib.RingTheory.QuotSMulTop
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Localization
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.KrullDimension
public import Mathlib.Order.KrullDimension
public import Mathlib.Data.Nat.Cast.Order.Basic
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.Ideal.Height
public import Mathlib.RingTheory.Spectrum.Prime.RingHom
public import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
public import Mathlib.RingTheory.Ideal.Quotient.Noetherian
public import Mathlib.Topology.LocallyClosed
public import Mathlib.Algebra.Ring.Subgroup
public import Mathlib.Algebra.Ring.Subring.Basic
public import Mathlib.Algebra.Algebra.Subalgebra.Basic
public import Mathlib.LinearAlgebra.Basis.Defs
public import Mathlib.RingTheory.Ideal.Operations
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.LinearAlgebra.Finsupp.Span
public import Mathlib.Algebra.Module.Submodule.Pointwise
public import Mathlib.RingTheory.Regular.RegularSequence
public import Mathlib.Algebra.Category.ModuleCat.Ext.Basic
public import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
public import Mathlib.Data.ENat.Monoid
public import Mathlib.Algebra.Module.FinitePresentation
public import Mathlib.RingTheory.Localization.Module
public import Mathlib.Algebra.Module.LocalizedModule.Submodule
public import Mathlib.RingTheory.Localization.Ideal
public import Mathlib.RingTheory.Depth.Basic
public import Mathlib.RingTheory.KrullDimension.Regular
public import Mathlib.RingTheory.Regular.Category
public import Mathlib.RingTheory.Flat.Localization
public import Mathlib.Algebra.Module.LocalizedModule.Basic
public import Mathlib.RingTheory.Finiteness.Defs
public import Mathlib.RingTheory.Ideal.MinimalPrime.Basic
public import Mathlib.RingTheory.KrullDimension.Field
public import Mathlib.RingTheory.DiscreteValuationRing.TFAE
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
public import Mathlib.RingTheory.Regular.LinearMap
public import Mathlib.RingTheory.IntegralClosure.GoingDown
public import Mathlib.Algebra.Module.Torsion.Free
public import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.QuasiFinite.Basic
public import Mathlib.RingTheory.Artinian.Algebra
public import Mathlib.LinearAlgebra.Dimension.Free
public import Mathlib.RingTheory.Ideal.Cotangent
public import Mathlib.RingTheory.Ideal.Over
public import Mathlib.Algebra.Algebra.Tower
public import Mathlib.LinearAlgebra.Span.Basic
public import Mathlib.RingTheory.Ideal.Defs
public import Mathlib.Algebra.Field.Basic
public import Mathlib.Algebra.Module.Torsion.Field
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.RingTheory.LocalRing.MaximalIdeal.Square
public import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
public import Mathlib.RingTheory.Ideal.AssociatedPrime.Finiteness
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.Localization.LocalizationLocalization
public import Mathlib.RingTheory.Localization.Submodule
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.Algebra.Module.SpanRank
public import Mathlib.LinearAlgebra.Quotient.Basic
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal
public import Mathlib.RingTheory.Finiteness.Nakayama
public import Mathlib.Algebra.Ring.Int.Field
public import Mathlib.RingTheory.Ideal.NatInt
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import Mathlib.RingTheory.LocalRing.Module
public import Mathlib.RingTheory.Support
public import Mathlib.RingTheory.Regular.Flat
public import Mathlib.RingTheory.Ideal.GoingUp
public import Mathlib.RingTheory.Ideal.HasGoingUp
public import Mathlib.RingTheory.KrullDimension.Basic
public import Mathlib.RingTheory.Localization.Integral
public import Mathlib.RingTheory.AlgebraicIndependent.TranscendenceBasis
public import Mathlib.RingTheory.KrullDimension.Polynomial
public import Mathlib.RingTheory.Localization.InvSubmonoid
public import Mathlib.RingTheory.NoetherNormalization
public import Mathlib.RingTheory.Polynomial.RationalRoot
public import Mathlib.RingTheory.Polynomial.UniqueFactorization
public import Mathlib.RingTheory.TensorProduct.MvPolynomial
public import Mathlib.RingTheory.Ideal.UFD
public import Mathlib.RingTheory.RegularLocalRing.Polynomial
public import Mathlib.RingTheory.Artinian.Ring
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import Mathlib.Algebra.Algebra.Operations
public import Mathlib.LinearAlgebra.ExteriorPower.Basic
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Grading
public import Mathlib.LinearAlgebra.TensorProduct.Decomposition
public import Mathlib.RingTheory.RootsOfUnity.EnoughRootsOfUnity
public import Mathlib.RingTheory.RootsOfUnity.CyclotomicUnits
public import Mathlib.RingTheory.RootsOfUnity.Minpoly
public import Mathlib.Algebra.Order.Antidiag.Finsupp
public import Mathlib.Algebra.Polynomial.Degree.Operations
public import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
public import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
public import Mathlib.RingTheory.MvPowerSeries.NoZeroDivisors
public import Mathlib.RingTheory.FinitePresentation
public import Mathlib.RingTheory.GradedAlgebra.Homogeneous.Ideal
public import Mathlib.RingTheory.Nilpotent.Lemmas
public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
public import Mathlib.CategoryTheory.Skeletal
public import Mathlib.Logic.Function.Basic
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.ExteriorPower.WedgePairing
public import Mathlib.Algebra.MvPolynomial.PDeriv
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Logic.Equiv.Set
public import Mathlib.RingTheory.Algebraic.Integral
public import Mathlib.RingTheory.AlgebraicIndependent.Defs
public import Mathlib.RingTheory.Etale.Field
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import Mathlib.RingTheory.Localization.Defs
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.MvPolynomial.Localization
public import Mathlib.RingTheory.Nullstellensatz
public import Mathlib.RingTheory.Smooth.StandardSmoothCotangent
public import Mathlib.RingTheory.Unramified.Field
public import Mathlib.SetTheory.Cardinal.Arithmetic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.RingTheory.Ideal.Quotient.Nilpotent
public import Mathlib.Logic.Equiv.Option
public import Mathlib.LinearAlgebra.Finsupp.Supported
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import Mathlib.LinearAlgebra.BilinearMap
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Algebra.Homology.Additive
public import Mathlib.CategoryTheory.Limits.Shapes.Opposites.Products
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.RingTheory.TensorProduct.IsBaseChangePi
public import Mathlib.RingTheory.LocalProperties.Exactness
public import Mathlib.Algebra.Module.LocalizedModule.Exact
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels
public import Mathlib.CategoryTheory.Limits.Shapes.Biproducts
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Product
public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import Mathlib.Algebra.DirectSum.Decomposition
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Biproducts
public import Mathlib.RingTheory.Ideal.Span
public import Mathlib.Algebra.Module.Submodule.Equiv
public import Mathlib.Algebra.Module.LinearMap.End
public import Mathlib.Algebra.Module.Submodule.Ker
public import Mathlib.Tactic.Abel
public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic
public import Mathlib.LinearAlgebra.TensorProduct.Basis
public import Mathlib.RingTheory.Nilpotent.Defs
public import Mathlib.RingTheory.Ideal.Lattice
public import Mathlib.LinearAlgebra.PiTensorProduct.Basic
public import Mathlib.LinearAlgebra.Multilinear.Curry
public import Mathlib.LinearAlgebra.Dual.Basis
public import Mathlib.Data.Finset.Interval
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Data.Nat.Choose.Basic
public import Mathlib.LinearAlgebra.PiTensorProduct.Dual
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
public import Mathlib.Tactic.Positivity
public import Mathlib.AlgebraicGeometry.IdealSheaf.Subscheme
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.LinearAlgebra.Projectivization.Subspace
public import Lean.Util.CollectAxioms
import all Lean.Util.CollectAxioms
public import Lean.Util.FoldConsts
public import Lean.Util.Sorry
public import Lean.Elab.Command
public import Lean.PrettyPrinter


set_option Elab.async false
set_option linter.all false

#eval do
  let toolchain ← IO.FS.readFile "lean-toolchain"
  let manifest ← IO.FS.readFile "lake-manifest.json"
  IO.println ("SEGRE_PUBLIC_ENVIRONMENT_BEGIN\n" ++ Lean.versionString ++ "\n" ++
    Lean.githash ++ "\n" ++ toolchain.trimAscii.toString ++ "\n" ++ manifest ++
    "\nSEGRE_PUBLIC_ENVIRONMENT_END")

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  unless env.header.trustLevel == 0 do
    throwError "The retained source check requires kernel trust level zero"
  let imported := exportedAxiomsExt.getState (asyncMode := .mainOnly) env
  let rows := CollectAxioms.runM (env.setExporting false) do
    #[``Nat.add_comm, ``Nat.zero_add].mapM fun name =>
      return (name, ← CollectAxioms.collectAndGet imported.find? name)
  for (name, axioms) in rows do
    unless (env.checked.get.find? name).isSome do throwError "Unchecked smoke target: {name}"
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unapproved shared-collector smoke axiom: {ax}"
  logInfo "SEGRE_SHARED_COLLECTOR_READY"


set_option Elab.async false
set_option maxErrors 0
set_option maxRecDepth 2048
set_option synthInstance.maxHeartbeats 200000
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

section ProbeLayer391



/-!
# Singular-vector geometry and all-format spanning theorems

The named sections preserve the original proof stages and local scopes.
-/

@[expose] public section

-- Emit compilation progress immediately while checking this large unit.
set_option stderrAsMessages false
-- Style linting is separate from elaboration, kernel checking, and the axiom audit.
set_option linter.all false
noncomputable section
set_option autoImplicit false


section SegreProjectiveCohomology

run_cmd do
  let out ← IO.getStderr
  out.putStrLn "SEGRE_STAGE SegreProjectiveCohomology"
  out.flush

/-!
# Projective exterior cohomology and the full Koszul gap

The named sections preserve the original proof stages and local scopes.
-/


section SegreProjectiveCech

/-!
# Actual projective-space cohomology from Laurent Čech contraction

The standard coordinate opens form an affine Leray cover. The chosen
categorical Čech products are identified with the actual section tuples,
and the differential is matched component by component. Leray comparison
then gives vanishing of the actual cohomology groups of `O(t)`.
-/

set_option autoImplicit false



attribute [local instance] MvPolynomial.gradedAlgebra

namespace PaperVerification.Segre.ProjectiveCech

open CoordinateLocalization CechMonomials TwistingSections
open AlgebraicGeometry CategoryTheory Limits TopologicalSpace Opposite
open TauCeti.CategoryTheory
open scoped BigOperators

universe w
variable {I K : Type w} [Fintype I] [DecidableEq I] [Field K]

local notation "P" => MvPolynomial I K
local notation "𝒜" => MvPolynomial.homogeneousSubmodule I K

def coordinateOpen (i : I) : (Proj 𝒜).Opens := Proj.basicOpen 𝒜 (MvPolynomial.X i)

theorem chartIntersection_eq_inf (S : Finset I) :
    chartIntersection (K := K) S=S.inf (coordinateOpen (K := K)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [chartIntersection,denominator]
  | @insert i S hi ih =>
      simp only [chartIntersection,denominator,Finset.prod_insert hi,Proj.basicOpen_mul,
        Finset.inf_insert]
      exact congrArg (coordinateOpen i ⊓ ·) ih

theorem coordinate_product_eq {q : ℕ} (a : Fin q → I) :
    (∏ᶜ fun j => coordinateOpen (K := K) (a j))=chartIntersection (tupleCoordinates a) := by
  rw [chartIntersection_eq_inf]
  simpa only [tupleCoordinates] using
    CategoryTheory.Limits.CompleteLattice.finite_product_eq_finset_image_inf
      (coordinateOpen (K := K)) a

/-- The standard coordinate charts cover the actual projective spectrum. -/
theorem coordinate_cover : (⨆ i, coordinateOpen (I := I) (K := K) i)=⊤ := by
  apply Proj.iSup_basicOpen_eq_top
  rw [HomogeneousIdeal.toIdeal_irrelevant_le]
  intro j hj p hp
  rw [← Set.image_univ]
  apply MvPolynomial.mem_ideal_span_X_image.mpr
  intro a ha
  have hd : a.degree=j := by
    simpa only [Finsupp.degree_eq_weight_one, Pi.one_def] using hp (MvPolynomial.mem_support_iff.mp ha)
  by_contra! hn
  have ha0 : a=0 := by
    ext i
    exact hn i (Set.mem_univ i)
  rw [ha0,map_zero] at hd
  omega

/-- Every nonempty finite intersection is an actual affine open. -/
theorem coordinate_intersections_affine (S : Finset I) (hS : S.Nonempty) :
    IsAffineOpen (S.inf (coordinateOpen (K := K))) := by
  rw [← chartIntersection_eq_inf]
  exact Proj.isAffineOpen_basicOpen _ _ (denominator_homogeneous S) hS.card_pos

section ProductGroups

universe u v
variable {J : Type v} (A : J → AddCommGrpCat.{max v u})

/-- The chosen categorical product of abelian groups is its full Cartesian product. -/
def groupProductIsoPi : (∏ᶜ A) ≅ AddCommGrpCat.of ((j : J) → A j) :=
  IsLimit.conePointUniqueUpToIso (limit.isLimit _)
    (AddCommGrpCat.HasLimit.productLimitCone A).isLimit

@[reassoc] theorem groupProductIsoPi_hom_eval (j : J) :
    (groupProductIsoPi A).hom ≫ AddCommGrpCat.ofHom (Pi.evalAddMonoidHom (fun j => A j) j)=
      Pi.π A j :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ (Discrete.mk j)

@[simp] theorem groupProductIsoPi_apply (x : ↑(∏ᶜ A)) (j : J) :
    (groupProductIsoPi A).hom x j=Pi.π A j x :=
  ConcreteCategory.congr_hom (groupProductIsoPi_hom_eval A j) x

end ProductGroups

/-- Evaluation of a finite sum in the actual category of abelian groups. -/
theorem ab_sum_apply {J : Type*} {A B : AddCommGrpCat} (s : Finset J)
    (f : J → (A ⟶ B)) (x : A) : (∑ j ∈ s, f j) x=∑ j ∈ s, f j x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | @insert j s hj ih =>
      rw [Finset.sum_insert hj,Finset.sum_insert hj]
      change f j x+(∑ k ∈ s, f k) x=f j x+∑ k ∈ s, f k x
      rw [ih]

theorem ab_zsmul_apply {A B : AddCommGrpCat} (n : ℤ) (f : A ⟶ B) (x : A) :
    (n • f) x=n • f x := rfl

/-- The actual categorical Čech complex of the twisting sheaf. -/
def twistingCech (t : ℤ) : CochainComplex AddCommGrpCat ℕ :=
  (cechComplexFunctor (coordinateOpen (I := I) (K := K))).obj
    (Proj.twistingSheaf 𝒜 t).presheaf

/-- Canonical transport from the chosen intersection product to the literal chart intersection. -/
def intersectionSectionEquiv (t : ℤ) {q : ℕ} (a : Fin q → I) :
    (Proj.twistingSheaf 𝒜 t).presheaf.obj (op (∏ᶜ fun j => coordinateOpen (a j))) ≃+
      Γ(Proj.twistingSheaf 𝒜 t,chartIntersection (tupleCoordinates a)) :=
  (((Proj.twistingSheaf 𝒜 t).presheaf.mapIso (eqToIso (coordinate_product_eq a)).op).symm).addCommGroupIsoToAddEquiv

/-- Every categorical Čech term is exactly the full actual section tuple group. -/
def cechTermEquiv (t : ℤ) (q : ℕ) :
    (twistingCech (I := I) (K := K) t).X q ≃+ SectionCochain (I := I) (K := K) t q :=
  (groupProductIsoPi (fun a : Fin (q+1) → I =>
    (Proj.twistingSheaf 𝒜 t).presheaf.obj (op (∏ᶜ fun j => coordinateOpen (a j))))).addCommGroupIsoToAddEquiv.trans (AddEquiv.piCongrRight (intersectionSectionEquiv t))

theorem cechTermEquiv_apply (t : ℤ) (q : ℕ)
    (x : (twistingCech (I := I) (K := K) t).X q) (a : Fin (q+1) → I) :
    cechTermEquiv t q x a =
      (Proj.twistingSheaf 𝒜 t).presheaf.map (eqToHom (coordinate_product_eq a).symm).op
        (Pi.π (fun b : Fin (q+1) → I =>
          (Proj.twistingSheaf 𝒜 t).presheaf.obj
            (op (∏ᶜ fun j => coordinateOpen (b j)))) a x) := by
  simp only [cechTermEquiv,AddEquiv.trans_apply,AddEquiv.piCongrRight_apply,
    groupProductIsoPi_apply,intersectionSectionEquiv]
  rfl

/-- Equality transport across intersections commutes with restriction; both maps are the
unique inclusion of the same actual open sets. -/
theorem intersection_transport_natural (t : ℤ) {V W U T : (Proj 𝒜).Opens}
    (hV : V=U) (hW : W=T) (f : W ⟶ V) (g : T ⟶ U) :
    (Proj.twistingSheaf 𝒜 t).presheaf.map f.op ≫
        (Proj.twistingSheaf 𝒜 t).presheaf.map (eqToHom hW.symm).op =
      (Proj.twistingSheaf 𝒜 t).presheaf.map (eqToHom hV.symm).op ≫
        (Proj.twistingSheaf 𝒜 t).presheaf.map g.op := by
  rw [← Functor.map_comp,← Functor.map_comp]
  congr 1 <;> exact Subsingleton.elim _ _

/-- The chosen categorical differential is the literal alternating restriction differential. -/
theorem cechTermEquiv_differential (t : ℤ) (q : ℕ)
    (x : (twistingCech (I := I) (K := K) t).X q) :
    cechTermEquiv t (q+1) ((twistingCech t).d q (q+1) x)=
      sectionDifferential t q (cechTermEquiv t q x) := by
  funext a
  let π₀ : (twistingCech (I := I) (K := K) t).X (q+1) ⟶
      (Proj.twistingSheaf 𝒜 t).presheaf.obj
        (op (∏ᶜ fun j => coordinateOpen (a j))) :=
    Pi.π (fun b : Fin (q+2) → I =>
      (Proj.twistingSheaf 𝒜 t).presheaf.obj
        (op (∏ᶜ fun j => coordinateOpen (b j)))) a
  let π : (j : Fin (q+2)) → (twistingCech (I := I) (K := K) t).X q ⟶
      (Proj.twistingSheaf 𝒜 t).presheaf.obj
        (op (∏ᶜ fun r => coordinateOpen ((a ∘ j.succAbove) r))) :=
    fun j => Pi.π (fun b : Fin (q+1) → I =>
      (Proj.twistingSheaf 𝒜 t).presheaf.obj
        (op (∏ᶜ fun r => coordinateOpen (b r)))) (a ∘ j.succAbove)
  let ρ : (j : Fin (q+2)) →
      (Proj.twistingSheaf 𝒜 t).presheaf.obj
        (op (∏ᶜ fun r => coordinateOpen ((a ∘ j.succAbove) r))) ⟶
      (Proj.twistingSheaf 𝒜 t).presheaf.obj
        (op (∏ᶜ fun r => coordinateOpen (a r))) :=
    fun j => (Proj.twistingSheaf 𝒜 t).presheaf.map
      (Pi.lift (fun r => Pi.π (fun s => coordinateOpen (a s)) (j.succAbove r))).op
  let τ : (Proj.twistingSheaf 𝒜 t).presheaf.obj
      (op (∏ᶜ fun r => coordinateOpen (a r))) ⟶
      (Proj.twistingSheaf 𝒜 t).presheaf.obj
        (op (chartIntersection (tupleCoordinates a))) :=
    (Proj.twistingSheaf 𝒜 t).presheaf.map
      (eqToHom (coordinate_product_eq a).symm).op
  have hd : π₀ ((twistingCech t).d q (q+1) x) =
      (∑ j : Fin (q+2), (-1 : ℤ) ^ (j : ℕ) • (π j ≫ ρ j)) x :=
    ConcreteCategory.congr_hom
      (cechComplexFunctor_obj_d_comp_π (coordinateOpen (I := I) (K := K))
        (Proj.twistingSheaf 𝒜 t).presheaf q a) x
  have hs : (∑ j : Fin (q+2), (-1 : ℤ) ^ (j : ℕ) • (π j ≫ ρ j)) x =
      ∑ j : Fin (q+2), (-1 : ℤ) ^ (j : ℕ) • ρ j (π j x) := by
    refine (ab_sum_apply Finset.univ
      (fun j : Fin (q+2) => (-1 : ℤ) ^ (j : ℕ) • (π j ≫ ρ j)) x).trans ?_
    apply Finset.sum_congr rfl
    intro j _
    rfl
  rw [cechTermEquiv_apply,sectionDifferential_apply]
  change τ (π₀ ((twistingCech t).d q (q+1) x)) = _
  calc
    τ (π₀ ((twistingCech t).d q (q+1) x)) =
        τ (∑ j : Fin (q+2), (-1 : ℤ) ^ (j : ℕ) • ρ j (π j x)) :=
      congrArg τ (hd.trans hs)
    _ = ∑ j : Fin (q+2), (-1 : ℤ) ^ (j : ℕ) • τ (ρ j (π j x)) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      exact map_zsmul (ConcreteCategory.hom τ) ((-1 : ℤ) ^ (j : ℕ)) (ρ j (π j x))
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      apply congrArg (fun z => (-1 : ℤ) ^ (j : ℕ) • z)
      have hn : τ (ρ j (π j x)) =
          (Proj.twistingSheaf 𝒜 t).presheaf.map
            (homOfLE (chartIntersection_antitone (tupleCoordinates_delete_subset a j))).op
            ((Proj.twistingSheaf 𝒜 t).presheaf.map
              (eqToHom (coordinate_product_eq (a ∘ j.succAbove)).symm).op (π j x)) :=
        ConcreteCategory.congr_hom
          (intersection_transport_natural t (coordinate_product_eq (a ∘ j.succAbove))
            (coordinate_product_eq a)
            (Pi.lift (fun r => Pi.π (fun s => coordinateOpen (a s)) (j.succAbove r)))
            (homOfLE (chartIntersection_antitone (tupleCoordinates_delete_subset a j))))
          (π j x)
      exact hn.trans (congrArg
        ((Proj.twistingSheaf 𝒜 t).presheaf.map
          (homOfLE (chartIntersection_antitone (tupleCoordinates_delete_subset a j))).op)
        (cechTermEquiv_apply t q x (a ∘ j.succAbove)).symm)

/-- Exactness of the actual categorical Čech complex in every intermediate degree. -/
theorem twistingCech_exact_below_dimension (t : ℤ) (q : ℕ) (hq : q+2<Fintype.card I) :
    (twistingCech (I := I) (K := K) t).ExactAt (q+1) := by
  apply (HomologicalComplex.exactAt_iff'
    (K := twistingCech (I := I) (K := K) t) (i := q) (j := q+1) (k := q+2)
    (by simp) (by simp)).2
  apply (ShortComplex.ab_exact_iff _).mpr
  intro x hx
  change (twistingCech t).d (q+1) (q+2) x = 0 at hx
  have hc : sectionDifferential t (q+1) (cechTermEquiv t (q+1) x)=0 := by
    erw [← cechTermEquiv_differential,hx,map_zero]
  obtain ⟨g,hg⟩ := section_exact_below_dimension t q hq _ hc
  refine ⟨(cechTermEquiv t q).symm g,?_⟩
  change (twistingCech t).d q (q+1) ((cechTermEquiv t q).symm g) = x
  apply (cechTermEquiv t (q+1)).injective
  simpa only [cechTermEquiv_differential,AddEquiv.apply_symm_apply] using hg

/-- Exactness of the actual categorical Čech complex in all positive degrees for `t≥-N`. -/
theorem twistingCech_exact_of_twist (t : ℤ) (ht : -(Fintype.card I : ℤ)<t) (q : ℕ) :
    (twistingCech (I := I) (K := K) t).ExactAt (q+1) := by
  apply (HomologicalComplex.exactAt_iff'
    (K := twistingCech (I := I) (K := K) t) (i := q) (j := q+1) (k := q+2)
    (by simp) (by simp)).2
  apply (ShortComplex.ab_exact_iff _).mpr
  intro x hx
  change (twistingCech t).d (q+1) (q+2) x = 0 at hx
  have hc : sectionDifferential t (q+1) (cechTermEquiv t (q+1) x)=0 := by
    erw [← cechTermEquiv_differential,hx,map_zero]
  obtain ⟨g,hg⟩ := section_exact_of_twist t ht q _ hc
  refine ⟨(cechTermEquiv t q).symm g,?_⟩
  change (twistingCech t).d q (q+1) ((cechTermEquiv t q).symm g) = x
  apply (cechTermEquiv t (q+1)).injective
  simpa only [cechTermEquiv_differential,AddEquiv.apply_symm_apply] using hg

/-- Actual line-bundle cohomology vanishes in every intermediate projective degree. -/
theorem twisting_cohomology_vanishes_below_dimension (t : ℤ) (q : ℕ)
    (hq : q+2<Fintype.card I) :
    Subsingleton (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology (Proj.twistingSheaf 𝒜 t) (q+1)) := by
  have he := AlgebraicGeometry.Scheme.Modules.homologyCechComplexIsoCohomology
    (coordinateOpen (I := I) (K := K)) coordinate_intersections_affine coordinate_cover
    (Proj.twistingSheaf 𝒜 t) (q+1)
  exact AddCommGrpCat.subsingleton_of_isZero
    (IsZero.of_iso (twistingCech_exact_below_dimension t q hq).isZero_homology he.symm)

/-- Actual positive line-bundle cohomology vanishes for all `t≥-N` on `P^N`. -/
theorem twisting_cohomology_vanishes_of_twist (t : ℤ) (ht : -(Fintype.card I : ℤ)<t)
    (q : ℕ) :
    Subsingleton (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology (Proj.twistingSheaf 𝒜 t) (q+1)) := by
  have he := AlgebraicGeometry.Scheme.Modules.homologyCechComplexIsoCohomology
    (coordinateOpen (I := I) (K := K)) coordinate_intersections_affine coordinate_cover
    (Proj.twistingSheaf 𝒜 t) (q+1)
  exact AddCommGrpCat.subsingleton_of_isZero
    (IsZero.of_iso (twistingCech_exact_of_twist t ht q).isZero_homology he.symm)

/-- Restriction of an actual global section to every coordinate chart tuple. -/
def globalSectionCochain (t : ℤ) (s : Γ(Proj.twistingSheaf 𝒜 t,⊤)) :
    SectionCochain (I := I) (K := K) t 0 :=
  fun _ => (Proj.twistingSheaf 𝒜 t).presheaf.map (homOfLE le_top).op s

theorem globalSectionCochain_cocycle (t : ℤ) (s : Γ(Proj.twistingSheaf 𝒜 t,⊤)) :
    sectionDifferential t 0 (globalSectionCochain t s)=0 := by
  funext a
  rw [sectionDifferential_apply,Fin.sum_univ_succ,Fin.sum_univ_succ]
  simp only [Fin.val_zero,pow_zero,one_zsmul,Fin.val_succ,pow_one,
    Fin.sum_univ_zero,add_zero,neg_one_zsmul,Nat.zero_add,Pi.zero_apply]
  rw [← sub_eq_add_neg]
  apply sub_eq_zero.mpr
  apply Proj.twistingSheaf.ext
  intro x
  rfl

/-- Actual global negative-twist sections vanish in every positive projective dimension. -/
theorem global_section_eq_zero_of_negative (hI : 1<Fintype.card I) (t : ℤ) (ht : t<0)
    (s : Γ(Proj.twistingSheaf 𝒜 t,⊤)) : s=0 := by
  have hz := section_global_cocycle_eq_zero hI t ht (globalSectionCochain t s)
    (globalSectionCochain_cocycle t s)
  apply Proj.twistingSheaf.ext
  intro x
  have hx : x.val ∈ (⨆ i, coordinateOpen (I := I) (K := K) i) := by rw [coordinate_cover]; trivial
  obtain ⟨i,hi⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  let a : Fin 1 → I := fun _ => i
  have ha : x.val ∈ chartIntersection (K := K) (tupleCoordinates a) := by
    change x.val ∈ (coordinateOpen (K := K) i : (Proj 𝒜).Opens) at hi
    simpa [tupleCoordinates,a,chartIntersection_eq_inf] using hi
  have hh := congrArg (fun f : SectionCochain (I := I) (K := K) t 0 =>
    (f a).val ⟨x.val,ha⟩) hz
  exact hh

/-- The degree-zero group of actual negative-twist sheaf cohomology vanishes as well. -/
theorem twisting_cohomology_zero_of_negative (hI : 1<Fintype.card I) (t : ℤ) (ht : t<0) :
    Subsingleton (TauCeti.AlgebraicGeometry.Scheme.Modules.Cohomology (Proj.twistingSheaf 𝒜 t) 0) := by
  let e := TauCeti.AlgebraicGeometry.Scheme.Modules.cohomologyZeroEquiv (Proj.twistingSheaf 𝒜 t)
  refine ⟨fun x y => e.injective ?_⟩
  rw [global_section_eq_zero_of_negative hI t ht (e x),
    global_section_eq_zero_of_negative hI t ht (e y)]

end PaperVerification.Segre.ProjectiveCech

end SegreProjectiveCech

end SegreProjectiveCohomology

end
end
end ProbeLayer391

/-! Future-only kernel audit for one exported mathematical stage.

Append to the stage being checked, with Lean.Util.CollectAxioms available through
both `public import Lean.Util.CollectAxioms` and `import all Lean.Util.CollectAxioms`
in that stage's header, as required by the reviewed FullFlattenedAudit.

Every new declaration in the checked kernel environment is included: public,
private, generated and vendored declarations receive the same direct-sorry and
transitive-axiom checks. This is evidence for this stage only. Later principal
theorems need not exist yet, and the final full principal audit remains required.

This preparation does not execute the audit, export a module or alter a proof.
-/

open Lean Elab Command in
set_option maxHeartbeats 0 in
run_cmd do
  let env ← getEnv
  unless env.header.trustLevel == 0 do
    throwError "The stage kernel audit requires kernel trust level zero"
  let names := (env.checked.get.constants.foldStage2
    (fun (names : Array Name) name _ => names.push name) #[]).qsort Name.quickLt
  unless names.size > 0 do throwError "The stage mathematical module is empty"
  -- Reject direct proof holes before computing transitive axiom closures.
  -- The complete successful audit below remains unchanged.
  for name in names do
    let some info := env.checked.get.find? name
      | throwError "Authored declaration is not kernel checked: {name}"
    if let .axiomInfo _ := info then throwError "Authored axiom: {name}"
    if info.type.hasSorry || ((info.value? (allowOpaque := true)).any (·.hasSorry)) then
      throwError "Authored declaration contains a sorry expression: {name}"
  let privateEnv := env.setExporting false
  let importedAxioms := exportedAxiomsExt.getState (asyncMode := .mainOnly) env
  -- Match Lean's ordinary export audit, sharing its traversal cache across names.
  let axiomRows := CollectAxioms.runM privateEnv do
    names.mapM fun name =>
      return (name, ← CollectAxioms.collectAndGet importedAxioms.find? name)
  let mut theoremCount : Nat := 0
  for (name, axioms) in axiomRows do
    let some info := env.checked.get.find? name
      | throwError "Authored declaration is not kernel checked: {name}"
    if let .axiomInfo _ := info then throwError "Authored axiom: {name}"
    if info.type.hasSorry || ((info.value? (allowOpaque := true)).any (·.hasSorry)) then
      throwError "Authored declaration contains a sorry expression: {name}"
    for ax in axioms do
      unless ax == ``propext || ax == ``Classical.choice || ax == ``Quot.sound do
        throwError "Unapproved transitive axiom in {name}: {ax}"
    if let .thmInfo _ := info then
      theoremCount := theoremCount + 1
  let report := Json.mkObj [
    ("main_module", toJson env.header.mainModule.toString),
    ("declaration_count", toJson names.size),
    ("theorem_count", toJson theoremCount),
    ("trust_level", toJson env.header.trustLevel.toNat),
    ("allowed_axioms", toJson #["propext", "Classical.choice", "Quot.sound"]),
    ("audit_scope", toJson "current_stage_new_declarations")]
  logInfo m!"SEGRE_STAGE_KERNEL_AUDIT_PASS {report.compress}"
