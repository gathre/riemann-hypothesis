module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.IsLocalHom
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import ReciprocityTheory.CommutativeAlgebra.SaturatedChains.IsSaturatedChain
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.ClMvps
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.CmOfRegular
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Coalgebra.IsFrobenius
import Mathlib.RingTheory.HopfAlgebra.Basic
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init
public import ReciprocityTheory.CommutativeAlgebra.PolynomialHeights.PolyCM

@[expose] public section

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.CA ReciprocityTheory.CA

theorem UpperTheory.V.CA.cl_cmquot :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] (R : Type) [CommRing R] [Algebra O R] [IsLocalRing R], IsCL O R → IsCMQuot R := by
  intro O _ _ _ _ R _ _ _ hR
  haveI := hR.noeth
  obtain ⟨n, a, ha⟩ :=
    Submodule.fg_iff_exists_fin_generating_family.mp (IsNoetherian.noetherian (maximalIdeal R))
  have hspan : Ideal.span (Set.range a) = maximalIdeal R := ha
  have hmem : ∀ s, a s ∈ maximalIdeal R := by
    intro s
    rw [← hspan]
    exact Ideal.subset_span ⟨s, rfl⟩
  have hrad : maximalIdeal R ≤
      (Ideal.span (Set.range a) ⊔ Ideal.map (algebraMap O R) (maximalIdeal O)).radical := by
    rw [hspan]
    exact le_sup_left.trans Ideal.le_radical
  obtain ⟨φ, -, hfin, hloc⟩ := cl_mvps O R hR (Fin n) a hmem hrad
  haveI := hloc
  exact cmquot_of_finite (cl_cm.1 O n).1 φ hfin
