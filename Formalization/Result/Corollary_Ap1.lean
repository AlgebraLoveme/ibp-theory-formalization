module
public import Formalization.Result.helpers.Corollary_Ap1.Machinery
public import Formalization.Axioms
public import Formalization.Definition
public import Mathlib
public import Formalization.Result.Theorem_3p4

open Definition

public section

open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Filter
namespace Corollary_Ap1

theorem sign_determination (n h h' : ℕ) (hn : 0 < n) (hh : 0 < h) (hh' : 0 < h')
    (W : ∀ k : Fin 2, Matrix (Fin (![n,h,n] k.succ)) (Fin (![n,h,n] k.castSucc)) ℝ)
    (V : ∀ k : Fin 2, Matrix (Fin (![n,h',n] k.succ)) (Fin (![n,h',n] k.castSucc)) ℝ)
    (hW : propagation_invariance 2 ![n,h,n] W)
    (hV : propagation_invariance 2 ![n,h',n] V)
    (hnW : ∀ k i j, W k i j ≠ 0) (hnV : ∀ k i j, V k i j ≠ 0)
    (hFW : ∀ i j, linear_network.F(linear_network 2 ![n,h,n] W) i j ≠ 0)
    (hFV : ∀ i j, linear_network.F(linear_network 2 ![n,h',n] V) i j ≠ 0)
    (r s : Fin n)
    (hrow : ∀ j, SignType.sign (linear_network.F(linear_network 2 ![n,h,n] W) r j) =
      SignType.sign (linear_network.F(linear_network 2 ![n,h',n] V) r j))
    (hcol : ∀ i, SignType.sign (linear_network.F(linear_network 2 ![n,h,n] W) i s) =
      SignType.sign (linear_network.F(linear_network 2 ![n,h',n] V) i s)) :
    ∀ i j, SignType.sign (linear_network.F(linear_network 2 ![n,h,n] W) i j) =
      SignType.sign (linear_network.F(linear_network 2 ![n,h',n] V) i j) := (by
  -- formalizer:proof-begin
  have hdW : ∀ k : Fin 3, 0 < (![n,h,n] k) := by
    intro k
    fin_cases k <;> assumption
  have hdV : ∀ k : Fin 3, 0 < (![n,h',n] k) := by
    intro k
    fin_cases k <;> assumption
  intro i j
  -- Corollary A.1: the chosen row and column supply three known corners.
  -- Apply the paper's fourth-corner construction to rows r,i and columns s,j;
  -- using these anchored blocks performs the construction for every entry.
  have pW : 0 < linear_network.F(linear_network 2 ![n,h,n] W) r s *
      linear_network.F(linear_network 2 ![n,h,n] W) r j *
      linear_network.F(linear_network 2 ![n,h,n] W) i s *
      linear_network.F(linear_network 2 ![n,h,n] W) i j := by
    -- Theorem 3.4 excludes a negative rectangle; nonzero entries exclude zero.
    apply lt_of_le_of_ne
    · exact le_of_not_gt (fun hneg =>
        Theorem_3p4.non_pi_sign_rectangle ![n,h,n] hdW W r i s j
          (fun k => ⟨hnW 0 k s, hnW 0 k j, hnW 1 r k, hnW 1 i k⟩) hneg hW)
    · exact Ne.symm (mul_ne_zero
        (mul_ne_zero (mul_ne_zero (hFW r s) (hFW r j)) (hFW i s)) (hFW i j))
  have pV : 0 < linear_network.F(linear_network 2 ![n,h',n] V) r s *
      linear_network.F(linear_network 2 ![n,h',n] V) r j *
      linear_network.F(linear_network 2 ![n,h',n] V) i s *
      linear_network.F(linear_network 2 ![n,h',n] V) i j := by
    apply lt_of_le_of_ne
    · exact le_of_not_gt (fun hneg =>
        Theorem_3p4.non_pi_sign_rectangle ![n,h',n] hdV V r i s j
          (fun k => ⟨hnV 0 k s, hnV 0 k j, hnV 1 r k, hnV 1 i k⟩) hneg hV)
    · exact Ne.symm (mul_ne_zero
        (mul_ne_zero (mul_ne_zero (hFV r s) (hFV r j)) (hFV i s)) (hFV i j))
  -- A positive four-corner product fixes the fourth sign: it is positive
  -- exactly when an odd number of the three known signs are positive.
  -- The same rule in both arrays completes all rows and columns (also n=1).
  rw [Machinery.fourth_sign _ _ _ _ pW,
      Machinery.fourth_sign _ _ _ _ pV,
      hrow s, hrow j, hcol i]
  -- formalizer:proof-end
)
end Corollary_Ap1
