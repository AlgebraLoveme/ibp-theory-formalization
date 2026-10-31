module
public import Formalization.Axioms
public import Formalization.Definition
public import Formalization.Result.Theorem_3p4
public import Formalization.Result.Lemma_3p3
public import Formalization.Result.Lemma_Bp1
public import Mathlib

public section

namespace Corollary_Ap1.Machinery

-- formalizer:machinery-begin
lemma fourth_sign (a b c d : ℝ) (hp : 0 < a * b * c * d) :
    SignType.sign d = SignType.sign a * SignType.sign b * SignType.sign c := by
  have hs := sign_pos hp
  simp only [sign_mul] at hs
  cases ha : SignType.sign a <;> cases hb : SignType.sign b <;>
    cases hc : SignType.sign c <;> cases hd : SignType.sign d <;>
    simp_all

-- formalizer:machinery-end

end Corollary_Ap1.Machinery
