module
public import Formalization.Axioms
public import Formalization.Definition
public import Formalization.Result.Lemma_3p3
public import Formalization.Result.Lemma_Bp1
public import Mathlib

public section

namespace Theorem_3p4.Machinery

-- formalizer:machinery-begin
lemma sum_mul_path_pos {n : ℕ} (a : Fin n → ℝ) (k : Fin n)
    (hne : a k ≠ 0)
    (hs : (∀ t, 0 ≤ a t) ∨ (∀ t, a t ≤ 0)) :
    0 < (∑ t, a t) * a k := by
  rw [Finset.sum_mul]
  apply Finset.sum_pos'
  · intro t _
    rcases hs with h | h
    · exact mul_nonneg (h t) (h k)
    · exact mul_nonneg_of_nonpos_of_nonpos (h t) (h k)
  · exact ⟨k, Finset.mem_univ k, mul_self_pos.mpr hne⟩

lemma network_product (d : Fin 3 → ℕ)
    (W : ∀ k : Fin 2, Matrix (Fin (d k.succ)) (Fin (d k.castSucc)) ℝ) :
    let A : Matrix (Fin (d 1)) (Fin (d 0)) ℝ := W 0
    let B : Matrix (Fin (d 2)) (Fin (d 1)) ℝ := W 1
    linear_network.F(Definition.linear_network 2 d W) = B * A := by
  let A : Matrix (Fin (d 1)) (Fin (d 0)) ℝ := W 0
  let B : Matrix (Fin (d 2)) (Fin (d 1)) ℝ := W 1
  change B * (A * (1 : Matrix (Fin (d 0)) (Fin (d 0)) ℝ)) = _
  rw [Matrix.mul_one]

-- formalizer:machinery-end

end Theorem_3p4.Machinery
