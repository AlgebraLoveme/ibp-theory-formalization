module
public import Formalization.Axioms
public import Formalization.Definition
public import Mathlib

public section

namespace Lemma_Bp1.Machinery

-- formalizer:machinery-begin
lemma row_bounds {n : ℕ} (a x e z : Fin n → ℝ)
    (hz : ∀ j, x j - e j ≤ z j ∧ z j ≤ x j + e j) :
    (∑ j, a j * x j) - (∑ j, |a j| * e j) ≤ ∑ j, a j * z j ∧
    (∑ j, a j * z j) ≤ (∑ j, a j * x j) + (∑ j, |a j| * e j) := by
  constructor
  · rw [← Finset.sum_sub_distrib]
    apply Finset.sum_le_sum
    intro j _
    rcases le_total 0 (a j) with h | h
    · rw [abs_of_nonneg h]; nlinarith [mul_nonneg h (sub_nonneg.mpr (hz j).1)]
    · rw [abs_of_nonpos h]; nlinarith [mul_nonpos_of_nonpos_of_nonneg h (sub_nonneg.mpr (hz j).2)]
  · rw [← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro j _
    rcases le_total 0 (a j) with h | h
    · rw [abs_of_nonneg h]; nlinarith [mul_nonneg h (sub_nonneg.mpr (hz j).2)]
    · rw [abs_of_nonpos h]; nlinarith [mul_nonpos_of_nonpos_of_nonneg h (sub_nonneg.mpr (hz j).1)]

lemma row_extrema {n : ℕ} (a x e : Fin n → ℝ) (he : ∀ j, 0 ≤ e j) :
    sInf ((fun z : Fin n → ℝ => ∑ j, a j * z j) '' {z | ∀ j, x j - e j ≤ z j ∧ z j ≤ x j + e j}) =
      (∑ j, a j * x j) - (∑ j, |a j| * e j) ∧
    sSup ((fun z : Fin n → ℝ => ∑ j, a j * z j) '' {z | ∀ j, x j - e j ≤ z j ∧ z j ≤ x j + e j}) =
      (∑ j, a j * x j) + (∑ j, |a j| * e j) := by
  classical
  have lower : (∑ j, a j * x j) - (∑ j, |a j| * e j) ∈
      (fun z : Fin n → ℝ => ∑ j, a j * z j) '' {z | ∀ j, x j - e j ≤ z j ∧ z j ≤ x j + e j} := by
    refine ⟨(fun j => if 0 ≤ a j then x j - e j else x j + e j), ?_, ?_⟩
    · intro j; dsimp only; split_ifs <;> constructor <;> linarith [he j]
    · rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro j _
      dsimp only
      split_ifs with h
      · rw [abs_of_nonneg h]; ring
      · rw [abs_of_neg (lt_of_not_ge h)]; ring
  have upper : (∑ j, a j * x j) + (∑ j, |a j| * e j) ∈
      (fun z : Fin n → ℝ => ∑ j, a j * z j) '' {z | ∀ j, x j - e j ≤ z j ∧ z j ≤ x j + e j} := by
    refine ⟨(fun j => if 0 ≤ a j then x j + e j else x j - e j), ?_, ?_⟩
    · intro j; dsimp only; split_ifs <;> constructor <;> linarith [he j]
    · rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro j _
      dsimp only
      split_ifs with h
      · rw [abs_of_nonneg h]; ring
      · rw [abs_of_neg (lt_of_not_ge h)]; ring
  constructor
  · apply IsLeast.csInf_eq
    refine ⟨lower, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact (row_bounds a x e z hz).1
  · apply IsGreatest.csSup_eq
    refine ⟨upper, ?_⟩
    rintro _ ⟨z, hz, rfl⟩
    exact (row_bounds a x e z hz).2

-- formalizer:machinery-end

end Lemma_Bp1.Machinery
