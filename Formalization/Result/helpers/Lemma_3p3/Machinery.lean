module
public import Formalization.Axioms
public import Formalization.Definition
public import Formalization.Result.Lemma_Bp1
public import Mathlib

public section

namespace Lemma_3p3.Machinery

-- formalizer:machinery-begin
lemma endpoints_eq {n : ℕ} (a b : (Fin n → ℝ) × (Fin n → ℝ))
    (hc : (a.2 + a.1) / 2 = (b.2 + b.1) / 2)
    (hr : (a.2 - a.1) / 2 = (b.2 - b.1) / 2) : a = b := by
  apply Prod.ext <;> funext i
  all_goals
    have hci := congrFun hc i
    have hri := congrFun hr i
    simp only [Pi.div_apply, Pi.add_apply, Pi.sub_apply, Pi.ofNat_apply] at hci hri
    linarith

lemma network_coefficients (d : Fin 3 → ℕ)
    (W : ∀ k : Fin 2, Matrix (Fin (d k.succ)) (Fin (d k.castSucc)) ℝ) :
    let A : Matrix (Fin (d 1)) (Fin (d 0)) ℝ := W 0
    let B : Matrix (Fin (d 2)) (Fin (d 1)) ℝ := W 1
    (Definition.linear_network 2 d W).2.1 = (B * A).map abs ∧
    (Definition.linear_network 2 d W).2.2.1 = B.map abs * A.map abs := by
  let A : Matrix (Fin (d 1)) (Fin (d 0)) ℝ := W 0
  let B : Matrix (Fin (d 2)) (Fin (d 1)) ℝ := W 1
  change (B * (A * (1 : Matrix (Fin (d 0)) (Fin (d 0)) ℝ))).map abs = _ ∧
    B.map abs * (A.map abs * (1 : Matrix (Fin (d 0)) (Fin (d 0)) ℝ)) = _
  simp only [Matrix.mul_one]
  exact ⟨rfl, rfl⟩

lemma signed_sum_decomposition {n : ℕ} (a : Fin n → ℝ) :
    (∑ k, a k) = (∑ k, max (a k) 0) - (∑ k, max (-a k) 0) ∧
    (∑ k, |a k|) = (∑ k, max (a k) 0) + (∑ k, max (-a k) 0) := by
  constructor
  · rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rcases le_total 0 (a k) with h | h <;>
      simp [h, neg_nonpos.mpr, neg_nonneg.mpr]
  · rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    rcases le_total 0 (a k) with h | h
    · rw [abs_of_nonneg h, max_eq_left h, max_eq_right (neg_nonpos.mpr h), add_zero]
    · rw [abs_of_nonpos h, max_eq_right h, max_eq_left (neg_nonneg.mpr h), zero_add]

lemma nonpos_of_positive_sum_zero {n : ℕ} (a : Fin n → ℝ)
    (h : (∑ k, max (a k) 0) = 0) : ∀ k, a k ≤ 0 := by
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun k (_ : k ∈ Finset.univ) =>
    le_max_right (a k) 0)).mp h
  intro k
  have hk := hz k (Finset.mem_univ k)
  exact (le_max_left (a k) 0).trans (le_of_eq hk)

-- formalizer:machinery-end

end Lemma_3p3.Machinery
