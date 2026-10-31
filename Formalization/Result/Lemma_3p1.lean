module
public import Formalization.Result.helpers.Lemma_3p1.Machinery
public import Formalization.Axioms
public import Formalization.Definition
public import Mathlib

open Definition

public section

open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Filter
namespace Lemma_3p1

theorem exact_certification {n c : ℕ} (hn : 0 < n)
    (y : (Fin n → ℝ) → Fin c → ℝ) (hy : Continuous y)
    (t : Fin c) (x e : Fin n → ℝ) (he : ∀ j, 0 ≤ e j) :
    let D := robust_classification y t x e
    let B := boxes.B(boxes x e y)
    let lo := fun i : {i : Fin c // i ≠ t} => sInf ((fun z => D.1 z i) '' B)
    let hi := fun i : {i : Fin c // i ≠ t} => sSup ((fun z => D.1 z i) '' B)
    (D.2.1 ↔ {v | ∀ i, lo i ≤ v i ∧ v i ≤ hi i} ⊆ D.2.2) ∧
    (D.2.1 ↔ ∀ i, hi i < 0) := (by
  -- formalizer:proof-begin
  classical
  dsimp only
  let B := boxes.B(boxes x e y)
  let f := (robust_classification y t x e).1
  let hi := fun i => sSup ((fun z => f z i) '' B)
  let lo := fun i => sInf ((fun z => f z i) '' B)
  -- The full closed box contains its center and is compact, even for zero radii.
  have hx : x ∈ B := by
    change ∀ j, x j - e j ≤ x j ∧ x j ≤ x j + e j
    intro j
    constructor <;> linarith [he j]
  have hB : IsCompact B := by
    have hEq : B = Set.Icc (x - e) (x + e) := by
      ext z
      exact forall_and
    rw [hEq]
    exact isCompact_Icc
  have hf (i : {i : Fin c // i ≠ t}) : Continuous (fun z => f z i) :=
    (continuous_apply i.val |>.comp hy).sub (continuous_apply t |>.comp hy)
  have hK i := hB.image (hf i)
  have hne i : ((fun z => f z i) '' B).Nonempty := ⟨f x i, x, hx, rfl⟩
  -- Appendix proof of Lemma 3.1: each continuous difference attains its upper endpoint.
  have hmax i : ∃ z ∈ B, f z i = hi i :=
    (hK i).isClosed.csSup_mem (hne i) (hK i).bddAbove
  have hupper i {z} (hz : z ∈ B) : f z i ≤ hi i :=
    le_csSup (hK i).bddAbove ⟨z, hz, rfl⟩
  have hend i : lo i ≤ hi i :=
    csInf_le_csSup (hne i) (hK i).bddBelow (hK i).bddAbove
  -- Unique winning at a maximizing input makes each upper difference bound negative;
  -- conversely every difference lies below that negative upper bound.
  have hrob : (robust_classification y t x e).2.1 ↔ ∀ i, hi i < 0 := by
    constructor
    · intro h i
      obtain ⟨z, hz, hzi⟩ := hmax i
      rw [← hzi]
      exact sub_neg.mpr (h z hz i.val i.property)
    · intro h z hz i hit
      have hlt := lt_of_le_of_lt (hupper ⟨i, hit⟩ hz) (h ⟨i, hit⟩)
      exact sub_neg.mp hlt
  -- The upper-endpoint vector belongs to the optimal box. Thus containment in
  -- the negative orthant is equivalent to negativity of all upper endpoints.
  have hbox : ({v | ∀ i, lo i ≤ v i ∧ v i ≤ hi i} ⊆
      (robust_classification y t x e).2.2) ↔ ∀ i, hi i < 0 := by
    constructor
    · intro h
      exact h (fun i => ⟨hend i, le_rfl⟩)
    · intro h v hv i
      exact lt_of_le_of_lt (hv i).2 (h i)
  exact ⟨hrob.trans hbox.symm, hrob⟩
  -- formalizer:proof-end
)
end Lemma_3p1
