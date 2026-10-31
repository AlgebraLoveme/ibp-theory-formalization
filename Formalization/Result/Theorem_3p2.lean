module
public import Formalization.Result.helpers.Theorem_3p2.Machinery
public import Formalization.Axioms
public import Formalization.Definition
public import Mathlib
public import Formalization.Result.Lemma_Bp1

open Definition

public section

open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Filter
namespace Theorem_3p2

theorem deep_linear_boxes (L : ℕ) (hL : 1 ≤ L) (d : Fin (L + 1) → ℕ)
    (hd : ∀ k, 0 < d k)
    (W : ∀ k : Fin L, Matrix (Fin (d k.succ)) (Fin (d k.castSucc)) ℝ)
    (x e : Fin (d ⟨0, Nat.zero_lt_succ L⟩) → ℝ) (he : ∀ j, 0 ≤ e j) :
    let N := linear_network L d W
    let p := N.2.2.2 x e
    (p.1.2 + p.1.1) / 2 = linear_network.F(N).mulVec x ∧
    (p.2.2 + p.2.1) / 2 = linear_network.F(N).mulVec x ∧
    (p.1.2 - p.1.1) / 2 = N.2.1.mulVec e ∧
    (p.2.2 - p.2.1) / 2 = N.2.2.1.mulVec e := (by
  -- formalizer:proof-begin
  classical
  let prod := Nat.rec
    (motive := fun k => (hk : k ≤ L) → Bool →
      Matrix (Fin (d ⟨k, by omega⟩)) (Fin (d ⟨0, Nat.zero_lt_succ L⟩)) ℝ)
    (fun _ _ => 1)
    (fun k ih hk a =>
      let w := W ⟨k, by omega⟩
      fun i j => ∑ t, (if a then |w i t| else w i t) * ih (by omega) a t j)
  let seq := Nat.rec
    (motive := fun k => (hk : k ≤ L) →
      (Fin (d ⟨0, Nat.zero_lt_succ L⟩) → ℝ) →
      (Fin (d ⟨0, Nat.zero_lt_succ L⟩) → ℝ) →
      (Fin (d ⟨k, by omega⟩) → ℝ) × (Fin (d ⟨k, by omega⟩) → ℝ))
    (fun _ x e => (x - e, x + e))
    (fun k ih hk x e =>
      let p := ih (by omega) x e
      (boxes (fun i => (p.2 i + p.1 i) / 2) (fun i => (p.2 i - p.1 i) / 2)
        (fun z => (W ⟨k, by omega⟩).mulVec z)).2.1)
  let F := prod L le_rfl false
  let Q := prod L le_rfl true
  -- Lemma B.1, (pf1-1): the composed linear map has endpoints Fx ± |F|e.
  -- Grouping the first m layers gives precisely the product used here.
  have optimal := Machinery.layer_endpoints F x e he
  -- Induct over prefixes, retaining nonnegative radii so that every next
  -- full box is in the domain of the single-layer calculation (pf1-1).
  have prefixes : ∀ k (hk : k ≤ L),
      seq k hk x e = ((prod k hk false).mulVec x - (prod k hk true).mulVec e,
        (prod k hk false).mulVec x + (prod k hk true).mulVec e) ∧
      (∀ i, 0 ≤ (prod k hk true).mulVec e i) := by
    intro k
    induction k with
    | zero =>
      intro hk
      simpa only [seq, prod, Nat.rec_zero, Matrix.one_mulVec] using
        (And.intro rfl he : (x - e, x + e) = (x - e, x + e) ∧ (∀ i, 0 ≤ e i))
    | succ k ih =>
      intro hk
      have prev := ih (Nat.le_of_succ_le hk)
      let A : Matrix (Fin (d ⟨k + 1, by omega⟩)) (Fin (d ⟨k, by omega⟩)) ℝ := W ⟨k, by omega⟩
      have step := Machinery.layer_endpoints
        A ((prod k (by omega) false).mulVec x) ((prod k (by omega) true).mulVec e) prev.2
      have pos := Machinery.absolute_mulVec_nonneg
        A ((prod k (by omega) true).mulVec e) prev.2
      -- The new center is W times the previous center; the radius is
      -- |W| times the previous radius, giving the ordered products.
      constructor
      · change (boxes (fun i => ((seq k (by omega) x e).2 i + (seq k (by omega) x e).1 i) / 2)
          (fun i => ((seq k (by omega) x e).2 i - (seq k (by omega) x e).1 i) / 2)
          (fun z => A.mulVec z)).2.1 = _
        rw [prev.1]
        simp only [Machinery.endpoint_center,
          Machinery.endpoint_radius]
        rw [step]
        change _ = ((A * prod k (by omega) false).mulVec x -
          (A.map abs * prod k (by omega) true).mulVec e,
          (A * prod k (by omega) false).mulVec x +
          (A.map abs * prod k (by omega) true).mulVec e)
        simp only [Matrix.mulVec_mulVec]
      · change ∀ i, 0 ≤ (A.map abs * prod k (by omega) true).mulVec e i
        simpa only [← Matrix.mulVec_mulVec] using pos
  have sequential := (prefixes L le_rfl).1
  change (boxes.hi(boxes x e (fun z => F.mulVec z)) +
      boxes.lo(boxes x e (fun z => F.mulVec z))) / 2 = F.mulVec x ∧
    ((seq L le_rfl x e).2 + (seq L le_rfl x e).1) / 2 = F.mulVec x ∧
    (boxes.hi(boxes x e (fun z => F.mulVec z)) -
      boxes.lo(boxes x e (fun z => F.mulVec z))) / 2 = (F.map abs).mulVec e ∧
    ((seq L le_rfl x e).2 - (seq L le_rfl x e).1) / 2 = Q.mulVec e
  rw [optimal, sequential]
  -- Half-sums and half-differences recover the common center and the two
  -- radii of Theorem 3.2, including coordinates with zero radius.
  refine ⟨?_, ?_, ?_, ?_⟩ <;> funext i <;>
    simp only [Pi.div_apply, Pi.add_apply, Pi.sub_apply, Pi.ofNat_apply] <;> ring
  -- formalizer:proof-end
)
end Theorem_3p2
