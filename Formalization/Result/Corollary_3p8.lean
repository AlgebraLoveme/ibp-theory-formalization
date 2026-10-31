module
public import Formalization.Result.helpers.Corollary_3p8.Machinery
public import Formalization.Axioms
public import Formalization.Definition
public import Mathlib
public import Formalization.Result.Theorem_3p2
public import Formalization.Result.Lemma_Bp2
public import Formalization.Result.Lemma_3p7

open Definition

public section

open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Filter
namespace Corollary_3p8

theorem initialization_depth {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (L : ℕ) (hL : 2 ≤ L) (d : Fin (L + 1) → ℕ)
    (σ : Fin L → ℝ≥0)
    (W : Ω → ∀ k : Fin L, Matrix (Fin (d k.succ)) (Fin (d k.castSucc)) ℝ)
    (hinit : (gaussian_initialization μ L d σ W (fun _ => 0)).1)
    (x e : Fin (d ⟨0, Nat.zero_lt_succ L⟩) → ℝ)
    (he : ∀ j, 0 ≤ e j) (hne : e ≠ 0) :
    let dmin := sInf {r : ℕ | ∃ k : Fin (L + 1), 0 < k.val ∧ k.val < L ∧ d k = r}
    let t := fun n : ℕ => Real.sqrt Real.pi * Real.Gamma (((n : ℝ) + 1) / 2) /
      ((n : ℝ) * Real.Gamma ((n : ℝ) / 2))
    let p := fun ω => (linear_network L d (W ω)).2.2.2 x e
    let r := fun ω i => ((p ω).1.2 i - (p ω).1.1 i) / 2
    let s := fun ω i => ((p ω).2.2 i - (p ω).2.1 i) / 2
    (∀ i, 0 < ∫ ω, s ω i ∂μ) ∧
    (∀ i, (∫ ω, r ω i ∂μ) / (∫ ω, s ω i ∂μ) ≤ t dmin ^ (L / 2)) := (by
  -- formalizer:proof-begin
  classical
  -- For L = 2 there is one pair; Lemma 3.7 gives the exact ratio.
  by_cases htwo : L = 2
  · subst L
    have hw := Lemma_3p7.initialization_width μ d σ W hinit x e he hne
    have hmin : sInf {r : ℕ | ∃ k : Fin (2 + 1),
        0 < k.val ∧ k.val < 2 ∧ d k = r} = d 1 := by
      have hset : {r : ℕ | ∃ k : Fin (2 + 1),
          0 < k.val ∧ k.val < 2 ∧ d k = r} = {d 1} := by
        ext r
        constructor
        · rintro ⟨k, hk, hk', rfl⟩
          have heq : k = 1 := Fin.ext (by change k.val = 1; omega)
          simp [heq]
        · intro hr
          exact ⟨1, by norm_num, by norm_num, by simpa using hr.symm⟩
      rw [hset, csInf_singleton]
    dsimp only at hw ⊢
    rw [hmin]
    exact ⟨hw.1, fun i => by simpa using le_of_eq (hw.2.1 i)⟩
  let t := fun n : ℕ => Real.sqrt Real.pi * Real.Gamma (((n : ℝ) + 1) / 2) /
    ((n : ℝ) * Real.Gamma ((n : ℝ) / 2))
  let dmin := sInf {r : ℕ | ∃ k : Fin (L + 1), 0 < k.val ∧ k.val < L ∧ d k = r}
  let factor := ∏ j : Fin (L / 2), t (d ⟨2 * j.val + 1, by omega⟩)
  let O := fun ω => (linear_network L d (W ω)).2.1
  let Q := fun ω => (linear_network L d (W ω)).2.2.1
  have hd := hinit.2.2.1
  -- Theorem 3.2 identifies the two geometric radii with |F|e and Qe.
  have hr (ω : Ω) (i : Fin (d (Fin.last L))) :
      (((linear_network L d (W ω)).2.2.2 x e).1.2 i -
        ((linear_network L d (W ω)).2.2.2 x e).1.1 i) / 2 = (O ω).mulVec e i := by
    exact congrFun (Theorem_3p2.deep_linear_boxes L (by omega) d hd (W ω) x e he).2.2.1 i
  have hs (ω : Ω) (i : Fin (d (Fin.last L))) :
      (((linear_network L d (W ω)).2.2.2 x e).2.2 i -
        ((linear_network L d (W ω)).2.2.2 x e).2.1 i) / 2 = (Q ω).mulVec e i := by
    exact congrFun (Theorem_3p2.deep_linear_boxes L (by omega) d hd (W ω) x e he).2.2.2 i
  -- Independent Gaussian absolute moments are positive and integrable.
  -- Induction over prefixes factors the next weight from the earlier
  -- product; every intermediate width is positive.
  have hQ : ∀ i j, Integrable (fun ω => Q ω i j) μ ∧
      0 < ∫ ω, Q ω i j ∂μ :=
    Machinery.gaussian_sequential_coefficients
      μ L d σ W hinit
  have hO : ∀ i j, Integrable (fun ω => O ω i j) μ ∧
      (∫ ω, O ω i j ∂μ) ≤ factor * ∫ ω, Q ω i j ∂μ := by
    intro i j
    refine ⟨Machinery.optimal_coefficient_integrable
      μ L d σ W hinit i j, ?_⟩
    letI := hinit.1
    let I := Σ k : Fin L, Fin (d k.succ) × Fin (d k.castSucc)
    let Z : I → Ω → ℝ := fun p ω => W ω p.1 p.2.1 p.2.2
    let P := fun z : I → ℝ => Nat.rec
      (motive := fun k => (hk : k ≤ L) → Bool →
        Matrix (Fin (d ⟨k, by omega⟩)) (Fin (d ⟨0, Nat.zero_lt_succ L⟩)) ℝ)
      (fun _ _ => 1)
      (fun k ih hk a => fun i j => ∑ t,
        (if a then |z ⟨⟨k, by omega⟩, i, t⟩| else z ⟨⟨k, by omega⟩, i, t⟩) * ih (by omega) a t j)
    have hreg := Machinery.prefix_regularity
      μ L d σ W hinit
    change (∀ k hk a i j, Measurable (fun z => P z k hk a i j)) ∧ _ at hreg
    -- Disjoint layer coordinates make each new block independent of the
    -- preceding product, including after taking entrywise absolute values.
    have hsep (k : ℕ) (hk : k ≤ L) (f : (I → ℝ) → ℝ) (hf : Measurable f)
        (hloc : ∀ z z', (∀ p, k ≤ p.1.val → z p = z' p) → f z = f z')
        (a : Bool) (r : Fin (d ⟨k, by omega⟩)) (s : Fin (d ⟨0, by omega⟩))
        (g : ℝ → ℝ) (hg : Measurable g) :
        IndepFun (fun ω => f (fun p => Z p ω))
          (fun ω => g (P (fun p => Z p ω) k hk a r s)) μ := by
      refine Machinery.independent_coordinate_functions
        μ Z (fun p => (hinit.2.2.2.2.2 p).aemeasurable) hinit.2.2.2.2.1
        (Finset.univ.filter (fun p => k ≤ p.1.val))
        (Finset.univ.filter (fun p => p.1.val < k)) ?_
        f (fun z => g (P z k hk a r s)) hf (hg.comp (hreg.1 k hk a r s)) ?_ ?_
      · apply Finset.disjoint_left.2
        intro p hp hq
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
        omega
      · intro z z' heq
        exact hloc z z' (fun p hp => heq p (by simp [hp]))
      · intro z z' heq
        exact congrArg g (hreg.2.1 k hk a r s z z' (fun p hp => heq p (by simp [hp])))
    -- Appending one independent absolute matrix preserves a coefficient
    -- bound. This is the unpaired leftmost layer for odd L.
    have hone (k : ℕ) (hk : k + 1 ≤ L) (u : ℝ)
        (hu : ∀ (r : Fin (d ⟨k, by omega⟩)) (s : Fin (d ⟨0, by omega⟩)), (∫ ω, |P (fun p => Z p ω) k (by omega) false r s| ∂μ) ≤
          u * ∫ ω, P (fun p => Z p ω) k (by omega) true r s ∂μ) :
        ∀ (r : Fin (d ⟨k + 1, by omega⟩)) (s : Fin (d ⟨0, by omega⟩)),
          (∫ ω, |P (fun p => Z p ω) (k + 1) hk false r s| ∂μ) ≤
          u * ∫ ω, P (fun p => Z p ω) (k + 1) hk true r s ∂μ := by
      let A : Ω → Matrix (Fin (d ⟨k + 1, by omega⟩)) (Fin (d ⟨k, by omega⟩)) ℝ :=
        fun ω => W ω ⟨k, by omega⟩
      have hA (r : Fin (d ⟨k + 1, by omega⟩)) (s : Fin (d ⟨k, by omega⟩)) := Lemma_3p7.Machinery.gaussian_abs_moment
        μ (fun ω => A ω r s) (σ ⟨k, by omega⟩) (hinit.2.2.2.1 _) (hinit.2.2.2.2.2 ⟨⟨k, by omega⟩, r, s⟩)
      have hind (r : Fin (d ⟨k + 1, by omega⟩)) (t : Fin (d ⟨k, by omega⟩))
          (s : Fin (d ⟨0, by omega⟩)) (a : Bool) (g : ℝ → ℝ) (hg : Measurable g) :
          IndepFun (fun ω => |A ω r t|)
            (fun ω => g (P (fun p => Z p ω) k (by omega) a t s)) μ := by
        refine hsep k (by omega) (fun z => |z ⟨⟨k, by omega⟩, r, t⟩|)
          (by fun_prop) ?_ a t s g hg
        intro z z' heq
        exact congrArg abs (heq _ (by simp))
      have hb := Machinery.block_expectation_bound
        μ (fun ω => (A ω).map abs) (fun ω => (A ω).map abs)
        (fun ω => P (fun p => Z p ω) k (by omega) false)
        (fun ω => P (fun p => Z p ω) k (by omega) true)
        (fun ω => (P (fun p => Z p ω) (k + 1) hk false).map abs)
        (fun r t => (hA r t).1) (fun r t => (hA r t).1)
        (fun r s => (hreg.2.2 k (by omega) false r s).abs)
        (hreg.2.2 k (by omega) true)
        (fun r s => (hreg.2.2 (k + 1) hk false r s).abs)
        (fun r t s => hind r t s false abs measurable_abs)
        (fun r t s => hind r t s true id measurable_id)
        (fun ω r t => abs_nonneg _) ?_ u 1 (fun r t => by simp) hu
      · simpa only [one_mul] using hb
      · intro ω r s
        exact Machinery.absolute_matrix_product_bound
          (A ω) (P (fun p => Z p ω) k (by omega) false) r s
    -- For two layers, C = |BA| and D = |B||A|. Lemma 3.7 gives
    -- E C = t(d_(k+1)) E D; the triangle inequality and independence
    -- multiply the earlier bound by this scalar (appendix lines 350–360).
    have htwoStep (k : ℕ) (hk : k + 2 ≤ L) (u : ℝ)
        (hu : ∀ (r : Fin (d ⟨k, by omega⟩)) (s : Fin (d ⟨0, by omega⟩)), (∫ ω, |P (fun p => Z p ω) k (by omega) false r s| ∂μ) ≤
          u * ∫ ω, P (fun p => Z p ω) k (by omega) true r s ∂μ) :
        ∀ (r : Fin (d ⟨k + 2, by omega⟩)) (s : Fin (d ⟨0, by omega⟩)),
          (∫ ω, |P (fun p => Z p ω) (k + 2) hk false r s| ∂μ) ≤
          (t (d ⟨k + 1, by omega⟩) * u) *
            ∫ ω, P (fun p => Z p ω) (k + 2) hk true r s ∂μ := by
      let A : Ω → Matrix (Fin (d ⟨k + 1, by omega⟩)) (Fin (d ⟨k, by omega⟩)) ℝ :=
        fun ω => W ω ⟨k, by omega⟩
      let B : Ω → Matrix (Fin (d ⟨k + 2, by omega⟩)) (Fin (d ⟨k + 1, by omega⟩)) ℝ :=
        fun ω => W ω ⟨k + 1, by omega⟩
      let C := fun ω => (B ω * A ω).map abs
      let D := fun ω => (B ω).map abs * (A ω).map abs
      have hpair (r : Fin (d ⟨k + 2, by omega⟩)) (s : Fin (d ⟨k, by omega⟩)) := Machinery.consecutive_pair_moments
        μ L d σ W hinit k hk r s
      have hc (r : Fin (d ⟨k + 2, by omega⟩)) (v : Fin (d ⟨k, by omega⟩))
          (s : Fin (d ⟨0, by omega⟩)) :
          IndepFun (fun ω => C ω r v)
            (fun ω => |P (fun p => Z p ω) k (by omega) false v s|) μ := by
        refine hsep k (by omega)
          (fun z => |∑ a, z ⟨⟨k + 1, by omega⟩, r, a⟩ * z ⟨⟨k, by omega⟩, a, v⟩|)
          (by apply Measurable.abs; apply Finset.measurable_sum; intro a _; fun_prop) ?_ false v s abs measurable_abs
        intro z z' heq
        apply congrArg abs
        apply Finset.sum_congr rfl
        intro a _
        rw [heq ⟨⟨k + 1, by omega⟩, r, a⟩ (by simp), heq ⟨⟨k, by omega⟩, a, v⟩ (by simp)]
      have hdq (r : Fin (d ⟨k + 2, by omega⟩)) (v : Fin (d ⟨k, by omega⟩))
          (s : Fin (d ⟨0, by omega⟩)) :
          IndepFun (fun ω => D ω r v)
            (fun ω => P (fun p => Z p ω) k (by omega) true v s) μ := by
        refine hsep k (by omega)
          (fun z => ∑ a, |z ⟨⟨k + 1, by omega⟩, r, a⟩| * |z ⟨⟨k, by omega⟩, a, v⟩|)
          (by apply Finset.measurable_sum; intro a _; fun_prop) ?_ true v s id measurable_id
        intro z z' heq
        apply Finset.sum_congr rfl
        intro a _
        rw [heq ⟨⟨k + 1, by omega⟩, r, a⟩ (by simp), heq ⟨⟨k, by omega⟩, a, v⟩ (by simp)]
      have hbound (ω : Ω) (r : Fin (d ⟨k + 2, by omega⟩)) (s : Fin (d ⟨0, by omega⟩)) : |P (fun p => Z p ω) (k + 2) hk false r s| ≤
          (C ω * (P (fun p => Z p ω) k (by omega) false).map abs) r s := by
        change |(B ω * (A ω * P (fun p => Z p ω) k (by omega) false)) r s| ≤ _
        rw [← Matrix.mul_assoc]
        exact Machinery.absolute_matrix_product_bound
          (B ω * A ω) (P (fun p => Z p ω) k (by omega) false) r s
      have hnext ω : D ω * P (fun p => Z p ω) k (by omega) true =
          P (fun p => Z p ω) (k + 2) hk true := by
        change ((B ω).map abs * (A ω).map abs) * P (fun p => Z p ω) k (by omega) true =
          (B ω).map abs * ((A ω).map abs * P (fun p => Z p ω) k (by omega) true)
        exact Matrix.mul_assoc _ _ _
      have hb := Machinery.block_expectation_bound
        μ C D (fun ω => P (fun p => Z p ω) k (by omega) false)
        (fun ω => P (fun p => Z p ω) k (by omega) true)
        (fun ω => (P (fun p => Z p ω) (k + 2) hk false).map abs)
        (fun r v => (hpair r v).1) (fun r v => (hpair r v).2.1)
        (fun r s => (hreg.2.2 k (by omega) false r s).abs)
        (hreg.2.2 k (by omega) true)
        (fun r s => (hreg.2.2 (k + 2) hk false r s).abs)
        hc hdq (fun ω r v => abs_nonneg _) hbound u (t (d ⟨k + 1, by omega⟩))
        (fun r v => (hpair r v).2.2.2) hu
      simpa only [hnext] using hb
    -- Iterating the two-layer step gives the product of pair factors.
    have heven : ∀ m (hm : 2 * m ≤ L) (r : Fin (d ⟨2 * m, by omega⟩))
        (s : Fin (d ⟨0, by omega⟩)),
        (∫ ω, |P (fun p => Z p ω) (2 * m) hm false r s| ∂μ) ≤
          (∏ a : Fin m, t (d ⟨2 * a.val + 1, by omega⟩)) *
            ∫ ω, P (fun p => Z p ω) (2 * m) hm true r s ∂μ := by
      intro m
      induction m with
      | zero =>
        intro hm r s
        simp only [Fin.prod_univ_zero, one_mul]
        apply le_of_eq
        apply integral_congr_ae
        apply Filter.Eventually.of_forall
        intro ω
        change |(1 : Matrix (Fin (d ⟨0, by omega⟩)) (Fin (d ⟨0, by omega⟩)) ℝ) r s| =
          (1 : Matrix (Fin (d ⟨0, by omega⟩)) (Fin (d ⟨0, by omega⟩)) ℝ) r s
        rw [Matrix.one_apply]
        split_ifs <;> norm_num
      | succ m ih =>
        intro hm
        have h := htwoStep (2 * m) (by omega)
          (∏ a : Fin m, t (d ⟨2 * a.val + 1, by omega⟩)) (ih (by omega))
        have hf : (∏ a : Fin (m + 1), t (d ⟨2 * a.val + 1, by omega⟩)) =
            t (d ⟨2 * m + 1, by omega⟩) * ∏ a : Fin m, t (d ⟨2 * a.val + 1, by omega⟩) := by
          rw [Fin.prod_univ_castSucc]
          exact mul_comm _ _
        intro r s
        rw [hf]
        exact h r s
    -- An odd depth has exactly one additional independent absolute matrix;
    -- it preserves the factor from the even prefix.
    let Bound : Fin (L + 1) → ℝ → Prop := fun n u =>
      ∀ (r : Fin (d n)) (s : Fin (d ⟨0, by omega⟩)),
        (∫ ω, |P (fun p => Z p ω) n.val (Nat.le_of_lt_succ n.isLt) false r s| ∂μ) ≤
          u * ∫ ω, P (fun p => Z p ω) n.val (Nat.le_of_lt_succ n.isLt) true r s ∂μ
    rcases Nat.mod_two_eq_zero_or_one L with he | ho
    · have h := heven (L / 2) (by omega)
      have hn : 2 * (L / 2) = L := by omega
      change Bound ⟨2 * (L / 2), by omega⟩ factor at h
      rw [show (⟨2 * (L / 2), by omega⟩ : Fin (L + 1)) = Fin.last L from Fin.ext hn] at h
      exact h i j
    · have h := hone (2 * (L / 2)) (by omega) factor (heven (L / 2) (by omega))
      have hn : 2 * (L / 2) + 1 = L := by omega
      change Bound ⟨2 * (L / 2) + 1, by omega⟩ factor at h
      rw [show (⟨2 * (L / 2) + 1, by omega⟩ : Fin (L + 1)) = Fin.last L from Fin.ext hn] at h
      exact h i j
  -- Integrating the finite sums against e ≥ 0 transfers the entrywise
  -- comparison to radii; e ≠ 0 and positive coefficient means give the
  -- strictly positive denominator in appendix lines 362–363.
  have hQmean i : (∫ ω, (Q ω).mulVec e i ∂μ) =
      ∑ j, (∫ ω, Q ω i j ∂μ) * e j := by
    simp only [Matrix.mulVec, dotProduct]
    rw [integral_finset_sum Finset.univ (fun j _ => (hQ i j).1.mul_const (e j))]
    simp only [integral_mul_const]
  have hOmean i : (∫ ω, (O ω).mulVec e i ∂μ) =
      ∑ j, (∫ ω, O ω i j ∂μ) * e j := by
    simp only [Matrix.mulVec, dotProduct]
    rw [integral_finset_sum Finset.univ (fun j _ => (hO i j).1.mul_const (e j))]
    simp only [integral_mul_const]
  have hpos i : 0 < ∫ ω, (Q ω).mulVec e i ∂μ := by
    rw [hQmean]
    exact Machinery.positive_weighted_sum
      _ e (fun j => (hQ i j).2) he hne
  -- Lemma B.2 says t = 1/g is decreasing. Bound each of the floor(L/2)
  -- pair factors by t(dmin), then divide by the positive expected radius.
  have hfactor : factor ≤ t dmin ^ (L / 2) :=
    Machinery.paired_scalar_bound L hL d hd
  dsimp only
  simp_rw [hr, hs]
  refine ⟨hpos, fun i => ?_⟩
  apply le_trans ((div_le_iff₀ (hpos i)).mpr ?_) hfactor
  rw [hOmean, hQmean, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_right (hO i j).2 (he j)
  -- formalizer:proof-end
)
end Corollary_3p8
