module
public import Formalization.Axioms
public import Formalization.Definition
public import Formalization.Result.Theorem_3p2
public import Formalization.Result.Lemma_Bp2
public import Formalization.Result.Lemma_3p7
public import Formalization.Result.Lemma_Bp1
public import Mathlib

public section

namespace Corollary_3p8.Machinery

-- formalizer:machinery-begin
lemma internal_minimum_bounds (L : ℕ) (hL : 2 ≤ L) (d : Fin (L + 1) → ℕ)
    (hd : ∀ k, 0 < d k) :
    0 < sInf {r : ℕ | ∃ k : Fin (L + 1), 0 < k.val ∧ k.val < L ∧ d k = r} ∧
    (∀ k : Fin (L + 1), 0 < k.val → k.val < L →
      sInf {r : ℕ | ∃ k : Fin (L + 1), 0 < k.val ∧ k.val < L ∧ d k = r} ≤ d k) := by
  have hn : Set.Nonempty {r : ℕ | ∃ k : Fin (L + 1),
      0 < k.val ∧ k.val < L ∧ d k = r} :=
    ⟨d ⟨1, by omega⟩, ⟨⟨1, by omega⟩, by simp, by change 1 < L; omega, rfl⟩⟩
  constructor
  · apply Nat.succ_le_iff.mp
    apply le_csInf hn
    rintro r ⟨k, _, _, rfl⟩
    exact hd k
  · intro k hk hkL
    exact csInf_le (OrderBot.bddBelow _) ⟨k, hk, hkL, rfl⟩

lemma tightness_positive (n : ℕ) (hn : 0 < n) :
    0 < Real.sqrt Real.pi * Real.Gamma (((n : ℝ) + 1) / 2) /
      ((n : ℝ) * Real.Gamma ((n : ℝ) / 2)) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  exact div_pos
    (mul_pos (Real.sqrt_pos.2 Real.pi_pos) (Axioms.external_gamma.1 _ (by positivity)).1)
    (mul_pos hn' (Axioms.external_gamma.1 _ (by positivity)).1)

lemma tightness_antitone (a b : ℕ) (ha : 0 < a) (hab : a ≤ b) :
    Real.sqrt Real.pi * Real.Gamma (((b : ℝ) + 1) / 2) /
      ((b : ℝ) * Real.Gamma ((b : ℝ) / 2)) ≤
    Real.sqrt Real.pi * Real.Gamma (((a : ℝ) + 1) / 2) /
      ((a : ℝ) * Real.Gamma ((a : ℝ) / 2)) := by
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hmono := Lemma_Bp2.gamma_ratio_growth.2.1
    (show (a : ℝ) ∈ Set.Ici 1 by change (1 : ℝ) ≤ a; exact_mod_cast ha)
    (show (b : ℝ) ∈ Set.Ici 1 by change (1 : ℝ) ≤ b; exact_mod_cast (ha.trans_le hab))
    (show (a : ℝ) ≤ b by exact_mod_cast hab)
  have hpos : 0 < (a : ℝ) * Real.Gamma ((a : ℝ) / 2) /
      (Real.sqrt Real.pi * Real.Gamma (((a : ℝ) + 1) / 2)) :=
    div_pos (mul_pos ha' (Axioms.external_gamma.1 _ (by positivity)).1)
      (mul_pos (Real.sqrt_pos.2 Real.pi_pos) (Axioms.external_gamma.1 _ (by positivity)).1)
  simpa only [one_div_div] using one_div_le_one_div_of_le hpos hmono

lemma paired_scalar_bound (L : ℕ) (hL : 2 ≤ L) (d : Fin (L + 1) → ℕ)
    (hd : ∀ k, 0 < d k) :
    let t := fun n : ℕ => Real.sqrt Real.pi * Real.Gamma (((n : ℝ) + 1) / 2) /
      ((n : ℝ) * Real.Gamma ((n : ℝ) / 2))
    let dmin := sInf {r : ℕ | ∃ k : Fin (L + 1), 0 < k.val ∧ k.val < L ∧ d k = r}
    (∏ j : Fin (L / 2), t (d ⟨2 * j.val + 1, by omega⟩)) ≤ t dmin ^ (L / 2) := by
  classical
  let t := fun n : ℕ => Real.sqrt Real.pi * Real.Gamma (((n : ℝ) + 1) / 2) /
    ((n : ℝ) * Real.Gamma ((n : ℝ) / 2))
  let dmin := sInf {r : ℕ | ∃ k : Fin (L + 1), 0 < k.val ∧ k.val < L ∧ d k = r}
  change (∏ j : Fin (L / 2), t (d ⟨2 * j.val + 1, _⟩)) ≤ t dmin ^ (L / 2)
  have hm := internal_minimum_bounds L hL d hd
  calc
    _ ≤ ∏ _j : Fin (L / 2), t dmin := by
      apply Finset.prod_le_prod
      · intro j _
        exact (tightness_positive _ (hd _)).le
      · intro j _
        exact tightness_antitone _ _ hm.1 (hm.2 ⟨2 * j.val + 1, by omega⟩
          (by change 0 < 2 * j.val + 1; omega)
          (by change 2 * j.val + 1 < L; have := j.isLt; omega))
    _ = _ := by simp

lemma absolute_matrix_product_bound {a b c : ℕ}
    (A : Matrix (Fin a) (Fin b) ℝ) (B : Matrix (Fin b) (Fin c) ℝ) :
    ∀ i j, |(A * B) i j| ≤ (A.map abs * B.map abs) i j := by
  intro i j
  simp only [Matrix.mul_apply, Matrix.map_apply]
  simpa only [abs_mul] using Finset.abs_sum_le_sum_abs (fun k => A i k * B k j) Finset.univ

lemma independent_matrix_product_mean {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) {a b c : ℕ}
    (A : Ω → Matrix (Fin a) (Fin b) ℝ) (B : Ω → Matrix (Fin b) (Fin c) ℝ)
    (hA : ∀ i k, MeasureTheory.Integrable (fun ω => A ω i k) μ)
    (hB : ∀ k j, MeasureTheory.Integrable (fun ω => B ω k j) μ)
    (hAB : ∀ i k j, ProbabilityTheory.IndepFun (fun ω => A ω i k) (fun ω => B ω k j) μ) :
    (∀ i j, MeasureTheory.Integrable (fun ω => (A ω * B ω) i j) μ) ∧
    (∀ i j, (∫ ω, (A ω * B ω) i j ∂μ) =
      (Matrix.of (fun i k => ∫ ω, A ω i k ∂μ) *
        Matrix.of (fun k j => ∫ ω, B ω k j ∂μ)) i j) := by
  classical
  have hint i k j := (hAB i k j).integrable_mul (hA i k) (hB k j)
  constructor
  · intro i j
    simpa only [Matrix.mul_apply] using
      MeasureTheory.integrable_finset_sum Finset.univ (fun k _ => hint i k j)
  · intro i j
    simp only [Matrix.mul_apply]
    erw [MeasureTheory.integral_finset_sum Finset.univ (fun k _ => hint i k j)]
    apply Finset.sum_congr rfl
    intro k _
    exact (hAB i k j).integral_fun_mul_eq_mul_integral
      (hA i k).aestronglyMeasurable (hB k j).aestronglyMeasurable

lemma independent_product_integrable {Ω I : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : I → Ω → ℝ) (hX : ∀ i, MeasureTheory.Integrable (X i) μ)
    (hi : ProbabilityTheory.iIndepFun X μ) (s : Finset I) :
    MeasureTheory.Integrable (fun ω => ∏ i ∈ s, X i ω) μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (MeasureTheory.integrable_const (1 : ℝ))
  | @insert i s his ih =>
    have hind := (hi.indepFun_finset_prod_of_notMem₀
      (fun j => (hX j).aemeasurable) his).symm
    have hprod : MeasureTheory.Integrable (∏ j ∈ s, X j) μ := by
      convert ih using 1
      funext ω
      simp
    convert hind.integrable_mul (hX i) hprod using 1
    funext ω
    simp [his]

lemma positive_weighted_sum {I : Type*} [Fintype I] (a e : I → ℝ)
    (ha : ∀ j, 0 < a j) (he : ∀ j, 0 ≤ e j) (hne : e ≠ 0) :
    0 < ∑ j, a j * e j := by
  classical
  obtain ⟨j, hj⟩ : ∃ j, e j ≠ 0 := by
    by_contra hn
    apply hne
    funext j
    simpa using not_exists.mp hn j
  apply Finset.sum_pos' (fun j _ => mul_nonneg (ha j).le (he j))
  exact ⟨j, Finset.mem_univ _, mul_pos (ha j) (lt_of_le_of_ne (he j) (Ne.symm hj))⟩

lemma pair_coefficient_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (d : Fin 3 → ℕ) (σ : Fin 2 → NNReal)
    (W : Ω → ∀ k : Fin 2, Matrix (Fin (d k.succ)) (Fin (d k.castSucc)) ℝ)
    (hinit : (Definition.gaussian_initialization μ 2 d σ W (fun _ => 0)).1)
    (i : Fin (d 2)) (j : Fin (d 0)) :
    let C := fun ω => |∑ k, W ω 1 i k * W ω 0 k j|
    let D := fun ω => ∑ k, |W ω 1 i k| * |W ω 0 k j|
    MeasureTheory.Integrable C μ ∧ MeasureTheory.Integrable D μ ∧
    0 < ∫ ω, D ω ∂μ ∧
    (∫ ω, C ω ∂μ) =
      (Real.sqrt Real.pi * Real.Gamma (((d 1 : ℝ) + 1) / 2) /
        ((d 1 : ℝ) * Real.Gamma ((d 1 : ℝ) / 2))) * ∫ ω, D ω ∂μ := by
  classical
  rcases hinit with ⟨hprob, hL, hd, hσ, hind, hlaw⟩
  letI := hprob
  have hm := fun k a b =>
    Lemma_3p7.Machinery.gaussian_abs_moment
      μ (fun ω => W ω k a b) (σ k) (hσ k) (hlaw ⟨k, a, b⟩)
  have hmeas k a b := (hlaw ⟨k, a, b⟩).aemeasurable.aestronglyMeasurable
  have hip k := hind.indepFun (i := ⟨1, i, k⟩) (j := ⟨0, k, j⟩)
    (by intro h; have hh := congrArg Sigma.fst h; cases hh)
  have hprod k : MeasureTheory.Integrable (fun ω => |W ω 1 i k| * |W ω 0 k j|) μ :=
    ((hip k).comp measurable_abs measurable_abs).integrable_mul (hm 1 i k).1 (hm 0 k j).1
  have hsigned k : MeasureTheory.Integrable (fun ω => W ω 1 i k * W ω 0 k j) μ := by
    apply (hprod k).mono' ((hmeas 1 i k).mul (hmeas 0 k j))
    exact Filter.Eventually.of_forall (fun ω => by simp only [Real.norm_eq_abs, Pi.mul_apply, abs_mul]; rfl)
  have hC := (MeasureTheory.integrable_finset_sum Finset.univ (fun k _ => hsigned k)).abs
  have hD := MeasureTheory.integrable_finset_sum Finset.univ (fun k _ => hprod k)
  let e : Fin (d 0) → ℝ := Pi.single j 1
  have he : ∀ a, 0 ≤ e a := by
    intro a
    by_cases h : a = j <;> simp [e, Pi.single_apply, h, eq_comm]
  have hne : e ≠ 0 := by
    intro h
    have hj := congrFun h j
    simp [e] at hj
  have hw := Lemma_3p7.initialization_width μ d σ W ⟨hprob, hL, hd, hσ, hind, hlaw⟩ 0 e he hne
  have hr (ω : Ω) :
      (((Definition.linear_network 2 d (W ω)).2.2.2 0 e).1.2 i -
        ((Definition.linear_network 2 d (W ω)).2.2.2 0 e).1.1 i) / 2 =
      |∑ k, W ω 1 i k * W ω 0 k j| := by
    have h := congrFun (Lemma_Bp1.two_layer_boxes d hd (W ω) 0 e he).2.2.1 i
    change (((Definition.linear_network 2 d (W ω)).2.2.2 0 e).1.2 i -
      ((Definition.linear_network 2 d (W ω)).2.2.2 0 e).1.1 i) / 2 =
      ((Definition.linear_network 2 d (W ω)).2.1.mulVec e) i at h
    rw [h]
    let A : Matrix (Fin (d 1)) (Fin (d 0)) ℝ := W ω 0
    let B : Matrix (Fin (d 2)) (Fin (d 1)) ℝ := W ω 1
    change (((B * (A * (1 : Matrix (Fin (d 0)) (Fin (d 0)) ℝ))).map abs).mulVec (Pi.single j 1)) i = _
    simp only [Matrix.mul_one, Matrix.mulVec_single_one, Matrix.map_apply, Matrix.mul_apply]
    rfl
  have hs (ω : Ω) :
      (((Definition.linear_network 2 d (W ω)).2.2.2 0 e).2.2 i -
        ((Definition.linear_network 2 d (W ω)).2.2.2 0 e).2.1 i) / 2 =
      ∑ k, |W ω 1 i k| * |W ω 0 k j| := by
    have h := congrFun (Lemma_Bp1.two_layer_boxes d hd (W ω) 0 e he).2.2.2 i
    change (((Definition.linear_network 2 d (W ω)).2.2.2 0 e).2.2 i -
      ((Definition.linear_network 2 d (W ω)).2.2.2 0 e).2.1 i) / 2 =
      ((Definition.linear_network 2 d (W ω)).2.2.1.mulVec e) i at h
    rw [h]
    let A : Matrix (Fin (d 1)) (Fin (d 0)) ℝ := W ω 0
    let B : Matrix (Fin (d 2)) (Fin (d 1)) ℝ := W ω 1
    change (B.map abs * (A.map abs * (1 : Matrix (Fin (d 0)) (Fin (d 0)) ℝ))).mulVec (Pi.single j 1) i = _
    simp only [Matrix.mul_one, Matrix.mulVec_single_one, Matrix.mul_apply, Matrix.map_apply]
    rfl
  have hpos := hw.1 i
  have hratio := hw.2.1 i
  change 0 < ∫ ω, (((Definition.linear_network 2 d (W ω)).2.2.2 0 e).2.2 i -
    ((Definition.linear_network 2 d (W ω)).2.2.2 0 e).2.1 i) / 2 ∂μ at hpos
  simp_rw [hs] at hpos
  change (∫ ω, (((Definition.linear_network 2 d (W ω)).2.2.2 0 e).1.2 i -
    ((Definition.linear_network 2 d (W ω)).2.2.2 0 e).1.1 i) / 2 ∂μ) /
    (∫ ω, (((Definition.linear_network 2 d (W ω)).2.2.2 0 e).2.2 i -
    ((Definition.linear_network 2 d (W ω)).2.2.2 0 e).2.1 i) / 2 ∂μ) = _ at hratio
  simp_rw [hr, hs] at hratio
  exact ⟨hC, hD, hpos, (div_eq_iff hpos.ne').mp hratio⟩

lemma independent_coordinate_functions {Ω I : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [Fintype I] (Z : I → Ω → ℝ)
    (hZ : ∀ i, AEMeasurable (Z i) μ) (hi : ProbabilityTheory.iIndepFun Z μ)
    (S T : Finset I) (hST : Disjoint S T) (f g : (I → ℝ) → ℝ)
    (hf : Measurable f) (hg : Measurable g)
    (hfS : ∀ x y, (∀ i ∈ S, x i = y i) → f x = f y)
    (hgT : ∀ x y, (∀ i ∈ T, x i = y i) → g x = g y) :
    ProbabilityTheory.IndepFun (fun ω => f (fun i => Z i ω))
      (fun ω => g (fun i => Z i ω)) μ := by
  classical
  let extS := fun (v : S → ℝ) (i : I) => if hi : i ∈ S then v ⟨i, hi⟩ else 0
  let extT := fun (v : T → ℝ) (i : I) => if hi : i ∈ T then v ⟨i, hi⟩ else 0
  have h := (ProbabilityTheory.iIndepFun.indepFun_finset₀ S T hST hi hZ).comp
    (φ := fun v => f (extS v)) (ψ := fun v => g (extT v))
    (hf.comp (by
      apply measurable_pi_lambda
      intro i
      by_cases hi : i ∈ S <;> simp [extS, hi] <;> fun_prop))
    (hg.comp (by
      apply measurable_pi_lambda
      intro i
      by_cases hi : i ∈ T <;> simp [extT, hi] <;> fun_prop))
  convert h using 1
  · funext ω
    apply hfS
    intro i hi
    simp [extS, hi]
  · funext ω
    apply hgT
    intro i hi
    simp [extT, hi]

lemma gaussian_sequential_coefficients {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (L : ℕ) (d : Fin (L + 1) → ℕ)
    (σ : Fin L → NNReal)
    (W : Ω → ∀ k : Fin L, Matrix (Fin (d k.succ)) (Fin (d k.castSucc)) ℝ)
    (hinit : (Definition.gaussian_initialization μ L d σ W (fun _ => 0)).1) :
    ∀ i j, MeasureTheory.Integrable (fun ω => (Definition.linear_network L d (W ω)).2.2.1 i j) μ ∧
      0 < ∫ ω, (Definition.linear_network L d (W ω)).2.2.1 i j ∂μ := by
  classical
  rcases hinit with ⟨hprob, hL, hd, hσ, hind, hlaw⟩
  letI := hprob
  let I := Σ k : Fin L, Fin (d k.succ) × Fin (d k.castSucc)
  let Z : I → Ω → ℝ := fun p ω => W ω p.1 p.2.1 p.2.2
  let P := fun z : I → ℝ => Nat.rec
    (motive := fun k => (hk : k ≤ L) → Bool →
      Matrix (Fin (d ⟨k, by omega⟩)) (Fin (d ⟨0, Nat.zero_lt_succ L⟩)) ℝ)
    (fun _ _ => 1)
    (fun k ih hk a => fun i j => ∑ t,
      (if a then |z ⟨⟨k, by omega⟩, i, t⟩| else z ⟨⟨k, by omega⟩, i, t⟩) * ih (by omega) a t j)
  have hmeas : ∀ k (hk : k ≤ L) i j, Measurable (fun z => P z k hk true i j) := by
    intro k
    induction k with
    | zero => intro hk i j; exact measurable_const
    | succ k ih =>
      intro hk i j
      change Measurable (fun z : I → ℝ => ∑ t,
        |z ⟨⟨k, by omega⟩, i, t⟩| * P z k (by omega) true t j)
      exact Finset.measurable_sum _ (fun t _ => (measurable_pi_apply _).abs.mul (ih _ t j))
  have hlocal : ∀ k (hk : k ≤ L) i j (z z' : I → ℝ),
      (∀ p, p.1.val < k → z p = z' p) → P z k hk true i j = P z' k hk true i j := by
    intro k
    induction k with
    | zero => intros; rfl
    | succ k ih =>
      intro hk i j z z' heq
      change (∑ t, |z ⟨⟨k, by omega⟩, i, t⟩| * P z k (by omega) true t j) =
        ∑ t, |z' ⟨⟨k, by omega⟩, i, t⟩| * P z' k (by omega) true t j
      apply Finset.sum_congr rfl
      intro t _
      rw [heq ⟨⟨k, by omega⟩, i, t⟩ (by simp), ih _ t j z z' (fun p hp => heq p (by omega))]
  have hm := fun k i j =>
    Lemma_3p7.Machinery.gaussian_abs_moment
      μ (fun ω => W ω k i j) (σ k) (hσ k) (hlaw ⟨k, i, j⟩)
  have hmoment : ∀ k (hk : k ≤ L) i j,
      MeasureTheory.Integrable (fun ω => P (fun p => Z p ω) k hk true i j) μ ∧
      (0 < k → 0 < ∫ ω, P (fun p => Z p ω) k hk true i j ∂μ) := by
    intro k
    induction k with
    | zero =>
      intro hk i j
      exact ⟨MeasureTheory.integrable_const _, by omega⟩
    | succ k ih =>
      intro hk i j
      have hcoeff (t : Fin (d ⟨k, by omega⟩)) := hm ⟨k, by omega⟩ i t
      have hpos (t : Fin (d ⟨k, by omega⟩)) : 0 < ∫ ω, |W ω ⟨k, by omega⟩ i t| ∂μ := by
        rw [(hcoeff t).2]
        exact mul_pos (by exact_mod_cast hσ ⟨k, by omega⟩)
          (Real.sqrt_pos.2 (div_pos (by norm_num) Real.pi_pos))
      have hi (t : Fin (d ⟨k, by omega⟩)) : ProbabilityTheory.IndepFun (fun ω => |W ω ⟨k, by omega⟩ i t|)
          (fun ω => P (fun p => Z p ω) k (by omega) true t j) μ := by
        refine independent_coordinate_functions μ Z (fun p => (hlaw p).aemeasurable) hind
          {⟨⟨k, by omega⟩, i, t⟩} (Finset.univ.filter (fun p => p.1.val < k)) ?_
          (fun z => |z ⟨⟨k, by omega⟩, i, t⟩|)
          (fun z => P z k (by omega) true t j) ?_ ?_ ?_ ?_
        · simp
        · exact (measurable_pi_apply _).abs
        · exact hmeas k (by omega) t j
        · intro z z' heq
          exact congrArg abs (heq _ (Finset.mem_singleton_self _))
        · intro z z' heq
          exact hlocal k (by omega) t j z z' (fun p hp => heq p (by simp [hp]))
      have hint t := (hi t).integrable_mul (hcoeff t).1 (ih (by omega) t j).1
      have hintsum := MeasureTheory.integrable_finset_sum Finset.univ (fun t _ => hint t)
      constructor
      · exact hintsum
      · intro _
        change 0 < ∫ ω, ∑ t, |W ω ⟨k, by omega⟩ i t| *
          P (fun p => Z p ω) k (by omega) true t j ∂μ
        erw [MeasureTheory.integral_finset_sum Finset.univ (fun t _ => hint t)]
        simp only [Pi.mul_apply]
        simp_rw [(hi _).integral_fun_mul_eq_mul_integral
          (hcoeff _).1.aestronglyMeasurable (ih (by omega) _ j).1.aestronglyMeasurable]
        cases k with
        | zero =>
          simpa [P, Matrix.one_apply, Z] using hpos j
        | succ k =>
          apply Finset.sum_pos'
          · intro t _
            exact (mul_pos (hpos t) ((ih (by omega) t j).2 (by omega))).le
          · exact ⟨⟨0, hd ⟨k + 1, by omega⟩⟩, Finset.mem_univ _,
              mul_pos (hpos _) ((ih (by omega) _ j).2 (by omega))⟩
  intro i j
  exact ⟨(hmoment L le_rfl i j).1, (hmoment L le_rfl i j).2 hL⟩

lemma optimal_coefficient_integrable {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (L : ℕ) (d : Fin (L + 1) → ℕ)
    (σ : Fin L → NNReal)
    (W : Ω → ∀ k : Fin L, Matrix (Fin (d k.succ)) (Fin (d k.castSucc)) ℝ)
    (hinit : (Definition.gaussian_initialization μ L d σ W (fun _ => 0)).1) :
    ∀ i j, MeasureTheory.Integrable (fun ω => (Definition.linear_network L d (W ω)).2.1 i j) μ := by
  classical
  let P := fun ω => Nat.rec
    (motive := fun k => (hk : k ≤ L) → Bool →
      Matrix (Fin (d ⟨k, by omega⟩)) (Fin (d ⟨0, Nat.zero_lt_succ L⟩)) ℝ)
    (fun _ _ => 1)
    (fun k ih hk a => fun i j => ∑ t,
      (if a then |W ω ⟨k, by omega⟩ i t| else W ω ⟨k, by omega⟩ i t) * ih (by omega) a t j)
  have hmeas : ∀ k (hk : k ≤ L) i j,
      MeasureTheory.AEStronglyMeasurable (fun ω => P ω k hk false i j) μ := by
    intro k
    induction k with
    | zero => intros; exact MeasureTheory.aestronglyMeasurable_const
    | succ k ih =>
      intro hk i j
      change MeasureTheory.AEStronglyMeasurable (fun ω => ∑ t,
        W ω ⟨k, by omega⟩ i t * P ω k (by omega) false t j) μ
      exact Finset.aestronglyMeasurable_fun_sum _ (fun t _ =>
        (hinit.2.2.2.2.2 ⟨⟨k, by omega⟩, i, t⟩).aemeasurable.aestronglyMeasurable.mul (ih _ t j))
  have hbound : ∀ k (hk : k ≤ L) ω i j,
      |P ω k hk false i j| ≤ P ω k hk true i j := by
    intro k
    induction k with
    | zero =>
      intro hk ω i j
      change |(1 : Matrix (Fin (d ⟨0, by omega⟩)) (Fin (d ⟨0, by omega⟩)) ℝ) i j| ≤
        (1 : Matrix (Fin (d ⟨0, by omega⟩)) (Fin (d ⟨0, by omega⟩)) ℝ) i j
      rw [Matrix.one_apply]
      split_ifs <;> norm_num
    | succ k ih =>
      intro hk ω i j
      change |∑ t, W ω ⟨k, by omega⟩ i t * P ω k (by omega) false t j| ≤
        ∑ t, |W ω ⟨k, by omega⟩ i t| * P ω k (by omega) true t j
      apply (Finset.abs_sum_le_sum_abs _ _).trans
      apply Finset.sum_le_sum
      intro t _
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (ih _ ω t j) (abs_nonneg _)
  intro i j
  apply (gaussian_sequential_coefficients μ L d σ W hinit i j).1.mono'
    (continuous_abs.comp_aestronglyMeasurable (hmeas L le_rfl i j))
  exact Filter.Eventually.of_forall (fun ω => by
    change ‖|P ω L le_rfl false i j|‖ ≤ P ω L le_rfl true i j
    simpa only [Real.norm_eq_abs, abs_abs] using hbound L le_rfl ω i j)

lemma consecutive_pair_moments {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (L : ℕ) (d : Fin (L + 1) → ℕ)
    (σ : Fin L → NNReal)
    (W : Ω → ∀ k : Fin L, Matrix (Fin (d k.succ)) (Fin (d k.castSucc)) ℝ)
    (hinit : (Definition.gaussian_initialization μ L d σ W (fun _ => 0)).1)
    (k : ℕ) (hk : k + 2 ≤ L) (i : Fin (d ⟨k + 2, by omega⟩))
    (j : Fin (d ⟨k, by omega⟩)) :
    let C := fun ω => |∑ a, W ω ⟨k + 1, by omega⟩ i a * W ω ⟨k, by omega⟩ a j|
    let D := fun ω => ∑ a, |W ω ⟨k + 1, by omega⟩ i a| * |W ω ⟨k, by omega⟩ a j|
    MeasureTheory.Integrable C μ ∧ MeasureTheory.Integrable D μ ∧
    0 < ∫ ω, D ω ∂μ ∧
    (∫ ω, C ω ∂μ) =
      (Real.sqrt Real.pi * Real.Gamma (((d ⟨k + 1, by omega⟩ : ℝ) + 1) / 2) /
        ((d ⟨k + 1, by omega⟩ : ℝ) * Real.Gamma ((d ⟨k + 1, by omega⟩ : ℝ) / 2))) *
        ∫ ω, D ω ∂μ := by
  let d' : Fin 3 → ℕ := fun a => d ⟨k + a.val, by omega⟩
  let σ' : Fin 2 → NNReal := fun a => σ ⟨k + a.val, by omega⟩
  let W' : Ω → ∀ a : Fin 2, Matrix (Fin (d' a.succ)) (Fin (d' a.castSucc)) ℝ :=
    fun ω a => W ω ⟨k + a.val, by omega⟩
  let ι : (Σ a : Fin 2, Fin (d' a.succ) × Fin (d' a.castSucc)) →
      (Σ a : Fin L, Fin (d a.succ) × Fin (d a.castSucc)) :=
    fun p => ⟨⟨k + p.1.val, by omega⟩, p.2⟩
  have hinj : Function.Injective ι := by
    rintro ⟨a, u⟩ ⟨b, v⟩ h
    have hab : a = b := Fin.ext (Nat.add_left_cancel (congrArg (fun p => p.1.val) h))
    subst b
    have huv : u = v := by simpa [ι] using h
    subst v
    rfl
  have hp : (Definition.gaussian_initialization μ 2 d' σ' W' (fun _ => 0)).1 := by
    refine ⟨hinit.1, by norm_num, (fun a => hinit.2.2.1 _),
      (fun a => hinit.2.2.2.1 _), ?_, fun p => hinit.2.2.2.2.2 (ι p)⟩
    exact hinit.2.2.2.2.1.precomp hinj
  exact pair_coefficient_moments μ d' σ' W' hp i j

lemma prefix_regularity {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (L : ℕ) (d : Fin (L + 1) → ℕ)
    (σ : Fin L → NNReal)
    (W : Ω → ∀ k : Fin L, Matrix (Fin (d k.succ)) (Fin (d k.castSucc)) ℝ)
    (hinit : (Definition.gaussian_initialization μ L d σ W (fun _ => 0)).1) :
    let I := Σ k : Fin L, Fin (d k.succ) × Fin (d k.castSucc)
    let P := fun z : I → ℝ => Nat.rec
      (motive := fun k => (hk : k ≤ L) → Bool →
        Matrix (Fin (d ⟨k, by omega⟩)) (Fin (d ⟨0, Nat.zero_lt_succ L⟩)) ℝ)
      (fun _ _ => 1)
      (fun k ih hk a => fun i j => ∑ t,
        (if a then |z ⟨⟨k, by omega⟩, i, t⟩| else z ⟨⟨k, by omega⟩, i, t⟩) * ih (by omega) a t j)
    (∀ k (hk : k ≤ L) a i j, Measurable (fun z => P z k hk a i j)) ∧
    (∀ k (hk : k ≤ L) a i j (z z' : I → ℝ),
      (∀ p, p.1.val < k → z p = z' p) → P z k hk a i j = P z' k hk a i j) ∧
    (∀ k (hk : k ≤ L) a i j,
      MeasureTheory.Integrable (fun ω => P (fun p => W ω p.1 p.2.1 p.2.2) k hk a i j) μ) := by
  classical
  dsimp only
  let I := Σ k : Fin L, Fin (d k.succ) × Fin (d k.castSucc)
  let Z : I → Ω → ℝ := fun p ω => W ω p.1 p.2.1 p.2.2
  let P := fun z : I → ℝ => Nat.rec
    (motive := fun k => (hk : k ≤ L) → Bool →
      Matrix (Fin (d ⟨k, by omega⟩)) (Fin (d ⟨0, Nat.zero_lt_succ L⟩)) ℝ)
    (fun _ _ => 1)
    (fun k ih hk a => fun i j => ∑ t,
      (if a then |z ⟨⟨k, by omega⟩, i, t⟩| else z ⟨⟨k, by omega⟩, i, t⟩) * ih (by omega) a t j)
  change (∀ k hk a i j, Measurable (fun z => P z k hk a i j)) ∧ _
  have hmeas : ∀ k (hk : k ≤ L) a i j, Measurable (fun z => P z k hk a i j) := by
    intro k
    induction k with
    | zero => intros; exact measurable_const
    | succ k ih =>
      intro hk a i j
      change Measurable (fun z : I → ℝ => ∑ t,
        (if a then |z ⟨⟨k, by omega⟩, i, t⟩| else z ⟨⟨k, by omega⟩, i, t⟩) * P z k (by omega) a t j)
      apply Finset.measurable_sum
      intro t _
      apply Measurable.mul _ (ih _ a t j)
      cases a <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop
  have hlocal : ∀ k (hk : k ≤ L) a i j (z z' : I → ℝ),
      (∀ p, p.1.val < k → z p = z' p) → P z k hk a i j = P z' k hk a i j := by
    intro k
    induction k with
    | zero => intros; rfl
    | succ k ih =>
      intro hk a i j z z' heq
      change (∑ t, (if a then |z ⟨⟨k, by omega⟩, i, t⟩| else z ⟨⟨k, by omega⟩, i, t⟩) *
        P z k (by omega) a t j) = ∑ t, (if a then |z' ⟨⟨k, by omega⟩, i, t⟩| else z' ⟨⟨k, by omega⟩, i, t⟩) *
        P z' k (by omega) a t j
      apply Finset.sum_congr rfl
      intro t _
      rw [heq ⟨⟨k, by omega⟩, i, t⟩ (by simp), ih _ a t j z z' (fun p hp => heq p (by omega))]
  refine ⟨hmeas, hlocal, ?_⟩
  letI := hinit.1
  have hm k i j := Lemma_3p7.Machinery.gaussian_abs_moment
    μ (fun ω => W ω k i j) (σ k) (hinit.2.2.2.1 k) (hinit.2.2.2.2.2 ⟨k, i, j⟩)
  have hweight k i j (a : Bool) : MeasureTheory.Integrable
      (fun ω => if a then |W ω k i j| else W ω k i j) μ := by
    cases a
    · apply (hm k i j).1.mono'
        (hinit.2.2.2.2.2 ⟨k, i, j⟩).aemeasurable.aestronglyMeasurable
      exact Filter.Eventually.of_forall (fun ω => le_rfl)
    · exact (hm k i j).1
  intro k
  induction k with
  | zero => intros; exact MeasureTheory.integrable_const _
  | succ k ih =>
    intro hk a i j
    have hi (t : Fin (d ⟨k, by omega⟩)) : ProbabilityTheory.IndepFun
        (fun ω => if a then |W ω ⟨k, by omega⟩ i t| else W ω ⟨k, by omega⟩ i t)
        (fun ω => P (fun p => Z p ω) k (by omega) a t j) μ := by
      refine independent_coordinate_functions μ Z (fun p => (hinit.2.2.2.2.2 p).aemeasurable)
        hinit.2.2.2.2.1 {⟨⟨k, by omega⟩, i, t⟩}
        (Finset.univ.filter (fun p => p.1.val < k)) (by simp)
        (fun z => if a then |z ⟨⟨k, by omega⟩, i, t⟩| else z ⟨⟨k, by omega⟩, i, t⟩)
        (fun z => P z k (by omega) a t j) ?_ (hmeas k (by omega) a t j) ?_ ?_
      · cases a <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop
      · intro z z' heq
        exact congrArg (fun r : ℝ => if a then |r| else r) (heq _ (Finset.mem_singleton_self _))
      · intro z z' heq
        exact hlocal k (by omega) a t j z z' (fun p hp => heq p (by simp [hp]))
    exact MeasureTheory.integrable_finset_sum Finset.univ (fun t _ =>
      (hi t).integrable_mul (hweight ⟨k, by omega⟩ i t a) (ih (by omega) a t j))

lemma block_expectation_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) {a b c : ℕ}
    (C D : Ω → Matrix (Fin a) (Fin b) ℝ)
    (F Q : Ω → Matrix (Fin b) (Fin c) ℝ) (R : Ω → Matrix (Fin a) (Fin c) ℝ)
    (hC : ∀ i k, MeasureTheory.Integrable (fun ω => C ω i k) μ)
    (hD : ∀ i k, MeasureTheory.Integrable (fun ω => D ω i k) μ)
    (hF : ∀ k j, MeasureTheory.Integrable (fun ω => |F ω k j|) μ)
    (hQ : ∀ k j, MeasureTheory.Integrable (fun ω => Q ω k j) μ)
    (hR : ∀ i j, MeasureTheory.Integrable (fun ω => R ω i j) μ)
    (hCF : ∀ i k j, ProbabilityTheory.IndepFun (fun ω => C ω i k) (fun ω => |F ω k j|) μ)
    (hDQ : ∀ i k j, ProbabilityTheory.IndepFun (fun ω => D ω i k) (fun ω => Q ω k j) μ)
    (hCpos : ∀ ω i k, 0 ≤ C ω i k)
    (hbound : ∀ ω i j, R ω i j ≤ (C ω * (F ω).map abs) i j)
    (u v : ℝ) (hpair : ∀ i k, (∫ ω, C ω i k ∂μ) = v * ∫ ω, D ω i k ∂μ)
    (hprefix : ∀ k j, (∫ ω, |F ω k j| ∂μ) ≤ u * ∫ ω, Q ω k j ∂μ) :
    ∀ i j, (∫ ω, R ω i j ∂μ) ≤ (v * u) * ∫ ω, (D ω * Q ω) i j ∂μ := by
  classical
  have hleft := independent_matrix_product_mean μ C (fun ω => (F ω).map abs) hC hF hCF
  have hright := independent_matrix_product_mean μ D Q hD hQ hDQ
  intro i j
  calc
    _ ≤ ∫ ω, (C ω * (F ω).map abs) i j ∂μ :=
      MeasureTheory.integral_mono (hR i j) (hleft.1 i j) (fun ω => hbound ω i j)
    _ = ∑ k, (∫ ω, C ω i k ∂μ) * ∫ ω, |F ω k j| ∂μ := hleft.2 i j
    _ ≤ ∑ k, (∫ ω, C ω i k ∂μ) * (u * ∫ ω, Q ω k j ∂μ) := by
      apply Finset.sum_le_sum
      intro k _
      exact mul_le_mul_of_nonneg_left (hprefix k j)
        (MeasureTheory.integral_nonneg (fun ω => hCpos ω i k))
    _ = (v * u) * ∫ ω, (D ω * Q ω) i j ∂μ := by
      rw [hright.2]
      simp only [Matrix.mul_apply, Matrix.of_apply]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      rw [hpair]
      ring

-- formalizer:machinery-end

end Corollary_3p8.Machinery
