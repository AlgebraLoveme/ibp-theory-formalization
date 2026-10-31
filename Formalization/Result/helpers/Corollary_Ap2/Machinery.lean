module
public import Formalization.Axioms
public import Formalization.Definition
public import Formalization.Result.Lemma_3p7
public import Formalization.Result.Lemma_Bp1
public import Mathlib

public section

namespace Corollary_Ap2.Machinery

-- formalizer:machinery-begin
lemma sqrt_deviation_bound (u a : ℝ) (hu : 0 ≤ u) (ha : 0 < a) :
    |Real.sqrt u - Real.sqrt a| ≤ |u - a| / Real.sqrt a := by
  have hs := Real.sqrt_pos.2 ha
  have hsu := Real.sqrt_nonneg u
  have hu2 := Real.sq_sqrt hu
  have ha2 := Real.sq_sqrt ha.le
  apply (le_div_iff₀ hs).mpr
  have hid : (Real.sqrt u - Real.sqrt a) * (Real.sqrt u + Real.sqrt a) = u - a := by
    nlinarith
  rw [← hid, abs_mul, abs_of_nonneg (by positivity : 0 ≤ Real.sqrt u + Real.sqrt a)]
  exact mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)

lemma halfspace_even_integral {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (A V : Ω → ℝ)
    (hA : AEMeasurable A μ) (hV : MeasureTheory.Integrable V μ)
    (hne : ∀ᵐ ω ∂μ, A ω ≠ 0)
    (hsym : ProbabilityTheory.IdentDistrib (fun ω => (A ω, V ω))
      (fun ω => (-A ω, V ω)) μ μ) :
    (∫ ω, if 0 < A ω then V ω else 0 ∂μ) = (∫ ω, V ω ∂μ) / 2 := by
  have hp : MeasureTheory.Integrable (fun ω => if 0 < A ω then V ω else 0) μ := by
    exact hV.indicator₀ (nullMeasurableSet_lt aemeasurable_const hA)
  have hm : MeasureTheory.Integrable (fun ω => if 0 < -A ω then V ω else 0) μ := by
    exact hV.indicator₀ (nullMeasurableSet_lt aemeasurable_const hA.neg)
  have he := (hsym.comp (show Measurable
    (fun p : ℝ × ℝ => if 0 < p.1 then p.2 else 0) from
      measurable_snd.ite (measurableSet_lt measurable_const measurable_fst)
        measurable_const)).integral_eq
  have hsum : (fun ω => (if 0 < A ω then V ω else 0) +
      (if 0 < -A ω then V ω else 0)) =ᵐ[μ] V := by
    filter_upwards [hne] with ω hω
    rcases lt_or_gt_of_ne hω with h | h
    · simp [h, le_of_lt h, neg_pos.mpr h]
    · simp [h, le_of_lt h]
  have hi := MeasureTheory.integral_congr_ae hsum
  rw [MeasureTheory.integral_add hp hm] at hi
  simp only [Function.comp_def] at he
  linarith

lemma gaussian_row_even_half {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (d : ℕ) (Z : Fin d → Ω → ℝ)
    (hZ : ∀ j, ProbabilityTheory.HasLaw (Z j) (ProbabilityTheory.gaussianReal 0 1) μ)
    (hInd : ProbabilityTheory.iIndepFun Z μ)
    (x : Fin d → ℝ) (hx : x ≠ 0)
    (φ : (Fin d → ℝ) → ℝ) (hφ : Measurable φ)
    (heven : ∀ z, φ (-z) = φ z)
    (hint : MeasureTheory.Integrable (fun ω => φ (fun j => Z j ω)) μ) :
    (∫ ω, if 0 < ∑ j, x j * Z j ω then φ (fun j => Z j ω) else 0 ∂μ) =
      (∫ ω, φ (fun j => Z j ω) ∂μ) / 2 := by
  have hz : AEMeasurable (fun ω j => Z j ω) μ :=
    aemeasurable_pi_lambda _ (fun j => (hZ j).aemeasurable)
  have hm := Axioms.external_gaussian_moments μ d Z hZ hInd
  have hid : ProbabilityTheory.IdentDistrib (fun ω j => Z j ω)
      (fun ω j => -Z j ω) μ μ := ⟨hz, hz.neg, hm.2.2.2.1⟩
  have hp := hid.comp (show Measurable (fun z : Fin d → ℝ =>
      (∑ j, x j * z j, φ z)) by fun_prop)
  have hsym : ProbabilityTheory.IdentDistrib
      (fun ω => (∑ j, x j * Z j ω, φ (fun j => Z j ω)))
      (fun ω => (-(∑ j, x j * Z j ω), φ (fun j => Z j ω))) μ μ := by
    have heven' : ∀ z, φ (fun j => -z j) = φ z := heven
    simpa only [Function.comp_def, mul_neg, Finset.sum_neg_distrib, heven'] using hp
  apply halfspace_even_integral μ _ _ (by fun_prop) hint _ hsym
  have hn := hm.2.2.1 x hx 0
  simpa only [MeasureTheory.ae_iff, not_not] using hn

lemma gaussian_random_dot_ne_zero {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (d : ℕ) (Z : Fin d → Ω → ℝ)
    (hZ : ∀ j, ProbabilityTheory.HasLaw (Z j) (ProbabilityTheory.gaussianReal 0 1) μ)
    (hInd : ProbabilityTheory.iIndepFun Z μ)
    (X : Ω → Fin d → ℝ) (hX : AEMeasurable X μ)
    (hXZ : ProbabilityTheory.IndepFun X (fun ω j => Z j ω) μ)
    (hXne : ∀ᵐ ω ∂μ, X ω ≠ 0) :
    ∀ᵐ ω ∂μ, (∑ j, X ω j * Z j ω) ≠ 0 := by
  have hz : AEMeasurable (fun ω j => Z j ω) μ :=
    aemeasurable_pi_lambda _ (fun j => (hZ j).aemeasurable)
  have hzero := (Axioms.external_gaussian_moments μ d Z hZ hInd).2.2.1
  have hxm : ∀ᵐ x ∂(μ.map X), x ≠ 0 :=
    (MeasureTheory.ae_map_iff hX (by measurability)).mpr hXne
  have hprod : ∀ᵐ p : (Fin d → ℝ) × (Fin d → ℝ)
      ∂((μ.map X).prod (μ.map (fun ω j => Z j ω))), (∑ j, p.1 j * p.2 j) ≠ 0 := by
    apply (MeasureTheory.Measure.ae_prod_iff_ae_ae (by measurability)).mpr
    filter_upwards [hxm] with x hx
    apply (MeasureTheory.ae_map_iff hz (by measurability)).mpr
    simpa only [MeasureTheory.ae_iff, not_not] using hzero x hx 0
  rw [← (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map hX hz).mp hXZ] at hprod
  exact (MeasureTheory.ae_map_iff (hX.prodMk hz) (by measurability)).mp hprod

lemma integral_abs_le_sqrt_square {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (f : Ω → ℝ) (hf : MeasureTheory.Integrable f μ)
    (hf2 : MeasureTheory.Integrable (fun ω => f ω ^ 2) μ) :
    (∫ ω, |f ω| ∂μ) ≤ Real.sqrt (∫ ω, f ω ^ 2 ∂μ) := by
  let m := ∫ ω, |f ω| ∂μ
  have hsq : (∫ ω, (|f ω| - m) ^ 2 ∂μ) =
      (∫ ω, f ω ^ 2 ∂μ) - m ^ 2 := by
    have hid : (fun ω => (|f ω| - m) ^ 2) =
        (fun ω => f ω ^ 2 - 2 * m * |f ω| + m ^ 2) := by
      funext ω
      nlinarith [sq_abs (f ω)]
    rw [hid]
    erw [MeasureTheory.integral_add (hf2.sub (hf.abs.const_mul (2*m)))
      (MeasureTheory.integrable_const (m^2)),
      MeasureTheory.integral_sub hf2 (hf.abs.const_mul (2*m)),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const]
    simp only [MeasureTheory.probReal_univ, smul_eq_mul, one_mul]
    dsimp only [m]
    ring
  have hnonneg : 0 ≤ ∫ ω, (|f ω| - m)^2 ∂μ :=
    MeasureTheory.integral_nonneg (fun ω => sq_nonneg (|f ω| - m))
  rw [hsq] at hnonneg
  have hsecond : 0 ≤ ∫ ω, f ω ^ 2 ∂μ :=
    MeasureTheory.integral_nonneg (fun ω => sq_nonneg (f ω))
  have hr := Real.sq_sqrt hsecond
  have hrpos := Real.sqrt_nonneg (∫ ω, f ω ^ 2 ∂μ)
  change m ≤ _
  nlinarith

lemma sqrt_expectation_deviation {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (U : Ω → ℝ) (a : ℝ) (ha : 0 < a)
    (hU : MeasureTheory.Integrable U μ)
    (hU0 : ∀ᵐ ω ∂μ, 0 ≤ U ω)
    (hU2 : MeasureTheory.Integrable (fun ω => (U ω - a) ^ 2) μ) :
    |(∫ ω, Real.sqrt (U ω) ∂μ) - Real.sqrt a| ≤
      Real.sqrt (∫ ω, (U ω - a) ^ 2 ∂μ) / Real.sqrt a := by
  have hdev := hU.sub (MeasureTheory.integrable_const a)
  have hbound := hdev.abs.div_const (Real.sqrt a)
  have hpoint : ∀ᵐ ω ∂μ, |Real.sqrt (U ω) - Real.sqrt a| ≤
      |U ω - a| / Real.sqrt a := hU0.mono (fun ω hω => sqrt_deviation_bound _ _ hω ha)
  have hdiff : MeasureTheory.Integrable (fun ω => Real.sqrt (U ω) - Real.sqrt a) μ := by
    apply hbound.mono' (by fun_prop)
    simpa only [Real.norm_eq_abs] using hpoint
  have hsqrt : MeasureTheory.Integrable (fun ω => Real.sqrt (U ω)) μ := by
    convert hdiff.add (MeasureTheory.integrable_const (Real.sqrt a)) using 1
    ext ω
    simp only [Pi.add_apply, sub_add_cancel]
  have habs : |(∫ ω, Real.sqrt (U ω) ∂μ) - Real.sqrt a| ≤
      ∫ ω, |Real.sqrt (U ω) - Real.sqrt a| ∂μ := by
    have h := MeasureTheory.norm_integral_le_integral_norm
      (fun ω => Real.sqrt (U ω) - Real.sqrt a) (μ := μ)
    simpa only [Real.norm_eq_abs, MeasureTheory.integral_sub hsqrt
      (MeasureTheory.integrable_const _), MeasureTheory.integral_const,
      MeasureTheory.probReal_univ, smul_eq_mul, one_mul] using h
  calc
    _ ≤ ∫ ω, |Real.sqrt (U ω) - Real.sqrt a| ∂μ := habs
    _ ≤ ∫ ω, |U ω - a| / Real.sqrt a ∂μ :=
      MeasureTheory.integral_mono_ae hdiff.abs hbound hpoint
    _ = (∫ ω, |U ω - a| ∂μ) / Real.sqrt a := by simp only [div_eq_mul_inv, MeasureTheory.integral_mul_const]
    _ ≤ _ := div_le_div_of_nonneg_right
      (integral_abs_le_sqrt_square μ _ hdev hU2) (Real.sqrt_nonneg _)

lemma relu_row_on_small_box {d : ℕ} (a x e z : Fin d → ℝ)
    (hz : ∀ j, x j - e j ≤ z j ∧ z j ≤ x j + e j)
    (hm : (∑ j, |a j| * e j) < |∑ j, a j * x j|) :
    max 0 (∑ j, a j * z j) =
      ∑ j, ((if 0 < ∑ j, a j * x j then 1 else 0) * a j) * z j := by
  classical
  have hb := Lemma_Bp1.Machinery.row_bounds
    a x e z hz
  by_cases h : 0 < ∑ j, a j * x j
  · rw [abs_of_pos h] at hm
    simp only [if_pos h, one_mul]
    exact max_eq_right (by linarith)
  · rw [abs_of_nonpos (le_of_not_gt h)] at hm
    simp only [if_neg h, zero_mul, Finset.sum_const_zero]
    exact max_eq_left (by linarith)

lemma box_endpoints_congr {d m : ℕ} (x e : Fin d → ℝ)
    (f g : (Fin d → ℝ) → Fin m → ℝ)
    (hfg : ∀ z, (∀ j, x j - e j ≤ z j ∧ z j ≤ x j + e j) → f z = g z) :
    (Definition.boxes x e f).2.1 = (Definition.boxes x e g).2.1 := by
  apply Prod.ext <;> funext i
  · change sInf _ = sInf _
    congr 1
    exact Set.image_congr (fun z hz => congrFun (hfg z hz) i)
  · change sSup _ = sSup _
    congr 1
    exact Set.image_congr (fun z hz => congrFun (hfg z hz) i)

lemma relu_box_endpoints {d m : ℕ} (A : Matrix (Fin m) (Fin d) ℝ)
    (x e : Fin d → ℝ)
    (hm : ∀ i, (∑ j, |A i j| * e j) < |A.mulVec x i|) :
    (Definition.boxes x e (fun z i => max 0 (A.mulVec z i))).2.1 =
      (Definition.boxes x e (fun z =>
        Matrix.mulVec (fun i j => (if 0 < A.mulVec x i then 1 else 0) * A i j) z)).2.1 := by
  apply box_endpoints_congr
  intro z hz
  funext i
  exact relu_row_on_small_box (A i) x e z hz (hm i)

lemma linear_box_endpoints {d m : ℕ} (A : Matrix (Fin m) (Fin d) ℝ)
    (x e : Fin d → ℝ) (he : ∀ j, 0 ≤ e j) :
    (Definition.boxes x e (fun z => A.mulVec z)).2.1 =
      (A.mulVec x - (A.map abs).mulVec e, A.mulVec x + (A.map abs).mulVec e) := by
  apply Prod.ext <;> funext i
  · exact (Lemma_Bp1.Machinery.row_extrema
      (A i) x e he).1
  · exact (Lemma_Bp1.Machinery.row_extrema
      (A i) x e he).2

lemma relu_geometric_radii {d n m : ℕ}
    (A : Matrix (Fin n) (Fin d) ℝ) (B : Matrix (Fin m) (Fin n) ℝ)
    (x e : Fin d → ℝ) (he : ∀ j, 0 ≤ e j)
    (hm : ∀ i, (∑ j, |A i j| * e j) < |A.mulVec x i|) :
    let C : Matrix (Fin n) (Fin d) ℝ :=
      fun i j => (if 0 < A.mulVec x i then 1 else 0) * A i j
    let p := (Definition.boxes x e (fun z i => max 0 (A.mulVec z i))).2.1
    let q := (Definition.boxes (fun i => (p.2 i + p.1 i) / 2)
      (fun i => (p.2 i - p.1 i) / 2) (fun z => B.mulVec z)).2.1
    ((Definition.boxes x e (fun z => B.mulVec (fun i => max 0 (A.mulVec z i)))).2.2.1.2,
      (q.2 - q.1) / 2) =
      ((B * C).map abs |>.mulVec e, (B.map abs).mulVec ((C.map abs).mulVec e)) := by
  classical
  dsimp only
  let C : Matrix (Fin n) (Fin d) ℝ :=
    fun i j => (if 0 < A.mulVec x i then 1 else 0) * A i j
  have hp := (relu_box_endpoints A x e hm).trans (linear_box_endpoints C x e he)
  have hcenter : (fun i => ((C.mulVec x + (C.map abs).mulVec e) i +
      (C.mulVec x - (C.map abs).mulVec e) i) / 2) = C.mulVec x := by
    funext i
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hradius : (fun i => ((C.mulVec x + (C.map abs).mulVec e) i -
      (C.mulVec x - (C.map abs).mulVec e) i) / 2) = (C.map abs).mulVec e := by
    funext i
    simp only [Pi.add_apply, Pi.sub_apply]
    ring
  have hrpos : ∀ i, 0 ≤ (C.map abs).mulVec e i := by
    intro i
    change 0 ≤ ∑ j, |C i j| * e j
    exact Finset.sum_nonneg (fun j _ => mul_nonneg (abs_nonneg _) (he j))
  have hq := linear_box_endpoints B (C.mulVec x) ((C.map abs).mulVec e) hrpos
  have hopt := box_endpoints_congr x e
    (fun z => B.mulVec (fun i => max 0 (A.mulVec z i)))
    (fun z => (B * C).mulVec z) (by
      intro z hz
      change B.mulVec (fun i => max 0 (A.mulVec z i)) = (B * C).mulVec z
      rw [← Matrix.mulVec_mulVec]
      congr 1
      funext i
      exact relu_row_on_small_box (A i) x e z hz (hm i))
  have ho := hopt.trans (linear_box_endpoints (B * C) x e he)
  apply Prod.ext
  · change ((boxes.hi(Definition.boxes x e _) - boxes.lo(Definition.boxes x e _)) / 2) = _
    rw [ho]
    funext i
    simp only [Pi.div_apply, Pi.sub_apply, Pi.add_apply, Pi.ofNat_apply]
    ring
  · rw [hp, hcenter, hradius, hq]
    funext i
    simp only [Pi.div_apply, Pi.sub_apply, Pi.add_apply, Pi.ofNat_apply]
    ring

lemma relu_radius_functions_eq (d : Fin 3 → ℕ)
    (W : ∀ k : Fin 2, Matrix (Fin (d k.succ)) (Fin (d k.castSucc)) ℝ)
    (x : Fin (d 0) → ℝ) (ε : ℝ) (hε : 0 ≤ ε)
    (hm : ∀ i, (∑ j, |W 0 i j| * ε) < |(W 0).mulVec x i|) :
    let C : Matrix (Fin (d 1)) (Fin (d 0)) ℝ :=
      fun i j => (if 0 < (W 0).mulVec x i then 1 else 0) * W 0 i j
    let B : Matrix (Fin (d 2)) (Fin (d 1)) ℝ := W 1
    relu_local_radii.radii(Definition.relu_local_radii 2 d W (fun _ => 0) x) ε =
      (((B * C).map abs).mulVec (fun _ => ε),
        (B.map abs).mulVec ((C.map abs).mulVec (fun _ => ε))) := by
  have hc : (fun i : Fin (d 0) => ((x i + ε) + (x i - ε)) / 2) = x := by
    funext i
    ring
  have hr : (fun i : Fin (d 0) => ((x i + ε) - (x i - ε)) / 2) = (fun _ => ε) := by
    funext i
    ring
  have h := relu_geometric_radii (W 0) (W 1) x (fun _ => ε) (fun _ => hε) hm
  let f₀ := fun z : Fin (d 0) → ℝ => fun i => max 0 ((W 0).mulVec z i + 0)
  let f₁ := fun z : Fin (d 1) → ℝ => fun i => (W 1).mulVec z i + 0
  let p := (Definition.boxes (fun i => ((x i + ε) + (x i - ε)) / 2)
    (fun i => ((x i + ε) - (x i - ε)) / 2) f₀).2.1
  let q := (Definition.boxes (fun i => (p.2 i + p.1 i) / 2)
    (fun i => (p.2 i - p.1 i) / 2) f₁).2.1
  change ((Definition.boxes x (fun _ => ε) (fun z => f₁ (f₀ z))).2.2.1.2,
    (q.2 - q.1) / 2) = _
  simpa [q, p, f₀, f₁, hc, hr] using h

lemma relu_local_rates (d : Fin 3 → ℕ)
    (W : ∀ k : Fin 2, Matrix (Fin (d k.succ)) (Fin (d k.castSucc)) ℝ)
    (x : Fin (d 0) → ℝ) (hne : ∀ i, (W 0).mulVec x i ≠ 0) :
    let C : Matrix (Fin (d 1)) (Fin (d 0)) ℝ :=
      fun i j => (if 0 < (W 0).mulVec x i then 1 else 0) * W 0 i j
    let B : Matrix (Fin (d 2)) (Fin (d 1)) ℝ := W 1
    (Definition.relu_local_radii 2 d W (fun _ => 0) x).2.2.2.1 =
      (((B * C).map abs).mulVec (fun _ => 1),
        (B.map abs).mulVec ((C.map abs).mulVec (fun _ => 1))) := by
  classical
  let C : Matrix (Fin (d 1)) (Fin (d 0)) ℝ :=
    fun i j => (if 0 < (W 0).mulVec x i then 1 else 0) * W 0 i j
  let B : Matrix (Fin (d 2)) (Fin (d 1)) ℝ := W 1
  let r := ((B * C).map abs).mulVec (fun _ => 1)
  let s := (B.map abs).mulVec ((C.map abs).mulVec (fun _ => 1))
  let f := relu_local_radii.radii(Definition.relu_local_radii 2 d W (fun _ => 0) x)
  have hmargin : ∀ᶠ ε : ℝ in nhds 0,
      ∀ i, (∑ j, |W 0 i j| * ε) < |(W 0).mulVec x i| := by
    apply Filter.eventually_all.2
    intro i
    have ht : Filter.Tendsto (fun ε : ℝ => ∑ j, |W 0 i j| * ε) (nhds 0) (nhds 0) := by
      simpa only [ContinuousAt, mul_zero, Finset.sum_const_zero] using
        (show Continuous (fun ε : ℝ => ∑ j, |W 0 i j| * ε) by fun_prop).continuousAt (x := 0)
    exact ht.eventually_lt_const (abs_pos.mpr (hne i))
  have hcalc (ε : ℝ) (hε : 0 ≤ ε)
      (hm : ∀ i, (∑ j, |W 0 i j| * ε) < |(W 0).mulVec x i|) :
      f ε = (fun i => ε * r i, fun i => ε * s i) := by
    have h := relu_radius_functions_eq d W x ε hε hm
    change f ε = _ at h
    rw [h]
    apply Prod.ext <;> funext i
    · change (∑ j, |(B * C) i j| * ε) = ε * (∑ j, |(B * C) i j| * 1)
      simp only [mul_one, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring
    · change (∑ k, |B i k| * ∑ j, |C k j| * ε) =
        ε * (∑ k, |B i k| * ∑ j, |C k j| * 1)
      simp only [mul_one, Finset.mul_sum, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro k _
      apply Finset.sum_congr rfl
      intro j _
      ring
  have hzero := hcalc 0 le_rfl (by simpa using fun i => abs_pos.mpr (hne i))
  have heq : ∀ᶠ ε in nhdsWithin 0 (Set.Ioi 0),
      f ε = (fun i => ε * r i, fun i => ε * s i) := by
    filter_upwards [hmargin.filter_mono nhdsWithin_le_nhds,
      self_mem_nhdsWithin] with ε hm hε
    exact hcalc ε (le_of_lt hε) hm
  have hd (g : ℝ → ℝ) (c : ℝ)
      (hg : g =ᶠ[nhdsWithin 0 (Set.Ioi 0)] (fun ε => ε * c)) (hg0 : g 0 = 0 * c) :
      derivWithin g (Set.Ioi 0) 0 = c := by
    have hder : HasDerivWithinAt (fun ε : ℝ => ε * c) c (Set.Ioi 0) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const c).hasDerivWithinAt
    exact (hder.congr_of_eventuallyEq hg hg0).derivWithin (uniqueDiffWithinAt_Ioi 0)
  apply Prod.ext <;> funext i
  · exact hd (fun ε => (f ε).1 i) (r i)
      (heq.mono (fun ε h => congrFun (congrArg Prod.fst h) i))
      (congrFun (congrArg Prod.fst hzero) i)
  · exact hd (fun ε => (f ε).2 i) (s i)
      (heq.mono (fun ε h => congrFun (congrArg Prod.snd h) i))
      (congrFun (congrArg Prod.snd hzero) i)

lemma gaussian_random_row_even_half {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (d : ℕ) (Z : Fin d → Ω → ℝ)
    (hZ : ∀ j, ProbabilityTheory.HasLaw (Z j) (ProbabilityTheory.gaussianReal 0 1) μ)
    (hInd : ProbabilityTheory.iIndepFun Z μ)
    (X : Ω → Fin d → ℝ) (hX : AEMeasurable X μ)
    (hXZ : ProbabilityTheory.IndepFun X (fun ω j => Z j ω) μ)
    (hXne : ∀ᵐ ω ∂μ, X ω ≠ 0)
    (φ : (Fin d → ℝ) → ℝ) (hφ : Measurable φ)
    (heven : ∀ z, φ (-z) = φ z)
    (hint : MeasureTheory.Integrable (fun ω => φ (fun j => Z j ω)) μ) :
    (∫ ω, if 0 < ∑ j, X ω j * Z j ω then φ (fun j => Z j ω) else 0 ∂μ) =
      (∫ ω, φ (fun j => Z j ω) ∂μ) / 2 := by
  have hz : AEMeasurable (fun ω j => Z j ω) μ :=
    aemeasurable_pi_lambda _ (fun j => (hZ j).aemeasurable)
  have hm := Axioms.external_gaussian_moments μ d Z hZ hInd
  have hid : ProbabilityTheory.IdentDistrib (fun ω j => Z j ω)
      (fun ω j => -Z j ω) μ μ := ⟨hz, hz.neg, hm.2.2.2.1⟩
  have hp := ((ProbabilityTheory.IdentDistrib.refl hX).prodMk hid hXZ hXZ.neg_right).comp
    (show Measurable (fun p : (Fin d → ℝ) × (Fin d → ℝ) =>
      (∑ j, p.1 j * p.2 j, φ p.2)) by fun_prop)
  have hsym : ProbabilityTheory.IdentDistrib
      (fun ω => (∑ j, X ω j * Z j ω, φ (fun j => Z j ω)))
      (fun ω => (-(∑ j, X ω j * Z j ω), φ (fun j => Z j ω))) μ μ := by
    have heven' : ∀ z, φ (fun j => -z j) = φ z := heven
    simpa only [Function.comp_def, mul_neg, Finset.sum_neg_distrib, heven'] using hp
  exact halfspace_even_integral μ _ _ (by fun_prop) hint
    (gaussian_random_dot_ne_zero μ d Z hZ hInd X hX hXZ hXne) hsym

lemma gated_gaussian_path_mean {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (d : ℕ) (Z : Fin d → Ω → ℝ) (Y : Ω → ℝ)
    (hZ : ∀ j, ProbabilityTheory.HasLaw (Z j) (ProbabilityTheory.gaussianReal 0 1) μ)
    (hY : ProbabilityTheory.HasLaw Y (ProbabilityTheory.gaussianReal 0 1) μ)
    (hInd : ProbabilityTheory.iIndepFun Z μ)
    (hYZ : ProbabilityTheory.IndepFun Y (fun ω j => Z j ω) μ)
    (x : Fin d → ℝ) (hx : x ≠ 0) (j : Fin d) :
    MeasureTheory.Integrable
      (fun ω => |Y ω| * (if 0 < ∑ k, x k * Z k ω then |Z j ω| else 0)) μ ∧
    (∫ ω, |Y ω| * (if 0 < ∑ k, x k * Z k ω then |Z j ω| else 0) ∂μ) =
      1 / Real.pi := by
  have hm := (Axioms.external_gaussian_moments μ d Z hZ hInd).1 j
  have hy := (Axioms.external_gaussian_moments μ 1 (fun _ => Y) (fun _ => hY)
    ProbabilityTheory.iIndepFun.of_subsingleton).1 0
  have hg : MeasureTheory.Integrable
      (fun ω => if 0 < ∑ k, x k * Z k ω then |Z j ω| else 0) μ :=
    hm.1.indicator₀ (show MeasureTheory.NullMeasurableSet
      {ω | 0 < ∑ k, x k * Z k ω} μ from
      nullMeasurableSet_lt aemeasurable_const (by fun_prop))
  have hi := hYZ.comp measurable_abs (show Measurable
    (fun z : Fin d → ℝ => if 0 < ∑ k, x k * z k then |z j| else 0) from
      ((measurable_pi_apply j).abs.ite
        (measurableSet_lt measurable_const (by fun_prop)) measurable_const))
  simp only [Function.comp_def] at hi
  have hmean := gaussian_row_even_half μ d Z hZ hInd x hx (fun z => |z j|)
    (by fun_prop) (by intro z; exact abs_neg _) hm.1
  refine ⟨hi.integrable_mul hy.1 hg, ?_⟩
  erw [hi.integral_fun_mul_eq_mul_integral hy.1.aestronglyMeasurable hg.aestronglyMeasurable,
    hmean, hy.2.2.2.1, hm.2.2.2.1]
  have hs := Real.sq_sqrt (show 0 ≤ 2 / Real.pi by positivity)
  have hfrac : 2 / Real.pi = 2 * (1 / Real.pi) := by ring
  nlinarith only [hs, hfrac]

lemma random_gated_gaussian_path_mean {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (d : ℕ) (Z : Fin d → Ω → ℝ) (Y : Ω → ℝ)
    (hZ : ∀ j, ProbabilityTheory.HasLaw (Z j) (ProbabilityTheory.gaussianReal 0 1) μ)
    (hY : ProbabilityTheory.HasLaw Y (ProbabilityTheory.gaussianReal 0 1) μ)
    (hInd : ProbabilityTheory.iIndepFun Z μ)
    (hYZ : ProbabilityTheory.IndepFun Y (fun ω j => Z j ω) μ)
    (X : Ω → Fin d → ℝ) (hX : AEMeasurable X μ)
    (hXjoint : ProbabilityTheory.IndepFun X (fun ω => (Y ω, fun j => Z j ω)) μ)
    (hXne : ∀ᵐ ω ∂μ, X ω ≠ 0) (j : Fin d) :
    MeasureTheory.Integrable
      (fun ω => if 0 < ∑ k, X ω k * Z k ω then |Y ω| * |Z j ω| else 0) μ ∧
    (∫ ω, if 0 < ∑ k, X ω k * Z k ω then |Y ω| * |Z j ω| else 0 ∂μ) =
      1 / Real.pi := by
  have hz : AEMeasurable (fun ω j => Z j ω) μ :=
    aemeasurable_pi_lambda _ (fun j => (hZ j).aemeasurable)
  have hm := Axioms.external_gaussian_moments μ d Z hZ hInd
  have hy := (Axioms.external_gaussian_moments μ 1 (fun _ => Y) (fun _ => hY)
    ProbabilityTheory.iIndepFun.of_subsingleton).1 0
  have hid : ProbabilityTheory.IdentDistrib (fun ω j => Z j ω)
      (fun ω j => -Z j ω) μ μ := ⟨hz, hz.neg, hm.2.2.2.1⟩
  have hp := (ProbabilityTheory.IdentDistrib.refl hY.aemeasurable).prodMk hid hYZ hYZ.neg_right
  have hpX := (ProbabilityTheory.IdentDistrib.refl hX).prodMk hp hXjoint
    (hXjoint.comp measurable_id (show Measurable (fun p : ℝ × (Fin d → ℝ) =>
      (p.1, -p.2)) by fun_prop))
  have hsign := hpX.comp (show Measurable
    (fun p : (Fin d → ℝ) × (ℝ × (Fin d → ℝ)) =>
      (∑ k, p.1 k * p.2.2 k, |p.2.1| * |p.2.2 j|)) by fun_prop)
  simp only [Function.comp_def, Pi.neg_apply, mul_neg, Finset.sum_neg_distrib, abs_neg] at hsign
  have hi := hYZ.comp measurable_abs (show Measurable (fun z : Fin d → ℝ => |z j|) by fun_prop)
  simp only [Function.comp_def] at hi
  have hv := hi.integrable_mul hy.1 (hm.1 j).1
  have hdot : AEMeasurable (fun ω => ∑ k, X ω k * Z k ω) μ := by fun_prop
  have hXZ := hXjoint.comp measurable_id measurable_snd
  have hne := gaussian_random_dot_ne_zero μ d Z hZ hInd X hX hXZ hXne
  have hg := hv.indicator₀ (nullMeasurableSet_lt
    (show AEMeasurable (fun _ : Ω => (0 : ℝ)) μ from aemeasurable_const) hdot)
  refine ⟨hg, ?_⟩
  erw [halfspace_even_integral μ _ _ hdot hv hne hsign]
  erw [hi.integral_fun_mul_eq_mul_integral hy.1.aestronglyMeasurable (hm.1 j).1.aestronglyMeasurable,
    hy.2.2.2.1, (hm.1 j).2.2.2.1]
  have hs := Real.sq_sqrt (show 0 ≤ 2 / Real.pi by positivity)
  have hfrac : 2 / Real.pi = 2 * (1 / Real.pi) := by ring
  nlinarith only [hs, hfrac]

lemma independent_normal_linear_mean {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (n : ℕ) (A Z : Fin n → Ω → ℝ)
    (hA : ∀ j, MeasureTheory.Integrable (A j) μ)
    (hZ : ∀ j, ProbabilityTheory.HasLaw (Z j) (ProbabilityTheory.gaussianReal 0 1) μ)
    (hInd : ProbabilityTheory.iIndepFun Z μ)
    (hAZ : ProbabilityTheory.IndepFun (fun ω j => A j ω) (fun ω j => Z j ω) μ) :
    MeasureTheory.Integrable (fun ω => |∑ j, A j ω * Z j ω|) μ ∧
    (∫ ω, |∑ j, A j ω * Z j ω| ∂μ) =
      (∫ ω, Real.sqrt (∑ j, A j ω ^ 2) ∂μ) * Real.sqrt (2 / Real.pi) := by
  have hm := Axioms.external_gaussian_moments μ n Z hZ hInd
  have hcopy :=
    Lemma_3p7.Machinery.independent_pair_copy
      μ (fun ω j => A j ω) (fun ω j => Z j ω)
      (aemeasurable_pi_lambda _ (fun j => (hA j).aemeasurable))
      (aemeasurable_pi_lambda _ (fun j => (hZ j).aemeasurable)) hAZ
  have hdot := hcopy.comp (show Measurable
    (fun p : (Fin n → ℝ) × (Fin n → ℝ) => |∑ j, p.1 j * p.2 j|) by fun_prop)
  have hzint (j : Fin n) : MeasureTheory.Integrable (Z j) μ := by
    apply (MeasureTheory.integrable_norm_iff (hZ j).aemeasurable.aestronglyMeasurable).mp
    simpa only [Real.norm_eq_abs] using (hm.1 j).1
  have hp : MeasureTheory.Integrable
      (fun ω : Ω × Ω => |∑ j, A j ω.1 * Z j ω.2|) (μ.prod μ) :=
    (MeasureTheory.integrable_finset_sum Finset.univ
      (fun j _ => (hA j).mul_prod (hzint j))).abs
  refine ⟨hdot.integrable_iff.mpr hp, ?_⟩
  calc
    _ = ∫ ω : Ω × Ω, |∑ j, A j ω.1 * Z j ω.2| ∂(μ.prod μ) := hdot.integral_eq
    _ = ∫ ω, ∫ η, |∑ j, A j ω * Z j η| ∂μ ∂μ := MeasureTheory.integral_prod _ hp
    _ = ∫ ω, Real.sqrt (∑ j, A j ω ^ 2) * Real.sqrt (2 / Real.pi) ∂μ := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall (fun ω =>
        (Lemma_3p7.Machinery.linear_abs_moment
          μ n Z hZ hInd (fun j => A j ω)).2)
    _ = _ := MeasureTheory.integral_mul_const _ _

lemma independent_square_root_average_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (n : ℕ) (hn : 0 < n) (Y : Fin n → Ω → ℝ) (a b : ℝ) (ha : 0 < a)
    (hY : ∀ k, MeasureTheory.Integrable (Y k) μ)
    (hY2 : ∀ k, MeasureTheory.Integrable (fun ω => Y k ω ^ 2) μ)
    (hpos : ∀ k, ∀ᵐ ω ∂μ, 0 ≤ Y k ω)
    (hmean : ∀ k, (∫ ω, Y k ω ∂μ) = a)
    (hsecond : ∀ k, (∫ ω, Y k ω ^ 2 ∂μ) = b)
    (hind : Pairwise (fun k l => ProbabilityTheory.IndepFun (Y k) (Y l) μ)) :
    |(∫ ω, Real.sqrt ((∑ k, Y k ω) / (n : ℝ)) ∂μ) - Real.sqrt a| ≤
      Real.sqrt ((b - a ^ 2) / (n : ℝ)) / Real.sqrt a := by
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hlp k := (MeasureTheory.memLp_two_iff_integrable_sq (hY k).aestronglyMeasurable).mpr (hY2 k)
  have hsum := MeasureTheory.integrable_finset_sum Finset.univ (fun k _ => hY k)
  have hlpsum := MeasureTheory.memLp_finset_sum Finset.univ (fun k _ => hlp k)
  let U := fun ω => (∑ k, Y k ω) / (n : ℝ)
  have hu : MeasureTheory.Integrable U μ := hsum.div_const _
  have hmeanU : (∫ ω, U ω ∂μ) = a := by
    dsimp [U]
    rw [MeasureTheory.integral_div,
      MeasureTheory.integral_finset_sum Finset.univ (fun k _ => hY k)]
    simp [hmean, hn0]
  have hv k : ProbabilityTheory.variance (Y k) μ = b - a ^ 2 := by
    rw [ProbabilityTheory.variance_eq_sub (hlp k)]
    change (∫ ω, Y k ω ^ 2 ∂μ) - (∫ ω, Y k ω ∂μ) ^ 2 = _
    rw [hsecond, hmean]
  have hvs := ProbabilityTheory.IndepFun.variance_sum
    (fun k (_ : k ∈ Finset.univ) => hlp k)
    (fun k _ l _ hkl => hind hkl)
  have hvU : ProbabilityTheory.variance U μ = (b - a ^ 2) / (n : ℝ) := by
    dsimp [U]
    simp only [div_eq_mul_inv, ProbabilityTheory.variance_mul_const]
    have hs : ProbabilityTheory.variance (fun ω => ∑ k, Y k ω) μ =
        (n : ℝ) * (b - a ^ 2) := by
      have heq : (∑ k, Y k) = (fun ω => ∑ k, Y k ω) := by
        funext ω
        simp only [Finset.sum_apply]
      rw [heq] at hvs
      simpa [hv, mul_sub] using hvs
    rw [hs]
    field_simp
  have hlpU : MeasureTheory.MemLp U 2 μ := by
    simpa only [U, div_eq_mul_inv, Finset.sum_apply] using hlpsum.mul_const (n : ℝ)⁻¹
  have hcenter := (MeasureTheory.memLp_two_iff_integrable_sq
    (hu.sub (MeasureTheory.integrable_const a)).aestronglyMeasurable).mp
      (hlpU.sub (MeasureTheory.memLp_const a))
  have hb := sqrt_expectation_deviation μ U a ha hu
    (by
      filter_upwards [MeasureTheory.ae_all_iff.mpr hpos] with ω hω
      exact div_nonneg (Finset.sum_nonneg (fun k _ => hω k)) (by positivity)) hcenter
  rw [← hmeanU, ← ProbabilityTheory.variance_eq_integral hu.aemeasurable, hvU] at hb
  simpa only [hmeanU] using hb

lemma gated_square_root_average_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (n d : ℕ) (hn : 0 < n) (Z : Fin n → Fin d → Ω → ℝ)
    (hZ : ∀ k j, ProbabilityTheory.HasLaw (Z k j) (ProbabilityTheory.gaussianReal 0 1) μ)
    (hirow : ∀ k, ProbabilityTheory.iIndepFun (Z k) μ)
    (hrows : Pairwise (fun k l => ProbabilityTheory.IndepFun
      (fun ω j => Z k j ω) (fun ω j => Z l j ω) μ))
    (x : Fin d → ℝ) (hx : x ≠ 0) (j : Fin d) :
    |(∫ ω, Real.sqrt ((∑ k, if 0 < ∑ l, x l * Z k l ω then Z k j ω ^ 2 else 0) /
      (n : ℝ)) ∂μ) - Real.sqrt (1 / 2)| ≤
      Real.sqrt ((5 / 4) / (n : ℝ)) / Real.sqrt (1 / 2) := by
  let Y := fun k ω => if 0 < ∑ l, x l * Z k l ω then Z k j ω ^ 2 else 0
  have hm k := (Axioms.external_gaussian_moments μ d (Z k) (hZ k) (hirow k)).1 j
  have hg k : MeasureTheory.NullMeasurableSet {ω | 0 < ∑ l, x l * Z k l ω} μ :=
    nullMeasurableSet_lt aemeasurable_const (by fun_prop)
  have hY k : MeasureTheory.Integrable (Y k) μ := (hm k).2.1.indicator₀ (hg k)
  have hsquare k : (fun ω => Y k ω ^ 2) =
      (fun ω => if 0 < ∑ l, x l * Z k l ω then Z k j ω ^ 4 else 0) := by
    funext ω
    dsimp [Y]
    split_ifs <;> ring
  have hY2 k : MeasureTheory.Integrable (fun ω => Y k ω ^ 2) μ := by
    rw [hsquare]
    exact (hm k).2.2.1.indicator₀ (hg k)
  have hmean k : (∫ ω, Y k ω ∂μ) = (1 / 2 : ℝ) := by
    have h := gaussian_row_even_half μ d (Z k) (hZ k) (hirow k) x hx
      (fun z => z j ^ 2) (by fun_prop) (by intro z; simp) (hm k).2.1
    simpa only [(hm k).2.2.2.2.1] using h
  have hsecond k : (∫ ω, Y k ω ^ 2 ∂μ) = (3 / 2 : ℝ) := by
    rw [hsquare]
    have h := gaussian_row_even_half μ d (Z k) (hZ k) (hirow k) x hx
      (fun z => z j ^ 4) (by fun_prop) (by intro z; change (-z j)^4 = _; ring) (hm k).2.2.1
    simpa only [(hm k).2.2.2.2.2] using h
  have hmeas : Measurable (fun z : Fin d → ℝ => if 0 < ∑ l, x l * z l then z j ^ 2 else 0) :=
    ((measurable_pi_apply j).pow_const 2).ite
      (measurableSet_lt measurable_const (by fun_prop)) measurable_const
  have hind : Pairwise (fun k l => ProbabilityTheory.IndepFun (Y k) (Y l) μ) :=
    fun k l hkl => (hrows hkl).comp hmeas hmeas
  have h := independent_square_root_average_bound μ n hn Y (1/2) (3/2) (by norm_num)
    hY hY2 (fun k => Filter.Eventually.of_forall (fun ω => by
      dsimp [Y]; split_ifs <;> positivity)) hmean hsecond hind
  norm_num only [show (3/2 : ℝ) - (1/2)^2 = 5/4 by norm_num] at h
  exact h

lemma gaussian_square_root_average_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (n : ℕ) (hn : 0 < n) (Z : Fin n → Ω → ℝ)
    (hZ : ∀ k, ProbabilityTheory.HasLaw (Z k) (ProbabilityTheory.gaussianReal 0 1) μ)
    (hInd : ProbabilityTheory.iIndepFun Z μ) :
    |(∫ ω, Real.sqrt ((∑ k, Z k ω ^ 2) / (n : ℝ)) ∂μ) - 1| ≤
      Real.sqrt (2 / (n : ℝ)) := by
  have hm := (Axioms.external_gaussian_moments μ n Z hZ hInd).1
  have h := independent_square_root_average_bound μ n hn (fun k ω => Z k ω ^ 2)
    1 3 (by norm_num) (fun k => (hm k).2.1)
    (fun k => by simpa only [← pow_mul] using (hm k).2.2.1)
    (fun k => Filter.Eventually.of_forall (fun ω => sq_nonneg _))
    (fun k => (hm k).2.2.2.2.1)
    (fun k => by simpa only [← pow_mul] using (hm k).2.2.2.2.2)
    (fun k l hkl => (hInd.indepFun hkl).comp (measurable_id.pow_const 2) (measurable_id.pow_const 2))
  norm_num at h ⊢
  exact h

lemma gated_normal_sum_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (n d : ℕ) (hn : 0 < n) (Z : Fin n → Fin d → Ω → ℝ) (Y : Fin n → Ω → ℝ)
    (hZ : ∀ k j, ProbabilityTheory.HasLaw (Z k j) (ProbabilityTheory.gaussianReal 0 1) μ)
    (hY : ∀ k, ProbabilityTheory.HasLaw (Y k) (ProbabilityTheory.gaussianReal 0 1) μ)
    (hirow : ∀ k, ProbabilityTheory.iIndepFun (Z k) μ)
    (hiY : ProbabilityTheory.iIndepFun Y μ)
    (hrows : Pairwise (fun k l => ProbabilityTheory.IndepFun
      (fun ω j => Z k j ω) (fun ω j => Z l j ω) μ))
    (hYZ : ProbabilityTheory.IndepFun (fun ω k => Y k ω) (fun ω k j => Z k j ω) μ)
    (x : Fin d → ℝ) (hx : x ≠ 0) (j : Fin d) :
    let F := fun ω => |∑ k, (if 0 < ∑ l, x l * Z k l ω then Z k j ω else 0) * Y k ω|
    MeasureTheory.Integrable F μ ∧
    |(∫ ω, F ω ∂μ) / (Real.sqrt (n : ℝ) * Real.sqrt (2 / Real.pi)) - Real.sqrt (1/2)| ≤
      Real.sqrt ((5/4) / (n : ℝ)) / Real.sqrt (1/2) := by
  let A := fun k ω => if 0 < ∑ l, x l * Z k l ω then Z k j ω else 0
  have hA k : MeasureTheory.Integrable (A k) μ := by
    have hm := (Axioms.external_gaussian_moments μ d (Z k) (hZ k) (hirow k)).1 j
    have hzint : MeasureTheory.Integrable (Z k j) μ := by
      apply (MeasureTheory.integrable_norm_iff (hZ k j).aemeasurable.aestronglyMeasurable).mp
      simpa only [Real.norm_eq_abs] using hm.1
    exact hzint.indicator₀ (show MeasureTheory.NullMeasurableSet {ω | 0 < ∑ l, x l * Z k l ω} μ from
      nullMeasurableSet_lt aemeasurable_const (by fun_prop))
  have hmeas : Measurable (fun z : Fin n → Fin d → ℝ =>
      fun k => if 0 < ∑ l, x l * z k l then z k j else 0) := by
    apply measurable_pi_lambda
    intro k
    exact ((measurable_pi_apply j).comp (measurable_pi_apply k)).ite
      (measurableSet_lt measurable_const (by fun_prop)) measurable_const
  have hm := independent_normal_linear_mean μ n A Y hA hY hiY
    (hYZ.symm.comp hmeas measurable_id)
  refine ⟨hm.1, ?_⟩
  have hb := gated_square_root_average_bound μ n d hn Z hZ hirow hrows x hx j
  have hsquare (ω : Ω) : (∑ k, A k ω ^ 2) =
      ∑ k, if 0 < ∑ l, x l * Z k l ω then Z k j ω ^ 2 else 0 := by
    apply Finset.sum_congr rfl
    intro k _
    dsimp [A]
    split_ifs <;> simp
  simp_rw [← hsquare, Real.sqrt_div' _ (Nat.cast_nonneg n)] at hb
  rw [MeasureTheory.integral_div] at hb
  change |(∫ ω, |∑ k, A k ω * Y k ω| ∂μ) / _ - _| ≤ _
  rw [hm.2]
  have hc : Real.sqrt (2 / Real.pi) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 (by positivity))
  have heq (v : ℝ) : v * Real.sqrt (2 / Real.pi) /
      (Real.sqrt (n : ℝ) * Real.sqrt (2 / Real.pi)) = v / Real.sqrt (n : ℝ) := by
    exact mul_div_mul_right v (Real.sqrt (n : ℝ)) hc
  rw [heq]
  simpa only [Real.sqrt_div' _ (Nat.cast_nonneg n)] using hb

lemma independent_parameter_bound {Ω E F : Type*} [MeasurableSpace Ω]
    [MeasurableSpace E] [MeasurableSpace F]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : Ω → E) (V : Ω → F) (hX : AEMeasurable X μ) (hV : AEMeasurable V μ)
    (hind : ProbabilityTheory.IndepFun X V μ)
    (f : E × F → ℝ) (hf : Measurable f) (G : F → ℝ)
    (hG : MeasureTheory.Integrable (fun ω => G (V ω)) μ)
    (hbound : ∀ x v, |f (x,v)| ≤ G v)
    (P : E → Prop) (hP : ∀ᵐ ω ∂μ, P (X ω)) (c a b : ℝ)
    (hmean : ∀ x, P x → |(∫ ω, f (x,V ω) ∂μ) / c - a| ≤ b) :
    MeasureTheory.Integrable (fun ω => f (X ω,V ω)) μ ∧
      |(∫ ω, f (X ω,V ω) ∂μ) / c - a| ≤ b := by
  have hc :=
    Lemma_3p7.Machinery.independent_pair_copy
      μ X V hX hV hind
  have hid := hc.comp hf
  simp only [Function.comp_def] at hid
  have hg := hG.comp_snd μ
  have hp : MeasureTheory.Integrable (fun p : Ω × Ω => f (X p.1,V p.2)) (μ.prod μ) := by
    apply hg.mono' hid.aemeasurable_snd.aestronglyMeasurable
    exact Filter.Eventually.of_forall (fun p => by
      simpa only [Real.norm_eq_abs] using hbound (X p.1) (V p.2))
  refine ⟨hid.integrable_iff.mpr hp, ?_⟩
  have hinner := hp.integral_prod_left
  have hdiff := (hinner.div_const c).sub (MeasureTheory.integrable_const a)
  have heq : (∫ ω, f (X ω,V ω) ∂μ) / c - a =
      ∫ ω, (∫ η, f (X ω,V η) ∂μ) / c - a ∂μ := by
    erw [hid.integral_eq, MeasureTheory.integral_prod _ hp,
      MeasureTheory.integral_sub (hinner.div_const c) (MeasureTheory.integrable_const a),
      MeasureTheory.integral_div, MeasureTheory.integral_const]
    simp
  rw [heq]
  calc
    _ ≤ ∫ ω, |(∫ η, f (X ω,V η) ∂μ) / c - a| ∂μ := by
      simpa only [Real.norm_eq_abs] using MeasureTheory.norm_integral_le_integral_norm
        (fun ω => (∫ η, f (X ω,V η) ∂μ) / c - a) (μ := μ)
    _ ≤ ∫ _ : Ω, b ∂μ := MeasureTheory.integral_mono_ae hdiff.abs
      (MeasureTheory.integrable_const b) (hP.mono (fun ω hω => hmean _ hω))
    _ = b := by simp

lemma random_gated_normal_sum_bound {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (n d : ℕ) (hn : 0 < n) (Z : Fin n → Fin d → Ω → ℝ) (Y : Fin n → Ω → ℝ)
    (hZ : ∀ k j, ProbabilityTheory.HasLaw (Z k j) (ProbabilityTheory.gaussianReal 0 1) μ)
    (hY : ∀ k, ProbabilityTheory.HasLaw (Y k) (ProbabilityTheory.gaussianReal 0 1) μ)
    (hirow : ∀ k, ProbabilityTheory.iIndepFun (Z k) μ)
    (hiY : ProbabilityTheory.iIndepFun Y μ)
    (hrows : Pairwise (fun k l => ProbabilityTheory.IndepFun
      (fun ω j => Z k j ω) (fun ω j => Z l j ω) μ))
    (hYZ : ProbabilityTheory.IndepFun (fun ω k => Y k ω) (fun ω k j => Z k j ω) μ)
    (X : Ω → Fin d → ℝ) (hX : AEMeasurable X μ)
    (hXW : ProbabilityTheory.IndepFun X (fun ω => ((fun k j => Z k j ω), fun k => Y k ω)) μ)
    (hXne : ∀ᵐ ω ∂μ, X ω ≠ 0) (j : Fin d) :
    let F := fun ω => |∑ k, (if 0 < ∑ l, X ω l * Z k l ω then Z k j ω else 0) * Y k ω|
    MeasureTheory.Integrable F μ ∧
    |(∫ ω, F ω ∂μ) / (Real.sqrt (n : ℝ) * Real.sqrt (2 / Real.pi)) - Real.sqrt (1/2)| ≤
      Real.sqrt ((5/4) / (n : ℝ)) / Real.sqrt (1/2) := by
  let V := fun ω => ((fun k j => Z k j ω), fun k => Y k ω)
  let f := fun p : (Fin d → ℝ) × ((Fin n → Fin d → ℝ) × (Fin n → ℝ)) =>
    |∑ k, (if 0 < ∑ l, p.1 l * p.2.1 k l then p.2.1 k j else 0) * p.2.2 k|
  let G := fun p : (Fin n → Fin d → ℝ) × (Fin n → ℝ) => ∑ k, |p.1 k j| * |p.2 k|
  have hv : AEMeasurable V μ := by
    apply AEMeasurable.prodMk
    · exact aemeasurable_pi_lambda _ (fun k => aemeasurable_pi_lambda _ (fun j => (hZ k j).aemeasurable))
    · exact aemeasurable_pi_lambda _ (fun k => (hY k).aemeasurable)
  have hf : Measurable f := by
    apply Measurable.abs
    apply Finset.measurable_sum
    intro k _
    apply Measurable.mul
    · exact Measurable.ite (measurableSet_lt measurable_const (by fun_prop)) (by fun_prop) measurable_const
    · fun_prop
  have hG : MeasureTheory.Integrable (fun ω => G (V ω)) μ := by
    apply MeasureTheory.integrable_finset_sum Finset.univ
    intro k _
    have hzi := (Axioms.external_gaussian_moments μ d (Z k) (hZ k) (hirow k)).1 j
    have hyi := (Axioms.external_gaussian_moments μ n Y hY hiY).1 k
    have hi := hYZ.symm.comp
      (show Measurable (fun z : Fin n → Fin d → ℝ => |z k j|) by fun_prop)
      (show Measurable (fun y : Fin n → ℝ => |y k|) by fun_prop)
    exact hi.integrable_mul hzi.1 hyi.1
  have hb : ∀ x v, |f (x,v)| ≤ G v := by
    intro x v
    dsimp [f, G]
    rw [abs_abs]
    apply (Finset.abs_sum_le_sum_abs _ _).trans
    apply Finset.sum_le_sum
    intro k _
    split_ifs
    · simp only [abs_mul, le_refl]
    · simp only [zero_mul, abs_zero]
      positivity
  exact independent_parameter_bound μ X V hX hv hXW f hf G hG hb
    (fun x => x ≠ 0) hXne _ _ _
    (fun x hx => (gated_normal_sum_bound μ n d hn Z Y hZ hY hirow hiY hrows hYZ x hx j).2)

lemma finite_average_bound (d : ℕ) (hd : 0 < d) (v : Fin d → ℝ)
    (a b : ℝ) (hv : ∀ j, |v j - a| ≤ b) :
    |(∑ j, v j) / (d : ℝ) - a| ≤ b := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have heq : (∑ j, v j) / (d : ℝ) - a = (∑ j, (v j - a)) / (d : ℝ) := by
    simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    field_simp
  rw [heq, abs_div, abs_of_pos hd']
  apply (div_le_iff₀ hd').mpr
  calc
    |∑ j, (v j - a)| ≤ ∑ j, |v j - a| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin d, b := Finset.sum_le_sum (fun j _ => hv j)
    _ = b * (d : ℝ) := by simp [mul_comm]

lemma radius_ratio_normalization (r n d s g h : ℝ)
    (hn : 0 < n) (hd : 0 < d) (hs : 0 < s) (hg : 0 < g) (hh : 0 < h) :
    (r / (n * d * (s / Real.pi))) /
      (Real.sqrt 2 * (Real.sqrt Real.pi * g / (n * h))) =
      Real.sqrt 2 * (r / (s * (Real.sqrt n * Real.sqrt (2 / Real.pi)) * d)) /
        ((Real.sqrt 2 * g / h) / Real.sqrt n) := by
  rw [Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2)]
  have hp := Real.sqrt_pos.2 Real.pi_pos
  have htwo : 0 < Real.sqrt (2 : ℝ) := by positivity
  have hsqrt := Real.sqrt_pos.2 hn
  field_simp
  rw [Real.sq_sqrt Real.pi_pos.le]

-- formalizer:machinery-end

end Corollary_Ap2.Machinery
