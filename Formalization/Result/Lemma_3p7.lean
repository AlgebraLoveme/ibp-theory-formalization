module
public import Formalization.Result.helpers.Lemma_3p7.Machinery
public import Formalization.Axioms
public import Formalization.Definition
public import Mathlib
public import Formalization.Result.Lemma_Bp1

open Axioms Definition

public section

open scoped BigOperators NNReal
open MeasureTheory ProbabilityTheory Filter
namespace Lemma_3p7

theorem initialization_width {Ω : Type*} [MeasurableSpace Ω]
    (μ : Measure Ω) (d : Fin 3 → ℕ) (σ : Fin 2 → ℝ≥0)
    (W : Ω → ∀ k : Fin 2, Matrix (Fin (d k.succ)) (Fin (d k.castSucc)) ℝ)
    (hinit : (gaussian_initialization μ 2 d σ W (fun _ => 0)).1)
    (x e : Fin (d 0) → ℝ) (he : ∀ j, 0 ≤ e j) (hne : e ≠ 0) :
    let t := fun n : ℕ => Real.sqrt Real.pi * Real.Gamma (((n : ℝ) + 1) / 2) /
      ((n : ℝ) * Real.Gamma ((n : ℝ) / 2))
    let p := fun ω => (linear_network 2 d (W ω)).2.2.2 x e
    let r := fun ω i => ((p ω).1.2 i - (p ω).1.1 i) / 2
    let s := fun ω i => ((p ω).2.2 i - (p ω).2.1 i) / 2
    (∀ i, 0 < ∫ ω, s ω i ∂μ) ∧
    (∀ i, (∫ ω, r ω i ∂μ) / (∫ ω, s ω i ∂μ) = t (d 1)) ∧
    Asymptotics.IsTheta atTop t (fun n : ℕ => (Real.sqrt (n : ℝ))⁻¹) := (by
  -- formalizer:proof-begin
  classical
  dsimp only
  rcases hinit with ⟨hprob, _, hd, hσ, hInd, hLaw⟩
  letI := hprob
  let c := Real.sqrt (2 / Real.pi)
  have hm := fun k i j =>
    Machinery.gaussian_abs_moment
      μ (fun ω => W ω k i j) (σ k) (hσ k) (hLaw ⟨k, i, j⟩)
  -- Lemma B.1 identifies the geometric half-widths with the absolute
  -- composed matrix and the product of the two absolute matrices.
  have hs (ω : Ω) (i : Fin (d 2)) :
      (((linear_network 2 d (W ω)).2.2.2 x e).2.2 i -
        ((linear_network 2 d (W ω)).2.2.2 x e).2.1 i) / 2 =
      ∑ j, (∑ k, |W ω 1 i k| * |W ω 0 k j|) * e j := by
    have h := congrFun (Lemma_Bp1.two_layer_boxes d hd (W ω) x e he).2.2.2 i
    change (((linear_network 2 d (W ω)).2.2.2 x e).2.2 i -
      ((linear_network 2 d (W ω)).2.2.2 x e).2.1 i) / 2 =
      (linear_network 2 d (W ω)).2.2.1.mulVec e i at h
    rw [h]
    let A : Matrix (Fin (d 1)) (Fin (d 0)) ℝ := W ω 0
    let B : Matrix (Fin (d 2)) (Fin (d 1)) ℝ := W ω 1
    change (B.map abs * (A.map abs *
      (1 : Matrix (Fin (d 0)) (Fin (d 0)) ℝ))).mulVec e i = _
    simp only [Matrix.mul_one, Matrix.mulVec, Matrix.mul_apply, Matrix.map_apply,
      dotProduct]
    rfl
  -- Equation (3-1): independence factors each absolute path product;
  -- Gaussian moments justify integration of the finite path sums.
  have hind (i : Fin (d 2)) (k : Fin (d 1)) (j : Fin (d 0)) :
      IndepFun (fun ω => |W ω 1 i k|) (fun ω => |W ω 0 k j|) μ := by
    exact (hInd.indepFun (i := ⟨1, i, k⟩) (j := ⟨0, k, j⟩)
      (by intro h; have hh := congrArg Sigma.fst h; cases hh)).comp
        measurable_abs measurable_abs
  have hint (i : Fin (d 2)) (k : Fin (d 1)) (j : Fin (d 0)) :
      Integrable (fun ω => |W ω 1 i k| * |W ω 0 k j|) μ :=
    (hind i k j).integrable_mul (hm 1 i k).1 (hm 0 k j).1
  have hmean (i : Fin (d 2)) :
      (∫ ω, (((linear_network 2 d (W ω)).2.2.2 x e).2.2 i -
        ((linear_network 2 d (W ω)).2.2.2 x e).2.1 i) / 2 ∂μ) =
      ((σ 1 : ℝ) * c) * ((σ 0 : ℝ) * c) * (d 1 : ℝ) * ∑ j, e j := by
    simp_rw [hs]
    erw [integral_finset_sum Finset.univ (fun j _ => (integrable_finset_sum Finset.univ
      (fun k _ => hint i k j)).mul_const (e j))]
    simp_rw [integral_mul_const]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    erw [integral_finset_sum Finset.univ (fun k _ => hint i k j)]
    simp_rw [(hind i _ j).integral_fun_mul_eq_mul_integral
      (hm 1 i _).1.aestronglyMeasurable (hm 0 _ j).1.aestronglyMeasurable,
      (hm 1 i _).2, (hm 0 _ j).2]
    simp [c, mul_comm, mul_left_comm]
  have hepos : 0 < ∑ j, e j := by
    apply Finset.sum_pos' (fun j _ => he j)
    obtain ⟨j, hj⟩ : ∃ j, e j ≠ 0 := by
      by_contra h
      apply hne
      funext j
      simpa using not_exists.mp h j
    exact ⟨j, Finset.mem_univ _, lt_of_le_of_ne (he j) (Ne.symm hj)⟩
  refine ⟨?_, ?_⟩
  · intro i
    rw [hmean]
    have hc : 0 < c := Real.sqrt_pos.2 (div_pos (by norm_num) Real.pi_pos)
    exact mul_pos (mul_pos (mul_pos (mul_pos (by exact_mod_cast hσ 1) hc)
      (mul_pos (by exact_mod_cast hσ 0) hc)) (by exact_mod_cast hd 1)) hepos
  · refine ⟨?_, ?_⟩
    · intro i
      let Z : (Σ k : Fin 2, Fin (d k.succ) × Fin (d k.castSucc)) → Ω → ℝ :=
        fun p ω => (σ p.1 : ℝ)⁻¹ * W ω p.1 p.2.1 p.2.2
      have hZ p : HasLaw (Z p) (gaussianReal 0 1) μ :=
        Machinery.gaussian_standardized
          μ _ (σ p.1) (hσ p.1) (hLaw p)
      have hiZ : iIndepFun Z μ := hInd.comp
        (fun p z => (σ p.1 : ℝ)⁻¹ * z) (fun _ => by fun_prop)
      have hz (ω : Ω) (k : Fin 2) (a : Fin (d k.succ)) (b : Fin (d k.castSucc)) :
          W ω k a b = (σ k : ℝ) * Z ⟨k, a, b⟩ ω := by
        dsimp [Z]
        field_simp [ne_of_gt (show (0 : ℝ) < σ k by exact_mod_cast hσ k)]
      let M := Real.sqrt 2 * Real.Gamma (((d 1 : ℝ) + 1) / 2) /
        Real.Gamma ((d 1 : ℝ) / 2) * c
      -- For each optimal coefficient, condition on the standardized second
      -- row. The first-layer sum is normal with variance the row's squared
      -- norm. Fubini and the chi mean give equation (3-2).
      have hcoef (j : Fin (d 0)) :
          Integrable (fun ω => |∑ k, W ω 1 i k * W ω 0 k j|) μ ∧
          (∫ ω, |∑ k, W ω 1 i k * W ω 0 k j| ∂μ) =
            (σ 1 : ℝ) * (σ 0 : ℝ) * M := by
        have hiX : iIndepFun (fun k : Fin (d 1) => Z ⟨1, i, k⟩) μ :=
          hiZ.precomp (g := fun k : Fin (d 1) => ⟨1, i, k⟩)
            (by intro a b h; simpa using h)
        have hiY : iIndepFun (fun k : Fin (d 1) => Z ⟨0, k, j⟩) μ :=
          hiZ.precomp (g := fun k : Fin (d 1) => ⟨0, k, j⟩)
            (by intro a b h; simpa using h)
        have hiXY :=
          Machinery.independent_vectors
            μ Z (fun p => (hZ p).aemeasurable) hiZ
            (fun k : Fin (d 1) => ⟨1, i, k⟩) (fun k : Fin (d 1) => ⟨0, k, j⟩)
            (by intro a b h; have hh := congrArg Sigma.fst h; cases hh)
        have hmom :=
          Machinery.normal_dot_abs_mean
            μ (d 1) (hd 1) _ _ (fun k => hZ ⟨1, i, k⟩) (fun k => hZ ⟨0, k, j⟩)
            hiX hiY hiXY
        have hp (ω : Ω) : |∑ k, W ω 1 i k * W ω 0 k j| =
            ((σ 1 : ℝ) * (σ 0 : ℝ)) * |∑ k, Z ⟨1, i, k⟩ ω * Z ⟨0, k, j⟩ ω| := by
          simp_rw [hz]
          have hscl : (∑ k : Fin (d 1), ((σ 1 : ℝ) * Z ⟨1, i, k⟩ ω) *
              ((σ 0 : ℝ) * Z ⟨0, k, j⟩ ω)) =
              ((σ 1 : ℝ) * (σ 0 : ℝ)) * ∑ k, Z ⟨1, i, k⟩ ω * Z ⟨0, k, j⟩ ω := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro k _; ring
          erw [hscl, abs_mul, abs_of_nonneg (mul_nonneg (σ 1).coe_nonneg (σ 0).coe_nonneg)]
        simp_rw [hp]
        exact ⟨hmom.1.const_mul _, by erw [integral_const_mul, hmom.2]⟩
      have hr (ω : Ω) :
          (((linear_network 2 d (W ω)).2.2.2 x e).1.2 i -
            ((linear_network 2 d (W ω)).2.2.2 x e).1.1 i) / 2 =
          ∑ j, |∑ k, W ω 1 i k * W ω 0 k j| * e j := by
        have h := congrFun (Lemma_Bp1.two_layer_boxes d hd (W ω) x e he).2.2.1 i
        change (((linear_network 2 d (W ω)).2.2.2 x e).1.2 i -
          ((linear_network 2 d (W ω)).2.2.2 x e).1.1 i) / 2 =
          (linear_network 2 d (W ω)).2.1.mulVec e i at h
        rw [h]
        let A : Matrix (Fin (d 1)) (Fin (d 0)) ℝ := W ω 0
        let B : Matrix (Fin (d 2)) (Fin (d 1)) ℝ := W ω 1
        change ((B * (A * (1 : Matrix (Fin (d 0)) (Fin (d 0)) ℝ))).map abs).mulVec e i = _
        simp only [Matrix.mul_one, Matrix.mulVec, Matrix.map_apply, Matrix.mul_apply, dotProduct]
        rfl
      -- Integrate the optimal radius's finite sum, then divide (3-2) by
      -- (3-1). This inverts the reciprocal displayed in equation (3-3).
      simp_rw [hr]
      erw [integral_finset_sum Finset.univ (fun j _ => (hcoef j).1.mul_const (e j))]
      simp_rw [integral_mul_const, (hcoef _).2]
      rw [← Finset.mul_sum, hmean]
      have hc : 0 < c := Real.sqrt_pos.2 (div_pos (by norm_num) Real.pi_pos)
      have hs0 : (σ 0 : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hσ 0)
      have hs1 : (σ 1 : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hσ 1)
      have hn1 : (d 1 : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hd 1)
      have hgam : Real.Gamma ((d 1 : ℝ) / 2) ≠ 0 :=
        ne_of_gt ((external_gamma.1 _ (div_pos (by exact_mod_cast hd 1) (by norm_num))).1)
      have hsqrtpi : Real.sqrt Real.pi ≠ 0 := ne_of_gt (Real.sqrt_pos.2 Real.pi_pos)
      have hsqrt2 : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
      have hcsqrt : c = Real.sqrt 2 / Real.sqrt Real.pi := Real.sqrt_div (by norm_num) _
      dsimp only [M]
      rw [hcsqrt]
      field_simp [hs0, hs1, hn1, hgam, ne_of_gt hepos, hsqrtpi, hsqrt2]
    · -- The scalar Gamma-ratio limit at x = n/2 gives the order n^(-1/2).
      have hg := external_gamma.2.2.2.2.2.2 (1 / 2 : ℝ)
      have hn : Tendsto (fun n : ℕ => (n : ℝ) / 2) atTop atTop :=
        (tendsto_div_const_atTop_of_pos (by norm_num : (0 : ℝ) < 2)).mpr
          tendsto_natCast_atTop_atTop
      have hlim := (hg.comp hn).const_mul (Real.sqrt Real.pi / Real.sqrt 2)
      have hneC : Real.sqrt Real.pi / Real.sqrt 2 ≠ 0 :=
        ne_of_gt (div_pos (Real.sqrt_pos.2 Real.pi_pos) (Real.sqrt_pos.2 (by norm_num)))
      apply Asymptotics.IsTheta.symm
      apply Asymptotics.isTheta_of_div_tendsto_nhds_ne_zero (c := Real.sqrt Real.pi / Real.sqrt 2)
      · simp only [mul_one] at hlim
        apply hlim.congr'
        filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hnpos
        have hnR : 0 < (n : ℝ) := by exact_mod_cast hnpos
        have hroot : Real.sqrt (n : ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hnR)
        have hroot2 : Real.sqrt (2 : ℝ) ≠ 0 := by positivity
        have hsq := Real.sq_sqrt hnR.le
        have hsq2 := Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
        dsimp only [Function.comp_def]
        rw [← Real.sqrt_eq_rpow, Real.sqrt_div hnR.le]
        have harg : (n : ℝ) / 2 + 1 / 2 = ((n : ℝ) + 1) / 2 := by ring
        rw [harg]
        field_simp
        nlinarith
      · exact hneC
  -- formalizer:proof-end
)
end Lemma_3p7
