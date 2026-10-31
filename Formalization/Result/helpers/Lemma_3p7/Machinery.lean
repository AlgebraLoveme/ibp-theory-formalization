module
public import Formalization.Axioms
public import Formalization.Definition
public import Formalization.Result.Lemma_Bp1
public import Mathlib

public section

namespace Lemma_3p7.Machinery

-- formalizer:machinery-begin
lemma gaussian_standardized {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : Ω → ℝ) (σ : NNReal) (hσ : 0 < σ)
    (hX : ProbabilityTheory.HasLaw X (ProbabilityTheory.gaussianReal 0 (σ ^ 2)) μ) :
    ProbabilityTheory.HasLaw (fun ω => (σ : ℝ)⁻¹ * X ω)
      (ProbabilityTheory.gaussianReal 0 1) μ := by
  have hs : (σ : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hσ)
  have hZ := ProbabilityTheory.gaussianReal_const_mul hX (σ : ℝ)⁻¹
  change ProbabilityTheory.HasLaw (fun ω => (σ : ℝ)⁻¹ * X ω)
    (ProbabilityTheory.gaussianReal ((σ : ℝ)⁻¹ * 0) (σ⁻¹ ^ 2 * σ ^ 2)) μ at hZ
  have hv : σ⁻¹ ^ 2 * σ ^ 2 = 1 := by
    apply NNReal.coe_injective
    simp only [NNReal.coe_mul, NNReal.coe_inv, NNReal.coe_pow, NNReal.coe_one]
    field_simp [hs]
  rw [mul_zero, hv] at hZ
  exact hZ

lemma gaussian_abs_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : Ω → ℝ) (σ : NNReal) (hσ : 0 < σ)
    (hX : ProbabilityTheory.HasLaw X (ProbabilityTheory.gaussianReal 0 (σ ^ 2)) μ) :
    MeasureTheory.Integrable (fun ω => |X ω|) μ ∧
      (∫ ω, |X ω| ∂μ) = (σ : ℝ) * Real.sqrt (2 / Real.pi) := by
  have hs : (σ : ℝ) ≠ 0 := ne_of_gt (by exact_mod_cast hσ)
  have hZ := gaussian_standardized μ X σ hσ hX
  have hm := (Axioms.external_gaussian_moments μ 1 (fun _ => fun ω => (σ : ℝ)⁻¹ * X ω)
    (fun _ => hZ) ProbabilityTheory.iIndepFun.of_subsingleton).1 0
  have heq : (fun ω => |X ω|) =
      (fun ω => (σ : ℝ) * |(σ : ℝ)⁻¹ * X ω|) := by
    funext ω
    rw [abs_mul, abs_inv, abs_of_nonneg σ.coe_nonneg]
    field_simp [hs]
  rw [heq]
  exact ⟨hm.1.const_mul _, by rw [MeasureTheory.integral_const_mul, hm.2.2.2.1]⟩

lemma linear_abs_moment {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (n : ℕ) (Z : Fin n → Ω → ℝ)
    (hZ : ∀ j, ProbabilityTheory.HasLaw (Z j) (ProbabilityTheory.gaussianReal 0 1) μ)
    (hInd : ProbabilityTheory.iIndepFun Z μ) (a : Fin n → ℝ) :
    MeasureTheory.Integrable (fun ω => |∑ j, a j * Z j ω|) μ ∧
      (∫ ω, |∑ j, a j * Z j ω| ∂μ) =
        Real.sqrt (∑ j, a j ^ 2) * Real.sqrt (2 / Real.pi) := by
  classical
  by_cases ha : a = 0
  · subst a
    simp
  have hpos : 0 < ∑ j, a j ^ 2 := by
    apply Finset.sum_pos' (fun j _ => sq_nonneg (a j))
    obtain ⟨j, hj⟩ : ∃ j, a j ≠ 0 := by
      by_contra h
      apply ha
      funext j
      simpa using not_exists.mp h j
    exact ⟨j, Finset.mem_univ _, sq_pos_of_ne_zero hj⟩
  let v : NNReal := ∑ j, Real.toNNReal (a j ^ 2)
  have hv : (v : ℝ) = ∑ j, a j ^ 2 := by
    simp [v, Real.toNNReal_of_nonneg (sq_nonneg _)]
  have hσ : 0 < NNReal.sqrt v := by
    apply NNReal.sqrt_pos.2
    exact_mod_cast (hv.symm ▸ hpos)
  have hlaw := (Axioms.external_gaussian_moments μ n Z hZ hInd).2.1 a
  have hm := gaussian_abs_moment μ (fun ω => ∑ j, a j * Z j ω)
    (NNReal.sqrt v) hσ (by simpa only [NNReal.sq_sqrt] using hlaw)
  simpa only [Real.coe_sqrt, hv] using hm

lemma independent_vectors {Ω I J K : Type*} [MeasurableSpace Ω]
    [Fintype J] [Fintype K] (μ : MeasureTheory.Measure Ω)
    (Z : I → Ω → ℝ) (hZ : ∀ i, AEMeasurable (Z i) μ)
    (hInd : ProbabilityTheory.iIndepFun Z μ) (f : J → I) (g : K → I)
    (hfg : ∀ j k, f j ≠ g k) :
    ProbabilityTheory.IndepFun (fun ω j => Z (f j) ω) (fun ω k => Z (g k) ω) μ := by
  classical
  let S := Finset.univ.image f
  let T := Finset.univ.image g
  have hd : Disjoint S T := by
    apply Finset.disjoint_left.2
    intro i hi hj
    obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hi
    obtain ⟨k, _, hk⟩ := Finset.mem_image.mp hj
    exact hfg j k hk.symm
  have h := ProbabilityTheory.iIndepFun.indepFun_finset₀ S T hd hInd hZ
  exact h.comp
    (φ := fun z j => z ⟨f j, Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩⟩)
    (ψ := fun z k => z ⟨g k, Finset.mem_image.mpr ⟨k, Finset.mem_univ _, rfl⟩⟩)
    (by fun_prop) (by fun_prop)

lemma independent_pair_copy {Ω A B : Type*} [MeasurableSpace Ω]
    [MeasurableSpace A] [MeasurableSpace B]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (X : Ω → A) (Y : Ω → B) (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ)
    (hXY : ProbabilityTheory.IndepFun X Y μ) :
    ProbabilityTheory.IdentDistrib (fun ω => (X ω, Y ω))
      (fun ω : Ω × Ω => (X ω.1, Y ω.2)) μ (μ.prod μ) := by
  have hx : ProbabilityTheory.HasLaw X (μ.map X) μ := ⟨hX, rfl⟩
  have hy : ProbabilityTheory.HasLaw Y (μ.map Y) μ := ⟨hY, rfl⟩
  have hx' := hx.comp (MeasureTheory.measurePreserving_fst (μ := μ) (ν := μ)).hasLaw
  have hy' := hy.comp (MeasureTheory.measurePreserving_snd (μ := μ) (ν := μ)).hasLaw
  refine ⟨hX.prodMk hY, hx'.aemeasurable.prodMk hy'.aemeasurable, ?_⟩
  erw [(ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map hX hY).mp hXY,
    (ProbabilityTheory.indepFun_iff_map_prod_eq_prod_map_map hx'.aemeasurable hy'.aemeasurable).mp
      (ProbabilityTheory.indepFun_prod₀ hX hY), hx'.map_eq, hy'.map_eq]

lemma normal_dot_abs_mean {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure μ]
    (n : ℕ) (hn : 0 < n) (X Y : Fin n → Ω → ℝ)
    (hX : ∀ j, ProbabilityTheory.HasLaw (X j) (ProbabilityTheory.gaussianReal 0 1) μ)
    (hY : ∀ j, ProbabilityTheory.HasLaw (Y j) (ProbabilityTheory.gaussianReal 0 1) μ)
    (hiX : ProbabilityTheory.iIndepFun X μ) (hiY : ProbabilityTheory.iIndepFun Y μ)
    (hXY : ProbabilityTheory.IndepFun (fun ω j => X j ω) (fun ω j => Y j ω) μ) :
    MeasureTheory.Integrable (fun ω => |∑ j, X j ω * Y j ω|) μ ∧
      (∫ ω, |∑ j, X j ω * Y j ω| ∂μ) =
        (Real.sqrt 2 * Real.Gamma (((n : ℝ) + 1) / 2) / Real.Gamma ((n : ℝ) / 2)) *
          Real.sqrt (2 / Real.pi) := by
  have mx := Axioms.external_gaussian_moments μ n X hX hiX
  have my := Axioms.external_gaussian_moments μ n Y hY hiY
  -- Independence identifies the joint law with independent copies on μ × μ.
  have hcopy := independent_pair_copy μ (fun ω j => X j ω) (fun ω j => Y j ω)
    (aemeasurable_pi_lambda _ (fun j => (hX j).aemeasurable))
    (aemeasurable_pi_lambda _ (fun j => (hY j).aemeasurable)) hXY
  have hdot := hcopy.comp (show Measurable
      (fun p : (Fin n → ℝ) × (Fin n → ℝ) => |∑ j, p.1 j * p.2 j|) by fun_prop)
  have hxint (j : Fin n) : MeasureTheory.Integrable (X j) μ := by
    apply (MeasureTheory.integrable_norm_iff (hX j).aemeasurable.aestronglyMeasurable).mp
    simpa only [Real.norm_eq_abs] using (mx.1 j).1
  have hyint (j : Fin n) : MeasureTheory.Integrable (Y j) μ := by
    apply (MeasureTheory.integrable_norm_iff (hY j).aemeasurable.aestronglyMeasurable).mp
    simpa only [Real.norm_eq_abs] using (my.1 j).1
  have hp : MeasureTheory.Integrable
      (fun ω : Ω × Ω => |∑ j, X j ω.1 * Y j ω.2|) (μ.prod μ) :=
    (MeasureTheory.integrable_finset_sum Finset.univ
      (fun j _ => (hxint j).mul_prod (hyint j))).abs
  refine ⟨hdot.integrable_iff.mpr hp, ?_⟩
  -- Absolute integrability permits Fubini; the inner linear normal mean
  -- leaves the Euclidean norm, whose expectation is the chi mean.
  calc
    _ = ∫ ω : Ω × Ω, |∑ j, X j ω.1 * Y j ω.2| ∂(μ.prod μ) := hdot.integral_eq
    _ = ∫ ω, ∫ η, |∑ j, X j ω * Y j η| ∂μ ∂μ := MeasureTheory.integral_prod _ hp
    _ = ∫ ω, Real.sqrt (∑ j, X j ω ^ 2) * Real.sqrt (2 / Real.pi) ∂μ := by
      apply MeasureTheory.integral_congr_ae
      exact Filter.Eventually.of_forall (fun ω => (linear_abs_moment μ n Y hY hiY (fun j => X j ω)).2)
    _ = _ := by
      rw [MeasureTheory.integral_mul_const, mx.2.2.2.2.2]
      simp [Nat.ne_of_gt hn]

-- formalizer:machinery-end

end Lemma_3p7.Machinery
