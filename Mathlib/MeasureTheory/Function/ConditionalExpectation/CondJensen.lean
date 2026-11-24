/-
Copyright (c) 2026 Yongxi Lin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yongxi Lin, Thomas Zhu
-/
module

public import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
public import Mathlib.Analysis.Convex.LinearMean.Conditional

import Mathlib.Analysis.Convex.Approximation
import Mathlib.Analysis.Convex.Continuous

/-!
# Conditional Jensen's Inequality

This file contains the conditional Jensen's inequality. We follow the proof in
[Hytonen_VanNeerven_Veraar_Wies_2016].

## Main Statement

* `Convex.condExp_mem `: in a Banach space `E` with a finite measure `μ`, if `f` lies in a
  closed convex set `s` a.e., then `μ[f | m]` lies in `s` a.e.
* `ConvexOn.map_condExp_le_univ`: in a Banach space `E` with a sigma finite measure `μ`, if
  `φ : E → ℝ` is a convex lower-semicontinuous function, then for any `f : α → E` such that `f` and
  `φ ∘ f` are integrable, we have `φ (𝔼[f | m]) ≤ 𝔼[φ ∘ f | m]` a.e.
-/

public section

open MeasureTheory Function Set Filter

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {α : Type*} {f : α → E} {φ : E → ℝ} {m mα : MeasurableSpace α} {μ : Measure α} {s : Set E}

namespace MeasureTheory.Measure

variable (E) (μ)

@[expose]
noncomputable def extendedCondLinearMean [IsFiniteMeasure μ] (hm : m ≤ mα) :
    ExtendedCondLinearMean α ℝ E where
  toMean f := μ[f | m]
  conegligible := ae μ
  L := { f | Integrable f μ }
  mem_conegligible := sorry -- same proof as in IsProbabilityMeasure.extendedLinearMean
  add_mem ha hb := ha.add hb
  smul_mem c f hf := hf.smul c
  map_add' hf hg := condExp_add hf hg m
  map_smul' c {f} _ := condExp_smul c f m
  one_mem := integrable_const 1
  map_one' := Filter.EventuallyEq.of_eq <| condExp_const hm 1
  monotoneOn' f hf g hg h := condExp_mono hf hg h
  ℒ := { f | Integrable f μ }
  toExtendedMean f := μ[f | m]
  map_comp' l f hf := ⟨l.integrable_comp hf, l.comp_condExp_comm hf |>.symm⟩

noncomputable def extendedCondLinearMean_restrict [IsFiniteMeasure μ] (hm : m ≤ mα)
    (C : ClosedSubmodule ℝ E) :
    (extendedCondLinearMean E μ hm).Restrict C where
  restrict' := extendedCondLinearMean C μ hm
  toCondLinearMean_restrict' := rfl
  mem_and_map_eq' := by
    intro f hf
    have : CompleteSpace C := by infer_instance
    have : Integrable f μ := hf.mono
      (Topology.IsEmbedding.subtypeVal.aestronglyMeasurable_comp_iff.1 hf.aestronglyMeasurable)
      (by simp)
    exact ⟨this, C.subtypeL.comp_condExp_comm this (m := m) |>.symm⟩

lemma extendedCondLinearMean_conegligiblyInvariant [IsFiniteMeasure μ] (hm : m ≤ mα) :
    extendedCondLinearMean E μ hm |>.conegligiblyInvariant where
  mem_and_apply_eq _ hf _ hfg := ⟨hf.congr hfg, condExp_congr_ae hfg⟩
  mem_L_and_apply_M_eq _ hf _ hfg := ⟨hf.congr hfg, condExp_congr_ae hfg⟩

end MeasureTheory.Measure

private lemma Convex.condExp_mem_of_isFiniteMeasure [IsFiniteMeasure μ] (hm : m ≤ mα)
    (hf_int : Integrable f μ) (hs : IsClosed s) (hc : Convex ℝ s) (hf : ∀ᵐ a ∂μ, f a ∈ s) :
    ∀ᵐ a ∂μ, μ[f | m] a ∈ s := by
  have : CountableInterFilter (μ.extendedCondLinearMean E hm).conegligible :=
    show CountableInterFilter (ae μ) by infer_instance
  obtain ⟨t, ht, htt⟩ := hf_int.aestronglyMeasurable.isSeparable_ae_range
  let Y := (Submodule.span ℝ t).topologicalClosure
  have hY : IsClosed (Y : Set E) := Submodule.isClosed_topologicalClosure _
  have : SecondCountableTopology Y := ht.span.closure.secondCountableTopology
  have lem0 : ∀ᵐ a ∂μ, f a ∈ Y := by
    filter_upwards [htt] with a ha using
      (Submodule.closure_subset_topologicalClosure_span t) (subset_closure ha)
  exact μ.extendedCondLinearMean E hm |>.mem_convex_of_restrict
    hs hc hf_int hf
    (μ.extendedCondLinearMean_restrict E hm ⟨Y, hY⟩)
    (μ.extendedCondLinearMean_conegligiblyInvariant E hm)
    lem0

/-- Conditional Jensen's inequality for finite measures. -/
private theorem ConvexOn.map_condExp_le_of_isFiniteMeasure [IsFiniteMeasure μ] (hm : m ≤ mα)
    (hφ_cvx : ConvexOn ℝ s φ) (hφ_cont : LowerSemicontinuousOn φ s) (hf : ∀ᵐ a ∂μ, f a ∈ s)
    (hs : IsClosed s) (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) :
    φ ∘ μ[f | m] ≤ᵐ[μ] μ[φ ∘ f | m] := by
  have : CountableInterFilter (μ.extendedCondLinearMean E hm).conegligible :=
    show CountableInterFilter (ae μ) by infer_instance
  obtain ⟨t, ht, htt⟩ := hf_int.aestronglyMeasurable.isSeparable_ae_range
  let Y := (Submodule.span ℝ t).topologicalClosure
  have hY : IsClosed (Y : Set E) := Submodule.isClosed_topologicalClosure _
  have lem0 : ∀ᵐ a ∂μ, f a ∈ Y := by
    filter_upwards [htt] with a ha using
      (Submodule.closure_subset_topologicalClosure_span t) (subset_closure ha)
  have : SecondCountableTopology Y := ht.span.closure.secondCountableTopology
  exact μ.extendedCondLinearMean E hm |>.comp_mean_le
    (hφ_cont.isClosed_re_epigraph hs) hφ_cvx.convex_epigraph hf_int hf hφ_int
    (μ.extendedCondLinearMean_restrict E hm ⟨Y, hY⟩)
    (μ.extendedCondLinearMean_conegligiblyInvariant E hm)
    lem0

/-- If `f` lies in a closed convex set `s` a.e., then `μ[f | m]` lies in `s` a.e. -/
lemma Convex.condExp_mem (hm : m ≤ mα) [SigmaFinite (μ.trim hm)]
    (hf_int : Integrable f μ) (hs : IsClosed s) (hc : Convex ℝ s) (hf : ∀ᵐ a ∂μ, f a ∈ s) :
    ∀ᵐ a ∂μ, μ[f | m] a ∈ s := by
  apply (isCountablySpanning_spanningSets (μ.trim hm)).null_of_forall_restrict_null <;>
    rintro - ⟨n, rfl⟩
  · exact hm _ (measurableSet_spanningSets (μ.trim hm) n)
  have h1 := condExp_restrict_ae_eq_restrict hm (measurableSet_spanningSets (μ.trim hm) n) hf_int
  have : IsFiniteMeasure (μ.restrict (spanningSets (μ.trim hm) n)) := isFiniteMeasure_restrict.2
    ((le_trim hm).trans_lt (measure_spanningSets_lt_top (μ.trim hm) n)).ne
  have h2 := hc.condExp_mem_of_isFiniteMeasure (μ := μ.restrict (spanningSets (μ.trim hm) n)) hm
    hf_int.restrict hs (ae_restrict_of_ae hf)
  filter_upwards [h1, h2] with a ha hb
  simp_all

/-- **Conditional Jensen's inequality**: in a Banach space `E` with a measure `μ` that is σ-finite
on a sub-σ-algebra `m`, if `φ : E → ℝ` is convex and lower-semicontinuous on a closed set `s`, then
for any `f : α → E` such that `f` and `φ ∘ f` are integrable, and `f` lies in `s` a.e., we have
`φ (𝔼[f | m]) ≤ᵐ[μ] 𝔼[φ ∘ f | m]`. -/
theorem ConvexOn.map_condExp_le (hm : m ≤ mα) [SigmaFinite (μ.trim hm)]
    (hφ_cvx : ConvexOn ℝ s φ) (hφ_cont : LowerSemicontinuousOn φ s) (hf : ∀ᵐ a ∂μ, f a ∈ s)
    (hs : IsClosed s) (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) :
    φ ∘ μ[f | m] ≤ᵐ[μ] μ[φ ∘ f | m] := by
  apply (isCountablySpanning_spanningSets (μ.trim hm)).null_of_forall_restrict_null <;>
    rintro - ⟨n, rfl⟩
  · exact hm _ (measurableSet_spanningSets (μ.trim hm) n)
  have h1 := condExp_restrict_ae_eq_restrict hm (measurableSet_spanningSets (μ.trim hm) n) hf_int
  have h2 := condExp_restrict_ae_eq_restrict hm (measurableSet_spanningSets (μ.trim hm) n) hφ_int
  have : IsFiniteMeasure (μ.restrict (spanningSets (μ.trim hm) n)) := isFiniteMeasure_restrict.2
    ((le_trim hm).trans_lt (measure_spanningSets_lt_top (μ.trim hm) n)).ne
  have h3 := hφ_cvx.map_condExp_le_of_isFiniteMeasure (μ := μ.restrict (spanningSets (μ.trim hm) n))
    hm hφ_cont (ae_restrict_of_ae hf) hs hf_int.restrict hφ_int.restrict
  filter_upwards [h1, h2, h3] with a ha hb hc
  simpa [← ha, ← hb]

theorem ConvexOn.map_condExp_le_trim {mE : MeasurableSpace E} [BorelSpace E]
    (hm : m ≤ mα) [SigmaFinite (μ.trim hm)]
    (hφ_cvx : ConvexOn ℝ s φ) (hφ_cont : LowerSemicontinuousOn φ s)
    (hφ_meas : StronglyMeasurable φ) (hf : ∀ᵐ a ∂μ, f a ∈ s)
    (hs : IsClosed s) (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) :
    φ ∘ μ[f | m] ≤ᵐ[μ.trim hm] μ[φ ∘ f | m] := by
  rw [StronglyMeasurable.ae_le_trim_iff hm (by fun_prop) (by fun_prop)]
  exact hφ_cvx.map_condExp_le hm hφ_cont hf hs hf_int hφ_int

theorem ConcaveOn.condExp_map_le (hm : m ≤ mα) [SigmaFinite (μ.trim hm)]
    (hφ_cvx : ConcaveOn ℝ s φ) (hφ_cont : UpperSemicontinuousOn φ s) (hf : ∀ᵐ a ∂μ, f a ∈ s)
    (hs : IsClosed s) (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) :
    μ[φ ∘ f | m] ≤ᵐ[μ] φ ∘ μ[f | m] := by
  filter_upwards [hφ_cvx.neg.map_condExp_le hm hφ_cont.neg hf hs hf_int hφ_int.neg,
    condExp_neg (φ ∘ f) m] with a h ha
  simp_all [Pi.neg_comp]

theorem ConcaveOn.condExp_map_le_trim {mE : MeasurableSpace E} [BorelSpace E]
    (hm : m ≤ mα) [SigmaFinite (μ.trim hm)]
    (hφ_cvx : ConcaveOn ℝ s φ) (hφ_cont : UpperSemicontinuousOn φ s)
    (hφ_meas : StronglyMeasurable φ) (hf : ∀ᵐ a ∂μ, f a ∈ s)
    (hs : IsClosed s) (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) :
    μ[φ ∘ f | m] ≤ᵐ[μ.trim hm] φ ∘ μ[f | m] := by
  rw [StronglyMeasurable.ae_le_trim_iff hm (by fun_prop) (by fun_prop)]
  exact hφ_cvx.condExp_map_le hm hφ_cont hf hs hf_int hφ_int

/-- **Conditional Jensen's inequality**: in a Banach space `E` with a measure `μ` that is σ-finite
on a sub-σ-algebra `m`, if `φ : E → ℝ` is convex and lower-semicontinuous, then for any `f : α → E`
such that `f` and `φ ∘ f` are integrable, we have `φ (𝔼[f | m]) ≤ᵐ[μ] 𝔼[φ ∘ f | m]`. -/
theorem ConvexOn.map_condExp_le_univ (hm : m ≤ mα) [SigmaFinite (μ.trim hm)]
    (hφ_cvx : ConvexOn ℝ univ φ) (hφ_cont : LowerSemicontinuous φ)
    (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) :
    φ ∘ μ[f | m] ≤ᵐ[μ] μ[φ ∘ f | m] :=
  ConvexOn.map_condExp_le hm hφ_cvx (lowerSemicontinuousOn_univ_iff.2 hφ_cont) (by simp)
    isClosed_univ hf_int hφ_int

theorem ConvexOn.map_condExp_le_trim_univ {mE : MeasurableSpace E} [BorelSpace E]
    (hm : m ≤ mα) [SigmaFinite (μ.trim hm)]
    (hφ_cvx : ConvexOn ℝ univ φ) (hφ_cont : LowerSemicontinuous φ)
    (hφ_meas : StronglyMeasurable φ) (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) :
    φ ∘ μ[f | m] ≤ᵐ[μ.trim hm] μ[φ ∘ f | m] := by
  rw [StronglyMeasurable.ae_le_trim_iff hm (by fun_prop) (by fun_prop)]
  exact hφ_cvx.map_condExp_le_univ hm hφ_cont hf_int hφ_int

theorem ConcaveOn.condExp_map_le_univ (hm : m ≤ mα) [SigmaFinite (μ.trim hm)]
    (hφ_cvx : ConcaveOn ℝ univ φ) (hφ_cont : UpperSemicontinuous φ)
    (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) :
    μ[φ ∘ f | m] ≤ᵐ[μ] φ ∘ μ[f | m] := by
  filter_upwards [hφ_cvx.neg.map_condExp_le_univ hm hφ_cont.neg hf_int hφ_int.neg,
    condExp_neg (φ ∘ f) m] with a h ha
  simp_all [Pi.neg_comp]

theorem ConcaveOn.condExp_map_le_trim_univ {mE : MeasurableSpace E} [BorelSpace E]
    (hm : m ≤ mα) [SigmaFinite (μ.trim hm)]
    (hφ_cvx : ConcaveOn ℝ univ φ) (hφ_cont : UpperSemicontinuous φ)
    (hφ_meas : StronglyMeasurable φ) (hf_int : Integrable f μ) (hφ_int : Integrable (φ ∘ f) μ) :
    μ[φ ∘ f | m] ≤ᵐ[μ.trim hm] φ ∘ μ[f | m] := by
  rw [StronglyMeasurable.ae_le_trim_iff hm (by fun_prop) (by fun_prop)]
  exact hφ_cvx.condExp_map_le_univ hm hφ_cont hf_int hφ_int

/-- In a Banach space `E` with a measure `μ`, then for any `f : α → E`, we have
`‖𝔼[f | m]‖ ≤ᵐ[μ] 𝔼[‖f‖ | m]`. -/
theorem norm_condExp_le (f : α → E) : (‖μ[f | m] ·‖) ≤ᵐ[μ] μ[(‖f ·‖) | m] := by
  by_cases! hm : ¬ m ≤ mα
  · simp [condExp_of_not_le hm]; aesop
  by_cases! hμm : ¬ SigmaFinite (μ.trim hm)
  · simp [condExp_of_not_sigmaFinite hm hμm]; aesop
  by_cases! hf_int : ¬ Integrable f μ
  · simp only [condExp_of_not_integrable hf_int, Pi.zero_apply, norm_zero]
    apply condExp_nonneg
    filter_upwards with a; positivity
  exact convexOn_univ_norm.map_condExp_le_univ hm continuous_norm.lowerSemicontinuous hf_int
    hf_int.norm

theorem Integrable.norm_condExp_rpow_le {p : ℝ} (hp : 1 ≤ p)
    (hfint : Integrable (fun x => ‖f x‖ ^ p) μ) :
    (‖μ[f | m] ·‖ ^ p) ≤ᵐ[μ] μ[(‖f ·‖ ^ p) | m] := by
  have hp' : 0 < p := by linarith
  by_cases! hm : ¬ m ≤ mα
  · simp [condExp_of_not_le hm, Real.zero_rpow hp'.ne.symm]; aesop
  by_cases! hμm : ¬ SigmaFinite (μ.trim hm)
  · simp [condExp_of_not_sigmaFinite hm hμm, Real.zero_rpow hp'.ne.symm]; aesop
  by_cases! hf_int : ¬ Integrable f μ
  · simp only [condExp_of_not_integrable hf_int, Pi.zero_apply, norm_zero,
      Real.zero_rpow hp'.ne.symm]
    apply condExp_nonneg
    filter_upwards with a; positivity
  have hl := (Real.continuous_rpow_const hp'.le).lowerSemicontinuous.lowerSemicontinuousOn (Ici 0)
  have := (convexOn_rpow hp).map_condExp_le hm hl (by simp) isClosed_Ici hf_int.norm hfint
  filter_upwards [norm_condExp_le f, this] with a ha hb
  exact (Real.rpow_le_rpow (norm_nonneg _) ha hp'.le).trans hb

/-- **Conditional Jensen's inequality**: in a finite dimensional Banach space `E` with a measure
`μ` that is σ-finite on a sub-σ-algebra `m`, if `φ : E → ℝ` is convex, then for any `f : α → E` such
that `f` and `φ ∘ f` are integrable, we have `φ (𝔼[f | m]) ≤ᵐ[μ] 𝔼[φ ∘ f | m]`. -/
theorem ConvexOn.map_condExp_le_of_finiteDimensional [FiniteDimensional ℝ E] (hm : m ≤ mα)
    [SigmaFinite (μ.trim hm)] (hφ_cvx : ConvexOn ℝ univ φ) (hf_int : Integrable f μ)
    (hφ_int : Integrable (φ ∘ f) μ) :
    φ ∘ μ[f | m] ≤ᵐ[μ] μ[φ ∘ f | m] :=
  hφ_cvx.map_condExp_le_univ hm
    (continuousOn_univ.1 (hφ_cvx.continuousOn isOpen_univ)).lowerSemicontinuous hf_int hφ_int

theorem ConcaveOn.condExp_map_le_of_finiteDimensional [FiniteDimensional ℝ E] (hm : m ≤ mα)
    [SigmaFinite (μ.trim hm)] (hφ_cvx : ConcaveOn ℝ univ φ) (hf_int : Integrable f μ)
    (hφ_int : Integrable (φ ∘ f) μ) :
    μ[φ ∘ f | m] ≤ᵐ[μ] φ ∘ μ[f | m] := by
  filter_upwards [hφ_cvx.neg.map_condExp_le_of_finiteDimensional hm hf_int hφ_int.neg,
    condExp_neg (φ ∘ f) m] with a h ha
  simp_all [Pi.neg_comp]
