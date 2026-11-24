/-
Copyright (c) 2020 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
module

public import Mathlib.Analysis.Convex.LinearMean.Basic
public import Mathlib.Analysis.Convex.StrictConvexSpace
public import Mathlib.MeasureTheory.Function.AEEqOfIntegral
public import Mathlib.MeasureTheory.Integral.Average

/-!
# Jensen's inequality for integrals

In this file we prove several forms of Jensen's inequality for integrals.

- for convex sets: `Convex.average_mem`, `Convex.set_average_mem`, `Convex.integral_mem`;

- for convex functions: `ConvexOn.average_mem_epigraph`, `ConvexOn.map_average_le`,
  `ConvexOn.set_average_mem_epigraph`, `ConvexOn.map_set_average_le`, `ConvexOn.map_integral_le`;

- for strictly convex sets: `StrictConvex.ae_eq_const_or_average_mem_interior`;

- for a closed ball in a strictly convex normed space:
  `ae_eq_const_or_norm_integral_lt_of_norm_le_const`;

- for strictly convex functions: `StrictConvexOn.ae_eq_const_or_map_average_lt`.

## TODO

- Use a typeclass for strict convexity of a closed ball.

## Tags

convex, integral, center mass, average value, Jensen's inequality
-/

public section


open MeasureTheory MeasureTheory.Measure Metric Set Filter TopologicalSpace Function

open scoped Topology ENNReal Convex

variable {α E : Type*} {m0 : MeasurableSpace α} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] {μ : Measure α} {s : Set E} {t : Set α} {f : α → E} {g : E → ℝ} {C : ℝ}

/-!
### Non-strict Jensen's inequality
-/

section

variable (E μ) [IsProbabilityMeasure μ]

noncomputable def IsProbabilityMeasure.extendedLinearMean : ExtendedLinearMean α ℝ E where
  toMean f := ∫ x, f x ∂μ
  L := { f | Integrable f μ }
  add_mem hf hg := hf.add hg
  smul_mem c f hf := hf.smul c
  map_add' hf hg := integral_add hf hg
  map_smul' c f _ := by simp_rw [Pi.smul_apply]; rw [integral_smul]
  one_mem := integrable_const 1
  map_one' := by simp
  ℒ := { f | Integrable f μ }
  toExtendedMean f := ∫ x, f x ∂μ
  map_comp' l f hf := ⟨l.integrable_comp hf, l.integral_comp_comm hf⟩
  monotoneOn' f hf g hg h := integral_mono hf hg h
  conegligible := ae μ
  mem_conegligible' {s} := by
    rw [MeasureTheory.mem_ae_iff]
    symm
    constructor
    · rintro ⟨f, hf, h0f, hsf, h0⟩
      change ∫ x, f x ∂μ = 0 at h0
      rw [integral_eq_zero_iff_of_nonneg h0f hf] at h0
      unfold EventuallyEq Filter.Eventually at h0
      rw [MeasureTheory.mem_ae_iff] at h0
      simp only [Pi.zero_apply] at h0
      rw [← nonpos_iff_eq_zero] at h0 ⊢
      refine le_trans ?_ h0
      apply measure_mono
      grind
    · intro hs
      use sᶜ.indicator 1
      have hs' := NullMeasurableSet.of_null hs
      refine ⟨?_, ?_, ?_, ?_⟩
      · apply IntegrableOn.integrable_indicator₀
        · exact integrableOn_const
        · exact NullMeasurableSet.of_null hs
      · apply Set.indicator_nonneg
        simp
      · intro x hx
        classical
        rw [Set.indicator_apply, ite_eq_left (mem_compl hx)]
        simp
      · rw [integral_indicator₀ hs']
        simp only [Pi.one_apply, integral_const, MeasurableSet.univ, measureReal_restrict_apply,
          univ_inter, smul_eq_mul, mul_one]
        rwa [measureReal_eq_zero_iff]

lemma IsProbabilityMeasure.extendedLinearMean_conegligible_def :
    (extendedLinearMean E μ).conegligible = ae μ := by rfl

lemma IsProbabilityMeasure.extendedLinearMean_conegligiblyInvariant :
    extendedLinearMean E μ |>.ConegligiblyInvariant where
  mem_and_apply_eq _ hf _ hfg := ⟨hf.congr hfg, integral_congr_ae hfg⟩
  mem_L_and_apply_M_eq _ hf _ hfg := ⟨hf.congr hfg, integral_congr_ae hfg⟩

end

/-- If `μ` is a probability measure on `α`, `s` is a convex closed set in `E`, and `f` is an
integrable function sending `μ`-a.e. points to `s`, then the expected value of `f` belongs to `s`:
`∫ x, f x ∂μ ∈ s`. See also `Convex.sum_mem` for a finite sum version of this lemma. -/
theorem Convex.integral_mem [IsProbabilityMeasure μ] (hs : Convex ℝ s) (hsc : IsClosed s)
    (hf : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ) : (∫ x, f x ∂μ) ∈ s := by
  have : IsProbabilityMeasure.extendedLinearMean E μ |>.conegligible.NeBot :=
    show (ae μ).NeBot by infer_instance
  exact IsProbabilityMeasure.extendedLinearMean_conegligiblyInvariant E μ |>.mem_convex
    hsc hs hfi hf

/-- If `μ` is a non-zero finite measure on `α`, `s` is a convex closed set in `E`, and `f` is an
integrable function sending `μ`-a.e. points to `s`, then the average value of `f` belongs to `s`:
`⨍ x, f x ∂μ ∈ s`. See also `Convex.centerMass_mem` for a finite sum version of this lemma. -/
theorem Convex.average_mem [IsFiniteMeasure μ] [NeZero μ] (hs : Convex ℝ s) (hsc : IsClosed s)
    (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ) : (⨍ x, f x ∂μ) ∈ s :=
  hs.integral_mem hsc (ae_mono' smul_absolutelyContinuous hfs) hfi.to_average

/-- If `μ` is a non-zero finite measure on `α`, `s` is a convex closed set in `E`, and `f` is an
integrable function sending `μ`-a.e. points to `s`, then the average value of `f` belongs to `s`:
`⨍ x, f x ∂μ ∈ s`. See also `Convex.centerMass_mem` for a finite sum version of this lemma. -/
theorem Convex.set_average_mem (hs : Convex ℝ s) (hsc : IsClosed s) (h0 : μ t ≠ 0) (ht : μ t ≠ ∞)
    (hfs : ∀ᵐ x ∂μ.restrict t, f x ∈ s) (hfi : IntegrableOn f t μ) : (⨍ x in t, f x ∂μ) ∈ s :=
  have := Fact.mk ht.lt_top
  have := NeZero.mk h0
  hs.average_mem hsc hfs hfi

/-- If `μ` is a non-zero finite measure on `α`, `s` is a convex set in `E`, and `f` is an integrable
function sending `μ`-a.e. points to `s`, then the average value of `f` belongs to `closure s`:
`⨍ x, f x ∂μ ∈ s`. See also `Convex.centerMass_mem` for a finite sum version of this lemma. -/
theorem Convex.set_average_mem_closure (hs : Convex ℝ s) (h0 : μ t ≠ 0) (ht : μ t ≠ ∞)
    (hfs : ∀ᵐ x ∂μ.restrict t, f x ∈ s) (hfi : IntegrableOn f t μ) :
    (⨍ x in t, f x ∂μ) ∈ closure s :=
  hs.closure.set_average_mem isClosed_closure h0 ht (hfs.mono fun _ hx => subset_closure hx) hfi

theorem ConvexOn.average_mem_epigraph [IsFiniteMeasure μ] [NeZero μ] (hg : ConvexOn ℝ s g)
    (hgc : ContinuousOn g s) (hsc : IsClosed s) (hfs : ∀ᵐ x ∂μ, f x ∈ s)
    (hfi : Integrable f μ) (hgi : Integrable (g ∘ f) μ) :
    (⨍ x, f x ∂μ, ⨍ x, g (f x) ∂μ) ∈ {p : E × ℝ | p.1 ∈ s ∧ g p.1 ≤ p.2} := by
  have ht_mem : ∀ᵐ x ∂μ, (f x, g (f x)) ∈ {p : E × ℝ | p.1 ∈ s ∧ g p.1 ≤ p.2} :=
    hfs.mono fun x hx => ⟨hx, le_rfl⟩
  exact average_pair hfi hgi ▸
    hg.convex_epigraph.average_mem (hsc.epigraph hgc) ht_mem (hfi.prodMk hgi)

theorem ConcaveOn.average_mem_hypograph [IsFiniteMeasure μ] [NeZero μ] (hg : ConcaveOn ℝ s g)
    (hgc : ContinuousOn g s) (hsc : IsClosed s) (hfs : ∀ᵐ x ∂μ, f x ∈ s)
    (hfi : Integrable f μ) (hgi : Integrable (g ∘ f) μ) :
    (⨍ x, f x ∂μ, ⨍ x, g (f x) ∂μ) ∈ {p : E × ℝ | p.1 ∈ s ∧ p.2 ≤ g p.1} := by
  simpa using hg.neg.average_mem_epigraph hgc.neg hsc hfs hfi hgi.neg

/-- **Jensen's inequality**: if a function `g : E → ℝ` is convex and continuous on a convex closed
set `s`, `μ` is a finite non-zero measure on `α`, and `f : α → E` is a function sending
`μ`-a.e. points to `s`, then the value of `g` at the average value of `f` is less than or equal to
the average value of `g ∘ f` provided that both `f` and `g ∘ f` are integrable. See also
`ConvexOn.map_centerMass_le` for a finite sum version of this lemma. -/
theorem ConvexOn.map_average_le [IsFiniteMeasure μ] [NeZero μ]
    (hg : ConvexOn ℝ s g) (hgc : ContinuousOn g s) (hsc : IsClosed s)
    (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ) (hgi : Integrable (g ∘ f) μ) :
    g (⨍ x, f x ∂μ) ≤ ⨍ x, g (f x) ∂μ :=
  (hg.average_mem_epigraph hgc hsc hfs hfi hgi).2

/-- **Jensen's inequality**: if a function `g : E → ℝ` is concave and continuous on a convex closed
set `s`, `μ` is a finite non-zero measure on `α`, and `f : α → E` is a function sending
`μ`-a.e. points to `s`, then the average value of `g ∘ f` is less than or equal to the value of `g`
at the average value of `f` provided that both `f` and `g ∘ f` are integrable. See also
`ConcaveOn.le_map_centerMass` for a finite sum version of this lemma. -/
theorem ConcaveOn.le_map_average [IsFiniteMeasure μ] [NeZero μ]
    (hg : ConcaveOn ℝ s g) (hgc : ContinuousOn g s) (hsc : IsClosed s)
    (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ) (hgi : Integrable (g ∘ f) μ) :
    (⨍ x, g (f x) ∂μ) ≤ g (⨍ x, f x ∂μ) :=
  (hg.average_mem_hypograph hgc hsc hfs hfi hgi).2

/-- **Jensen's inequality**: if a function `g : E → ℝ` is convex and continuous on a convex closed
set `s`, `μ` is a finite non-zero measure on `α`, and `f : α → E` is a function sending
`μ`-a.e. points of a set `t` to `s`, then the value of `g` at the average value of `f` over `t` is
less than or equal to the average value of `g ∘ f` over `t` provided that both `f` and `g ∘ f` are
integrable. -/
theorem ConvexOn.set_average_mem_epigraph (hg : ConvexOn ℝ s g) (hgc : ContinuousOn g s)
    (hsc : IsClosed s) (h0 : μ t ≠ 0) (ht : μ t ≠ ∞) (hfs : ∀ᵐ x ∂μ.restrict t, f x ∈ s)
    (hfi : IntegrableOn f t μ) (hgi : IntegrableOn (g ∘ f) t μ) :
    (⨍ x in t, f x ∂μ, ⨍ x in t, g (f x) ∂μ) ∈ {p : E × ℝ | p.1 ∈ s ∧ g p.1 ≤ p.2} :=
  have := Fact.mk ht.lt_top
  have := NeZero.mk h0
  hg.average_mem_epigraph hgc hsc hfs hfi hgi

/-- **Jensen's inequality**: if a function `g : E → ℝ` is concave and continuous on a convex closed
set `s`, `μ` is a finite non-zero measure on `α`, and `f : α → E` is a function sending
`μ`-a.e. points of a set `t` to `s`, then the average value of `g ∘ f` over `t` is less than or
equal to the value of `g` at the average value of `f` over `t` provided that both `f` and `g ∘ f`
are integrable. -/
theorem ConcaveOn.set_average_mem_hypograph (hg : ConcaveOn ℝ s g) (hgc : ContinuousOn g s)
    (hsc : IsClosed s) (h0 : μ t ≠ 0) (ht : μ t ≠ ∞) (hfs : ∀ᵐ x ∂μ.restrict t, f x ∈ s)
    (hfi : IntegrableOn f t μ) (hgi : IntegrableOn (g ∘ f) t μ) :
    (⨍ x in t, f x ∂μ, ⨍ x in t, g (f x) ∂μ) ∈ {p : E × ℝ | p.1 ∈ s ∧ p.2 ≤ g p.1} := by
  simpa using hg.neg.set_average_mem_epigraph hgc.neg hsc h0 ht hfs hfi hgi.neg

/-- **Jensen's inequality**: if a function `g : E → ℝ` is convex and continuous on a convex closed
set `s`, `μ` is a finite non-zero measure on `α`, and `f : α → E` is a function sending
`μ`-a.e. points of a set `t` to `s`, then the value of `g` at the average value of `f` over `t` is
less than or equal to the average value of `g ∘ f` over `t` provided that both `f` and `g ∘ f` are
integrable. -/
theorem ConvexOn.map_set_average_le (hg : ConvexOn ℝ s g) (hgc : ContinuousOn g s)
    (hsc : IsClosed s) (h0 : μ t ≠ 0) (ht : μ t ≠ ∞) (hfs : ∀ᵐ x ∂μ.restrict t, f x ∈ s)
    (hfi : IntegrableOn f t μ) (hgi : IntegrableOn (g ∘ f) t μ) :
    g (⨍ x in t, f x ∂μ) ≤ ⨍ x in t, g (f x) ∂μ :=
  (hg.set_average_mem_epigraph hgc hsc h0 ht hfs hfi hgi).2

/-- **Jensen's inequality**: if a function `g : E → ℝ` is concave and continuous on a convex closed
set `s`, `μ` is a finite non-zero measure on `α`, and `f : α → E` is a function sending
`μ`-a.e. points of a set `t` to `s`, then the average value of `g ∘ f` over `t` is less than or
equal to the value of `g` at the average value of `f` over `t` provided that both `f` and `g ∘ f`
are integrable. -/
theorem ConcaveOn.le_map_set_average (hg : ConcaveOn ℝ s g) (hgc : ContinuousOn g s)
    (hsc : IsClosed s) (h0 : μ t ≠ 0) (ht : μ t ≠ ∞) (hfs : ∀ᵐ x ∂μ.restrict t, f x ∈ s)
    (hfi : IntegrableOn f t μ) (hgi : IntegrableOn (g ∘ f) t μ) :
    (⨍ x in t, g (f x) ∂μ) ≤ g (⨍ x in t, f x ∂μ) :=
  (hg.set_average_mem_hypograph hgc hsc h0 ht hfs hfi hgi).2

/-- **Jensen's inequality**: if a function `g : E → ℝ` is convex and continuous on a convex closed
set `s`, `μ` is a probability measure on `α`, and `f : α → E` is a function sending `μ`-a.e.  points
to `s`, then the value of `g` at the expected value of `f` is less than or equal to the expected
value of `g ∘ f` provided that both `f` and `g ∘ f` are integrable. See also
`ConvexOn.map_centerMass_le` for a finite sum version of this lemma. -/
theorem ConvexOn.map_integral_le [IsProbabilityMeasure μ] (hg : ConvexOn ℝ s g)
    (hgc : ContinuousOn g s) (hsc : IsClosed s) (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ)
    (hgi : Integrable (g ∘ f) μ) : g (∫ x, f x ∂μ) ≤ ∫ x, g (f x) ∂μ := by
  simpa only [average_eq_integral] using hg.map_average_le hgc hsc hfs hfi hgi

/-- **Jensen's inequality**: if a function `g : E → ℝ` is concave and continuous on a convex closed
set `s`, `μ` is a probability measure on `α`, and `f : α → E` is a function sending `μ`-a.e.  points
to `s`, then the expected value of `g ∘ f` is less than or equal to the value of `g` at the expected
value of `f` provided that both `f` and `g ∘ f` are integrable. -/
theorem ConcaveOn.le_map_integral [IsProbabilityMeasure μ] (hg : ConcaveOn ℝ s g)
    (hgc : ContinuousOn g s) (hsc : IsClosed s) (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ)
    (hgi : Integrable (g ∘ f) μ) : (∫ x, g (f x) ∂μ) ≤ g (∫ x, f x ∂μ) := by
  simpa only [average_eq_integral] using hg.le_map_average hgc hsc hfs hfi hgi

/-!
### Strict Jensen's inequality
-/


/-- If `f : α → E` is an integrable function, then either it is a.e. equal to the constant
`⨍ x, f x ∂μ` or there exists a measurable set such that `μ t ≠ 0`, `μ tᶜ ≠ 0`, and the average
values of `f` over `t` and `tᶜ` are different. -/
theorem ae_eq_const_or_exists_average_ne_compl [IsFiniteMeasure μ] (hfi : Integrable f μ) :
    f =ᵐ[μ] const α (⨍ x, f x ∂μ) ∨
      ∃ t, MeasurableSet t ∧ μ t ≠ 0 ∧ μ tᶜ ≠ 0 ∧ (⨍ x in t, f x ∂μ) ≠ ⨍ x in tᶜ, f x ∂μ := by
  refine or_iff_not_imp_right.mpr fun H => ?_; push Not at H
  refine hfi.ae_eq_of_forall_setIntegral_eq _ _ (integrable_const _) fun t ht ht' => ?_; clear ht'
  simp only [const_apply, setIntegral_const]
  by_cases h₀ : μ t = 0
  · rw [restrict_eq_zero.2 h₀, integral_zero_measure, measureReal_def, h₀,
      ENNReal.toReal_zero, zero_smul]
  by_cases h₀' : μ tᶜ = 0
  · rw [← ae_eq_univ] at h₀'
    rw [restrict_congr_set h₀', restrict_univ, measureReal_congr h₀', measure_smul_average]
  have := average_mem_openSegment_compl_self ht.nullMeasurableSet h₀ h₀' hfi
  rw [← H t ht h₀ h₀', openSegment_same, mem_singleton_iff] at this
  rw [this, measure_smul_setAverage _ (by finiteness)]

/-- If an integrable function `f : α → E` takes values in a convex set `s` and for some set `t` of
positive measure, the average value of `f` over `t` belongs to the interior of `s`, then the average
of `f` over the whole space belongs to the interior of `s`. -/
theorem Convex.average_mem_interior_of_set [IsFiniteMeasure μ] (hs : Convex ℝ s) (h0 : μ t ≠ 0)
    (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ) (ht : (⨍ x in t, f x ∂μ) ∈ interior s) :
    (⨍ x, f x ∂μ) ∈ interior s := by
  rw [← measure_toMeasurable] at h0; rw [← restrict_toMeasurable (by finiteness)] at ht
  by_cases h0' : μ (toMeasurable μ t)ᶜ = 0
  · rw [← ae_eq_univ] at h0'
    rwa [restrict_congr_set h0', restrict_univ] at ht
  exact hs.openSegment_interior_closure_subset_interior ht
      (hs.set_average_mem_closure h0' (by finiteness) (ae_restrict_of_ae hfs) hfi.integrableOn)
      (average_mem_openSegment_compl_self (measurableSet_toMeasurable μ t).nullMeasurableSet h0
        h0' hfi)

/-- If an integrable function `f : α → E` takes values in a strictly convex closed set `s`, then
either it is a.e. equal to its average value, or its average value belongs to the interior of
`s`. -/
theorem StrictConvex.ae_eq_const_or_average_mem_interior [IsFiniteMeasure μ] (hs : StrictConvex ℝ s)
    (hsc : IsClosed s) (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ) :
    f =ᵐ[μ] const α (⨍ x, f x ∂μ) ∨ (⨍ x, f x ∂μ) ∈ interior s := by
  have : ∀ {t}, μ t ≠ 0 → (⨍ x in t, f x ∂μ) ∈ s := fun ht =>
    hs.convex.set_average_mem hsc ht (by finiteness) (ae_restrict_of_ae hfs) hfi.integrableOn
  refine (ae_eq_const_or_exists_average_ne_compl hfi).imp_right ?_
  rintro ⟨t, hm, h₀, h₀', hne⟩
  exact
    hs.openSegment_subset (this h₀) (this h₀') hne
      (average_mem_openSegment_compl_self hm.nullMeasurableSet h₀ h₀' hfi)

/-- **Jensen's inequality**, strict version: if an integrable function `f : α → E` takes values in a
convex closed set `s`, and `g : E → ℝ` is continuous and strictly convex on `s`, then
either `f` is a.e. equal to its average value, or `g (⨍ x, f x ∂μ) < ⨍ x, g (f x) ∂μ`. -/
theorem StrictConvexOn.ae_eq_const_or_map_average_lt [IsFiniteMeasure μ] (hg : StrictConvexOn ℝ s g)
    (hgc : ContinuousOn g s) (hsc : IsClosed s) (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ)
    (hgi : Integrable (g ∘ f) μ) :
    f =ᵐ[μ] const α (⨍ x, f x ∂μ) ∨ g (⨍ x, f x ∂μ) < ⨍ x, g (f x) ∂μ := by
  have : ∀ {t}, μ t ≠ 0 → (⨍ x in t, f x ∂μ) ∈ s ∧ g (⨍ x in t, f x ∂μ) ≤ ⨍ x in t, g (f x) ∂μ :=
    fun ht =>
    hg.convexOn.set_average_mem_epigraph hgc hsc ht (by finiteness) (ae_restrict_of_ae hfs)
      hfi.integrableOn hgi.integrableOn
  refine (ae_eq_const_or_exists_average_ne_compl hfi).imp_right ?_
  rintro ⟨t, hm, h₀, h₀', hne⟩
  rcases average_mem_openSegment_compl_self hm.nullMeasurableSet h₀ h₀' (hfi.prodMk hgi) with
    ⟨a, b, ha, hb, hab, h_avg⟩
  rw [average_pair hfi hgi, average_pair hfi.integrableOn hgi.integrableOn,
    average_pair hfi.integrableOn hgi.integrableOn, Prod.smul_mk,
    Prod.smul_mk, Prod.mk_add_mk, Prod.mk_inj] at h_avg
  simp only [Function.comp] at h_avg
  rw [← h_avg.1, ← h_avg.2]
  calc
    g ((a • ⨍ x in t, f x ∂μ) + b • ⨍ x in tᶜ, f x ∂μ) <
        a * g (⨍ x in t, f x ∂μ) + b * g (⨍ x in tᶜ, f x ∂μ) :=
      hg.2 (this h₀).1 (this h₀').1 hne ha hb hab
    _ ≤ (a * ⨍ x in t, g (f x) ∂μ) + b * ⨍ x in tᶜ, g (f x) ∂μ := by
      gcongr
      exacts [(this h₀).2, (this h₀').2]

/-- **Jensen's inequality**, strict version: if an integrable function `f : α → E` takes values in a
convex closed set `s`, and `g : E → ℝ` is continuous and strictly concave on `s`, then
either `f` is a.e. equal to its average value, or `⨍ x, g (f x) ∂μ < g (⨍ x, f x ∂μ)`. -/
theorem StrictConcaveOn.ae_eq_const_or_lt_map_average [IsFiniteMeasure μ]
    (hg : StrictConcaveOn ℝ s g) (hgc : ContinuousOn g s) (hsc : IsClosed s)
    (hfs : ∀ᵐ x ∂μ, f x ∈ s) (hfi : Integrable f μ) (hgi : Integrable (g ∘ f) μ) :
    f =ᵐ[μ] const α (⨍ x, f x ∂μ) ∨ (⨍ x, g (f x) ∂μ) < g (⨍ x, f x ∂μ) := by
  simpa using hg.neg.ae_eq_const_or_map_average_lt hgc.neg hsc hfs hfi hgi.neg

/-- If `E` is a strictly convex normed space and `f : α → E` is a function such that `‖f x‖ ≤ C`
a.e., then either this function is a.e. equal to its average value, or the norm of its average value
is strictly less than `C`. -/
theorem ae_eq_const_or_norm_average_lt_of_norm_le_const [StrictConvexSpace ℝ E]
    (h_le : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) : f =ᵐ[μ] const α (⨍ x, f x ∂μ) ∨ ‖⨍ x, f x ∂μ‖ < C := by
  rcases le_or_gt C 0 with hC0 | hC0
  · have : f =ᵐ[μ] 0 := h_le.mono fun x hx => norm_le_zero_iff.1 (hx.trans hC0)
    simp only [average_congr this, Pi.zero_apply, average_zero]
    exact Or.inl this
  by_cases hfi : Integrable f μ; swap
  · simp [average_eq, integral_undef hfi, hC0]
  rcases (le_top : μ univ ≤ ∞).eq_or_lt with hμt | hμt
  · simp [average_eq, measureReal_def, hμt, hC0]
  have : IsFiniteMeasure μ := ⟨hμt⟩
  replace h_le : ∀ᵐ x ∂μ, f x ∈ closedBall (0 : E) C := by simpa only [mem_closedBall_zero_iff]
  simpa only [interior_closedBall _ hC0.ne', mem_ball_zero_iff] using
    (strictConvex_closedBall ℝ (0 : E) C).ae_eq_const_or_average_mem_interior isClosed_closedBall
      h_le hfi

/-- If `E` is a strictly convex normed space and `f : α → E` is a function such that `‖f x‖ ≤ C`
a.e., then either this function is a.e. equal to its average value, or the norm of its integral is
strictly less than `μ.real univ * C`. -/
theorem ae_eq_const_or_norm_integral_lt_of_norm_le_const [StrictConvexSpace ℝ E] [IsFiniteMeasure μ]
    (h_le : ∀ᵐ x ∂μ, ‖f x‖ ≤ C) :
    f =ᵐ[μ] const α (⨍ x, f x ∂μ) ∨ ‖∫ x, f x ∂μ‖ < μ.real univ * C := by
  rcases eq_or_ne μ 0 with h₀ | h₀; · simp [h₀, EventuallyEq]
  have hμ : 0 < μ.real univ := by
    simp [measureReal_def, ENNReal.toReal_pos_iff, pos_iff_ne_zero, h₀, measure_lt_top]
  refine (ae_eq_const_or_norm_average_lt_of_norm_le_const h_le).imp_right fun H => ?_
  rwa [average_eq, norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hμ, ← div_eq_inv_mul,
    div_lt_iff₀' hμ] at H

/-- If `E` is a strictly convex normed space and `f : α → E` is a function such that `‖f x‖ ≤ C`
a.e. on a set `t` of finite measure, then either this function is a.e. equal to its average value on
`t`, or the norm of its integral over `t` is strictly less than `μ.real t * C`. -/
theorem ae_eq_const_or_norm_setIntegral_lt_of_norm_le_const [StrictConvexSpace ℝ E] (ht : μ t ≠ ∞)
    (h_le : ∀ᵐ x ∂μ.restrict t, ‖f x‖ ≤ C) :
    f =ᵐ[μ.restrict t] const α (⨍ x in t, f x ∂μ) ∨ ‖∫ x in t, f x ∂μ‖ < μ.real t * C := by
  have := Fact.mk ht.lt_top
  rw [← measureReal_restrict_apply_univ]
  exact ae_eq_const_or_norm_integral_lt_of_norm_le_const h_le
