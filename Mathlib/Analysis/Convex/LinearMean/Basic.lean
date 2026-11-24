/-
Copyright (c) 2026 Tian Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tian Chen
-/
module

public import Mathlib.Analysis.Convex.LinearMean.Defs
public import Mathlib.Analysis.LocallyConvex.Separation

import Mathlib.Analysis.LocallyConvex.HahnBanach
import Mathlib.Analysis.Normed.Affine.AddTorsorBases
import Mathlib.RingTheory.Finiteness.Prod

/-!

TODO: equality cases

-/

public section

variable {E R B : Type*}

section

variable [Preorder R] [CommSemiring R] [IsOrderedAddMonoid R] [TopologicalSpace R]

variable (M : LinearMean E R)

def LinearMean.toExtendedLinearMean : ExtendedLinearMean E R R := {
  M with
  ℒ := M.L
  toExtendedMean := M.toMean
  map_comp' l f hf := by
    have := Dual.apply_one_mul_eq l.toLinearMap
    have h : l ∘ f = l 1 • f := by
      ext x
      simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul]
      rw [← ContinuousLinearMap.coe_coe, ← this]
    rw [h]
    refine ⟨M.smul_mem _ hf, ?_⟩
    rw [← ContinuousLinearMap.coe_coe, M.map_smul' _ hf, smul_eq_mul]
    conv_rhs => rw [← this]
}

variable {M}

lemma LinearMean.ConegligiblyInvariant.toExtendedLinearMean
  (h : M.ConegligiblyInvariant) : M.toExtendedLinearMean.ConegligiblyInvariant := {
  h with
  mem_and_apply_eq := h.mem_L_and_apply_M_eq
}

instance [M.conegligible.NeBot] : M.toExtendedLinearMean.conegligible.NeBot := by assumption

end

namespace ExtendedLinearMean

section

variable [CommSemiring R] [Preorder R] [IsOrderedAddMonoid R] [AddCommMonoid B] [Module R B]
  [TopologicalSpace R] [TopologicalSpace B] [ContinuousAdd R]
  (ℳ : ExtendedLinearMean E R B)

/-- An extended linear mean on `B` can be extended to `B × R` -/
def prodScalar : ExtendedLinearMean E R (B × R) := {
  ℳ.toLinearMean with
  ℒ := { f | Prod.fst ∘ f ∈ ℳ.ℒ ∧ Prod.snd ∘ f ∈ ℳ.L }
  toExtendedMean := fun f ↦ (ℳ (Prod.fst ∘ f), ℳ.toLinearMean (Prod.snd ∘ f))
  map_comp' := by
    rintro l g ⟨hgℒ, hgL⟩
    set l₁ : B →L[R] R := l.comp (ContinuousLinearMap.inl R B R) with hl₁
    set l₂ : R →L[R] R := l.comp (ContinuousLinearMap.inr R B R) with hl₂
    have hl : l₁.coprod l₂ = l := by
      rw [← ContinuousLinearMap.coe_inj, hl₁, hl₂]
      simp
    rw [← hl]
    have h₂ : l₂ ∘ Prod.snd ∘ g = l₂.toLinearMap 1 • Prod.snd ∘ g := by
      ext x
      rw [Pi.smul_apply, smul_eq_mul]
      exact (Dual.apply_one_mul_eq _ _).symm
    have hl₁L : l₁ ∘ Prod.fst ∘ g ∈ ℳ.L := ℳ.comp_mem l₁ hgℒ
    have hl₂L : l₂ ∘ Prod.snd ∘ g ∈ ℳ.L := by
      rw [h₂]
      exact ℳ.smul_mem _ hgL
    refine ⟨ℳ.add_mem hl₁L hl₂L, ?_⟩
    rw [ContinuousLinearMap.coprod_apply, ← ℳ.map_comp l₁ hgℒ,
      ← l₂.coe_coe, ← Dual.apply_one_mul_eq, ← smul_eq_mul,
      ← ℳ.map_smul _ hgL, ← h₂, ← ℳ.map_add hl₁L hl₂L]
    rfl
}

namespace ConegligiblyInvariant

variable {ℳ}

theorem prod_scalar (hℳ : ℳ.ConegligiblyInvariant) : ℳ.prodScalar.ConegligiblyInvariant where
  mem_and_apply_eq := fun _ ⟨hf₁, hf₂⟩ _ hg ↦
    have ⟨hg₁, hf₁⟩ := hℳ.mem_and_apply_eq hf₁ (hg.fun_comp _)
    have ⟨hg₂, hf₂⟩ := hℳ.mem_L_and_apply_M_eq hf₂ (hg.fun_comp _)
    ⟨⟨hg₁, hg₂⟩, Prod.ext hf₁ hf₂⟩
  mem_L_and_apply_M_eq := hℳ.mem_L_and_apply_M_eq

instance [ℳ.conegligible.NeBot] : ℳ.prodScalar.conegligible.NeBot := by assumption

end ConegligiblyInvariant

end

section LocallyConvexSpace

variable [TopologicalSpace B] [AddCommGroup B] [IsTopologicalAddGroup B]
  [Module ℝ B] [ContinuousSMul ℝ B] [LocallyConvexSpace ℝ B]
  (ℳ : ExtendedLinearMean E ℝ B) {s : Set B} {f : E → B} {φ : B → ℝ}

theorem mem_convex (hs₁ : IsClosed s) (hs₂ : Convex ℝ s)
    (hf : f ∈ ℳ.ℒ) (hfs : ∀ x, f x ∈ s) : ℳ f ∈ s := by
  by_contra h
  obtain ⟨l, c, hlc, hls⟩ := geometric_hahn_banach_point_closed hs₂ hs₁ h
  have h : c • (1 : E → ℝ) ≤ l ∘ f := by
    intro x
    simpa using hls _ (hfs x) |>.le
  have := ℳ.monotoneOn (ℳ.smul_mem _ ℳ.one_mem) (ℳ.comp_mem _ hf) h
  rw [ℳ.map_comp l hf, ℳ.map_smul _ ℳ.one_mem, ℳ.map_one, smul_eq_mul, mul_one] at this
  exact hlc.not_ge this

theorem map_mean_le_of_epigraph
    (h_epigraph_closed : IsClosed {p : B × ℝ | p.1 ∈ s ∧ φ p.1 ≤ p.2})
    (h_epigraph_convex : Convex ℝ {p : B × ℝ | p.1 ∈ s ∧ φ p.1 ≤ p.2})
    (hf : f ∈ ℳ.ℒ) (hfs : ∀ x, f x ∈ s) (hφf : φ ∘ f ∈ ℳ.L) :
    φ (ℳ f) ≤ ℳ.toLinearMean (φ ∘ f) :=
  ℳ.prodScalar.mem_convex h_epigraph_closed h_epigraph_convex
    (f := fun x ↦ (f x, φ (f x))) ⟨hf, hφf⟩ (fun x ↦ ⟨hfs x, le_rfl⟩) |>.2

/-- A generalization of Jensen's inequality by McShane. -/
theorem map_mean_le (hs : IsClosed s) (hφ : ConvexOn ℝ s φ) (hφc : ContinuousOn φ s)
    (hf : f ∈ ℳ.ℒ) (hfs : ∀ x, f x ∈ s) (hφf : φ ∘ f ∈ ℳ.L) :
    φ (ℳ f) ≤ ℳ.toLinearMean (φ ∘ f) :=
  ℳ.map_mean_le_of_epigraph (hs.epigraph hφc) hφ.convex_epigraph hf hfs hφf

namespace ConegligiblyInvariant

variable [ℳ.conegligible.NeBot] {ℳ} (hℳ : ℳ.ConegligiblyInvariant)

include hℳ

theorem mem_convex (hs₁ : IsClosed s) (hs₂ : Convex ℝ s)
    (hf : f ∈ ℳ.ℒ) (hfs : ∀ᶠ x in ℳ.conegligible, f x ∈ s) :
    ℳ f ∈ s := by
  obtain ⟨f', hf', hff', h⟩ := hℳ.exists_of_eventually hf hfs
  rw [hℳ.apply_eq hf hff']
  exact ℳ.mem_convex hs₁ hs₂ (hℳ.mem hf hff') h

theorem map_mean_le_of_epigraph
    (h_epigraph_closed : IsClosed {p : B × ℝ | p.1 ∈ s ∧ φ p.1 ≤ p.2})
    (h_epigraph_convex : Convex ℝ {p : B × ℝ | p.1 ∈ s ∧ φ p.1 ≤ p.2})
    (hf : f ∈ ℳ.ℒ) (hfs : ∀ᶠ x in ℳ.conegligible, f x ∈ s) (hφf : φ ∘ f ∈ ℳ.L) :
    φ (ℳ f) ≤ ℳ.toLinearMean (φ ∘ f) :=
  hℳ.prod_scalar.mem_convex h_epigraph_closed h_epigraph_convex
    (f := fun x ↦ (f x, φ (f x))) ⟨hf, hφf⟩ (by simpa) |>.2

/-- A generalization of Jensen's inequality by McShane. -/
theorem map_mean_le (hs : IsClosed s) (hφ : ConvexOn ℝ s φ) (hφc : ContinuousOn φ s)
    (hf : f ∈ ℳ.ℒ) (hfs : ∀ᶠ x in ℳ.conegligible, f x ∈ s) (hφf : φ ∘ f ∈ ℳ.L) :
    φ (ℳ f) ≤ ℳ.toLinearMean (φ ∘ f) :=
  hℳ.map_mean_le_of_epigraph (hs.epigraph hφc) hφ.convex_epigraph hf hfs hφf

end ConegligiblyInvariant

end LocallyConvexSpace

namespace FiniteDimensional

variable [NormedAddCommGroup B] [NormedSpace ℝ B]

private lemma helper₁ (s : Set B) (hs : s ⊆ vectorSpan ℝ s) :
  vectorSpan ℝ ((Subtype.val : vectorSpan ℝ s → B) ⁻¹' s) = ⊤ :=
  eq_top_iff.2 fun ⟨x, hx⟩ _ ↦ Submodule.span_induction
    (fun _ ⟨a, ha, b, hb, h⟩ ↦ Submodule.subset_span ⟨⟨a, hs ha⟩, ha, ⟨b, hs hb⟩, hb, h ▸ rfl⟩)
    (Submodule.zero_mem _)
    (fun _ _ _ _ hx hy ↦ Submodule.add_mem _ hx hy)
    (fun _ _ _ hx ↦ Submodule.smul_mem _ _ hx) hx

variable {ℳ : ExtendedLinearMean E ℝ B} (hℳ : ℳ.ConegligiblyInvariant)
  [ℳ.conegligible.NeBot] {s : Set B} [FiniteDimensional ℝ (vectorSpan ℝ s)] {f : E → B}

include hℳ

open Module LinearMap

open scoped Pointwise Set.Notation

private lemma mem_convex_aux (hs_convex : Convex ℝ s)
    (hf : f ∈ ℳ.ℒ) (hfs : ∀ᶠ x in ℳ.conegligible, f x ∈ s)
    {d : ℕ} (hd : d = finrank ℝ (vectorSpan ℝ s)) : ℳ f ∈ s := by
  induction d using Nat.strong_induction_on generalizing s with
  | ind d h_ind =>
    by_contra h
    rw [hd] at h_ind
    have hℳfs : ℳ f ∈ closure s := hℳ.mem_convex isClosed_closure hs_convex.closure hf <|
      hfs.mono fun _ h ↦ subset_closure h
    -- let p be the vector subspace of the differences in s
    set p := vectorSpan ℝ s with hp
    -- let s₀ be s shifted by ℳ f
    let s₀ : Set B := ((· - ℳ f) '' s)
    -- since ℳ f ∈ closure s and p is closed itself, s₀ ⊆ p
    have hs₀p : s₀ ⊆ p := by
      rw [← p.isClosed_of_finiteDimensional.closure_eq]
      apply subset_trans ?_ (closure_mono Submodule.subset_span)
      change _ ⊆ closure (s - s)
      rw [sub_eq_add_neg]
      apply subset_trans ?_ (vadd_set_closure_subset _ _)
      change _ ⊆ closure s + _
      rw [← neg_closure, ← sub_eq_add_neg]
      rintro x ⟨a, ha, rfl⟩
      apply Set.sub_mem_sub (subset_closure ha) hℳfs
    have hs₀ : s₀ = (AffineEquiv.vaddConst ℝ (- ℳ f)).toAffineMap '' s :=
      Set.image_congr fun _ _ ↦ sub_eq_add_neg ..
    -- s₀ as a subset of p
    let sₚ : Set p := ↑p ↓∩ s₀
    have hsₚ_convex : Convex ℝ sₚ := by
      refine Convex.linear_preimage ?_ p.subtype
      rw [hs₀]
      apply hs_convex.affine_image
    -- 0 ∉ interior sₚ as ℳ f ∉ s
    have h0sₚ : 0 ∉ interior sₚ := by
      apply Set.notMem_subset interior_subset
      unfold sₚ s₀
      rintro ⟨a, has, ha⟩
      rw [p.coe_zero, sub_eq_zero] at ha
      exact h (ha ▸ has)
    have hs_nonempty := Set.Nonempty.of_closure ⟨_, hℳfs⟩
    have hp' : p = vectorSpan ℝ s₀ := by
      rw [hs₀, ← AffineMap.map_vectorSpan]
      simpa
    have hsₚ_nonempty : (interior sₚ).Nonempty := by
      rw [hsₚ_convex.interior_nonempty_iff_affineSpan_eq_top]
      rw [AffineSubspace.affineSpan_eq_top_iff_vectorSpan_eq_top_of_nonempty]
      · unfold sₚ
        rw [hp'] at hs₀p ⊢
        apply helper₁ _ hs₀p
      · rwa [Subtype.preimage_coe_nonempty, Set.inter_eq_self_of_subset_right hs₀p,
          Set.image_nonempty]
    obtain ⟨l, hl⟩ := geometric_hahn_banach_point_open hsₚ_convex.interior isOpen_interior h0sₚ
    rw [map_zero] at hl
    have hls₀ : ∀ b, (h : b ∈ s₀) → 0 ≤ l ⟨b, hs₀p h⟩ := by
      intro b h
      apply le_on_closure (fun b h ↦ (hl b h).le) continuous_zero.continuousOn
        l.continuous_of_finiteDimensional.continuousOn
      rw [hsₚ_convex.closure_interior_eq_closure_of_nonempty_interior hsₚ_nonempty]
      exact subset_closure h
    have hl0 : l.toLinearMap ≠ 0 := by
      intro hl0
      obtain ⟨x, hx⟩ := hsₚ_nonempty
      have : 0 < l.toLinearMap _ := hl x hx
      rw [hl0, LinearMap.zero_apply] at this
      exact this.ne rfl
    -- let q be the kernel of l shifted by ℳ f
    set q := AffineSubspace.mk' (ℳ f) ((ker l.toLinearMap).map p.subtype) with hq
    have hfq : ∀ᶠ x in ℳ.conegligible, f x ∈ q := by
      obtain ⟨f', hf', hff', hf's⟩ := hℳ.exists_of_eventually hf hfs
      apply hff'.mp
      unfold Filter.Eventually
      rw [ℳ.mem_conegligible]
      obtain ⟨l', hl'⟩ := l.exist_extension_of_finiteDimensional_range
      set g := l' ∘ f' - l' (ℳ f) • 1 with hg
      have hfp : ∀ a, f' a - ℳ f ∈ s₀ := fun a ↦ Set.mem_image_of_mem (· - ℳ f) (hf's a)
      have hgl : ∀ a, g a = l ⟨f' a - ℳ f, hs₀p (hfp a)⟩ := by
        intro a
        simp [hl', hg]
      use g, ℳ.sub_mem (ℳ.comp_mem _ hf') (ℳ.smul_mem _ ℳ.one_mem)
      refine ⟨?_, ?_, ?_⟩
      · intro a
        rw [hgl]
        exact hls₀ _ (hfp a)
      · simp only [Set.mem_ofPred_eq, Classical.not_imp, and_imp]
        intro a hfa hfaq
        rw [hfa] at *
        rw [hgl]
        apply lt_of_le_of_ne' (hls₀ _ (hfp a))
        intro h
        exact hfaq <| (ker l.toLinearMap).mem_map_of_mem h
      · rw [hg, ℳ.map_sub (ℳ.comp_mem _ hf') (ℳ.smul_mem _ ℳ.one_mem),
          ℳ.map_comp _ hf', hℳ.apply_eq hf hff', ℳ.map_smul _ ℳ.one_mem,
          ℳ.map_one, smul_eq_mul, mul_one, sub_self]
    have hqs : vectorSpan ℝ (q ∩ s) ≤ (ker l.toLinearMap).map p.subtype  :=
      calc _ ≤ vectorSpan ℝ (q : Set B) := vectorSpan_mono _ Set.inter_subset_left
        _ = _ := by rw [hq, ← AffineSubspace.direction_eq_vectorSpan, AffineSubspace.direction_mk']
    have := Submodule.finiteDimensional_of_le hqs
    refine h <| h_ind _ ?_ (s := q ∩ s) (q.convex.inter hs_convex) (hfq.and hfs) rfl |>.2
    rw [← Dual.finrank_ker_add_one_of_ne_zero hl0, Nat.lt_add_one_iff]
    exact (Submodule.finrank_mono hqs).trans (Submodule.finrank_map_le p.subtype _)

theorem mem_convex (hs_convex : Convex ℝ s) (hf : f ∈ ℳ.ℒ)
    (hfs : ∀ᶠ x in ℳ.conegligible, f x ∈ s) : ℳ f ∈ s :=
  mem_convex_aux hℳ hs_convex hf hfs rfl

variable {φ : B → ℝ}

theorem map_mean_le_of_epigraph
    (h_epigraph_convex : Convex ℝ {p : B × ℝ | p.1 ∈ s ∧ φ p.1 ≤ p.2})
    (hf : f ∈ ℳ.ℒ) (hfs : ∀ᶠ x in ℳ.conegligible, f x ∈ s) (hφf : φ ∘ f ∈ ℳ.L) :
    φ (ℳ f) ≤ ℳ.toLinearMean (φ ∘ f) :=
  have : (vectorSpan ℝ s).prod (⊤ : Submodule ℝ ℝ) |>.FG := by
    apply Submodule.FG.prod
    · rwa [Submodule.fg_iff_finiteDimensional]
    · exact Finite.fg_top
  have : FiniteDimensional ℝ ↥(vectorSpan ℝ {p : B × ℝ | p.1 ∈ s ∧ φ p.1 ≤ p.2}) := by
    rw [Submodule.fg_iff_finiteDimensional] at this
    apply Submodule.finiteDimensional_of_le (S₂ := (vectorSpan ℝ s).prod ⊤)
    rw [← Submodule.span_univ]
    refine le_trans ?_ (Submodule.span_prod_le _ _)
    rw [Set.prod_univ]
    apply Submodule.span_mono
    rw [Set.vsub_subset_iff]
    intro p hp q hq
    exact ⟨p.1, hp.1, q.1, hq.1, rfl⟩
  mem_convex (f := fun x ↦ (f x, φ (f x))) hℳ.prod_scalar h_epigraph_convex ⟨hf, hφf⟩
    (by simpa) |>.2

/-- A generalization of Jensen's inequality by Guseinov. -/
theorem map_mean_le (hφ : ConvexOn ℝ s φ)
    (hf : f ∈ ℳ.ℒ) (hfs : ∀ᶠ x in ℳ.conegligible, f x ∈ s)
    (hφf : φ ∘ f ∈ ℳ.L) : φ (ℳ f) ≤ ℳ.toLinearMean (φ ∘ f) :=
  map_mean_le_of_epigraph hℳ hφ.convex_epigraph hf hfs hφf

end FiniteDimensional

end ExtendedLinearMean

namespace LinearMean

variable (M : LinearMean E ℝ) {s : Set ℝ} {f : E → ℝ} {φ : ℝ → ℝ}

theorem mem_convex (hs₁ : IsClosed s) (hs₂ : Convex ℝ s)
    (hf : f ∈ M.L) (hfs : ∀ x, f x ∈ s) : M f ∈ s :=
  M.toExtendedLinearMean.mem_convex hs₁ hs₂ hf hfs

theorem map_mean_le_of_epigraph
    (h_epigraph_closed : IsClosed {p : ℝ × ℝ | p.1 ∈ s ∧ φ p.1 ≤ p.2})
    (h_epigraph_convex : Convex ℝ {p : ℝ × ℝ | p.1 ∈ s ∧ φ p.1 ≤ p.2})
    (hf : f ∈ M.L) (hfs : ∀ x, f x ∈ s) (hφf : φ ∘ f ∈ M.L) :
    φ (M f) ≤ M (φ ∘ f) :=
  M.toExtendedLinearMean.map_mean_le_of_epigraph h_epigraph_closed h_epigraph_convex hf hfs hφf

/-- A generalization of Jensen's inequality by McShane. -/
theorem map_mean_le (hs : IsClosed s) (hφ : ConvexOn ℝ s φ) (hφc : ContinuousOn φ s)
    (hf : f ∈ M.L) (hfs : ∀ x, f x ∈ s) (hφf : φ ∘ f ∈ M.L) :
    φ (M f) ≤ M (φ ∘ f) :=
  M.toExtendedLinearMean.map_mean_le hs hφ hφc hf hfs hφf

namespace ConegligiblyInvariant

variable (hM : M.ConegligiblyInvariant) [M.conegligible.NeBot]

include hM

theorem mem_convex (hs : Convex ℝ s)
    (hf : f ∈ M.L) (hfs : ∀ᶠ x in M.conegligible, f x ∈ s) : M f ∈ s :=
  ExtendedLinearMean.FiniteDimensional.mem_convex hM.toExtendedLinearMean hs hf hfs

theorem map_mean_le_of_epigraph
    (h_epigraph_convex : Convex ℝ {p : ℝ × ℝ | p.1 ∈ s ∧ φ p.1 ≤ p.2})
    (hf : f ∈ M.L) (hfs : ∀ᶠ x in M.conegligible, f x ∈ s) (hφf : φ ∘ f ∈ M.L) :
    φ (M f) ≤ M (φ ∘ f) :=
  ExtendedLinearMean.FiniteDimensional.map_mean_le_of_epigraph hM.toExtendedLinearMean
    h_epigraph_convex hf hfs hφf

/-- A generalization of Jensen's inequality by Guseinov. -/
theorem map_mean_le (hφ : ConvexOn ℝ s φ)
    (hf : f ∈ M.L) (hfs : ∀ᶠ x in M.conegligible, f x ∈ s) (hφf : φ ∘ f ∈ M.L) :
    φ (M f) ≤ M (φ ∘ f) :=
  ExtendedLinearMean.FiniteDimensional.map_mean_le hM.toExtendedLinearMean
    hφ hf hfs hφf

end ConegligiblyInvariant

end LinearMean
