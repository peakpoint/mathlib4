/-
Copyright (c) 2026 Tian Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tian Chen
-/

module

public import Mathlib.Analysis.LocallyConvex.Separation
public import Mathlib.Topology.Algebra.Module.Equiv.Prod
public import Mathlib.Topology.Algebra.Module.Equiv.Submodule

@[expose] public section

universe u

variable {E : Type u} {R B : Type*}

section Defs

variable (E R) [Semiring R] [Preorder R]

/-- This structure contains the data of a conditional linear mean. -/
structure CondLinearMean where
  /-- The mean function. -/
  toMean : (E → R) → (E → R)
  conegligible : Filter E
  /-- The domain of the linear mean. -/
  L : Set (E → R)
  mem_conegligible : ∀ s : Set E,
    (∃ f ∈ L, 0 ≤ f ∧ (∀ x ∉ s, 0 < f x) ∧ toMean f =ᶠ[conegligible] 0) → s ∈ conegligible
  add_mem : ∀ {a b}, a ∈ L → b ∈ L → a + b ∈ L
  smul_mem : ∀ (c : R) {a}, a ∈ L → c • a ∈ L
  map_add' : ∀ {a b}, a ∈ L → b ∈ L → toMean (a + b) =ᶠ[conegligible] toMean a + toMean b
  map_smul' : ∀ (c : R) {a}, a ∈ L → toMean (c • a) =ᶠ[conegligible] c • toMean a
  one_mem : 1 ∈ L
  map_one' : toMean 1 =ᶠ[conegligible] 1
  monotoneOn' : ∀ ⦃a⦄ (_ : a ∈ L) ⦃b⦄ (_ : b ∈ L),
    a ≤ᶠ[conegligible] b → toMean a ≤ᶠ[conegligible] toMean b

namespace CondLinearMean

variable {E R} (M : CondLinearMean E R)

@[coe]
def toFun : (E → R) → (E → R) := M.toMean

instance instCoeFun : CoeFun (CondLinearMean E R) (fun _ => (E → R) → (E → R)) :=
  ⟨CondLinearMean.toFun⟩

variable {a b : E → R}

theorem map_add : a ∈ M.L → b ∈ M.L → M (a + b) =ᶠ[M.conegligible] M a + M b := M.map_add'

theorem map_smul (c : R) : a ∈ M.L → M (c • a) =ᶠ[M.conegligible] c • M a := M.map_smul' c

theorem map_one : M 1 =ᶠ[M.conegligible] 1 := M.map_one'

-- theorem monotoneOn : MonotoneOn M M.L := M.monotoneOn'

theorem zero_mem : 0 ∈ M.L :=
  zero_smul R (1 : E → R) ▸ M.smul_mem 0 M.one_mem

theorem map_zero : M 0 =ᶠ[M.conegligible] 0 :=
  by simpa only [zero_smul] using M.map_smul 0 M.one_mem

theorem monotoneOn : ∀ ⦃a⦄ (_ : a ∈ M.L) ⦃b⦄ (_ : b ∈ M.L),
  a ≤ᶠ[M.conegligible] b → M a ≤ᶠ[M.conegligible] M b := M.monotoneOn'

-- def Monotone : Prop := ∀ ⦃a⦄ (_ : a ∈ M.L) ⦃b⦄ (_ : b ∈ M.L),
--   a ≤ᶠ[M.conegligible] b → M a ≤ᶠ[M.conegligible] M b

end CondLinearMean

end Defs

namespace CondLinearMean

section Ring

variable [Ring R] [Preorder R]
  (M : CondLinearMean E R) {a b : E → R}

theorem neg_mem : a ∈ M.L → -a ∈ M.L := by
  intro ha
  rw [← neg_one_smul R]
  exact M.smul_mem _ ha

theorem map_neg : a ∈ M.L → M (-a) =ᶠ[M.conegligible] -M a := by
  intro ha
  have := M.map_smul (-1) ha
  rw [← neg_one_smul R]
  filter_upwards [this]
  simp only [neg_smul, one_smul, Pi.smul_apply, smul_eq_mul, neg_mul, one_mul, Pi.neg_apply,
    imp_self, implies_true]

theorem sub_mem : a ∈ M.L → b ∈ M.L → a - b ∈ M.L := by
  intro ha hb
  rw [sub_eq_add_neg]
  apply M.add_mem ha (M.neg_mem hb)

theorem map_sub : a ∈ M.L → b ∈ M.L → M (a - b) =ᶠ[M.conegligible] M a - M b := by
  intro ha hb
  rw [sub_eq_add_neg]
  filter_upwards [M.map_add ha (M.neg_mem hb), M.map_neg hb] with x h₁ h₂
  simp [h₁, h₂, sub_eq_add_neg]

theorem const_mem (c : R) : (fun _ ↦ c) ∈ M.L := by
  convert M.smul_mem c M.one_mem
  simp

theorem map_const (c : R) : M (fun _ ↦ c) =ᶠ[M.conegligible] (fun _ ↦ c) := by
  have := M.map_smul c M.one_mem
  grw [M.map_one] at this
  simpa [Pi.smul_def] using this

end Ring

end CondLinearMean

section Defs

variable (E R B) [TopologicalSpace R] [TopologicalSpace B]
  [Semiring R] [Preorder R]
  [AddCommMonoid B] [Module R B]

/-- An extension of a linear mean to an `R`-module `B`.

This generalizes the idea that a mean `M : LinearMean E R` can be extended to
`ι → R` by `ℳ f = fun i ↦ M i` by noticing that the projections
`fun f ↦ f i` are a (continuous) linear map.
-/
structure ExtendedCondLinearMean extends CondLinearMean E R where
  ℒ : Set (E → B)
  toExtendedMean : (E → B) → (E → B)
  map_comp' : ∀ l : B →L[R] R, ∀ f ∈ ℒ, l ∘ f ∈ L ∧
    toMean (l ∘ f) =ᶠ[conegligible] l ∘ (toExtendedMean f)


namespace ExtendedCondLinearMean

open CondLinearMean

variable {E R B} (ℳ : ExtendedCondLinearMean E R B)

@[coe]
def toFun := ℳ.toExtendedMean

instance : CoeFun (ExtendedCondLinearMean E R B) (fun _ => (E → B) → E → B) :=
  ⟨ExtendedCondLinearMean.toFun⟩

protected lemma comp_mem (l : B →L[R] R) {f : E → B} (hf : f ∈ ℳ.ℒ) : l ∘ f ∈ ℳ.L :=
  (ℳ.map_comp' l f hf).1

protected lemma map_comp (l : B →L[R] R) {f : E → B} (hf : f ∈ ℳ.ℒ) :
    ℳ.toCondLinearMean (l ∘ f) =ᶠ[ℳ.conegligible] l ∘ (ℳ f) :=
  (ℳ.map_comp' l f hf).2

variable {C} [TopologicalSpace C] [AddCommMonoid C] [Module R C]

def equiv (e : B ≃L[R] C) : ExtendedCondLinearMean E R C := {
  ℳ.toCondLinearMean with
  ℒ := { f | e.symm ∘ f ∈ ℳ.ℒ }
  toExtendedMean f := e ∘ ℳ (e.symm ∘ f)
  map_comp' l f hf := by
    have : l ∘ f ∈ ℳ.L := by
      convert ℳ.comp_mem (l ∘SL e.toContinuousLinearMap) hf
      ext
      simp
    refine ⟨this, ?_⟩
    convert ℳ.map_comp (l ∘SL e.toContinuousLinearMap) hf
    · congr
      ext
      simp
    · ext
      simp
}

end ExtendedCondLinearMean

end Defs


namespace ExtendedCondLinearMean

section OrderedSemiring

variable [Semiring R] [PartialOrder R] --[IsOrderedRing R]
  [AddCommMonoid B] [Module R B] [TopologicalSpace R] [TopologicalSpace B]
  (ℳ : ExtendedCondLinearMean E R B)

structure ConegligiblyInvariant where
  mem_and_apply_eq : ∀ ⦃f⦄, f ∈ ℳ.ℒ → ∀ ⦃g⦄, f =ᶠ[ℳ.conegligible] g →
    g ∈ ℳ.ℒ ∧ ℳ f =ᶠ[ℳ.conegligible] ℳ g
  mem_L_and_apply_M_eq : ∀ ⦃f⦄, f ∈ ℳ.L → ∀ ⦃g⦄, f =ᶠ[ℳ.conegligible] g →
    g ∈ ℳ.L ∧ ℳ.toCondLinearMean f =ᶠ[ℳ.conegligible] ℳ.toCondLinearMean g

namespace ConegligiblyInvariant

variable {ℳ} (h : ℳ.ConegligiblyInvariant)

include h

theorem mem_L : ∀ ⦃f⦄, f ∈ ℳ.L → ∀ ⦃g⦄, f =ᶠ[ℳ.conegligible] g → g ∈ ℳ.L :=
  fun _ hf _ hg ↦ (h.mem_L_and_apply_M_eq hf hg).1

theorem apply_M_eq : ∀ ⦃f⦄, f ∈ ℳ.L → ∀ ⦃g⦄, f =ᶠ[ℳ.conegligible] g →
    ℳ.toCondLinearMean f =ᶠ[ℳ.conegligible] ℳ.toCondLinearMean g :=
  fun _ hf _ hg ↦ (h.mem_L_and_apply_M_eq hf hg).2

theorem mem : ∀ ⦃f⦄, f ∈ ℳ.ℒ → ∀ ⦃g⦄, f =ᶠ[ℳ.conegligible] g → g ∈ ℳ.ℒ :=
  fun _ hf _ hg ↦ (h.mem_and_apply_eq hf hg).1

theorem apply_eq : ∀ ⦃f⦄, f ∈ ℳ.ℒ → ∀ ⦃g⦄, f =ᶠ[ℳ.conegligible] g → ℳ f =ᶠ[ℳ.conegligible] ℳ g :=
  fun _ hf _ hg ↦ (h.mem_and_apply_eq hf hg).2

variable [ℳ.conegligible.NeBot]

theorem exists_of_eventually {f} {p : B → Prop} (hfL : f ∈ ℳ.ℒ)
    (hf : ∀ᶠ x in ℳ.conegligible, p (f x)) : ∃ g ∈ ℳ.ℒ,
      f =ᶠ[ℳ.conegligible] g ∧ ∀ x, p (g x) := by
  obtain ⟨a, ha⟩ := hf.exists
  classical
  have hff' : f =ᶠ[ℳ.conegligible] fun x ↦ if p (f x) then f x else f a :=
    hf.mono fun x hx ↦ (ite_eq_left hx).symm
  refine ⟨_, h.mem hfL hff', hff', ?_⟩
  intro
  split_ifs
  all_goals assumption

theorem exists_of_eventually_L {f} {p : R → Prop} (hfL : f ∈ ℳ.L)
    (hf : ∀ᶠ x in ℳ.conegligible, p (f x)) : ∃ g ∈ ℳ.L, f =ᶠ[ℳ.conegligible] g ∧ ∀ x, p (g x) := by
  obtain ⟨a, ha⟩ := hf.exists
  classical
  have hff' : f =ᶠ[ℳ.conegligible] fun x ↦ if p (f x) then f x else f a :=
    hf.mono fun x hx ↦ (ite_eq_left hx).symm
  refine ⟨_, h.mem_L hfL hff', hff', ?_⟩
  intro
  split_ifs
  all_goals assumption

end ConegligiblyInvariant

end OrderedSemiring

section prodScalar

variable [CommSemiring R] [PartialOrder R] [AddCommMonoid B] [Module R B]
  [TopologicalSpace R] [TopologicalSpace B]
  (ℳ : ExtendedCondLinearMean E R B)

variable [ContinuousAdd R]

/-- An extended linear mean on `B` can be extended to `B × R` -/
def prodScalar : ExtendedCondLinearMean E R (B × R) := {
  ℳ.toCondLinearMean with
  ℒ := { f | Prod.fst ∘ f ∈ ℳ.ℒ ∧ Prod.snd ∘ f ∈ ℳ.L }
  toExtendedMean f x := (ℳ (Prod.fst ∘ f) x, ℳ.toCondLinearMean (Prod.snd ∘ f) x)
  map_comp' := by
    rintro l g ⟨hgℒ, hgL⟩
    set l₁ : B →L[R] R := l.comp (.inl R B R) with hl₁
    set l₂ : R →L[R] R := l.comp (.inr R B R) with hl₂
    have hl : l₁.coprod l₂ = l := by
      rw [hl₁, hl₂]
      ext x
      all_goals simp
    rw [← hl]
    have h₂ (f : E → R) : l₂ ∘ f = l₂.toLinearMap 1 • f := by
      ext x
      rw [Pi.smul_apply, smul_eq_mul]
      exact (Dual.apply_one_mul_eq _ _).symm
    have hl₁L : l₁ ∘ Prod.fst ∘ g ∈ ℳ.L := ℳ.comp_mem l₁ hgℒ
    have hl₂L : l₂ ∘ Prod.snd ∘ g ∈ ℳ.L := by
      rw [h₂]
      exact ℳ.smul_mem _ hgL
    refine ⟨ℳ.add_mem hl₁L hl₂L, ?_⟩
    change ℳ.toCondLinearMean (l₁ ∘ Prod.fst ∘ g + l₂ ∘ Prod.snd ∘ g) =ᶠ[_] _
    have : ℳ.toCondLinearMean (l₂ ∘ Prod.snd ∘ g)
        =ᶠ[ℳ.conegligible] l₂ ∘ ℳ.toCondLinearMean (Prod.snd ∘ g) := by
      rw [h₂, h₂]
      exact ℳ.map_smul _ hgL
    grw [ℳ.map_add hl₁L hl₂L, ℳ.map_comp l₁ hgℒ, this]
    rfl
}

lemma prodScalar_apply (f) : ℳ.prodScalar f =
  fun x ↦ (ℳ (Prod.fst ∘ f) x, ℳ.toCondLinearMean (Prod.snd ∘ f) x) := by rfl

lemma prodScalar_conegligible : ℳ.prodScalar.conegligible = ℳ.conegligible := rfl

namespace ConegligiblyInvariant

variable {ℳ}

theorem prodScalar (hℳ : ℳ.ConegligiblyInvariant) : ℳ.prodScalar.ConegligiblyInvariant where
  mem_and_apply_eq := fun f ⟨hf₁, hf₂⟩ g hg ↦
    have ⟨hg₁, hf₁⟩ := hℳ.mem_and_apply_eq hf₁ (hg.fun_comp _)
    have ⟨hg₂, hf₂⟩ := hℳ.mem_L_and_apply_M_eq hf₂ (hg.fun_comp _)
    ⟨⟨hg₁, hg₂⟩, by filter_upwards [hf₁, hf₂] with x h₁ h₂; exact Prod.ext h₁ h₂⟩
  mem_L_and_apply_M_eq := hℳ.mem_L_and_apply_M_eq

instance [ℳ.conegligible.NeBot] : ℳ.prodScalar.conegligible.NeBot := by assumption

end ConegligiblyInvariant

end prodScalar

section restrict

variable [CommSemiring R] [PartialOrder R] [AddCommMonoid B] [Module R B]
  [TopologicalSpace R] [TopologicalSpace B]
  (ℳ : ExtendedCondLinearMean E R B)

structure Restrict (C : Submodule R B) where
  restrict' : ExtendedCondLinearMean E R C
  toCondLinearMean_restrict' :
    restrict'.toCondLinearMean = ℳ.toCondLinearMean
  mem_and_map_eq' : ∀ ⦃g : E → C⦄, Subtype.val ∘ g ∈ ℳ.ℒ →
    g ∈ restrict'.ℒ ∧ ℳ (Subtype.val ∘ g) =ᶠ[ℳ.conegligible] Subtype.val ∘ restrict' g

namespace Restrict

variable {ℳ} {C : Submodule R B} (r : ℳ.Restrict C)

def restrict : ExtendedCondLinearMean E R C := {
  ℳ.toCondLinearMean with
  ℒ := r.restrict'.ℒ
  toExtendedMean := r.restrict'.toExtendedMean
  map_comp' l f hf := by
    rw [← r.toCondLinearMean_restrict']
    exact r.restrict'.map_comp' l f hf
}

theorem mem_of_subtype_val_comp_mem :
    ∀ ⦃g : E → C⦄, Subtype.val ∘ g ∈ ℳ.ℒ → g ∈ r.restrict.ℒ :=
  fun _ hg ↦ r.mem_and_map_eq' hg |>.1

theorem subtype_val_comp : ∀ ⦃g : E → C⦄, Subtype.val ∘ g ∈ ℳ.ℒ →
    ℳ (Subtype.val ∘ g) =ᶠ[ℳ.conegligible] Subtype.val ∘ r.restrict g :=
  fun _ hg ↦ r.mem_and_map_eq' hg |>.2

variable [ContinuousAdd R] [ContinuousAdd B] [ContinuousConstSMul R B]
  [ContinuousConstSMul R R]

def prodScalar : ℳ.prodScalar.Restrict (C.prod ⊤) :=
  let e := ContinuousLinearEquiv.ofIsHomeomorph (C.prodEquiv ⊤)
    (Homeomorph.Set.prod _ _).isHomeomorph
  let e' := e.trans <| ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl R C)
    Submodule.topContEquiv
  {
    restrict' := r.restrict.prodScalar.equiv e'.symm
    toCondLinearMean_restrict' := rfl
    mem_and_map_eq' g hg := by
      constructor
      · constructor
        · have := r.mem_of_subtype_val_comp_mem
          apply this
          exact hg.1
        · exact hg.2
      · have hg₁' : Subtype.val ∘ Prod.fst ∘ e'.toFun ∘ g ∈ ℳ.ℒ := hg.1
        apply Filter.EventuallyEq.prodMk
        · exact r.subtype_val_comp hg₁'
        · exact ℳ.prodScalar.map_comp (ContinuousLinearMap.snd R B R) hg
  }

end Restrict

end restrict

section LocallyConvexSpace

variable [TopologicalSpace B] [AddCommGroup B] [IsTopologicalAddGroup B]
  [Module ℝ B] [ContinuousSMul ℝ B] [LocallyConvexSpace ℝ B]
  (ℳ : ExtendedCondLinearMean E ℝ B) [CountableInterFilter ℳ.conegligible]
  {s : Set B} {f : E → B} {φ : B → ℝ}

theorem mem_convex [HereditarilyLindelofSpace B] (hs₁ : IsClosed s) (hs₂ : Convex ℝ s)
    (hf : f ∈ ℳ.ℒ) (hfs : ∀ᶠ x in ℳ.conegligible, f x ∈ s) :
      ∀ᶠ x in ℳ.conegligible, ℳ f x ∈ s := by
  obtain ⟨l, c, h⟩ := RCLike.iInter_countable_halfSpaces_eq (𝕜 := ℝ) hs₂ hs₁
  simp only [RCLike.re_to_real] at h
  rw [Set.ext_iff] at h
  simp only [Set.mem_iInter, Set.mem_ofPred_eq] at h
  simp_rw [← h]
  rw [eventually_countable_forall]
  intro i
  change (l i ∘ ℳ f) ≤ᶠ[ℳ.conegligible] (fun t ↦ c i)
  have := ℳ.monotoneOn (ℳ.comp_mem (l i) hf) (ℳ.const_mem (c i))
    (by filter_upwards [hfs] with x hx; exact h (f x) |>.2 hx i)
  apply this.congr (ℳ.map_comp (l i) hf)
  apply ℳ.map_const

theorem mem_convex_of_restrict
    (hs₁ : IsClosed s) (hs₂ : Convex ℝ s)
    (hf : f ∈ ℳ.ℒ) (hfs : ∀ᶠ x in ℳ.conegligible, f x ∈ s)
    {C : ClosedSubmodule ℝ B} [HereditarilyLindelofSpace C]
    (r : ℳ.Restrict C)
    (hℳ : ℳ.ConegligiblyInvariant)
    (hfC : ∀ᶠ x in ℳ.conegligible, f x ∈ C) :
      ∀ᶠ x in ℳ.conegligible, ℳ f x ∈ s := by
  classical
  let f' : E → C := fun a => if h : f a ∈ C then ⟨f a, h⟩ else 0
  let ℳC := r.restrict
  have hff' : f =ᶠ[ℳ.conegligible] Subtype.val ∘ f' := by
    apply hfC.mono
    intro x hx
    simp [f', hx]
  have hsf' : Subtype.val ∘ f' ∈ ℳ.ℒ := hℳ.mem hf hff'
  have lem1 : f =ᶠ[ℳ.conegligible] Subtype.val ∘ f' := by
    filter_upwards [hfC] with a ha
    simp_all [f']
  have lem2 : ∀ᶠ a in ℳ.conegligible, f' a ∈ C.subtypeL ⁻¹' s := by
    filter_upwards [hfC, hfs] with a ha hs
    simpa [f', ha]
  have : CountableInterFilter ℳC.conegligible := by assumption
  have hf' : f' ∈ ℳC.ℒ := r.mem_of_subtype_val_comp_mem hsf'
  have := ℳC.mem_convex (hs₁.preimage C.subtypeL.continuous)
    (hs₂.linear_preimage C.subtype) hf' lem2
  have hff' : ℳ f =ᶠ[ℳ.conegligible] ℳ (Subtype.val ∘ f') := hℳ.apply_eq hf hff'
  filter_upwards [this, r.subtype_val_comp hsf', hff']
  intro a ha ha' hfa
  simp only [Submodule.coe_subtypeL, Submodule.coe_subtype, Set.mem_preimage,
    Function.comp_apply] at ha ha'
  rw [← ha'] at ha
  rw [hfa]
  exact ha

theorem comp_mean_le
    (h_epigraph_closed : IsClosed {p : B × ℝ | p.1 ∈ s ∧ φ p.1 ≤ p.2})
    (h_epigraph_convex : Convex ℝ {p : B × ℝ | p.1 ∈ s ∧ φ p.1 ≤ p.2})
    (hf : f ∈ ℳ.ℒ) (hfs : ∀ᶠ x in ℳ.conegligible, f x ∈ s) (hφf : φ ∘ f ∈ ℳ.L)
    {C : ClosedSubmodule ℝ B} [SecondCountableTopology C]
    (r : ℳ.Restrict C)
    (hℳ : ℳ.ConegligiblyInvariant)
    (hfC : ∀ᶠ x in ℳ.conegligible, f x ∈ C) :
    φ ∘ (ℳ f) ≤ᶠ[ℳ.conegligible] ℳ.toCondLinearMean (φ ∘ f) := by
  have : CountableInterFilter ℳ.prodScalar.conegligible := by assumption
  have : SecondCountableTopology (C.prod (⊤ : Submodule ℝ ℝ)) :=
    Homeomorph.secondCountableTopology (Homeomorph.Set.prod _ _)
  have := ℳ.prodScalar.mem_convex_of_restrict h_epigraph_closed h_epigraph_convex
    (f := fun x ↦ (f x, φ (f x))) ⟨hf, hφf⟩ (C := ⟨C.prod ⊤, C.isClosed.prod (by simp)⟩)
    (by filter_upwards [hfs] with a ha; exact ⟨ha, le_rfl⟩)
    r.prodScalar hℳ.prodScalar
    (by filter_upwards [hfC] with a ha; exact ⟨ha, Set.mem_univ _⟩)
  filter_upwards [this] with a ha
  exact ha.2

end LocallyConvexSpace

end ExtendedCondLinearMean
