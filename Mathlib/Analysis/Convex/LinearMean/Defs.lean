/-
Copyright (c) 2026 Tian Chen. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Tian Chen
-/
module

public import Mathlib.Algebra.Order.Pi
public import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Basic

/-!
# Linear Means

Let `R` be an ordered (semi)ring. Given a unital submodule of functions `domain : Set (E → R)`, a
linear mean `M : (E → R) → R` is a monotonic (or isotonic) linear function on `domain`.

The means we consider are normalized so `M (1 : E → R) = (1 : R)`.
(TODO: make this a typeclass assumption instead?)

An example of a linear mean is `M f := ∫ x, f x ∂μ` with the domain `{ f | Integrable f μ }`
where `μ` is a probability measure.
-/

@[expose] public section

variable {E R B : Type*}

section Defs

variable (E R) [Semiring R] [Preorder R] [IsOrderedAddMonoid R]

/-- This structure contains the data of a linear mean. -/
structure LinearMean where
  /-- The mean function. -/
  toMean : (E → R) → R
  /-- The domain of the linear mean. -/
  L : Set (E → R) -- TODO: find a better name
  add_mem : ∀ {a b}, a ∈ L → b ∈ L → a + b ∈ L
  smul_mem : ∀ (c : R) {a}, a ∈ L → c • a ∈ L
  map_add' : ∀ {a b}, a ∈ L → b ∈ L → toMean (a + b) = toMean a + toMean b
  map_smul' : ∀ (c : R) {a}, a ∈ L → toMean (c • a) = c • toMean a
  one_mem : 1 ∈ L
  map_one' : toMean 1 = 1
  conegligible : Filter E := .comk
    (fun s ↦ ∃ f ∈ L, 0 ≤ f ∧ (∀ x ∈ s, 0 < f x) ∧ toMean f = 0)
    ⟨0, ⟨zero_smul R (1 : E → R) ▸ smul_mem 0 one_mem, le_rfl,
      fun _ h ↦ False.elim h, by simpa only [zero_smul] using map_smul' 0 one_mem⟩⟩
    (by
      rintro t ⟨f, hfL, h0f, hf, hMf⟩ s hst
      refine ⟨f, hfL, h0f, ?_, hMf⟩
      intro _ hs
      apply hf _ (hst hs))
    (by
      rintro s ⟨f, hfL, h0f, hf, hMf⟩ t ⟨g, hgL, h0g, hg, hMg⟩
      use f + g
      refine ⟨add_mem hfL hgL, add_nonneg h0f h0g, ?_, ?_⟩
      · intro x hx
        rcases hx with hxs | hxt
        · apply add_pos_of_pos_of_nonneg (hf _ hxs) (h0g x)
        · apply Right.add_pos_of_nonneg_of_pos (h0f x) (hg _ hxt)
      · rw [map_add' hfL hgL, hMf, hMg, add_zero])
  mem_conegligible' {s : Set E} : s ∈ conegligible ↔
    ∃ f ∈ L, 0 ≤ f ∧ (∀ x ∉ s, 0 < f x) ∧ toMean f = 0 := by rfl
  monotoneOn' : MonotoneOn toMean L

namespace LinearMean

section

variable {E R} (M : LinearMean E R)

@[coe]
def toFun : (E → R) → R := M.toMean

instance instCoeFun : CoeFun (LinearMean E R) (fun _ => (E → R) → R) := ⟨LinearMean.toFun⟩

variable {a b : E → R}

theorem map_add : a ∈ M.L → b ∈ M.L → M (a + b) = M a + M b := M.map_add'

theorem map_smul (c : R) : a ∈ M.L → M (c • a) = c • M a := M.map_smul' c

theorem map_one : M 1 = 1 := M.map_one'

theorem zero_mem : 0 ∈ M.L :=
  zero_smul R (1 : E → R) ▸ M.smul_mem 0 M.one_mem

theorem map_zero : M 0 = 0 :=
  by simpa only [zero_smul] using M.map_smul 0 M.one_mem

theorem monotoneOn : MonotoneOn M M.L := M.monotoneOn'

theorem mem_conegligible {s : Set E} : s ∈ M.conegligible ↔
    ∃ f ∈ M.L, 0 ≤ f ∧ (∀ x ∉ s, 0 < f x) ∧ M f = 0 := M.mem_conegligible'

end

variable {E R} (M : LinearMean E R)

structure ConegligiblyInvariant where
  mem_L_and_apply_M_eq : ∀ ⦃f⦄, f ∈ M.L → ∀ ⦃g⦄, f =ᶠ[M.conegligible] g →
    g ∈ M.L ∧ M f = M g

namespace ConegligiblyInvariant

variable {M}

theorem mem_L (h : M.ConegligiblyInvariant) :
    ∀ ⦃f⦄, f ∈ M.L → ∀ ⦃g⦄, f =ᶠ[M.conegligible] g → g ∈ M.L :=
  fun _ hf _ hg ↦ (h.mem_L_and_apply_M_eq hf hg).1

theorem apply_M_eq (h : M.ConegligiblyInvariant) :
    ∀ ⦃f⦄, f ∈ M.L → ∀ ⦃g⦄, f =ᶠ[M.conegligible] g → M f = M g :=
  fun _ hf _ hg ↦ (h.mem_L_and_apply_M_eq hf hg).2

end ConegligiblyInvariant

end LinearMean

variable (B) [TopologicalSpace R] [TopologicalSpace B]
  [AddCommMonoid B] [Module R B]

/-- An extension of a linear mean to an `R`-module `B`.

This generalizes the idea that a mean `M : LinearMean E R` can be extended to
`B := ι → R` by `ℳ f = fun i ↦ M (f · i)` by noticing that the projections
`fun f : ι → R ↦ f i` are (continuous) linear maps.
-/
structure ExtendedLinearMean extends LinearMean E R where
  ℒ : Set (E → B)
  toExtendedMean : (E → B) → B
  map_comp' : ∀ l : B →L[R] R, ∀ f ∈ ℒ, l ∘ f ∈ L ∧ toMean (l ∘ f) = l (toExtendedMean f)

namespace ExtendedLinearMean

open LinearMean

variable {E R B} (ℳ : ExtendedLinearMean E R B)

@[coe]
def toFun := ℳ.toExtendedMean

instance : CoeFun (ExtendedLinearMean E R B) (fun _ => (E → B) → B) :=
  ⟨ExtendedLinearMean.toFun⟩

protected lemma comp_mem (l : B →L[R] R) {f : E → B} (hf : f ∈ ℳ.ℒ) : l ∘ f ∈ ℳ.L :=
  (ℳ.map_comp' l f hf).1

protected lemma map_comp (l : B →L[R] R) {f : E → B} (hf : f ∈ ℳ.ℒ) :
    ℳ.toLinearMean (l ∘ f) = l (ℳ f) :=
  (ℳ.map_comp' l f hf).2

section OrderedSemiring

variable (ℳ : ExtendedLinearMean E R B)

structure ConegligiblyInvariant extends ℳ.toLinearMean.ConegligiblyInvariant where
  mem_and_apply_eq : ∀ ⦃f⦄, f ∈ ℳ.ℒ → ∀ ⦃g⦄, f =ᶠ[ℳ.conegligible] g → g ∈ ℳ.ℒ ∧ ℳ f = ℳ g
namespace ConegligiblyInvariant

variable {ℳ} (h : ℳ.ConegligiblyInvariant)

include h

theorem mem_L : ∀ ⦃f⦄, f ∈ ℳ.L → ∀ ⦃g⦄, f =ᶠ[ℳ.conegligible] g → g ∈ ℳ.L :=
  h.toConegligiblyInvariant.mem_L

theorem apply_M_eq : ∀ ⦃f⦄, f ∈ ℳ.L → ∀ ⦃g⦄, f =ᶠ[ℳ.conegligible] g →
    ℳ.toLinearMean f = ℳ.toLinearMean g :=
  fun _ hf _ hg ↦ (h.mem_L_and_apply_M_eq hf hg).2

theorem mem : ∀ ⦃f⦄, f ∈ ℳ.ℒ → ∀ ⦃g⦄, f =ᶠ[ℳ.conegligible] g → g ∈ ℳ.ℒ :=
  fun _ hf _ hg ↦ (h.mem_and_apply_eq hf hg).1

theorem apply_eq : ∀ ⦃f⦄, f ∈ ℳ.ℒ → ∀ ⦃g⦄, f =ᶠ[ℳ.conegligible] g → ℳ f = ℳ g :=
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


end ExtendedLinearMean

end Defs

namespace LinearMean

section Ring

variable [Ring R] [Preorder R] [IsOrderedAddMonoid R]
  (M : LinearMean E R) {a b : E → R}

theorem neg_mem : a ∈ M.L → -a ∈ M.L := by
  intro ha
  rw [← neg_one_smul R]
  exact M.smul_mem _ ha

theorem map_neg : a ∈ M.L → M (-a) = -M a := by
  intro ha
  rw [← neg_one_smul R, M.map_smul _ ha, neg_one_smul]

theorem sub_mem : a ∈ M.L → b ∈ M.L → a - b ∈ M.L := by
  intro ha hb
  rw [sub_eq_add_neg]
  apply M.add_mem ha (M.neg_mem hb)

theorem map_sub : a ∈ M.L → b ∈ M.L → M (a - b) = M a - M b := by
  intro ha hb
  rw [sub_eq_add_neg, M.map_add ha (M.neg_mem hb), M.map_neg hb, sub_eq_add_neg]

end Ring

end LinearMean
