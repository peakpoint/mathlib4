/-
Copyright (c) 2023 Yury Kudryashov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yury Kudryashov
-/
import Mathlib.MeasureTheory.Function.AEEqFun.DomAct
import Mathlib.MeasureTheory.Function.LpSpace.Indicator

/-!
# Action of `Mᵈᵃ` on `Lᵖ` spaces

In this file we define action of `Mᵈᵃ` on `MeasureTheory.Lp E p μ`
If `f : α → E` is a function representing an equivalence class in `Lᵖ(α, E)`, `M` acts on `α`,
and `c : M`, then `(.mk c : Mᵈᵃ) • [f]` is represented by the function `a ↦ f (c • a)`.

We also prove basic properties of this action.
-/

open MeasureTheory Filter
open scoped ENNReal

namespace DomAct

variable {M N α E : Type*} [MeasurableSpace M] [MeasurableSpace N]
  [MeasurableSpace α] [NormedAddCommGroup E] {μ : MeasureTheory.Measure α} {p : ℝ≥0∞}

section SMul

variable [SMul M α] [SMulInvariantMeasure M α μ] [MeasurableSMul M α]

@[to_additive]
instance : SMul Mᵈᵃ (Lp E p μ) where
  smul c f := Lp.compMeasurePreserving (mk.symm c • ·) (measurePreserving_smul _ _) f

@[to_additive (attr := simp)]
theorem smul_Lp_val (c : Mᵈᵃ) (f : Lp E p μ) : (c • f).1 = c • f.1 := rfl

@[to_additive]
theorem smul_Lp_ae_eq (c : Mᵈᵃ) (f : Lp E p μ) : c • f =ᵐ[μ] (f <| mk.symm c • ·) :=
  Lp.coeFn_compMeasurePreserving _ _

@[to_additive]
theorem mk_smul_toLp (c : M) {f : α → E} (hf : MemLp f p μ) :
    mk c • hf.toLp f =
      (hf.comp_measurePreserving <| measurePreserving_smul c μ).toLp (f <| c • ·) :=
  rfl

@[to_additive (attr := simp)]
theorem smul_Lp_const [IsFiniteMeasure μ] (c : Mᵈᵃ) (a : E) :
    c • Lp.const p μ a = Lp.const p μ a :=
  rfl

@[to_additive]
theorem mk_smul_indicatorConstLp (c : M)
    {s : Set α} (hs : MeasurableSet s) (hμs : μ s ≠ ∞) (b : E) :
    mk c • indicatorConstLp p hs hμs b =
      indicatorConstLp p (hs.preimage <| measurable_const_smul c)
        (by rwa [SMulInvariantMeasure.measure_preimage_smul c hs]) b :=
  rfl

instance [SMul N α] [SMulCommClass M N α] [SMulInvariantMeasure N α μ] [MeasurableSMul N α] :
    SMulCommClass Mᵈᵃ Nᵈᵃ (Lp E p μ) :=
  Subtype.val_injective.smulCommClass (fun _ _ ↦ rfl) fun _ _ ↦ rfl

instance {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] :
    SMulCommClass Mᵈᵃ 𝕜 (Lp E p μ) :=
  Subtype.val_injective.smulCommClass (fun _ _ ↦ rfl) fun _ _ ↦ rfl

instance {𝕜 : Type*} [NormedRing 𝕜] [Module 𝕜 E] [IsBoundedSMul 𝕜 E] :
    SMulCommClass 𝕜 Mᵈᵃ (Lp E p μ) :=
  .symm _ _ _

-- We don't have a typeclass for additive versions of the next few lemmas
-- Should we add `AddDistribAddAction` with `to_additive` both from `MulDistribMulAction`
-- and `DistribMulAction`?

@[to_additive]
theorem smul_Lp_add (c : Mᵈᵃ) : ∀ f g : Lp E p μ, c • (f + g) = c • f + c • g := by
  rintro ⟨⟨⟩, _⟩ ⟨⟨⟩, _⟩; rfl
attribute [simp] DomAct.vadd_Lp_add

@[to_additive (attr := simp 1001)]
theorem smul_Lp_zero (c : Mᵈᵃ) : c • (0 : Lp E p μ) = 0 := rfl

@[to_additive]
theorem smul_Lp_neg (c : Mᵈᵃ) (f : Lp E p μ) : c • (-f) = -(c • f) := by
  rcases f with ⟨⟨_⟩, _⟩; rfl

@[to_additive]
theorem smul_Lp_sub (c : Mᵈᵃ) : ∀ f g : Lp E p μ, c • (f - g) = c • f - c • g := by
  rintro ⟨⟨⟩, _⟩ ⟨⟨⟩, _⟩; rfl

instance : DistribSMul Mᵈᵃ (Lp E p μ) where
  smul_zero _ := rfl
  smul_add := by rintro _ ⟨⟨⟩, _⟩ ⟨⟨⟩, _⟩; rfl

-- The next few lemmas follow from the `IsIsometricSMul` instance if `1 ≤ p`
@[to_additive (attr := simp)]
theorem norm_smul_Lp (c : Mᵈᵃ) (f : Lp E p μ) : ‖c • f‖ = ‖f‖ :=
  Lp.norm_compMeasurePreserving _ _

@[to_additive (attr := simp)]
theorem nnnorm_smul_Lp (c : Mᵈᵃ) (f : Lp E p μ) : ‖c • f‖₊ = ‖f‖₊ :=
  NNReal.eq <| Lp.norm_compMeasurePreserving _ _

@[to_additive (attr := simp)]
theorem dist_smul_Lp (c : Mᵈᵃ) (f g : Lp E p μ) : dist (c • f) (c • g) = dist f g := by
  simp only [dist, ← smul_Lp_sub, norm_smul_Lp]

@[to_additive (attr := simp)]
theorem edist_smul_Lp (c : Mᵈᵃ) (f g : Lp E p μ) : edist (c • f) (c • g) = edist f g := by
  simp only [Lp.edist_dist, dist_smul_Lp]

variable [Fact (1 ≤ p)]

@[to_additive]
instance : IsIsometricSMul Mᵈᵃ (Lp E p μ) := ⟨edist_smul_Lp⟩

end SMul

section MulAction

variable [Monoid M] [MulAction M α] [SMulInvariantMeasure M α μ] [MeasurableSMul M α]

@[to_additive]
instance : MulAction Mᵈᵃ (Lp E p μ) := Subtype.val_injective.mulAction _ fun _ _ ↦ rfl

instance : DistribMulAction Mᵈᵃ (Lp E p μ) :=
  Subtype.val_injective.distribMulAction ⟨⟨_, rfl⟩, fun _ _ ↦ rfl⟩ fun _ _ ↦ rfl

end MulAction

end DomAct
