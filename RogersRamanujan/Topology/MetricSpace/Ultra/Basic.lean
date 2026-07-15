module

public import RogersRamanujan.Topology.Algebra.Nonarchimedean.Strong
import Mathlib.Analysis.Normed.Group.Ultra
public import Mathlib.NumberTheory.Padics.PadicNumbers

/-! # Ultrametric spaces
-/

@[expose] public section

instance (priority := 100)
    {F : Type*} [NormedRing F] [IsUltrametricDist F] : NonarchimedeanRing F where
  __ := IsUltrametricDist.nonarchimedeanAddGroup

instance (priority := 100)
    {F : Type*} [NormedRing F] [IsUltrametricDist F] : StrongNonarchimedeanRing F where
  exists_mul_subset_self U hu :=
    let ⟨ε, hε, hεU⟩ := NormedAddGroup.nhds_zero_basis_norm_lt.mem_iff.mp hu
    let ε' := min 1 ε
    have key : ε' * ε' ≤ ε' := by nth_grw 1 [show ε' ≤ 1 by grind, one_mul]
    ⟨{x | ‖x‖ < ε'}, by simpa [ε'], isOpen_lt (by fun_prop) (by fun_prop), by grind,
      Set.mul_subset_iff.mpr fun x hx y hy ↦ by
        simpa using ((norm_mul_le x y).trans_lt <|
          (mul_lt_mul'' hx hy (norm_nonneg x) (norm_nonneg y)).trans_le key)⟩

instance (p : ℕ) [Fact p.Prime] : StrongNonarchimedeanRing ℚ_[p] := inferInstance
