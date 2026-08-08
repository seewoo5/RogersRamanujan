module

import RogersRamanujan.Data.Nat.Choose.Basic
public import RogersRamanujan.NumberTheory.QTheory.Defs
public import RogersRamanujan.NumberTheory.QTheory.JacobiTripleProduct.Basic
import RogersRamanujan.NumberTheory.QTheory.StrongNonarchimedean
public import RogersRamanujan.RingTheory.PowerSeries.DiscreteTopology
public import Mathlib.Algebra.Polynomial.Laurent
public import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.RingTheory.MvPowerSeries.LinearTopology

/-! # The Jacobi triple product over `ℂ`

`RogersRamanujan/NumberTheory/QTheory/JacobiTripleProduct/Basic.lean` proves the Jacobi triple
product in a complete strongly nonarchimedean ring, for a topologically nilpotent `q`. The field
`ℂ` with its usual topology is *not* nonarchimedean, so that theorem does not apply to it directly.
In this file we recover the classical analytic statement from the formal one: for `a b q : ℂ` with
`‖q‖ < 1` and `a * b = q`,
`(q; q)_∞ * (-a; q)_∞ * (-b; q)_∞ = ∑' n : ℤ, abPow a b n * q ^ (|n| choose 2)`,
where the infinite products converge in `ℂ` and the sum over `ℤ` is a genuine `HasSum`.

## Strategy

The nonarchimedean theorem is instantiated in the ring `ℤ[T;T⁻¹]⟦X⟧` of formal power series over
the Laurent polynomials, with `q := X` (topologically nilpotent), `a := T` and `b := T⁻¹X`; note
that the coefficient ring carries no topology of its own, so all the required instances on
`ℤ[T;T⁻¹]⟦X⟧` come from `PowerSeries.DiscreteTopology`. The resulting formal identity is then
evaluated at `T ↦ a`, `X ↦ q`.

## Main definitions

The evaluation bridge, stated for an arbitrary ring homomorphism `φ : R →+* ℂ` on the coefficients:

* `PowerSeries.evalAt φ q f = ∑' m, φ (coeff m f) * q ^ m`, the value of a formal power series
  at a complex number;
* `PowerSeries.enormAt φ q f = ∑' m, ‖φ (coeff m f) * q ^ m‖ₑ`, an `ℝ≥0∞`-valued `ℓ¹`-norm which
  controls it. It is subadditive, submultiplicative (`PowerSeries.enormAt_mul_le`) and lower
  semicontinuous for the `X`-adic topology (`PowerSeries.enormAt_le_of_tendsto`), which is what
  makes the transfer work.

## Main results

* `PowerSeries.hasSum_evalAt`: an `X`-adically convergent sum of formal power series evaluates
  termwise, provided the double family of coefficients is absolutely summable;
* `PowerSeries.qPochhammerInf_eq_evalAt`: the formal product `(c Xᵈ; X)_∞` evaluates to the
  convergent complex product `(φ c qᵈ; q)_∞`;
* `jacobi_triple_product_hasSum_complex`, `jacobi_triple_product_complex`: the Jacobi triple
  product over `ℂ`, in the same shape as `jacobi_triple_product_hasSum` and
  `jacobi_triple_product`;
* `jacobi_triple_product_theta_hasSum`: the classical two-variable form
  `∏ (1 - q^{i+1})(1 + z q^i)(1 + z⁻¹ q^{i+1}) = ∑ n : ℤ, z ^ n * q ^ (n(n-1)/2)`.
-/

@[expose] public section

open Filter Finset Topology SummationFilter
open QTheory PowerSeries DiscreteTopology
open scoped ENNReal NNReal

/-! ### Evaluating a formal power series at a complex number -/

namespace PowerSeries

variable {R : Type*} [CommRing R] (φ : R →+* ℂ) (q : ℂ)

/-- The value at `q : ℂ` of the formal power series `f`, with coefficients transported along
the ring homomorphism `φ`. Only meaningful when `enormAt φ q f ≠ ⊤`. -/
noncomputable def evalAt (f : R⟦X⟧) : ℂ := ∑' m, φ (f.coeff m) * q ^ m

/-- The `ℓ¹`-norm of `f` at `q`, valued in `ℝ≥0∞`: `∑ ‖φ (coeff m f)‖ * ‖q‖ ^ m`. -/
noncomputable def enormAt (f : R⟦X⟧) : ℝ≥0∞ := ∑' m, ‖φ (f.coeff m) * q ^ m‖ₑ

variable {φ q}

theorem summable_norm_of_enormAt_ne_top {f : R⟦X⟧} (hf : enormAt φ q f ≠ ⊤) :
    Summable fun m ↦ ‖φ (f.coeff m) * q ^ m‖ :=
  tsum_enorm_ne_top_iff_summable_norm.mp hf

theorem summable_of_enormAt_ne_top {f : R⟦X⟧} (hf : enormAt φ q f ≠ ⊤) :
    Summable fun m ↦ φ (f.coeff m) * q ^ m :=
  (summable_norm_of_enormAt_ne_top hf).of_norm

theorem enorm_evalAt_le (f : R⟦X⟧) : ‖evalAt φ q f‖ₑ ≤ enormAt φ q f :=
  enorm_tsum_le_tsum_enorm

@[simp] theorem enormAt_zero : enormAt φ q (0 : R⟦X⟧) = 0 := by simp [enormAt]

@[simp] theorem enormAt_one : enormAt φ q (1 : R⟦X⟧) = 1 := by
  rw [enormAt, tsum_eq_single 0] <;> simp +contextual [coeff_one]

@[simp] theorem enormAt_C (c : R) : enormAt φ q (C c) = ‖φ c‖ₑ := by
  rw [enormAt, tsum_eq_single 0] <;> simp +contextual [coeff_C]

@[simp] theorem enormAt_neg (f : R⟦X⟧) : enormAt φ q (-f) = enormAt φ q f := by
  simp [enormAt]

theorem enormAt_add_le (f g : R⟦X⟧) : enormAt φ q (f + g) ≤ enormAt φ q f + enormAt φ q g := by
  rw [enormAt, enormAt, enormAt, ← ENNReal.tsum_add]
  refine ENNReal.tsum_le_tsum fun m ↦ ?_
  simpa [map_add, add_mul] using
    enorm_add_le (φ (f.coeff m) * q ^ m) (φ (g.coeff m) * q ^ m)

theorem enormAt_sub_le (f g : R⟦X⟧) : enormAt φ q (f - g) ≤ enormAt φ q f + enormAt φ q g := by
  simpa [sub_eq_add_neg] using enormAt_add_le f (-g)

/-- The Cauchy product formula for `ℝ≥0∞`-valued series. -/
private theorem tsum_sum_antidiagonal_mul (a b : ℕ → ℝ≥0∞) :
    ∑' n, ∑ p ∈ antidiagonal n, a p.1 * b p.2 = (∑' m, a m) * (∑' m, b m) := by
  simp_rw [← Finset.tsum_subtype,
    ← ENNReal.tsum_sigma' fun x : Σ n : ℕ, antidiagonal n ↦ a x.2.1.1 * b x.2.1.2]
  refine (Finset.sigmaAntidiagonalEquivProd.tsum_eq fun p : ℕ × ℕ ↦ a p.1 * b p.2).trans ?_
  simp [ENNReal.tsum_prod', ENNReal.tsum_mul_left, ENNReal.tsum_mul_right]

/-- `enormAt` is submultiplicative. -/
theorem enormAt_mul_le (f g : R⟦X⟧) : enormAt φ q (f * g) ≤ enormAt φ q f * enormAt φ q g := by
  rw [enormAt, enormAt, enormAt, ← tsum_sum_antidiagonal_mul]
  refine ENNReal.tsum_le_tsum fun n ↦ ?_
  rw [coeff_mul, map_sum, sum_mul]
  refine (enorm_sum_le _ _).trans_eq (sum_congr rfl fun p hp ↦ ?_)
  rw [map_mul, ← mem_antidiagonal.mp hp, pow_add, mul_mul_mul_comm, enorm_mul]

theorem enormAt_prod_le {ι : Type*} (s : Finset ι) (f : ι → R⟦X⟧) :
    enormAt φ q (∏ i ∈ s, f i) ≤ ∏ i ∈ s, enormAt φ q (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
    rw [prod_insert hi, prod_insert hi]
    exact (enormAt_mul_le _ _).trans (by gcongr)

/-- Weierstrass-type estimate: `‖∏ (1 + uᵢ) - 1‖ + 1 ≤ ∏ (‖uᵢ‖ + 1)`. -/
theorem enormAt_prod_one_add_sub_one_le {ι : Type*} (s : Finset ι) (f : ι → R⟦X⟧) :
    enormAt φ q (∏ i ∈ s, (1 + f i) - 1) + 1 ≤ ∏ i ∈ s, (enormAt φ q (f i) + 1) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert j s hj ih =>
    set B := ∏ i ∈ s, (enormAt φ q (f i) + 1)
    have hprod : enormAt φ q (∏ i ∈ s, (1 + f i)) ≤ B := by
      have h := enormAt_add_le (φ := φ) (q := q) (∏ i ∈ s, (1 + f i) - 1) 1
      rw [sub_add_cancel, enormAt_one] at h
      exact h.trans ih
    rw [prod_insert hj, prod_insert hj, show (1 + f j) * ∏ i ∈ s, (1 + f i) - 1
      = (∏ i ∈ s, (1 + f i) - 1) + f j * ∏ i ∈ s, (1 + f i) from by ring]
    calc enormAt φ q ((∏ i ∈ s, (1 + f i) - 1) + f j * ∏ i ∈ s, (1 + f i)) + 1
        ≤ (enormAt φ q (∏ i ∈ s, (1 + f i) - 1) + 1)
            + enormAt φ q (f j * ∏ i ∈ s, (1 + f i)) := by
          rw [add_right_comm]; exact add_le_add (enormAt_add_le _ _) le_rfl
      _ ≤ B + enormAt φ q (f j) * B :=
          add_le_add ih ((enormAt_mul_le _ _).trans (by gcongr))
      _ = (enormAt φ q (f j) + 1) * B := by ring

/-- The `ℓ¹`-norm is lower semicontinuous for the `X`-adic topology. -/
theorem enormAt_le_of_tendsto {ι : Type*} {u : Filter ι} [u.NeBot] {F : ι → R⟦X⟧} {f : R⟦X⟧}
    (hF : Tendsto F u (𝓝 f)) {B : ℝ≥0∞} (hB : ∀ i, enormAt φ q (F i) ≤ B) : enormAt φ q f ≤ B := by
  rw [enormAt, ENNReal.tsum_eq_iSup_nat]
  refine iSup_le fun n ↦ ?_
  obtain ⟨i, hi⟩ := ((eventually_all_finset (range n)).mpr fun m _ ↦
    (tendsto_iff_coeff_eventually_const F u f).mp hF m).exists
  calc ∑ m ∈ range n, ‖φ (f.coeff m) * q ^ m‖ₑ
      = ∑ m ∈ range n, ‖φ ((F i).coeff m) * q ^ m‖ₑ := sum_congr rfl fun m hm ↦ by rw [hi m hm]
    _ ≤ B := (ENNReal.sum_le_tsum _).trans (hB i)

@[simp] theorem evalAt_zero : evalAt φ q (0 : R⟦X⟧) = 0 := by simp [evalAt]

@[simp] theorem evalAt_C (c : R) : evalAt φ q (C c) = φ c := by
  rw [evalAt, tsum_eq_single 0] <;> simp +contextual [coeff_C]

@[simp] theorem evalAt_one : evalAt φ q (1 : R⟦X⟧) = 1 := by
  simpa using evalAt_C (φ := φ) (q := q) 1

theorem evalAt_C_mul_X_pow (c : R) (d : ℕ) : evalAt φ q (C c * X ^ d) = φ c * q ^ d := by
  rw [evalAt, tsum_eq_single d] <;> simp +contextual [coeff_X_pow, mul_comm, eq_comm]

theorem evalAt_add {f g : R⟦X⟧} (hf : enormAt φ q f ≠ ⊤) (hg : enormAt φ q g ≠ ⊤) :
    evalAt φ q (f + g) = evalAt φ q f + evalAt φ q g := by
  rw [evalAt, evalAt, evalAt,
    ← (summable_of_enormAt_ne_top hf).tsum_add (summable_of_enormAt_ne_top hg)]
  exact tsum_congr fun m ↦ by simp [map_add, add_mul]

@[simp] theorem evalAt_neg (f : R⟦X⟧) : evalAt φ q (-f) = -evalAt φ q f := by
  simp only [evalAt, map_neg, neg_mul, tsum_neg]

theorem evalAt_sub {f g : R⟦X⟧} (hf : enormAt φ q f ≠ ⊤) (hg : enormAt φ q g ≠ ⊤) :
    evalAt φ q (f - g) = evalAt φ q f - evalAt φ q g := by
  rw [sub_eq_add_neg, evalAt_add hf (by simpa using hg), evalAt_neg, ← sub_eq_add_neg]

theorem evalAt_mul {f g : R⟦X⟧} (hf : enormAt φ q f ≠ ⊤) (hg : enormAt φ q g ≠ ⊤) :
    evalAt φ q (f * g) = evalAt φ q f * evalAt φ q g := by
  rw [evalAt, evalAt, evalAt, tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm
    (summable_norm_of_enormAt_ne_top hf) (summable_norm_of_enormAt_ne_top hg)]
  refine tsum_congr fun n ↦ ?_
  rw [coeff_mul, map_sum, sum_mul]
  refine sum_congr rfl fun p hp ↦ ?_
  rw [map_mul, ← mem_antidiagonal.mp hp, pow_add, mul_mul_mul_comm]

theorem evalAt_prod {ι : Type*} (s : Finset ι) (f : ι → R⟦X⟧)
    (hf : ∀ i ∈ s, enormAt φ q (f i) ≠ ⊤) :
    evalAt φ q (∏ i ∈ s, f i) = ∏ i ∈ s, evalAt φ q (f i) := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert i s hi ih =>
    have hne : enormAt φ q (∏ j ∈ s, f j) ≠ ⊤ :=
      ne_top_of_le_ne_top (ENNReal.prod_ne_top fun j hj ↦ hf j (mem_insert_of_mem hj))
        (enormAt_prod_le s f)
    rw [prod_insert hi, prod_insert hi, evalAt_mul (hf i (mem_insert_self i s)) hne,
      ih fun j hj ↦ hf j (mem_insert_of_mem hj)]

/-- Transfer of an `X`-adically convergent sum to a convergent sum of complex numbers. -/
theorem hasSum_evalAt {ι : Type*} {F : ι → R⟦X⟧} {G : R⟦X⟧} (h : HasSum F G)
    (hs : Summable fun p : ι × ℕ ↦ ‖φ ((F p.1).coeff p.2) * q ^ p.2‖) :
    HasSum (fun i ↦ evalAt φ q (F i)) (evalAt φ q G) := by
  set c : ι × ℕ → ℂ := fun p ↦ φ ((F p.1).coeff p.2) * q ^ p.2
  have hcs : Summable c := hs.of_norm
  have hcoeff : ∀ m, HasSum (fun i ↦ φ ((F i).coeff m)) (φ (G.coeff m)) := fun m ↦
    EventuallyEq.tendsto <| ((tendsto_iff_coeff_eventually_const _ _ _).mp h m).mono
      fun s hs ↦ by simp only [← map_sum, hs]
  have hswap : HasSum (fun m ↦ φ (G.coeff m) * q ^ m) (∑' p, c p) :=
    ((Equiv.prodComm ℕ ι).hasSum_iff.mpr hcs.hasSum).prod_fiberwise fun m ↦ (hcoeff m).mul_right _
  rw [evalAt, hswap.tsum_eq]
  exact hcs.hasSum.prod_fiberwise fun i ↦ (hcs.prod_factor i).hasSum


/-! ### Transfer of the infinite `q`-Pochhammer symbol

The formal infinite product `(c Xᵈ; X)_∞` in `R⟦X⟧` evaluates at `q` to the convergent complex
infinite product `(φ c qᵈ; q)_∞`, provided `‖q‖ < 1`.
-/

section Pochhammer

variable {R : Type*} [CommRing R] {φ : R →+* ℂ} {q : ℂ} (c : R) (d : ℕ)

@[simp] theorem enormAt_C_mul_X_pow (k : ℕ) : enormAt φ q (C c * X ^ k) = ‖φ c‖ₑ * ‖q‖ₑ ^ k := by
  rw [enormAt, tsum_eq_single k] <;>
    simp +contextual [coeff_C_mul, coeff_X_pow, enorm_mul, enorm_pow, eq_comm]

theorem enormAt_C_mul_X_pow_ne_top (k : ℕ) : enormAt φ q (C c * X ^ k) ≠ ⊤ := by
  simp [ENNReal.mul_ne_top, enorm_ne_top]

theorem enormAt_one_sub_C_mul_X_pow_ne_top (k : ℕ) : enormAt φ q (1 - C c * X ^ k) ≠ ⊤ := by
  refine ne_top_of_le_ne_top ?_ (enormAt_sub_le _ _)
  simp [ENNReal.mul_ne_top, enorm_ne_top]

theorem qPochhammer_eq_prod_one_sub (N : ℕ) :
    ((C c * X ^ d; X)_N : R⟦X⟧) = ∏ i ∈ range N, (1 - C c * X ^ (d + i)) := by
  unfold qPochhammer
  exact prod_congr rfl fun i _ ↦ by rw [pow_add]; ring

theorem enormAt_qPochhammer_ne_top (N : ℕ) : enormAt φ q ((C c * X ^ d; X)_N) ≠ ⊤ := by
  rw [qPochhammer_eq_prod_one_sub]
  exact ne_top_of_le_ne_top
    (ENNReal.prod_ne_top fun i _ ↦ enormAt_one_sub_C_mul_X_pow_ne_top c (d + i))
    (enormAt_prod_le _ _)

/-- A uniform Weierstrass bound for the truncated formal `q`-Pochhammer symbols. -/
theorem enormAt_qPochhammer_sub_one_le (N : ℕ) :
    enormAt φ q ((C c * X ^ d; X)_N - 1) + 1 ≤ ∏ i ∈ range N, (‖φ c‖ₑ * ‖q‖ₑ ^ (d + i) + 1) := by
  rw [qPochhammer_eq_prod_one_sub]
  simp only [sub_eq_add_neg (1 : R⟦X⟧)]
  refine (enormAt_prod_one_add_sub_one_le _ _).trans (le_of_eq (prod_congr rfl fun i _ ↦ ?_))
  rw [enormAt_neg, enormAt_C_mul_X_pow]

private theorem prod_enorm_le_exp (ht : ‖q‖ < 1) (N : ℕ) :
    ∏ i ∈ range N, (‖φ c‖ₑ * ‖q‖ₑ ^ (d + i) + 1)
      ≤ ENNReal.ofReal (Real.exp (‖φ c‖ * ‖q‖ ^ d / (1 - ‖q‖))) := by
  have key : ∀ i, ‖φ c‖ₑ * ‖q‖ₑ ^ (d + i) + 1 = ENNReal.ofReal (1 + ‖φ c * q ^ (d + i)‖) :=
    fun i ↦ by rw [ENNReal.ofReal_add zero_le_one (norm_nonneg _), ENNReal.ofReal_one,
      ofReal_norm, enorm_mul, enorm_pow, add_comm]
  rw [prod_congr rfl fun i _ ↦ key i, ← ENNReal.ofReal_prod_of_nonneg (fun i _ ↦ by positivity)]
  refine (ENNReal.ofReal_le_ofReal (Real.prod_one_add_le_exp_sum _ fun i ↦ norm_nonneg _)).trans ?_
  simp only [norm_mul, norm_pow, pow_add, div_eq_mul_inv, ← mul_assoc, ← mul_sum]
  gcongr
  exact sum_le_hasSum _ (fun i _ ↦ pow_nonneg (norm_nonneg _) i)
    (hasSum_geometric_of_lt_one (norm_nonneg _) ht)

end Pochhammer

section PochhammerInf

variable {R : Type*} [CommRing R] {φ : R →+* ℂ} {q : ℂ} (c : R) (d : ℕ)

theorem enormAt_qPochhammerInf_sub_one_le (ht : ‖q‖ < 1) :
    enormAt φ q ((C c * X ^ d; X)_∞ - 1)
      ≤ ENNReal.ofReal (Real.exp (‖φ c‖ * ‖q‖ ^ d / (1 - ‖q‖)) - 1) := by
  have hexp : (0 : ℝ) ≤ Real.exp (‖φ c‖ * ‖q‖ ^ d / (1 - ‖q‖)) - 1 :=
    sub_nonneg.mpr (Real.one_le_exp (by positivity))
  refine enormAt_le_of_tendsto (u := atTop)
    ((tendsto_qPochhammer_qPochhammerInf (by simp)).sub tendsto_const_nhds) fun N ↦
    (ENNReal.add_le_add_iff_right ENNReal.one_ne_top).mp
      ((enormAt_qPochhammer_sub_one_le c d N).trans ((prod_enorm_le_exp c d ht N).trans ?_))
  rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add hexp zero_le_one, sub_add_cancel]

theorem enormAt_qPochhammerInf_ne_top (ht : ‖q‖ < 1) : enormAt φ q ((C c * X ^ d; X)_∞) ≠ ⊤ := by
  refine ne_top_of_le_ne_top
    (b := enormAt φ q ((C c * X ^ d; X)_∞ - 1) + enormAt φ q (1 : R⟦X⟧)) ?_ ?_
  · exact ENNReal.add_ne_top.mpr ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top
      (enormAt_qPochhammerInf_sub_one_le c d ht), by simp⟩
  · exact le_trans (le_of_eq (by rw [sub_add_cancel])) (enormAt_add_le _ _)

theorem norm_evalAt_qPochhammerInf_sub_one_le (ht : ‖q‖ < 1) :
    ‖evalAt φ q ((C c * X ^ d; X)_∞) - 1‖ ≤ Real.exp (‖φ c‖ * ‖q‖ ^ d / (1 - ‖q‖)) - 1 := by
  have hexp : (1 : ℝ) ≤ Real.exp (‖φ c‖ * ‖q‖ ^ d / (1 - ‖q‖)) := Real.one_le_exp (by positivity)
  have hsub : evalAt φ q ((C c * X ^ d; X)_∞) - 1 = evalAt φ q ((C c * X ^ d; X)_∞ - 1) := by
    rw [evalAt_sub (enormAt_qPochhammerInf_ne_top c d ht) (by simp), evalAt_one]
  have key : ‖evalAt φ q ((C c * X ^ d; X)_∞ - 1)‖ₑ
      ≤ ENNReal.ofReal (Real.exp (‖φ c‖ * ‖q‖ ^ d / (1 - ‖q‖)) - 1) :=
    (enorm_evalAt_le _).trans (enormAt_qPochhammerInf_sub_one_le c d ht)
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top key
  rw [toReal_enorm, ENNReal.toReal_ofReal (by linarith)] at h
  rwa [hsub]

theorem evalAt_qPochhammer (N : ℕ) :
    evalAt φ q ((C c * X ^ d; X)_N) = ∏ i ∈ range N, (1 - φ c * q ^ d * q ^ i) := by
  rw [qPochhammer_eq_prod_one_sub,
    evalAt_prod _ _ fun i _ ↦ enormAt_one_sub_C_mul_X_pow_ne_top c (d + i)]
  refine prod_congr rfl fun i _ ↦ ?_
  rw [evalAt_sub (by simp) (enormAt_C_mul_X_pow_ne_top c (d + i)), evalAt_one,
    evalAt_C_mul_X_pow, pow_add, mul_assoc]

/-- **Formal to analytic**: the formal infinite `q`-Pochhammer symbol `(c Xᵈ; X)_∞` evaluates at
`q` to the convergent complex infinite product `(φ c qᵈ; q)_∞`. -/
theorem hasProd_qPochhammerInf_evalAt (ht : ‖q‖ < 1) :
    HasProd (fun i ↦ 1 - φ c * q ^ d * q ^ i)
      (evalAt φ q ((C c * X ^ d; X)_∞)) (conditional ℕ) := by
  set L := evalAt φ q ((C c * X ^ d; X)_∞) with hL
  have hLN : ∀ N : ℕ, L = (∏ i ∈ range N, (1 - φ c * q ^ d * q ^ i)) *
      evalAt φ q ((C c * X ^ (d + N); X)_∞) := fun N ↦ by
    rw [hL, qPochhammerInf_eq_qPochhammer_mul_qPochhammerInf N (by simp), mul_assoc, ← pow_add,
      evalAt_mul (enormAt_qPochhammer_ne_top c d N)
        (enormAt_qPochhammerInf_ne_top c (d + N) ht), evalAt_qPochhammer]
  have htend : Tendsto (fun N ↦ evalAt φ q ((C c * X ^ (d + N); X)_∞)) atTop (𝓝 1) := by
    have h0 : Tendsto (fun N : ℕ ↦ ‖φ c‖ * ‖q‖ ^ (d + N) / (1 - ‖q‖)) atTop (𝓝 0) := by
      simpa [add_comm] using (((tendsto_pow_atTop_nhds_zero_of_lt_one (norm_nonneg q) ht).comp
        (tendsto_add_atTop_nat d)).const_mul ‖φ c‖).div_const (1 - ‖q‖)
    simpa using (squeeze_zero_norm (fun N ↦ norm_evalAt_qPochhammerInf_sub_one_le c (d + N) ht)
      (by simpa using ((Real.continuous_exp.tendsto 0).comp h0).sub_const 1)).add_const 1
  have hdiv : Tendsto (fun N ↦ L / evalAt φ q ((C c * X ^ (d + N); X)_∞)) atTop (𝓝 L) := by
    have h := (tendsto_const_nhds (x := L)).div htend one_ne_zero
    rwa [div_one] at h
  rw [HasProd, conditional_filter_eq_map_range, tendsto_map'_iff]
  refine hdiv.congr' ?_
  filter_upwards [htend.eventually_ne one_ne_zero] with N hN using (div_eq_iff hN).mpr (hLN N)

theorem qPochhammerInf_eq_evalAt (ht : ‖q‖ < 1) :
    ((φ c * q ^ d; q)_∞ : ℂ) = evalAt φ q ((C c * X ^ d; X)_∞) :=
  (hasProd_qPochhammerInf_evalAt c d ht).tprod_eq

end PochhammerInf

end PowerSeries

/-! ### The Jacobi triple product over `ℂ`

We instantiate the general Jacobi triple product in the ring `ℤ[T;T⁻¹]⟦X⟧` of formal power series
over the Laurent polynomials, with `q := X`, `a := T` and `b := T⁻¹X`, and transport the resulting
identity to `ℂ` along the evaluation `T ↦ a`, `X ↦ q`.
-/

open LaurentPolynomial hiding C

/-- The `X`-degree of the `n`-th term of the formal Jacobi triple product:
`n.choose 2` for `n ≥ 0`, and `n.choose 2 + n` for `n < 0`. -/
def jtpDeg : ℤ → ℕ
  | (k : ℕ) => k.choose 2
  | Int.negSucc k => (k + 1).choose 2 + (k + 1)

@[simp] theorem jtpDeg_nat (k : ℕ) : jtpDeg k = k.choose 2 := rfl

@[simp] theorem jtpDeg_neg_nat (k : ℕ) : jtpDeg (-k) = k.choose 2 + k := by
  obtain _ | k := k
  · simp [jtpDeg]
  rw [Nat.cast_succ, ← Int.negSucc_eq]
  rfl

/-- Ratio test for the theta-type series `∑ sᵏ t^(k choose 2 + j k)`. -/
theorem summable_pow_mul_pow_choose_two {s t : ℝ} (hs : 0 ≤ s) (ht0 : 0 ≤ t) (ht : t < 1) (j : ℕ) :
    Summable fun k : ℕ ↦ s ^ k * t ^ (k.choose 2 + j * k) := by
  have hnn : ∀ k : ℕ, 0 ≤ s ^ k * t ^ (k.choose 2 + j * k) := fun k ↦ by positivity
  refine summable_of_ratio_norm_eventually_le (r := 1 / 2) (by norm_num) ?_
  filter_upwards [(tendsto_add_atTop_nat j).eventually
    (((tendsto_pow_atTop_nhds_zero_of_lt_one ht0 ht).const_mul s).eventually_le_const
      (by norm_num : s * 0 < 1 / 2))] with k hk
  rw [Real.norm_of_nonneg (hnn _), Real.norm_of_nonneg (hnn _), Nat.choose_succ_two]
  exact (mul_le_mul_of_nonneg_right hk (hnn k)).trans_eq' (by ring)

section

variable {a b q : ℂ}

/-- The formal Jacobi triple product in `ℤ[T;T⁻¹]⟦X⟧`. -/
theorem hasSum_jacobi_triple_product_laurentPolynomial :
    HasSum (fun n : ℤ ↦ abPow (-(C (T 1))) (-(C (T (-1)) * X)) n * X ^ n.natAbs.choose 2)
      ((X; X)_∞ * (C (T 1); X)_∞ * (C (T (-1)) * X; X)_∞ : ℤ[T;T⁻¹]⟦X⟧) :=
  jacobi_triple_product_hasSum' (by simp) (by simp [← mul_assoc, ← map_mul, -T_mul, ← T_add])

theorem LaurentPolynomial.neg_T_pow {R : Type*} [CommRing R] (m : ℤ) (k : ℕ) :
    (-(T m : R[T;T⁻¹])) ^ k = (-1) ^ k * T (k * m) := by
  rw [neg_pow, T_pow]

/-- Each term of the formal Jacobi triple product is a monomial. -/
theorem jtp_summand_eq (n : ℤ) :
    (abPow (-(C (T 1))) (-(C (T (-1)) * X)) n * X ^ n.natAbs.choose 2 : ℤ[T;T⁻¹]⟦X⟧)
      = C ((-1) ^ n.natAbs * T n) * X ^ jtpDeg n := by
  have hT := @LaurentPolynomial.neg_T_pow ℤ _
  obtain ⟨k, rfl | rfl⟩ := n.eq_nat_or_neg
  · rw [abPow_nat, jtpDeg_nat, Int.natAbs_natCast, ← map_neg, ← map_pow, hT, mul_one]
  · rw [abPow_neg_nat, jtpDeg_neg_nat, Int.natAbs_neg, Int.natAbs_natCast,
      show (-(C (T (-1)) * X) : ℤ[T;T⁻¹]⟦X⟧) = C (-(T (-1))) * X by rw [map_neg, neg_mul],
      mul_pow, ← map_pow, hT, mul_neg_one, mul_assoc, ← pow_add, add_comm k]

end

section Evaluation

variable {a b q : ℂ}

/-- Evaluation of Laurent polynomials at a nonzero complex number. -/
noncomputable def laurentEval (a : ℂ) (ha : a ≠ 0) : ℤ[T;T⁻¹] →+* ℂ :=
  LaurentPolynomial.eval₂ (Int.castRingHom ℂ) (Units.mk0 a ha)

@[simp] theorem laurentEval_T (ha : a ≠ 0) (n : ℤ) : laurentEval a ha (T n) = a ^ n := by
  rw [laurentEval, eval₂_T]
  simp

theorem coeff_jtp_summand (n : ℤ) (m : ℕ) :
    (C ((-1) ^ n.natAbs * T n) * X ^ jtpDeg n : ℤ[T;T⁻¹]⟦X⟧).coeff m
      = if m = jtpDeg n then (-1) ^ n.natAbs * T n else 0 := by
  rw [coeff_C_mul, coeff_X_pow]
  split <;> simp

theorem evalAt_jtp_summand (ha : a ≠ 0) (n : ℤ) :
    evalAt (laurentEval a ha) q (C ((-1) ^ n.natAbs * T n) * X ^ jtpDeg n)
      = (-1) ^ n.natAbs * a ^ n * q ^ jtpDeg n := by
  rw [evalAt_C_mul_X_pow, map_mul, map_pow, map_neg, map_one, laurentEval_T]

/-- The `n`-th summand of the formal Jacobi triple product evaluates to the `n`-th summand of the
complex one, for the splitting `a * (a⁻¹ * q) = q`. -/
theorem evalAt_jtp_summand_eq_abPow (ha : a ≠ 0) (n : ℤ) :
    evalAt (laurentEval a ha) q (C ((-1) ^ n.natAbs * T n) * X ^ jtpDeg n)
      = abPow (-a) (-(a⁻¹ * q)) n * q ^ n.natAbs.choose 2 := by
  rw [evalAt_jtp_summand ha]
  obtain ⟨k, rfl | rfl⟩ := n.eq_nat_or_neg
  · rw [abPow_nat, jtpDeg_nat, Int.natAbs_natCast, zpow_natCast]
    ring
  · rw [abPow_neg_nat, jtpDeg_neg_nat, Int.natAbs_neg, Int.natAbs_natCast, zpow_neg, zpow_natCast,
      ← inv_pow, pow_add]
    ring

theorem norm_evalAt_jtp_summand (ha : a ≠ 0) (n : ℤ) (m : ℕ) :
    ‖laurentEval a ha ((C ((-1) ^ n.natAbs * T n) * X ^ jtpDeg n : ℤ[T;T⁻¹]⟦X⟧).coeff m) * q ^ m‖
      = if m = jtpDeg n then ‖a ^ n‖ * ‖q‖ ^ m else 0 := by
  rw [coeff_jtp_summand]
  split
  · rw [map_mul, map_pow, map_neg, map_one, laurentEval_T, norm_mul, norm_mul, norm_pow, norm_pow,
      norm_neg, norm_one, one_pow, one_mul]
  · simp

/-- The double family of coefficients of the formal Jacobi triple product is absolutely
summable at any `q` with `‖q‖ < 1`. -/
theorem summable_norm_jtp (ha : a ≠ 0) (hq : ‖q‖ < 1) :
    Summable fun p : ℤ × ℕ ↦
      ‖laurentEval a ha ((C ((-1) ^ p.1.natAbs * T p.1) * X ^ jtpDeg p.1 :
        ℤ[T;T⁻¹]⟦X⟧).coeff p.2) * q ^ p.2‖ := by
  have hvanish : ∀ p : ℤ × ℕ, p ∉ Set.range (fun n : ℤ ↦ (n, jtpDeg n)) →
      ‖laurentEval a ha ((C ((-1) ^ p.1.natAbs * T p.1) * X ^ jtpDeg p.1 :
        ℤ[T;T⁻¹]⟦X⟧).coeff p.2) * q ^ p.2‖ = 0 := fun p hp ↦
    (norm_evalAt_jtp_summand ha p.1 p.2).trans (if_neg fun hm ↦ hp ⟨p.1, Prod.ext rfl hm.symm⟩)
  rw [← Function.Injective.summable_iff (fun x y h ↦ congrArg Prod.fst h) hvanish]
  simp only [Function.comp_def, norm_evalAt_jtp_summand ha, if_pos]
  refine Summable.of_nat_of_neg ?_ ?_
  · simpa using summable_pow_mul_pow_choose_two (norm_nonneg a) (norm_nonneg q) hq 0
  · simpa using summable_pow_mul_pow_choose_two (norm_nonneg a⁻¹) (norm_nonneg q) hq 1

end Evaluation

section Main

variable {a b q : ℂ}

/-- **Jacobi triple product over `ℂ`**, nondegenerate case. -/
theorem jacobi_triple_product_hasSum'_complex_of_ne_zero
    (ha : a ≠ 0) (hq : ‖q‖ < 1) (hab : a * b = q) :
    HasSum (fun n : ℤ ↦ abPow (-a) (-b) n * q ^ n.natAbs.choose 2)
      ((q; q)_∞ * (a; q)_∞ * (b; q)_∞) := by
  obtain rfl : b = a⁻¹ * q := by rw [← hab, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
  set φ := laurentEval a ha with hφ
  have p1 : evalAt φ q ((X; X)_∞ : ℤ[T;T⁻¹]⟦X⟧) = ((q; q)_∞ : ℂ) := by
    simpa using (qPochhammerInf_eq_evalAt (φ := φ) (1 : ℤ[T;T⁻¹]) 1 hq).symm
  have p2 : evalAt φ q ((C (T 1); X)_∞ : ℤ[T;T⁻¹]⟦X⟧) = ((a; q)_∞ : ℂ) := by
    simpa [hφ] using (qPochhammerInf_eq_evalAt (φ := φ) (T 1) 0 hq).symm
  have p3 : evalAt φ q ((C (T (-1)) * X; X)_∞ : ℤ[T;T⁻¹]⟦X⟧) = ((a⁻¹ * q; q)_∞ : ℂ) := by
    simpa [hφ] using (qPochhammerInf_eq_evalAt (φ := φ) (T (-1)) 1 hq).symm
  have n1 : enormAt φ q ((X; X)_∞ : ℤ[T;T⁻¹]⟦X⟧) ≠ ⊤ := by
    simpa using enormAt_qPochhammerInf_ne_top (φ := φ) (1 : ℤ[T;T⁻¹]) 1 hq
  have n2 : enormAt φ q ((C (T 1); X)_∞ : ℤ[T;T⁻¹]⟦X⟧) ≠ ⊤ := by
    simpa using enormAt_qPochhammerInf_ne_top (φ := φ) (T 1) 0 hq
  have n3 : enormAt φ q ((C (T (-1)) * X; X)_∞ : ℤ[T;T⁻¹]⟦X⟧) ≠ ⊤ := by
    simpa using enormAt_qPochhammerInf_ne_top (φ := φ) (T (-1)) 1 hq
  have hformal := hasSum_jacobi_triple_product_laurentPolynomial
  simp only [jtp_summand_eq] at hformal
  have h := hasSum_evalAt (φ := φ) (q := q) hformal (summable_norm_jtp ha hq)
  rw [evalAt_mul (ne_top_of_le_ne_top (ENNReal.mul_ne_top n1 n2) (enormAt_mul_le _ _)) n3,
    evalAt_mul n1 n2, p1, p2, p3] at h
  simpa only [hφ, evalAt_jtp_summand_eq_abPow ha] using h

end Main

section Degenerate

/-- Over `ℂ`, the infinite `q`-Pochhammer symbol at `q = 0` collapses to its first factor. -/
theorem qPochhammerInf_zero_right (x : ℂ) : (x; (0 : ℂ))_∞ = 1 - x := by
  refine HasProd.tprod_eq ?_
  rw [HasProd, conditional_filter_eq_map_range, tendsto_map'_iff]
  refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
  filter_upwards [eventually_ge_atTop 1] with N hN
  rw [Function.comp_apply, prod_eq_single 0 (fun i _ hi ↦ by simp [zero_pow hi])
    (fun h ↦ absurd (mem_range.mpr hN) h)]
  simp

variable {b : ℂ}

/-- **Jacobi triple product over `ℂ`**, degenerate case `a = 0` (hence `q = 0`). -/
theorem jacobi_triple_product_hasSum'_complex_of_eq_zero :
    HasSum (fun n : ℤ ↦ abPow (-(0 : ℂ)) (-b) n * (0 : ℂ) ^ n.natAbs.choose 2)
      (((0 : ℂ); (0 : ℂ))_∞ * ((0 : ℂ); (0 : ℂ))_∞ * (b; (0 : ℂ))_∞) := by
  have hvanish : ∀ n : ℤ, n ∉ ({-1, 0} : Finset ℤ) →
      abPow (-(0 : ℂ)) (-b) n * (0 : ℂ) ^ n.natAbs.choose 2 = 0 := by
    intro n hn
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hn
    obtain ⟨k, rfl | rfl⟩ := n.eq_nat_or_neg
    · simp [abPow_nat, zero_pow fun (hk : k = 0) ↦ hn.2 (by rw [hk]; rfl)]
    · have hk : 2 ≤ k := by rcases k with _ | _ | k <;> simp_all
      simp [abPow_neg_nat, zero_pow (Nat.choose_pos hk).ne']
  have h : HasSum (fun n : ℤ ↦ abPow (-(0 : ℂ)) (-b) n * (0 : ℂ) ^ n.natAbs.choose 2)
      (∑ n ∈ ({-1, 0} : Finset ℤ), abPow (-(0 : ℂ)) (-b) n * (0 : ℂ) ^ n.natAbs.choose 2) :=
    hasSum_sum_of_ne_finset_zero hvanish
  convert h using 1
  rw [Finset.sum_pair (by norm_num), show (-1 : ℤ) = -((1 : ℕ) : ℤ) by norm_num]
  simp only [qPochhammerInf_zero_right, abPow_neg_nat]
  norm_num
  rw [show (0 : ℤ) = ((0 : ℕ) : ℤ) from rfl, abPow_nat]
  ring

end Degenerate

section Statements

variable {a b q z : ℂ}

/-- `jtpDeg n` is the triangular number `n(n-1)/2`. -/
theorem two_mul_jtpDeg (n : ℤ) : 2 * (jtpDeg n : ℤ) = n * (n - 1) := by
  obtain ⟨k, rfl | rfl⟩ := n.eq_nat_or_neg
  · rw [jtpDeg_nat, Nat.two_mul_cast_choose_two_right]
  · rw [jtpDeg_neg_nat, Nat.cast_add, mul_add, Nat.two_mul_cast_choose_two_right]
    ring

/-- **Jacobi triple product over `ℂ`**: for complex `a, b, q` with `‖q‖ < 1` and `a * b = q`,
`(q; q)_∞ (a; q)_∞ (b; q)_∞ = ∑_{n : ℤ} abPow (-a) (-b) n * q ^ (|n| choose 2)`,
where all products and sums converge.

This is the analytic counterpart of `jacobi_triple_product_hasSum'`, recovered from it by
evaluating the formal identity in `ℤ[T;T⁻¹]⟦X⟧` at `T ↦ a`, `X ↦ q`. -/
theorem jacobi_triple_product_hasSum'_complex (hq : ‖q‖ < 1) (hab : a * b = q) :
    HasSum (fun n : ℤ ↦ abPow (-a) (-b) n * q ^ n.natAbs.choose 2)
      ((q; q)_∞ * (a; q)_∞ * (b; q)_∞) := by
  rcases eq_or_ne a 0 with rfl | ha
  · obtain rfl : q = 0 := by rw [← hab, zero_mul]
    exact jacobi_triple_product_hasSum'_complex_of_eq_zero
  · exact jacobi_triple_product_hasSum'_complex_of_ne_zero ha hq hab

theorem jacobi_triple_product'_complex (hq : ‖q‖ < 1) (hab : a * b = q) :
    (q; q)_∞ * (a; q)_∞ * (b; q)_∞ = ∑' n : ℤ, abPow (-a) (-b) n * q ^ n.natAbs.choose 2 :=
  (jacobi_triple_product_hasSum'_complex hq hab).tsum_eq.symm

/-- **Jacobi triple product over `ℂ`**: for complex `a, b, q` with `‖q‖ < 1` and `a * b = q`,
`(q; q)_∞ (-a; q)_∞ (-b; q)_∞ = ∑_{n : ℤ} abPow a b n * q ^ (|n| choose 2)`.

This is the analytic counterpart of `jacobi_triple_product_hasSum`. -/
theorem jacobi_triple_product_hasSum_complex (hq : ‖q‖ < 1) (hab : a * b = q) :
    HasSum (fun n : ℤ ↦ abPow a b n * q ^ n.natAbs.choose 2)
      ((q; q)_∞ * (-a; q)_∞ * (-b; q)_∞) := by
  simpa using jacobi_triple_product_hasSum'_complex (a := -a) (b := -b) hq (by simpa using hab)

theorem jacobi_triple_product_complex (hq : ‖q‖ < 1) (hab : a * b = q) :
    (q; q)_∞ * (-a; q)_∞ * (-b; q)_∞ = ∑' n : ℤ, abPow a b n * q ^ n.natAbs.choose 2 :=
  (jacobi_triple_product_hasSum_complex hq hab).tsum_eq.symm

/-- **Jacobi triple product**, classical two-variable form: for `‖q‖ < 1` and `z ≠ 0`,
$$\prod_{i \ge 0} (1 - q^{i+1})(1 + z q^i)(1 + z^{-1} q^{i+1}) = \sum_{n \in ℤ} z^n q^{n(n-1)/2}.$$
-/
theorem jacobi_triple_product_theta_hasSum (hq : ‖q‖ < 1) (hz : z ≠ 0) :
    HasSum (fun n : ℤ ↦ z ^ n * q ^ jtpDeg n)
      ((q; q)_∞ * (-z; q)_∞ * (-(z⁻¹ * q); q)_∞) := by
  have hab : z * (z⁻¹ * q) = q := by rw [← mul_assoc, mul_inv_cancel₀ hz, one_mul]
  have heq : (fun n : ℤ ↦ z ^ n * q ^ jtpDeg n)
      = fun n : ℤ ↦ abPow z (z⁻¹ * q) n * q ^ n.natAbs.choose 2 := by
    funext n
    obtain ⟨k, rfl | rfl⟩ := n.eq_nat_or_neg
    · rw [abPow_nat, jtpDeg_nat, Int.natAbs_natCast, zpow_natCast]
    · rw [abPow_neg_nat, jtpDeg_neg_nat, Int.natAbs_neg, Int.natAbs_natCast, zpow_neg,
        zpow_natCast, ← inv_pow, mul_pow, pow_add]
      ring
  rw [heq]
  exact jacobi_triple_product_hasSum_complex hq hab

theorem jacobi_triple_product_theta (hq : ‖q‖ < 1) (hz : z ≠ 0) :
    (q; q)_∞ * (-z; q)_∞ * (-(z⁻¹ * q); q)_∞ = ∑' n : ℤ, z ^ n * q ^ jtpDeg n :=
  (jacobi_triple_product_theta_hasSum hq hz).tsum_eq.symm

end Statements
