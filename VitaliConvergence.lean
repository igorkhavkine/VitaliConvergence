/-
Copyright (c) 2023 Igor Khavkine. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Igor Khavkine
-/

import Mathlib

open Classical Set Filter Topology MeasureTheory NNReal ENNReal


/- missing lemmas/theorems from mathlib4 -/

namespace Set

theorem indicator_tsub {α M : Type*}
    [PartialOrder M] [AddCommMonoid M] [Sub M] [OrderedSub M] (s : Set α) (f g : α → M) :
    (indicator s fun a ↦ f a - g a) = fun a ↦ indicator s f a - indicator s g a := by
  suffices ∀ b, (indicator s fun a ↦ f a - g a) b = (fun a ↦ indicator s f a - indicator s g a) b by
    ext b
    exact this b
  intro b; simp only []
  repeat rw [indicator_apply s]
  by_cases hb : b ∈ s <;> simp only [hb, ite_true, ite_false]
  exact (tsub_zero 0).symm

theorem indicator_tsub' {α M : Type*}
    [PartialOrder M] [AddCommMonoid M] [Sub M] [OrderedSub M] (s : Set α) (f g : α → M) :
    (indicator s (f - g)) = (indicator s f) - (indicator s g) := by
  suffices ∀ b, (indicator s fun a ↦ f a - g a) b = (fun a ↦ indicator s f a - indicator s g a) b by
    ext b
    exact this b
  intro b; simp only []
  repeat rw [indicator_apply s]
  by_cases hb : b ∈ s <;> simp only [hb, ite_true, ite_false]
  exact (tsub_zero 0).symm

end Set

namespace ENNReal

theorem rpow_inv_rpow_self {y : ℝ} (hy : y ≠ 0) (x : ℝ≥0∞) : (x ^ y) ^ (1 / y) = x := by
  rw [← ENNReal.rpow_mul]; field_simp

theorem rpow_self_rpow_inv {y : ℝ} (hy : y ≠ 0) (x : ℝ≥0∞) : (x ^ (1 / y)) ^ y = x := by
  rw [← ENNReal.rpow_mul]; field_simp

end ENNReal


namespace MeasureTheory

variable {α β ι : Type*} {m : MeasurableSpace α} {μ : Measure α} [NormedAddCommGroup β]


/- Counterpart of `tendsto_indicator_ge` from `MeasureTheory.Function.UniformIntegrable`.
   It is used in `lintegral_indicator_compl_le`, so it is more convenient
   to formulate it for `f` valued in `ENNReal`. Could be wrapped with `nnnorm` to make it
   more general. -/
theorem tendsto_ENNReal_indicator_lt (f : α → ℝ≥0∞) (x : α) :
    Tendsto (fun M : ℕ => { x | f x < 1 / (↑M + 1) }.indicator f x) atTop (𝓝 0) := by
  by_cases hfx : f x ≠ 0
  . refine' tendsto_atTop_of_eventually_const (i₀ := Nat.ceil (1 / f x).toReal) fun n hn => _
    rw [Set.indicator_of_not_mem]
    simp only [not_lt, Set.mem_setOf_eq, one_div, inv_le_iff_inv_le]
    simp only [one_div, ge_iff_le, Nat.ceil_le] at hn
    calc
      (f x)⁻¹
        = _ := (ofReal_toReal (inv_ne_top.mpr hfx)).symm
      _ ≤ _ := ENNReal.ofReal_le_ofReal hn
      _ = _ := by norm_cast
      ↑n ≤ ↑n + 1 := by norm_num
  . refine' tendsto_atTop_of_eventually_const (i₀ := 0) fun n _ => _
    simp only [ne_eq, not_not] at hfx
    simp only [mem_setOf_eq, not_lt, indicator_apply_eq_zero]
    intro; assumption


section UnifIntegrable

/- Missing lemmas from the same section of `MeasureTheory.Function.UniformIntegrable`. -/

/-- Uniform integrability is preserved by restriction of functions to a set. -/
theorem UnifIntegrable.indicator {f : ι → α → β} {p : ℝ≥0∞} {μ : Measure α}
  (hui : UnifIntegrable f p μ) (E : Set α)
    : UnifIntegrable (fun i => E.indicator (f i)) p μ := by
  intro ε hε; obtain ⟨δ, hδ_pos, hε⟩ := hui hε
  use δ, hδ_pos; intro i s hs hμs
  dsimp only -- eta reduction
  calc
    ENNReal.ofReal ε ≥ _ := (hε i s hs hμs)
    _ ≥ _ := (snorm_indicator_le _)
    _ = _ := by rw [indicator_indicator, inter_comm, ← indicator_indicator]
  -- alternative: rw [indicator_indicator, inter_comm, ← indicator_indicator]; exact (hδ i s hs hμs).trans' (snorm_indicator_le (s.indicator (f i)))

/-- Uniform integrability is preserved by restriction of measure to measurable set. -/
theorem unifIntegrable_restrict {f : ι → α → β} {p : ℝ≥0∞} {μ : Measure α} {E : Set α}
  (hui : UnifIntegrable f p μ) (hE : MeasurableSet E)
    : UnifIntegrable (fun i => f i) p (μ.restrict E) := by
  intro ε hε; obtain ⟨δ, hδ_pos, hε⟩ := hui hε
  use δ, hδ_pos; intro i s hs hμs
  have hμEs : μ (E ∩ s) ≤ _ := by calc
    _ = _ := by rw [inter_comm]
    _ = (μ.restrict E) s := (μ.restrict_apply hs).symm
    _ ≤ ENNReal.ofReal δ := hμs
  have hEε := (hε i (E ∩ s) (hE.inter hs) hμEs)
  dsimp only at hEε ⊢ -- eta reduction
  calc
    _ = _ := (snorm_indicator_eq_snorm_restrict hE).symm
    _ = _ := by conv => { lhs; rw [indicator_indicator, ← E.inter_self, inter_assoc, ← indicator_indicator] }
    _ = _ := snorm_indicator_eq_snorm_restrict hE
    _ ≤ _ := by exact (snorm_mono_measure _ μ.restrict_le_self)
    _ ≤ ENNReal.ofReal ε := hEε


end UnifIntegrable


section UnifTight

/- This follows closely the `UnifIntegrable` section from `MeasureTheory.Functions.UniformIntegrable`.-/

variable {f g : ι → α → β} {p : ℝ≥0∞}


/-- Definition of being Uniformly Tight. -/
def UnifTight {_ : MeasurableSpace α} (f : ι → α → β) (p : ℝ≥0∞) (μ : Measure α) : Prop :=
  ∀ ⦃ε : ℝ⦄ (_ : 0 < ε), ∃ (s : Set α) (_: MeasurableSet s) (_: μ s < ∞),
    ∀ i, snorm (sᶜ.indicator (f i)) p μ ≤ ENNReal.ofReal ε

namespace UnifTight

protected theorem add (hf : UnifTight f p μ) (hg : UnifTight g p μ) (hp : 1 ≤ p)
    (hf_meas : ∀ i, AEStronglyMeasurable (f i) μ) (hg_meas : ∀ i, AEStronglyMeasurable (g i) μ) :
    UnifTight (f + g) p μ := by
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨s₁, hms₁, hμs₁, hfε₁⟩ := hf hε2
  obtain ⟨s₂, hms₂, hμs₂, hgε₂⟩ := hg hε2
  have hms := hms₁.union hms₂
  refine' ⟨s₁ ∪ s₂, hms, (measure_union_le (μ := μ) s₁ s₂).trans_lt (ENNReal.add_lt_top.mpr ⟨hμs₁,hμs₂⟩), fun i => _⟩
  simp_rw [Pi.add_apply, Set.indicator_add']
  refine' (snorm_add_le ((hf_meas i).indicator hms.compl) ((hg_meas i).indicator hms.compl) hp).trans _
  have hε_halves : ENNReal.ofReal ε = ENNReal.ofReal (ε / 2) + ENNReal.ofReal (ε / 2) := by
    rw [← ENNReal.ofReal_add hε2.le hε2.le, add_halves]
  rw [compl_union]
  calc
    _ = snorm (indicator (s₂ᶜ ∩ s₁ᶜ) (f i)) p μ + _ := by
        congr; rw [inter_comm]
    _ ≤ snorm (indicator s₁ᶜ (f i)) p μ + snorm (indicator s₂ᶜ (g i)) p μ := by
        gcongr <;> rw [← indicator_indicator] <;> exact snorm_indicator_le _
    _ ≤ _ := add_le_add (hfε₁ i) (hgε₂ i)
    _ = _ := hε_halves.symm

protected theorem neg (hf : UnifTight f p μ) : UnifTight (-f) p μ := by
  simp_rw [UnifTight, Pi.neg_apply, Set.indicator_neg', snorm_neg]
  exact hf

protected theorem sub (hf : UnifTight f p μ) (hg : UnifTight g p μ) (hp : 1 ≤ p)
    (hf_meas : ∀ i, AEStronglyMeasurable (f i) μ) (hg_meas : ∀ i, AEStronglyMeasurable (g i) μ) :
    UnifTight (f - g) p μ := by
  rw [sub_eq_add_neg]
  exact hf.add hg.neg hp hf_meas fun i => (hg_meas i).neg


protected theorem ae_eq (hf : UnifTight f p μ) (hfg : ∀ n, f n =ᵐ[μ] g n) :
    UnifTight g p μ := by
  intro ε hε
  obtain ⟨s, hms, hμs, hfε⟩ := hf hε
  refine' ⟨s, hms, hμs, fun n /-s hs hμs-/ => (le_of_eq <| snorm_congr_ae _).trans (hfε n)⟩
  filter_upwards [hfg n] with x hx
  simp only [indicator, mem_compl_iff, ite_not, hx]

end UnifTight


/-- Core lemma to be used in `MeasureTheory.Memℒp.snorm_indicator_compl_le`. -/
theorem lintegral_indicator_compl_le /- (hp_one : 1 ≤ p) (hp_top : p ≠ ∞) -/
    {g : α → ℝ≥0∞} (haesmg : AEStronglyMeasurable g μ) (hg : ∫⁻ a, g a ∂μ < ∞)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (s : Set α) (_ : MeasurableSet s) (_ : μ s < ∞),
      ∫⁻ a, (sᶜ.indicator g) a ∂μ ≤ ENNReal.ofReal ε := by
  -- come up with an a.e. equal strongly measurable replacement `f` for `g`
  have hsmf := haesmg.stronglyMeasurable_mk
  have hgf := haesmg.ae_eq_mk
  set f := haesmg.mk
  have hf := calc
    _ = _ := (lintegral_congr_ae hgf).symm
    _ < ∞ := hg
  conv => -- replace `g` by `f` in goal
    enter [1, s, 1, hms, 1, hμs]
    rw [lintegral_congr_ae hgf.indicator]
    rfl
  -- set up a sequence of vertical cutoffs of f by 1/(M+1)
  have hmeas_lt : ∀ M : ℕ, MeasurableSet { x | f x < 1 / (↑M + 1) } := by
    intro M
    apply StronglyMeasurable.measurableSet_lt hsmf stronglyMeasurable_const
  have hmeas : ∀ M : ℕ, Measurable ({ x | f x < 1 / (↑M + 1) }.indicator f) := by
    intro M
    apply StronglyMeasurable.measurable
    apply hsmf.indicator
    apply hmeas_lt M
  -- show that the sequence a.e. converges to 0
  have htendsto :
      ∀ᵐ x ∂μ, Tendsto (fun M : ℕ => { x | f x < 1 / (↑M + 1) }.indicator f x) atTop (𝓝 0) :=
    univ_mem' (id fun x => tendsto_ENNReal_indicator_lt f x)
  -- use Lebesgue dominated convergence to show that the integrals eventually go to zero
  have : Tendsto (fun n : ℕ ↦ ∫⁻ a, { x | f x < 1 / (↑n + 1) }.indicator f a ∂μ)
      atTop (𝓝 (∫⁻ (_ : α), 0 ∂μ)) := by
    refine' tendsto_lintegral_of_dominated_convergence _ hmeas _ hf.ne htendsto
    -- show that the sequence is bounded by f (which is integrable)
    refine' fun n => univ_mem' (id fun x => _)
    by_cases hx : f x < 1 / (↑n + 1)
    · dsimp
      rwa [Set.indicator_of_mem]
    · dsimp
      rw [Set.indicator_of_not_mem]
      · exact zero_le _
      · assumption
  -- rewrite limit to be more usable and get the sufficiently large M, so the integral is < ε
  rw [lintegral_zero, ENNReal.tendsto_atTop_zero] at this
  obtain ⟨M, hM⟩ := this (ENNReal.ofReal ε) (ENNReal.ofReal_pos.2 hε)
  simp only [true_and_iff, ge_iff_le, zero_tsub, zero_le, sub_zero, zero_add, coe_nnnorm,
    Set.mem_Icc] at hM
  -- the target estimate is now in hM
  have hM := hM M le_rfl
  -- let s be the complement of the integration domain in hM, prove its measurability and finite measure
  have : { x | f x < 1 / (↑M + 1) } = { x | 1 / (↑M + 1) ≤ f x }ᶜ := by
    apply Set.ext; intro x
    simp only [mem_compl_iff, mem_setOf_eq, not_le]
  have hms := (hmeas_lt M).compl
  rw [this] at hM hms
  rw [compl_compl] at hms
  have hμs := calc
    μ { x | 1 / (↑M + 1) ≤ f x }
      ≤ _ := meas_ge_le_lintegral_div hsmf.aemeasurable (by norm_num) (by norm_num)
    _ < ∞ := by apply div_lt_top hf.ne (by norm_num)
  set s := { x | 1 / (↑M + 1) ≤ f x }
  -- fulfill the goal
  use s, hms, hμs, hM


/-- A single function that is `Memℒp f p μ` is tight wrt to `μ`. -/
theorem Memℒp.snorm_indicator_compl_le (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    {f : α → β} (hf : Memℒp f p μ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ (s : Set α) (_ : MeasurableSet s) (_ : μ s < ∞),
      snorm (sᶜ.indicator f) p μ ≤ ENNReal.ofReal ε := by
  -- The proof unwraps `Memℒp f p μ` and applies the analogous result for `lintegral`.
  -- do some arithmetic that will come in useful
  have hp_pos := zero_lt_one.trans_le hp_one
  have hp_nz := hp_pos.ne.symm
  have hrp_pos : 0 < p.toReal := ENNReal.toReal_pos hp_nz hp_top
  have hεp : 0 < ε ^ p.toReal := by simp only [Real.rpow_pos_of_pos, hε] --exact Real.rpow_pos_of_pos hε p.toReal
  -- decode Memℒp into a.e. strong measurability and finite snorm
  obtain ⟨haesmf, hsnf⟩ := hf
  -- transform snorm to lintegral
  rw [snorm_eq_snorm' (by assumption) (by assumption)] at hsnf
  have hinpf := calc
    _ = _ := lintegral_rpow_nnnorm_eq_rpow_snorm' hrp_pos
    _ < ∞ := (rpow_lt_top_iff_of_pos hrp_pos).mpr hsnf --by sorry
  -- get a.e. strong measurability for the integrand
  -- XXX: why does `AEStronglyMeasurable.ennnorm` only give the weaker AEMeasurable?
  have haesmnf := (ENNReal.continuous_coe.comp_aestronglyMeasurable haesmf.nnnorm)
  have haesmnpf := (@ENNReal.continuous_rpow_const p.toReal).comp_aestronglyMeasurable haesmnf
  -- use core result for lintegral, the target estimate will be in `hsfε`
  obtain ⟨s, hms, hμs, hsfε⟩ := lintegral_indicator_compl_le haesmnpf hinpf hεp
  use s, hms, hμs
  -- move indicator through function compositions, XXX: is this simp-able?
  rw [← Function.comp_def (fun x : ℝ≥0∞ => x ^ p.toReal)] at hsfε
  rw [← Function.comp_def ENNReal.ofNNReal] at hsfε
  rw [← Function.comp_def nnnorm] at hsfε
  rw [sᶜ.indicator_comp_of_zero (@ENNReal.zero_rpow_of_pos p.toReal hrp_pos)] at hsfε
  rw [sᶜ.indicator_comp_of_zero ENNReal.coe_zero] at hsfε
  rw [sᶜ.indicator_comp_of_zero nnnorm_zero] at hsfε
  rw [Function.comp_def nnnorm] at hsfε
  rw [Function.comp_def ENNReal.ofNNReal] at hsfε
  rw [Function.comp_def (fun x : ℝ≥0∞ => x ^ p.toReal)] at hsfε
  -- convert lintegral to snorm
  rw [lintegral_rpow_nnnorm_eq_rpow_snorm' hrp_pos] at hsfε
  rw [← snorm_eq_snorm' (by assumption) (by assumption)] at hsfε
  -- commute ENNReal coersion with rpow, use rpow monotonicity
  rw [← ofReal_rpow_of_pos (by assumption)] at hsfε
  rw [ENNReal.rpow_le_rpow_iff hrp_pos] at hsfε
  exact hsfε


/-- A constant function is uniformly integrable. -/
theorem unifTight_const {g : α → β} (hp : 1 ≤ p) (hp_ne_top : p ≠ ∞) (hg : Memℒp g p μ) :
    UnifTight (fun _ : ι => g) p μ := by
  intro ε hε
  obtain ⟨s, hms, hμs, hgε⟩ := hg.snorm_indicator_compl_le hp hp_ne_top hε
  exact ⟨s, hms, hμs, fun _ => hgε⟩

/-- A single function is uniformly integrable. -/
theorem unifTight_subsingleton [Subsingleton ι] (hp_one : 1 ≤ p) (hp_top : p ≠ ∞)
    {f : ι → α → β} (hf : ∀ i, Memℒp (f i) p μ) : UnifTight f p μ := by
  intro ε hε
  by_cases hι : Nonempty ι
  · cases' hι with i
    obtain ⟨s, hms, hμs, hfε⟩ := (hf i).snorm_indicator_compl_le hp_one hp_top hε
    refine' ⟨s, hms, hμs, fun j => _⟩
    convert hfε
  · exact ⟨∅, (by measurability), (by measurability),
      fun i => False.elim <| hι <| Nonempty.intro i⟩


/-- This lemma is less general than `MeasureTheory.unifIntegrable_finite` which applies to
all sequences indexed by a finite type. -/
theorem unifTight_fin (hp_one : 1 ≤ p) (hp_top : p ≠ ∞) {n : ℕ} {f : Fin n → α → β}
    (hf : ∀ i, Memℒp (f i) p μ) : UnifTight f p μ := by
  revert f
  induction' n with n h
  · intro f hf
    have : Subsingleton (Fin Nat.zero) := subsingleton_fin_zero -- Porting note: Added this instance
    exact unifTight_subsingleton hp_one hp_top hf
  intro f hfLp ε hε
  let g : Fin n → α → β := fun k => f k
  have hgLp : ∀ i, Memℒp (g i) p μ := fun i => hfLp i
  obtain ⟨S, hmS, hμS, hFε⟩ := h hgLp hε
  obtain ⟨s, hms, hμs, hfε⟩ := (hfLp n).snorm_indicator_compl_le hp_one hp_top hε
  refine' ⟨s ∪ S, (by measurability), (by measurability),
    fun i => _⟩
  by_cases hi : i.val < n
  · rw [(_ : f i = g ⟨i.val, hi⟩)]
    · rw [compl_union, ← indicator_indicator]
      apply (snorm_indicator_le _).trans
      exact hFε (Fin.castLT i hi)
    · simp only [Fin.coe_eq_castSucc, Fin.castSucc_mk, Fin.eta]
  · rw [(_ : i = n)]
    · rw [compl_union, inter_comm, ← indicator_indicator]
      apply (snorm_indicator_le _).trans
      exact hfε
    · have hi' := Fin.is_lt i
      rw [Nat.lt_succ_iff] at hi'
      rw [not_lt] at hi
      -- Porting note: Original proof was `simp [← le_antisymm hi' hi]`
      ext; symm; rw [Fin.coe_ofNat_eq_mod, le_antisymm hi' hi, Nat.mod_succ_eq_iff_lt, Nat.lt_succ]

/-- A finite sequence of Lp functions is uniformly integrable. -/
theorem unifTight_finite [Finite ι] (hp_one : 1 ≤ p) (hp_top : p ≠ ∞) {f : ι → α → β}
    (hf : ∀ i, Memℒp (f i) p μ) : UnifTight f p μ := by
  obtain ⟨n, hn⟩ := Finite.exists_equiv_fin ι
  intro ε hε
  set g : Fin n → α → β := f ∘ hn.some.symm with hgeq
  have hg : ∀ i, Memℒp (g i) p μ := fun _ => hf _
  obtain ⟨s, hms, hμs, hfε⟩ := unifTight_fin hp_one hp_top hg hε
  refine' ⟨s, hms, hμs, fun i => _⟩
  specialize hfε (hn.some i)
  simp_rw [hgeq, Function.comp_apply, Equiv.symm_apply_apply] at hfε
  assumption

end UnifTight


section VitaliConvergence

/- XXX: In the analogous place in MeasureTheory.Function.UniformIntegrable, the measure variable
   is declared `(μ)` non-implicit. I don't see why, as in all relevant cases it can be
   deduced from other arguments. -/
variable {μ : Measure α} {p : ℝ≥0∞}

variable {f : ℕ → α → β} {g : α → β}

/- Both directions and an iff version of Vitali's convergence theorem on measure spaces
   of not necesserily finite volume. See `Thm III.6.15` of Dunford & Schwartz, Part I (1958). -/

/- We start with the reverse direction. We only need to show that uniform tightness follows
   from convergence in Lp. Mathlib already has the analogous `unifIntegrable_of_tendsto_Lp`
   and `tendstoInMeasure_of_tendsto_snorm`. -/

/-- Intermediate lemma for `unifTight_of_tendsto_Lp`. -/
theorem unifTight_of_tendsto_Lp_zero (hp : 1 ≤ p) (hp' : p ≠ ∞) (hf : ∀ n, Memℒp (f n) p μ)
    (hf_tendsto : Tendsto (fun n => snorm (f n) p μ) atTop (𝓝 0)) : UnifTight f p μ := by
  intro ε hε
  rw [ENNReal.tendsto_atTop_zero] at hf_tendsto
  obtain ⟨N, hNε⟩ := hf_tendsto (ENNReal.ofReal ε) (by simpa only [gt_iff_lt, ofReal_pos])
  let F : Fin N → α → β := fun n => f n
  have hF : ∀ n, Memℒp (F n) p μ := fun n => hf n
  obtain ⟨s, hms, hμs, hFε⟩ := unifTight_fin hp hp' hF hε
  refine' ⟨s, hms, hμs, fun n => _⟩
  by_cases hn : n < N
  · exact hFε ⟨n, hn⟩
  · exact (snorm_indicator_le _).trans (hNε n (not_lt.mp hn))

/-- Convergence in Lp implies uniform tightness. -/
theorem unifTight_of_tendsto_Lp (hp : 1 ≤ p) (hp' : p ≠ ∞) (hf : ∀ n, Memℒp (f n) p μ)
    (hg : Memℒp g p μ) (hfg : Tendsto (fun n => snorm (f n - g) p μ) atTop (𝓝 0)) :
    UnifTight f p μ := by
  have : f = (fun _ => g) + fun n => f n - g := by ext1 n; simp
  rw [this]
  refine' UnifTight.add _ _ hp (fun _ => hg.aestronglyMeasurable)
      fun n => (hf n).1.sub hg.aestronglyMeasurable
  · exact unifTight_const hp hp' hg
  · exact unifTight_of_tendsto_Lp_zero hp hp' (fun n => (hf n).sub hg) hfg


/- Next we deal with the forward direction. The `Memℒp` and `TendstoInMeasure` hypotheses
   are unwrapped and strengthened to by known lemmas to have in addition `StrongMeasurable`
   and a.e. convergence. The bulk of the proof is done under these stronger hyptheses. -/

theorem tendsto_Lp_notFinite_of_tendsto_ae_of_meas (hp : 1 ≤ p) (hp' : p ≠ ∞)
    {f : ℕ → α → β} {g : α → β} (hf : ∀ n, StronglyMeasurable (f n)) (hg : StronglyMeasurable g)
    (hg' : Memℒp g p μ) (hui : UnifIntegrable f p μ) (hut : UnifTight f p μ)
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => snorm (f n - g) p μ) atTop (𝓝 0) := by
  rw [ENNReal.tendsto_atTop_zero]
  intro ε hε
  by_cases hfinε : ε ≠ ∞; swap
  · rw [not_ne_iff.mp hfinε]; exact ⟨0, fun n _ => le_top⟩
  by_cases hμ : μ = 0
  · rw [hμ]; use 0; intro n _; rw [snorm_measure_zero]; exact zero_le ε
  have hε'' : ε / 3 ≠ ∞ := (ENNReal.div_lt_top (by assumption) (by norm_num)).ne
  have hε' : 0 < ε / 3 := ENNReal.div_pos hε.ne.symm (by norm_num)
  have hrε' : 0 < (ε / 3).toReal := ENNReal.toReal_pos hε'.ne.symm (by assumption)
  -- use tightness to divide the domain into interior and exterior
  obtain ⟨Eg, hmEg, hμEg, hgε⟩ := Memℒp.snorm_indicator_compl_le hp hp' hg' hrε'
  obtain ⟨Ef, hmEf, hμEf, hfε⟩ := hut hrε'
  have hmE := hmEf.union hmEg
  have hfmE := (measure_union_le Ef Eg).trans_lt (add_lt_top.mpr ⟨hμEf, hμEg⟩)
  set E : Set α := Ef ∪ Eg
  -- use uniform integrability to get control on the limit over E
  have hgE' := Memℒp.restrict E hg'
  have huiE := unifIntegrable_restrict hui hmE
  have hfgE : (∀ᵐ x ∂(μ.restrict E), Tendsto (fun n => f n x) atTop (𝓝 (g x))) := ae_restrict_of_ae hfg
  have ffmE : Fact _ := { out := hfmE }
  have ifmE := @Restrict.isFiniteMeasure _ _ _ μ ffmE  -- XXX: any way to do this without explitizing all arguments?
  have hInner := tendsto_Lp_of_tendsto_ae_of_meas (μ.restrict E) hp hp' hf hg hgE' huiE hfgE
  rw [ENNReal.tendsto_atTop_zero] at hInner
  -- get a sufficiently large N for given ε, and consider any n ≥ N
  obtain ⟨N, hfngε⟩ := hInner (ε / 3) hε'
  use N; intro n hn
  -- get interior estimates
  have hmfngE : AEStronglyMeasurable _ μ := (((hf n).sub hg).indicator hmE).aestronglyMeasurable
  have hfngEε := calc
    snorm (E.indicator (f n - g)) p μ
      = _ := snorm_indicator_eq_snorm_restrict hmE
    _ ≤ ε / 3 := hfngε n hn
  -- get exterior estimates
  have hmgEc : AEStronglyMeasurable _ μ := (hg.indicator hmE.compl).aestronglyMeasurable
  have hgEcε := calc
    snorm (Eᶜ.indicator g) p μ
      ≤ _ := by
        unfold_let; rw [compl_union, ← indicator_indicator]
    _ ≤ _ := snorm_indicator_le _
    _ ≤ _ := hgε
    _ = ε / 3 := ENNReal.ofReal_toReal hε''
  have hmfnEc : AEStronglyMeasurable _ μ := ((hf n).indicator hmE.compl).aestronglyMeasurable
  have hfnEcε : snorm (Eᶜ.indicator (f n)) p μ ≤ ε / 3 := calc
    snorm (Eᶜ.indicator (f n)) p μ
      ≤ _ := by
        unfold_let; rw [compl_union, inter_comm, ← indicator_indicator]
    _ ≤ _ := snorm_indicator_le _
    _ ≤ _ := hfε n
    _ = ε / 3 := ENNReal.ofReal_toReal hε''
  have hmfngEc : AEStronglyMeasurable _ μ := (((hf n).sub hg).indicator hmE.compl).aestronglyMeasurable
  have hfngEcε := calc
    snorm (Eᶜ.indicator (f n - g)) p μ
      = _ := by rw [(Eᶜ.indicator_sub' _ _)]
    _ ≤ _ := by apply snorm_sub_le (by assumption) (by assumption) hp
    _ ≤ ε / 3 + ε / 3 := add_le_add hfnEcε hgEcε
  -- finally, combine interior and exterior estimates
  calc
    snorm (f n - g) p μ
      = snorm (Eᶜ.indicator (f n - g) + E.indicator (f n - g)) p μ := by
        congr; exact (E.indicator_compl_add_self _).symm
    _ ≤ _ := by
        apply snorm_add_le (by assumption) (by assumption) hp
    _ ≤ (ε / 3 + ε / 3) + ε / 3 := add_le_add hfngEcε hfngEε
    _ = ε := by simp only [ENNReal.add_thirds] --ENNReal.add_thirds ε

/- Lemma used in `tendsto_Lp_notFinite_of_tendsto_ae`. Alternative name: `ae_tendsto_ae_congr`? -/
theorem tendsto_ae_congr_ae {f f' : ℕ → α → β} {g g' : α → β}
    (hff' : ∀ (n : ℕ), f n =ᵐ[μ] f' n) (hgg' : g =ᵐ[μ] g')
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)))
    : ∀ᵐ x ∂μ, Tendsto (fun n => f' n x) atTop (𝓝 (g' x)) := by
  have hff'' := eventually_countable_forall.mpr hff'
  filter_upwards [hff'', hgg', hfg] with x hff'x hgg'x hfgx
  apply Tendsto.congr hff'x
  rw [← hgg'x]; exact hfgx

theorem tendsto_Lp_notFinite_of_tendsto_ae (hp : 1 ≤ p) (hp' : p ≠ ∞)
    {f : ℕ → α → β} {g : α → β} (haef : ∀ n, AEStronglyMeasurable (f n) μ)
    (hg' : Memℒp g p μ) (hui : UnifIntegrable f p μ) (hut : UnifTight f p μ)
    (hfg : ∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x))) :
    Tendsto (fun n => snorm (f n - g) p μ) atTop (𝓝 0) := by
  -- come up with an a.e. equal strongly measurable replacement `f` for `g`
  have hf := fun n => (haef n).stronglyMeasurable_mk
  have hff' := fun n => (haef n).ae_eq_mk (μ := μ)
  have hui' := hui.ae_eq hff'
  have hut' := hut.ae_eq hff'
  have hg := hg'.aestronglyMeasurable.stronglyMeasurable_mk
  have hgg' := hg'.aestronglyMeasurable.ae_eq_mk (μ := μ)
  have hg'' := hg'.ae_eq hgg'
  have haefg' := tendsto_ae_congr_ae hff' hgg' hfg
  set f' := fun n => (haef n).mk (μ := μ)
  set g' := hg'.aestronglyMeasurable.mk (μ := μ)
  have haefg (n : ℕ) : f n - g =ᵐ[μ] f' n - g' := (hff' n).sub hgg'
  have hsnfg (n : ℕ) := snorm_congr_ae (p := p) (haefg n)
  apply Filter.Tendsto.congr (fun n => (hsnfg n).symm)
  exact tendsto_Lp_notFinite_of_tendsto_ae_of_meas hp hp' hf hg hg'' hui' hut' haefg'


/-- Forward direction of Vitali's convergence theorem (non-finite version):
    if `f` is a sequence of uniformly integrable, uniformly tight functions that converge in
    measure to some function `g` in a finite measure space, then `f` converge in Lp to `g`. -/
theorem tendsto_Lp_notFinite_of_tendstoInMeasure (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hf : ∀ n, AEStronglyMeasurable (f n) μ) (hg : Memℒp g p μ)
    (hui : UnifIntegrable f p μ) (hut : UnifTight f p μ)
    (hfg : TendstoInMeasure μ f atTop g) : Tendsto (fun n => snorm (f n - g) p μ) atTop (𝓝 0) := by
  refine' tendsto_of_subseq_tendsto fun ns hns => _
  obtain ⟨ms, _, hms'⟩ := TendstoInMeasure.exists_seq_tendsto_ae fun ε hε => (hfg ε hε).comp hns
  exact ⟨ms,
    tendsto_Lp_notFinite_of_tendsto_ae hp hp' (fun _ => hf _) hg
      (fun ε hε => -- `UnifIntegrable` on a subsequence
        let ⟨δ, hδ, hδ'⟩ := hui hε
        ⟨δ, hδ, fun i s hs hμs => hδ' _ s hs hμs⟩)
      (fun ε hε => -- `UnifTight` on a subsequence
        let ⟨s, hms, hμs, hfε⟩ := hut hε
        ⟨s, hms, hμs, fun i => hfε _⟩)
      hms'⟩


/-- **Vitali's convergence theorem** (non-finite measure version):
    A sequence of functions `f` converges to `g` in Lp
    if and only if it is uniformly integrable, uniformly tight and to `g` in measure. -/
theorem tendstoInMeasure_notFinite_iff_tendsto_Lp (hp : 1 ≤ p) (hp' : p ≠ ∞)
    (hf : ∀ n, Memℒp (f n) p μ) (hg : Memℒp g p μ) :
    /-(∀ᵐ x ∂μ, Tendsto (fun n => f n x) atTop (𝓝 (g x)))-/ TendstoInMeasure μ f atTop g ∧ UnifIntegrable f p μ ∧ UnifTight f p μ
      ↔ Tendsto (fun n => snorm (f n - g) p μ) atTop (𝓝 0) := --by
  ⟨fun h => tendsto_Lp_notFinite_of_tendstoInMeasure hp hp' (fun n => (hf n).1) hg h.2.1 h.2.2 h.1,
    fun h =>
    ⟨tendstoInMeasure_of_tendsto_snorm (lt_of_lt_of_le zero_lt_one hp).ne.symm
        (fun n => (hf n).aestronglyMeasurable) hg.aestronglyMeasurable h,
      unifIntegrable_of_tendsto_Lp μ hp hp' hf hg h,
      unifTight_of_tendsto_Lp hp hp' hf hg h⟩⟩

#print axioms tendstoInMeasure_notFinite_iff_tendsto_Lp

end VitaliConvergence


end MeasureTheory
