import Mathlib

local macro_rules | `($x ^ $y)   => `(HPow.hPow $x $y)

-- TODO: Fix precedence in the `IsBigO` notation, and use the same fix for `EqModBigO`.

open Filter Topology Asymptotics Real

section functions_simps /- Uninteresting lemmas missing from Mathlib. -/

@[simp] lemma Pi.inv_pow_mul_inv_pow (a b : ℕ) :
    ((fun n : ℕ ↦ 1 / (n : ℝ)^a)*fun n : ℕ ↦ 1 / (n : ℝ)^b) = (fun n : ℕ ↦ 1 / (n : ℝ)^(a+b)) := by
  ext n
  field_simp
  ring

@[simp] lemma Pi.inv_mul_inv :
    ((fun n : ℕ ↦ 1 / (n : ℝ)) * fun n : ℕ ↦ 1 / (n : ℝ)) = (fun n : ℕ ↦ 1 / (n : ℝ)^2) := by
  simpa using Pi.inv_pow_mul_inv_pow 1 1

lemma Pi.mul_eq {α β : Type*} [Mul β] (f g : α → β) : f*g = fun x ↦ (f x * g x) := rfl

end functions_simps

section limits_and_computations /- Elementary limits and estimates missing from Mathlib. -/

lemma tendsto_inv_pow_pos {a : ℕ} (ha : a ≠ 0) :
    Tendsto (fun x : ℝ ↦ 1 / x^a) atTop (𝓝 0) := by
  have : ∀ x : ℝ, 1/x^a = x^(-a : ℤ) := by intro x; simp
  simp only [this, tendsto_pow_neg_atTop ha]

lemma tendsto_pow_div_log (a : ℤ) {b : ℕ} (hb : b ≠ 0) :
    Tendsto (fun x ↦ (log x)^a / x^b) atTop (𝓝 0) := by
  have hb' := Nat.pos_of_ne_zero hb
  by_cases ha : a = 0
  · simp_rw [ha, zpow_zero]
    exact tendsto_inv_pow_pos hb
  rw [← Asymptotics.isLittleO_iff_tendsto]
  · simp only [← rpow_int_cast, ← rpow_nat_cast]
    apply isLittleO_log_rpow_rpow_atTop
    exact_mod_cast hb'
  · intro x hx
    simp [(pow_eq_zero_iff hb').mp hx, zero_zpow a ha]

lemma tendsto_log_div_id  :
    Tendsto (fun x ↦ log x / x) atTop (𝓝 0) := by
  simpa using tendsto_pow_div_log 1 one_ne_zero

lemma tendsto_log_div_id_nat_cast :
    Tendsto (fun n : ℕ ↦ log n / n) atTop (𝓝 0) :=
  tendsto_log_div_id.comp tendsto_nat_cast_atTop_atTop

lemma log_add_one (x : ℝ) : log (x + 1) = log x + log (1 + 1/x) := by
  by_cases hx : x = 0
  · simp [hx]
  by_cases hx' : x = -1
  · simp [hx']
  rw [← log_mul hx, mul_add, mul_one, mul_div_cancel' 1 hx]
  field_simp
  simpa [eq_neg_iff_add_eq_zero] using hx'

lemma isLittleO_rpow_log_div_rpow (a c : ℝ) {b d : ℝ} (hbd : d < b) :
    (fun x ↦ (log x)^a / x^b) =o[atTop] (fun x ↦ (log x)^c / x^d) := by
  have A : ∀ᶠ x in atTop, 0 < x ∧ 0 < log x :=
    (eventually_gt_atTop 0).and (tendsto_log_atTop.eventually_gt_atTop 0)
  have : (fun x ↦ log x ^ a / x ^ b / (log x ^ c / x ^ d)) =ᶠ[atTop]
      fun x ↦ log x ^ (a - c) / (x ^ (b - d)) :=
    A.mono fun x ⟨h₁, h₂⟩ ↦ by beta_reduce; rw [rpow_sub, rpow_sub, div_div_div_comm] <;> positivity
  rw [Asymptotics.isLittleO_iff_tendsto']
  · apply Tendsto.congr' this.symm
    exact (isLittleO_log_rpow_rpow_atTop _ (sub_pos.2 hbd)).tendsto_div_nhds_zero
  · refine A.mono fun _ _ ↦ ?_
    simp [rpow_pos_of_pos, *, ne_of_gt]

lemma isLittleO_pow_log_div_pow (a c : ℕ) {b d : ℕ} (hbd : d < b) :
    (fun x ↦ (log x)^a / x^b) =o[atTop] (fun x ↦ (log x)^c / x^d) := by
  simp only [← rpow_nat_cast, isLittleO_rpow_log_div_rpow a c (Nat.cast_lt.mpr hbd)]

lemma isLittleO_log_div_pow {b d : ℕ} (hbd : d < b) :
    (fun x ↦ (log x) / x^b) =o[atTop] (fun x ↦ (log x) / x^d) := by
  simpa using isLittleO_pow_log_div_pow 1 1 hbd

lemma isLittleO_inv_pow_pos_log {b d : ℕ} (hbd : d < b) :
    (fun x : ℝ ↦ 1 / (x ^b)) =o[atTop] (fun x ↦ (log x) / x^d) := by
  simpa using isLittleO_pow_log_div_pow 0 1 hbd

@[simp]
lemma seq_exp_log_eventually_eq : (fun (n : ℕ) ↦ exp (log n)) =ᶠ[atTop] fun n ↦ n := by
  apply (eventually_gt_atTop 0).mono (fun n hn ↦ ?_)
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  simp [exp_log hn']

@[simp]
lemma eventually_mul_div_cancel (f : ℝ → ℝ) :
    (id * fun x ↦ f x/x)  =ᶠ[atTop] f := by
  apply (eventually_gt_atTop 0).mono (fun n hn ↦ ?_)
  field_simp ; ring

@[simp]
lemma eventually_mul_div_cancel_seq (f : ℕ → ℝ) :
    ((fun n : ℕ ↦ (n:ℝ)) * fun n ↦ f n/(n : ℝ)) =ᶠ[atTop] f := by
  apply (eventually_gt_atTop 0).mono (fun n hn ↦ ?_)
  field_simp ; ring

open Asymptotics

lemma Filter.Tendsto.isBigO_mul_atTop {ι : Type*} {l : Filter ι} {f : ι → ℝ}
    (h : Tendsto f l atTop)  (g : ι → ℝ) : g =O[l] (f*g) := by
  apply IsBigO.of_bound'
  apply (tendsto_atTop.1 h 1).mono
  intro i hi
  simp only [norm_eq_abs, Pi.mul_apply, norm_mul]
  exact le_mul_of_one_le_left (abs_nonneg _) (hi.trans (le_abs_self _))

lemma Filter.Tendsto.isBigO_mul_nhds {ι : Type*} {l : Filter ι} {f : ι → ℝ} {x : ℝ}
    (h : Tendsto f l (𝓝 x)) (g : ι → ℝ) : (f*g) =O[l] g := by
  apply IsBigO.of_bound
  swap ; exact ‖x‖ + 1
  have hf' : Tendsto (fun i ↦ ‖f i‖) l (𝓝 ‖x‖) := norm h
  have : ∀ᶠ i in l, |f i| ≤ |x| + 1 := by
    have : Set.Iic (‖x‖ + 1) ∈ 𝓝  ‖x‖ := Iic_mem_nhds (by linarith)
    exact hf' this
  apply this.mono
  intro i hi
  simp
  gcongr

lemma Filter.Tendsto.isBigO_mul_nhds' {ι : Type*} {l : Filter ι} {f : ι → ℝ} {x : ℝ}
    (h : Tendsto f l (𝓝 x)) (g : ι → ℝ) : (g*f) =O[l] g := by
  rw [mul_comm]
  exact h.isBigO_mul_nhds g

lemma Filter.Tendsto.isBigO_inv {ι : Type*} {l : Filter ι} {f g : ι → ℝ} (h : Tendsto f l atTop) :
    (1/g) =O[l] (f/g) := by
  apply IsBigO.of_bound'
  apply (tendsto_atTop.1 h 1).mono
  intro i hi
  simp only [Pi.div_apply, Pi.one_apply, norm_eq_abs, norm_div]
  gcongr
  rw [abs_one]
  exact hi.trans (le_abs_self _)

end limits_and_computations

attribute [simp] isBigO_refl EventuallyEq.rfl

/-! # Equality modulo BigO. -/

namespace Asymptotics
variable {α : Type*} {E : Type*} {F : Type*} [SeminormedAddCommGroup E] [SeminormedAddCommGroup F]

/-- Placeholder for a tactic discharging easy asymptotic side conditions. -/
macro "asymp" : tactic => `(tactic| simp)

def EqModBigO (l : Filter α) (h : α → F) (f g : α → E) : Prop := (f - g) =O[l] h

notation:50 f " = " g " + O[" l "](" h")" => EqModBigO l h f g

variable {l : Filter α}

@[simp]
lemma eqModBigO_self (f : α → E) (h₁ : α → F) : f = f + O[l](h₁) := by
  unfold EqModBigO
  simp
  apply isBigO_zero

lemma EqModBigO.congr {f f' g g' : α → E} {h h' : α → F} (hf : f = g + O[l](h))
    (hff' : f  =ᶠ[l] f' := by simp) (hgg' : g  =ᶠ[l] g' := by simp) (hhh' : h  =ᶠ[l] h' := by simp) :
    f' = g' + O[l](h') :=
  (isBigO_congr (hff'.sub hgg') hhh').mp hf

lemma eqModBigO_of_eq {f g : α → E} {h₁ : α → F} (eq : ∀ x, f x = g x) :
    f = g + O[l](h₁) := by
  have : f - g = 0 := by ext x; simp [eq]
  simp [EqModBigO, this]
  apply isBigO_zero

lemma isBigO_of_eq {f g : α → E} (eq : ∀ x, f x = g x) : f =O[l] g := by
  simp [show f = g from funext eq]

lemma EqModBigO.isBigO {f g : α → E} {h : α → F}
    (hfg : f = g + O[l](h)) (hg : g =O[l] h) : f =O[l] h := by
  simpa using (IsBigO.add hfg hg)

@[simp]
lemma EqModBigO.isBigO_zero {f : α → E} {h : α → F} :
    f = 0 + O[l](h) ↔ f =O[l] h := by
  simp [EqModBigO]

@[simp]
lemma EqModBigO.isBigO_zero' {f : α → E} {h : α → F} :
    f = (fun _ ↦ 0) + O[l](h) ↔ f =O[l] h :=
  EqModBigO.isBigO_zero

lemma EqModBigO.isBigO' {f g : α → E} {h₁ h₂ : α → F}
    (hfg : f = g + O[l](h₁)) (hg : g =O[l] h₂)
    (h₁h₂ : h₁ =O[l] h₂ := by asymp) : f =O[l] h₂ := by
  simpa using (IsBigO.trans hfg h₁h₂).add  hg

/-! # Transitivity and basic calc block support -/
section Trans

lemma EqModBigO.trans {f g k : α → E} {h₁ h₂ h₃ : α → F}
    (hfg : f = g + O[l](h₁)) (hgk : g = k + O[l](h₂))
    (h₁h₃ : h₁ =O[l] h₃ := by asymp) (h₂h₃ : h₂ =O[l] h₃ := by asymp) : f = k + O[l](h₃) := by
  unfold EqModBigO at *
  simpa using (hfg.trans h₁h₃).add (hgk.trans h₂h₃)

lemma EqModBigO.trans_tendsto {E F : Type*}
  [NormedAddCommGroup E] [NormedAddCommGroup F] {f g : α → E} {h : α → F}
  (hfg : f = g + O[l](h)) (hh : Tendsto h l (𝓝 0)) : Tendsto (f - g) l (𝓝 0) :=
IsBigO.trans_tendsto hfg hh

variable  (h : α → F)

instance : @Trans (α → E) (α → E) (α → E) (EqModBigO l h) (EqModBigO l h) (EqModBigO l h) where
  trans := EqModBigO.trans

instance : @Trans (α → E) (α → E) (α → E) (· =ᶠ[l] ·) (· = · + O[l](h)) (· = · + O[l](h)) where
  trans := by
    intro f f' f'' h₁ h₂
    calc
      f - f'' =ᶠ[l] f' -  f'' := h₁.sub (EventuallyEq.refl _ _)
      _ =O[l] h := h₂

instance : @Trans (α → E) (α → E) (α → E) (· = · + O[l](h)) (· =ᶠ[l] ·) (· = · + O[l](h)) where
  trans := by
    intro f f' f'' h₁ h₂
    calc
      f - f'' =ᶠ[l] f - f' := (EventuallyEq.refl _ _).sub h₂.symm
      _ =O[l] h := h₁

end Trans

/-! # Algebraic operation with EqModBigO. -/

lemma IsBigO.add_eqModBigO {f g : α → E} {h₁ h₂ : α → F}
     (hg : g =O[l] h₁) (h₁h₃ : h₁ =O[l] h₂ := by asymp) : f + g = f + O[l](h₂) := by
  simp [EqModBigO, hg.trans h₁h₃]

lemma EqModBigO.add {f g f' g' : α → E} {h₁ h₂ h₃ : α → F}
    (hfg : f = g + O[l](h₁)) (hfg' : f' = g' + O[l](h₂))
    (h₁h₃ : h₁ =O[l] h₃) (h₂h₃ : h₂ =O[l] h₃) :
    f + f' = g + g' + O[l](h₃) := by
  unfold EqModBigO at *
  convert (hfg.trans h₁h₃).add (hfg'.trans h₂h₃)
  dsimp
  abel

lemma EqModBigO.comp_tendsto {ι : Type*} {l' : Filter ι }{f g : α → E} {h : α → F}
    {u : ι → α} (hfg : f = g + O[l](h)) (hu : Tendsto u l' l) :
    f ∘ u  = g ∘ u  + O[l'](h ∘ u) :=
  IsBigO.comp_tendsto hfg hu

section NormedSpace
variable {𝕜 : Type*} [NormedField 𝕜] {V : Type*} [SeminormedAddCommGroup V] [NormedSpace 𝕜 V]

lemma EqModBigO.smul {f g : α → 𝕜} {f' g' : α → V} {h₁ h₂ h₃ : α → 𝕜}
    (hfg : f = g + O[l](h₁)) (hfg' : f' = g' + O[l](h₂))
    (h₁g' : (h₁•g') =O[l] h₃) (h₂g : (g*h₂) =O[l] h₃) (h₁h₂ : (h₁*h₂) =O[l] h₃) :
    f • f' = g • g' + O[l](h₃) := by
  unfold EqModBigO at *
  have : f • f' - g • g' = (f - g)•g' + g • (f'-g') + (f - g)•(f'-g') := by
    simp [sub_smul, smul_sub]
    abel
  rw [this]
  have h₂gbis : (g • h₂) =O[l] h₃ := by simp [h₂g]
  exact ((hfg.smul $ isBigO_refl ..).trans h₁g' |>.add <| ((isBigO_refl ..).smul hfg').trans h₂gbis).add
    <| (hfg.smul hfg').trans h₁h₂

lemma EqModBigO.mul {f g f' g' : α → 𝕜} {h₁ h₂ h₃ : α → 𝕜}
    (hfg : f = g + O[l](h₁)) (hfg' : f' = g' + O[l](h₂))
    (h₁g' : (h₁*g') =O[l] h₃) (h₂g : (g*h₂) =O[l] h₃) (h₁h₂ : (h₁*h₂) =O[l] h₃) :
    f * f' = g * g' + O[l](h₃) :=
  hfg.smul hfg' h₁g' h₂g h₁h₂

lemma EqModBigO.mul' {f g f' g' gg': α → 𝕜} {h₁ h₂ h₃ : α → 𝕜}
    (hfg : f = g + O[l](h₁)) (hfg' : f' = g' + O[l](h₂))
    (h₁g' : (h₁*g') =O[l] h₃) (h₂g : (g*h₂) =O[l] h₃) (h₁h₂ : (h₁*h₂) =O[l] h₃)
    (hgg': gg'= g*g' := by try simp) :
    f * f' = gg' + O[l](h₃) := by
  rw [hgg']
  exact hfg.mul hfg' h₁g' h₂g h₁h₂

end NormedSpace

section Calculus

/-! # EqModBigO from calculus. -/

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {V : Type*} [NormedAddCommGroup V] [NormedSpace 𝕜 V]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace 𝕜 W]

lemma _root_.HasFDerivAt.eqModBigO {f : V → W} {f' : V →L[𝕜] W}
    {x₀ : V} (hf : HasFDerivAt f f' x₀) : f = fun _ ↦ f x₀ + O[𝓝 x₀]((· - x₀)) :=
  EqModBigO.isBigO (IsLittleO.isBigO hf) <| ContinuousLinearMap.isBigO_sub _ (𝓝 x₀) x₀

lemma _root_.HasDerivAt.eqModBigO {f : 𝕜 → V}
    {x₀ : 𝕜} {e : V} (hf : HasDerivAt f e x₀) : f = fun _ ↦ f x₀ + O[𝓝 x₀]((· - x₀)) :=
  _root_.HasFDerivAt.eqModBigO hf


end Calculus
end Asymptotics

/-! # Applications -/

lemma exp_eqModBigO_zero : exp = 1 + O[𝓝 0](id) := by
  have : HasDerivAt exp 1 0 := by simpa using hasDerivAt_exp 0
  simpa using this.eqModBigO

lemma exp_inv_eqModBigO : (fun n : ℕ ↦ exp (1/n)) = 1 + O[atTop](fun n : ℕ ↦ 1/(n : ℝ)) := by
   exact exp_eqModBigO_zero.comp_tendsto (tendsto_const_div_atTop_nhds_0_nat 1)

lemma Asymptotics.EqModBigO.exp_comp {α : Type*} {l : Filter α} {f g : α → ℝ} {h : α → ℝ}
    (hh : Tendsto h l (𝓝 0)) (hf : f = g + O[l](h)) : exp ∘ f = exp ∘ g + O[l]((exp ∘ g) * h) := by
  have : exp ∘ f = exp ∘ g * (exp ∘ (f - g))  := by
    ext x
    simp [← exp_add (g x) (f x - g x)]
  rw [this] ; clear this
  have hfg : Tendsto (f - g) l (𝓝 0) := by
    exact hf.trans_tendsto hh
  have F : rexp ∘ (f - g) = 1 + O[l](f - g) := by simpa using exp_eqModBigO_zero.comp_tendsto hfg
  have : exp ∘ (f - g) = 1 + O[l](h) := by
    exact IsBigO.trans F hf
  apply (eqModBigO_self (exp ∘ g) (rexp ∘ g * h)).mul' this
  simp only [isBigO_refl, mul_one]
  simp only [mul_comm, isBigO_refl]
  apply hh.isBigO_mul_nhds'

lemma isBigO_log_one_add : (fun x: ℝ  ↦ log (1 + x)) =O[𝓝 0] id := by
  have : HasDerivAt (fun x : ℝ ↦ 1+x) 1 0 := by
    simpa using (hasDerivAt_const (0 : ℝ) (1 : ℝ)).add (hasDerivAt_id' (0 : ℝ))
  simpa using (this.log (by norm_num)).eqModBigO

/-- Notation for sequence avoiding the type ascription `fun n : ℕ` where Lean would assume
a real number input. -/
notation "seq" n " ↦ " f => fun n : ℕ ↦ f

lemma log_succ_eqModBigO :
    (seq n ↦ log (n + 1)) = (seq n ↦ log n) + O[atTop](seq n ↦ 1/(n : ℝ) ) := by
  have : (seq n ↦ log (n + 1)) = (seq n ↦ log n) + seq n ↦ log (1 + 1/n) := by
    ext n; apply log_add_one
  let Inv := seq n ↦ 1/(n : ℝ)
  calc (seq n ↦ log (n + 1))
      = (seq n ↦ log n) + seq n ↦ log (1 + 1/n) + O[atTop](Inv) := by simp [this]
    _ = (fun n: ℕ ↦ log n) + O[atTop](Inv) := by
          apply IsBigO.add_eqModBigO
          exact isBigO_log_one_add.comp_tendsto (tendsto_const_div_atTop_nhds_0_nat 1)
          simp -- don't understand why `simp` as auto-param doesn't do it.

lemma tao_aux :
    ((seq n ↦ exp (1/n)) * seq n ↦ log (n + 1)) =
    (fun n ↦ log n) + O[atTop](seq n ↦ (log (n : ℝ))/n) := by
  apply exp_inv_eqModBigO.mul' log_succ_eqModBigO
  -- The next three side conditions should be discharged by a dedicated tactic.
  · rw [Pi.mul_eq]
    apply isBigO_of_eq
    intro n
    field_simp
  · simpa using (tendsto_log_atTop.comp tendsto_nat_cast_atTop_atTop).isBigO_inv
  · rw [Pi.inv_mul_inv]
    apply IsLittleO.isBigO
    simpa using (isLittleO_inv_pow_pos_log one_lt_two).comp_tendsto tendsto_nat_cast_atTop_atTop

lemma tao : (seq n ↦ (n + 1 : ℝ) ^ (exp (1/n))) = seq n ↦ n + O[atTop](seq n ↦ log n) := by
  have := calc
    (seq n ↦ (n + 1 : ℝ) ^ (exp (1/n))) = (seq n ↦ exp (exp (1/n) * log (n + 1))) := by
        ext n
        rw [rpow_def_of_pos, mul_comm]
        exact_mod_cast n.succ_pos
    _ = rexp ∘ seq n ↦ log n + O[atTop]((rexp ∘ seq n ↦ log n) * seq n ↦ log n / n) :=
          tao_aux.exp_comp tendsto_log_div_id_nat_cast
    _ =ᶠ[atTop] seq n ↦ n := seq_exp_log_eventually_eq
  refine this.congr (by simp) (by simp) ?_
  calc
  ((seq n ↦ rexp (log n)) * seq n ↦ log n / n) =ᶠ[atTop] (seq n ↦ (n : ℝ)) * seq n ↦ log n / n :=
        seq_exp_log_eventually_eq.mul EventuallyEq.rfl
  _ =ᶠ[atTop] seq n ↦ log n := by simp
