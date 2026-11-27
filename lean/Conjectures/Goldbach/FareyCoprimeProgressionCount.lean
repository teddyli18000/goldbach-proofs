import Mathlib

namespace FareyCoprimeProgressionCount

private theorem shiftCard (P : ℕ → Prop) [DecidablePred P] (l t : ℕ) :
    ((Finset.Ico l (l + t)).filter P).card =
      Nat.count (fun k => P (k + l)) t := by
  rw [Nat.count_eq_card_filter_range]
  symm
  apply Finset.card_bij (fun k _ => k + l)
  · intro k hk
    obtain ⟨hk, hp⟩ := Finset.mem_filter.mp hk
    have hk' := Finset.mem_range.mp hk
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨by omega, by omega⟩, hp⟩
  · intro a ha b hb hab
    omega
  · intro x hx
    obtain ⟨hi, hp⟩ := Finset.mem_filter.mp hx
    obtain ⟨hl, hh⟩ := Finset.mem_Ico.mp hi
    have he : x - l + l = x := by omega
    refine ⟨x - l, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), ?_⟩, he⟩
    rwa [he]

private theorem countBlocks (P : ℕ → Prop) [DecidablePred P] {q : ℕ}
    (hP : Function.Periodic P q) (a b : ℕ) :
    Nat.count P (b + a * q) = Nat.count P b + a * Nat.count P q := by
  induction a with
  | zero => simp
  | succ a ih =>
    rw [Nat.succ_mul, ← Nat.add_assoc, Nat.count_add']
    simp_rw [show ∀ k, P (k + q) = P k from hP]
    rw [ih, Nat.succ_mul, Nat.add_assoc]

private theorem residueError (q a l h : ℕ) (hq : 0 < q) (ha : a < q) (hl : l ≤ h) :
    |(((Finset.Icc l h).filter (fun u => u % q = a)).card : ℝ) -
      ((h - l + 1 : ℕ) : ℝ) / q| ≤ 1 := by
  let t := h - l + 1
  let P : ℕ → Prop := fun k => (k + l) % q = a
  have hP : Function.Periodic P q := by
    intro k
    dsimp only [P]
    rw [Nat.add_right_comm k q l, Nat.add_mod_right]
  have hper : Function.Periodic (fun u : ℕ => u % q = a) q :=
    fun u => congrArg (fun x : ℕ => x = a) (Nat.periodic_mod q u)
  have hbase : Nat.count (fun u => u % q = a) q = 1 := by
    rw [Nat.count_eq_card_filter_range]
    have hs : (Finset.range q).filter (fun u => u % q = a) = {a} := by
      ext u
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
      constructor
      · rintro ⟨hu, he⟩
        rwa [Nat.mod_eq_of_lt hu] at he
      · rintro rfl
        exact ⟨ha, Nat.mod_eq_of_lt ha⟩
    simp [hs]
  have hfull : Nat.count P q = 1 := by
    change Nat.count (fun k => (k + l) % q = a) q = 1
    rw [← shiftCard (fun u => u % q = a) l q,
      Nat.filter_Ico_card_eq_of_periodic l q (fun u => u % q = a) hper]
    exact hbase
  have hi : Finset.Icc l h = Finset.Ico l (l + t) := by
    ext u
    simp only [Finset.mem_Icc, Finset.mem_Ico]
    dsimp only [t]
    omega
  have hdiv : t % q + (t / q) * q = t := by
    simpa only [Nat.mul_comm q] using Nat.mod_add_div t q
  have hc := countBlocks P hP (t / q) (t % q)
  rw [hdiv, hfull, mul_one] at hc
  have hcR : (Nat.count P t : ℝ) =
      (Nat.count P (t % q) : ℝ) + ((t / q : ℕ) : ℝ) := by exact_mod_cast hc
  have htR : (t : ℝ) = ((t % q : ℕ) : ℝ) + ((t / q : ℕ) : ℝ) * (q : ℝ) := by
    exact_mod_cast hdiv.symm
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have htail : (Nat.count P (t % q) : ℝ) ≤ 1 := by
    have ht' := Nat.count_monotone P (Nat.mod_lt t hq).le
    rw [hfull] at ht'
    exact_mod_cast ht'
  have hfrac : ((t % q : ℕ) : ℝ) / q ≤ 1 :=
    (div_le_one hqR).mpr (by exact_mod_cast (Nat.mod_lt t hq).le)
  have hfrac0 : 0 ≤ ((t % q : ℕ) : ℝ) / q := by positivity
  have hexp : (t : ℝ) / q = ((t / q : ℕ) : ℝ) + ((t % q : ℕ) : ℝ) / q := by
    conv_lhs => rw [htR]
    field_simp [hqR.ne'] <;> ring
  rw [hi, shiftCard]
  change |(Nat.count P t : ℝ) - (t : ℝ) / q| ≤ 1
  rw [hcR, hexp, abs_le]
  constructor <;> linarith [show (0 : ℝ) ≤ Nat.count P (t % q) by positivity]

private theorem mobiusMask (n u : ℕ) (hn : 0 < n) :
    (∑ c ∈ n.divisors, if c ∣ u then (ArithmeticFunction.moebius c : ℝ) else 0) =
      if u.Coprime n then 1 else 0 := by
  have hg : 0 < Nat.gcd u n := Nat.gcd_pos_of_pos_right u hn
  have hs : n.divisors.filter (fun c => c ∣ u) = (Nat.gcd u n).divisors := by
    ext c
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hcn, _⟩, hcu⟩
      exact ⟨Nat.dvd_gcd hcu hcn, hg.ne'⟩
    · rintro ⟨hcg, _⟩
      exact ⟨⟨hcg.trans (Nat.gcd_dvd_right u n), hn.ne'⟩,
        hcg.trans (Nat.gcd_dvd_left u n)⟩
  rw [← Finset.sum_filter, hs]
  have hm : (∑ c ∈ (Nat.gcd u n).divisors, ArithmeticFunction.moebius c) =
      (if Nat.gcd u n = 1 then 1 else 0 : ℤ) := by
    rw [← ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.moebius_mul_coe_zeta,
      ArithmeticFunction.one_apply]
  change (∑ c ∈ (Nat.gcd u n).divisors, (ArithmeticFunction.moebius c : ℝ)) =
    if Nat.gcd u n = 1 then 1 else 0
  rw [← Int.cast_sum, hm]
  split_ifs <;> norm_num

end FareyCoprimeProgressionCount

open FareyCoprimeProgressionCount

theorem Conjectures.Goldbach.FareyCoprimeProgressionCount :
    ∀ n d b l h : ℕ, 0 < n → 0 < d → d.Coprime n → b < d → l ≤ h →
      |((((Finset.Icc l h).filter (fun u => u % d = b ∧ u.Coprime n)).card : ℝ) -
        ((h - l + 1 : ℕ) : ℝ) * (n.totient : ℝ) / ((d : ℝ) * n))| ≤ (n.divisors.card : ℝ) := by
  intro n d b l h hn hd hdn hb hl
  let S := (Finset.Icc l h).filter (fun u => u % d = b)
  let C : ℕ → ℝ := fun c => ((S.filter (fun u => c ∣ u)).card : ℝ)
  let mu : ℕ → ℝ := fun c => (ArithmeticFunction.moebius c : ℝ)
  let L : ℝ := ((h - l + 1 : ℕ) : ℝ)
  have hset : (Finset.Icc l h).filter (fun u => u % d = b ∧ u.Coprime n) =
      S.filter (fun u => u.Coprime n) := by
    ext u
    simp only [S, Finset.mem_filter]
    tauto
  have hcount : ((S.filter (fun u => u.Coprime n)).card : ℝ) =
      ∑ c ∈ n.divisors, mu c * C c := by
    calc
      _ = ∑ u ∈ S, if u.Coprime n then (1 : ℝ) else 0 := by
        rw [← Finset.sum_filter]
        simp
      _ = ∑ u ∈ S, ∑ c ∈ n.divisors, if c ∣ u then mu c else 0 := by
        apply Finset.sum_congr rfl
        intro u hu
        exact (mobiusMask n u hn).symm
      _ = ∑ c ∈ n.divisors, ∑ u ∈ S, if c ∣ u then mu c else 0 := Finset.sum_comm
      _ = _ := by
        apply Finset.sum_congr rfl
        intro c hc
        rw [← Finset.sum_filter]
        simp [C, nsmul_eq_mul, mul_comm]
  have ht : (∑ c ∈ n.divisors, mu c * ((n / c : ℕ) : ℝ)) = (n.totient : ℝ) := by
    have hsum : ∀ (k : ℕ), 0 < k → (∑ j ∈ k.divisors, (j.totient : ℝ)) = (k : ℝ) := by
      intro k hk
      exact_mod_cast Nat.sum_totient k
    have hm := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
      (f := fun k => (k.totient : ℝ)) (g := fun k => (k : ℝ))).mp hsum n hn
    rw [Nat.sum_divisorsAntidiagonal (fun x y => (ArithmeticFunction.moebius x : ℝ) * (y : ℝ))] at hm
    exact hm
  have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hmain : (∑ c ∈ n.divisors, mu c * (L / ((d : ℝ) * c))) =
      L * (n.totient : ℝ) / ((d : ℝ) * n) := by
    calc
      _ = ∑ c ∈ n.divisors, (L / ((d : ℝ) * n)) * (mu c * ((n / c : ℕ) : ℝ)) := by
        apply Finset.sum_congr rfl
        intro c hc
        have hcR : (c : ℝ) ≠ 0 := by exact_mod_cast (Nat.pos_of_mem_divisors hc).ne'
        have hcn : ((n / c : ℕ) : ℝ) * c = n := by
          exact_mod_cast Nat.div_mul_cancel (Nat.dvd_of_mem_divisors hc)
        rw [(eq_div_iff hcR).mpr hcn]
        field_simp [hcR, hdR, hnR] <;> ring
      _ = _ := by rw [← Finset.mul_sum, ht]; ring
  have hC : ∀ c ∈ n.divisors, |C c - L / ((d : ℝ) * c)| ≤ 1 := by
    intro c hc
    have hcpos := Nat.pos_of_mem_divisors hc
    have hdc := hdn.coprime_dvd_right (Nat.dvd_of_mem_divisors hc)
    let r := Nat.chineseRemainder hdc b 0
    have hr : r.val < d * c := Nat.chineseRemainder_lt_mul hdc b 0 hd.ne' hcpos.ne'
    have hrd : r.val % d = b := Eq.trans r.property.1 (Nat.mod_eq_of_lt hb)
    have hrc : r.val % c = 0 := Eq.trans r.property.2 (Nat.zero_mod c)
    have he : S.filter (fun u => c ∣ u) =
        (Finset.Icc l h).filter (fun u => u % (d * c) = r.val) := by
      ext u
      simp only [S, Finset.mem_filter]
      constructor
      · rintro ⟨⟨hu, hub⟩, hcu⟩
        have h1 : Nat.ModEq d u r.val := hub.trans hrd.symm
        have h2 : Nat.ModEq c u r.val := (Nat.modEq_zero_iff_dvd.mpr hcu).trans
          (Nat.modEq_zero_iff_dvd.mpr (Nat.dvd_iff_mod_eq_zero.mpr hrc)).symm
        have hh := (Nat.modEq_and_modEq_iff_modEq_mul hdc).mp ⟨h1, h2⟩
        exact ⟨hu, Eq.trans hh (Nat.mod_eq_of_lt hr)⟩
      · rintro ⟨hu, hub⟩
        have hh : Nat.ModEq (d * c) u r.val := hub.trans (Nat.mod_eq_of_lt hr).symm
        obtain ⟨h1, h2⟩ := (Nat.modEq_and_modEq_iff_modEq_mul hdc).mpr hh
        exact ⟨⟨hu, Eq.trans h1 hrd⟩, Nat.dvd_iff_mod_eq_zero.mpr (Eq.trans h2 hrc)⟩
    dsimp only [C, L]
    rw [he]
    simpa only [Nat.cast_mul] using residueError (d * c) r.val l h (Nat.mul_pos hd hcpos) hr hl
  have hmu : ∀ c : ℕ, |mu c| ≤ 1 := by
    intro c
    rcases ArithmeticFunction.moebius_eq_or c with hc | hc | hc <;> simp [mu, hc]
  rw [hset, hcount]
  change |(∑ c ∈ n.divisors, mu c * C c) - L * (n.totient : ℝ) / ((d : ℝ) * n)| ≤ _
  rw [← hmain, ← Finset.sum_sub_distrib]
  calc
    _ ≤ ∑ c ∈ n.divisors, |mu c * C c - mu c * (L / ((d : ℝ) * c))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ c ∈ n.divisors, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro c hc
      rw [← mul_sub, abs_mul]
      simpa using mul_le_mul (hmu c) (hC c hc) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    _ = _ := by simp
