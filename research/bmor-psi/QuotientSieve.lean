import Mathlib

open Finset

namespace BmorQuotientSieve

def survivors (q p v r : ℕ) : Finset ℕ :=
  (Icc 2 v).filter (fun n => n.Coprime q ∧ n % q = r ∧ (n.Prime ∨ p ≤ n.minFac))

def source (q p v r : ℕ) : Finset ℕ :=
  (Icc p (v / p)).filter (fun k => k.Coprime q ∧ k % q = r ∧ p ≤ k.minFac)

theorem minFac_mul_eq (p k : ℕ) (hp : p.Prime) (hk : 2 ≤ k)
    (h : p ≤ k.minFac) : (p*k).minFac = p := by
  have hpk : p ∣ p*k := dvd_mul_right p k
  apply le_antisymm (Nat.minFac_le_of_dvd hp.two_le hpk)
  have hpos : 0 < p*k := Nat.mul_pos hp.pos (by omega)
  have hl : p*k = 1 ∨ p ≤ (p*k).minFac := Nat.le_minFac.mpr (by
    intro l hl hld
    rcases (Nat.Prime.dvd_mul hl).mp hld with hd | hd
    · exact le_of_eq ((Nat.prime_dvd_prime_iff_eq hl hp).mp hd).symm
    · exact h.trans (Nat.minFac_le_of_dvd hl.two_le hd))
  rcases hl with he | he
  · have := Nat.mul_le_mul_right k hp.two_le
    omega
  · exact he

theorem subset_survivors (q p v r : ℕ) :
    survivors q (p+1) v r ⊆ survivors q p v r := by
  intro n hn
  simp only [survivors, mem_filter, mem_Icc] at hn ⊢
  obtain ⟨hi,hc,hr,hprime | hmin⟩ := hn
  · exact ⟨hi,hc,hr,Or.inl hprime⟩
  · exact ⟨hi,hc,hr,Or.inr (by omega)⟩

theorem removed_iff (q p v r n : ℕ) :
    n ∈ survivors q p v r \ survivors q (p+1) v r ↔
      n ∈ Icc 2 v ∧ n.Coprime q ∧ n % q = r ∧ ¬ n.Prime ∧ n.minFac = p := by
  simp only [mem_sdiff, survivors, mem_filter]
  constructor
  · rintro ⟨⟨hi,hc,hr,hpr | hmin⟩,hn⟩
    · exact (hn ⟨hi,hc,hr,Or.inl hpr⟩).elim
    · have hnp : ¬n.Prime := fun h => hn ⟨hi,hc,hr,Or.inl h⟩
      have hlt : ¬p+1 ≤ n.minFac := fun h => hn ⟨hi,hc,hr,Or.inr h⟩
      exact ⟨hi,hc,hr,hnp,by omega⟩
  · rintro ⟨hi,hc,hr,hnp,hm⟩
    refine ⟨⟨hi,hc,hr,Or.inr (by omega)⟩,?_⟩
    rintro ⟨_,_,_,hpr | hmin⟩
    · exact hnp hpr
    · omega

theorem removed_image (q p v r : ℕ) (hp : p.Prime) (hc : p.Coprime q) (hr : r < q) :
    (source q p v r).image (fun k => p*k) =
      survivors q p v ((p*r) % q) \ survivors q (p+1) v ((p*r) % q) := by
  ext n
  rw [mem_image,removed_iff]
  constructor
  · rintro ⟨k,hk,rfl⟩
    obtain ⟨⟨hkp,hkv⟩,hkq,hkr,hkm⟩ : (p ≤ k ∧ k ≤ v/p) ∧
        k.Coprime q ∧ k % q = r ∧ p ≤ k.minFac := by
      simpa only [source, mem_filter,mem_Icc] using hk
    have hk2 : 2 ≤ k := hp.two_le.trans hkp
    have hupper : p*k ≤ v := by
      rw [mul_comm]
      exact (Nat.le_div_iff_mul_le hp.pos).mp hkv
    have hlo : 2 ≤ p*k := by
      have := Nat.mul_le_mul hp.two_le hk2
      omega
    have hmod : p*k % q = p*r % q := by
      calc
        _ = (p % q * (k % q)) % q := Nat.mul_mod _ _ _
        _ = (p % q * r) % q := by rw [hkr]
        _ = _ := by rw [Nat.mul_mod p r q,Nat.mod_eq_of_lt hr]
    exact ⟨mem_Icc.mpr ⟨hlo,hupper⟩,Nat.coprime_mul_iff_left.mpr ⟨hc,hkq⟩,
      hmod,Nat.not_prime_mul hp.ne_one (by omega),minFac_mul_eq p k hp hk2 hkm⟩
  · rintro ⟨hn,hnq,hnr,hnp,hm⟩
    have hn2 := (mem_Icc.mp hn).1
    have hnv := (mem_Icc.mp hn).2
    have hd : p ∣ n := by rw [← hm]; exact Nat.minFac_dvd n
    obtain ⟨k,hk⟩ := hd
    have hkp : p ≤ k := by
      have h := Nat.minFac_le_div (by omega : 0 < n) hnp
      rw [hm,hk,Nat.mul_div_cancel_left _ hp.pos] at h
      exact h
    have hk2 : 2 ≤ k := hp.two_le.trans hkp
    have hkv : k ≤ v/p := by
      apply (Nat.le_div_iff_mul_le hp.pos).mpr
      rwa [mul_comm,← hk]
    have hkq : k.Coprime q := (Nat.coprime_mul_iff_left.mp (hk ▸ hnq)).2
    have hmod : p*k ≡ p*r [MOD q] := by
      change p*k % q = p*r % q
      rwa [← hk]
    have hkr : k % q = r := by
      have hh := Nat.ModEq.cancel_left_of_coprime hc.symm.gcd_eq_one hmod
      change k % q = r % q at hh
      simpa only [Nat.mod_eq_of_lt hr] using hh
    have hkm : p ≤ k.minFac := by
      have hd' : k.minFac ∣ n := by rw [hk]; exact dvd_mul_of_dvd_right (Nat.minFac_dvd k) p
      have hh := Nat.minFac_le_of_dvd (Nat.minFac_prime (by omega : k ≠ 1)).two_le hd'
      rwa [hm] at hh
    exact ⟨k,mem_filter.mpr ⟨mem_Icc.mpr ⟨hkp,hkv⟩,hkq,hkr,hkm⟩,hk.symm⟩

theorem removed_weight (q p v r : ℕ) (hp : p.Prime) (hc : p.Coprime q) (hr : r < q)
    (w : ℕ → ℝ) :
    (∑ n ∈ survivors q p v ((p*r) % q), w n) -
      (∑ n ∈ survivors q (p+1) v ((p*r) % q), w n) =
      ∑ k ∈ source q p v r, w (p*k) := by
  rw [← sum_sdiff_eq_sub (subset_survivors q p v _), ← removed_image q p v r hp hc hr]
  rw [sum_image]
  intro i _ j _ he
  exact Nat.eq_of_mul_eq_mul_left hp.pos he

theorem source_diff (q p v r : ℕ) (hp : p.Prime) (hv : p*p ≤ v) :
    source q p v r = survivors q p (v/p) r \ survivors q p (p-1) r := by
  ext k
  simp only [source, survivors,mem_sdiff,mem_filter,mem_Icc]
  constructor
  · rintro ⟨⟨hkp,hkv⟩,hc,hr,hm⟩
    exact ⟨⟨⟨hp.two_le.trans hkp,hkv⟩,hc,hr,Or.inr hm⟩,fun h => by omega⟩
  · rintro ⟨⟨⟨hk2,hkv⟩,hc,hr,hpr⟩,hn⟩
    have hkp : p ≤ k := by
      by_contra! hh
      exact hn ⟨⟨hk2,by omega⟩,hc,hr,hpr⟩
    have hm : p ≤ k.minFac := by
      rcases hpr with h | h
      · rwa [h.minFac_eq]
      · exact h
    exact ⟨⟨hkp,hkv⟩,hc,hr,hm⟩

theorem source_subset (q p v r : ℕ) (hp : p.Prime) (hv : p*p ≤ v) :
    survivors q p (p-1) r ⊆ survivors q p (v/p) r := by
  have h : p ≤ v/p := (Nat.le_div_iff_mul_le hp.pos).mpr hv
  intro k hk
  simp only [survivors,mem_filter,mem_Icc] at hk ⊢
  exact ⟨⟨hk.1.1,by have := hk.1.2; omega⟩,hk.2⟩

noncomputable def W (q p v r : ℕ) : ℝ :=
    ∑ n ∈ survivors q p v r, Real.log n

def C (q p v r : ℕ) : ℕ := (survivors q p v r).card

theorem weighted_recurrence (q p v r : ℕ) (hp : p.Prime) (hc : p.Coprime q)
    (hr : r < q) (hv : p*p ≤ v) :
    W q p v ((p*r) % q) - W q (p+1) v ((p*r) % q) =
      W q p (v/p) r - W q p (p-1) r +
        Real.log p * ((C q p (v/p) r : ℝ) - (C q p (p-1) r : ℝ)) := by
  have he := removed_weight q p v r hp hc hr (fun n => Real.log n)
  change W q p v ((p*r) % q) - W q (p+1) v ((p*r) % q) = _ at he
  rw [he]
  have hterm (k : ℕ) (hk : k ∈ source q p v r) :
      Real.log ((p*k:ℕ):ℝ) = Real.log (k:ℝ) + Real.log (p:ℝ) := by
    have hkpos : 0 < k := by
      have h := (mem_Icc.mp (mem_filter.mp hk).1).1
      exact hp.pos.trans_le h
    rw [Nat.cast_mul,Real.log_mul (by positivity) (by positivity),add_comm]
  rw [sum_congr rfl hterm,sum_add_distrib,sum_const, nsmul_eq_mul, source_diff q p v r hp hv]
  rw [sum_sdiff_eq_sub (source_subset q p v r hp hv),card_sdiff_of_subset (source_subset q p v r hp hv)]
  unfold W C
  rw [Nat.cast_sub (card_le_card (source_subset q p v r hp hv))]
  ring

theorem survivors_initial (q v r : ℕ) :
    survivors q 2 v r = (Icc 2 v).filter (fun n => n.Coprime q ∧ n % q = r) := by
  ext n
  simp only [survivors,mem_filter,mem_Icc]
  constructor
  · exact fun ⟨hi,hc,hr,_⟩ => ⟨hi,hc,hr⟩
  · rintro ⟨hi,hc,hr⟩
    exact ⟨hi,hc,hr,Or.inr (Nat.minFac_prime (by omega : n ≠ 1)).two_le⟩

theorem survivors_terminal (q p v r : ℕ) (h : v < p*p) :
    survivors q p v r = (Icc 2 v).filter (fun n => n.Coprime q ∧ n % q = r ∧ n.Prime) := by
  ext n
  simp only [survivors,mem_filter,mem_Icc]
  constructor
  · rintro ⟨hi,hc,hr,hpr | hm⟩
    · exact ⟨hi,hc,hr,hpr⟩
    · refine ⟨hi,hc,hr,?_⟩
      by_contra hn
      have hh := Nat.minFac_sq_le_self (by omega : 0 < n) hn
      have hmul := Nat.mul_le_mul hm hm
      rw [pow_two] at hh
      omega
  · exact fun ⟨hi,hc,hr,hpr⟩ => ⟨hi,hc,hr,Or.inl hpr⟩

end BmorQuotientSieve
