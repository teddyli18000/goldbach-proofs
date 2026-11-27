import Mathlib

private theorem primitiveKernel :
∀ (k : ℕ) (χ : DirichletCharacter ℂ (2^(k+1))), 1 ≤ k →
  (χ.IsPrimitive ↔ χ ((1 + 2^k : ℕ) : ZMod (2^(k+1))) = -1) := by
  intro k χ hk
  haveI : NeZero (2^(k+1)) := ⟨by positivity⟩
  have hd : 2^k ∣ 2^(k+1) := pow_dvd_pow 2 (Nat.le_succ k)
  have hlt : 1 < 2^k := by
    calc (1:ℕ) < 2^1 := by norm_num
      _ ≤ 2^k := Nat.pow_le_pow_right (by norm_num) hk
  have hodd : Odd (1 + 2^k) := by
    rw [add_comm, Nat.odd_add_one, Nat.not_odd_iff_even]
    exact ⟨2^(k-1), by rw [← two_mul, ← pow_succ', Nat.sub_add_cancel hk]⟩
  have hcop : Nat.Coprime (1 + 2^k) (2^(k+1)) :=
    Nat.Coprime.pow_right (k+1) hodd.coprime_two_right
  have hker : ∀ x : (ZMod (2^(k+1)))ˣ, ZMod.unitsMap hd x = 1 →
      (x : ZMod (2^(k+1))) = 1 ∨
        (x : ZMod (2^(k+1))) = ((1 + 2^k : ℕ) : ZMod (2^(k+1))) := by
    intro x hx
    have hcast : (((x : ZMod (2^(k+1))).cast : ZMod (2^k))) = 1 := by
      have h := congrArg (fun y : (ZMod (2^k))ˣ => (y : ZMod (2^k))) hx
      simpa [ZMod.unitsMap_val] using h
    set a : ℕ := (x : ZMod (2^(k+1))).val with ha
    have haval : (a : ZMod (2^(k+1))) = (x : ZMod (2^(k+1))) := by
      rw [ha]
      exact ZMod.natCast_zmod_val _
    have hamod : a % 2^k = 1 := by
      have h1 : (a : ZMod (2^k)) = 1 := by
        rw [← ZMod.cast_natCast hd a, haval]
        exact hcast
      have h2 : a ≡ 1 [MOD 2^k] := (ZMod.natCast_eq_natCast_iff a 1 (2^k)).mp (by simpa using h1)
      simpa [Nat.ModEq, Nat.mod_eq_of_lt hlt] using h2
    have haeq : a = 2^k * (a / 2^k) + 1 := by
      have h := Nat.div_add_mod a (2^k)
      rw [hamod] at h
      omega
    have hq : a / 2^k < 2 := by
      have halt : a < 2^k * 2 := by
        have h := ZMod.val_lt (x : ZMod (2^(k+1)))
        rw [← ha, pow_succ] at h
        exact h
      have h1 : 2^k * (a / 2^k) < 2^k * 2 := by omega
      exact Nat.lt_of_mul_lt_mul_left h1
    have hq2 : a / 2^k = 0 ∨ a / 2^k = 1 := by
      rcases Nat.eq_zero_or_pos (a / 2^k) with h0 | hpos
      · exact Or.inl h0
      · exact Or.inr (by omega)
    rcases hq2 with h0 | h1
    · left
      rw [← haval, haeq, h0, mul_zero, zero_add]
      norm_num
    · right
      rw [← haval, haeq, h1, mul_one]
      norm_num [Nat.add_comm]
  have hfac_iff : χ.FactorsThrough (2^k) ↔
      χ ((1 + 2^k : ℕ) : ZMod (2^(k+1))) = 1 := by
    have hu : ZMod.unitsMap hd (ZMod.unitOfCoprime (1 + 2^k) hcop) = 1 := by
      refine Units.ext ?_
      rw [ZMod.unitsMap_val, ZMod.coe_unitOfCoprime, Units.val_one, ZMod.cast_natCast hd]
      rw [Nat.cast_add, Nat.cast_one]
      have h : (((2:ℕ)^k : ℕ) : ZMod (2^k)) = 0 := ZMod.natCast_self _
      rw [h]
      ring
    constructor
    · intro hf
      have hker' := (DirichletCharacter.factorsThrough_iff_ker_unitsMap hd).mp hf
      have hmem : χ.toUnitHom (ZMod.unitOfCoprime (1 + 2^k) hcop) = 1 :=
        MonoidHom.mem_ker.mp (hker' (MonoidHom.mem_ker.mpr hu))
      have h := congrArg (fun y : ℂˣ => (y : ℂ)) hmem
      simpa [MulChar.coe_toUnitHom, ZMod.coe_unitOfCoprime] using h
    · intro hv
      rw [DirichletCharacter.factorsThrough_iff_ker_unitsMap hd]
      intro x hx
      apply MonoidHom.mem_ker.mpr
      apply Units.ext
      rw [MulChar.coe_toUnitHom, Units.val_one]
      rcases hker x (MonoidHom.mem_ker.mp hx) with h | h
      · rw [h]
        exact MulChar.map_one χ
      · rw [h, hv]
  constructor
  ·
    intro hprim
    have hne : ¬ χ.FactorsThrough (2^k) := by
      intro hf
      have hmem : 2^k ∈ χ.conductorSet := (DirichletCharacter.mem_conductorSet_iff χ).mpr hf
      have hdvd : χ.conductor ∣ 2^k :=
        (DirichletCharacter.mem_conductorSet_iff_conductor_dvd χ hd).mp hmem
      rw [(DirichletCharacter.isPrimitive_def χ).mp hprim] at hdvd
      have hle : k + 1 ≤ k := (Nat.pow_dvd_pow_iff_le_right (x := 2) (by norm_num)).mp hdvd
      omega
    have hne1 : χ ((1 + 2^k : ℕ) : ZMod (2^(k+1))) ≠ 1 := fun h => hne (hfac_iff.mpr h)
    have hsq : χ ((1 + 2^k : ℕ) : ZMod (2^(k+1))) ^ 2 = 1 := by
      have hkey : (((1 + 2^k : ℕ) : ZMod (2^(k+1))) ^ 2) = 1 := by
        have hnat : (1 + 2^k : ℕ) ^ 2 = 1 + 2^(k+1) * (1 + 2^(k-1)) := by
          have hm : 2 * 2^(k-1) = 2^k := by rw [← pow_succ', Nat.sub_add_cancel hk]
          have hA : 2^(k+1) = 2 * 2^k := pow_succ' 2 k
          nlinarith
        calc (((1 + 2^k : ℕ) : ZMod (2^(k+1))) ^ 2)
            = (((1 + 2^k : ℕ) ^ 2 : ℕ) : ZMod (2^(k+1))) := (Nat.cast_pow _ _).symm
          _ = ((1 + 2^(k+1) * (1 + 2^(k-1)) : ℕ) : ZMod (2^(k+1))) := by rw [hnat]
          _ = 1 := by
            rw [Nat.cast_add, Nat.cast_one, Nat.cast_mul]
            have h : (((2:ℕ)^(k+1) : ℕ) : ZMod (2^(k+1))) = 0 := ZMod.natCast_self _
            rw [h]
            ring
      calc χ ((1 + 2^k : ℕ) : ZMod (2^(k+1))) ^ 2
          = χ (((1 + 2^k : ℕ) : ZMod (2^(k+1))) ^ 2) := (map_pow χ _ 2).symm
        _ = χ 1 := by rw [hkey]
        _ = 1 := MulChar.map_one χ
    rcases (sq_eq_one_iff.mp hsq) with h | h
    · exact absurd h hne1
    · exact h
  ·
    intro hv
    rw [DirichletCharacter.isPrimitive_def]
    have hnot : ¬ χ.FactorsThrough (2^k) := by
      intro hf
      have h1 : χ ((1 + 2^k : ℕ) : ZMod (2^(k+1))) = 1 := hfac_iff.mp hf
      rw [hv] at h1
      norm_num at h1
    have hdvd : χ.conductor ∣ 2^(k+1) := DirichletCharacter.conductor_dvd_level χ
    obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow (by norm_num : Nat.Prime 2)).mp hdvd
    rw [hjeq]
    by_cases hjk : j = k + 1
    · rw [hjk]
    · exfalso
      have hjk' : j ≤ k := by omega
      have hdvd' : χ.conductor ∣ 2^k := by
        rw [hjeq]
        exact (Nat.pow_dvd_pow_iff_le_right (x := 2) (by norm_num)).mpr hjk'
      exact hnot ((DirichletCharacter.mem_conductorSet_iff χ).mp
        ((DirichletCharacter.mem_conductorSet_iff_conductor_dvd χ hd).mpr hdvd'))


open Finset

private theorem oddSplit {R : Type*} [AddCommMonoid R] (q : ℕ) (hq : Even q) (f : ℕ → R) :
    (∑ r ∈ (range (2*q)).filter Odd, f r) =
      (∑ r ∈ (range q).filter Odd, f r) + ∑ r ∈ (range q).filter Odd, f (r+q) := by
  simp only [sum_filter]
  rw [show 2*q = q+q by omega, sum_range_add]
  congr 1
  apply sum_congr rfl
  intro r hr
  have hh : Odd (q+r) ↔ Odd r := by
    rw [Nat.odd_iff, Nat.odd_iff, Nat.add_mod, Nat.even_iff.mp hq]
    simp
  rw [if_congr hh rfl rfl, Nat.add_comm q r]

private theorem finiteParseval (m : ℕ) [NeZero m] (S : Finset ℕ)
    (hS : ∀ a ∈ S, a < m ∧ a.Coprime m) (g : ℕ → ℝ) :
    (∑ χ : DirichletCharacter ℂ m, ‖∑ a ∈ S, (g a : ℂ)*χ (a : ZMod m)‖^2) =
      (m.totient : ℝ) * ∑ a ∈ S, (g a)^2 := by
  classical
  let T (χ : DirichletCharacter ℂ m) := ∑ a ∈ S, (g a : ℂ)*χ (a : ZMod m)
  have orth (a b : ℕ) (ha : a ∈ S) (hb : b ∈ S) :
      (∑ χ : DirichletCharacter ℂ m, star (χ (a : ZMod m))*χ (b : ZMod m)) =
        if a=b then (m.totient : ℂ) else 0 := by
    let u := ZMod.unitOfCoprime a (hS a ha).2
    have hca (χ : DirichletCharacter ℂ m) :
        star (χ (a : ZMod m)) = χ ((a : ZMod m)⁻¹) := by
      rw [← ZMod.coe_unitOfCoprime a (hS a ha).2]
      rw [MulChar.star_apply', MulChar.inv_apply, Ring.inverse_unit, ZMod.inv_coe_unit]
    simp_rw [hca]
    have h := DirichletCharacter.sum_char_inv_mul_char_eq ℂ
      ((ZMod.isUnit_iff_coprime a m).mpr (hS a ha).2) (b : ZMod m)
    simp only [h, ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt (hS a ha).1,
      Nat.mod_eq_of_lt (hS b hb).1]
  have hex (χ : DirichletCharacter ℂ m) :
      star (T χ) * T χ = ∑ a ∈ S, ∑ b ∈ S,
        ((g a : ℂ)*(g b : ℂ)) * (star (χ (a : ZMod m))*χ (b : ZMod m)) := by
    dsimp only [T]
    rw [star_sum, sum_mul]
    apply sum_congr rfl
    intro a ha
    rw [mul_sum, star_mul]
    simp only [Complex.star_def, Complex.conj_ofReal]
    apply sum_congr rfl
    intro b hb
    ring
  have he : (∑ χ : DirichletCharacter ℂ m, star (T χ)*T χ) =
      (m.totient : ℂ) * ∑ a ∈ S, (g a : ℂ)^2 := by
    simp_rw [hex]
    rw [sum_comm, mul_sum]
    apply sum_congr rfl
    intro a ha
    rw [sum_comm]
    have hs : (∑ b ∈ S, ∑ χ : DirichletCharacter ℂ m,
        ((g a : ℂ)*(g b : ℂ)) * (star (χ (a : ZMod m))*χ (b : ZMod m))) =
        ∑ b ∈ S, ((g a : ℂ)*(g b : ℂ)) * (if a=b then (m.totient : ℂ) else 0) := by
      apply sum_congr rfl
      intro b hb
      rw [← mul_sum, orth a b ha hb]
    rw [hs, sum_eq_single a]
    · simp <;> ring
    · intro b hb hba
      simp [Ne.symm hba]
    · exact fun h => (h ha).elim
  have hv (z : ℂ) : star z * z = ((‖z‖^2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_mul', Complex.ofReal_pow]
  simp_rw [hv] at he
  exact_mod_cast he

private theorem layerEnergy (N k : ℕ) (hN : 4 ≤ N) (hk : 1 ≤ k) (B : ℝ) (hB : 0 ≤ B)
    (H : ∀ χ : DirichletCharacter ℂ (2^(k+1)), χ.IsPrimitive →
      ‖∑ n ∈ (range (N+1)).filter Nat.Prime,
        (Real.log (n : ℝ) : ℂ) * star (χ (n : ZMod (2^(k+1))))‖ ≤ B) :
    let q : ℕ := 2^k
    let A := fun r : ℕ => ∑ n ∈ (range (N+1)).filter (fun n => n % (2*q)=r ∧ n.Prime), Real.log (n : ℝ)
    let D := fun r : ℕ => A r - A (r+q)
    (∑ r ∈ range q, (D r)^2) ≤ 2*B^2 + (Real.log 2)^2 := by
  classical
  dsimp only
  let q : ℕ := 2^k
  let m : ℕ := 2^(k+1)
  have hm : m = 2*q := by dsimp [m,q]; rw [pow_succ']
  have hq : 0 < q := by positivity
  have hq2 : 2 ≤ q := by
    exact Nat.pow_le_pow_right (by norm_num : 0 < (2:ℕ)) hk
  have hqe : Even q := by
    obtain ⟨j, hj⟩ : ∃ j, k=j+1 := ⟨k-1, by omega⟩
    exact ⟨2^j, by dsimp [q]; rw [hj, pow_succ]; ring⟩
  letI : NeZero m := ⟨by dsimp [m]; positivity⟩
  let A (r : ℕ) : ℝ := ∑ n ∈ (range (N+1)).filter (fun n => n % m=r ∧ n.Prime), Real.log (n : ℝ)
  let D (r : ℕ) : ℝ := A r - A (r+q)
  let O := (range q).filter Odd
  let S := (range m).filter Odd
  let g (r : ℕ) : ℝ := if r < q then D r else -D (r-q)
  let T (χ : DirichletCharacter ℂ m) := ∑ a ∈ S, (g a : ℂ)*χ (a : ZMod m)
  let U (χ : DirichletCharacter ℂ m) := ∑ a ∈ range m, (A a : ℂ)*χ (a : ZMod m)
  have hcop (a : ℕ) (ha : Odd a) : a.Coprime m := by
    exact Nat.Coprime.pow_right (k+1) ha.coprime_two_right
  have hodd (a : ℕ) (ha : a ∈ S) : a < m ∧ a.Coprime m :=
    ⟨mem_range.mp (mem_filter.mp ha).1, hcop a (mem_filter.mp ha).2⟩
  have hgs : (∑ a ∈ S, g a ^ 2) = 2 * ∑ a ∈ O, D a ^ 2 := by
    change (∑ a ∈ (range m).filter Odd, g a ^ 2) = _
    rw [show (range m).filter Odd = (range (2*q)).filter Odd by rw [hm], oddSplit q hqe]
    have h1 : (∑ a ∈ O, g a ^ 2) = ∑ a ∈ O, D a ^ 2 := by
      apply sum_congr rfl
      intro a ha
      simp [g, mem_range.mp (mem_filter.mp ha).1]
    have h2 : (∑ a ∈ O, g (a+q)^2) = ∑ a ∈ O, D a ^ 2 := by
      apply sum_congr rfl
      intro a ha
      simp [g, show ¬ a+q < q by omega, show a+q-q=a by omega]
    change (∑ a ∈ O, g a ^ 2) + (∑ a ∈ O, g (a+q)^2) = _
    rw [h1,h2]
    ring
  have hshift (a : ℕ) (ha : Odd a) :
      ((a+q : ℕ) : ZMod m) = (a : ZMod m) * ((1+q : ℕ) : ZMod m) := by
    obtain ⟨j,hj⟩ := ha
    have he : a*(1+q) = a+q+m*j := by rw [hm,hj]; ring
    rw [← Nat.cast_mul, he, Nat.cast_add, Nat.cast_mul, ZMod.natCast_self, zero_mul, add_zero]
  let z (χ : DirichletCharacter ℂ m) : ℂ := χ ((1+q : ℕ) : ZMod m)
  have hzsq (χ : DirichletCharacter ℂ m) : z χ ^ 2 = 1 := by
    have ho : Odd (1+q) := by
      rw [Nat.odd_iff, Nat.add_mod, Nat.even_iff.mp hqe]
      norm_num
    have he := hshift (1+q) ho
    have he' : (((1+q)+q : ℕ) : ZMod m) = 1 := by
      rw [show 1+q+q=1+m by omega, Nat.cast_add, Nat.cast_one, ZMod.natCast_self, add_zero]
    change χ ((1+q : ℕ) : ZMod m)^2=1
    rw [pow_two, ← map_mul, ← he, he', map_one]
  have hprim (χ : DirichletCharacter ℂ m) : χ.IsPrimitive ↔ z χ = -1 :=
    primitiveKernel k χ hk
  have hz (χ : DirichletCharacter ℂ m) (hχ : ¬ χ.IsPrimitive) : z χ = 1 := by
    rcases sq_eq_one_iff.mp (hzsq χ) with h | h
    · exact h
    · exact (hχ ((hprim χ).mpr h)).elim
  have hch (χ : DirichletCharacter ℂ m) (a : ℕ) (ha : a ∈ O) :
      χ ((a+q : ℕ) : ZMod m) = χ (a : ZMod m) * z χ := by
    rw [hshift a (mem_filter.mp ha).2, map_mul] <;> rfl
  have hT (χ : DirichletCharacter ℂ m) :
      T χ = ∑ a ∈ O, (D a : ℂ) * (χ (a : ZMod m) - χ ((a+q : ℕ) : ZMod m)) := by
    change (∑ a ∈ (range m).filter Odd, (g a : ℂ)*χ (a : ZMod m)) = _
    rw [show (range m).filter Odd = (range (2*q)).filter Odd by rw [hm], oddSplit q hqe]
    change (∑ a ∈ O, (g a : ℂ)*χ (a : ZMod m)) +
      (∑ a ∈ O, (g (a+q) : ℂ)*χ ((a+q : ℕ) : ZMod m)) = _
    rw [← sum_add_distrib]
    apply sum_congr rfl
    intro a ha
    simp [g, mem_range.mp (mem_filter.mp ha).1, show ¬ a+q < q by omega,
      show a+q-q=a by omega] <;> ring
  have hUodd (χ : DirichletCharacter ℂ m) :
      U χ = ∑ a ∈ S, (A a : ℂ)*χ (a : ZMod m) := by
    change _ = ∑ a ∈ (range m).filter Odd, _
    rw [sum_filter]
    apply sum_congr rfl
    intro a ha
    by_cases ho : Odd a
    · simp [ho]
    · have hnu : ¬ IsUnit (a : ZMod m) := by
        rw [ZMod.isUnit_iff_coprime]
        intro hc
        have h2 : a.Coprime 2 := (Nat.coprime_pow_right_iff (by omega : 0 < k+1) a 2).mp hc
        exact ho (by simpa [Nat.coprime_two_right] using h2)
      simp [ho, χ.map_nonunit hnu]
  have hU (χ : DirichletCharacter ℂ m) :
      U χ = ∑ n ∈ (range (N+1)).filter Nat.Prime,
        (Real.log (n : ℝ) : ℂ)*χ (n : ZMod m) := by
    let P := (range (N+1)).filter Nat.Prime
    calc
      U χ = ∑ a ∈ range m, ∑ n ∈ P.filter (fun n => n % m=a),
          (Real.log (n : ℝ) : ℂ)*χ (n : ZMod m) := by
        apply sum_congr rfl
        intro a ha
        have he : (range (N+1)).filter (fun n => n % m=a ∧ n.Prime) =
            P.filter (fun n => n % m=a) := by
          ext n
          simp only [P,mem_filter]
          tauto
        simp only [A,he,Complex.ofReal_sum,sum_mul]
        apply sum_congr rfl
        intro n hn
        rw [← (mem_filter.mp hn).2, ZMod.natCast_mod]
      _ = _ := sum_fiberwise_of_maps_to (fun n _ => mem_range.mpr (Nat.mod_lt n (NeZero.pos m))) _
  have hnorm (χ : DirichletCharacter ℂ m) (hχ : χ.IsPrimitive) : ‖U χ‖ ≤ B := by
    rw [hU]
    have h := H χ hχ
    have he : (∑ n ∈ (range (N+1)).filter Nat.Prime,
        (Real.log (n : ℝ) : ℂ)*star (χ (n : ZMod m))) =
        star (∑ n ∈ (range (N+1)).filter Nat.Prime, (Real.log (n : ℝ) : ℂ)*χ (n : ZMod m)) := by
      rw [star_sum]
      apply sum_congr rfl
      intro n hn
      rw [star_mul]
      simp [Complex.star_def]
    change ‖∑ n ∈ (range (N+1)).filter Nat.Prime,
      (Real.log (n : ℝ) : ℂ)*star (χ (n : ZMod m))‖ ≤ B at h
    rwa [he, norm_star] at h
  have hTb (χ : DirichletCharacter ℂ m) : ‖T χ‖ ≤ 2*B := by
    by_cases hp : χ.IsPrimitive
    · have hv := (hprim χ).mp hp
      have heU : U χ = ∑ a ∈ O, (D a : ℂ)*χ (a : ZMod m) := by
        rw [hUodd]
        change (∑ a ∈ (range m).filter Odd, (A a : ℂ)*χ (a : ZMod m)) = _
        rw [show (range m).filter Odd = (range (2*q)).filter Odd by rw [hm], oddSplit q hqe]
        change (∑ a ∈ O, (A a : ℂ)*χ (a : ZMod m)) +
          (∑ a ∈ O, (A (a+q) : ℂ)*χ ((a+q : ℕ) : ZMod m)) = _
        rw [← sum_add_distrib]
        apply sum_congr rfl
        intro a ha
        rw [hch χ a ha, hv]
        simp only [D,Complex.ofReal_sub]
        ring
      have heT : T χ = 2*U χ := by
        rw [hT,heU,mul_sum]
        apply sum_congr rfl
        intro a ha
        rw [hch χ a ha,hv]
        ring
      rw [heT,norm_mul]
      norm_num
      linarith [hnorm χ hp]
    · have he : T χ = 0 := by
        rw [hT]
        apply sum_eq_zero
        intro a ha
        rw [hch χ a ha,hz χ hp,mul_one,sub_self,mul_zero]
      rw [he,norm_zero]
      positivity
  have hpv := finiteParseval m S hodd g
  change (∑ χ : DirichletCharacter ℂ m, ‖T χ‖^2) = (m.totient : ℝ) * ∑ a ∈ S, g a^2 at hpv
  rw [hgs] at hpv
  have hcard : Fintype.card (DirichletCharacter ℂ m) = m.totient := by
    rw [← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ m
  have hsum : (∑ χ : DirichletCharacter ℂ m, ‖T χ‖^2) ≤ (m.totient : ℝ)*(2*B)^2 := by
    calc
      _ ≤ ∑ _ : DirichletCharacter ℂ m, (2*B)^2 :=
        sum_le_sum fun χ _ => pow_le_pow_left₀ (norm_nonneg _) (hTb χ) 2
      _ = _ := by simp [hcard,nsmul_eq_mul]
  have hpos : 0 < (m.totient : ℝ) := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos m)
  have hoddE : (∑ a ∈ O, D a^2) ≤ 2*B^2 := by
    rw [hpv] at hsum
    have he := (mul_le_mul_left hpos).mp hsum
    nlinarith only [he]
  have hAeven (a : ℕ) (ha : Even a) : A a = if a=2 then Real.log 2 else 0 := by
    have hset : (range (N+1)).filter (fun n => n % m=a ∧ n.Prime) =
        if a=2 then {2} else ∅ := by
      ext n
      by_cases h : a=2
      · subst a
        simp only [if_pos rfl,mem_filter,mem_range,mem_singleton]
        constructor
        · rintro ⟨_, hmod, hp⟩
          rcases hp.eq_two_or_odd with he | ho
          · exact he
          · have hh := Nat.mod_mod_of_dvd n (show 2 ∣ m by rw [hm]; exact dvd_mul_right 2 q)
            rw [hmod] at hh
            have hodd := Nat.odd_iff.mp ho
            omega
        · rintro rfl
          exact ⟨by omega,Nat.mod_eq_of_lt (by omega),Nat.prime_two⟩
      · simp only [if_neg h,mem_filter,mem_range,notMem_empty,iff_false]
        rintro ⟨_,hmod,hp⟩
        rcases hp.eq_two_or_odd with he | ho
        · subst n
          rw [Nat.mod_eq_of_lt (by omega : 2 < m)] at hmod
          exact h hmod.symm
        · have hh := Nat.mod_mod_of_dvd n (show 2 ∣ m by rw [hm]; exact dvd_mul_right 2 q)
          rw [hmod,Nat.even_iff.mp ha] at hh
          have hodd := Nat.odd_iff.mp ho
          omega
    dsimp only [A]
    rw [hset]
    split_ifs <;> simp
  have hEvenE : (∑ a ∈ (range q).filter Even, D a^2) ≤ (Real.log 2)^2 := by
    have hpoint (a : ℕ) (ha : a ∈ (range q).filter Even) :
        D a^2 = if a=2 % q then (Real.log 2)^2 else 0 := by
      obtain ⟨hal,hae⟩ := mem_filter.mp ha
      have halt := mem_range.mp hal
      dsimp only [D]
      rw [hAeven a hae, hAeven (a+q) (hae.add hqe)]
      by_cases he : q=2
      · have ha0 : a=0 := by
          have hm := Nat.even_iff.mp hae
          omega
        simp [he,ha0]
      · have hqt : 2 < q := by omega
        rw [Nat.mod_eq_of_lt hqt,if_neg (show a+q≠2 by omega)]
        by_cases ha2 : a=2 <;> simp [ha2]
    calc
      _ = ∑ a ∈ (range q).filter Even, if a=2 % q then (Real.log 2)^2 else 0 :=
        sum_congr rfl hpoint
      _ ≤ ∑ a ∈ range q, if a=2 % q then (Real.log 2)^2 else 0 := by
        apply sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
        intro a ha hb
        split_ifs <;> positivity
      _ = _ := by simp [Nat.mod_lt 2 hq]
  have hsplit : (∑ a ∈ range q,D a^2) =
      (∑ a ∈ O,D a^2) + ∑ a ∈ (range q).filter Even,D a^2 := by
    rw [← sum_filter_add_sum_filter_not (range q) Odd]
    congr 1
    ext a
    simp [Nat.not_odd_iff_even]
  simpa only [D,A,hm,q] using (show (∑ a ∈ range q,D a^2) ≤ 2*B^2+(Real.log 2)^2 by
    rw [hsplit]
    linarith only [hoddE,hEvenE])
 
private theorem reflectBound (N q : ℕ) (hq : 0 < q) (D : ℕ → ℝ) :
    |∑ r ∈ range q, (if (N+2*q-r) % (2*q) < q then (1:ℝ) else -1)*D r*D ((N+q-r) % q)| ≤
      ∑ r ∈ range q,D r^2 := by
  let ρ (r : ℕ) := (N+q-r) % q
  have hlt (r : ℕ) : ρ r < q := Nat.mod_lt _ hq
  have hi (r : ℕ) (hr : r < q) : ρ (ρ r)=r := by
    have hd := Nat.mod_add_div (N+q-r) q
    have he : N+q-ρ r = r + q*((N+q-r)/q) := by
      change N+q-(N+q-r) % q = _
      omega
    change (N+q-ρ r) % q=r
    rw [he,Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt hr]
  have hs : (∑ r ∈ range q,D (ρ r)^2) = ∑ r ∈ range q,D r^2 := by
    apply sum_bij (fun r _ => ρ r)
    · intro r hr
      exact mem_range.mpr (hlt r)
    · intro a ha b hb he
      rw [← hi a (mem_range.mp ha),← hi b (mem_range.mp hb),he]
    · intro b hb
      exact ⟨ρ b,mem_range.mpr (hlt b),hi b (mem_range.mp hb)⟩
    · intros
      rfl
  calc
    _ ≤ ∑ r ∈ range q, |(if (N+2*q-r) % (2*q) < q then (1:ℝ) else -1)*D r*D (ρ r)| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ r ∈ range q, (D r^2+D (ρ r)^2)/2 := by
      apply sum_le_sum
      intro r hr
      rw [abs_mul,abs_mul]
      have he : |(if (N+2*q-r) % (2*q) < q then (1:ℝ) else -1)|=1 := by split_ifs <;> norm_num
      rw [he,one_mul]
      have hp := sq_nonneg (|D r|-|D (ρ r)|)
      have he1 : |D r|^2 = D r^2 := sq_abs _
      have he2 : |D (ρ r)|^2 = D (ρ r)^2 := sq_abs _
      nlinarith only [hp, he1, he2]
    _ = _ := by rw [← sum_div,sum_add_distrib,hs]; ring

private theorem geometric (K : ℕ) :
    (∑ k ∈ range K, (2:ℝ)^k) = 2^K-1 := by
  induction K with
  | zero => simp
  | succ K ih => rw [sum_range_succ,ih,pow_succ]; ring

theorem Conjectures.Goldbach.DyadicCoarseReflectionBudget :
    ∀ (N K : ℕ) (Q C : ℝ), 4 ≤ N → Even N → N < 2^K → 0 ≤ Q → 2*Q ≤ N → 0 ≤ C →
      (∀ k : ℕ, 1 ≤ k → k < K → (2^k : ℝ) ≤ Q →
        ∀ χ : DirichletCharacter ℂ (2^(k+1)), χ.IsPrimitive →
          ‖∑ n ∈ (Finset.range (N+1)).filter Nat.Prime,
            (Real.log (n : ℝ) : ℂ) * star (χ (n : ZMod (2^(k+1))))‖ ≤
              C * Real.sqrt (N : ℝ) * (Real.log (2*N : ℝ))^2) →
      let w := fun n : ℕ => if n.Prime then Real.log (n : ℝ) else 0
      let A := fun (d r : ℕ) => ∑ n ∈ (Finset.range (N+1)).filter (fun n => n % d=r), w n
      let S := (Finset.range K).filter (fun k => 1 ≤ k ∧ (2^k : ℝ) ≤ Q)
      (∑ k ∈ S,
        let q : ℕ := 2^k
        let D := fun r : ℕ => A (2*q) r - A (2*q) (r+q)
        |(q : ℝ) / ((2^K : ℕ) : ℝ) * ∑ r ∈ Finset.range q,
          (if (N+2*q-r) % (2*q) < q then (1 : ℝ) else -1) * D r * D ((N+q-r) % q)|) ≤ 4 * C^2 * Q * (Real.log (2*N : ℝ))^4 + (Real.log 2)^2 := by
  intro N K Q C hN hNe hNK hQ hQN hC H
  dsimp only
  let B := C * Real.sqrt (N : ℝ) * (Real.log (2*N : ℝ))^2
  let M : ℝ := ((2^K : ℕ) : ℝ)
  let S := (range K).filter (fun k => 1 ≤ k ∧ (2^k : ℝ) ≤ Q)
  have hM : 0 < M := by positivity
  have hB : 0 ≤ B := by positivity
  have hN' : (N:ℝ) < M := by dsimp only [M]; exact_mod_cast hNK
  let w := fun n : ℕ => if n.Prime then Real.log (n : ℝ) else 0
  let A := fun (d r : ℕ) => ∑ n ∈ (range (N+1)).filter (fun n => n % d=r), w n
  have hA (d r : ℕ) : A d r =
      ∑ n ∈ (range (N+1)).filter (fun n => n % d=r ∧ n.Prime), Real.log (n : ℝ) := by
    dsimp only [A,w]
    rw [← sum_filter,filter_filter]
  have hsumM : (∑ k ∈ S,(2:ℝ)^k) ≤ M := by
    calc
      _ ≤ ∑ k ∈ range K,(2:ℝ)^k := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (by intros; positivity)
      _ = 2^K-1 := geometric K
      _ ≤ M := by dsimp [M]; push_cast; linarith
  have hsumQ : (∑ k ∈ S,(2:ℝ)^k) ≤ 2*Q := by
    by_cases he : S.Nonempty
    · let j := S.max' he
      have hj := (mem_filter.mp (max'_mem S he)).2.2
      have hsub : S ⊆ range (j+1) := fun k hk => mem_range.mpr (Nat.lt_succ_of_le (le_max' S k hk))
      calc
        _ ≤ ∑ k ∈ range (j+1),(2:ℝ)^k := sum_le_sum_of_subset_of_nonneg hsub (by intros; positivity)
        _ = 2^(j+1)-1 := geometric _
        _ ≤ 2*Q := by rw [pow_succ]; linarith
    · have hs : S=∅ := not_nonempty_iff_eq_empty.mp he
      simp [hs,hQ]
  change (∑ k ∈ S, |((2^k:ℕ):ℝ)/M * ∑ r ∈ range (2^k),
      (if (N+2*2^k-r) % (2*2^k) < 2^k then (1:ℝ) else -1) *
      (A (2*2^k) r-A (2*2^k) (r+2^k)) *
      (A (2*2^k) ((N+2^k-r) % 2^k)-A (2*2^k) (((N+2^k-r) % 2^k)+2^k))|) ≤ _
  calc
    _ ≤ ∑ k ∈ S, (2:ℝ)^k/M * (2*B^2+(Real.log 2)^2) := by
      apply sum_le_sum
      intro k hk
      obtain ⟨hkr,hk1,hkQ⟩ := mem_filter.mp hk
      let q : ℕ := 2^k
      let D (r : ℕ) := A (2*q) r-A (2*q) (r+q)
      have hq : 0 < q := by positivity
      have hE := layerEnergy N k hN hk1 B hB (H k hk1 (mem_range.mp hkr) hkQ)
      dsimp only at hE
      have hED : (∑ r ∈ range q,D r^2) ≤ 2*B^2+(Real.log 2)^2 := by
        simpa only [D,q,hA] using hE
      have hc := (reflectBound N q hq D).trans hED
      change |(q:ℝ)/M * ∑ r ∈ range q, (if (N+2*q-r) % (2*q) < q then (1:ℝ) else -1)*D r*D ((N+q-r) % q)| ≤ _
      rw [abs_mul,abs_of_nonneg (by positivity : 0 ≤ (q:ℝ)/M)]
      simpa only [q,Nat.cast_pow,Nat.cast_ofNat] using mul_le_mul_of_nonneg_left hc (by positivity : 0 ≤ (q:ℝ)/M)
    _ = (∑ k ∈ S,(2:ℝ)^k)/M * (2*B^2+(Real.log 2)^2) := by
      rw [← sum_mul,← sum_div]
    _ ≤ _ := by
      have h1 : (∑ k ∈ S,(2:ℝ)^k)/M ≤ 1 := (div_le_one hM).mpr hsumM
      have h2 : (∑ k ∈ S,(2:ℝ)^k)/M * (2*B^2) ≤ 4*C^2*Q*(Real.log (2*N:ℝ))^4 := by
        have hBsq : B^2=C^2*(N:ℝ)*(Real.log (2*N:ℝ))^4 := by
          dsimp [B]
          rw [mul_pow,mul_pow,Real.sq_sqrt (by positivity)]
          ring
        rw [hBsq]
        have hratio : (N:ℝ)/M ≤ 1 := (div_le_one hM).mpr hN'.le
        have hs0 : 0 ≤ (∑ k ∈ S,(2:ℝ)^k) := sum_nonneg fun _ _ => by positivity
        calc
          _ = (∑ k ∈ S,(2:ℝ)^k)*((N:ℝ)/M)*(2*C^2*(Real.log (2*N:ℝ))^4) := by ring
          _ ≤ (2*Q)*1*(2*C^2*(Real.log (2*N:ℝ))^4) := by
            exact mul_le_mul_of_nonneg_right (mul_le_mul hsumQ hratio (by positivity) (by positivity)) (by positivity)
          _ = _ := by ring
      nlinarith only [h2,mul_le_mul_of_nonneg_right h1 (sq_nonneg (Real.log 2))]
