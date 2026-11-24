import Mathlib

namespace PEqualNP.Outside.L_clb_033_aux

open Polynomial

-- the summand of the binomial expansion of (X + (1 - X)) ^ n
noncomputable def term (n i : ℕ) : Polynomial ℤ :=
  C ((n.choose i : ℕ) : ℤ) * X ^ i * (1 - X) ^ (n - i)

theorem term_eval (n i : ℕ) (x : ℤ) :
    (term n i).eval x = ((n.choose i : ℕ) : ℤ) * x ^ i * (1 - x) ^ (n - i) := by
  simp [term]

theorem term_deg (n i : ℕ) (hi : i ≤ n) : (term n i).natDegree ≤ n := by
  unfold term
  have h1 : (C ((n.choose i : ℕ) : ℤ) * X ^ i : Polynomial ℤ).natDegree ≤ i :=
    natDegree_C_mul_X_pow_le _ _
  have h2 : ((1 - X : Polynomial ℤ) ^ (n - i)).natDegree ≤ n - i := by
    refine (natDegree_pow_le).trans ?_
    have : (1 - X : Polynomial ℤ).natDegree ≤ 1 := by
      refine (natDegree_sub_le _ _).trans ?_
      simp
    calc (n - i) * (1 - X : Polynomial ℤ).natDegree ≤ (n - i) * 1 := Nat.mul_le_mul_left _ this
      _ = n - i := by ring
  calc _ ≤ _ := natDegree_mul_le
    _ ≤ i + (n - i) := Nat.add_le_add h1 h2
    _ = n := by omega

theorem full_sum (n : ℕ) (x : ℤ) :
    ∑ i ∈ Finset.range (n + 1), ((n.choose i : ℕ) : ℤ) * x ^ i * (1 - x) ^ (n - i) = 1 := by
  calc ∑ i ∈ Finset.range (n + 1), ((n.choose i : ℕ) : ℤ) * x ^ i * (1 - x) ^ (n - i)
      = ∑ i ∈ Finset.range (n + 1), x ^ i * (1 - x) ^ (n - i) * ((n.choose i : ℕ) : ℤ) :=
        Finset.sum_congr rfl fun i _ => by ring
    _ = (x + (1 - x)) ^ n := (add_pow x (1 - x) n).symm
    _ = 1 := by ring

end PEqualNP.Outside.L_clb_033_aux

open Polynomial PEqualNP.Outside.L_clb_033_aux

theorem PEqualNP.Outside.L_clb_033 : ∀ m k : ℕ, 1 ≤ k → ∃ F : Polynomial ℤ, F.natDegree ≤ 2 * k - 1 ∧ ∀ x : ℤ, ((m : ℤ) ∣ x → (m : ℤ) ^ k ∣ F.eval x) ∧ ((m : ℤ) ∣ x - 1 → (m : ℤ) ^ k ∣ F.eval x - 1) := by
  intro m k hk
  refine ⟨∑ i ∈ Finset.Ico k (2 * k - 1 + 1), term (2 * k - 1) i, ?_, ?_⟩
  · refine natDegree_sum_le_of_forall_le _ _ fun i hi => ?_
    have := Finset.mem_Ico.mp hi
    exact term_deg _ _ (by omega)
  · intro x
    rw [show ∀ (s : Finset ℕ) (f : ℕ → Polynomial ℤ), (∑ i ∈ s, f i).eval x = ∑ i ∈ s, (f i).eval x from fun s f => map_sum (Polynomial.evalRingHom x) f s]
    simp only [term_eval]
    constructor
    · intro hx
      refine Finset.dvd_sum fun i hi => ?_
      have hi' := Finset.mem_Ico.mp hi
      have hxi : (m : ℤ) ^ k ∣ x ^ i :=
        (pow_dvd_pow_of_dvd hx k).trans (pow_dvd_pow x hi'.1)
      exact Dvd.dvd.mul_right (Dvd.dvd.mul_left hxi _) _
    · intro hx
      have hx' : (m : ℤ) ∣ 1 - x := by
        have := dvd_neg.mpr hx
        simpa using this
      have hsplit := Finset.sum_range_add_sum_Ico
        (fun i => ((2 * k - 1).choose i : ℕ) * x ^ i * (1 - x) ^ (2 * k - 1 - i))
        (show k ≤ 2 * k - 1 + 1 by omega)
      rw [full_sum] at hsplit
      have hlow : (m : ℤ) ^ k ∣ ∑ i ∈ Finset.range k,
          ((2 * k - 1).choose i : ℕ) * x ^ i * (1 - x) ^ (2 * k - 1 - i) := by
        refine Finset.dvd_sum fun i hi => ?_
        have hi' := Finset.mem_range.mp hi
        have h1 : (m : ℤ) ^ k ∣ (1 - x) ^ (2 * k - 1 - i) :=
          (pow_dvd_pow_of_dvd hx' k).trans (pow_dvd_pow _ (by omega))
        exact Dvd.dvd.mul_left h1 _
      have : (∑ i ∈ Finset.Ico k (2 * k - 1 + 1),
          ((2 * k - 1).choose i : ℕ) * x ^ i * (1 - x) ^ (2 * k - 1 - i) : ℤ) - 1 =
          -(∑ i ∈ Finset.range k,
          ((2 * k - 1).choose i : ℕ) * x ^ i * (1 - x) ^ (2 * k - 1 - i)) := by
        linarith
      rw [this]
      exact dvd_neg.mpr hlow
