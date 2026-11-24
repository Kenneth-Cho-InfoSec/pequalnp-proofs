import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.GenericRejection PEqualNP.TopForm in
theorem PEqualNP.Outside.R_meta_2984_1
    (hMedium : ∀ (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit),
      200 ≤ q → q ≤ 299 → N = q ^ 2 + q + 1 →
      (∀ l, (S l).card = q + 1) →
      (∀ p r, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l) →
      IsAO2 (N + N) C → RightOnIncidentPairs S C →
      (∀ X Y, Y.card ≤ q → IsFalseInput S X Y →
        C.eval (incidenceInput X Y) = false) →
      3 * N ≤ C.size + 1)
    (hLarge : ∀ (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit),
      300 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l, (S l).card = q + 1) →
      (∀ p r, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l) →
      IsAO2 (N + N) C → C.output < N + N + C.size →
      RightOnIncidentPairs S C →
      (∀ X Y, Y.card ≤ q → IsFalseInput S X Y →
        C.eval (incidenceInput X Y) = false) →
      N * q ≤ 100 * C.size) :
    ∀ (q N : ℕ) (S : Fin N → Finset (Fin N)) (C : Circuit),
      200 ≤ q → N = q ^ 2 + q + 1 →
      (∀ l, (S l).card = q + 1) →
      (∀ p r, p ≠ r → ∃! l, p ∈ S l ∧ r ∈ S l) →
      IsAO2 (N + N) C → C.output < N + N + C.size →
      RightOnIncidentPairs S C →
      (∀ X Y, Y.card ≤ q → IsFalseInput S X Y →
        C.eval (incidenceInput X Y) = false) →
      N * q ≤ 100 * C.size := by
  intro q N S C hq hN hlines huniq hmodel hout hright hreject
  by_cases hmid : q ≤ 299
  · have hbound := hMedium q N S C hq hmid hN hlines huniq hmodel hright hreject
    have hNlarge : 100 ≤ N := by nlinarith [hN, hq]
    have h300 : 300 * N ≤ 100 * C.size + 100 := by nlinarith [hbound]
    have h299 : 299 * N ≤ 100 * C.size := by nlinarith [h300, hNlarge]
    have hprod : N * q ≤ N * 299 := Nat.mul_le_mul_left N hmid
    nlinarith [hprod, h299]
  · have hhigh : 300 ≤ q := by omega
    exact hLarge q N S C hhigh hN hlines huniq hmodel hout hright hreject
