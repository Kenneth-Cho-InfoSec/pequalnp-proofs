import Mathlib
import PEqualNP.Defs
import PEqualNP.Library.LRAT.Link

private def edges : List (ℕ × ℕ) :=
  [(0, 7), (0, 8), (0, 10), (1, 7), (1, 9), (1, 13), (2, 8), (2, 12), (2, 13),
   (3, 7), (3, 11), (3, 12), (4, 10), (4, 11), (4, 13), (5, 9), (5, 10), (5, 12),
   (6, 8), (6, 9), (6, 11)]

private def criticalRows : List ℕ :=
  ([127, 129, 130, 136, 244, 257, 260, 314, 320, 432, 514, 541, 544, 576, 660, 792,
   1025, 1040, 1056, 1102, 1220, 1290, 1548, 2056, 2064, 2087, 2112, 2212, 2338,
   2565, 3078, 3716, 4100, 4104, 4128, 4179, 4304, 4370, 4625, 5008, 5186, 6147,
   7426, 8194, 8196, 8208, 8297, 8416, 8488, 8713, 9288, 9992, 10273, 10656,
   12353, 13504, 14849, 16256] : List ℕ).filter (fun r => r < 2 ^ 14)

private def edgeFun (x : Fin 14 → Bool) : Bool :=
  decide (∃ u v : Fin 14, (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true)

/-- The only remaining obligation is a checked LRAT refutation of the row-reduced
26-gate encoding. The rows are the 21 minimal true inputs and 37 maximal false inputs;
the generic link theorem lifts this finite certificate to all monotone circuits. -/
theorem PEqualNP.Outside.L_meta_971
    (hUnsat : ¬ PEqualNP.Library.LRAT.FormulaSat
      (PEqualNP.Library.LRAT.Link.enc 14 26
        (PEqualNP.Library.LRAT.Link.rowFun 14 edgeFun) criticalRows)) :
    ∀ C : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 C →
      (∀ x : Fin 14 → Bool,
        (C.eval (List.ofFn x) = true ↔
          ∃ u v : Fin 14, (u.val, v.val) ∈ edges ∧ x u = true ∧ x v = true)) →
      27 ≤ C.size := by
  intro C hMono hCompute
  have hRows : ∀ r ∈ criticalRows, r < 2 ^ 14 := by
    intro r hr
    unfold criticalRows at hr
    exact of_decide_eq_true (List.mem_filter.mp hr).2
  have hEval : ∀ x : Fin 14 → Bool, C.eval (List.ofFn x) = edgeFun x := by
    intro x
    apply Bool.eq_iff_iff.mpr
    change C.eval (List.ofFn x) = true ↔
      decide (∃ u v : Fin 14, (u.val, v.val) ∈ edges ∧
        x u = true ∧ x v = true) = true
    exact (hCompute x).trans (Eq.to_iff decide_eq_true_eq.symm)
  exact PEqualNP.Library.LRAT.Link.lower_of_unsat
    14 26 edgeFun criticalRows hRows hUnsat C hMono hEval

