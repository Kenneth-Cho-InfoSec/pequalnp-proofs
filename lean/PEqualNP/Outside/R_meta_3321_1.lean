import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover

noncomputable def PEqualNP.Outside.R_meta_3321_badCount
    (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (E : PEqualNP.CircuitLowerBounds.Circuit) : ℕ := by
  classical
  exact (Finset.univ.filter (fun j : Fin E.gates.length =>
    (PEqualNP.MetaComplexity.NestedCover.gateAt E j.val).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
      ((∃ z : Fin (N + N) → Bool,
          (E.wires (List.ofFn z)).getD (N + N + j.val) false = true ∧
          ¬ ((E.wires (List.ofFn (fun ka : Fin (N + N) => decide (ka.val < N) && z ka))).getD (N + N + j.val) false = true ∨
             (E.wires (List.ofFn (fun kb : Fin (N + N) => decide (N ≤ kb.val) && z kb))).getD (N + N + j.val) false = true ∨
             ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) ∨
       (∃ p : Fin N,
          (E.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j.val) false = true) ∨
       (∃ l : Fin N,
          (E.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j.val) false = true)))).card

theorem PEqualNP.Outside.R_meta_3321_1
    (oneHotPeel : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
      PEqualNP.MetaComplexity.Monotone2 C →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C →
      (∀ z : Fin (N + N) → Bool,
        PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔
          ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      (∃ j, j < C.gates.length ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        ((∃ p : Fin N,
          (C.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = true) ∨
         (∃ l : Fin N,
          (C.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = true))) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 D ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧
        D.size ≤ C.size ∧
        (∀ z : Fin (N + N) → Bool,
          PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔
            ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
        PEqualNP.Outside.R_meta_3321_badCount N I D < PEqualNP.Outside.R_meta_3321_badCount N I C)
    (rectanglePeel : ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
      (C : PEqualNP.CircuitLowerBounds.Circuit),
      (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
      PEqualNP.MetaComplexity.Monotone2 C →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C →
      (∀ z : Fin (N + N) → Bool,
        PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔
          ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      (∀ j < C.gates.length,
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (∀ p : Fin N,
          (C.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧
        ∀ l : Fin N,
          (C.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false) →
      (∃ j, j < C.gates.length ∧
        (PEqualNP.MetaComplexity.NestedCover.gateAt C j).op = PEqualNP.CircuitLowerBounds.GateOp.and ∧
        ∃ z : Fin (N + N) → Bool,
          (C.wires (List.ofFn z)).getD (N + N + j) false = true ∧
          ¬ ((C.wires (List.ofFn (fun ka : Fin (N + N) => decide (ka.val < N) && z ka))).getD (N + N + j) false = true ∨
             (C.wires (List.ofFn (fun kb : Fin (N + N) => decide (N ≤ kb.val) && z kb))).getD (N + N + j) false = true ∨
             ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) →
      ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
        PEqualNP.MetaComplexity.Monotone2 D ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧
        D.size ≤ C.size ∧
        (∀ z : Fin (N + N) → Bool,
          PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔
            ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
        PEqualNP.Outside.R_meta_3321_badCount N I D < PEqualNP.Outside.R_meta_3321_badCount N I C)
    :
  ∀ (N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I]
    (C : PEqualNP.CircuitLowerBounds.Circuit),
    (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
    PEqualNP.MetaComplexity.Monotone2 C →
    PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) C →
    (∀ z : Fin (N + N) → Bool,
      PEqualNP.MetaComplexity.circuitFun (N + N) C z = true ↔
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
    ∃ D : PEqualNP.CircuitLowerBounds.Circuit,
      PEqualNP.MetaComplexity.Monotone2 D ∧
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧
      D.size ≤ C.size ∧
      (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔
        ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
      (∀ j < D.gates.length,
        (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        ∀ z : Fin (N + N) → Bool,
          (D.wires (List.ofFn z)).getD (N + N + j) false = true →
          (D.wires (List.ofFn (fun ka : Fin (N + N) => decide (ka.val < N) && z ka))).getD (N + N + j) false = true ∨
          (D.wires (List.ofFn (fun kb : Fin (N + N) => decide (N ≤ kb.val) && z kb))).getD (N + N + j) false = true ∨
          ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
      (∀ j < D.gates.length,
        (PEqualNP.MetaComplexity.NestedCover.gateAt D j).op = PEqualNP.CircuitLowerBounds.GateOp.and →
        (∀ p : Fin N,
          (D.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false = false) ∧
        ∀ l : Fin N,
          (D.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false = false) := by
  classical
  intro N I hdec C hNoSquare hMono hRead hSpec
  let badGate : ∀ (E : Circuit), Fin E.gates.length → Prop := fun E j =>
    (gateAt E j.val).op = GateOp.and ∧
      ((∃ z : Fin (N + N) → Bool,
          (E.wires (List.ofFn z)).getD (N + N + j.val) false = true ∧
          ¬ ((E.wires (List.ofFn (fun ka : Fin (N + N) => decide (ka.val < N) && z ka))).getD (N + N + j.val) false = true ∨
             (E.wires (List.ofFn (fun kb : Fin (N + N) => decide (N ≤ kb.val) && z kb))).getD (N + N + j.val) false = true ∨
             ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) ∨
       (∃ p : Fin N,
          (E.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j.val) false = true) ∨
       (∃ l : Fin N,
          (E.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j.val) false = true))
  let badCount (E : Circuit) : ℕ := (Finset.univ.filter (badGate E)).card
  have aux : ∀ m : ℕ, ∀ (E : Circuit), badCount E = m →
      (∀ p p' l l' : Fin N, p ≠ p' → l ≠ l' → ¬ (I p l ∧ I p l' ∧ I p' l ∧ I p' l')) →
      PEqualNP.MetaComplexity.Monotone2 E →
      PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) E →
      (∀ z : Fin (N + N) → Bool,
        PEqualNP.MetaComplexity.circuitFun (N + N) E z = true ↔
          ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) →
      ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧
        PEqualNP.MetaComplexity.NestedCover.ReadsBack (N + N) D ∧ D.size ≤ E.size ∧
        (∀ z : Fin (N + N) → Bool,
          PEqualNP.MetaComplexity.circuitFun (N + N) D z = true ↔
            ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) ∧
        badCount D = 0 := by
    intro m
    induction m using Nat.strong_induction_on with
    | ind m ih =>
      intro E hMeasure hNoSquare' hMono' hRead' hSpec'
      by_cases hzero : badCount E = 0
      · exact ⟨E, hMono', hRead', le_rfl, hSpec', hzero⟩
      · have hpos : 0 < badCount E := Nat.pos_of_ne_zero hzero
        obtain ⟨j, hj⟩ := Finset.card_pos.mp (by simpa [badCount] using hpos)
        have hbad := (Finset.mem_filter.mp hj).2
        by_cases hunit : ∃ j0, j0 < E.gates.length ∧
            (gateAt E j0).op = GateOp.and ∧
            ((∃ p : Fin N,
                (E.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j0) false = true) ∨
             (∃ l : Fin N,
                (E.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j0) false = true))
        · obtain ⟨D, hMonoD, hReadD, hSizeD, hSpecD, hDec⟩ :=
            oneHotPeel N I E hNoSquare' hMono' hRead' hSpec' hunit
          have hlt : badCount D < m := by rw [← hMeasure]; exact hDec
          obtain ⟨F, hMonoF, hReadF, hSizeF, hSpecF, hZeroF⟩ :=
            ih (badCount D) hlt D rfl hNoSquare' hMonoD hReadD hSpecD
          exact ⟨F, hMonoF, hReadF, hSizeF.trans hSizeD, hSpecF, hZeroF⟩
        · have hNoUnit : ∀ j0 < E.gates.length, (gateAt E j0).op = GateOp.and →
              (∀ p : Fin N,
                (E.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j0) false = false) ∧
              ∀ l : Fin N,
                (E.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j0) false = false := by
            intro j0 hj0 hop
            constructor
            · intro p
              cases hv : (E.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j0) false with
              | false => rfl
              | true => exact False.elim (hunit ⟨j0, hj0, hop, Or.inl ⟨p, hv⟩⟩)
            · intro l
              cases hv : (E.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j0) false with
              | false => rfl
              | true => exact False.elim (hunit ⟨j0, hj0, hop, Or.inr ⟨l, hv⟩⟩)
          have hRect : ∃ j0, j0 < E.gates.length ∧ (gateAt E j0).op = GateOp.and ∧
              ∃ z : Fin (N + N) → Bool,
                (E.wires (List.ofFn z)).getD (N + N + j0) false = true ∧
                ¬ ((E.wires (List.ofFn (fun ka : Fin (N + N) => decide (ka.val < N) && z ka))).getD (N + N + j0) false = true ∨
                   (E.wires (List.ofFn (fun kb : Fin (N + N) => decide (N ≤ kb.val) && z kb))).getD (N + N + j0) false = true ∨
                   ∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true) := by
            refine ⟨j.val, j.isLt, hbad.1, ?_⟩
            rcases hbad.2 with rect | unitCases
            · exact rect
            · rcases unitCases with point | line
              · obtain ⟨p, hp⟩ := point
                exact False.elim (hunit ⟨j.val, j.isLt, hbad.1, Or.inl ⟨p, hp⟩⟩)
              · obtain ⟨l, hl⟩ := line
                exact False.elim (hunit ⟨j.val, j.isLt, hbad.1, Or.inr ⟨l, hl⟩⟩)
          obtain ⟨D, hMonoD, hReadD, hSizeD, hSpecD, hDec⟩ :=
            rectanglePeel N I E hNoSquare' hMono' hRead' hSpec' hNoUnit hRect
          have hlt : badCount D < m := by rw [← hMeasure]; exact hDec
          obtain ⟨F, hMonoF, hReadF, hSizeF, hSpecF, hZeroF⟩ :=
            ih (badCount D) hlt D rfl hNoSquare' hMonoD hReadD hSpecD
          exact ⟨F, hMonoF, hReadF, hSizeF.trans hSizeD, hSpecF, hZeroF⟩
  obtain ⟨D, hMonoD, hReadD, hSizeD, hSpecD, hZeroD⟩ :=
    aux (badCount C) C rfl hNoSquare hMono hRead hSpec
  refine ⟨D, hMonoD, hReadD, hSizeD, hSpecD, ?_, ?_⟩
  · intro j hj hop z hGate
    by_contra hFalse
    have hmem : (⟨j, hj⟩ : Fin D.gates.length) ∈ Finset.univ.filter (badGate D) := by
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨hop, Or.inl ⟨z, hGate, hFalse⟩⟩
    have hpos : 0 < badCount D := Finset.card_pos.mpr ⟨⟨j, hj⟩, hmem⟩
    omega
  · intro j hj hop
    constructor
    · intro p
      cases hv : (D.wires (List.ofFn (fun kc : Fin (N + N) => decide (kc = Fin.castAdd N p)))).getD (N + N + j) false with
      | false => rfl
      | true =>
        have hmem : (⟨j, hj⟩ : Fin D.gates.length) ∈ Finset.univ.filter (badGate D) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hop, Or.inr (Or.inl ⟨p, hv⟩)⟩
        have hpos : 0 < badCount D := Finset.card_pos.mpr ⟨⟨j, hj⟩, hmem⟩
        omega
    · intro l
      cases hv : (D.wires (List.ofFn (fun kd : Fin (N + N) => decide (kd = Fin.natAdd N l)))).getD (N + N + j) false with
      | false => rfl
      | true =>
        have hmem : (⟨j, hj⟩ : Fin D.gates.length) ∈ Finset.univ.filter (badGate D) := by
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          exact ⟨hop, Or.inr (Or.inr ⟨l, hv⟩)⟩
        have hpos : 0 < badCount D := Finset.card_pos.mpr ⟨⟨j, hj⟩, hmem⟩
        omega
