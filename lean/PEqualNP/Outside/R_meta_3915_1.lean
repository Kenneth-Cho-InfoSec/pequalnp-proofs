import Mathlib
import PEqualNP.Defs

theorem PEqualNP.Outside.R_meta_3915_1
    (normalize : ∀ (n : ℕ) (C : PEqualNP.MetaComplexity.BinaryCircuit),
      (∀ g ∈ C.gates, ∃ a b : Bool, g.op = fun x y => x == a && y == b) →
      ∃ D : PEqualNP.MetaComplexity.BinaryCircuit,
        D.size ≤ C.size ∧
        (∀ g ∈ D.gates, ∃ a b : Bool, g.op = fun x y => x == a && y == b) ∧
        (∀ i : Fin D.size,
          let g := D.gates.get i
          g.left < g.right ∧ g.right < n + i) ∧
        ∀ xs : List Bool, xs.length = n →
          D.eval xs = C.eval (xs ++ [false]))
    (trimOutput : ∀ (n : ℕ) (D : PEqualNP.MetaComplexity.BinaryCircuit) (b : Bool),
      (∀ g ∈ D.gates, ∃ a b : Bool, g.op = fun x y => x == a && y == b) →
      (∀ i : Fin D.size,
        let g := D.gates.get i
        g.left < g.right ∧ g.right < n + i) →
      ∃ E : PEqualNP.MetaComplexity.BinaryCircuit, ∃ c : Bool,
        E.size ≤ D.size ∧
        (∀ g ∈ E.gates, ∃ a b : Bool, g.op = fun x y => x == a && y == b) ∧
        (∀ i : Fin E.size,
          let g := E.gates.get i
          g.left < g.right ∧ g.right < n + i) ∧
        (E.size = 0 ∨ E.output = n + E.size - 1) ∧
        ∀ xs : List Bool, xs.length = n →
          (E.eval xs != c) = (D.eval xs != b)) :
    have x1 : PEqualNP.MetaComplexity.BinaryCircuit → Prop := fun C =>
      ∀ g ∈ C.gates, ∃ a b : Bool, g.op = fun x y => x == a && y == b
    have x2 : ℕ → PEqualNP.MetaComplexity.BinaryCircuit → Prop := fun n C =>
      ∀ i : Fin C.size,
        let g := C.gates.get i
        g.left < g.right ∧ g.right < n + i
    ∀ (n : ℕ) (C : PEqualNP.MetaComplexity.BinaryCircuit) (b : Bool), x1 C →
      ∃ D : PEqualNP.MetaComplexity.BinaryCircuit, ∃ c : Bool,
        D.size ≤ C.size ∧ x1 D ∧ x2 n D ∧
        (D.size = 0 ∨ D.output = n + D.size - 1) ∧
        ∀ xs : List Bool, xs.length = n →
          (D.eval xs != c) = (C.eval (xs ++ [false]) != b) := by
  intro x1 x2 n C b hC
  obtain ⟨D, hsize, hshape, hordered, heval⟩ := normalize n C hC
  obtain ⟨E, c, htrim, hEshape, hEordered, houtput, hequal⟩ :=
    trimOutput n D b hshape hordered
  refine ⟨E, c, htrim.trans hsize, hEshape, hEordered, houtput, ?_⟩
  intro xs hxs
  rw [← heval xs hxs]
  exact hequal xs hxs
