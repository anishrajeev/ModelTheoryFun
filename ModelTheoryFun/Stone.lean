import Mathlib.Data.Rat.Cast.Order
import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics
import Mathlib.Tactic.Linarith
import Mathlib.ModelTheory.Satisfiability


import Mathlib.ModelTheory.Types
import Mathlib.Topology.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Order

open FirstOrder
open FirstOrder.Language
open FirstOrder.Language.BoundedFormula

namespace StoneSpace

variable {L : FirstOrder.Language} {T : L.Theory}

/-
  Constructs the
-/
def basis {n : ℕ} : Set (Set (T.CompleteType (Fin n))) := {X | ∃ φ, X = {p | φ ∈ p}}

instance (n : ℕ) : TopologicalSpace (T.CompleteType (Fin n)) :=
    TopologicalSpace.generateFrom (basis)

lemma exists_separating_sets {n : ℕ} (x y : T.CompleteType (Fin n))
                         (φ : L[[Fin n]].Sentence)
                         (φ_inx_φ_niny : φ ∈ x.toTheory ∧ φ ∉ y.toTheory) :
                         ∃ u v : Set (T.CompleteType (Fin n)), IsOpen u ∧ IsOpen v ∧
                         x ∈ u ∧ y ∈ v ∧ Disjoint u v := by
                          let B_φ : Set (T.CompleteType (Fin n)) := {X | φ ∈ X}
                          let B_nφ : Set (T.CompleteType (Fin n)) := {X | ∼φ ∈ X}
                          refine ⟨B_φ, B_nφ, ?_, ?_, ?_, ?_, ?_⟩
                          · apply TopologicalSpace.GenerateOpen.basic
                            dsimp[basis, B_φ]
                            use φ
                          · apply TopologicalSpace.GenerateOpen.basic
                            dsimp[basis, B_φ]
                            use ∼φ
                          · dsimp [B_φ]
                            exact φ_inx_φ_niny.1
                          · dsimp [B_nφ]
                            exact (y.isMaximal.2 φ).resolve_left φ_inx_φ_niny.2
                          · rw[Set.disjoint_left]
                            · dsimp [B_φ, B_nφ]
                              intro Γ
                              contrapose!
                              exact (Γ.not_mem_iff φ).1


instance {n : ℕ} : T2Space (T.CompleteType (Fin n)) := by
  constructor
  intro x y xneqy
  have xT_neq_yT : x.toTheory ≠ y.toTheory := by
    contrapose! xneqy
    cases x
    cases y
    simp_all
  simp at xT_neq_yT
  rw[Set.Subset.antisymm_iff, not_and_or] at xT_neq_yT
  rcases xT_neq_yT with x_nsub_y | y_nsub_x
  · rw [Set.subset_def] at x_nsub_y
    push_neg at x_nsub_y
    rcases x_nsub_y with ⟨φ, φ_x_y⟩
    exact exists_separating_sets x y φ φ_x_y
  · rw [Set.subset_def] at y_nsub_x
    push_neg at y_nsub_x
    rcases y_nsub_x with ⟨φ, φ_x_y⟩
    have swapped : ∼φ ∈ x ∧ ∼φ ∉ y := by
      constructor
      · exact (x.not_mem_iff φ).2 φ_x_y.2
      · intro nφy
        exact (y.not_mem_iff φ).1 nφy φ_x_y.1
    exact exists_separating_sets x y ∼φ swapped
end StoneSpace
