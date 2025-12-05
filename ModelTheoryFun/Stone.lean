import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Satisfiability
import Mathlib.ModelTheory.Types
import Mathlib.Topology.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Baire.LocallyCompactRegular

open FirstOrder
open FirstOrder.Language

namespace TypeSpace

variable {L : FirstOrder.Language} {T : L.Theory}

def basis {n : ℕ} : Set (Set (T.CompleteType (Fin n))) := {X | ∃ φ, X = {p | φ ∈ p}}
def basicOpen {n : ℕ} (φ : L[[Fin n]].Sentence) : Set (T.CompleteType (Fin n)) :=
  {X : T.CompleteType (Fin n) | φ ∈ X}


instance (n : ℕ) : TopologicalSpace (T.CompleteType (Fin n)) :=
    TopologicalSpace.generateFrom (basis)
lemma exists_separating_sets {n : ℕ} (x y : T.CompleteType (Fin n))
                         (φ : L[[Fin n]].Sentence)
                         (φ_inx_φ_niny : φ ∈ x.toTheory ∧ φ ∉ y.toTheory) :
                         ∃ u v : Set (T.CompleteType (Fin n)), IsOpen u ∧ IsOpen v ∧
                         x ∈ u ∧ y ∈ v ∧ Disjoint u v := by
                          let B_φ : Set (T.CompleteType (Fin n)) := {X | φ ∈ X}
                          let B_nφ : Set (T.CompleteType (Fin n)) := {X | φ.not ∈ X}
                          refine ⟨B_φ, B_nφ, ?_, ?_, ?_, ?_, ?_⟩
                          · apply TopologicalSpace.GenerateOpen.basic
                            dsimp[basis, B_φ]
                            use φ
                          · apply TopologicalSpace.GenerateOpen.basic
                            dsimp[basis, B_φ]
                            use φ.not
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
    have swapped : φ.not ∈ x ∧ φ.not ∉ y := by
      constructor
      · exact (x.not_mem_iff φ).2 φ_x_y.2
      · intro nφy
        exact (y.not_mem_iff φ).1 nφy φ_x_y.1
    exact exists_separating_sets x y φ.not swapped

lemma basicOpen_compl {n : ℕ} (T : L.Theory) (φ : L[[Fin n]].Sentence) :
  basicOpen (T := T) φ.not = (basicOpen φ)ᶜ := by ext p ; exact p.not_mem_iff φ

instance {n : ℕ} : CompactSpace (T.CompleteType (Fin n)) := by
  constructor
  rw[isCompact_iff_ultrafilter_le_nhds]
  intros F hf_ultra
  let pTheory : L[[Fin n]].Theory := {φ | basicOpen φ ∈ F}
  have p_isConsistentWith : (L.lhomWithConstants (Fin n)).onTheory T ⊆ pTheory := by
    intro φ φinT
    have uni : basicOpen (T := T) φ = Set.univ := by
      ext h
      simp [basicOpen, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact h.subset φinT
    rw[Set.mem_setOf_eq, uni]
    exact Filter.univ_mem
  have p_isMaximal : Theory.IsMaximal pTheory := by
    rw[Theory.IsMaximal]
    constructor
    · rw[Theory.isSatisfiable_iff_isFinitelySatisfiable, Theory.IsFinitelySatisfiable]
      intro φᵢ h_subset
      have in_uf : ∀ φ ∈ φᵢ, basicOpen φ ∈ F.toFilter := by
        intro φ φ_in_finset
        exact h_subset φ_in_finset
      rw[←Filter.biInter_finset_mem φᵢ] at in_uf
      obtain ⟨T, T_inter⟩ := F.neBot.nonempty_of_mem in_uf
      have subset : SetLike.coe φᵢ ⊆ T.toTheory := by rwa[Set.mem_iInter₂] at T_inter
      exact Theory.IsSatisfiable.mono T.isMaximal'.1 subset
    · intro φ
      rcases Ultrafilter.mem_or_compl_mem F (basicOpen φ) with  φ_in | φ_nin
      · exact Or.inl φ_in
      · rw[←basicOpen_compl T φ] at φ_nin
        exact Or.inr φ_nin
  let p : T.CompleteType (Fin n) := ⟨pTheory, p_isConsistentWith, p_isMaximal⟩
  use p
  constructor
  · trivial
  · rw [TopologicalSpace.nhds_generateFrom]
    apply le_iInf₂
    intro _ s_in
    rw [Filter.le_principal_iff]
    obtain ⟨_, rfl⟩ := s_in.2
    exact s_in.1

instance {n : ℕ} : BaireSpace (T.CompleteType (Fin n)) :=
  BaireSpace.of_t2Space_locallyCompactSpace

end TypeSpace
