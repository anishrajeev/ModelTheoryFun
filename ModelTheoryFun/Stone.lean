import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Satisfiability
import Mathlib.ModelTheory.Types
import Mathlib.Topology.Basic
import Mathlib.Topology.Order
import Mathlib.Topology.Bases
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Separation.Profinite
import Mathlib.Topology.Connected.Separation
import Mathlib.Topology.Baire.LocallyCompactRegular

open FirstOrder
open FirstOrder.Language
open TopologicalSpace

namespace TypeSpace

variable {L : FirstOrder.Language} {T : L.Theory}

def sub_basis {n : ℕ} : Set (Set (T.CompleteType (Fin n))) := {X | ∃ φ, X = {p | φ ∈ p}}
def BasicOpen {n : ℕ} (φ : L[[Fin n]].Sentence) : Set (T.CompleteType (Fin n)) :=
  {X : T.CompleteType (Fin n) | φ ∈ X}

lemma finite_inter {n : ℕ} : FiniteInter (α := T.CompleteType (Fin n)) sub_basis := by
  constructor
  · use ⊤
    ext p
    simp
    exact Theory.CompleteType.mem_of_models p (fun M v xs a ↦ a)
  · rintro s ⟨φ, rfl⟩ t ⟨ψ, rfl⟩
    use φ ⊓ ψ
    ext p
    simp
    simp_rw[← SetLike.mem_coe, p.isMaximal.mem_iff_models (φ ⊓ ψ), p.isMaximal.mem_iff_models φ,
            p.isMaximal.mem_iff_models ψ]
    simp only [Theory.models_sentence_iff]
    constructor
    · rintro ⟨h₀, h₁⟩ M
      exact Formula.realize_inf.2 ⟨h₀ M, h₁ M⟩
    · intro h
      rw [←forall_and]
      intro M
      exact Formula.realize_inf.1 (h M)
lemma basic_open_compl {n : ℕ} (T : L.Theory) (φ : L[[Fin n]].Sentence) :
                       BasicOpen (T := T) φ.not =
    (BasicOpen φ)ᶜ := by ext p ; exact p.not_mem_iff φ

instance (n : ℕ) : TopologicalSpace (T.CompleteType (Fin n)) := generateFrom (sub_basis)
instance {n : ℕ} : T0Space (T.CompleteType (Fin n)) := by
  rw [t0Space_iff_inseparable]
  intro x y eq
  apply SetLike.ext
  intro φ
  replace eq := inseparable_iff_forall_isOpen.1 eq
  have o : IsOpen (X := (T.CompleteType (Fin n))) (BasicOpen φ) := by
    apply TopologicalSpace.GenerateOpen.basic
    use φ ; trivial
  exact eq (BasicOpen φ) o
instance {n : ℕ} : TotallySeparatedSpace (T.CompleteType (Fin n)) := by
  apply totallySeparatedSpace_of_t0_of_basis_clopen
  have h := isTopologicalBasis_of_subbasis_of_finiteInter
            (α := T.CompleteType (Fin n)) (s := sub_basis) (by trivial) finite_inter
  apply IsTopologicalBasis.of_isOpen_of_subset
  · intro _ p ; exact p.2
  · exact h
  · intro p q
    obtain ⟨φ, b⟩ := q
    constructor
    · have h : IsOpen pᶜ := by
        have q : p = BasicOpen φ := b
        rw[q, ←basic_open_compl]
        apply TopologicalSpace.GenerateOpen.basic
        exact ⟨φ.not, by trivial⟩
      rw[←compl_compl p]
      exact isClosed_compl_iff.2 h
    · apply TopologicalSpace.GenerateOpen.basic
      use φ
instance {n : ℕ} : T2Space (T.CompleteType (Fin n)) := TotallySeparatedSpace.t2Space
instance {n : ℕ} : CompactSpace (T.CompleteType (Fin n)) := by
  constructor
  rw[isCompact_iff_ultrafilter_le_nhds]
  intros F hf_ultra
  let pTheory : L[[Fin n]].Theory := {φ | BasicOpen φ ∈ F}
  have p_isConsistentWith : (L.lhomWithConstants (Fin n)).onTheory T ⊆ pTheory := by
    intro φ φinT
    have uni : BasicOpen (T := T) φ = Set.univ := by
      ext h
      simp [BasicOpen, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact h.subset φinT
    rw[Set.mem_setOf_eq, uni]
    exact Filter.univ_mem
  have p_isMaximal : Theory.IsMaximal pTheory := by
    rw[Theory.IsMaximal]
    constructor
    · rw[Theory.isSatisfiable_iff_isFinitelySatisfiable, Theory.IsFinitelySatisfiable]
      intro φᵢ h_subset
      have in_uf : ∀ φ ∈ φᵢ, BasicOpen φ ∈ F.toFilter := by
        intro φ φ_in_finset
        exact h_subset φ_in_finset
      rw[←Filter.biInter_finset_mem φᵢ] at in_uf
      obtain ⟨T, T_inter⟩ := F.neBot.nonempty_of_mem in_uf
      have subset : SetLike.coe φᵢ ⊆ T.toTheory := by rwa[Set.mem_iInter₂] at T_inter
      exact Theory.IsSatisfiable.mono T.isMaximal'.1 subset
    · intro φ
      rcases Ultrafilter.mem_or_compl_mem F (BasicOpen φ) with  φ_in | φ_nin
      · exact Or.inl φ_in
      · rw[←basic_open_compl T φ] at φ_nin
        exact Or.inr φ_nin
  let p : T.CompleteType (Fin n) := ⟨pTheory, p_isConsistentWith, p_isMaximal⟩
  use p
  constructor
  · trivial
  · rw [nhds_generateFrom]
    apply le_iInf₂
    intro _ s_in
    rw [Filter.le_principal_iff]
    obtain ⟨_, rfl⟩ := s_in.2
    exact s_in.1
instance {n : ℕ} : BaireSpace (T.CompleteType (Fin n)) := BaireSpace.of_t2Space_locallyCompactSpace

end TypeSpace
