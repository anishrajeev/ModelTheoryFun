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
import Mathlib.Topology.Gdelta.Basic

open FirstOrder
open FirstOrder.Language
open TopologicalSpace

namespace TypeSpace

variable {L : FirstOrder.Language} {T : L.Theory}

def basis {n : ℕ} : Set (Set (T.CompleteType (Fin n))) := {U | ∃ φ, U = {s | φ ∈ s}}
def BasicOpen {n : ℕ} (φ : L[[Fin n]].Sentence) : Set (T.CompleteType (Fin n)) :=
  {s : T.CompleteType (Fin n) | φ ∈ s}

lemma finite_inter {n : ℕ} : FiniteInter (α := T.CompleteType (Fin n)) basis := by
  constructor
  · use ⊤
    ext x
    simp
    exact Theory.CompleteType.mem_of_models x (fun _ _ _ a ↦ a)
  · rintro s ⟨φ, rfl⟩ t ⟨ψ, rfl⟩
    use φ ⊓ ψ
    ext t
    simp
    simp_rw[← SetLike.mem_coe, t.isMaximal.mem_iff_models (φ ⊓ ψ), t.isMaximal.mem_iff_models φ,
            t.isMaximal.mem_iff_models ψ, Theory.models_sentence_iff]
    constructor
    · rintro ⟨a, b⟩ M
      exact Formula.realize_inf.2 ⟨a M, b M⟩
    · intro a
      rw [←forall_and]
      intro M
      exact Formula.realize_inf.1 (a M)

lemma basic_open_compl {n : ℕ} (T : L.Theory) (φ : L[[Fin n]].Sentence) :
                       BasicOpen (T := T) φ.not = (BasicOpen φ)ᶜ :=
                       by ext p ; exact p.not_mem_iff φ

instance (n : ℕ) : TopologicalSpace (T.CompleteType (Fin n)) := generateFrom basis

instance {n : ℕ} : T0Space (T.CompleteType (Fin n)) := by
  rw [t0Space_iff_inseparable]
  intro x y a
  apply SetLike.ext
  intro φ
  replace h := inseparable_iff_forall_isOpen.1 a
  have b : IsOpen (X := (T.CompleteType (Fin n))) (BasicOpen φ) := by
    apply TopologicalSpace.GenerateOpen.basic
    use φ ; trivial
  exact h (BasicOpen φ) b

instance {n : ℕ} : TotallySeparatedSpace (T.CompleteType (Fin n)) := by
  apply totallySeparatedSpace_of_t0_of_basis_clopen
  have a := isTopologicalBasis_of_subbasis_of_finiteInter
            (α := T.CompleteType (Fin n)) (s := basis) (by trivial) finite_inter
  apply IsTopologicalBasis.of_isOpen_of_subset
  · intro _ h ; exact h.2
  · exact a
  · intro s ⟨φ, b⟩
    constructor
    · have h : IsOpen sᶜ := by
        replace b : s = BasicOpen φ := b
        rw[b, ←basic_open_compl]
        apply TopologicalSpace.GenerateOpen.basic
        exact ⟨φ.not, by trivial⟩
      rw[←compl_compl s]
      exact isClosed_compl_iff.2 h
    · apply TopologicalSpace.GenerateOpen.basic ; use φ



instance {n : ℕ} : T2Space (T.CompleteType (Fin n)) := TotallySeparatedSpace.t2Space

instance {n : ℕ} : CompactSpace (T.CompleteType (Fin n)) := by
  constructor
  rw[isCompact_iff_ultrafilter_le_nhds]
  intros F _
  let x : L[[Fin n]].Theory := {φ | BasicOpen φ ∈ F}
  have a : (L.lhomWithConstants (Fin n)).onTheory T ⊆ x := by
    intro φ a
    have b : BasicOpen (T := T) φ = Set.univ := by
      ext y
      simp [BasicOpen, Set.mem_setOf_eq, Set.mem_univ, iff_true]
      exact y.subset a
    rw[Set.mem_setOf_eq, b]
    exact Filter.univ_mem
  have b : Theory.IsMaximal x := by
    rw[Theory.IsMaximal]
    constructor
    · rw[Theory.isSatisfiable_iff_isFinitelySatisfiable, Theory.IsFinitelySatisfiable]
      intro φᵢ a
      have b : ∀ φ ∈ φᵢ, BasicOpen φ ∈ F.toFilter := by
        intro _ b
        exact a b
      rw[←Filter.biInter_finset_mem φᵢ] at b
      obtain ⟨y, c⟩ := F.neBot.nonempty_of_mem b
      have d : SetLike.coe φᵢ ⊆ y.toTheory := by rwa[Set.mem_iInter₂] at c
      exact Theory.IsSatisfiable.mono y.isMaximal'.1 d
    · intro φ
      rcases Ultrafilter.mem_or_compl_mem F (BasicOpen φ) with  a | b
      · exact Or.inl a
      · rw[←basic_open_compl T φ] at b
        exact Or.inr b
  let p : T.CompleteType (Fin n) := ⟨x, a, b⟩
  use p
  constructor
  · trivial
  · rw [nhds_generateFrom]
    apply le_iInf₂
    intro _ a
    rw [Filter.le_principal_iff]
    obtain ⟨_, rfl⟩ := a.2
    exact a.1

instance {n : ℕ} : BaireSpace (T.CompleteType (Fin n)) := BaireSpace.of_t2Space_locallyCompactSpace

end TypeSpace

namespace Canvas

/-
Plan:
We are working in the context of a language L and theory T

Take the meagre set A and split it into its closed countable nowhere dense sets A = ∪ Fᵢ
Note that Uᵢ := (Fᵢ)ᶜ is open and dense
By Baire Category, G := ∩ Uᵢ is Gδ and dense
Also, define Vₙ := U₁ ∩ … ∩ Uₙ (this is open and dense)
We also know that G avoids every type in A by construction


We then define a new language L' = L ∪ {cᵢ : i ∈ ℕ}
We will have formulas that are free in n variables in L'
This is technically going to be implemented as L'[[Fin n]]

-/

variable {L : FirstOrder.Language} {T : L.Theory} {n : ℕ}

def countable_language (L : Language) : Prop :=
          ∀ n : ℕ, Countable (L.Functions n) ∧ Countable (L.Relations n)

def omits_type (M : T.ModelType) (p : T.CompleteType (Fin n)) : Prop := by
  have h := T.realizedTypes (α := Fin n) M
  #check T.realizedTypes (α := Fin n) M
  exact p ∉ h

abbrev ExpandedLanguage := L[[ℕ]]
local notation "L'" => @ExpandedLanguage L
def toL' : L →ᴸ L' := L.lhomWithConstants ℕ
local notation "T'" => toL'.onTheory T

variable (φ : (L').Sentence)

def henkin_set (φ : L'[[Fin n]].Sentence) : Set ((T').CompleteType (Fin n)) :=
  have φe : L'[[Fin n]].Sentence := by
    have φ' := BoundedFormula.constantsVarsEquiv φ
    have φ' := BoundedFormula.relabelEquiv (Equiv.sumComm (Fin n) Empty) φ'
    have φ' := Formula.iExs (Fin n) φ'
    exact LHom.onSentence (lhomWithConstants L' (Fin n)) φ'
  have φc : (Fin n → ℕ) → L'[[Fin n]].Sentence := by
    intro c
    have φ' := BoundedFormula.constantsVarsEquiv φ
    have φ' := BoundedFormula.relabelEquiv (Equiv.sumEmpty (Fin n) Empty) φ'
    have φ' := BoundedFormula.subst φ' (fun a ↦ Constants.term ((L).con (c a))) (β := Empty)
    exact LHom.onSentence (lhomWithConstants L' (Fin n)) φ'
  {p : (T').CompleteType (Fin n) | φe ∈ p → ∃ c : (Fin n → ℕ), (φc c) ∈ p}

def dense : ∀ φ : L'[[Fin n]].Sentence, Dense (X := (T').CompleteType (Fin n)) (henkin_set φ) := by
  intros φ x
  apply mem_closure_iff.mpr
  intro o ho hx
  dsimp[IsOpen] at ho
  #check IsTopologicalBasis.dense_iff
  sorry


theorem Omitting_Types_Theorem (c : countable_language L) (s : Set (T.CompleteType (Fin n)))
                               (p : IsMeagre s) : ∃ M : T.ModelType, ∀ x ∈ s, omits_type M x := by
  sorry

end Canvas
