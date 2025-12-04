import Mathlib.Data.Rat.Cast.Order
import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics
import Mathlib.Tactic.Linarith
import Mathlib.ModelTheory.Satisfiability


import Mathlib.ModelTheory.Types
import Mathlib.Topology.Basic
import Mathlib.Order.Filter.Ultrafilter.Defs
import Mathlib.Topology.Order
import Mathlib.Topology.Separation.Hausdorff
import Mathlib.Topology.Order

-- import Mathlib.Data.Rat.Order

-- Lets define some cool models and theories
open FirstOrder
open FirstOrder.Language
open FirstOrder.Language.BoundedFormula

-- Language with an ≤ and ≡ symbol, and 2 constants and thats it
namespace OrderedLang

inductive fn_symbols : ℕ → Type
  | zero : fn_symbols 0
  | one : fn_symbols 0
inductive rel_symbols : ℕ → Type
  | lt : rel_symbols 2
def language : Language := Language.mk fn_symbols rel_symbols

-- Natural Numbers model
def natStructure : language.Structure ℕ where
  funMap {n} f v :=
  match f with
    | fn_symbols.zero => 0
    | fn_symbols.one => 1
  RelMap {n} r v :=
    match r with
    | rel_symbols.lt =>
      have x := v (Fin.mk 0 (by simp))
      have y := v (Fin.mk 1 (by simp))
      x < y

-- Rational Numbers Model
def rationalStructure : language.Structure Rat where
  funMap {n} f v :=
  match f with
    | fn_symbols.zero => 0.0
    | fn_symbols.one => 1.0
  RelMap {n} r v : Prop :=
    match r with
    | rel_symbols.lt =>
      have x := v (Fin.mk 0 (by simp))
      have y := v (Fin.mk 1 (by simp))
      x < y

/- I'm bored now; I want to define a theory now. What about defining DLO,
and showing rationalStructure models it?
-/

/-
Antireflexivity: ∀ x. ¬ (x < x)
Linear order: ∀ x. ∀ y. (x < y) ∨ (y < x) ∨ (x ≡ y)
Transitivity: ∀ x. ∀ y. ∀ z. ((x < y) ∧ (y < z)) → (x < z)
No endpoint: ∀ x. ∃ y. x < y
No endpoint: ∀ x. ∃ y. y < x
Density: ∀ x. ∀ y. x < y → (∃ z. (x < z) ∧ (z < y))
-/

def antireflexive : language.Sentence :=
all (imp (rel rel_symbols.lt (fun x => var (Sum.inr (Fin.mk 0 (by simp))))) falsum)
def linear_order : language.Sentence :=
  ∀' ∀' (∼ (rel rel_symbols.lt (fun x => var (Sum.inr x))) ⟹
        (∼ (rel rel_symbols.lt
            (fun x =>
                match x with
                | ⟨0, _⟩ => var (Sum.inr ⟨1, by simp⟩)
                | ⟨1, _⟩ => var (Sum.inr ⟨0, by simp⟩))) ⟹
          (var (Sum.inr ⟨0, by simp⟩) =' var (Sum.inr ⟨1, by simp⟩))))
def transitivity : language.Sentence :=
  ∀' ∀' ∀' (∼ ((rel rel_symbols.lt
                  (fun x =>
                    match x with
                    | ⟨0, _⟩ => var (Sum.inr ⟨0, by simp⟩)
                    | ⟨1, _⟩ => var (Sum.inr ⟨1, by simp⟩))) ⟹
              (∼ (rel rel_symbols.lt
                  (fun x =>
                    match x with
                    | ⟨0, _⟩ => var (Sum.inr ⟨1, by simp⟩)
                    | ⟨1, _⟩ => var (Sum.inr ⟨2, by simp⟩))))) ⟹
      (rel rel_symbols.lt
        (fun x =>
          match x with
          | ⟨0, _⟩ => var (Sum.inr ⟨0, by simp⟩)
          | ⟨1, _⟩ => var (Sum.inr ⟨2, by simp⟩))))
def no_endpoint_1 : language.Sentence :=
  ∀' ∃' rel rel_symbols.lt (fun x => var (Sum.inr x))
def no_endpoint_2 : language.Sentence :=
  ∀' ∃' rel rel_symbols.lt
            (fun x =>
              match x with
              | ⟨0, _⟩ => var (Sum.inr ⟨1, by simp⟩)
              | ⟨1, _⟩ => var (Sum.inr ⟨0, by simp⟩))
def density : language.Sentence :=
  ∀' ∀' (rel rel_symbols.lt (fun x => var (Sum.inr x)) ⟹
  (∃' ∼ ((rel rel_symbols.lt (fun x => match x with
                                      | 0 => var (Sum.inr 0)
                                      | 1 => var (Sum.inr 2))) ⟹
      ∼ (rel rel_symbols.lt (fun x => match x with
                                      | 0 => var (Sum.inr 2)
                                      | 1 => var (Sum.inr 1))))))

def DLO_Theory : language.Theory := {antireflexive,
                                     linear_order,
                                     transitivity,
                                     no_endpoint_1,
                                     no_endpoint_2,
                                     density}

instance : language.Structure Rat := rationalStructure
instance : language.Structure ℕ := natStructure

theorem ratAntireflexive : Rat ⊨ antireflexive := by
  dsimp [Sentence.Realize, antireflexive, Formula.Realize]
  intros x xltx
  dsimp [BoundedFormula.Realize]
  dsimp [BoundedFormula.Realize, Fin.snoc] at xltx
  unfold Structure.RelMap at xltx
  dsimp [instStructureLanguageRat] at xltx
  exact Rat.lt_irrefl xltx
theorem ratLinearOrder : Rat ⊨ linear_order := by
  rw [linear_order]
  rw [Sentence.Realize]
  rw [Formula.Realize]
  intro x y
  rw [realize_imp]
  intro h₁
  rw [realize_imp]
  intro h₂
  rw [realize_bdEqual]
  rw [realize_not] at h₁ h₂
  have hxy : ¬ (x < y) := h₁
  have hyx : ¬ (y < x) := h₂
  cases lt_trichotomy x y with
  | inl hc => exact (False.elim (hxy hc))
  | inr smallhypothesis =>
    cases smallhypothesis with
    | inl ans => exact ans
    | inr hc => exact (False.elim (hyx hc))
theorem ratTransitivity : Rat ⊨ transitivity := by
  rw [transitivity]
  rw [Sentence.Realize]
  intro x y z
  rw [realize_imp]
  intro h
  rw [realize_not] at h
  rw [realize_imp] at h
  simp at h
  cases h with
  |intro hx hy =>
  have hxy : x < y := hx
  have hyz : y < z := hy
  exact lt_trans hxy hyz
theorem ratNoUpperBound : Rat ⊨ no_endpoint_1 := by
  simp [no_endpoint_1, Sentence.Realize, Formula.Realize]
  intros x
  have pf : x + 1 > x := by linarith
  exact ⟨x + 1, pf⟩
theorem ratNoLowerBound : Rat ⊨ no_endpoint_2 := by
  simp [no_endpoint_2, Sentence.Realize, Formula.Realize]
  intros x
  have pf : x - 1 < x := by linarith
  exact ⟨x - 1, pf⟩
theorem ratDensity : Rat ⊨ density := by
  simp [density, Sentence.Realize, Formula.Realize]
  intro x y xy
  have h : x < y := xy
  have pf : x < (x + y)/2 ∧ (x + y)/2 < y := by
    apply And.intro
    case left => linarith
    case right => linarith
  exact ⟨(x + y)/2, pf⟩

theorem ratIsDLO : Theory.Model Rat DLO_Theory := by
  simp [DLO_Theory]
  exact ⟨ratAntireflexive, ratLinearOrder, ratTransitivity,
        ratNoUpperBound, ratNoLowerBound, ratDensity⟩

end OrderedLang

namespace StoneSpace

variable {L : FirstOrder.Language} {T : L.Theory}

def basis {n : ℕ} : Set (Set (T.CompleteType (Fin n))) := {X | ∃ φ, X = {p | φ ∈ p}}

instance (n : ℕ) : TopologicalSpace (T.CompleteType (Fin n)) :=
    TopologicalSpace.generateFrom (basis)

/- variable (n : ℕ)
 variable (x y : T.CompleteType (Fin n)) -/

lemma construct_basic_sets {n : ℕ} (x y : T.CompleteType (Fin n))
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
    exact construct_basic_sets x y φ φ_x_y
  · rw [Set.subset_def] at y_nsub_x
    push_neg at y_nsub_x
    rcases y_nsub_x with ⟨φ, φ_x_y⟩
    have swapped : ∼φ ∈ x ∧ ∼φ ∉ y := by
      constructor
      · exact (x.not_mem_iff φ).2 φ_x_y.2
      · intro nφy
        exact (y.not_mem_iff φ).1 nφy φ_x_y.1
    exact construct_basic_sets x y ∼φ swapped

end StoneSpace
