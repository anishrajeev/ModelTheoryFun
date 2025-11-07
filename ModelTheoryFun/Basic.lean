import Mathlib.Data.Rat.Cast.Order
import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics
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
and showing rationalStructure models it but not Natural?
-/

/-
Antireflexivity: ∀ x. ¬ (x < x)
Linear order: ∀ x. ∀ y. (x < y) ∨ (y < x) ∨ (x ≡ y)
Transitivity: ∀ x. ∀ y. ∀ z. ((x < y) ∧ (y < z)) → (x < z)
No endpoint: ∀ x. ∃ y. x < y
No endpoint: ∀ x. ∃ y. y < x
Density: ∀ x. ∀ y. ∃ z. (x < z) ∧ (z < y)
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
∀' ∀' ∃'
  ∼ ((rel rel_symbols.lt
          (fun x =>
            match x with
            | ⟨0, _⟩ => var (Sum.inr ⟨0, by simp⟩)
            | ⟨1, _⟩ => var (Sum.inr ⟨2, by simp⟩))) ⟹
  ∼ ((rel rel_symbols.lt
          (fun x =>
            match x with
            | ⟨0, _⟩ => var (Sum.inr ⟨2, by simp⟩)
            | ⟨1, _⟩ => var (Sum.inr ⟨1, by simp⟩)))))

def DLO_Theory : language.Theory := {antireflexive,
                                     linear_order,
                                     transitivity,
                                     no_endpoint_1,
                                     no_endpoint_2,
                                     density}

instance : language.Structure Rat := rationalStructure
instance : language.Structure ℕ := natStructure

theorem ratantiReflexive : antireflexive.Realize Rat := by
  dsimp [Sentence.Realize, antireflexive, Formula.Realize]
  intros x xltx
  dsimp [BoundedFormula.Realize]
  dsimp [BoundedFormula.Realize, Fin.snoc] at xltx
  unfold Structure.RelMap at xltx
  dsimp [instStructureLanguageRat] at xltx
  exact Rat.lt_irrefl xltx
theorem ratTransitivity : transitivity.Realize Rat := by
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
theorem ratLinearOrder : linear_order.Realize Rat := by
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

end OrderedLang
