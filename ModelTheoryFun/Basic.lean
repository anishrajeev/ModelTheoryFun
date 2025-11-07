import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Semantics

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
def conjunction (x : language.Sentence) (y : language.Sentence) : language.Sentence := ∼ (x ⟹ ∼ y)
def disjunction (x : language.Sentence) (y : language.Sentence) : language.Sentence := (∼ x) ⟹ y

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

theorem ratAntiReflexive : antireflexive.Realize Rat := by
  dsimp [Sentence.Realize, antireflexive, Formula.Realize]
  intros x xltx
  dsimp [BoundedFormula.Realize]
  dsimp [BoundedFormula.Realize, Fin.snoc] at xltx
  unfold Structure.RelMap at xltx
  dsimp [instStructureLanguageRat] at xltx
  exact Rat.lt_irrefl xltx


end OrderedLang
