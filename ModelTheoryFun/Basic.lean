import Mathlib.ModelTheory.Basic

-- Lets define some cool models just for fun!
open FirstOrder

-- 1) Language with an ≤ symbol and thats it
namespace OrderedLang

inductive fn_symbols : ℕ → Type
  | zero : fn_symbols 0
  | one : fn_symbols 0
  
inductive rel_symbols : ℕ → Type
  | leq : rel_symbols 2

def language : Language := Language.mk fn_symbols rel_symbols
def natStructure : language.Structure ℕ where
  funMap {n} f v :=
  match f with
    | fn_symbols.zero => 0
    | fn_symbols.one => 1
  RelMap {n} r v :=
    match r with
    | rel_symbols.leq =>
      have x := v (Fin.mk 0 (by simp))
      have y := v (Fin.mk 1 (by simp))
      x ≤ y

def rationalStructure : language.Structure Rat where
  funMap {n} f v :=
  match f with
    | fn_symbols.zero => 0.0
    | fn_symbols.one => 1.0
  RelMap {n} r v : Prop :=
    match r with
    | rel_symbols.leq =>
      have x := v (Fin.mk 0 (by simp))
      have y := v (Fin.mk 1 (by simp))
      x ≤ y

end OrderedLang
