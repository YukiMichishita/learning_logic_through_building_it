inductive Atom where
  | mk : (name: String) -> Atom
open Atom
inductive Wff where
  | atom : Atom -> Wff
  | not_ : Wff -> Wff
  | and_ : Wff -> Wff -> Wff
  | or_ : Wff -> Wff -> Wff
  | impl : Wff -> Wff -> Wff
open Wff

def p : Wff := atom (mk "P")
def q : Wff := atom (mk "Q")
def p_and__q : Wff := and_ p q

inductive TruthVal where
  | true_
  | false_
open TruthVal

def assignment : ((String -> TruthVal) -> Atom -> TruthVal) :=
  fun eval : String -> TruthVal =>
  fun a : Atom =>
    match a with
     | Atom.mk s => eval s

def eval_1 : (String -> TruthVal)
     | "P" => true_
     | "Q" => false_
     | _ => false_

#check assignment eval_1
#eval assignment eval_1 (mk "P")


def eval : (Atom -> TruthVal) -> (Wff) ->  TruthVal:=
  fun (valuation : Atom -> TruthVal) (p : Wff) =>
    match p with
      | atom s => valuation s
      | not_ pp => match eval valuation pp with
        | true_ => .false_
        | .false_ => .true_
      | and_ p1 p2 => match eval valuation p1 with
        | .true_ => eval valuation p2
        | .false_ => .false_
      | or_ p1 p2 => match eval valuation p1 with
        | .true_ => .true_
        | .false_ => eval valuation p2
      | impl p1 p2 => match eval valuation p1 with
        | .true_ => eval valuation p2
        | .false_ => .true_

#eval eval (assignment eval_1) p_and__q
