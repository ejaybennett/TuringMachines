
import Mathlib.Computability.TuringMachine

open Turing
open Turing.TM0

inductive my_states : Type 
| s0 : my_states
| s1 : my_states

instance my_states.inhabited : Inhabited my_states :=  ⟨my_states.s0⟩



    inductive my_chars : Type
| c0 : my_chars
| c1 : my_chars
| c2 : my_chars
| c3 : my_chars
instance my_chars.inhabited : Inhabited my_chars :=  ⟨my_chars.c3⟩

open my_chars
open my_states

def my_machine  (state : my_states) (char : my_chars) : Option (my_states × (Stmt my_chars)) :=
  match state with
  | s0 => (match char with | c0 => some ((s1, Stmt.move Dir.right)) | c1 => some ((s1, Stmt.move Dir.right)) | c2 => some ((s0, Stmt.move Dir.left)) | c3 => some ((s0, Stmt.move Dir.left)) )
  | s1 => none



def my_cfg : Cfg my_chars my_states := init [c0, c2, c2, c0]


open Nat
def step_n  (M : (Machine my_chars my_states)) (cfg1: Option (Cfg my_chars my_states)) (n : Nat)  : Option (Cfg my_chars my_states) :=
match cfg1 with
| some cfg => (
  match n with
  | zero => cfg1
  | (succ x) => step_n M (step M cfg) x
)
| none => none
