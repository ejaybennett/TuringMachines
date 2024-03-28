import Mathlib.Computability.TuringMachine

open Turing
open Turing.TM0

inductive my_states : Type
| a : my_states
| b : my_states
| c : my_states
instance my_states.inhabited : Inhabited my_states :=
  ⟨my_states.a⟩

inductive my_chars : Type
| C : my_chars
| D : my_chars
instance my_chars.inhabited : Inhabited my_chars :=
  ⟨my_chars.C⟩

open my_chars
open my_states

local notation "StmtS" => Stmt my_chars
local notation "CfgS" => Cfg my_chars my_states
local notation "MachineS" => Machine my_chars my_states
def my_machine  (state : my_states) (char : my_chars) : Option (my_states × (Stmt my_chars)) :=
  match state with
  | c => none
  | a => (match char with | C => some ((c, Stmt.move Dir.left)) | D => some ((c, Stmt.move Dir.left)))
  | b => (match char with | C => some ((c, Stmt.write D)) | D => some ((c, Stmt.move Dir.left)))


def my_cfg : CfgS := init [C, D]

def next_state := step my_machine my_cfg

open Nat
def step_n  (M : MachineS) (cfg1: Option CfgS) (n : Nat)  : Option CfgS :=
match cfg1 with
| some cfg => (
  match n with
  | zero => cfg1
  | (succ x) => step_n M (step M cfg) x
)
| none => none

theorem my_machine_terminates : ∃ n , step_n my_machine (some my_cfg) n = none := by
