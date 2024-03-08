(** Coq configuration for system-semantic-coq (not meant to leak to clients).

Any downstream project should have its own options file as this might change at
any time without notice.

All SSC files should Import (but not Export) this. *)
(* Everything here should be [#[export] Set], which means when this
file is *imported*, the option will only apply on the import site
but not transitively. *)

(** Force [Proof.] commands in section to just be [Proof using.]. This means the
    code must specify any section variables, and that most lemmas that don't
    need any extra section variable can just start with [Proof.] and not
    [Proof using.] *)
#[export] Set Default Proof Using "".

(** Enforces that every tactic is executed with a single focused goal, meaning
    that bullets and curly braces must be used to structure the proof. *)
#[export] Set Default Goal Selector "!".

(** Improve the behavior of unification for rewriting tactics, at the cost of
    making rewriting a bit slower *)
#[export] Set Keyed Unification.

(** Use the if _ is _ notation in this project, but do not force users to use it *)
Export IfNotations.

(* TODO automatically check that all file in the project import this file.
   This might be done with a text checker that there exists a
   [Require Import Options.] or [Require Import SSCCommon.Options] *)
