/-
Copyright (c) 2026 Ben Hamlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import VCVio.Interaction.TwoParty.Strategy
import VCVio.OracleComp.ProbCompLift
import VCVio.EvalDist.Defs.Instances

/-!
# Message Transmission Protocols

A two-party interactive protocol in which a sender `S` transmits a message
`m ∈ M` to a receiver `R`, formalized in the style of Dodis and Fiore (Sec. 2.1
of *Unilaterally-Authenticated Key Exchange*).

The protocol shape is described by a list of `LinearStep`s, each pairing a
move type with the role of the speaker for that move. Each step has a
statically-known move type that does not depend on prior moves; this
non-dependent ("linear") shape is what every concrete protocol of interest
in the Dodis–Fiore framework actually uses, and it keeps the per-round move
types statically typed.

The honest sender / receiver are described by directly-list-recursive
strategy types `SenderProgram` / `ReceiverProgram`. Each of those *dispatches
on `step.speaker` inside its definition*, so destructuring a step list and
then matching on the head step's speaker refines the strategy's type along
the match branches without requiring transports through any role-decoration
layer. This is what makes the iCCA / iCMA `advanceSession` machinery
tractable.

This module defines:

* `LinearStep` — one round, paired move type and speaker.
* `LinearStep.linearSpec` / `linearRoles` — derive a `Spec.{0}` /
  `RoleDecoration` view from a step list (kept around as utilities for
  callers that want a `Spec`-flavored view; not used in the protocol's
  core shape).
* `SenderProgram` / `ReceiverProgram` — list-recursive strategy types whose
  shape dispatches on `step.speaker` at each step.
* `MessageTransmissionProtocol m M SendK RecvK` — the structural notion
  `(Setup, S, R)`, parameterized by `steps : List LinearStep`.
* `exec` — run a sender program against a receiver program of the same
  step list, returning the receiver's terminal output. The formal
  counterpart of the paper's `⟨S, R⟩` notation; left polymorphic in the
  receiver's terminal type so the same runner serves honest execution
  (`Y = Option M`) and the iCCA challenge (`Y = Bool`).
* `PerfectlyCorrect` — Definition 1 in the perfect-correctness variant,
  matching the convention used by `SymmEncAlg.Complete` and
  `AsymmEncAlg.PerfectlyCorrect`.

Security properties (matching transcripts, ping-pong adversaries, iCCA / iCMA
security) are deferred to sibling modules.
-/

namespace Interaction

open Spec

/-- One round of a (linear) message transmission protocol: a move type plus
the role of the party who speaks. The non-dependent shape (move types fixed
in advance, not chosen as a function of prior moves) is what all concrete
protocols of interest in this framework use. -/
structure LinearStep : Type 1 where
  moveType : Type 0
  speaker : Role

namespace LinearStep

/-- The linearized `Spec.{0}` from a list of steps: each step contributes one
non-branching node whose move type is the step's `moveType`. Kept as a
utility for callers that want a `Spec`-flavored view; the
`MessageTransmissionProtocol` shape itself doesn't go through `Spec`. -/
def linearSpec : List LinearStep → Spec.{0}
  | [] => .done
  | step :: rest => .node step.moveType (fun _ => linearSpec rest)

/-- The role decoration that pairs with `linearSpec`: each round's role is
the corresponding `step.speaker`. -/
def linearRoles : (steps : List LinearStep) → RoleDecoration (linearSpec steps)
  | [] => ⟨⟩
  | step :: rest => ⟨step.speaker, fun _ => linearRoles rest⟩

end LinearStep

/-- The sender's strategy along a list of `LinearStep`s, with terminal
output type `X`. At each step the type dispatches on `step.speaker`: the
sender either *produces* the move (at sender steps) or *consumes* the
receiver-supplied move (at receiver steps). At `[]` the sender carries the
terminal value of type `X` (`Unit` for the honest sender; possibly a
post-execution state for an adversary). -/
def SenderProgram (m : Type → Type) (X : Type) : List LinearStep → Type
  | [] => X
  | step :: rest =>
      match step.speaker with
      | .sender => m (step.moveType × SenderProgram m X rest)
      | .receiver => step.moveType → m (SenderProgram m X rest)

/-- The receiver's strategy along a list of `LinearStep`s, with terminal
output type `Y`. Mirrors `SenderProgram` with the role-dispatch flipped. At
`[]` the receiver carries its terminal value of type `Y` (`Option M` for
the honest receiver; `Bool` for an iCCA adversary's guess). -/
def ReceiverProgram (m : Type → Type) (Y : Type) : List LinearStep → Type
  | [] => Y
  | step :: rest =>
      match step.speaker with
      | .sender => step.moveType → m (ReceiverProgram m Y rest)
      | .receiver => m (step.moveType × ReceiverProgram m Y rest)

/-- A message transmission protocol in the sense of Dodis–Fiore (Sec. 2.1):
a possibly-interactive two-party protocol with sender keys in `SendK`,
receiver keys in `RecvK`, and message space `M`.

* `steps` describes the per-round move types and speakers.
* `setup` produces a fresh `(sendk, recvk)` pair.
* `sender sendk msg` is the honest sender's `SenderProgram` on message
  `msg`.
* `receiver recvk` is the honest receiver's `ReceiverProgram`; its terminal
  output is `some msg` on accept, `none` on reject.

WLOG the sender speaks last (Dodis–Fiore convention). This is not enforced
in the structure itself; concrete protocols should pick a step list whose
last entry has `.sender`. -/
@[ext]
structure MessageTransmissionProtocol
    (m : Type → Type) [Monad m] (M SendK RecvK : Type) : Type 1 where
  steps : List LinearStep
  setup : m (SendK × RecvK)
  sender : SendK → M → SenderProgram m Unit steps
  receiver : RecvK → ReceiverProgram m (Option M) steps

namespace MessageTransmissionProtocol

variable {m : Type → Type} [Monad m] {M SendK RecvK : Type}

/-! ## Honest execution -/

/-- Run a `SenderProgram` (with `Unit` terminal) against a `ReceiverProgram`
with terminal type `Y`, returning the receiver's terminal output. The
formal counterpart of the paper's `⟨S, R⟩` notation: instantiated at the
honest pair `(mtp.sender sendk msg, mtp.receiver recvk)` it computes the
paper's `m' = ⟨S(sendk, m), R(recvk)⟩` (with `Y = Option M`); instantiated
at an honest sender against an iCCA adversary it computes the adversary's
`Bool` guess.

The recursion matches on each step's `LinearStep` constructor pattern
(`⟨_, .sender⟩` or `⟨_, .receiver⟩`), so the role becomes a literal
constructor and the program types reduce by `rfl`. -/
def exec {Y : Type} : (steps : List LinearStep) →
    SenderProgram m Unit steps → ReceiverProgram m Y steps → m Y
  | [], _, recv => pure recv
  | ⟨_, .sender⟩ :: rest, send, recv => do
      let ⟨x, sNext⟩ ← send
      let rNext ← recv x
      exec rest sNext rNext
  | ⟨_, .receiver⟩ :: rest, send, recv => do
      let ⟨x, rNext⟩ ← recv
      let sNext ← send x
      exec rest sNext rNext

/-! ## Correctness -/

section Correct

variable [DecidableEq M]

/-- Correctness experiment: sample fresh keys, run the honest sender on `msg`
against the honest receiver, and return `true` iff the receiver's output is
`some msg`. -/
def CorrectExp (mtp : MessageTransmissionProtocol m M SendK RecvK) (msg : M) :
    m Bool := do
  let ⟨sendk, recvk⟩ ← mtp.setup
  let out ← exec mtp.steps (mtp.sender sendk msg) (mtp.receiver recvk)
  return decide (out = some msg)

/-- A message transmission protocol is *perfectly correct* under the given
probabilistic runtime when, for every message, the receiver outputs that
message with probability `1` in an honest run.

Definition 1 of Dodis–Fiore allows a negligible failure probability; the
perfect variant defined here matches the existing convention in this library
(`SymmEncAlg.Complete`, `AsymmEncAlg.PerfectlyCorrect`). Statistical or
asymptotic correctness can be layered on top later. -/
def PerfectlyCorrect (mtp : MessageTransmissionProtocol m M SendK RecvK)
    (runtime : ProbCompRuntime m) : Prop :=
  ∀ (msg : M), Pr[= true | runtime.evalDist (mtp.CorrectExp msg)] = 1

end Correct

end MessageTransmissionProtocol

end Interaction
