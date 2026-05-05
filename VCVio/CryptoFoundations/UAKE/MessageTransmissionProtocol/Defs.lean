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
types statically typed (necessary for stating the iCCA / iCMA security games
without universe-inflating heterogeneous-move tricks).

The sender / receiver fields of `MessageTransmissionProtocol` are role-
decorated strategies over the linearized `Spec.{0}` derived from the steps,
so an honest run is just `Spec.Strategy.runWithRoles`.

This module defines:

* `LinearStep` — one round, paired move type and speaker.
* `LinearStep.linearSpec` / `linearRoles` — derive the underlying `Spec.{0}`
  and `RoleDecoration` from a step list.
* `MessageTransmissionProtocol m M SendK RecvK` — the structural notion
  `(Setup, S, R)`, parameterized by `steps : List LinearStep`.
* `MessageTransmissionProtocol.spec` / `.roles` — convenience accessors that
  compute the spec / role decoration from the step list.
* `exec` / `execOutput` — running the honest sender against the honest
  receiver, producing the transcript-plus-output pair (or just the output).
  This is the formal counterpart of the paper's `⟨S(sendk, m), R(recvk)⟩ = m'`
  notation.
* `PerfectlyCorrect` — Definition 1 in the perfect-correctness variant,
  matching the convention used by `SymmEncAlg.Complete` and
  `AsymmEncAlg.PerfectlyCorrect`.

Security properties (matching transcripts, ping-pong adversaries, iCCA / iCMA
security) are deliberately deferred to sibling modules.
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
non-branching node whose move type is the step's `moveType`. -/
def linearSpec : List LinearStep → Spec.{0}
  | [] => .done
  | step :: rest => .node step.moveType (fun _ => linearSpec rest)

/-- The role decoration that pairs with `linearSpec`: each round's role is
the corresponding `step.speaker`. -/
def linearRoles : (steps : List LinearStep) → RoleDecoration (linearSpec steps)
  | [] => ⟨⟩
  | step :: rest => ⟨step.speaker, fun _ => linearRoles rest⟩

end LinearStep

/-- A message transmission protocol in the sense of Dodis–Fiore (Sec. 2.1):
a possibly-interactive two-party protocol with sender keys in `SendK`,
receiver keys in `RecvK`, and message space `M`.

* `steps` describes the per-round move types and speakers.
* `setup` produces a fresh `(sendk, recvk)` pair.
* `sender sendk msg` is the honest sender's role-decorated strategy on
  message `msg`; the sender has no terminal output (`Unit`).
* `receiver recvk` is the honest receiver's counterpart strategy; its output
  is `some msg` on accept, `none` on reject.

WLOG the sender speaks last (Dodis–Fiore convention). This is not enforced
in the structure itself; concrete protocols should pick a step list whose
last entry has `.sender`. -/
@[ext]
structure MessageTransmissionProtocol
    (m : Type → Type) [Monad m] (M SendK RecvK : Type) : Type 1 where
  steps : List LinearStep
  setup : m (SendK × RecvK)
  sender : SendK → M →
    Strategy.withRoles m (LinearStep.linearSpec steps)
      (LinearStep.linearRoles steps) (fun _ => Unit)
  receiver : RecvK →
    Counterpart m (LinearStep.linearSpec steps)
      (LinearStep.linearRoles steps) (fun _ => Option M)

namespace MessageTransmissionProtocol

variable {m : Type → Type} [Monad m] {M SendK RecvK : Type}

/-! ## Spec / role accessors -/

/-- The interaction `Spec` derived from the protocol's step list. -/
abbrev spec (mtp : MessageTransmissionProtocol m M SendK RecvK) : Spec.{0} :=
  LinearStep.linearSpec mtp.steps

/-- The role decoration derived from the protocol's step list. -/
abbrev roles (mtp : MessageTransmissionProtocol m M SendK RecvK) :
    RoleDecoration mtp.spec :=
  LinearStep.linearRoles mtp.steps

/-! ## Honest execution -/

/-- Execute the honest sender on message `msg` against the honest receiver,
returning the joint transcript paired with the receiver's output. The sender's
trivial `Unit` output is dropped.

This is the formal counterpart of the paper's `⟨S(sendk, m), R(recvk)⟩ = m'`
notation: `m'` is the second component of the returned sigma. -/
def exec (mtp : MessageTransmissionProtocol m M SendK RecvK)
    (sendk : SendK) (recvk : RecvK) (msg : M) :
    m ((_ : Transcript mtp.spec) × Option M) :=
  (fun (z : (_ : Transcript mtp.spec) × Unit × Option M) => ⟨z.1, z.2.2⟩) <$>
    Strategy.runWithRoles mtp.spec mtp.roles
      (mtp.sender sendk msg) (mtp.receiver recvk)

/-- The receiver's output of an honest run, with the transcript discarded. -/
def execOutput (mtp : MessageTransmissionProtocol m M SendK RecvK)
    (sendk : SendK) (recvk : RecvK) (msg : M) : m (Option M) :=
  Sigma.snd <$> mtp.exec sendk recvk msg

/-! ## Correctness -/

section Correct

variable [DecidableEq M]

/-- Correctness experiment: sample fresh keys, run the honest sender on `msg`
against the honest receiver, and return `true` iff the receiver's output is
`some msg`. -/
def CorrectExp (mtp : MessageTransmissionProtocol m M SendK RecvK) (msg : M) :
    m Bool := do
  let ⟨sendk, recvk⟩ ← mtp.setup
  let out ← mtp.execOutput sendk recvk msg
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
