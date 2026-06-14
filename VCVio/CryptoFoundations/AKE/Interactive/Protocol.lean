/-
Copyright (c) 2026 Ben Hamlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.CryptoFoundations.AsymmEncAlg.Defs
import PolyFun.Interaction.TwoParty.Strategy
import PolyFun.Interaction.TwoParty.Role
import PolyFun.Interaction.TwoParty.Decoration

/-!
# Interactive message-transmission protocols

This file models the *message transmission protocol* from DF'17
("Unilaterally-Authenticated Key Exchange", Definition 1).
-/

open OracleSpec OracleComp
open Interaction Interaction.TwoParty

universe v

/-- A message transmission protocol `Π = (Setup, S, R)` with message space
  `Msg`, sender key space `SendK`, and receiver key space `RecvK`, running in
  the effect monad `m`.

  Note that we use Spec for the protocol shape, which is more general than the
  protocol shape used in DF'17, where a protocol is linear, alternating between
  the two parties, with S speaking last. Instantiations should use the `ofRounds`
  constructor to the Spec is linear, that the parties alternate turns, and that
  S speaks last. -/
structure MsgTransmissionProtocol (m : Type → Type) [Monad m] (Msg SendK RecvK : Type) where
  /-- The shape of the message exchange: a tree whose moves are protocol messages. -/
  spec : Spec
  /-- Per-node assignment of which party sends each message (focal `S` vs counterpart). -/
  owner : RoleDecoration spec
  /-- Key generation, producing the sender and receiver keys. -/
  setup : m (SendK × RecvK)
  /-- The honest sender `S(sendk, m)` as a focal strategy with no private output. -/
  sender : SendK → Msg →
    StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal spec owner (fun _ => Unit)
  /-- The honest receiver `R(recvk)` as a counterpart strategy whose private
    output is a recovered message or `⊥`. -/
  receiver : RecvK →
    StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart spec owner
      (fun _ => Option Msg)

namespace MsgTransmissionProtocol

variable {m : Type → Type} [Monad m] {Msg SendK RecvK : Type}

/-- Run one honest session `⟨S(sendk, msg), R(recvk)⟩`, returning the session
  transcript paired with the sender's (trivial) output and the receiver's
  private output. -/
def execute (proto : MsgTransmissionProtocol m Msg SendK RecvK)
    (sendk : SendK) (recvk : RecvK) (msg : Msg) :
    m ((_tr : Spec.Transcript proto.spec) × Unit × Option Msg) :=
  Interaction.TwoParty.run proto.spec proto.owner (proto.sender sendk msg) (proto.receiver recvk)

/-- The receiver's private output `m' ∈ Msg ∪ {⊥}` after one honest session,
  i.e. the value of `⟨S(sendk, msg), R(recvk)⟩`. -/
def receiverOutput (proto : MsgTransmissionProtocol m Msg SendK RecvK)
    (sendk : SendK) (recvk : RecvK) (msg : Msg) : m (Option Msg) := do
  let ⟨_, _, out⟩ ← proto.execute sendk recvk msg
  return out

/-- Correctness experiment (Definition 1): generate keys, run one honest
  session on `msg`, and report whether the receiver recovered exactly `msg`. -/
def CorrectExp [DecidableEq Msg] (proto : MsgTransmissionProtocol m Msg SendK RecvK)
    (msg : Msg) : m Bool := do
  let (sendk, recvk) ← proto.setup
  let out ← proto.receiverOutput sendk recvk msg
  return decide (out = some msg)

/-- A protocol is perfectly correct when, for every message, an honest session
recovers it with probability `1`. -/
def PerfectlyCorrect [DecidableEq Msg]
    (proto : MsgTransmissionProtocol ProbComp Msg SendK RecvK) : Prop :=
  ∀ msg : Msg, Pr[= true | proto.CorrectExp msg] = 1

/-- A role declaration that models property from DF'17 (page 6) that S and R
  alternate turns and that S speaks last -/
def alternatingOwner : (Ms : List Type) → RoleDecoration (Spec.ofList Ms)
  | [] => ⟨⟩
  | _ :: tl => ⟨if tl.length % 2 = 0 then Role.sender else Role.receiver,
                fun _ => alternatingOwner tl⟩

/-- Using `alternatingOwner`, above, ensures that, for an n-round protocol, R
  speaks first if n is even, and S speaks first if n is odd. -/
theorem alternatingOwner_first_role (T : Type) (tl : List Type) :
    (alternatingOwner (T :: tl)).1 = Role.receiver ↔ Even (T :: tl).length := by
  change (if tl.length % 2 = 0 then Role.sender else Role.receiver) = Role.receiver ↔ _
  rw [Nat.even_iff, List.length_cons]
  by_cases h : tl.length % 2 = 0 <;> simp [h] <;> omega

/-- Construct a `MsgTransmissionProtocol` with a linear Spec, where the parties
  alternate turns, and where S speaks last. -/
def ofRounds (Ms : List Type)
    (setup : m (SendK × RecvK))
    (sender : SendK → Msg → StrategyOver (SyntaxOver.TwoParty.pairedSpec m)
      Participant.focal (Spec.ofList Ms) (alternatingOwner Ms) (fun _ => Unit))
    (receiver : RecvK → StrategyOver (SyntaxOver.TwoParty.pairedSpec m)
      Participant.counterpart (Spec.ofList Ms) (alternatingOwner Ms) (fun _ => Option Msg)) :
    MsgTransmissionProtocol m Msg SendK RecvK where
  spec := Spec.ofList Ms
  owner := alternatingOwner Ms
  setup := setup
  sender := sender
  receiver := receiver

end MsgTransmissionProtocol

structure TimestampedTranscript (Ms : List Type) where
  messages : Spec.Transcript (Spec.ofList Ms)
  timestamps : List ℕ
  length_eq : timestamps.length = Ms.length

instance : DecidableEq (Spec.Transcript (Spec.ofList ([] : List Type))) :=
  inferInstanceAs (DecidableEq PUnit)

instance {T : Type} {tl : List Type} [DecidableEq T]
    [DecidableEq (Spec.Transcript (Spec.ofList tl))] :
    DecidableEq (Spec.Transcript (Spec.ofList (T :: tl))) :=
  inferInstanceAs (DecidableEq ((_ : T) × Spec.Transcript (Spec.ofList tl)))

namespace TimestampedTranscript

private def interleave : Bool → List (ℕ × ℕ) → List ℕ
  | _, [] => []
  | ab, (a, b) :: rest => (if ab then [a, b] else [b, a]) ++ interleave (!ab) rest

def Matching {Ms : List Type} (T Tstar : TimestampedTranscript Ms) : Prop :=
  T.messages = Tstar.messages ∧
    List.IsChain (· < ·) (interleave (Ms.length % 2 == 0) (T.timestamps.zip Tstar.timestamps))

instance {Ms : List Type} [DecidableEq (Spec.Transcript (Spec.ofList Ms))]
    (T Tstar : TimestampedTranscript Ms) : Decidable (Matching T Tstar) := by
  unfold Matching
  infer_instance

end TimestampedTranscript
