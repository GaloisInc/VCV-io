/-
Copyright (c) 2026 Ben Hamlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import VCVio.CryptoFoundations.AKE.Interactive.Protocol

open OracleSpec OracleComp Interaction Interaction.TwoParty
open TimestampedTranscript MsgTransmissionProtocol

namespace AKE

variable {Msg SendK RecvK : Type}

abbrev CptStrategy (proto : MsgTransmissionProtocol ProbComp Msg SendK RecvK) : Type :=
  StrategyOver (SyntaxOver.TwoParty.pairedSpec ProbComp) Participant.counterpart
    proto.spec proto.owner (fun _ => Unit)

structure Env (proto : MsgTransmissionProtocol ProbComp Msg SendK RecvK) where
  clock : ℕ
  sessions : List (TimestampedTranscript proto.Ms)

structure ChallengeResult (proto : MsgTransmissionProtocol ProbComp Msg SendK RecvK)
    (Outcome : Type) where
  outcome : Outcome
  transcript : TimestampedTranscript proto.Ms
  oracleSessions : List (TimestampedTranscript proto.Ms)

def stampAt (proto : MsgTransmissionProtocol ProbComp Msg SendK RecvK)
    (tr : Spec.Transcript proto.spec) (clock : ℕ) : TimestampedTranscript proto.Ms :=
  ⟨tr, (List.range proto.Ms.length).map (· + clock),
    by simp [List.length_map, List.length_range]⟩

def logSession {proto : MsgTransmissionProtocol ProbComp Msg SendK RecvK}
    (tr : Spec.Transcript proto.spec) :
    StateT (Env proto) ProbComp (TimestampedTranscript proto.Ms) := do
  let env ← get
  let session := stampAt proto tr env.clock
  set (⟨env.clock + proto.Ms.length, env.sessions ++ [session]⟩ : Env proto)
  pure session

def withUnif {ι : Type} {customSpec : OracleSpec ι} {σ : Type}
    (customImpl : QueryImpl customSpec (StateT σ ProbComp)) :
    QueryImpl (unifSpec + customSpec) (StateT σ ProbComp) :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget (StateT σ ProbComp)
    + customImpl

def pingPong {proto : MsgTransmissionProtocol ProbComp Msg SendK RecvK}
    [DecidableEq (Spec.Transcript (Spec.ofList proto.Ms))] (challenger : Role)
    (oracleSessions : List (TimestampedTranscript proto.Ms))
    (challengeTr : TimestampedTranscript proto.Ms) : Bool :=
  oracleSessions.any fun T => decide (Matching challenger T challengeTr)

end AKE
