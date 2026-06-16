/-
Copyright (c) 2026 Ben Hamlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import VCVio.CryptoFoundations.AKE.Game

open OracleSpec OracleComp Interaction Interaction.TwoParty
open TimestampedTranscript MsgTransmissionProtocol AKE

namespace ICMA

variable {Msg SendK RecvK : Type}

def Soracle (proto : MsgTransmissionProtocol ProbComp Msg SendK RecvK) :
    OracleSpec (Msg × CptStrategy proto) :=
  fun _ => TimestampedTranscript proto.Ms

def soracleImpl {proto : MsgTransmissionProtocol ProbComp Msg SendK RecvK} (sendk : SendK) :
    QueryImpl (Soracle proto) (StateT (Env proto) ProbComp) := fun q => do
  let (msg, cpt) := q
  let ⟨tr, _, _⟩ ←
    (Interaction.TwoParty.run proto.spec proto.owner (proto.sender sendk msg) cpt : ProbComp _)
  logSession tr

def oracleImpl {proto : MsgTransmissionProtocol ProbComp Msg SendK RecvK} (sendk : SendK) :
    QueryImpl (unifSpec + Soracle proto) (StateT (Env proto) ProbComp) :=
  withUnif (soracleImpl (proto := proto) sendk)

structure Adversary (proto : MsgTransmissionProtocol ProbComp Msg SendK RecvK) where
  forge : RecvK → OracleComp (unifSpec + Soracle proto) (SenderStrategy ProbComp proto.Ms)

variable {proto : MsgTransmissionProtocol ProbComp Msg SendK RecvK}
  [DecidableEq (Spec.Transcript (Spec.ofList proto.Ms))]

def isPingPong (cr : ChallengeResult proto (Option Msg)) : Bool :=
  pingPong Role.receiver cr.oracleSessions cr.transcript

def challengeSession (A : Adversary proto) (sendk : SendK) (recvk : RecvK) :
    ProbComp (ChallengeResult proto (Option Msg)) := do
  let (focalStrat, env) ← (simulateQ (oracleImpl sendk) (A.forge recvk)).run ⟨0, []⟩
  let ⟨tr, _, mstar⟩ ←
    Interaction.TwoParty.run proto.spec proto.owner focalStrat (proto.receiver recvk)
  let challengeTr := stampAt proto tr env.clock
  pure ⟨mstar, challengeTr, env.sessions⟩

def Exp (A : Adversary proto) : ProbComp Bool := do
  let (sendk, recvk) ← proto.setup
  let cr ← challengeSession A sendk recvk
  if cr.outcome.isSome && !isPingPong cr then return true
  else return false

noncomputable def advantage (A : Adversary proto) : ℝ :=
  (Pr[= true | Exp A]).toReal

end ICMA
