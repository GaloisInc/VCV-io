/-
Copyright (c) 2026 Ben Hamlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import VCVio.CryptoFoundations.AKE.Game

open OracleSpec OracleComp Interaction Interaction.TwoParty
open TimestampedTranscript MsgTransmissionProtocol AKE

namespace UAKE

namespace Protocol

variable (m : Type → Type) [Monad m] (K : Type)

abbrev TStrategy (Ms : List Type) : Type 0 :=
  StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.focal
    (Spec.ofList Ms) (alternatingOwner Ms) (fun _ => Option K)

abbrev UStrategy (Ms : List Type) : Type 0 :=
  StrategyOver (SyntaxOver.TwoParty.pairedSpec m) Participant.counterpart
    (Spec.ofList Ms) (alternatingOwner Ms) (fun _ => Option K)

end Protocol

open Protocol

structure Protocol (m : Type → Type) [Monad m] (K UK TK : Type) where
  Ms : List Type
  setup : m (UK × TK)
  U : UK → UStrategy m K Ms
  T : TK → TStrategy m K Ms

namespace Protocol

variable {m : Type → Type} [Monad m] {K UK TK : Type}

def spec (proto : Protocol m K UK TK) : Spec :=
  Spec.ofList proto.Ms

def owner (proto : Protocol m K UK TK) : RoleDecoration proto.spec :=
  alternatingOwner proto.Ms

def execute (proto : Protocol m K UK TK) (uk : UK) (tk : TK) :
    m (Spec.Transcript proto.spec × Option K × Option K) := do
  let ⟨tr, kT, kU⟩ ← Interaction.TwoParty.run proto.spec proto.owner (proto.T tk) (proto.U uk)
  pure (tr, kU, kT)

def CorrectExp [DecidableEq K] (proto : Protocol m K UK TK) : m Bool := do
  let (uk, tk) ← proto.setup
  let (_, kU, kT) ← proto.execute uk tk
  return decide (kU = none ∨ kT = none ∨ kU = kT)

def PerfectlyCorrect [DecidableEq K] (proto : Protocol m K UK TK)
    (runtime : ProbCompRuntime m) : Prop :=
  Pr[= true | runtime.evalDist proto.CorrectExp] = 1

end Protocol

variable {K UK TK : Type}

def Toracle (proto : Protocol ProbComp K UK TK) :
    OracleSpec (CptStrategy proto.Ms) :=
  fun _ => TimestampedTranscript proto.Ms × Option K

def toracleImpl {proto : Protocol ProbComp K UK TK} (tk : TK) :
    QueryImpl (Toracle proto) (StateT (Env proto.Ms) ProbComp) := fun cpt => do
  let ⟨tr, kT, _⟩ ←
    (Interaction.TwoParty.run proto.spec proto.owner (proto.T tk) cpt : ProbComp _)
  let session ← logSession tr
  pure (session, kT)

def oracleImpl {proto : Protocol ProbComp K UK TK} (tk : TK) :
    QueryImpl (unifSpec + Toracle proto) (StateT (Env proto.Ms) ProbComp) :=
  withUnif (toracleImpl (proto := proto) tk)

structure Adversary (proto : Protocol ProbComp K UK TK) where
  State : Type
  challenge : UK → OracleComp (unifSpec + Toracle proto)
    (SenderStrategy ProbComp proto.Ms × State)
  post : State → Option K → OracleComp (unifSpec + Toracle proto)
    (Bool × Option (TimestampedTranscript proto.Ms))

variable {proto : Protocol ProbComp K UK TK}
  [DecidableEq (Spec.Transcript (Spec.ofList proto.Ms))]

def isPingPong (cr : ChallengeResult proto.Ms (Option K)) : Bool :=
  pingPong Role.receiver cr.oracleSessions cr.transcript

def isFullPingPong (cr : ChallengeResult proto.Ms (Option K)) :
    Option (TimestampedTranscript proto.Ms) → Bool
  | none => false
  | some T => decide (Matching Role.receiver T cr.transcript)

def challengeSession (A : Adversary proto) (uk : UK) (tk : TK) :
    ProbComp (ChallengeResult proto.Ms (Option K) × (A.State × Env proto.Ms × TK)) := do
  let ((focalStrat, st), env) ← (simulateQ (oracleImpl tk) (A.challenge uk)).run ⟨0, []⟩
  let ⟨tr, _, K0⟩ ← Interaction.TwoParty.run proto.spec proto.owner focalStrat (proto.U uk)
  let challengeTr := stampAt proto.Ms tr env.clock
  pure (⟨K0, challengeTr, env.sessions⟩,
    (st, { env with clock := env.clock + proto.Ms.length }, tk))

def finalize (A : Adversary proto) (st : A.State × Env proto.Ms × TK)
    (cr : ChallengeResult proto.Ms (Option K)) (b : Bool) (K1 : Option K) : ProbComp Bool := do
  let (aSt, env, tk) := st
  let Kb := if b then K1 else cr.outcome
  let ((b', revealed), _) ← (simulateQ (oracleImpl tk) (A.post aSt Kb)).run env
  if isFullPingPong cr revealed then $ᵗ Bool else pure (b' == b)

def Exp [SampleableType K] (A : Adversary proto) : ProbComp Bool := do
  let (uk, tk) ← proto.setup
  let b ← $ᵗ Bool
  let (cr, st) ← challengeSession A uk tk
  if cr.outcome.isNone then
    let K1 := none
    finalize A st cr b K1
  else if !isPingPong cr then
    return true
  else
    let K1 ← some <$> ($ᵗ K)
    finalize A st cr b K1

noncomputable def advantage [SampleableType K] (A : Adversary proto) : ℝ :=
  |(Pr[= true | Exp A]).toReal - 1 / 2|

end UAKE
