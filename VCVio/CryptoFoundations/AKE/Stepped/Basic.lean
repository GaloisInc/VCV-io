/-
Copyright (c) 2026 Ben Hamlin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Ben Hamlin
-/
import VCVio.CryptoFoundations.AKE.Game

open OracleSpec OracleComp

namespace Stepped

variable {Msg SendK RecvK W : Type}

structure Party (In W Out : Type) where
  State : Type
  init : In → ProbComp (State × Option W)
  step : State → W → ProbComp (State × ((W × Option Out) ⊕ Out))

structure Transcript (W : Type) where
  entries : List (W × ℕ)

structure Session (σ W : Type) where
  state : σ
  transcript : Transcript W

def interleave : Bool → List (ℕ × ℕ) → List ℕ
  | _, [] => []
  | ab, (a, b) :: rest => (if ab then [a, b] else [b, a]) ++ interleave (!ab) rest

def Matching (oracleLeadsFirst : Bool) (T Tstar : Transcript W) : Prop :=
  T.entries.map Prod.fst = Tstar.entries.map Prod.fst ∧
    List.IsChain (· < ·)
      (interleave oracleLeadsFirst ((T.entries.map Prod.snd).zip (Tstar.entries.map Prod.snd)))

instance [DecidableEq W] (b : Bool) (T Tstar : Transcript W) :
    Decidable (Matching b T Tstar) := by
  unfold Matching
  infer_instance

def pingPong [DecidableEq W] (oracleLeadsFirst : Bool)
    (oracleTrs : List (Transcript W)) (challengeTr : Transcript W) : Bool :=
  oracleTrs.any fun T => decide (Matching oracleLeadsFirst T challengeTr)

def recordOne (tr : Transcript W) (w : W) (clock : ℕ) : Transcript W × ℕ :=
  (⟨tr.entries ++ [(w, clock)]⟩, clock + 1)

def recordOpt (tr : Transcript W) : Option W → ℕ → Transcript W × ℕ
  | none, clock => (tr, clock)
  | some w, clock => recordOne tr w clock

def runHonestLoop {InP OutP InQ OutQ : Type}
    (P : Party InP W OutP) (Q : Party InQ W OutQ) :
    ℕ → P.State → Q.State → Option OutP → Option OutQ → W → Bool →
      ProbComp (Option OutP × Option OutQ)
  | 0, _, _, pOut, qOut, _, _ => pure (pOut, qOut)
  | fuel + 1, pState, qState, pOut, qOut, w, true => do
      let (qState', react) ← Q.step qState w
      match react with
      | .inl (w', none) => runHonestLoop P Q fuel pState qState' pOut qOut w' false
      | .inl (w', some out) => runHonestLoop P Q fuel pState qState' pOut (some out) w' false
      | .inr out => pure (pOut, some out)
  | fuel + 1, pState, qState, pOut, qOut, w, false => do
      let (pState', react) ← P.step pState w
      match react with
      | .inl (w', none) => runHonestLoop P Q fuel pState' qState pOut qOut w' true
      | .inl (w', some out) => runHonestLoop P Q fuel pState' qState (some out) qOut w' true
      | .inr out => pure (some out, qOut)

def runHonest {InP OutP InQ OutQ : Type}
    (P : Party InP W OutP) (Q : Party InQ W OutQ) (inP : InP) (inQ : InQ) (fuel : ℕ) :
    ProbComp (Option OutP × Option OutQ) := do
  let (pState, pOpen) ← P.init inP
  let (qState, qOpen) ← Q.init inQ
  match pOpen, qOpen with
  | some w, _ => runHonestLoop P Q fuel pState qState none none w true
  | none, some w => runHonestLoop P Q fuel pState qState none none w false
  | none, none => pure (none, none)

namespace MTP

structure Scheme (Msg SendK RecvK W : Type) where
  rounds : ℕ
  setup : ProbComp (SendK × RecvK)
  sender : Party (SendK × Msg) W Unit
  receiver : Party RecvK W (Option Msg)

def CorrectExp [DecidableEq Msg] (proto : Scheme Msg SendK RecvK W) (m : Msg) : ProbComp Bool := do
  let (sendk, recvk) ← proto.setup
  let (_, rOut) ← runHonest proto.sender proto.receiver (sendk, m) recvk (proto.rounds + 1)
  return decide (rOut.join = some m)

def PerfectlyCorrect [DecidableEq Msg] (proto : Scheme Msg SendK RecvK W) : Prop :=
  ∀ m : Msg, Pr[= true | CorrectExp proto m] = 1

end MTP

end Stepped
