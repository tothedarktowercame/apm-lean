import Mathlib

/-!
# APM transport and publication specification

A computational model of the transport/publication distinctions recovered from
the f63 and f64 traces.  In particular, an acquired observation and the outcome
recorded by the controller are separate fields: conformance requires them to
agree instead of permitting a failed read to be recorded as absence.
-/

namespace ConstructionTargets.APMTransportPublicationSpec

inductive Operation where
  | read
  | write
  | publication
  | postPublicationVerification
  deriving DecidableEq, Repr

inductive ObservationOutcome where
  | success
  | timeout
  | unavailable
  | malformed
  | authoritativeAbsence
  | visibilityLag
  deriving DecidableEq, Repr

inductive EvidenceValidity where
  | obtained
  | notObtained
  | invalid
  deriving DecidableEq, Repr

def ObservationOutcome.isTransportFailure : ObservationOutcome → Bool
  | .timeout | .unavailable => true
  | _ => false

def ObservationOutcome.isAuthoritativeAbsence : ObservationOutcome → Bool
  | .authoritativeAbsence => true
  | _ => false

/-- Evidence status compatible with what was actually acquired. -/
def EvidenceCompatible : ObservationOutcome → EvidenceValidity → Prop
  | .success, .obtained => True
  | .authoritativeAbsence, .obtained => True
  | .malformed, .invalid => True
  | .timeout, .notObtained => True
  | .unavailable, .notObtained => True
  | .visibilityLag, .notObtained => True
  | _, _ => False

structure HistoryEntry where
  attempt : Nat
  operation : Operation
  acquiredOutcome : ObservationOutcome
  evidence : EvidenceValidity
  deriving DecidableEq, Repr

/-- The bounded retry state mirrored by a wire certificate. -/
structure RetryState (State Evidence : Type) where
  attempt : Nat
  maxAttempts : Nat
  wakeAtMs : Nat
  history : List HistoryEntry
  lastValidState : Option State
  lastValidEvidence : Option Evidence
  deriving DecidableEq, Repr

inductive ParkReason where
  | retryExhausted
  | invalidEvidence
  | authoritativeAbsence
  deriving DecidableEq, Repr

inductive Decision where
  | retry (wakeAtMs : Nat)
  | park (reason : ParkReason)
  | advance
  deriving DecidableEq, Repr

def needsRetry : ObservationOutcome → EvidenceValidity → Bool
  | .timeout, .notObtained => true
  | .unavailable, .notObtained => true
  | .visibilityLag, .notObtained => true
  | _, _ => false

/-- The recovered bounded decision rule.  A retry always names its wake. -/
def decide {State Evidence : Type} (retry : RetryState State Evidence)
    (outcome : ObservationOutcome) (evidence : EvidenceValidity) : Decision :=
  if needsRetry outcome evidence then
    if retry.attempt + 1 < retry.maxAttempts then .retry retry.wakeAtMs
    else .park .retryExhausted
  else
    match outcome, evidence with
    | .success, .obtained => .advance
    | .authoritativeAbsence, .obtained => .park .authoritativeAbsence
    | _, _ => .park .invalidEvidence

/-- Append a failed attempt without changing the last valid state or evidence. -/
def scheduleRetry {State Evidence : Type} (retry : RetryState State Evidence)
    (entry : HistoryEntry) (nextWakeAtMs : Nat) : RetryState State Evidence :=
  { retry with
    attempt := retry.attempt + 1
    wakeAtMs := nextWakeAtMs
    history := retry.history ++ [entry] }

structure ImplementationIdentity where
  specId : String
  sourceId : String
  loadedRuntimeId : String
  deriving DecidableEq, Repr

/-- Wire-shaped certificate for one publication transition. -/
structure RunCertificate (State Evidence : Type) where
  identity : ImplementationIdentity
  operation : Operation
  acquiredOutcome : ObservationOutcome
  classifiedOutcome : ObservationOutcome
  evidence : EvidenceValidity
  attempt : Nat
  maxAttempts : Nat
  wakeAtMs : Nat
  history : List HistoryEntry
  lastValidState : Option State
  lastValidEvidence : Option Evidence
  decision : Decision
  deriving DecidableEq, Repr

def RunCertificate.retryState {State Evidence : Type}
    (certificate : RunCertificate State Evidence) : RetryState State Evidence :=
  { attempt := certificate.attempt
    maxAttempts := certificate.maxAttempts
    wakeAtMs := certificate.wakeAtMs
    history := certificate.history
    lastValidState := certificate.lastValidState
    lastValidEvidence := certificate.lastValidEvidence }

def RunCertificate.Conformant {State Evidence : Type}
    (certificate : RunCertificate State Evidence) : Prop :=
  certificate.classifiedOutcome = certificate.acquiredOutcome ∧
  EvidenceCompatible certificate.acquiredOutcome certificate.evidence ∧
  certificate.decision =
    decide certificate.retryState certificate.acquiredOutcome certificate.evidence

theorem transportFailure_not_authoritativeAbsence (outcome : ObservationOutcome)
    (failure : outcome.isTransportFailure = true) :
    outcome.isAuthoritativeAbsence = false := by
  cases outcome <;> simp_all [ObservationOutcome.isTransportFailure,
    ObservationOutcome.isAuthoritativeAbsence]

theorem evidenceNotObtained_not_authoritativeAbsence
    (outcome : ObservationOutcome)
    (compatible : EvidenceCompatible outcome .notObtained) :
    outcome ≠ .authoritativeAbsence := by
  intro equality
  subst equality
  exact compatible

theorem scheduleRetry_preserves_lastValidState {State Evidence : Type}
    (retry : RetryState State Evidence) (entry : HistoryEntry) (wake : Nat) :
    (scheduleRetry retry entry wake).lastValidState = retry.lastValidState := rfl

theorem scheduleRetry_preserves_lastValidEvidence {State Evidence : Type}
    (retry : RetryState State Evidence) (entry : HistoryEntry) (wake : Nat) :
    (scheduleRetry retry entry wake).lastValidEvidence = retry.lastValidEvidence := rfl

theorem terminalDecision_deterministic {State Evidence : Type}
    (retry : RetryState State Evidence) (outcome : ObservationOutcome)
    (evidence : EvidenceValidity) (first second : Decision)
    (hFirst : decide retry outcome evidence = first)
    (hSecond : decide retry outcome evidence = second) : first = second := by
  rw [← hFirst, ← hSecond]

def Decision.IsTerminal : Decision → Prop
  | .retry _ => False
  | .park _ | .advance => True

theorem retry_has_wake_or_terminal {State Evidence : Type}
    (retry : RetryState State Evidence) (outcome : ObservationOutcome)
    (evidence : EvidenceValidity) :
    (∃ wake, decide retry outcome evidence = .retry wake) ∨
      (decide retry outcome evidence).IsTerminal := by
  unfold decide
  split <;> rename_i hNeeds
  · split <;> rename_i hBound
    · exact Or.inl ⟨retry.wakeAtMs, rfl⟩
    · exact Or.inr trivial
  · split <;> simp [Decision.IsTerminal]

abbrev FixtureState := String
abbrev FixtureEvidence := String

def recoveredIdentity : ImplementationIdentity :=
  { specId := "apm-transport-publication/v1"
    sourceId := "recovered-source"
    loadedRuntimeId := "recovered-loaded-runtime" }

/-- f63 acquired visibility lag but historically recorded authoritative absence. -/
def f63HistoricalCertificate : RunCertificate FixtureState FixtureEvidence :=
  { identity := recoveredIdentity
    operation := .postPublicationVerification
    acquiredOutcome := .visibilityLag
    classifiedOutcome := .authoritativeAbsence
    evidence := .notObtained
    attempt := 0
    maxAttempts := 1
    wakeAtMs := 0
    history := []
    lastValidState := some "last-valid-frame"
    lastValidEvidence := some "persisted-review"
    decision := .park .authoritativeAbsence }

theorem f63_historical_nonconformant :
    ¬ f63HistoricalCertificate.Conformant := by
  simp [RunCertificate.Conformant, f63HistoricalCertificate]

def f64TransportFailure : RunCertificate FixtureState FixtureEvidence :=
  { identity := recoveredIdentity
    operation := .write
    acquiredOutcome := .timeout
    classifiedOutcome := .timeout
    evidence := .notObtained
    attempt := 0
    maxAttempts := 2
    wakeAtMs := 120000
    history := []
    lastValidState := some "last-valid-frame"
    lastValidEvidence := some "independent-review"
    decision := .retry 120000 }

def f64SuccessfulVisibility : RunCertificate FixtureState FixtureEvidence :=
  { identity := recoveredIdentity
    operation := .postPublicationVerification
    acquiredOutcome := .success
    classifiedOutcome := .success
    evidence := .obtained
    attempt := 1
    maxAttempts := 2
    wakeAtMs := 120000
    history :=
      [{ attempt := 0
         operation := .write
         acquiredOutcome := .timeout
         evidence := .notObtained }]
    lastValidState := some "published-frame"
    lastValidEvidence := some "visible-review"
    decision := .advance }

def RetryThenSuccessConformant {State Evidence : Type}
    (failure success : RunCertificate State Evidence) : Prop :=
  failure.Conformant ∧ success.Conformant ∧
  failure.decision = .retry success.wakeAtMs ∧
  success.attempt = failure.attempt + 1 ∧
  success.history = failure.history ++
    [{ attempt := failure.attempt
       operation := failure.operation
       acquiredOutcome := failure.acquiredOutcome
       evidence := failure.evidence }]

theorem f64_retry_then_visibility_conformant :
    RetryThenSuccessConformant f64TransportFailure f64SuccessfulVisibility := by
  simp [RetryThenSuccessConformant, RunCertificate.Conformant,
    f64TransportFailure, f64SuccessfulVisibility, EvidenceCompatible,
    RunCertificate.retryState, decide, needsRetry]

end ConstructionTargets.APMTransportPublicationSpec
