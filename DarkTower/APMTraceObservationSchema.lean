import DarkTower.APMCycleMachine

namespace DarkTower.APMTraceObservationSchema

inductive TraceObservationKind
  | progress | successor | delivery | proofStandard
  deriving DecidableEq, Repr

structure TraceObservationField where
  wireName : String
  sourcePath : List String

def traceObservationKinds : List TraceObservationKind :=
  [.progress, .successor, .delivery, .proofStandard]

def traceObservationCollection : TraceObservationKind → String
  | .progress => "progressObservations"
  | .successor => "successorObservations"
  | .delivery => "deliveryObservations"
  | .proofStandard => "proofStandardObservations"

def traceObservationDurableRecordKey : TraceObservationKind → String
  | .progress => "watchdog/trace-observation"
  | .successor => "trace/successor-observation"
  | .delivery => "trace/delivery-observation"
  | .proofStandard => "trace/proof-standard-observation"

def traceObservationFields : TraceObservationKind → List TraceObservationField
  | .progress =>
    [{wireName := "coordinatorEnabled", sourcePath := ["coordinator-enabled?"]},
     {wireName := "elapsedMs", sourcePath := ["elapsed-ms"]},
     {wireName := "validExternalWait", sourcePath := ["valid-external-wait?"]},
     {wireName := "semanticCursorAdvanced", sourcePath := ["semantic-cursor-advanced?"]},
     {wireName := "coordinatorDisabled", sourcePath := ["coordinator-disabled?"]},
     {wireName := "firstViolationRecorded", sourcePath := ["first-violation-recorded?"]}]
  | .successor =>
    [{wireName := "predecessorId", sourcePath := ["predecessor-id"]},
     {wireName := "terminalEvidenceId", sourcePath := ["terminal-evidence-id"]},
     {wireName := "collectionEvidenceId", sourcePath := ["collection-evidence-id"]},
     {wireName := "disposition", sourcePath := ["disposition"]},
     {wireName := "predecessorPersisted", sourcePath := ["predecessor-persisted?"]},
     {wireName := "successorAnnouncedId", sourcePath := ["successor-announced-id"]},
     {wireName := "successorActivatedId", sourcePath := ["successor-activated-id"]}]
  | .delivery =>
    [{wireName := "terminalJobId", sourcePath := ["terminal-job-id"]},
     {wireName := "deliveryStatus", sourcePath := ["delivery-status"]},
     {wireName := "inboxFileCreated", sourcePath := ["inbox-file-created?"]},
     {wireName := "registeredPushPerformed", sourcePath := ["registered-push-performed?"]},
     {wireName := "pollingAvailable", sourcePath := ["polling-available?"]}]
  | .proofStandard =>
    [{wireName := "artifactId", sourcePath := ["artifact-id"]},
     {wireName := "declarationName", sourcePath := ["declaration-name"]},
     {wireName := "solvedClaim", sourcePath := ["solved-claim?"]},
     {wireName := "axiomNames", sourcePath := ["axiom-names"]},
     {wireName := "allowedAxiomNames", sourcePath := ["allowed-axiom-names"]}]

theorem trace_observation_registry_complete (kind : TraceObservationKind) :
    kind ∈ traceObservationKinds := by cases kind <;> simp [traceObservationKinds]

end DarkTower.APMTraceObservationSchema
