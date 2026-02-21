---------------------- MODULE AdaptiveBFT_MainFlow ----------------------
EXTENDS AdaptiveBFT

(***************************************************************************)
(* Figure-A artifact: high-level AdaptiveBFT state-machine excerpt.        *)
(* This module aliases the main transition families used in the full spec. *)
(***************************************************************************)

M1_InjectAndValidate ==
    \/ InjectTxStep
    \/ PreValidateStep
    \/ AgeTxStep

M2_APSControlLoop ==
    \/ DetectAnomaly
    \/ SampleGrid
    \/ EstimateGrid
    \/ ExploreGrid
    \/ DeployConfig

M3_ConsensusPipeline ==
    \/ PreOrder
    \/ GenerateTentativeProposal
    \/ RecoverFullProposal
    \/ PrepareVoteStep
    \/ PrepareQC
    \/ PreCommitVoteStep
    \/ PreCommitQC
    \/ CommitVoteStep
    \/ DecideBlock

M4_AVCAndRVS ==
    \/ Tick
    \/ CastTimeoutVoteStep
    \/ StartViewChange
    \/ BroadcastNP
    \/ ConfirmNewPrimaryStep
    \/ BroadcastSyn
    \/ SendSynAckStep
    \/ CompleteViewChange

MainFlowNext ==
    \/ M1_InjectAndValidate
    \/ M2_APSControlLoop
    \/ M3_ConsensusPipeline
    \/ M4_AVCAndRVS

=============================================================================
