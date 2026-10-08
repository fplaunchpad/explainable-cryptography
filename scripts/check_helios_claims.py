#!/usr/bin/env python3
"""Check reconstruction audit coverage and stale status prose.

This source-level smoke check does not replace Lean elaboration or establish
that a supplied build log belongs to the current worktree. Historical result
entries are deliberately excluded from the stale-status scan.
"""

import argparse
from pathlib import Path
import re


ROOT = Path(__file__).resolve().parents[1]
MODULES = (
    "SourceBallotSecrecy SourceBallotSecrecySPOT "
    "SourceFrameReindexing SourceElectionRelation SourceElectionRelationSPOT "
    "SourceReadyPrefixExtraction SourceCommunicationAvailability SourceRawCommunicationMatching SourceOpenLocalPresentation SourceLocalCodePrefix SourcePresentedInternalAvailability SourceRawInternalMatching SourceRawInternalSPOT "
    "SourceVisibleReadiness SourceJointVisibleAvailability SourceRawInputMatching SourceRawOutputMatching SourceRawVisibleSPOT "
    "SourceCapturedEquations SourceCaptureAlgebra SourceCapturedEquationsSPOT SourceCaptureCopy SourceOutputFramePresentation SourceReachableFramePresentation SourceOutputFramePresentationSPOT "
    "SourceFrameAlgebra SourceFrameAlgebraQuotient SourceFrameAlgebraSPOT "
    "SourceVariableFramePrefix SourceReachableFramePrefix SourceVariableFramePrefixSPOT "
    "SourcePresentationAlignment SourcePresentationAlignmentSPOT "
    "SourceInputPresentationClosure SourceInputPresentationSPOT "
    "SourceExecutionHandleRenaming SourceReachableElectionPhases SourceReachableElectionSPOT "
    "SourceStructuralActionOpenings SourceStructuralOpeningReconstruction SourceStructuralOpeningSPOT "
    "SourceScopedProgramCapture SourceScopedCaptureFrames SourceScopedCaptureSPOT "
    "SourceLocalCaptureNormalization SourceTermProgramCapture SourceProgramCaptureSPOT "
    "SourceFrameContextSubstitution SourceRecipeCaptureNormalization SourceRecipeCaptureSPOT "
    "SourceNamedLocalRigidity SourceRigidExecution SourceRigidExecutionSPOT "
    "SourceRigidityEnvironment SourceRigidityBinders SourceBinderStructure SourceBoundRigidity SourceNamedRigidityBoundary SourcePresentationRigidity SourceBoundRigiditySPOT "
    "SourceLocalRigidity SourceRigidityPreservation SourceRigidityBoundary SourceLocalRigiditySPOT "
    "SourcePublicationSeparation SourceElectionHandleExclusion SourceElectionHandleSPOT "
    "SourceHandleOutputClosure SourceJointHandleOutput SourceHandleOutputDerivation SourceHandleOutputSPOT "
    "SourceMappedCanonicalStates SourceCoordinatedPhases SourceCoordinatedInput SourceCoordinatedFreshInput SourceCoordinatedInternal SourceCoordinatedOutput SourceCoordinatedSPOT "
    "SourcePairedOpeningObservations SourceJointPublicInput SourceJointBoundOutput SourceJointFreshInput SourceElectionJointVisible SourceJointVisibleSPOT "
    "SourcePairedCanonicalPermutations SourceJointOpeningInternal SourceElectionJointInvariant SourceJointInternalSPOT "
    "SourceRealizationChannels SourceJointOpening SourceJointOpeningPolicy SourceJointOpeningSPOT "
    "SourceBackwardVisibleRealization SourceInputRealizationClosure SourceOutputRealizationClosure SourcePairedVisibleOpenings SourceVisibleDeterminismPermutations SourceCanonicalOpeningVisible SourceElectionVisibleDeterminism SourceElectionVisibleInvariant SourceVisibleInvariantSPOT "
    "SourceBackwardRealization SourceRealizationTargetClosure SourcePairedOpeningReduction SourceOpeningValuePermutations SourceCanonicalOpeningInvariant SourceCanonicalOpeningInternal SourceInternalFrameIdentity SourceElectionOpeningInvariant SourceOpeningInternalTraces SourceTargetInvariantSPOT "
    "SourceSameRealizations SourceOpeningInversion SourceOpeningTransport SourceOpeningParallelComparison SourceOpeningAlphaComparison SourceOpeningNameComparison SourceOpeningVariableComparison SourceStructuralOpeningComparison SourceOpeningInternalInterpretation SourceFreshCanonicalInternal SourceFreshElectionInternal SourceOpeningComparisonSPOT "
    "SourceNameOpening SourceOpeningSupport SourceOpeningAlpha SourceOpeningDerivation SourceOpeningFaithfulness SourceCanonicalOpening SourceOpeningSPOT "
    "SourceGuardRetractions SourceReadyGuardRetractions SourceRetractedInterpretation SourceRetractionSubstitution SourceElectionGuardRetractions SourceGuardRetractionSPOT "
    "SourceConditionalReadiness SourceConditionalLocation SourceElectionConditionalLocation SourceNamedQuietPhases SourceConditionalLocationSPOT "
    "SourceClassifiedInternal SourceCommunicationInterpretation SourceElectionCommunicationMatching SourceClassifiedCommunication SourceClassifiedElection SourceCommunicationSPOT "
    "SourceNamedVisibleInterpretation SourceNamedCanonicalVisible SourceNamedElectionVisible SourceFiniteFaithfulAssignments SourceNamedVisibleSPOT "
    "SourceNameAssignments SourceNamedBodyInterpretation SourceBodyInterpretationContexts SourceNamedStructuralInterpretation SourceCanonicalBodyInterpretation SourceNamedBodySPOT "
    "SourceFrameConstraints SourceNamedFrameSolutions SourceFrameSolutionStructure SourceCanonicalFrameSolutions SourceIndependentFrameCompatibility SourceFrameEquationActions SourceFrameCompatibilitySPOT "
    "SourceGuardedProgram SourceGuardedActivation SourceBoardProgramSubstitution SourceGuardedBoard SourceGuardedBoardActions SourceGuardedElection SourceGuardedBoardSPOT "
    "SourceProgramSubstitution SourceNamedInstantiation SourceVoterSubstitution SourceOpenVoterTemplate SourceElectionParameters SourceOpenElectionApplication SourceAppliedElectionActions SourceVoterApplicationSPOT "
    "SourceScopedTermProgram SourceVoterNonceScopes SourceFreshElectionAllocation SourceVoterScopeContext SourceAdministrationNameSupport SourceNamePrefixPolicies SourceScopedVoterElection SourceScopedElectionActions SourceVoterScopeSPOT "
    "SourceAgentProgram SourceFiniteSubstitution SourceBoardTallyProgram SourceBoardTallyBridge SourceBoardTallySPOT "
    "SourceTermProgram SourceVoterRegisters SourceVoterComputation SourceComputedVoterElection SourceVoterComputationSPOT "
    "SourceUnusedRestrictions SourceFramePolicies SourceCanonicalPolicyPadding SourceCommonFramePolicy SourcePolicyPaddingSPOT "
    "SourceExtendedInstantiation SourceLocalNormalization SourceNamedLocalNormalization SourceLocalNormalizationSPOT "
    "SourceExtendedSubstitution SourceNamedGeneralSubstitution SourceExtendedSubstitutionSPOT "
    "SourceNamedNameSupport SourceNamedNameStructure SourceNamedNameActions SourceNamedPresentationNames SourceNamedPermutationSPOT "
    "SourceNamedFramePresentation SourceNamedStaticEquivalence SourceNamedFreshStatic SourceNamedElectionStatic SourceNamedStaticSPOT "
    "SourceNamedExports SourceNamedUniqueDefinitions SourceNamedUniqueStructure SourceNamedDomainActions SourceNamedVariableClosure SourceNamedLabelScope SourceAdmissiblePrenex SourceNamedAdmissibilitySPOT "
    "SourceExtendedFrameProjection SourceNamedFrameProjection SourceFrameStructure SourceFrameActions SourceCanonicalFrameProjection SourceFrameProjectionSPOT "
    "SourceVariableRenameTools SourceStructuralVariableRename SourceNamedVariableRename SourceBoundPairedPrenex SourceNamedBoundPrenex SourceFreshBoundPrenex SourceBoundPrenexSPOT "
    "SourcePairedPrenex SourceNamedInternalPrenex SourceFixedLabelNames SourceNamedFreePrenex SourceFreshOperationalPrenex SourceOperationalPrenexSPOT "
    "SourceEquationalNameTransport SourceInterpretationNames SourceInterpretedNameActions SourceFreshInterpretation SourceNamePrefixStructure SourceNamedPrenex SourceNameInterpretationSPOT "
    "SourceInterpretationEnvironment SourceInterpretedLabels SourceInterpretationFree SourceInterpretationBound SourceInterpretationVisibleFrames SourceInterpretationCapture SourceVisibleInterpretationSPOT "
    "SourceEquationalFormula SourceEquationalProcesses SourceEquationalParallel SourceEquationalVisible SourceEvaluatedEquivalence SourceActiveInterpretation SourceInterpretationStructure SourceInterpretationReduction SourceInterpretationFrames SourceInterpretationSPOT "
    "SourceBoundNames SourceFreshRepresentatives SourceFreshPrefixTools SourceCommonFreshPrefix SourceFreshPolicy SourceFreshInputStates SourceFreshNamesSPOT "
    "SourceInputAlphaBoundary "
    "SourceChannelSupport SourceNamedChannels SourceChannelScope SourceChannelPreservation SourceChannelClosureSPOT "
    "SourceNameSupport SourceNameRestrictionSyntax SourceNameRestrictionRules SourceNameRestrictionBridge SourceNameRestrictionSPOT "
    "SourceNameFrames SourceNameScoped SourceNameFrameEmbedding SourceNameFrameSPOT "
    "SourceNameTerms SourceNameProcesses SourceNameBehavior SourceNameExtended SourceNameLabels SourceNameSPOT "
    "SourceVariableScope SourceUniqueDefinitions SourceWellFormedStates SourceWellFormedPreservation SourceWellFormedSPOT "
    "SourceFrameSubstitution SourceFrameInput SourceFrameInternal SourceFrameInputSPOT "
    "SourceAtomicLabels SourceAtomicOutput SourceExtendedRenaming SourceActiveFrames SourceOutputDerivation SourceAtomicOutputSPOT "
    "SourceExtendedSyntax SourceActiveBinding SourceExtendedExports SourceExtendedInternal SourceActiveBindingSPOT "
    "SourceVisibleInversion SourcePublicationSyntax SourcePublicOutputPrefixes SourcePublicInputPrefixes SourceCapturedViews SourceVisibleCorrespondence SourceVisibleCorrespondenceSPOT "
    "SourceVisibleSyntax SourceVisibleReduction SourceScopedSyntax SourceScopedActions SourceVisibleElection SourceScopedSPOT "
    "SourceChannelPolicy SourceTauInversion SourceTauShapes SourceResidualQuiet SourceResidualDeterminism SourceInternalCorrespondence SourceInternalSPOT "
    "SourceParallelSyntax SourceParallelStructure SourceParallelReduction SourceParallelGuards SourceElectionResiduals SourceElectionSilent SourceParallelSPOT "
    "SourceElectionGuard SourceElectionSyntax SourceElectionBinding SourceElectionReduction SourceElectionSPOT "
    "SourceProcessSyntax SourceProcessBinding SourceProcessSPOT "
    "SourceInputBinding SourcePayloadSyntax SourcePayloadAgreement SourcePayloadSPOT "
    "HistoricalProcessSyntax HistoricalProcessInvariant HistoricalProcessMatching HistoricalProcessSPOT "
    "TrusteeFreeSyntax TrusteeFreeReduction InitialTrusteeFree TrusteeFreeValues TrusteeFreeMultiplication TrusteeFreeDestructors TrusteeFreeMinimumSupport PublishedStaticEquivalence TrusteeFreeSPOT "
    "ResultHandleSyntax ResultHandleTransport ResultNonceSPOT ResultHandleSPOT "
    "ExpandedPublicDecryption ExpandedTrusteeBinding ExpandedPublicDecryptionSPOT "
    "ExpandedSuccessfulCheckTransport ExpandedSuccessfulDecryptionTransport ExpandedSuccessfulCheckSPOT "
    "ExpandedOldRecipeTools ExpandedHonestFieldTransport ExpandedHonestTailMinima ExpandedPairMinimumTransport ExpandedPairMinimumSPOT ExpandedRootAssembly ExpandedRootAssemblySPOT "
    "PaddedNumericHandleCosts ExpandedPaddedMinima ExpandedSingleMixedTransport ExpandedPaddedSPOT "
    "MixedHandleTools ExpandedMixedCompression ExpandedMixedMinima ExpandedMixedSPOT "
    "CombinationHandleTools ExpandedHonestMinima ExpandedHonestSPOT "
    "AssemblyCompressionTools ExpandedConstructedMinima ExpandedConstructedCompression ExpandedConstructedSPOT "
    "ExpandedMulMinimumClosure ExpandedMulMinimumSPOT "
    "ExpandedObservationAssembly ExpandedMinimumLifting ExpandedObservationSPOT "
    "AssemblyHandleTools ExpandedCiphertextAssembly ExpandedCiphertextTransport ExpandedAssemblySPOT "
    "OpaqueMixedNonces ProtectedGroupEquality ExpandedGroupEquality ExpandedGroupSPOT "
    "MultiplicationOriginTools ExpandedMulOrigins ExpandedMulPartitions ExpandedMulTransport ExpandedMulSPOT "
    "NumericHandleCosts NumericHandleRealization ExpandedAddMinimumClosure ExpandedAddMinimumSPOT "
    "AdditionOriginTools ExpandedAdditionOrigins NumericHandleAddition ExpandedAdditionSummary ExpandedAdditionTransport ExpandedAdditionSPOT "
    "CompositionOriginTools ExpandedCompositionOrigins ExpandedCompositionTransport ExpandedCompositionSPOT "
    "StuckMinimumTools ExpandedStuckOrigins ExpandedStuckTransport ExpandedStuckSPOT "
    "FrameValueShapeReflection ExpandedShapeTools ExpandedValueShapes ExpandedDecryptionTransport ExpandedShapeSPOT "
    "CiphertextKeyTransfer ExpandedCipherKeyTransfer ExpandedCipherKeySPOT "
    "CheckMinimumTools ExpandedSuccessfulProjections ExpandedCheckOrigins ExpandedCheckSPOT "
    "ExpandedAtomicOrigins ExpandedAtomicTransport ExpandedAtomicSPOT "
    "ExpandedPairOrigins ExpandedPairTransport ExpandedPairSPOT "
    "ProofMinimumTools ExpandedProofOrigins ExpandedProofTransport ExpandedProofSPOT "
    "PublicKeyMinimumTools ExpandedPublicKeyOrigins ExpandedPublicKeyTransport ExpandedKeySPOT "
    "FrameMinimumOrigins ExpandedProjectionOrigins ExpandedValueOrigins ExpandedPartialTransport ExpandedOriginSPOT "
    "ExpandedPublishedFrames ExpandedFrameEquivalence ExpandedMinimumOrigins ExpandedFrameSPOT "
    "OpaqueProtection OpaqueNonDeducibility OpaqueComposedNames PublishedProtection PublishedProtectionSPOT "
    "TrusteePartialBoundary TrusteePartialSPOT "
    "PublishedFrames FrameExtension PublishedResults PublishedFrameSPOT "
    "ElectionTally AcceptedSequences SharedTally SharedTallySPOT "
    "SuccessfulDecryptionClosure SuccessfulDecryptionSPOT "
    "ConstructedCheckTransport HonestCheckCombinations SuccessfulCheckTransport SuccessfulDecryptionTransport SuccessfulCheckSPOT "
    "PaddedPayloadCosts PaddedPayloadMinima SingleMixedMinimumClosure DecryptCheckTransport PaddedMinimumSPOT "
    "MixedCompressionCosts MixedCompression DecryptCheckSingleMixedTransport MixedCompressionSPOT "
    "BoundedSharedMinima JointMinimumTransport DecryptCheckMixedMulTransport JointMinimumSPOT "
    "ConstructedCompression ConstructedCompressionSPOT "
    "HonestProductMinima HonestProductMinimumSPOT "
    "MultiplicationPieceReassembly MultiplicationSharedReassembly InductiveMinimumTransport DecryptCheckCipherMulTransport MultiplicationReassemblySPOT "
    "MultiplicationMinimumPartitions MultiplicationMinimumClosure MultiplicationMinimumSPOT "
    "AdditionMinimumCosts AdditionMinimumRealization AdditionMinimumClosure DecryptCheckMulTransport AdditionMinimumSPOT "
    "NumericAdditionInversion CandidateSubstitutions GeneralCandidateFrames "
    "GeneralCandidateProtection GeneralProjectionOrigins GeneralMinimumOrigins "
    "GeneralMinimumProofs GeneralAcceptedProofs GeneralAggregateExclusion "
    "GeneralAcceptedReconstruction GeneralCandidateSPOT GeneralReconstructionSPOT "
    "PublicReconstruction GeneralStaticTransfer StaticAcceptance StaticEquivalenceSPOT "
    "PublicReconstructionSPOT NumericOffsetEquality NumericReflectionSPOT "
    "CiphertextCombinations CiphertextCombinationSPOT "
    "MixedNonceProvenance MixedCiphertexts MixedCiphertextSPOT "
    "CiphertextGroupingSoundness CiphertextGroupingSPOT "
    "GroupedCiphertextEquality CiphertextObservationInduction CiphertextObservationSPOT "
    "HonestProofEquality ProofObservationInduction ProofObservationSPOT "
    "PublicKeyOrigins PublicKeyObservationInduction PublicKeyObservationSPOT "
    "PartialDecryptionOrigins PartialDecryptionObservationInduction PartialDecryptionObservationSPOT "
    "PairObservationOrigins PairObservationInduction PairObservationSPOT "
    "AtomicObservationOrigins AtomicObservationInduction AtomicObservationSPOT "
    "ProofCheckObservationInduction MinimumProjectionObservations StuckCheckOrigins MinimumDestructorSPOT "
    "StuckDestructorStructure StuckDestructorOrigins StuckDestructorSPOT "
    "DecryptionProbes PartialKeyObservationInduction DecryptionProbeSPOT "
    "ValueShapeTransfer MinimumValueShapes MinimumDestructorTransfer ValueShapeSPOT "
    "FullCompositionFactors MinimumCompositionOrigins CompositionLeaves "
    "CompositionObservationInduction CompositionObservationSPOT "
    "FullAdditionSummary MinimumAdditionOrigins AdditionLeaves AdditionObservationInduction AdditionObservationSPOT "
    "MinimumMultiplicationOrigins NormalMultiplicationFactors MultiplicationPartitions MultiplicationLeaves MinimumMultiplicationPartitions MultiplicationPartitionTransfer MultiplicationObservationInduction MultiplicationObservationSPOT "
    "MinimumTransport LocalMinimumTransport MinimumTransportSPOT "
    "NormalDestructorExclusions MinimumObservationAssembly ObservationAssemblySPOT "
    "MinimumParentClosure RemainingRootTransport LocalRootSPOT "
    "HonestProofMinima HonestProofTailMinima ProjectionMinimumTransport ProjectionTransportSPOT "
    "HonestCiphertextMinima CompleteProjectionTransport CompleteProjectionSPOT "
    "HonestFieldTransport HonestTailOrigins PairMinimumTransport PairTransportSPOT "
    "ConstructedCiphertextMinima DestructorArithmeticTransport ConstructedCiphertextSPOT "
    "CompositionMinimumCosts CompositionMinimumClosure DecryptCheckAddMulTransport CompositionMinimumSPOT"
).split()
DOCUMENTS = (
    "helios-reuse-retrospective "
    "helios-source-structural-openings "
    "helios-source-scoped-capture "
    "helios-source-program-capture "
    "helios-source-recipe-capture "
    "helios-source-rigid-execution "
    "helios-source-binder-rigidity "
    "helios-source-local-rigidity "
    "helios-source-publication-separation "
    "helios-source-handle-output "
    "helios-source-coordinated-phases "
    "helios-source-joint-visible "
    "helios-source-joint-internal "
    "helios-source-joint-openings "
    "helios-source-visible-invariant "
    "helios-source-target-invariant "
    "helios-source-opening-comparison "
    "helios-source-openings "
    "helios-source-guard-retractions "
    "helios-source-conditional-location "
    "helios-source-communication "
    "helios-source-named-visible "
    "helios-source-named-body "
    "helios-source-frame-compatibility "
    "helios-source-guarded-board "
    "helios-source-voter-application "
    "helios-source-voter-scopes "
    "helios-source-board-tallies "
    "helios-source-voter-computation "
    "helios-source-policy-padding "
    "helios-source-local-normalization "
    "helios-source-general-substitution "
    "helios-source-named-permutations "
    "helios-source-named-static "
    "helios-source-named-admissibility "
    "helios-source-frame-projection "
    "helios-source-bound-prenex "
    "helios-source-operational-prenex "
    "helios-source-name-interpretation "
    "helios-source-visible-interpretation "
    "helios-source-interpretation "
    "helios-source-fresh-names "
    "helios-source-channel-closure "
    "helios-source-name-restrictions "
    "helios-source-renamed-observations "
    "helios-source-name-permutations "
    "helios-source-wellformed "
    "helios-source-frame-input "
    "helios-source-atomic-output "
    "helios-source-active "
    "helios-source-visible "
    "helios-source-scoped "
    "helios-source-internal "
    "helios-source-parallel "
    "helios-source-election "
    "helios-source-processes "
    "helios-source-payloads "
    "helios-process-stages "
    "helios-published-static-equivalence "
    "helios-result-handle-binding "
    "helios-expanded-public-decryption "
    "helios-expanded-successful-checks "
    "helios-expanded-pair-selector-minima "
    "helios-expanded-padded-minima "
    "helios-expanded-mixed-compression "
    "helios-expanded-honest-minima "
    "helios-expanded-constructed-minima "
    "helios-expanded-multiplication-minima "
    "helios-expanded-observation-assembly "
    "helios-expanded-ciphertext-assemblies "
    "helios-expanded-ciphertext-groups "
    "helios-expanded-multiplication "
    "helios-expanded-addition-minima "
    "helios-expanded-addition "
    "helios-expanded-composition "
    "helios-expanded-stuck-values "
    "helios-expanded-value-shapes "
    "helios-expanded-ciphertext-keys "
    "helios-expanded-check-values "
    "helios-expanded-atomic-values "
    "helios-expanded-pair-values "
    "helios-expanded-proof-values "
    "helios-expanded-public-keys "
    "helios-expanded-value-origins "
    "helios-expanded-published-frames "
    "helios-published-protection "
    "helios-trustee-partial-boundary "
    "helios-published-frames "
    "helios-shared-tallies "
    "helios-initial-static-equivalence "
    "helios-successful-checks "
    "helios-padded-payload-minima "
    "helios-mixed-compression "
    "helios-joint-minimum-transport "
    "helios-constructed-compression "
    "helios-honest-product-minima "
    "helios-proof-blueprint helios-addition-minima helios-multiplication-minima helios-multiplication-reassembly "
    "handoff helios-symbolic helios-candidate-substitutions helios-accepted-ballots "
    "helios-historical-frames helios-minimal-recipes helios-nonce-nondeducibility "
    "helios-full-structure helios-static-equivalence helios-enriched-ciphertexts "
    "helios-mixed-ciphertexts helios-ciphertext-grouping helios-ciphertext-observations "
    "helios-proof-observations helios-public-key-observations "
    "helios-partial-decryption-observations helios-pair-observations helios-atomic-observations "
    "helios-destructor-observations helios-stuck-destructors helios-decryption-probes helios-value-shapes helios-composition-observations helios-addition-observations helios-multiplication-observations helios-minimum-transport helios-observation-assembly helios-local-root-transport helios-projection-transport helios-complete-projections helios-pair-transport helios-ciphertext-constructor-minima helios-composition-minima"
).split()


def declarations(path):
    # These modules use explicit, line-delimited namespaces and sections.
    # Track each scope instead of attributing a whole file to its first namespace.
    scopes = []
    for line in path.read_text().splitlines():
        match = re.match(r"^(namespace|section)(?:\s+(\S+))?\s*$", line)
        if match:
            scopes.append(match.groups())
        elif re.match(r"^end(?:\s|$)", line):
            if not scopes:
                raise ValueError(f"Unmatched end in {path}")
            scopes.pop()
        match = re.match(r"^theorem\s+(\S+)", line)
        if match:
            namespace = [name for kind, name in scopes if kind == "namespace"]
            yield ".".join(namespace + [match[1]])
    if scopes:
        raise ValueError(f"Unclosed scope in {path}")


def check(log_path=None):
    errors = []
    audit = (ROOT / "ExplainableCrypto/Helios/Symbolic/Audit.lean").read_text()
    checks = set(re.findall(r"^#check (\S+)\s*$", audit, re.M))
    axioms = set(re.findall(r"^#print axioms (\S+)\s*$", audit, re.M))
    names = set()
    for module in MODULES:
        path = ROOT / f"ExplainableCrypto/Helios/Symbolic/{module}.lean"
        names.update(declarations(path))
    for name in sorted(names):
        if name not in checks or name not in axioms:
            errors.append(f"Missing type/axiom audit entry: {name}")

    # Match specific retired claims, without matching 'Lemma 9; privacy is open'.
    stale = re.compile(
        r"(?:full source )?Lemma 9 remains open|Keep Lemma 9 open|"
        r"Extending the honest frame[^.]*remains (?:open|necessary)|"
        r"(?:characterization|characterisation) in Lemma 9 remains open|"
        r"(?:Named[.]StaticEq|Named static-equivalence|general StaticEq) transitivity "
        r"(?:remains? open|is not available)|"
        r"transitivity across unrelated presentation witnesses have not been proved",
        re.I,
    )
    for doc in DOCUMENTS:
        path = ROOT / f"docs/research/{doc}.md"
        flattened = " ".join(path.read_text().split())
        for match in stale.finditer(flattened):
            errors.append(f"Stale status in {path.relative_to(ROOT)}: {match[0]}")
    tasks = (ROOT / "task list.md").read_text()
    # The table is the maintained operator frontier. This consistency check
    # does not prove that its individual completion claims are justified.
    blueprint = (ROOT / "docs/research/helios-proof-blueprint.md").read_text()
    operator_rows = re.findall(
        r"^\| `(pk|partialDecrypt|spk|fst|snd|pair|penc|compose|add|mul|dec|checkspk)`(?: constructor)? \| ([^|]+)\|",
        blueprint, re.M,
    )
    closed = sum(status.replace("**", "").strip().startswith("Machine-checked")
                 for _, status in operator_rows)
    number_words = "zero one two three four five six seven eight nine ten eleven twelve".split()
    if len(operator_rows) != 12 or len({name for name, _ in operator_rows}) != 12:
        errors.append("Blueprint must contain exactly twelve distinct operator rows")
    elif f"Within B7, {number_words[closed]} of twelve operator-root cases are closed." not in blueprint:
        errors.append("Blueprint headline disagrees with its closed-operator table count")
    milestone_rows = re.findall(
        r"^\| (B\d+) \| [^|]+\| ([^|]+)\|", blueprint, re.M,
    )
    completed = sum(status.replace("**", "").strip().startswith("Machine-checked")
                    for _, status in milestone_rows)
    coverage = re.search(r"\*\*(\d+)%\s+milestone coverage\*\*", blueprint)
    if len(milestone_rows) != 10 or len({name for name, _ in milestone_rows}) != 10:
        errors.append("Blueprint must contain exactly ten distinct top-level milestones")
    elif not coverage or int(coverage[1]) != completed * 10:
        errors.append("Blueprint percentage disagrees with its completed-milestone table count")
    if not re.search(
        r"- \[x\] Prove the accepted-adversarial-ballot characterisation "
        r"\(Appendix B,\s+Lemma 9\)", tasks
    ):
        errors.append("Canonical task list does not mark the Lemma 9 item complete")

    if log_path:
        log = log_path.read_text()
        reports = dict(re.findall(
            r"'([^']+)' depends on axioms: \[([^\]]*)\]", log
        ))
        empty = set(re.findall(r"'([^']+)' does not depend on any axioms", log))
        for name in sorted(names - reports.keys() - empty):
            errors.append(f"No kernel axiom report in supplied log: {name}")
        for name, report in reports.items():
            if set(re.findall(r"[\w.]+", report)) - {
                "propext", "Classical.choice", "Quot.sound"
            }:
                errors.append(f"Unexpected axiom report: {name}: {report}")
        if not re.search(r"Build completed successfully \(\d+ jobs\)\.", log):
            errors.append("Supplied log has no successful full-build terminator")
        if re.search(r"sorryAx|^.*(?:warning:|error:)", log, re.M):
            errors.append("Supplied log contains a warning, error or sorryAx")
        print(f"Supplied log: {len(reports)} nonempty, {len(empty)} axiom-free reports")
    if errors:
        raise SystemExit("\n".join(errors))
    print(f"Checked {len(names)} public theorem audit entries and {len(DOCUMENTS)} current-status documents")


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--build-log", type=Path, help="Optional completed lake build log")
    check(parser.parse_args().build_log)
