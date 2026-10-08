import Examples.ElGamal.Basic
import VCVio.CryptoFoundations.SigmaProtocol
import Examples.ElGamal.ComputationalComplexity
import VCVio.CryptoFoundations.FiatShamir.Sigma

/-! Kernel audit of the selected pinned VCVio interfaces. -/

#check elGamalAsymmEnc
#check ChallengeVerifyProtocol
#check SigmaProtocol
#check OracleComp.Complexity.IsOraclePPTBy
#print axioms elGamalAsymmEnc.correct
#print axioms elGamalAsymmEnc.elGamal_oneTime_signedAdvantageReal_abs_eq_two_mul_ddhGuessAdvantage
#print axioms elGamalAsymmEnc.elGamal_IND_CPA_le_q_mul_ddh
#print axioms SigmaProtocol.extract_sound_of_speciallySoundAt
#print axioms elGamalAsymmEnc.IND_CPA_OneTime_DDHReduction_openOracle_isTotalQueryBound
#print axioms FiatShamir.perfectlyCorrect
