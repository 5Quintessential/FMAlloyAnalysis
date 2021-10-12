open util/boolean

-- Feature
abstract sig Feature{ up: set Feature, select: Bool }
-- No feature is a root feature of itself
fact { no f: Feature | f in f.^up }

-- Feature encoding described by Nakajima 2010

-- Mandatory : A0 ⇔ B0
-- Alternative : (A0 ⇔ B1 ⊕ B2) ∧¬(B1 ∧ B2)
-- Or : A0 ⇔ B1 ∨ B2
-- Optional : A0 ⇐ B0
-- Optional Alternative : (A0 ⇐ B1 ⊕ B2) ∧¬(B1 ∧ B2)
-- Optional Or : A0 ⇐ B1 ∨ B2
-- Mutual dependency : B2 ⇔ D1
-- Mutual Exclusion : ¬ (B2 ∧ D1)

-- Features in the bCMS model
one sig bCMS extends Feature{} {no up}
one sig Functional extends Feature{}
one sig NonFunctional extends Feature {}
one sig DataCommConf, Encrypted, NotEncrypted extends Feature {}
one sig Authentication, PasswordBased, CertificateBased, BiometricBased, OneTimePwd, ChallengeResponse extends Feature {}
one sig SymmetricEncryption, MutualAuthorization, Kerberos extends Feature {}
one sig VehiclesManagement, VMCommunicationProtocol, CrisisMultiplicity extends Feature {}
one sig NoSendAndReceive, Other, SOAP, SSL, Single, Multiple extends Feature {}
one sig PSCSendAndReceive, FSCSendAndReceive, PSCAndFSCSend, PSCReceive extends Feature {}

-- Encoding the Feature Model diagram using propositional formulas described by Nakajima 2010
fact {
	(bCMS.select = True) <=> (Functional.select = True) and (NonFunctional.select = True) and 
		((Functional.up = bCMS) and (NonFunctional.up = bCMS))
	(NonFunctional.select = True) <=> (DataCommConf.select = True) and (DataCommConf.up = (NonFunctional))
	(Functional.select = True) <=> (CrisisMultiplicity.select = True) and (CrisisMultiplicity.up = (Functional))
	(DataCommConf.select = True) => not (Encrypted.select = True and NotEncrypted.select = True)
		(Encrypted.select = True) => (Encrypted.up = (DataCommConf)) else (NotEncrypted.up = (DataCommConf))
	(CrisisMultiplicity.select = True) => not (Single.select = True and Multiple.select = True)
		(Single.select = True) => (Single.up = (CrisisMultiplicity)) else (Multiple.up = (CrisisMultiplicity))
	(Authentication.select = True) => ((NonFunctional.select = True) and (Authentication.up = (NonFunctional)))
	(Authentication.select = True) <=> (PasswordBased.select = True or CertificateBased.select = True or BiometricBased.select = True or OneTimePwd.select = True or ChallengeResponse.select = True)
		(PasswordBased.select = True) => (PasswordBased.up = (Authentication))
		(CertificateBased.select = True) => (CertificateBased.up = (Authentication))
		(BiometricBased.select = True) => (BiometricBased.up = (Authentication))
		(OneTimePwd.select = True) => (OneTimePwd.up = (Authentication))
		(ChallengeResponse.select = True) => (ChallengeResponse.up = (Authentication))
	(SymmetricEncryption.select = True or MutualAuthorization.select = True or Kerberos.select = True) => not(SymmetricEncryption.select = True and MutualAuthorization.select =True and Kerberos.select = True)
		(SymmetricEncryption.select = True) => (not (MutualAuthorization.select = True and Kerberos.select = True) and SymmetricEncryption.up = (ChallengeResponse))
		(MutualAuthorization.select = True) => (not (SymmetricEncryption.select = True and Kerberos.select = True) and MutualAuthorization.up = (ChallengeResponse))
		(Kerberos.select = True) => (not (MutualAuthorization.select = True and SymmetricEncryption.select = True) and Kerberos.up = (ChallengeResponse))
	(VehiclesManagement.select = True or VMCommunicationProtocol.select = True) => (Functional.select = True)
		(VehiclesManagement.select = True) => VehiclesManagement.up = (Functional)
		(VMCommunicationProtocol.select = True) => (Other.select = True) and (VMCommunicationProtocol.up =(Functional))
	(SOAP.select = True or SSL.select = True) => (VMCommunicationProtocol.select = True)
		(SOAP.select = True => SOAP.up = (VMCommunicationProtocol))
		(SSL.select = True => SSL.up = (VMCommunicationProtocol))
	(NoSendAndReceive.select = True or Other.select = True) => not(NoSendAndReceive.select = True and Other.select = True)
		(NoSendAndReceive.select = True) => (NoSendAndReceive.up = (VehiclesManagement))
		(Other.select = True) => (Other.up = (VehiclesManagement))
	(PSCSendAndReceive.select = True or FSCSendAndReceive.select = True or PSCAndFSCSend.select = True or PSCReceive.select = True) => (Other.select = True)
	(PSCAndFSCSend.select = True) => (FSCSendAndReceive.select = True and PSCSendAndReceive.select = True)
		(PSCSendAndReceive.select = True) => (PSCSendAndReceive.up = (Other))
		(FSCSendAndReceive.select = True) => (FSCSendAndReceive.up = (Other))
		(PSCAndFSCSend.select = True) => (PSCAndFSCSend.up = (Other))
		(PSCReceive.select = True) => (PSCReceive.up = (Other))
}
fact {
	all f1,f2: Feature | f1 in f2.up => f1.select =True and bCMS.select = True
}

--A1
-- Check for inconsistency
run {SSL.select = True and Other.select = False}
--A2
-- Check for valid configuration
run {SSL.select = True and Other.select = True}
--A2
-- Check for invalid configuration
run { VMCommunicationProtocol.select = True and bCMS.select = False}
