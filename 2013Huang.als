-- Feature
abstract sig Feature { up : Feature, select : Selected }
abstract sig Selected {} 
sig Yes, No extends Selected {} 

one sig bCMS extends Feature{}
one sig Functional extends Feature{}
one sig NonFunctional extends Feature {}
one sig DataCommConf, Encrypted, NotEncrypted extends Feature {}
one sig Authentication, PasswordBased, CertificateBased, BiometricBased, OneTimePwd, ChallengeResponse extends Feature {}
one sig SymmetricEncryption, MutualAuthorization, Kerberos extends Feature {}
one sig VehiclesManagement, VMCommunicationProtocol, CrisisMultiplicity extends Feature {}
one sig NoSendAndReceive, Other, SOAP, SSL, Single, Multiple extends Feature {}
one sig PSCSendAndReceive, FSCSendAndReceive, PSCAndFSCSend, PSCReceive extends Feature {}

-- Encoding
fact {
	(bCMS.select=Yes)
	(bCMS.select=Yes) => ((Functional.select=Yes) and (NonFunctional.select=Yes) and (Functional.up = bCMS and NonFunctional.up = bCMS))
	(Functional.select=Yes) => (CrisisMultiplicity.select = Yes) and (CrisisMultiplicity.up = Functional)
	(CrisisMultiplicity.select = Yes) => (Single.select=Yes or Multiple.select=Yes) and (not(Single.select=Yes and Multiple.select=Yes)) and (not(Single.select=No and Multiple.select=No))
	(Single.select=Yes) => (Single.up=CrisisMultiplicity)
	(Multiple.select=Yes) => (Multiple.up=CrisisMultiplicity)
	(NonFunctional.select=Yes) => (DataCommConf.select = Yes) and (DataCommConf.up = NonFunctional)
	(DataCommConf.select = Yes) => ((Encrypted.select=Yes or NotEncrypted.select=Yes) and (not(Encrypted.select=Yes and NotEncrypted.select=Yes)) and (not(Encrypted.select=No and NotEncrypted.select=No)))
	(Encrypted.select=Yes)=>(Encrypted.up=DataCommConf)
	(NotEncrypted.select=Yes)=>(NotEncrypted.up=DataCommConf)
	(VehiclesManagement.select=Yes) => (VehiclesManagement.up = Functional) and (NoSendAndReceive.select=Yes or Other.select=Yes) and (not(NoSendAndReceive.select=Yes and Other.select=Yes))
	(VMCommunicationProtocol.select=Yes) => (VMCommunicationProtocol.up = Functional) and (Other.select=Yes) and (SOAP.select=Yes or SSL.select=Yes)
	(Other.select=Yes) => (Other.up=VehiclesManagement) and (PSCSendAndReceive.select=Yes or FSCSendAndReceive.select=Yes or PSCAndFSCSend.select=Yes or PSCReceive.select=Yes)
	(NoSendAndReceive.select=Yes) => (NoSendAndReceive.up=VehiclesManagement)
	(PSCSendAndReceive.select=Yes) =>  (PSCSendAndReceive.up=Other)
	(FSCSendAndReceive.select=Yes) => (FSCSendAndReceive.up=Other)
	(PSCAndFSCSend.select=Yes) => (PSCAndFSCSend.up=Other) and (PSCSendAndReceive.select=Yes) and (FSCSendAndReceive.select=Yes)
	(PSCReceive.select=Yes) => (PSCReceive.up=Other)
	(SOAP.select=Yes) => (SOAP.up=VMCommunicationProtocol)
	(SSL.select=Yes) => (SSL.up=VMCommunicationProtocol)
	(Authentication.select=Yes)=>(Authentication.up=NonFunctional) and (PasswordBased.select=Yes or CertificateBased.select=Yes or BiometricBased.select=Yes or OneTimePwd.select=Yes or ChallengeResponse.select=Yes)
	(PasswordBased.select=Yes)=>(PasswordBased.up=Authentication)
	(CertificateBased.select=Yes)=>(CertificateBased.up=Authentication)
	(BiometricBased.select=Yes)=>(BiometricBased.up=Authentication)
	(OneTimePwd.select=Yes)=>(OneTimePwd.up=Authentication)
	(ChallengeResponse.select=Yes)=>(ChallengeResponse.up=Authentication) and ((SymmetricEncryption.select=Yes or MutualAuthorization.select=Yes or Kerberos.select=Yes) and (not(SymmetricEncryption.select=Yes and MutualAuthorization.select=Yes and Kerberos.select=Yes)) )
	(SymmetricEncryption.select=Yes)=>(SymmetricEncryption.up=ChallengeResponse) and(MutualAuthorization.select=No and Kerberos.select=No)
	(MutualAuthorization.select=Yes)=>(MutualAuthorization.up=ChallengeResponse) and(SymmetricEncryption.select=No and Kerberos.select=No)
	(Kerberos.select=Yes)=>(Kerberos.up=ChallengeResponse) and(MutualAuthorization.select=No and SymmetricEncryption.select=No)
}

run { bCMS.select=Yes }

--A1
-- inconsistency
pred A1 { VMCommunicationProtocol.select = Yes and Functional.select = Yes} run A1
--A2
-- invalid configuration
pred A2 { PSCAndFSCSend.select=Yes and FSCSendAndReceive.select=No} run A2
--A2
-- valid configuration
pred A2_Valid { SOAP.select=Yes and Other.select=Yes and VehiclesManagement.select=Yes } run A2_Valid
