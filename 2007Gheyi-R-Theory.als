-- Encoding --
one sig FM {
	features: set Name
}
sig Name {}

pred mandatory(A,B:Name, config:set Name) { A in config <=> B in config }
pred alternative(A:Name,B: set Name, config:set Name) { A in config => (one b:B | b in config )}
pred orFeature(A,B,C:Name, config:set Name) { A in config <=> (B in config) or (C in config) }

-- Feature model encoding for bCMS --
one sig bCMS extends Name{}
one sig Functional extends Name{}
one sig NonFunctional extends Name {}
one sig DataCommConf, Encrypted, NotEncrypted extends Name {}
one sig Authentication, PasswordBased, CertificateBased, BiometricBased, OneTimePwd, ChallengeResponse extends Name {}
one sig SymmetricEncryption, MutualAuthorization, Kerberos extends Name {}
one sig VehiclesManagement, VMCommunicationProtocol, CrisisMultiplicity extends Name {}
one sig NoSendAndReceive, Other, SOAP, SSL, Single, Multiple extends Name {}
one sig PSCSendAndReceive, FSCSendAndReceive, PSCAndFSCSend, PSCReceive extends Name {}

fact
{	
	bCMS in FM.features
	mandatory[bCMS,Functional,FM.features]
	mandatory[bCMS,NonFunctional,FM.features]
	mandatory[NonFunctional,DataCommConf,FM.features]
	mandatory[Functional,CrisisMultiplicity,FM.features]
	orFeature[NonFunctional,Authentication,Authentication,FM.features]
	alternative[Authentication,( PasswordBased+ CertificateBased+BiometricBased + OneTimePwd + ChallengeResponse ),FM.features]
	alternative[ChallengeResponse,( SymmetricEncryption+ MutualAuthorization+Kerberos ),FM.features]
	alternative[DataCommConf,( Encrypted+ NotEncrypted ),FM.features]
	alternative[CrisisMultiplicity,( Single+ Multiple ),FM.features]
	orFeature[Functional,VehiclesManagement,VMCommunicationProtocol,FM.features]
	alternative[VehiclesManagement,( NoSendAndReceive+ Other ),FM.features]
	orFeature[VMCommunicationProtocol,SOAP,SSL,FM.features]
	mandatory[VMCommunicationProtocol,Other,FM.features]
	orFeature[Other,PSCSendAndReceive, FSCSendAndReceive,FM.features]
	orFeature[Other,PSCAndFSCSend, PSCReceive,FM.features]
	mandatory[PSCAndFSCSend,PSCSendAndReceive,FM.features]
	mandatory[PSCAndFSCSend,FSCSendAndReceive,FM.features]
}
pred show(){ some SSL } 
run show
