open util/boolean

abstract sig FM {
	features: set Name,
	root: features,
	relations: set Relation,
	forms: set Formula
}
sig Name {}

sig Relation {
	parent: Name,
	child: set Name,
	type: Type
}

abstract sig Type {}
one sig Optional, Mandatory, OrFeature, Alternative, OptionalAlternative, OptionalOr extends Type {}

abstract sig Formula { 
	satisfy: Configuration -> one Bool, 
	wt: FM -> one Bool
}

sig NameF extends Formula { n: Name}
sig Form extends Formula { f: Formula, g: Formula, op: Op}
abstract sig Op {} one sig AndF, OrF, ImpliesF, NotF extends Op {}

-- Generator axiom
sig Configuration {	value: set Name }
fact configDatatype { 
	--all n:set Name | some c:Configuration | c.value=n 
	all c1,c2: Configuration | c1 != c2 => c1.value != c2.value
}

pred satisfyRelations[fm:FM, c:Configuration] { 
	all r:fm.relations { 
		(r.type=Optional => (r.child in c.value => r.parent in c.value))
		(r.type=Mandatory => (r.child in c.value <=> r.parent in c.value))
		(r.type=Alternative => (r.parent in c.value => one n:r.child | n in c.value))
		(r.type=OrFeature => (r.parent in c.value => some n:r.child | n in c.value))
-- additional definitions in Ripon paper compared to Gheyi (modified by us)
		(r.type=OptionalAlternative => (r.parent in c.value => (one n:r.child |n in c.value) or (no n:r.child|n in c.value)))
		(r.type = OptionalOr => (r.parent in c.value => (some n:r.child|n in c.value) or (no n:r.child|n in c.value)))
-- direct encoding from Ripon paper [Not working]
		--(r.type=OptionalAlternative => (r.parent in c.value => (one n:r.child + no n:r.child) | n in c.value))
		--(r.type = OptionalOr => (r.parent in c.value => (some n:r.child + no n:r.child) | n in c.value))
		} 
}

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

one sig bCMSFM extends FM {} 
one sig  r1,r2,r3,r4,r5,r6,r7,r8,r9,r10,r11,r12,r13,r14,r15 extends Relation {} 

fact element { 
	bCMSFM.root = bCMS
	bCMSFM.features = bCMS+Functional+NonFunctional+DataCommConf+Encrypted+NotEncrypted+Authentication+ PasswordBased+CertificateBased+BiometricBased+OneTimePwd+ChallengeResponse+SymmetricEncryption+MutualAuthorization+Kerberos+VehiclesManagement+ VMCommunicationProtocol+CrisisMultiplicity+NoSendAndReceive+Other+SOAP+SSL+Single+ Multiple+PSCSendAndReceive+FSCSendAndReceive+PSCAndFSCSend+PSCReceive
	bCMSFM.relations = r1+r2+r3+r4+r5+r6+r7+r8+r9+r10+r11+r12+r13+r14+r15
}

fact relations { 
	r1.type = Mandatory 
	r1.parent = bCMS 
	r1.child = Functional+NonFunctional 
	r2.type = Optional 
	r2.parent = Functional 
	r2.child = VehiclesManagement+ VMCommunicationProtocol
	r3.type = Optional 
	r3.parent = NonFunctional 
	r3.child = Authentication
	r4.type = Mandatory 
	r4.parent = NonFunctional 
	r4.child = DataCommConf
	r5.type = Alternative 
	r5.parent = DataCommConf 
	r5.child = Encrypted+NotEncrypted
	r6.type = OptionalOr 
	r6.parent = Authentication 
	r6.child = PasswordBased+CertificateBased+BiometricBased+OneTimePwd+ChallengeResponse
	r7.type = Optional 
	r7.parent = ChallengeResponse 
	r7.child = SymmetricEncryption+MutualAuthorization+Kerberos
	r8.type = Alternative 
	r8.parent = ChallengeResponse 
	r8.child = SymmetricEncryption+MutualAuthorization+Kerberos
	r9.type = Mandatory 
	r9.parent = Functional 
	r9.child = CrisisMultiplicity
	r10.type = Alternative 
	r10.parent = CrisisMultiplicity 
	r10.child = Single+ Multiple
	r11.type = Optional 
	r11.parent = VMCommunicationProtocol 
	r11.child = SOAP+SSL
	r12.type = OptionalAlternative 
	r12.parent = VehiclesManagement 
	r12.child = NoSendAndReceive+Other
	r13.type = Alternative 
	r13.parent = VehiclesManagement 
	r13.child = NoSendAndReceive+Other
	r14.type = Optional 
	r14.parent = Other 
	r14.child = PSCSendAndReceive+FSCSendAndReceive+PSCAndFSCSend+PSCReceive
}
-- All the below property checks are giving incorrect results because of missing 
-- rules for parent child relationship and root feature

-- A1
-- Checking inconsistency in the FM
pred InconsistencyCheck{
	some c:Configuration | (CrisisMultiplicity not in c.value) and 
								(Multiple in c.value)
}
run InconsistencyCheck

-- A2
-- Validating if the configuration is valid for the given FM
pred ValidConfiguration{
	some c:Configuration | {bCMS+Functional+NonFunctional+
			DataCommConf+Encrypted+CrisisMultiplicity+Multiple} in c.value
}
run ValidConfiguration

-- A2
-- Validating if the configuration is invalid for the given FM
assert InvalidConfiguration{
		no c:Configuration | (bCMS not in c.value) and (Multiple in c.value)
}
check InvalidConfiguration
