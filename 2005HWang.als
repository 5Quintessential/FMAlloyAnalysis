module feature/FeatureModel
sig Feature {}
sig Concept extends Feature {
holds : set Feature
} { this in holds }
 
pred Mandatory[c: Concept, pf: Feature , s:set Feature]
{
                pf !in s implies
                ((pf in c.holds => all f:s | f in c.holds) or
                (pf !in c.holds => all f:s |f !in c.holds))
}

pred Optional[c: Concept, pf: Feature , s:set Feature]
{
                pf !in s implies
                (pf !in c.holds => all f:s |f !in c.holds)
}
 
pred Alternative[c: Concept, pf: Feature , s:set Feature]
{
                pf !in s implies
                (pf in c.holds => one f:s |f in c.holds) and
       	    (pf !in c.holds => all f:s |f !in c.holds)
}

pred Or[c: Concept, pf: Feature , s:set Feature]
{
                pf !in s implies
                (pf in c.holds => some f:s |f in c.holds) and
       	    (pf !in c.holds => all f:s |f !in c.holds)
}

pred OptionalAlternative[c: Concept, pf: Feature , s:set Feature]
{
                pf !in s implies
                ((pf in c.holds => one f:s |f in c.holds) or
                (all f:s | f !in c.holds)) and
       	    (pf !in c.holds => all f:s |f !in c.holds)
}

pred Requires[c: Concept, f1: Feature , s:set Feature]
{
                (f1 in c.holds) implies
                (all f2:s | f2 in c.holds)
}

pred Excludes[c: Concept, f1: Feature , s:set Feature]
{
                (f1 in c.holds) implies
                (all f2:s | f2 !in c.holds)
}

one sig bCMS extends Concept{}
one sig Functional extends Feature{}
one sig NonFunctional extends Feature {}
one sig DataCommConf, Encrypted, NotEncrypted extends Feature {}
one sig Authentication, PasswordBased, CertificateBased, BiometricBased, OneTimePwd, ChallengeResponse extends Feature {}
one sig SymmetricEncryption, MutualAuthorization, Kerberos extends Feature {}
one sig VehiclesManagement, VMCommunicationProtocol, CrisisMultiplicity extends Feature {}
one sig NoSendAndReceive, Other, SOAP, SSL, Single, Multiple extends Feature {}
one sig PSCSendAndReceive, FSCSendAndReceive, PSCAndFSCSend, PSCReceive extends Feature {}

fact{ Mandatory[bCMS,bCMS,(Functional+NonFunctional)] }
fact{ Mandatory[bCMS,NonFunctional,(DataCommConf)] }
fact{ Alternative[bCMS,DataCommConf,(Encrypted+NotEncrypted)] }
fact{ Optional[bCMS,NonFunctional,(Authentication)] }
fact{ Or[bCMS,Authentication,(PasswordBased+CertificateBased+BiometricBased+OneTimePwd+ChallengeResponse)] }
fact{ OptionalAlternative[bCMS,ChallengeResponse,(SymmetricEncryption+MutualAuthorization+Kerberos)] }
fact{ Optional[bCMS,Functional,(VehiclesManagement+VMCommunicationProtocol)] }
fact{ Mandatory[bCMS,Functional,(CrisisMultiplicity)] }
fact{ OptionalAlternative[bCMS,VehiclesManagement,(NoSendAndReceive+Other)] }
fact{ Optional[bCMS,Other,(PSCSendAndReceive+ FSCSendAndReceive+ PSCAndFSCSend+ PSCReceive)] }
fact{ Optional[bCMS,VMCommunicationProtocol,(SOAP+SSL)] }
fact{ Alternative[bCMS,CrisisMultiplicity,(Single+Multiple)] }
fact{ Requires[bCMS,VMCommunicationProtocol,(Other)] }
fact{ Requires[bCMS,PSCAndFSCSend,(PSCSendAndReceive+FSCSendAndReceive)] }

--A2
-- Checking a valid concept instance
assert Correctness1 { 
	one c:bCMS | c.holds = c+Functional+NonFunctional+DataCommConf+
	NotEncrypted+Authentication+PasswordBased+CertificateBased+
	BiometricBased+OneTimePwd+ChallengeResponse+SymmetricEncryption+
	VehiclesManagement+VMCommunicationProtocol+CrisisMultiplicity+Single+
	PSCSendAndReceive+ FSCSendAndReceive+ PSCAndFSCSend+ PSCReceive+
	Other+SOAP+SSL
} 
check Correctness1 for 25

-- Checking an invalid concept instance
assert Correctness2{ 
	all c:bCMS | c.holds != c+Functional+NonFunctional+DataCommConf+ Encrypted+
	NotEncrypted+Authentication+ PasswordBased+ CertificateBased+ BiometricBased+ 
	OneTimePwd+ ChallengeResponse+SymmetricEncryption+ MutualAuthorization+ Kerberos+
	VehiclesManagement+ VMCommunicationProtocol+ CrisisMultiplicity+NoSendAndReceive+ 
	Other+ SOAP+ SSL+ Single+ Multiple+PSCSendAndReceive+ FSCSendAndReceive+
	PSCAndFSCSend+ PSCReceive
}
check Correctness2 for 25

--A1
-- Checking solvability
pred findInstance[] {some bCMS}
run findInstance for 25

--A14
-- Checking for semantic equivalant models
assert Equivalent{ 
	(Alternative[bCMS, bCMS, (Functional+NonFunctional)] && 
	Optional[bCMS, NonFunctional, (Encrypted+NotEncrypted)]) <=> (Alternative[bCMS, bCMS, (Functional+NonFunctional)] && 
	Optional[bCMS,bCMS, (Encrypted+NotEncrypted)]&& Requires[bCMS, Encrypted, NonFunctional] && 
	Requires[bCMS, NotEncrypted ,NonFunctional])
}
check Equivalent for 5

-- Checking solvability
pred NoInstance[] {no SSL}
run NoInstance
