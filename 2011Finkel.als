sig 	Functional {}
sig NonFunctional{}
sig DataCommConf extends NonFunctional{}
sig Encrypted extends DataCommConf{}
sig NotEncrypted extends DataCommConf{}
sig Authentication extends NonFunctional{}
sig PasswordBased extends Authentication{}
sig CertificateBased extends Authentication{}
sig BiometricBased extends Authentication{}
sig OneTimePwd extends Authentication{}
sig ChallengeResponse extends Authentication{}
sig SymmetricEncryption extends ChallengeResponse{}
sig MutualAuthorization extends ChallengeResponse{}
sig Kerberos extends ChallengeResponse{}
sig VehiclesManagement extends Functional{}
sig VMCommunicationProtocol extends Functional{}
sig CrisisMultiplicity extends Functional{}
sig NoSendAndReceive extends VehiclesManagement{}
sig Other extends VehiclesManagement{}
sig SOAP extends VMCommunicationProtocol{}
sig SSL extends VMCommunicationProtocol{}
sig Single extends CrisisMultiplicity{}
sig Multiple extends CrisisMultiplicity{}
sig PSCSendAndReceive extends Other{}
sig FSCSendAndReceive extends Other{}
sig PSCAndFSCSend extends Other{}
sig PSCReceive extends Other{}

sig bCMS
{
	functional:lone Functional,
	nonfunctional:lone NonFunctional,
	datacommconf:lone DataCommConf,
	encrypted:one Encrypted,
	notencrypted:one NotEncrypted,
	single:one Single,
	multiple:one Multiple,
	authentication:some Authentication,
	passwordBased:some PasswordBased,
	certificateBased:some CertificateBased,
	biometricBased:some BiometricBased,
	oneTimePwd:some OneTimePwd,
	challengeResponse:some ChallengeResponse,
	symmetricEncryption:some SymmetricEncryption,
	mutualAuthorization:some MutualAuthorization,
	kerberos:some Kerberos,
	vehiclesManagement:some VehiclesManagement,
	vmcommunicationProtocol:some VMCommunicationProtocol,
	crisisMultiplicity:some CrisisMultiplicity,
	noSendAndReceive:some NoSendAndReceive,
	other:some Other,
	soap:some SOAP,
	ssl:some SSL,
	pscsendAndReceive:some PSCSendAndReceive,
	fscsendAndReceive:some FSCSendAndReceive,
	pscandFSCSend:some PSCAndFSCSend,
	pscreceive:some PSCReceive
}

fact
{
	all root:bCMS|
		{
		-- FUNCTIONAL
			(root.functional in CrisisMultiplicity)=>((one root.single) or (one root.multiple) and (not((one root.single) and (one root.multiple))))
			(root.functional in VMCommunicationProtocol)=>(((one root.soap) or (one root.ssl)) and (lone root.other))
			(root.functional in VehiclesManagement)=>((one root.noSendAndReceive) or (one root.other) or (no root.noSendAndReceive and no root.other))
			(root.other in PSCAndFSCSend)=>(lone root.pscsendAndReceive) and (lone root.fscsendAndReceive)					
		-- NON_FUNCTIONAL	
			(root.nonfunctional in DataCommConf)=>((one root.encrypted) or (one root.notencrypted) and (not((one root.encrypted) and (one root.notencrypted))))
			(root.nonfunctional in Authentication)=>((one root.passwordBased) or (one root.certificateBased) or (one root.biometricBased) or (one root.oneTimePwd) or (one root.challengeResponse))
			(root.authentication in ChallengeResponse)=>((one root.symmetricEncryption) or (one root.mutualAuthorization) or (one root.kerberos) and (no root.symmetricEncryption and no root.mutualAuthorization and no root.kerberos))
		}
}
--A2
-- Check for inconsistency
run {} for 1

--OptFet
-- Optional feature flaw (marked as optional in FM but found in all products)
pred OptFet
{
	all fm:bCMS| some fm.pscreceive
}
run OptFet
--A7
--DeadFet
-- Missing feature flaw (dead feature)
assert DeadFet
{ 
	all fm:bCMS| one fm.crisisMultiplicity
}
check DeadFet
