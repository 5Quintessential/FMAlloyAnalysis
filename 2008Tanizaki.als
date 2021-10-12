//*************** Feature ***************// 
abstract sig Feature{}
abstract sig SchemaF { F : set Feature, rf : one Feature, ManF : set PCRelF, OptF : set PCRelF, AltF : set PCRelF, OrF : set PCRelF, ReqF : set RelF, MtxF : set RelF, structure : one Validity
}
abstract sig PCRelF { pF : one Feature, cF : set Feature, cause : set Cause, handling : set Handling, element : set Feature
}
abstract sig RelF { fF : one Feature, gF : set Feature, cause : set Cause, handling : set Handling, element : set Feature
}
abstract sig RequirementF { requiredF: set Feature, selection: one Validity
}
abstract sig InstanceF { configurationF : set Feature, inconsistentF : set (PCRelF + RelF), validity : one Validity, correctedF : set Feature
}
//*************** Module ***************// 
abstract sig Module{}
abstract sig InstanceM{configurationM: set Feature}
abstract sig RequirementM { requiredM: set Feature, selection: one Validity }
abstract sig Mf {Fins_M : set Module, validity : one Validity, diff : set Module}

//*************** Connection ***************// 
abstract sig Connection{f: one Feature, m: one Module, p: set Module }
abstract sig C { connectionFM : set Connection }

abstract sig Validity{}
one sig consistent, inconsistent, corrected, uncorrected extends Validity{}
abstract sig Cause{}
one sig lack_of_parent, lack_of_child, lack_of_required_element extends Cause{}
one sig excess_of_Alternative_element, mutex extends Cause{}
abstract sig Handling{}
one sig select_one, select_some, select_all, select_either extends Handling{}

// Schema structure check ***********************
fun Check_structureF[ s : SchemaF ] : Validity 
{
	acyclicF[s] => consistent else inconsistent 
}

pred acyclicF[ s : SchemaF ] {
	all feature : (s.F - s.rf) | #feature.~cF = 1 all pcr : (s.ManF + s.OptF + s.AltF + s.OrF)| s.rf !in pcr.cF
	all cr : (s.ReqF + s.MtxF) | s.rf !in cr.gF all ma : s.ManF | #ma.cF >= 1
	all op : s.OptF | #op.cF = 1
	all altor : (s.AltF + s.OrF) | #altor.cF > 1 all rel : (s.ReqF + s.MtxF) | #rel.gF >= 1
}

// Requirement check ***************************** 
fun Check_requirementF[ s : SchemaF, r : RequirementF ] : Validity {
	(r.requiredF in s.F and r.requiredF != none) => consistent else inconsistent
}
// Restrictions ******************************
pred RestrictionF [ s : SchemaF, i : InstanceF] {
all ma : s.ManF | (ma.pF in i.configurationF<=> ma.cF in i.configurationF)
all op : s.OptF | (op.cF in i.configurationF => op.pF in i.configurationF)
all al : s.AltF | ((al.pF in i.configurationF <=> one n : al.cF | n in i.configurationF)
	and #(al.cF & i.configurationF) =< 1)
all orf : s.OrF | (orf.pF in i.configurationF <=> #(orf.cF & i.configurationF) > 0)
all re : s.ReqF | re.fF in i.configurationF => re.gF in i.configurationF
all mt : s.MtxF | !(mt.fF in i.configurationF and mt.gF in i.configurationF)
}

pred correct_configurationF[ s : SchemaF, i : InstanceF ] 
{
	// Alternative
	all al : s.AltF | ((al.pF !in i.configurationF and #(al.cF & i.configurationF) = 1) --(1)
	=> (al in i.inconsistentF
		and lack_of_parent = al.cause
		and select_one = al.handling
		and al.pF in al.element
		and al.pF in i.correctedF)
	else (al.pF in i.configurationF and #(al.cF & i.configurationF) = 0) --(2)
	=> (al in i.inconsistentF 
		and lack_of_child = al.cause 
		and select_one = al.handling
		and al.cF in al.element
		and one n : al.cF | n in i.correctedF)
	else (al.pF in i.configurationF
		and #(al.cF & i.configurationF) > 1) --(3)
	=> (al in i.inconsistentF 
		and excess_of_Alternative_element = al.cause 
		and select_one = al.handling
		and al.cF in al.element 
		and one n : al.cF | n in i.correctedF)
	else (al.pF !in i.configurationF
		and #(al.cF & i.configurationF) != 0) --(4)
	=> (al in i.inconsistentF
		and excess_of_Alternative_element +lack_of_parent = al.cause
		and select_one = al.handling 
		and al.cF+al.pF in al.element 
		and al.pF in i.correctedF
		and one n : al.cF | n in i.correctedF)
	else al !in i.inconsistentF) and
		(al.pF in i.configurationF
		and #(al.cF & i.configurationF) = 1
	=> al.pF in i.correctedF
		and (i.configurationF & al.cF in i.correctedF
		or one n : al.cF | n in i.correctedF))
}

pred Val_connection[fi:InstanceF,mi:InstanceM,mf:Mf] 
{
	mf.Fins_M = C_InstanceF[fi]
	mf.validity = SubsetM[mi, mf]
	--mf.diff = mf.Fins_M - mi.configurationM
}
// C(InstanceF)
fun C_InstanceF[ i : InstanceF ] : set Module {
	f.(i.configurationF).m + f.(i.configurationF).p
}
// Check whether Mf is a subset of InstanceM
fun SubsetM[insM:InstanceM,CinsF:Mf]:set Validity {
	--(CinsF.Fins_M in insM.configurationM) => 
     inconsistent
}

-- FM of bCMS --
sig bCMS,Functional,NonFunctional,DataCommConf,Encrypted,NotEncrypted,Authentication, PasswordBased,CertificateBased,BiometricBased,OneTimePwd,ChallengeResponse,SymmetricEncryption,MutualAuthorization,Kerberos,VehiclesManagement, VMCommunicationProtocol,CrisisMultiplicity,NoSendAndReceive,Other,SOAP,SSL,Single, Multiple,PSCSendAndReceive,FSCSendAndReceive,PSCAndFSCSend,PSCReceive extends Feature{}
sig config extends SchemaF{}
sig G1,G4,G5,G6,G7,G8,G9,G10,G11,G12,G13,G14 extends PCRelF{}

--A2
-- Valid instance checking against inconsistency
pred FMBCMSInvalid{
	config.F = (bCMS+Functional+NonFunctional+
	DataCommConf+Encrypted+NotEncrypted+
	Authentication+ PasswordBased+CertificateBased+
	BiometricBased+OneTimePwd+ChallengeResponse+
	SymmetricEncryption+MutualAuthorization+Kerberos+
	VehiclesManagement+ VMCommunicationProtocol+
	CrisisMultiplicity+NoSendAndReceive+Other+SOAP+
	SSL+Single+ Multiple+PSCSendAndReceive+
	FSCSendAndReceive+PSCAndFSCSend+PSCReceive)
	config.rf=bCMS
	G1.pF=bCMS
	G1.cF=(Functional+NonFunctional)	
	G4.pF=NonFunctional
	G4.cF=Authentication
	G5.pF=NonFunctional
	G5.cF=DataCommConf
	G6.pF=Authentication
	G6.cF=(PasswordBased+CertificateBased+BiometricBased+OneTimePwd+ChallengeResponse)
	G7.pF=DataCommConf
	G7.cF=(Encrypted+NotEncrypted)
	G8.pF=ChallengeResponse
	G8.cF=(SymmetricEncryption+MutualAuthorization+Kerberos)
	G9.pF=Functional
	G9.cF=(VehiclesManagement+ VMCommunicationProtocol)
	G10.pF=Functional
	G10.cF=CrisisMultiplicity
	G11.pF=VehiclesManagement
	G11.cF=(NoSendAndReceive+Other)
	G12.pF=VMCommunicationProtocol
	G12.cF=SOAP+SSL
	G13.pF=CrisisMultiplicity
	G13.cF=Single+ Multiple
	G14.pF=Other
	G14.cF=(PSCSendAndReceive+FSCSendAndReceive+PSCAndFSCSend+PSCReceive)

	config.ManF= (G1+G5+G10)
	config.AltF= (G7+G8+G13+G11)
	config.OptF=(G4+G6+G9+G12+G14)
	config.structure = inconsistent -- It is a consistent model, but we check for inconsistency
} 
run FMBCMSInvalid

--A2
-- Valid instance
pred FMBCMS{
	config.F = (bCMS+Functional+NonFunctional+DataCommConf+Encrypted+
	NotEncrypted+Authentication+ PasswordBased+CertificateBased+
	BiometricBased+OneTimePwd+ChallengeResponse+SymmetricEncryption+
	MutualAuthorization+Kerberos+VehiclesManagement+ VMCommunicationProtocol+
	CrisisMultiplicity+NoSendAndReceive+Other+SOAP+SSL+Single+ Multiple+
	PSCSendAndReceive+FSCSendAndReceive+PSCAndFSCSend+PSCReceive)
	config.rf=bCMS
	G1.pF=bCMS
	G1.cF=(Functional+NonFunctional)
	config.ManF = G1
	config.structure = consistent -- It is consistent and we check for the same
} 
run FMBCMS
