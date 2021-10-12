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
one sig Optional, Mandatory, OrFeature, Alternative extends Type {}

abstract sig Formula { 
	satisfy: Configuration -> one Bool, 
	wt: FM -> one Bool
}

sig NameF extends Formula { n: Name}
sig Form extends Formula { f: Formula, g: Formula, op: Op}
abstract sig Op {} one sig AndF, OrF, ImpliesF, NotF extends Op {}

pred wellFormed(fm:FM) { 
	wellFormedRel[fm] 
	all f:fm.forms | f.wt[fm] = True
}

pred wellFormedRel(fm:FM) { 
	all r:fm.relations {
	r.parent+r.child in fm.features
	r.type in Optional+Mandatory => #r.child=1
	r.type in Alternative+OrFeature => #r.child>1
	-- Missing the constraint stating that all relations of a FM
	-- represent a tree.
	} 
}

fact FormulaConstruction { 
	all form:Form | form !in form.^(f+g)
	all fm:FM 
		{ 
			all f:NameF | f.wt[fm] = satisfyNameWT[f,fm] 
			all f:Form | f.wt[fm] = satisfyFormWT[f,fm]
		} 
}

fun satisfyNameWT[form:NameF, fm:FM]: Bool { 
	(form.n in fm.features) => True else False
}

fun satisfyFormWT[form:Form, fm:FM]: Bool { 
	(form.op=NotF) => form.f.wt[fm]
	else And[form.f.wt[fm],form.g.wt[fm]] 
}

-- Generator axiom
sig Configuration { value: set Name }
fact configDatatype { 
	--all n:set Name | some c:Configuration | c.value=n 
	all c1,c2: Configuration | c1 != c2 => c1.value != c2.value
}

fun semantics(fm:FM): set Configuration { 
	{ 
		c:Configuration | satisfyRelations[fm,c] and 
								   satImpConst[fm,c] and 
 								   satExpConst[fm,c]
	} 
}

pred satisfyRelations[fm:FM, c:Configuration] { 
	all r:fm.relations { 
		(r.type=Optional => (r.child in c.value => r.parent in c.value))
		(r.type=Mandatory => (r.child in c.value <=> r.parent in c.value))
		(r.type=Alternative => (r.parent in c.value => one n:r.child | n in c.value))
		(r.type=OrFeature => (r.parent in c.value => some n:r.child | n in c.value))
		} 
}

pred satImpConst[fm:FM, c:Configuration] { fm.root in c.value and c.value in fm.features }

pred satExpConst[fm:FM, c:Configuration] { all f:fm.forms | f.satisfy[c] = True }

fact FormulaSatisfaction { 
	all c: Configuration { 
		all f: NameF | f.satisfy[c] = satisfyName[f,c] 
		all f: Form | f.satisfy[c] = satisfyForm[f,c]
	} 
}

fun satisfyName[f:NameF, c:Configuration]: Bool { (f.n in c.value) => True else False}

fun satisfyForm[f:Form, c:Configuration]: Bool { 
	(f.op = AndF) => satisfyAnd[f,c] else 
	(f.op = NotF) => satisfyNot[f,c] else  
	(f.op = OrF) => satisfyOr[f,c] else 
	satisfyImplies[f,c]
}

fun satisfyAnd[form:Form, c:Configuration]: Bool { 
	And[form.f.satisfy[c],form.g.satisfy[c]]
}

fun satisfyOr[form:Form, c:Configuration]: Bool { 
	Or[form.f.satisfy[c],form.g.satisfy[c]]
}

fun satisfyImplies[form:Form, c:Configuration]: Bool { 
	((form.f.satisfy[c] = True) =>  (form.g.satisfy[c]=True)) => True else False
}

fun satisfyNot[form:Form, c:Configuration]: Bool { 
	Not[form.f.satisfy[c]]
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
one sig f1,f2,f3 extends Form {}
one sig f4,f5,f6,f7,f8,f9 extends NameF {}

fact elements { 
	bCMSFM.root = bCMS
	bCMSFM.features = bCMS+Functional+NonFunctional+DataCommConf+Encrypted+NotEncrypted+Authentication+ PasswordBased+CertificateBased+BiometricBased+OneTimePwd+ChallengeResponse+SymmetricEncryption+MutualAuthorization+Kerberos+VehiclesManagement+ VMCommunicationProtocol+CrisisMultiplicity+NoSendAndReceive+Other+SOAP+SSL+Single+ Multiple+PSCSendAndReceive+FSCSendAndReceive+PSCAndFSCSend+PSCReceive
	bCMSFM.relations = r1+r2+r3+r4+r5+r6+r7+r8+r9+r10+r11+r12+r13+r14+r15
	bCMSFM.forms = f1+f2+f3
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
	r6.type = OrFeature 
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
	r12.type = Optional 
	r12.parent = VehiclesManagement 
	r12.child = NoSendAndReceive+Other
	r13.type = Alternative 
	r13.parent = VehiclesManagement 
	r13.child = NoSendAndReceive+Other
	r14.type = Optional 
	r14.parent = Other 
	r14.child = PSCSendAndReceive+FSCSendAndReceive+PSCAndFSCSend+PSCReceive
}

fact formulas { 
	f1.op = ImpliesF 
	f1.f = f4 
	f1.g = f5
	f4.n = VMCommunicationProtocol 
	f5.n = Other
	f2.op = ImpliesF 
	f2.f = f6 
	f2.g = f7
	f6.n = PSCAndFSCSend 
	f7.n = FSCSendAndReceive
	f3.op = ImpliesF
	f3.f = f8
	f3.g = f9
	f8.n = PSCAndFSCSend 
	f9.n = PSCSendAndReceive
}

fact allConfigurationsValid {
   all c: Configuration | c in show[]
}

--A7 
-- Check for dead features
assert deadFeatureCheck{
	some name:bCMSFM.features | no config:Configuration | name in config.value
}
check deadFeatureCheck

--A2 
-- Check if configuration is valid
pred checkValidConfig{
	some config:Configuration| ((bCMS+Functional+NonFunctional+
	CrisisMultiplicity+Multiple+DataCommConf+Encrypted) in bCMSFM.features) and 
	((bCMS+Functional+NonFunctional+CrisisMultiplicity+Multiple+DataCommConf+Encrypted) in config.value)
}
run checkValidConfig

--A4 
-- Finding all configurations
fun show():set Configuration { 
	semantics[bCMSFM]
}
run show for 1 FM, 28 Name, 3 Formula, 15 Relation, 5 Configuration --> 2^28 configurations [268435456]

