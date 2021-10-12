sig FM {
features : set Name ,
root : one features ,
relations : features lone -> features ,
types : features -> FeatureType ,
groupTypes : features -> one GroupType ,
requires : features -> features ,
excludes : features -> features ,
}
sig Name {}
abstract sig FeatureType {}
one sig Mandatory , NonSelectable , Optional extends FeatureType {}
abstract sig GroupType {}
one sig OrFeatureGroup , Alternative , Aggregation extends GroupType {}

pred wellFormedFM ( fm : FM ) {
all f:fm. features - fm. root
| f in (fm. root ).^( fm. relations )
no f:fm. features
| f in f .^( fm. relations )
no f:fm. features | f in fm. requires [f]
no f:fm. features | f in fm. excludes [f]
no f:fm. features
| fm. groupTypes [f] in Alternative + OrFeatureGroup
and #fm. relations [f]<=1
}

sig Configuration {
value : set Name
}

pred isValid ( fm : FM , c : Configuration ) {
satisfyImplicitConstraints [ fm , c ]
and satisfyExplicitConstraints [ fm , c ]
and satisfyRelations [ fm , c ]
and satisfyGroupTypes [ fm , c ]
and satisfyFeatureTypes [ fm , c ]
}

pred satisfyImplicitConstraints
( fm : FM , c : Configuration ) {
fm. root in c. value
c. value in fm. features
}

pred satisfyExplicitConstraints
( fm : FM , c : Configuration ) {
all f : c. value {
fm. requires [ f ] in c. value
fm. excludes [ f ] != none
=> ( fm. excludes [ f ] !in c. value )
}
}

pred satisfyRelations ( fm : FM , c : Configuration ) {
no f : c. value |
fm. relations .(f) !in c. value
}

pred satisfyGroupTypes ( fm : FM , c : Configuration ) {
no f : c. value {
fm. groupTypes [f] = Alternative
and #( fm. relations [f] & c. value ) != 1
}
no f : c. value {
fm. groupTypes [f] = OrFeatureGroup
#( fm. relations [f] & c. value ) = 0
}
}

pred satisfyFeatureTypes ( fm : FM , c : Configuration ) {
no f : c. value
| NonSelectable in fm. types [ f ]
no disj f : c.value , f' : fm. features {
f' in fm. relations [ f ]
Mandatory in fm. types [ f ]
f' !in c. value
}
}

fun semantics ( fm : FM ) : set Configuration {
{ c : Configuration | isValid [ fm , c ] }
}

fun deadFeatures ( fm: FM ) : set Name {
{ f: Name |
all c : semantics [ fm ] |
f !in c.value
}
}
fun fullMandatories ( fm: FM ) : set Name {
fm. root .^( fm. relations :> fm. types .( Mandatory ) )
}

fun conflictingFeatures ( fm : FM ) : set Name {
{ f : fullMandatories [ fm ] |
NonSelectable in fm. types [ f ] }
}

sig FSGraph {
source : FM ,
target : FM ,
forces : Name -> Name ,
suggests : Name -> Name ,
prohibits : Name -> Name ,
}

pred wellFormedFSGraph ( fsg : FSGraph ) {
wellFormedFM [ fsg . source ]
wellFormedFM [ fsg . target ]
no f : Name , f' : fsg . forces [ f ] |
f !in fsg . source . features
and f' !in fsg . target . features
no f : Name , f' : fsg . suggests [ f ] |
f !in fsg . source . features
and f' !in fsg . target . features
no f : Name , f' : fsg . prohibits [ f ] |
f !in fsg . source . features
and f' !in fsg . target . features
}

pred appliedFSGraphToFM
( c : Configuration , fsg : FSGraph , fm , fm' : FM) {
fm'. root = fm. root
fm'. features = fm. features
fm'. relations = fm. relations
fm'. types = fm. types
+ { f : fsg . forces [ c. value ],
type : Mandatory }
+ { f : fsg . target . features ,
type : Mandatory
| some g : Name
| g in fsg . forces [ c. value ]
and (f in ancestors [ fsg. target , g])
}
+ { f : fsg . suggests [ c. value ],
type : Mandatory }
+ { f : fsg . prohibits [ c. value ],
type : NonSelectable }
fm'. groupTypes = fm. groupTypes
fm'. requires = fm. requires
fm'. excludes = fm. excludes
}

fun ancestors ( fm : FM , f : Name ) : set Name {
{f' : fm. features | f in f'.^( fm. relations ) }
}

pred convertForcesIntoSuggests
( c : Configuration , fsg , fsg' : FSGraph ) {
fsg'. source = fsg . source
fsg'. target = fsg . target
fsg'. forces = c. value <: fsg . forces
fsg'. suggests = c. value <: fsg . suggests
+ { x : c.value , f : fsg. target . features | f in fsg . forces [ x ] }
+ { x : c.value , f : fsg. target . features
| some g : Name
| g in fsg . forces [ x ]
and ( f in ancestors [ fsg . target , g]) }
fsg'. prohibits = c. value <: fsg . prohibits
}

pred appliedEffectsIntoFM ( c : Configuration ,
fsg : FSGraph , fm , fm' : FM ) {
all t : c.value , f : fsg. suggests [ t ] {
Mandatory in fm'. types [ f ]
(f-> Alternative) in fm. groupTypes 
=> all f' : fm.relations[f] |
NonSelectable in fm'. types [ f' ]
}
all t : c.value , f : fsg. prohibits [ t ] {
NonSelectable in fm'. types [ f ]
all f' : fm.relations[f] |
NonSelectable in fm'. types [ f' ]
all f' : fm.requires [ f ] |
NonSelectable in fm'. types [ f' ]
}
}

pred appliedEffectsIntoFSG ( c : Configuration ,
fsg , fsg' : FSGraph ) {
let fm = fsg . target {
all t : c.value , f : fsg. suggests [ t ] {
(f-> Alternative) in fm. groupTypes 
=> {
all f' :  fm.features | 
t -> f' in fsg'. prohibits }
}
all t : c.value , f : fsg. prohibits [ t ] {
all  f' : fm.relations[f] |
t -> f' in fsg'. prohibits
all f' : fm.requires [ f ] |
t -> f' in fsg'. prohibits
}
}
}
pred propagatedDecisionsIntoFM ( c : Configuration ,
fsg : FSGraph , fm , fm' : FM ) {
all f : fm. features
| fm. groupTypes [f] = Alternative
and #(  fm.relations[f]
& fm. types .( Mandatory )) > 1
=> NonSelectable in fm'. types [ f ]
all f : fm. features
| fm. groupTypes [f]
in ( Alternative + OrFeatureGroup )
and #( fm.relations[f] & fm. types .( NonSelectable ) )
= # fm.relations[f]
=> NonSelectable in fm'. types [ f ]
all f : fullMandatories [ fm ] |
all f' : fm.excludes [ f ]
| NonSelectable in fm'. types [ f' ]
all f : fullMandatories [ fm ] |
all f' : fm. requires [f]
| f' in fullMandatories [ fm' ]
all f : fm. features
| fm. groupTypes [f] in ( Aggregation )
and # fm.relations[f]>= 1
and #(fm.relations[f] & fm. types .( Mandatory ) &
fm. types .( NonSelectable )) = # fm.relations[f]
=> NonSelectable in fm'. types [ f ]
}

pred propagatedDecisionsIntoFSGraph
( c : Configuration , fsg , fsg' : FSGraph ) {
let fm = fsg . target {
all f : fm. features
| fm. groupTypes [f] = Alternative
and #( fm.relations[f]
& fm. types .( Mandatory )) > 1
=> {
all t :
fsg . suggests .( fm.relations[f]
& fm. types .( Mandatory ))
| t -> f in fsg'. prohibits
}
all f : fm. features
| fm. groupTypes [f]
in ( Alternative + OrFeatureGroup )
and #(fm.relations[f]
& fm. types .( NonSelectable ))
= # fm.relations[f]
=> {
all t :
fsg . prohibits .(fm.relations[f])
| t -> f in fsg'. prohibits
}
all f : fullMandatories [ fm ] {
all f' : fm.excludes [ f ] ,
t : fsg'. suggests .(f)
| t -> f' in fsg'. prohibits
}
all f : fullMandatories [ fm ] {
all f' : fm. requires [ f ],
t : fsg'. suggests .(f)
| t -> f' in fsg'. suggests
}
}
}

fun conflicts ( fsg : FSGraph ) : set Name {
conflictingFeatures [ fsg . target ]
}

fun causes ( fsg : FSGraph , f : Name ) : Name {
{ g : fsg . source . features |
f in fsg. suggests [ g ]
or f in fsg . prohibits [ g ]
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

one sig bCMSFM extends FM { } 
one sig targetFM extends FM { } 

one sig bCMSGraph extends FSGraph { }

fact FMM{
bCMSFM.features = bCMS+Functional+NonFunctional+DataCommConf+Encrypted+NotEncrypted+Authentication+ PasswordBased+CertificateBased+BiometricBased+OneTimePwd+ChallengeResponse+SymmetricEncryption+MutualAuthorization+Kerberos+VehiclesManagement+ VMCommunicationProtocol+CrisisMultiplicity+NoSendAndReceive+Other+SOAP+SSL+Single+ Multiple+PSCSendAndReceive+FSCSendAndReceive+PSCAndFSCSend+PSCReceive

bCMSFM.relations = bCMSFM.relations+ bCMS->(Functional+NonFunctional) 
bCMSFM.relations = bCMSFM.relations+ Functional->(VehiclesManagement+ VMCommunicationProtocol) 
bCMSFM.relations = bCMSFM.relations+ NonFunctional->(Authentication) 
bCMSFM.relations = bCMSFM.relations+ NonFunctional->(DataCommConf) 
bCMSFM.relations = bCMSFM.relations+ DataCommConf->(Encrypted+NotEncrypted) 
bCMSFM.relations = bCMSFM.relations+ Authentication->(PasswordBased+CertificateBased+BiometricBased+OneTimePwd+ChallengeResponse) 
bCMSFM.relations = bCMSFM.relations+ ChallengeResponse->(SymmetricEncryption+MutualAuthorization+Kerberos) 
bCMSFM.relations = bCMSFM.relations+ Functional->(CrisisMultiplicity) 
bCMSFM.relations = bCMSFM.relations+ CrisisMultiplicity->(Single+ Multiple) 
bCMSFM.relations = bCMSFM.relations+ VMCommunicationProtocol->(SOAP+SSL) 
bCMSFM.relations = bCMSFM.relations+ VehiclesManagement->(NoSendAndReceive+Other) 
bCMSFM.relations = bCMSFM.relations+ Other->(PSCSendAndReceive+FSCSendAndReceive+PSCAndFSCSend+PSCReceive) 

bCMSFM.root = bCMS

bCMSFM.types = bCMSFM.types + bCMS->Mandatory
bCMSFM.types = bCMSFM.types + Functional->Mandatory
bCMSFM.types = bCMSFM.types + NonFunctional->Mandatory
bCMSFM.types = bCMSFM.types + DataCommConf->Mandatory
bCMSFM.types = bCMSFM.types + Encrypted->Mandatory
bCMSFM.types = bCMSFM.types + NotEncrypted->Mandatory
//bCMSFM.types = bCMSFM.types + Encrypted->NonSelectable
//bCMSFM.types = bCMSFM.types + NotEncrypted->NonSelectable
bCMSFM.types = bCMSFM.types + Authentication->Optional
bCMSFM.types = bCMSFM.types + PasswordBased->Optional
bCMSFM.types = bCMSFM.types + CertificateBased->Optional
bCMSFM.types = bCMSFM.types + BiometricBased->Optional
bCMSFM.types = bCMSFM.types + OneTimePwd->Optional
bCMSFM.types = bCMSFM.types + ChallengeResponse->Optional
//bCMSFM.types = bCMSFM.types + PasswordBased->NonSelectable
//bCMSFM.types = bCMSFM.types + CertificateBased->NonSelectable
//bCMSFM.types = bCMSFM.types + BiometricBased->NonSelectable
//bCMSFM.types = bCMSFM.types + OneTimePwd->NonSelectable
//bCMSFM.types = bCMSFM.types + ChallengeResponse->NonSelectable
bCMSFM.types = bCMSFM.types + SymmetricEncryption->Optional
bCMSFM.types = bCMSFM.types + MutualAuthorization->Optional
bCMSFM.types = bCMSFM.types + Kerberos->Optional
bCMSFM.types = bCMSFM.types + VehiclesManagement->Optional
bCMSFM.types = bCMSFM.types + VMCommunicationProtocol->Optional
bCMSFM.types = bCMSFM.types + CrisisMultiplicity->Mandatory
bCMSFM.types = bCMSFM.types + NoSendAndReceive->Optional
bCMSFM.types = bCMSFM.types + Other->Optional
bCMSFM.types = bCMSFM.types + SOAP->Optional
bCMSFM.types = bCMSFM.types + SSL->Optional
bCMSFM.types = bCMSFM.types + Single->Mandatory
bCMSFM.types = bCMSFM.types + Multiple->Mandatory
bCMSFM.types = bCMSFM.types + PSCSendAndReceive->Optional
bCMSFM.types = bCMSFM.types + FSCSendAndReceive->Optional
bCMSFM.types = bCMSFM.types + PSCAndFSCSend->Optional
bCMSFM.types = bCMSFM.types + PSCReceive->Optional

bCMSFM.groupTypes = bCMSFM.groupTypes + (PasswordBased+CertificateBased+BiometricBased+OneTimePwd+ChallengeResponse)->OrFeatureGroup
bCMSFM.groupTypes = bCMSFM.groupTypes + (Encrypted+NotEncrypted)->Alternative
bCMSFM.groupTypes = bCMSFM.groupTypes + (SymmetricEncryption+MutualAuthorization+Kerberos)->Alternative
bCMSFM.groupTypes = bCMSFM.groupTypes + (NoSendAndReceive+Other)->Alternative
bCMSFM.groupTypes = bCMSFM.groupTypes + (Single+ Multiple)->Alternative

bCMSFM.requires = bCMSFM.requires + (VMCommunicationProtocol->Other)
bCMSFM.requires = bCMSFM.requires + (PSCAndFSCSend->(PSCSendAndReceive+FSCSendAndReceive))

bCMSGraph.source = bCMSFM
bCMSGraph.target = targetFM
bCMSGraph.forces = bCMSGraph.forces + (bCMS->Functional )
bCMSGraph.forces = bCMSGraph.forces + (bCMS->NonFunctional)
bCMSGraph.forces = bCMSGraph.forces + (NonFunctional->DataCommConf)
bCMSGraph.forces = bCMSGraph.forces + (Functional->CrisisMultiplicity)
bCMSGraph.forces = bCMSGraph.forces + (VMCommunicationProtocol->Other)
bCMSGraph.forces = bCMSGraph.forces + (PSCAndFSCSend->PSCSendAndReceive)
bCMSGraph.forces = bCMSGraph.forces + (PSCAndFSCSend->FSCSendAndReceive)

bCMSGraph.suggests = bCMSGraph.suggests + (Functional->VehiclesManagement)
bCMSGraph.suggests = bCMSGraph.suggests + (Functional->VMCommunicationProtocol)
bCMSGraph.suggests = bCMSGraph.suggests + (VehiclesManagement -> NoSendAndReceive)
bCMSGraph.suggests = bCMSGraph.suggests + (VehiclesManagement -> Other)
bCMSGraph.suggests = bCMSGraph.suggests + (DataCommConf->Encrypted)
bCMSGraph.suggests = bCMSGraph.suggests + (DataCommConf->NotEncrypted)
bCMSGraph.suggests = bCMSGraph.suggests + (Authentication->PasswordBased)
bCMSGraph.suggests = bCMSGraph.suggests + (Authentication->CertificateBased)
bCMSGraph.suggests = bCMSGraph.suggests + (Authentication->BiometricBased)
bCMSGraph.suggests = bCMSGraph.suggests + (Authentication->OneTimePwd)
bCMSGraph.suggests = bCMSGraph.suggests + (Authentication->ChallengeResponse)
bCMSGraph.suggests = bCMSGraph.suggests + (ChallengeResponse->SymmetricEncryption)
bCMSGraph.suggests = bCMSGraph.suggests + (ChallengeResponse->MutualAuthorization)
bCMSGraph.suggests = bCMSGraph.suggests + (ChallengeResponse->Kerberos)
bCMSGraph.suggests = bCMSGraph.suggests + (VMCommunicationProtocol->SOAP)
bCMSGraph.suggests = bCMSGraph.suggests + (VMCommunicationProtocol->SSL)
bCMSGraph.suggests = bCMSGraph.suggests + (CrisisMultiplicity->Single)
bCMSGraph.suggests = bCMSGraph.suggests + (CrisisMultiplicity->Multiple)
bCMSGraph.suggests = bCMSGraph.suggests + (Other->PSCAndFSCSend)
bCMSGraph.suggests = bCMSGraph.suggests + (Other->PSCReceive)
bCMSGraph.suggests = bCMSGraph.suggests + (Other->PSCSendAndReceive)
bCMSGraph.suggests = bCMSGraph.suggests + (Other->FSCSendAndReceive)
}

--A2
-- Check inconsistency
assert conflictsShow
{
	all fm:FM | fm = bCMSFM and (no n:Name | n in conflicts[bCMSGraph])
}
check conflictsShow


--A2
-- Check if configuration is Valid
assert show{ 
	lone c:Configuration| c.value =(bCMS+Functional+NonFunctional+
	DataCommConf+Encrypted+Authentication+ PasswordBased+
	CertificateBased+BiometricBased+OneTimePwd+ChallengeResponse+
	SymmetricEncryption+VehiclesManagement+ VMCommunicationProtocol+
	CrisisMultiplicity+Other+SOAP+SSL+ Multiple+PSCSendAndReceive+
	FSCSendAndReceive+PSCAndFSCSend+PSCReceive) and isValid[bCMSFM,c]
}
check show

