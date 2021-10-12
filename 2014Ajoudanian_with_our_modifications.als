sig Featurenames{}
sig DRelation{}
sig Mandatory, Optional, Or, Alternative, AttributeRel extends DRelation{}
one sig car{	c: (Int -> Int)}
fact {
		(car.c).univ = {n:Int|n>=0}
		univ.(car.c)={n:Int|n>=1}
}

sig Cardinality{Bound: set car}
fact{
		all a: Cardinality.Bound|(a.c).univ<=univ.(a.c)
}
sig LFeatureCardinality{FeatureCardinality:Featurenames-> one Cardinality}
pred Promote01(c1,c1':Cardinality,lfc,lfc':LFeatureCardinality,FNinput:Featurenames){
		FNinput in (lfc.FeatureCardinality).univ
		c1 =lfc.FeatureCardinality[FNinput]
		lfc'.FeatureCardinality=lfc.FeatureCardinality++(FNinput->c1')
}
pred AddLCardinality(c1,c1':Cardinality,binput:car){
		c1'.Bound =c1.Bound+binput
}
pred DeleteLCardinality(c1,c1':Cardinality,binput:car){
		binput in c1.Bound
		c1'.Bound =c1.Bound-binput
}
pred AddGCardinality(b1:car,c2,c2':Cardinality,lfc1,lfc1':LFeatureCardinality,FN:Featurenames){
		Promote01[c2,c2',lfc1,lfc1',FN] and AddLCardinality[c2,c2',b1]
}
pred DeleteGCardinality(b1:car,c2,c2':Cardinality,lfc1,lfc1':LFeatureCardinality,FN:Featurenames){
		Promote01[c2,c2',lfc1,lfc1',FN] and DeleteLCardinality[c2,c2',b1]
}
sig GSubModel1{ChildFeature1:DRelation->LFeatureCardinality}
fact{
		(GSubModel1.ChildFeature1).univ = Mandatory or
		(GSubModel1.ChildFeature1).univ = Optional
}
pred Promote1(gsm1,gsm1':GSubModel1,lfc,lfc':LFeatureCardinality,DRinput:DRelation){
		DRelation in (gsm1.ChildFeature1).univ
		lfc =gsm1.ChildFeature1[DRinput]
		gsm1'.ChildFeature1=gsm1.ChildFeature1++(DRinput->lfc')
}
pred AddFeature(lfc,lfc':LFeatureCardinality,FN:Featurenames,c:Cardinality){
		FN not in (lfc.FeatureCardinality).univ
		lfc'.FeatureCardinality = lfc.FeatureCardinality+(FN->c)
}
pred DeleteFeature(lfc,lfc':LFeatureCardinality,FN:Featurenames,c:Cardinality){
		FN in (lfc.FeatureCardinality).univ
		lfc'.FeatureCardinality=lfc.FeatureCardinality-(FN->c)
}
pred AddGFeature(lfc,lfc':LFeatureCardinality,gsm1,gsm1':GSubModel1,DRinput:DRelation,FN:Featurenames,c: Cardinality){
		Promote1[gsm1,gsm1',lfc,lfc',DRinput] and AddFeature[lfc,lfc',FN,c]
}
sig FNSet{fns:set Featurenames}
sig LGroupCardinality{GroupCardinality: FNSet ->one Cardinality }

pred Promote02(c1,c1':Cardinality,lgc,lgc':LGroupCardinality,FNinput:FNSet){
		FNinput in (lgc.GroupCardinality).univ
		c1 =lgc.GroupCardinality[FNinput]
		lgc'.GroupCardinality=lgc.GroupCardinality++(FNinput->c1')
}
sig GSubModel2{ ChildFeature2:DRelation->LGroupCardinality }
fact{
		(GSubModel2.ChildFeature2).univ = Or or
		(GSubModel2.ChildFeature2).univ = Alternative
}
pred Promote2(gsm2,gsm2':GSubModel2,lgc,lgc':LGroupCardinality,DRinput:DRelation){
		DRinput in (gsm2.ChildFeature2).univ
		lgc =gsm2.ChildFeature2[DRinput]
		gsm2'.ChildFeature2=gsm2.ChildFeature2++(DRinput->lgc')
}
sig AttributeNames{}
sig Domain{d:set Int}
sig Attribute{
		attrel:AttributeNames-> set Int,
		Value: AttributeNames-> one Int
}
fact {
		all a: AttributeNames|Attribute.Value[a] in Attribute.attrel[a]
}
sig AttributeSet{atts: set Attribute}
sig constSet{}

sig LAttribute{ChildAttribute:DRelation->AttributeSet}
fact{all ca: (LAttribute.ChildAttribute).univ | ca=AttributeRel}
sig LocalSubModel in GSubModel1 + GSubModel2 + LAttribute{}
sig LocalSubModelSet {lsms:set LocalSubModel}
sig Global_Model{ Feature: Featurenames ->one LocalSubModelSet}
pred Promote(lsms:LocalSubModelSet,lsm,lsm':LocalSubModel,gm,gm':Global_Model,finput:Featurenames){
		finput in (gm.Feature).univ
		lsms =gm.Feature[finput]
		gm'.Feature=gm.Feature++(finput->set lsm')
}
sig ConstModel {cm: Global_Model -> constSet}
sig constraints{
		requires:RWFF->RWFF,
		excludes:RWFF->RWFF
}
sig RWFF{
		rwAnd:RWFF->RWFF,
		rwOr:RWFF->RWFF,
		rwNot:RWFF,
		cond: Condition
}
sig Condition{
		Greater:expre->expre,
		EqualGreater:expre->expre,
		Less: expre->expre,
		EqualLess:expre->expre,
		Equal:expre->expre,
		notEqual:expre->expre,
		f: Featurenames,
		A: AttributeNames
}
sig expre{
		add: expre->expre,
		sub: expre->expre,
		mult:expre->expre,
		div:expre->expre,
		mod: expre->expre,
		a: AttributeNames,
		val: Int
}
pred ValidConst2(rwff:RWFF){
		all rwff1,rwff2:RWFF,cond1:Condition|
		rwff1->rwff2 in rwff.rwAnd iff
		(rwff1=ValidConst31[rwff1] and
		rwff2=ValidConst31[rwff2]) and
		rwff1->rwff2 in rwff.rwOr iff
		(rwff1=ValidConst31[rwff1] or
		rwff2=ValidConst31[rwff2]) and
		rwff1 in rwff.rwNot iff
		not(rwff1)=ValidConst31[rwff1] and
		cond1 in rwff.cond iff (cond1=Condition)
}
fun ValidConst31(rwff:RWFF):RWFF{
		rwff
}
pred ValidConst32(c:Condition){
		all e1,e2:expre,f1:Featurenames,a1:AttributeNames,a: Int |
		e1 ->e2 in c.Greater iff Exp[e1] >Exp[e2] and
		e1 ->e2 in c.EqualGreater iff Exp[e1] >=Exp[e2] and
		e1 ->e2 in c.Less iff Exp[e1] <Exp[e2] and
		e1 ->e2 in c.EqualLess iff Exp[e1] =<Exp[e2] and
		e1 ->e2 in c.Equal iff Exp[e1] =Exp[e2] and
		e1 ->e2 in c.notEqual iff Exp[e1]! =Exp[e2] and
		f1 in c.f iff f1 =ValidConst5[f1] and
		a1 in c.A iff a =Attribute.Value[a1]
}
pred ValidConst4(e:expre){
		all e1,e2:expre,a1:AttributeNames,b: Int |
		e1 ->e2 in e.add iff b =add[Exp[e1],Exp[e2]] and
		e1 ->e2 in e.sub iff b =sub[Exp[e1],Exp[e2]] and
		e1-> e2 in e.mult iff b =mul[Exp[e1],Exp[e2]] and
		e1-> e2 in e.div iff b =div[Exp[e1],Exp[e2]] and
		e1-> e2 in e.mod iff b =rem[Exp[e1],Exp[e2]] and
		a1 in e.a iff b =Attribute.Value[a1] and
		e1.val in e.val iff e1 =e
}
abstract sig product { product1: product, product2:product}
fun Exp(e: expre): Int{Exp[e]}
fun ValidConst5(f:Featurenames): Featurenames{f}
sig ValidProduct{	VP: product->ConstModel}
pred ValidProduct(p:product,cm:ConstModel){
		p ->cm in ValidProduct.VP iff
		all m:Global_Model,f:m.Feature,c1:Featurenames,
		d: FNSet,e:d.fns,s: set AttributeSet,lf:f[Featurenames],a:lf.lsms,
		cf1: a.ChildFeature1,cf2:a.ChildFeature2,ca:a.ChildAttribute|cf1.univ = Mandatory=>
			//p1.univ = f.univ and cf1.univ = Mandatory=>
			(c1 in cf1[DRelation].FeatureCardinality.univ) and cf1.univ = Optional=>
			//p1.univ = f.univ and cf1.univ = Optional=>
			(c1 in cf1[DRelation].FeatureCardinality.univ ) and cf2.univ = Or =>
			//p1.univ = f.univ and cf2.univ = Or =>
			(d in cf2[DRelation].GroupCardinality.univ implies (c1 in e) ) and cf2.univ = Alternative=>
			//p1.univ = f .univ and cf2.univ = Alternative=>
			(d in cf2[DRelation].GroupCardinality.univ implies (c1 in e) ) and
			s in univ.ca //implies p1 = fc.univ// and ValidConst32[c2]
}
fun allProduct(cm:ConstModel,p:product): set product{{p: product|ValidProduct[p,cm]}}


// bCMS encoding

sig bCMS,Functional,NonFunctional,DataCommConf,Encrypted,NotEncrypted,Authentication, PasswordBased,CertificateBased,BiometricBased,OneTimePwd,ChallengeResponse,SymmetricEncryption,MutualAuthorization,Kerberos,VehiclesManagement, VMCommunicationProtocol,CrisisMultiplicity,NoSendAndReceive,Other,SOAP,SSL,Single, Multiple,PSCSendAndReceive,FSCSendAndReceive,PSCAndFSCSend,PSCReceive extends Featurenames{}
sig c0,c1 extends car{}
sig card0,card1,card2,card3,card4,card5,card6,card7,card8,card9,card10,card11,card12,card13,card14,card15,card16,card17,card18,card19,card20,card21,card22,card23,card24,card25,card26,card27,card28,card29,card30 extends Cardinality{}

fact {
	c0.c=1->1 or
	c1.c=1->0
}
fact {
		card0.Bound=c0
		card1.Bound=c1		
}

sig lfc1,lfc2,lfc3,lfc4,lfc5,lfc6,lfc7,lfc8,lfc9,lfc10,lfc11,lfc12,lfc13,lfc14,lfc15,lfc16,lfc17,lfc18,lfc19,lfc20,lfc21,lfc22,lfc23,lfc24,lfc25,lfc26,lfc27,lfc28 extends LFeatureCardinality{}
fact {
		lfc1.FeatureCardinality=bCMS->card0
		lfc2.FeatureCardinality=Functional->card0
		lfc3.FeatureCardinality=NonFunctional->card0
		lfc4.FeatureCardinality=DataCommConf->card0
		lfc5.FeatureCardinality=Encrypted->card0
		lfc6.FeatureCardinality=NotEncrypted->card0
		lfc7.FeatureCardinality=Authentication->card1
		lfc8.FeatureCardinality=PasswordBased->card1
		lfc9.FeatureCardinality=CertificateBased->card1
		lfc10.FeatureCardinality=BiometricBased->card1
		lfc11.FeatureCardinality=OneTimePwd->card1
		lfc12.FeatureCardinality=ChallengeResponse->card1
		lfc13.FeatureCardinality=SymmetricEncryption->card1
		lfc14.FeatureCardinality=MutualAuthorization->card1
		lfc15.FeatureCardinality=Kerberos->card1
		lfc16.FeatureCardinality=VehiclesManagement->card1
		lfc17.FeatureCardinality=VMCommunicationProtocol->card1
		lfc18.FeatureCardinality=CrisisMultiplicity->card0
		lfc19.FeatureCardinality=NoSendAndReceive->card1
		lfc20.FeatureCardinality=Other->card1
		lfc21.FeatureCardinality=SOAP->card1
		lfc22.FeatureCardinality=SSL->card1
		lfc23.FeatureCardinality=Single->card0
		lfc24.FeatureCardinality=Multiple->card0
		lfc25.FeatureCardinality=PSCSendAndReceive->card1
		lfc26.FeatureCardinality=FSCSendAndReceive->card1
		lfc27.FeatureCardinality=PSCAndFSCSend->card1
		lfc28.FeatureCardinality=PSCReceive->card1
}

one sig gsm11,gsm12,gsm13,gsm14,gsm15,gsm16,gsm17,gsm18,gsm19,gsm110,gsm111,gsm112,gsm113,gsm114,gsm115,gsm116,gsm117,gsm118,gsm119,gsm120,gsm121,gsm122,gsm123,gsm124,gsm125,gsm126,gsm127,gsm128,gsm129,gsm130 extends GSubModel1{}
fact {
		gsm11.ChildFeature1=Mandatory->lfc1
		gsm12.ChildFeature1=Mandatory->lfc2
		gsm13.ChildFeature1=Mandatory->lfc3
		gsm14.ChildFeature1=Mandatory->lfc5
		gsm15.ChildFeature1=Mandatory->lfc6
		gsm16.ChildFeature1=Mandatory->lfc23
		gsm17.ChildFeature1=Mandatory->lfc24
		gsm18.ChildFeature1=Optional->lfc7
		gsm19.ChildFeature1=Optional->lfc16
		gsm110.ChildFeature1=Optional->lfc17
		gsm111.ChildFeature1=Optional->lfc21
		gsm112.ChildFeature1=Optional->lfc22
		gsm113.ChildFeature1=Optional->lfc25
		gsm114.ChildFeature1=Optional->lfc26
		gsm115.ChildFeature1=Optional->lfc27
		gsm116.ChildFeature1=Optional->lfc28
		gsm117.ChildFeature1=Or->lfc8
		gsm118.ChildFeature1=Or->lfc9
		gsm119.ChildFeature1=Or->lfc10
		gsm120.ChildFeature1=Or->lfc11
		gsm121.ChildFeature1=Or->lfc12
		gsm122.ChildFeature1=Alternative->lfc5
		gsm123.ChildFeature1=Alternative->lfc6
		gsm124.ChildFeature1=Alternative->lfc13
		gsm125.ChildFeature1=Alternative->lfc14
		gsm126.ChildFeature1=Alternative->lfc15
		gsm127.ChildFeature1=Alternative->lfc23
		gsm128.ChildFeature1=Alternative->lfc24
		gsm129.ChildFeature1=Alternative->lfc19
		gsm130.ChildFeature1=Alternative->lfc20
}

sig f11 extends AttributeNames{}
sig a extends Attribute{}
fact{
	a.attrel=f11->{1+2+3+4}
	a.Value =f11->3
}
one sig atts1 extends AttributeSet{}
fact {
	atts1.atts={a}
}
one sig la extends LAttribute{}
fact {
	la.ChildAttribute=AttributeRel->atts1
}
one sig lsms1,lsms2 extends LocalSubModelSet{}
fact {
	lsms1.lsms=gsm11+gsm12+gsm13+gsm14+gsm15+gsm16+gsm17+gsm18+gsm19+gsm110+gsm111+gsm112+gsm113+gsm114+gsm115
	lsms2.lsms=gsm116+gsm117+gsm118+gsm119+gsm120+gsm121+gsm122+gsm123+gsm124+gsm125+gsm126+gsm127+gsm128+gsm129+gsm130
}
one sig gm1,gm2 extends Global_Model{}
fact {
	gm1.Feature=bCMS->lsms1 or
	gm2.Feature=Functional->lsms2 
}
one sig const1,const2,const3 extends constraints{}
sig css extends constSet{}
one sig rwff1,rwff2,rwff3,rwff4,rwff5,rwff6,rwff7,rwff8,rwff9,rwff10 extends RWFF{}
fact {
	rwff1.cond=cond1
	rwff2.cond=cond2
	rwff3.cond=cond3
	rwff4.cond=cond4
	rwff5.rwAnd=rwff1->rwff2
	rwff6.rwAnd=rwff1->rwff3
	rwff7.rwNot=rwff1	
	rwff9.rwAnd=rwff4->rwff7	
}
one sig cond1,cond2,cond3,cond4 extends Condition{}
one sig exp1 extends expre{}
fact{
	exp1.a=f11	
}
fact{
	cond1.f=NonFunctional or
	cond2.f=DataCommConf or
	cond3.f=Encrypted or
	cond4.f=NotEncrypted 
}
fact{
	const1.requires=rwff5->rwff4
	const2.excludes=rwff6->rwff8
	const3.requires=rwff9->rwff10
}
sig cm extends ConstModel{}
fun nop(cm:ConstModel,p:product): Int{#allProduct[cm,p]}
sig ValidProductFeature{VP1: product->GSubModel1}

sig allProductFeatureLocal{
	allProductLoc:GSubModel1-> set product
}
pred allpfL(gsm1: GSubModel1){
	allProductFeatureLocal.allProductLoc[gsm1]={p:product|p->gsm1 in
	ValidProductFeature.VP1}
}

fun NumOfProdLocalFeature(gsm:GSubModel1): Int{
	#allProductFeatureLocal.allProductLoc[gsm]
}
sig ValidProductGroup{VP2: product->GSubModel2}

pred VprodG(p:product,m:GSubModel2,LGC:LGroupCardinality){
	p ->m in ValidProductGroup.VP2 iff all a:(LGC.GroupCardinality).univ, A: set
	Featurenames,g: univ.(LGC.GroupCardinality),d1:
	g.Bound, k:d1.c| g =LGC.GroupCardinality[a] and
	k.univ <= #A and #A <= univ.k
}
sig allProductGroupLocal{allProductLoc:GSubModel2-> set product}


pred allpgL(gsm2: GSubModel2){
	allProductGroupLocal.allProductLoc[gsm2]={p:product|p->gsm2 in
	ValidProductGroup.VP2}
}

fun NumOfProdLocalGroup(gsm2:GSubModel2): Int{
	#allProductGroupLocal.allProductLoc[gsm2]
}

sig ValidProductGlobal{
	VP3: product->Global_Model
}

pred VProduct(p:product,m:gm1,LFC:LFeatureCardinality,LGC:LGroupCardinality,A: set Featurenames,c1:Featurenames,d:FNSet,e:d.fns,s: set AttributeSet,s1:s.atts){
	p ->m in ValidProductGlobal.VP3 
--	all f1:p->m.Feature,lf:f1[Featurenames],a:lf.lsms,cf1:a.ChildFeature1,cf2:a.ChildFeature2,ca:a.ChildAttribute --|
--	(c1 in cf1[DRelation].FeatureCardinality.univ) and (c1 in cf1[DRelation].FeatureCardinality.univ) and 
--	(d in cf2[DRelation].GroupCardinality.univ implies (c1 in e) ) and (d in cf2[DRelation].GroupCardinality.univ implies (c1 in e)) and s in univ.ca
}

fun NumOfProdGlobalFeature(lsm,lsm':LocalSubModel,lsms:LocalSubModelSet,gm,gm':Global_Model,finput:Featurenames,gsm1: GSubModel1,cf1:univ.(GSubModel1.ChildFeature1),cf2: univ.(GSubModel2.ChildFeature2),p:product,LFC: LFeatureCardinality,LGC:LGroupCardinality,A: set Featurenames,d:FNSet,e:d.fns,s: set AttributeSet,s1: s.atts):Int{
		(Promote[lsms,lsm,lsm',gm,gm',finput] and VProduct[p,gm,LFC,LGC,A,finput,d,e,s,s1]) implies NumOfProdLocalFeature[gsm1] else 0
}

fun NumOfProdGroupGlobal(lsm,lsm':LocalSubModel,lsms:LocalSubModelSet,gm, gm':Global_Model,finput:Featurenames,gsm2:GSubModel2,cf1:univ.(GSubModel1.ChildFeature1),cf2:univ.(GSubModel2.ChildFeature2),p:product,LFC: LFeatureCardinality,LGC:LGroupCardinality,A: set Featurenames,d:FNSet,e:d.fns,s: set AttributeSet,s1:s.atts): Int{
	(Promote[lsms,lsm,lsm',gm,gm',finput] and VProduct[p,gm,LFC,LGC,A,finput,d,e,s,s1]) implies NumOfProdLocalGroup[gsm2] else 0
}
run NumOfProdGroupGlobal

--A2
-- Check if product is valid
pred Vprod(p:product,m:GSubModel1,LFC:LFeatureCardinality){
	p ->m in ValidProductFeature.VP1 iff
	all b:univ.(LFC.FeatureCardinality),d1:b.Bound| d1.c.univ <= 20
}
run Vprod

--A2
-- Find all valid configurations
fun totalnumofproduct(lsm,lsm':LocalSubModel,
						lsms:LocalSubModelSet,gm, 
						gm':Global_Model,finput:Featurenames,
						gsm1:GSubModel1,gsm2: GSubModel2,
						cf1:univ.(GSubModel1.ChildFeature1),
						cf2:univ.(GSubModel2.ChildFeature2),
						p: product,LFC:LFeatureCardinality,
						LGC:LGroupCardinality,A: set Featurenames,
						d: FNSet,e:d.fns,s: set AttributeSet,s1:s.atts):Int{
	NumOfProdGlobalFeature[lsm,lsm',lsms,gm,gm',finput,gsm1,cf1,cf2,p,LFC,LGC,A,d,e,s,s1]+
	NumOfProdGroupGlobal[lsm,lsm',lsms,gm,gm',finput,gsm2,cf1,cf2, p,LFC,LGC,A,d,e,s,s1]
}
run totalnumofproduct

--A27
-- Compute Reuse ration
-- Cannot reproduce the results from the paper
