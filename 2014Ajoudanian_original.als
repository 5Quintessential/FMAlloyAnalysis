sig Featurenames{}
one sig car{c: (Int -> Int)}
fact {(car.c).univ = {n:Int | n>=0}
univ.(car.c)={n:Int | n>=1}}
sig Cardinality{Bound:setcar}
sig FeatureCardinality{FC:Featurenames-> one Cardinality}
sig FNSet{fns: set Featurenames}
sig GroupCardinality{GC:FNSet-> one Cardinality}

sig DRelation{}
sig Mandatory,Optional,Or,Alternative,AttributeRel extends DRelation{}
sig parentchild1{p:FeatureCardinality.FC->FeatureCardinality.FC}
sig PC1{c1: parentchild1.p->DRelation}
fact{(PC1.parentchild1).univ = Mandatory or (PC1.parentchild1).univ = Optional}

sig parentchild2{p:FC->GroupCardinality.GC}
sig PC2{c2: parentchild2.p->DRelation}
fact{(PC2.parentchild2).univ = Or or (PC2.parentchild2).univ = Alternative}

sig Attributenames
sig Attribute{attrel:AttributeNames->setInt,
Value: AttributeNames-> one Int}
fact {all a: AttributeNames|Attribute.Value[a] in Attribute.attrel[a]}
sig AttributeSet{atts: set Attribute}
sig LAttribute{ChildAttribute:DRelation->AttributeSet}
fact{all ca: (LAttribute.ChildAttribute).univ | ca=AttributeRel}

sig Model in PC1 +PC2+LAttribute{}
sig RootModel{RM:Featurenames-> one Model}
sig ConstModel{cm:RootModel->Const}

sig vp{
	p1: Featurenames-> Int,
	p2: AttributeNames-> Int}
fact{all f: univ(vp.p1)| univ.(FeatureCardinality.FC[f]) ≤ (FeatureCardinality.FC[f]).univ}
fact{all g: univ(vp.p1), rt:DRelation|(f,g,rt):PC1=>f in fns}
fact{all g: f: univ(vp.p1), rt:DRelation|(f,g,rt):PC2=>f in fns}
fact{all pc1: PC1,pc2:PC2,f,g,gs: univ(vp.p1) |
(f, g,Mandatory) in pc1 and f in fns =>g in fns and
(f, g,Optional) in pc1 and f in fns =>g in fns or g notin fns and
(f, gs,Or) in pc2 and f in fns =>#gs ≥ 1 and
(f, gs,Alternative) in pc2 and f in fns =>#gs=1}
fact{all a: univ(vp.p2), v:Attribute.Value|vinDom[a]}

sig LFeatureCardinality{
FeatureCardinality:Featurenames-> one Cardinality
}

pred Promote01(c1,c1’:Cardinality,lfc,lfc’:LFeatureCardinality,FNinput:Featurenames){
FNinput in (lfc.FeatureCardinality).univ
c1 =lfc.FeatureCardinality[FNinput]
lfc’.FeatureCardinality=lfc.FeatureCardinality++(FNinput->c1’)
}

pred AddLCardinality(c1,c1’:Cardinality,binput:car){
c1’.Bound =c1.Bound+binput
}

pred DeleteLCardinality(c1,c1’:Cardinality,binput:car){
binput in c1.Bound
c1’.Bound =c1.Bound-binput
}

pred AddGCardinality(b1:car,c2,c2’:Cardinality,lfc1,lfc1’:LFeatureCardinality,FN:Featurenames){
Promote01[c2,c2’,lfc1,lfc1’,FN] and AddLCardinality[c2,c2’,b1]
}
pred DeleteGCardinality(b1:car,c2,c2’:Cardinality,lfc1,lfc1’:LFeatureCardinality,FN:Featurenames){
Promote01[c2,c2’,lfc1,lfc1’,FN] and DeleteLCardinality[c2,c2’,b1]
}

sig GSubModel1{
ChildFeature1:DRelation->LFeatureCardinality
}
fact{
(GSubModel1.ChildFeature1).univ = Mandatory or
(GSubModel1.ChildFeature1).univ = Optional
}

pred Promote1(gsm1,gsm1’:GSubModel1,lfc,lfc’:LFeatureCardinality,DRinput:DRelation){
DRelation in (gsm1.ChildFeature1).univ
lfc =gsm1.ChildFeature1[DRinput]
gsm1’.ChildFeature1=gsm1.ChildFeature1++(DRinput->lfc’)
}

pred AddFeature(lfc,lfc’:LFeatureCardinality,FN:Featurenames,c:Cardinality){
FN notin (lfc.FeatureCardinality).univ
lfc’.FeatureCardinality = lfc.FeatureCardinality+(FN->c)
}

pred DeleteFeature(lfc,lfc’:LFeatureCardinality,FN:Featurenames,c:Cardinality){
FN in (lfc.FeatureCardinality).univ
lfc’.FeatureCardinality=lfc.FeatureCardinality-(FN->c)
}

pred AddGFeature(lfc,lfc’:LFeatureCardinality,gsm1,gsm1’:GSubModel1,DRinput:DRelation,FN:Featurenames,
c: Cardinality){
Promote1[gsm1,gsm1’,lfc,lfc’,DRinput] and AddFeature[lfc,lfc’,FN,c]
}

sig FNSet{fns:setFeaturenames}
sig LGroupCardinality{GroupCardinality: FNSet ->oneCardinality }

pred Promote02(c1,c1’:Cardinality,lgc,lgc’:LGroupCardinality,FNinput:FNSet){
FNinput in (lgc.GroupCardinality).univ
c1 =lgc.GroupCardinality[FNinput]
lgc’.GroupCardinality=lgc.GroupCardinality++(FNinput->c1’)
}

sig GSubModel2{
ChildFeature2:DRelation->LGroupCardinality
}

fact{
(GSubModel2.ChildFeature2).univ = Or or
(GSubModel2.ChildFeature2).univ = Alternative
}

pred Promote2(gsm2,gsm2’:GSubModel2,lgc,lgc’:LGroupCardinality,DRinput:DRelation){
DRinput in (gsm2.ChildFeature2).univ
lgc =gsm2.ChildFeature2[DRinput]
gsm2’.ChildFeature2=gsm2.ChildFeature2++(DRinput->lgc’)
}

sig AttributeNames{}
sig Domain{d:setInt}

sig Attribute{
attrel:AttributeNames-> setInt,
Value: AttributeNames-> one Int
}
fact {
all a: AttributeNames|Attribute.Value[a] in Attribute.attrel[a]
}

sig AttributeSet{atts: set Attribute}
sig LAttribute{
ChildAttribute:DRelation->AttributeSet
}

fact{
all ca: (LAttribute.ChildAttribute).univ | ca=AttributeRel
}

sig LocalSubModelinGSubModel1 + GSubModel2 + LAttribute{}

sig LocalSubModelSet {lsms:setLocalSubModel}
sig Global_Model{ Feature: Featurenames ->oneLocalSubModelSet}

pred Promote(lsms:LocalSubModelSet,lsm,lsm’:LocalSubModel,gm,gm’:Global_Model,finput:Featurenames){
finput in (gm.Feature).univ
lsms =gm.Feature[finput]
gm’.Feature=gm.Feature++(finput->setlsm’)
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

pred ValidConst1(c1:constraints){
all rwff1,rwff2:RWFF|
rwff1->rwff2 in c1.requires iff (rwff1=RWFF=>rwff2=RWFF) and
rwff1->rwff2 in c1.excludes iff (rwff1=RWFF=>not(rwff2=RWFF))
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
cond1 in rwff.cond iff (cond 1=Condition)
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
fun Exp(e: expre): Int{Exp[e]}

fun ValidConst5(f:Featurenames): Featurenames{f}

sig ValidProduct{
VP: product->ConstModel
}
pred ValidProduct(p:product,cm:ConstModel){
p ->cm in ValidProduct.VP iff
all p1: p.product1,p2:p.product2,m:Global_Model,f:m.Feature,c1:Featurenames,
d: FNSet,e:d.fns,s: set AttributeSet,s1:s.atts,lf:f[Featurenames],a:lf.lsms,
cf1: a.ChildFeature1,cf2:a.ChildFeature2,ca:a.ChildAttribute,
LFC: LFeatureCardinality,fc:LFC.FeatureCardinality,d1:b.Bound,k:d1.c,
b:univ.(LFC.FeatureCardinality),c2:constraints|
p1.univ = f.univ and cf1.univ = Mandatory=>
(c1 in cf1[DRelation].FeatureCardinality.univ implies c1 in p1.univ) and
p1.univ = f.univ and cf1.univ = Optional=>
(c1 in cf1[DRelation].FeatureCardinality.univ implies c1 in p1.univ or c1 not
in p1.univ) and
p1.univ = f.univ and cf2.univ = Or =>
(d in cf2[DRelation].GroupCardinality.univ implies (c1 in e) =>c1 in p1.univ
or c1 notin p1.univ) and
p1.univ = f .univ and cf2.univ = Alternative=>(d in
cf2[DRelation].GroupCardinality.univ implies (c1 in e) =>c1 in p1.univ) and
s in univ.ca impliesuniv.p2 in s1.attrel[p2.univ] and
p1.univ = fc.univ and k.univ <= univ.p1 and univ.p1 <= univ.k and
ValidConst1[c2]
}
fun allProduct(cm:ConstModel,p:product): set product{
{p: product|ValidProduct[p,cm]}}

-- EXAMPLE ---------------------------

open Ext
sig F1,F2,F3,F4,F5,F6 extends Featurenames{}
one sig fns1 extends FNSet{}
fact {fns1.fns=F3+F4+F5}
sig c0, c1,c2extendscar{}
fact a {c0.c=1->1 or
c1.c=1->3 or
c2.c= 1->2}
sig card0,card1,card2 extends Cardinality{}
fact {card0.Bound=c0
card1.Bound=c1
card2.Bound=c2}

sig lfc1,lfc2,lfc3,lfc4,lfc5,lfc6 extends LFeatureCardinality{}
fact {lfc1.FeatureCardinality=F1->card0
lfc2.FeatureCardinality=F2->card1
lfc3.FeatureCardinality=F3->card0
lfc4.FeatureCardinality=F4->card0
lfc5.FeatureCardinality=F5->card0
lfc6.FeatureCardinality=F6->card0}
one sig gsm11,gsm12 extends GSubModel1{}
fact {gsm11.ChildFeature1=Mandatory->lfc2
gsm12.ChildFeature1=Optional->lfc6
}
onesig lgc extends LGroupCardinality{}
fact {lgc.GroupCardinality=fns1->card2}
one sig gsm21 extends GSubModel2{}
fact {gsm21.ChildFeature2=Or->lgc}
sig f11 extends AttributeNames{}
sig a extends Attribute{}
fact{a.attrel=f11->{1+2+3+4}
a.Value =f11->3
}
one sig atts1 extends AttributeSet{}
fact {atts1.atts={a}}
one sig la extends LAttribute{}
fact {la.ChildAttribute=AttributeRel->atts1}
one sig lsms1,lsms2,lsms3 extends LocalSubModelSet{}
fact {lsms1.lsms=gsm11+gsm21
lsms2.lsms =gsm12
lsms3.lsms =la}
one sig gm1,gm2,gm3 extends Global_Model{}
fact {gm1.Feature=F1->lsms1 or
gm2.Feature=F2->lsms2 or
gm3.Feature=F5->lsms3}
one sig const1,const2,const3 extends constraints{}
sig css extends constSet{}
one sig rwff1,rwff2,rwff3,rwff4,rwff5,rwff6,rwff7,rwff8,rwff9,rwff10 extends RWFF{}
fact {rwff1.cond=cond1
rwff2.cond=cond2
rwff3.cond=cond3
rwff4.cond=cond4
rwff5.rwAnd=rwff1->rwff2
rwff6.rwAnd=rwff1->rwff3
rwff7.rwNot=rwff1
rwff8.cond=cond5
rwff9.rwAnd=rwff4->rwff7
rwff10.cond=cond6}
one sig cond1,cond2,cond3,cond4,cond5,cond6 extends Condition{}
one sig exp1,exp2,exp3,exp4,exp5 extends expre{}

fact{exp1.a=f11
exp2.val=4
exp3.add=exp1->exp2
exp4.val=9
exp5.val=5}
fact{cond1.f=F3 or
cond 2.f=F4 or
cond 3.f=F5 or
cond 4.f=F6 or
cond5.Less =exp3->exp4 or
cond6. Greater=exp1->exp5}
fact{const1.requires=rwff5->rwff4
const2.excludes=rwff6->rwff8
const3.requires=rwff9->rwff10}
sig cm extends ConstModel{}

fun nop(cm:ConstModel,p:product): Int{
#allProduct[cm,p]}

sig ValidProductFeature{
VP1: product->GSubModel1
}
pred Vprod(p:product,m:GSubModel1,LFC:LFeatureCardinality){
p ->m in ValidProductFeature.VP1 iff
all p1: p.product1,fc:LFC.FeatureCardinality,b:
univ.(LFC.FeatureCardinality),d1:b.Bound,
k: d1.c|p1.univ = fc.univ and k.univ <= univ.p1 and univ.p1 <= univ.k
}

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

sig ValidProductGroup{
VP2: product->GSubModel2
}
pred VprodG(p:product,m:GSubModel2,LGC:LGroupCardinality){
p ->m in ValidProductGroup.VP2 iffall p1: p.product1,
a:(LGC.GroupCardinality).univ, A: set
Featurenames,b: set Featurenames,g: univ.(LGC.GroupCardinality),d1:
g.Bound, k:d1.c|
(p1.univ in b implies b in A) and g =LGC.GroupCardinality[a] and
k.univ <= #A and #A <= univ.k
}

sig allProductGroupLocal{
allProductLoc:GSubModel2-> set product
}
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
pred VProduct(p:product,m:Global_Model,LFC:LFeatureCardinality,LGC:
LGroupCardinality,A: set Featurenames,c1:Featurenames,
d:FNSet,e:d.fns,s: set AttributeSet,s1:s.atts){
p ->m in ValidProductGlobal.VP3 iff
all p1: p.product1,p2:p.product2,f:m.Feature,lf:
f[Featurenames],a:lf.lsms,cf1:a.ChildFeature1,cf2:
a.ChildFeature2,ca:a.ChildAttribute|
p1.univ = f.univ and cf1.univ = Mandatory=>
(c1 in cf1[DRelation].FeatureCardinality.univ implies
c1 in p1.univ) and
p1.univ = f.univ and cf1.univ = Optional=>
(c1 in cf1[DRelation].FeatureCardinality.univ
implies c1 in p1.univ or c1 notin p1.univ) and
p1.univ = f.univ and cf2.univ = Or =>
(d in cf2[DRelation].GroupCardinality.univ implies
(c1 in e) =>c1 in p1.univ or c1 notin p1.univ) and
p1.univ = f.univ and cf2.univ = Alternative=>
(d in cf2[DRelation].GroupCardinality.univ implies (c1 in e)
=> c1 in p1.univ) and
s in univ.ca impliesuniv.p2 in s1.attrel[p2.univ]
}

fun NumOfProdGlobalFeature(lsm,lsm’:LocalSubModel,lsms:
LocalSubModelSet,gm,gm’:Global_Model,finput:Featurenames,
gsm1: GSubModel1,cf1:univ.(GSubModel1.ChildFeature1),
cf2: univ.(GSubModel2.ChildFeature2),p:product,
LFC: LFeatureCardinality,LGC:LGroupCardinality,
A: set Featurenames,d:FNSet,e:d.fns,s: set AttributeSet,
s1: s.atts):Int{
(Promote[lsms,lsm,lsm’,gm,gm’,finput] and
VProduct[p,gm,LFC,LGC,A,finput,d,e,s,s1]) implies
NumOfProdLocalFeature[gsm1] else 0}
fun NumOfProdGroupGlobal(lsm,lsm’:LocalSubModel,lsms:LocalSubModelSet,
gm, gm’:Global_Model,
finput:Featurenames,gsm2:GSubModel2,
cf1:univ.(GSubModel1.ChildFeature1),cf2:
univ.(GSubModel2.ChildFeature2),p:product,
LFC: LFeatureCardinality,
LGC:LGroupCardinality,
A: set Featurenames,d:FNSet,e:d.fns,s: set
AttributeSet,s1:s.atts): Int{
(Promote[lsms,lsm,lsm’,gm,gm’,finput] and
VProduct[p,gm,LFC,LGC,A,finput,d,e,s,s1]) implies
NumOfProdLocalGroup[gsm2] else 0
}

fun totalnumofproduct(lsm,lsm’:LocalSubModel,lsms:LocalSubModelSet,
gm, gm’:Global_Model,finput:Featurenames,gsm1:GSubModel1,
gsm2: GSubModel2,
cf1:univ.(GSubModel1.ChildFeature1),cf2:
univ.(GSubModel2.ChildFeature2),
p: product,LFC:LFeatureCardinality,LGC:
LGroupCardinality,A: set Featurenames,
d: FNSet,e:d.fns,s: set AttributeSet,s1:s.atts):
Int{
NumOfProdGlobalFeature[lsm,lsm’,lsms,gm,gm’,finput,gsm1,
cf1,cf2,p,LFC,LGC,A,d,e,s,s1]+
NumOfProdGroupGlobal[lsm,lsm’,lsms,gm,gm’,finput,gsm2,cf1,
cf2, p,LFC,LGC,A,d,e,s,s1]
}





