(* ::Package:: *)

(* ::Subchapter:: *)
(*Routines*)


(* ::Subsubsection::Closed:: *)
(*$numberOfPaths property*)


Protect@ad;


Set::invnumpaths="Invalid number of paths specification: ``";


(*when $numberOfPaths is assigned new value, it is checked, whether this value is positive integer; is so,
then $listOfOpers and numOfPaths values are updated accordingly*)
ClearAll[$numberOfPaths,$listOfOpers,numOfPaths]

$numberOfPaths/:Set[$numberOfPaths,rhs_]:=Module[{},
	If[Not[Positive[rhs]&&IntegerQ[rhs]],Message[Set::invnumpaths,rhs];Return[]];
	OwnValues[$numberOfPaths]={HoldPattern[$numberOfPaths]:>rhs};
	$listOfOpers=ad/@Range[rhs];
	numOfPaths=rhs;
	{actions, probabilities}=generateActions[];
]


(* ::Subsubsection::Closed:: *)
(*fock states to operators*)


ClearAll[ketToOper]


ketToOper::usage="Transform state in Ket representation into creation-operator representation.";
ketToOper::folen="Number of modes in Ket vector is not equal to number of paths as given in $numberOfPaths.";
ketToOper::notfock="Input expression contains operator(s).";


ketToOper[expr_,listOfOpers_:$listOfOpers]:=Module[{aux,rule,error=False},
If[!FreeQ[expr,_ad],Message[ketToOper::notfock];Return[expr]];
rule=Ket[seq__]:>Times@@(1/Sqrt[{seq}!])Times@@(listOfOpers^{seq});
aux=Quiet[Check[expr/.rule,error=True;expr,{Thread::tdlen}],{Thread::tdlen}];
If[error,Message[ketToOper::folen];Return[expr]];
aux
]


(* ::Subsubsection::Closed:: *)
(*operators to fock states*)


ClearAll[operToKet]


operToKet::usage="Transform state in operator representation into Ket representation.";
operToKet::notoper="Input expression contains Ket(s).";


operToKet[expr_,listOfOpers_:$listOfOpers]:=Module[{rules},
If[!FreeQ[expr,_Ket],Message[operToKet::notoper];Return[expr]];
rules=CoefficientRules[expr,listOfOpers];
Total[rules/.Rule[spec_,coef_]:>coef Times@@Sqrt[spec!] Ket@@spec]
]


(*ketToOper@Ket[m,n]*)


(* ::Subsubsection::Closed:: *)
(*SPDC operators*)


normalizeState[expr_]:=Module[{norm},
norm=Norm@Cases[Collect[expr,_Ket],coef_ _Ket:>coef];
1/norm expr
]


dropHigherOrders[expr_,order_,couplconst_]:=Module[{gr},
Normal@Series[Refine[expr/.x:constPattern[couplconst]:>gr x,gr\[Element]Reals],{gr,0,order}]/.gr->1
]


spdcNonCollKet[expr_?(Not@*NumericQ),order_Integer,path1_,path2_,g_,normalize:True|False:False]:=Module[{prefactors,steps,rule,state},
rule=Ket[seq__]:>(g Sqrt[{seq}[[path1]]+1] Sqrt[{seq}[[path2]]+1]MapAt[#+1&,Ket[seq],{{path1},{path2}}]-g\[Conjugate] Sqrt[{seq}[[path1]]] Sqrt[{seq}[[path2]]]MapAt[#-1&,Ket[seq],{{path1},{path2}}]);

prefactors=1/Range[0,order]!;
steps=NestList[ReplaceAll[rule],expr,order];
state=Total[prefactors steps];
If[normalize,normalizeState[state],state]
]
spdcNonCollKet[order_Integer,path1_,path2_,g_,normalize:True|False:False]:=spdcNonCollKet[#,order,path1,path2,g,normalize]&


spdcNonCollOperOper[expr_?(Not@*NumericQ),order_Integer,path1_,path2_,g_,normalize:True|False:False]:=
	ketToOper@spdcNonCollKet[operToKet[expr],order,path1,path2,g,normalize]
spdcNonCollOperOper[order_Integer,path1_,path2_,g_,normalize:True|False:False]:=
	spdcNonCollOperOper[#,order,path1,path2,g,normalize]&


spdcNonColl=spdcNonCollOperOper


spdcCollKet[expr_?(Not@*NumericQ),order_Integer,path_,g_,normalize:True|False:False]:=Module[{prefactors,steps,rule,state},
rule=Ket[seq__]:>(g Sqrt[{seq}[[path]]+1] Sqrt[{seq}[[path]]+2]MapAt[#+2&,Ket[seq],path]-g\[Conjugate] Sqrt[{seq}[[path]]] Sqrt[{seq}[[path]]-1]MapAt[#-2&,Ket[seq],path]);

prefactors=1/Range[0,order]!;
steps=NestList[ReplaceAll[rule],expr,order];
state=Total[prefactors steps];
If[normalize,normalizeState[state],state]
]
spdcCollKet[order_Integer,path_,g_,normalize:True|False:False]:=spdcCollKet[#,order,path,g,normalize]&


spdcCollOperOper[expr_?(Not@*NumericQ),order_Integer,path_,g_,normalize:True|False:False]:=
	ketToOper@spdcCollKet[operToKet[expr],order,path,g,normalize]
spdcCollOperOper[order_Integer,path_,g_,normalize:True|False:False]:=
	spdcCollOperOper[#,order,path,g,normalize]&


spdcColl=spdcCollOperOper


(* ::Subsubsection::Closed:: *)
(*beamsplitter*)


beamFun[ket_,path1_,path2_,reflang_]:=Module[{k1,k2,pre,inter,post,binomProd,pathMin,pathMax,
refl=Cos[reflang],transm=Sin[reflang]},
If[refl==0,Return[ket]];
{pathMin,pathMax}=MinMax[{path1,path2}];
{k1,k2}={ket[[pathMin]],ket[[pathMax]]};
{pre,inter,post}={ket[[;;pathMin-1]],ket[[pathMin+1;;pathMax-1]],ket[[pathMax+1;;]]};

binomProd[n1_,n2_]:=Binomial[k1,n1]Binomial[k2,n2]Binomial[k1-n1+n2,n2]Binomial[k2-n2+n1,n1];
(I refl)^(k1+k2) Sum[(transm/(I refl))^(m1+m2) Sqrt[binomProd[m1,m2]]Join[pre,Ket[k2-m2+m1],inter,Ket[k1-m1+m2],post],{m1,0,k1},{m2,0,k2}]
]


ClearAll[beamsplitterKet]
beamsplitterKet[expr_,path1_,path2_,reflang_]:=Module[{ee},
(*for reflang=\[Pi]/4 one gets 50:50 BS*)
ee=expr/.x_Ket:>beamFun[x,path1,path2,reflang];
(*Collect[ee,_Ket]*)
ee
]
beamsplitterKet[path1_,path2_,reflang_: \[Pi]/4]:=beamsplitterKet[#,path1,path2,reflang]&


(*ClearAll[beamsplitterOper]
beamsplitterRules[path1_,path2_]:={ad[path1]\[RuleDelayed]1/Sqrt[2](ad[path1]+I ad[path2]),ad[path2]\[RuleDelayed]1/Sqrt[2](ad[path2]+I ad[path1])}
beamsplitterOper[expr_,path1_,path2_]:=operToKet[ketToOper[expr]/.beamsplitterRules[path1,path2]]
beamsplitterOper[path1_,path2_]:=beamsplitterOper[#,path1,path2]&*)


beamsplitterRules[path1_,path2_,reflang_]:=
{ad[path1]:>(Sin[reflang]ad[path1]+I Cos[reflang]ad[path2]),
ad[path2]:>(Sin[reflang]ad[path2]+I Cos[reflang]ad[path1])}


ClearAll[beamsplitterOper]
beamsplitterOper[expr_,path1_,path2_,reflang_]:=operToKet[ketToOper[expr]/.beamsplitterRules[path1,path2,reflang]]
beamsplitterOper[path1_,path2_,reflang_:\[Pi]/4]:=beamsplitterOper[#,path1,path2,reflang]&


ClearAll[beamsplitterOperOper]
beamsplitterOperOper[expr_,path1_,path2_,reflang_]:=expr/.beamsplitterRules[path1,path2,reflang]
beamsplitterOperOper[path1_,path2_,reflang_:\[Pi]/4]:=beamsplitterOperOper[#,path1,path2,reflang]&


beamsplitter=beamsplitterOperOper


(* ::Subsubsection::Closed:: *)
(*phaseshift*)


ClearAll[phaseshiftKet]
phaseshiftKet[expr_,path_,phase_]:=expr/.seq_Ket:>Exp[I phase seq[[path]]]seq
phaseshiftKet[path_,phase_]:=phaseshiftKet[#,path,phase]&


ClearAll[phaseshiftOperOper]
phaseshiftOperOper[expr_,path_,phase_]:=expr/.ad[path]:>Exp[I phase]ad[path]
phaseshiftOperOper[path_,phase_]:=phaseshiftOperOper[#,path,phase]&


phaseshift=phaseshiftOperOper


(* ::Subsubsection::Closed:: *)
(*actions*)


generateActions[numOfPaths_:numOfPaths,couplconst_:couplconst,beamsplitter_:beamsplitter,phaseshift_:phaseshift,spdcColl_:spdcColl,spdcNonColl_:spdcNonColl]:=
	Module[{aux,subprobabilities=<||>,subactions=<||>,actions,probabilities},
	
	aux=subactions["beamsplitter"]=Flatten@Table[beamsplitter[##,angl]&@@@Subsets[Range[numOfPaths],{2}],{angl,{(*\[Pi]/3,*)\[Pi]/4(*,(\[Pi]/5)*)}}];
	subprobabilities["beamsplitter"]=With[{len=Length@aux},ConstantArray[20/2./len,len]];
	
	aux=subactions["phaseshift"]=Flatten[Table[phaseshift[path,ang],{path,numOfPaths},{ang,\[Pi]{1,1/2,1/3,2/3}}],1];
	subprobabilities["phaseshift"]=With[{len=Length@aux},ConstantArray[1.5 25/2./len,len]];

	aux=subactions["spdcColl"]=Table[spdcColl[2,path,couplconst,False],{path,numOfPaths}];
	subprobabilities["spdcColl"]=With[{len=Length@aux},ConstantArray[15/2./len,len]];

	(*aux=subactions["spdcNonColl"]=spdcNonColl[2,##,couplconst,False]&@@@Subsets[Range[numOfPaths],{2}]
	subprobabilities["spdcNonColl"]=With[{len=Length@aux},ConstantArray[15/2./len,len]]*)

	aux=subactions["identity"]={Identity};
	subprobabilities["identity"]=With[{len=Length@aux},ConstantArray[1,len]];

	actions=Flatten[subactions//Values];
	probabilities=Flatten[subprobabilities//Values];
	(*probabilities/Total[probabilities]*)
	{actions, probabilities}
]


(* ::Subsubsection::Closed:: *)
(*measurement*)


projectOntoStates[expr_,states_List]:=expr/.Except[Alternatives@@states,_Ket]->0


coincidenceDetection::nokets="No kets found.";
coincidenceDetection::short="Coincidence wanted in nonexisting path.";
coincidenceDetection[expr_,pos_List,reduce:(True|False):False]:= Module[{patt,ket,output,compl},
	ket=FirstCase[expr,_Ket,None,Infinity];
	If[ket===None,Message[coincidenceDetection::nokets];Return[expr]];
	If[Length[ket]<Max[pos],Message[coincidenceDetection::short];Return[expr]];
	patt=_&/@ket;
	patt[[pos]]=_?Positive;
	(*Print[patt];*)
	output=expr/.Except[patt,_Ket]->0;
	compl=Complement[Range[Length[ket]],pos];
	If[reduce,
		output=output/.k_Ket:>k[[compl]];
		output=Collect[output,_Ket,Simplify];
	];
	output
]


(* ::Subsubsection::Closed:: *)
(*miscellaneous*)


applyActions[listOfActions_,expr_,step_:3]:=Module[{i=0},
(*instead of Composition this routine is used to apply Simplify after every step-th action to
make expression simplified on the fly*)

Fold[
If[Divisible[++i,step],(*Inactive[Simplify]*)Simplify,Identity]@*First@Map[#2,{#1}]&,
expr,
Reverse@listOfActions
]
]


constPattern::usage="For symbols in 'consts' return Alternatives[symbols..., their conjugates...]. This routine is meant to be used primarily in other routines.";
constPattern[consts_]:=Module[{aux},
aux=Switch[Head[consts],
List,consts,
Alternatives,List@@consts,
_,{consts}
];
aux=aux~Join~Conjugate[aux];
Alternatives@@aux
]


getCoeffs[expr_]:=Module[{h},List@@@List@@Collect[expr,$pattern,h]/.h->Identity]


getGCoeff::usage="If 'expr' can be seen as a polynomial in 'couplconst' or its complex conjugate, return the 'order'-th order term from 'expr'.";
getGCoeff[expr_,couplconst_,order_]:=Module[{gr},Coefficient[expr/. x:constPattern[couplconst]:>gr x/.gr\[Conjugate]->gr,gr,order]]


newFileName[num_,head_:"setup_",extension_:"txt"]:=StringJoin[head,ToString[num],".",extension]
newFileName["Timestamp",head_:"setup_",extension_:"txt"]:=StringJoin[head,DateString[Now,{"DayNameShort","_","Day","_","MonthShort","_","Year","_","Hour","h","Minute","m","Second","s"}],".",extension]


(*relevantTerms[expr_,refList_List]:=Module[{aux,relTermsFun},
(*assumes refList={{patt11,...,patt1n},...,{pattM1,...,pattMm}}*)

relTermsFun[andOptsList_]:=Module[{auxlist},
auxlist=FirstCase[expr,#,None,3]&/@andOptsList;
If[MemberQ[auxlist,None],None,auxlist]
];

aux=relTermsFun/@refList;
aux/.None->Nothing
(*Cases[expr,refList,Infinity]*)
]*)


relevantTerms[expr_,refList_List,allCases_:False]:=Module[{aux,ee,relTermsFun},
(*assumes refList={{patt11,...,patt1n},...,{pattM1,...,pattMm}}*)

(*ee=Expand@If[Head[expr]=!=Plus,{expr},expr];*)
ee=If[Head[expr]=!=Plus,{expr},expr];
ee=Expand[Collect[ee,$pattern,h]];
ee=ee/.h->Identity;

If[allCases,
relTermsFun[andOptsList_]:=Module[{auxlist},
	auxlist=Cases[ee,#,3]&/@andOptsList;
	(*If[MemberQ[auxlist,None],None,auxlist]*)
	auxlist
];
,
relTermsFun[andOptsList_]:=Module[{auxlist},
	auxlist=FirstCase[ee,#,None,3]&/@andOptsList;
	If[MemberQ[auxlist,None],None,auxlist]
];

];

aux=relTermsFun/@refList;
aux/.None->Nothing
(*Cases[expr,refList,Infinity]*)
]


(* ::Subsubsection::Closed:: *)
(*highlight parts*)


highlightTerms[expr_]:=TraditionalForm[Collect[expr,$pattern,Framed@*Factor@*Simplify]/.x:$pattern:>Highlighted[x]]
highlightTerms[expr_,"Column"]:=TraditionalForm[List@@(Collect[expr,$pattern,Framed@*Simplify]/.x:$pattern:>Highlighted[x])//Column]
highlightTerms[expr_,"Grid"]:=TraditionalForm[List@@@List@@(Collect[expr,$pattern,Framed@*Simplify]/.x:$pattern:>Highlighted[x])//Grid]


highlightConsts[expr_,consts_]:=Module[{conspatt=constPattern[consts]},TraditionalForm[ExpandAll[Collect[expr,conspatt,Framed@*Simplify]/.x:conspatt:>Highlighted[x],conspatt]]]
highlightConsts[expr_,consts_,"Column"]:=Module[{conspatt=constPattern[consts]},TraditionalForm[List@@(Collect[expr,conspatt,Framed@*Simplify]/.x:conspatt:>Highlighted[x])//Column]]
highlightConsts[expr_,consts_,"Grid"]:=Module[{conspatt=constPattern[consts]},TraditionalForm[List@@@List@@ExpandAll[Collect[expr,conspatt,Framed@*Simplify]/.x:conspatt:>Highlighted[x],conspatt]//Grid]]
highlightConsts[expr_,consts_,"Terms"]:=Module[{conspatt=constPattern[consts]},TraditionalForm[ExpandAll[Collect[expr,conspatt,Framed@*highlightTerms]/.x:conspatt:>Highlighted[x,Background->LightBlue],conspatt]]]


(* ::Subchapter:: *)
(*Iteration*)


(* ::Subsubsection:: *)
(*Input parameters*)


numOfIterations=1;


(*initState=\[Beta] ad[1]+\[Alpha] ad[1] ad[2];*)
(*refParts={{\[Alpha] ad[3]Except[_. ad[4],_],_ \[Beta] ad[3]ad[4]}};*)
initState=\[Alpha] ad[2]ad[3]+\[Beta] ad[2] ad[4];
refParts={{\[Beta] ad[2] ad[3]_?(FreeQ[ad[1]|ad[4]]),\[Alpha] ad[2] ad[4]_?(FreeQ[ad[1]|ad[3]])}};
(*refParts={{\[Beta] ad[2] ad[3]_?(FreeQ[ad[1]|ad[4]]),\[Alpha] ad[2] ad[4]_?(FreeQ[ad[1]|ad[3]])}};*)
(*refParts={{\[Beta] ad[2]ad[4] _.,_. \[Alpha] ad[2]ad[4]}};*)
coincidenceList={}(*{5,6}*); (*REMEMBER: refParts are used only after coincidence detection, i.e. number of paths reduces*)
unwantedPatternsZero=None;
(*unwantedPatternsFirst={{__ Ket[_?Positive,0,0,0,___]},{__ Ket[0,_?Positive,0,0,___]},{__ Ket[0,0,_?Positive,0,___]},{__ Ket[0,0,0,_?Positive,___]}}(*_(Ket[_?Positive,_,__]|Ket[_,_?Positive,__])*);*)
unwantedPatternsFirst={{__ Ket[seq__,_,_]/;Plus[seq]!=2}};


(*relevantTerms[\[Alpha] 2 ad[3]ad[4]+2 \[Beta] ad[3]ad[4],refParts]*)


numOfActions=15;
subdir="setups_"<>DateString[Today,{"DayNameShort","_","Day","_","MonthShort","_","Year"}];
Protect[g];
couplconst=g;


(*BEWARE: $numberOfPaths WORKS LIKE PYTHON-TYPE PROPERTY. SPECIFICALLY, BY SETTING $numberOfPaths,
ALSO $listOfOpers, numOfPaths, actions AND probabilities ARE AUTOMATICALLY RECALCULATED!!!*)
$numberOfPaths=6;
$pattern=_ad;


setDir[]:=Module[{dir,dir2,subdir=subdir},
dir=DirectoryName@If[$InputFileName=="",NotebookDirectory[],$InputFileName];
SetDirectory[dir];
dir2=FileNameJoin[{dir,subdir}];
If[!FileExistsQ[dir2],CreateDirectory[dir2]];
SetDirectory[dir2]
]


(* ::Subsubsection:: *)
(*Modules*)


printComplexityEstimate[False,___]:=Null;
printComplexityEstimate[True,expr_,patt_:$pattern]:=Module[{estimate},
estimate=Count[expr,patt,Infinity];
Print["Number of occurences of ",patt," in expression: ",estimate];
]


printSummary[initTime_,iternum_,numexported_]:=Module[{timediff},
timediff=ToString@QuantityForm[DateDifference[initTime,DateList[],{"Hour","Minute","Second"}],"LongForm"];
Print["Total computation time: ",timediff];
Print["End of computation: ",DateString@Now];
Print["Total number of completed iterations: ",iternum];
Print["In total ",numexported," setups exported."];
]


generateState[settAssoc_,printInter_]:=Module[{setup,outputState,numKetsPre,
probabilities=settAssoc["probabilities"],actions=settAssoc["actions"],initState=settAssoc["initState"],
maxNumOfActions=settAssoc["maxNumOfActions"],coincidenceList=settAssoc["coincidenceList"]},

setup=RandomChoice[probabilities->actions,maxNumOfActions]/.Identity->Nothing;

(*calculate output state*)
outputState=(Composition@@setup)[initState];
interPrint[printInter,"State generation completed..."];

(*estimate complexity of unsimplified output state*)
printComplexityEstimate[printInter,outputState];

If[Length@coincidenceList>0,
outputState=coincidenceDetection[outputState,coincidenceList,True];
];
{setup,outputState}
]


exportData[initTime_,setup_,outputState_,matches_,settAssoc_]:=Module[{currentTime,filename,assoc},
	currentTime=DateDifference[initTime,DateList[],{"Minute","Second"}];
	filename=newFileName["Timestamp"];
	
	assoc=<|"timestamp"->currentTime,"setup"->setup,"outputState"->outputState,"matches"->matches|>;
	AssociateTo[assoc,settAssoc];
	Put[assoc,filename];
	Print["Exported into ",filename,". (Directory: ",Directory[](*dir*),")"];
]


ClearAll[interPrint];


interPrint[True,e__]:=Print[e];
interPrint[False,e__]:=Null;


(* ::Subsubsection:: *)
(*Calculation*)


DistributeDefinitions[actions, numOfActions, initState];


settingAssoc:=<|"maxNumOfActions"->numOfActions,"initState"->initState,"referencePatterns"->refParts,
"coincidenceList"->coincidenceList,"dir"->dir,
"unwantedPatternsZero"->unwantedPatternsZero,"unwantedPatternsFirst"->unwantedPatternsFirst,
"couplingConstant"->couplconst,"actions"->actions,"probabilities"->probabilities,
"timeConstraint"->(.5 60),"singleOperTimeConstraint"->60|>


ClearAll[runSearch];


Options[runSearch]={"intermediateMessages"->True};


runSearch[maxNumOfIterations_:numOfIterations,settAssoc_:settingAssoc,OptionsPattern[]]:=

Module[
{setup,outputState,time,res,initTime=DateList[],assoc,iternum=0,numexported=0,currentTime,matches,
numKetsPre,numKetsPost,coef,coefconj,ss,zeroOrder,firstOrder,filename,timediff,unwantedmatches,
printInter=OptionValue["intermediateMessages"],
maxNumOfActions=settAssoc["maxNumOfActions"],actions=settAssoc["actions"],
probabilities=settAssoc["probabilities"],initState=settAssoc["initState"],
coincidenceList=settAssoc["coincidenceList"],couplconst=settAssoc["couplingConstant"],
refParts=settAssoc["referencePatterns"],singleOperTimeConstraint=settAssoc["singleOperTimeConstraint"],
timeConstraint=settAssoc["timeConstraint"],unwantedPatternsFirst=settAssoc["unwantedPatternsFirst"]
},

SetSharedVariable[numexported,iternum];
Print["Start of computation: ",DateString@Now];

(*loop*)
CheckAbort[
ParallelDo[
	interPrint[printInter,"Iteration no. ",iter, " out of ",maxNumOfIterations];
	
	(*generate setup*)
	{setup,outputState}=generateState[settAssoc,printInter];

	(*check criteria*)
	firstOrder=getGCoeff[outputState,couplconst,1];
	matches=relevantTerms[firstOrder,refParts];
	unwantedmatches=relevantTerms[operToKet@firstOrder,unwantedPatternsFirst];
		
	(*if criteria satisfied, export data*)
	If[(*False*)Flatten@matches=!={}&&Flatten@unwantedmatches==={}(*True*),
		interPrint[printInter,"Preparation for export..."];
		(*outputState=Collect[outputState,_ad(*_Ket*),
			Simplify[#,TimeConstraint->{singleOperTimeConstraint,timeConstraint}]&
			];*)
		outputState=TimeConstrained[Collect[outputState,_ad(*_Ket*),
			Simplify[#,TimeConstraint->{singleOperTimeConstraint,timeConstraint}]&
			],10 timeConstraint];
		printComplexityEstimate[printInter,outputState];
		exportData[initTime,setup,outputState,matches,settAssoc];
		++numexported;
	,
		interPrint[printInter,"Not exported."]
	];
	iternum++;
	,
	{iter,maxNumOfIterations}
];
,
Print["Aborted!"];
];

printSummary[initTime,iternum,numexported];
UnsetShared[numexported,iternum];
]


(* ::Subsubsection::Closed:: *)
(*Tests*)


(*SetOptions[runSearch,"intermediateMessages"->True]*)


(*runSearch[1]*)


(*RuntimeTools`Profile[runSearch[2,20]]*)
