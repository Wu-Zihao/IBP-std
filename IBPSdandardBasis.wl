(* ::Package:: *)

(* ::Section::Closed:: *)
(*Global Variables*)


SDim=9
ns=Table[ToExpression["n"<>ToString[i]],{i,SDim}]
zs=Table[ToExpression["z"<>ToString[i]],{i,SDim}]
ws=Table[ToExpression["w"<>ToString[i]],{i,SDim}]
vars={d,s,t}


(* ::Section:: *)
(*Data Structures*)


(* ::Subsection::Closed:: *)
(*Simplifier*)


RandomNumericCheck[expr_]:=Module[
{vars=Variables[expr],table},
	
	table=Quiet[Table[
		Factor[expr/.(#->RandomPrime[Length[vars]*5000]/RandomPrime[Length[vars]^2*10000]&/@vars)],
		Length[vars]+5
	],{Power::infy,Infinity::indet}];
	
	table=DeleteCases[table,Indeterminate];
	table=DeleteCases[table,0];
		

	If[table==={},
		Return[0]
	,
		Return[table[[1]]]
	]
]


SmartCheck[expr_]:=TimeConstrained[expr//Together,1,expr//RandomNumericCheck]


(* ::Subsection:: *)
(*IndMon*)


IndMon//ClearAll
(*IndMon[0,_List]:=0*)
Coeff[x_IndMon]:=x[[1]];
Indices[x_IndMon]:=x[[2]];
Multiplies[x_,y_IndMon]:=IndMon[x*Coeff[y],Indices[y]]
Act[x_IndMon,y_IndMon]:=IndMon[
	Coeff[x]*(Coeff[y]/.Table[
		ns[[i]]->ns[[i]]+Indices[x][[i]],
		{i,SDim}
	]),
	Indices[x]+Indices[y]
]
Mns[x_IndMon]:=IndMon[-Coeff[x],Indices[x]];

Inv[x_IndMon]:=IndMon[
	1/Coeff[x]/.Table[
		ns[[i]]->ns[[i]]-Indices[x][[i]],
		{i,SDim}
	],
	-Indices[x]
]
Division[x_IndMon,y_IndMon]:=Act[x,y//Inv]




(* ::Subsection::Closed:: *)
(*IndPol*)


(* ::Subsubsection:: *)
(*IndPol*)


ClearAll[IndPol,ToIndPol]
TermList[x_IndPol]:=x[[1]]
ToIndPol[x_]:=IndPol[IndMon[
	#[[2]],
	#[[1,;;SDim]]-#[[1,SDim+1;;]]
]&/@CoefficientRules[x,Join[zs,ws]]]
IndexSplit[list_List]:=Module[{list1,list2},
	list1=If[#>0,#,0]&/@list;
	list2=If[#<0,-#,0]&/@list;
	Join[list1,list2]
]
FromIndPol[x_IndPol]:=FromCoefficientRules[
	(IndexSplit[#//Indices]->(#//Coeff))&/@TermList[x],
	Join[zs,ws]
]
FromIndPol[x_IndMon]:=FromIndPol[IndPol[{x}]]
Mns[x_IndPol]:=IndPol[Mns/@TermList[x]];
Add[x_IndMon,y_IndMon]:=IndPol[{x,y}]//Collected
Add[x_IndMon,y_IndPol]:=IndPol[Append[y//TermList,x]]//Collected
Add[x_IndPol,y_IndMon]:=Add[y,x]//Collected
Add[x_IndPol,y_IndPol]:=IndPol[Join[x//TermList,y//TermList]]//Collected

Substract[x_IndMon,y_IndMon]:=Add[x,y//Mns]
Substract[x_IndMon,y_IndPol]:=Add[x,y//Mns]
Substract[x_IndPol,y_IndMon]:=Add[x,y//Mns]
Substract[x_IndPol,y_IndPol]:=Add[x,y//Mns]


Simplifier=SmartCheck;
Collected[x_IndPol]:=Module[
{terms=x//TermList,termsGrouped},
	termsGrouped=GatherBy[terms,Indices];
	IndPol[
		(IndMon[Total[Coeff/@#],Indices[#[[1]]]]&/@termsGrouped)/.IndMon[0,_]->Nothing
	]
]
Act[x_IndPol,y_IndMon]:=IndPol[Act[#,y]&/@TermList[x]]//Collected
Act[x_IndMon,y_IndPol]:=IndPol[Act[x,#]&/@TermList[y]]//Collected
Act[x_IndPol,y_IndPol]:=Module[{xTerms=x//TermList,yTerms=y//TermList},
	IndPol[
		Table[
			Act[xTerms[[i]],yTerms[[j]]],
			{i,Length[xTerms]},
			{j,Length[yTerms]}
		]//Flatten
	]
]//Collected
Devision[x_IndPol,y_IndMon]:=Act[x,y//Inv]


ZERO=IndPol[{}];


(* ::Subsubsection:: *)
(*LT*)


ClearAll[LexiOrdering,DegLexiGOrdering,RevDegLexiGOrdering]
LexiOrdering[x_]:=x
DegLexiGOrdering[x_]:=Module[
{y=x},
	Join[{Total[y]},y[[;;-2]]]
]
RevDegLexiGOrdering[x_]:=Module[
{y=x},
	Join[{Total[y]},Reverse[-y][[;;-2]]]
]



LT//ClearAll
LT[x_IndPol,directions_,ordering_]:=SortBy[
	x//Collected//TermList,
	ordering[DiagonalMatrix[directions].(#//Indices)
]&][[-1]]


(* ::Subsubsection:: *)
(*Cornerized*)


Cornerized[directions_][x_IndPol]:=Module[{refMon,indices,refInd},
	indices=Indices/@(x//TermList);
	indices=DiagonalMatrix[directions].#&/@indices;
	refInd=Min/@Transpose[indices];
	refInd=DiagonalMatrix[directions].refInd;
	refMon=IndMon[1,-refInd];
	Act[refMon,x]
]



(* ::Section:: *)
(*Polynomial Division with remainder*)


(* ::Subsection:: *)
(*Divisible Q*)


IndMonDivisibleQ[x_IndMon,y_IndMon,directions_]:=Module[{indx,indy},
	indx=x//Indices;
	indy=y//Indices;
	!MemberQ[Sign/@(
		DiagonalMatrix[directions].
		(indx-indy)
	),-1]
]



(* ::Subsection:: *)
(*reduction towards an IndPol*)


Reduced[f_IndPol,g_IndPol,directions_,ordering_]:=Module[
{quotient,remainder,rest,gLT,restLT,q1,i=0},
	rest=f;
	quotient=ZERO;
	remainder=ZERO;
	gLT=LT[g,directions,ordering];
	While[True,

		If[rest===ZERO,Break[]];
		
		restLT=LT[rest,directions,ordering];
		If[IndMonDivisibleQ[restLT,gLT,directions],
			q1=Division[restLT,gLT];(*perhaps, left/right division can affect performance*)
			rest=Substract[rest,Act[q1,g]];
			quotient=Add[quotient,q1]
		,
			rest=Substract[rest,restLT];
			remainder=Add[remainder,restLT];
		]
	];
	{quotient,remainder}
]


(* ::Subsection:: *)
(*reduction towards an IndPolIdeal*)


Generators[x_IndPolIdeal]:=x[[1]]


Reduced[f_IndPol,g_IndPolIdeal,directions_,ordering_]:=Module[
{
	quotients=Table[ZERO,Length[g//Generators]],
	remainder=f,
	i=1,n=0,
	q,newRemainder,gens=g//Generators
},
	While[True,
		newRemainder=remainder;(*maybe this is not needed?*)
		{q,newRemainder}=Reduced[newRemainder,gens[[i]],directions,ordering];
		If[q=!=ZERO,
			remainder=newRemainder;
			quotients[[i]]=Add[quotients[[i]],q];
			n=0;(*n counts for how many times that the division do nothing*)
		,
			n++
		];
		If[n==Length[gens],Break[]];
		i++;
		If[i>Length[gens],i-=Length[gens]];(*loop*)
	];
	{quotients,remainder}
]





(* ::Section:: *)
(*Draft*)
