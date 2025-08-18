(* ::Package:: *)

(* ::Section:: *)
(*Global Variables*)


SDim=5
ns=Table[ToExpression["n"<>ToString[i]],{i,SDim}]//Reverse
zs=Table[ToExpression["z"<>ToString[i]],{i,SDim}]//Reverse
ws=Table[ToExpression["w"<>ToString[i]],{i,SDim}]//Reverse
vars=Table[ToExpression["m"<>ToString[i]],{i,SDim+1,20}]
numerics=(#->1/RandomPrime[6787])&/@vars



(* ::Input:: *)
(**)


"ibpVectors={5 + m10 + m12 + m13 + m14 + m16 + m17 + m19 + m7 + m8 + m9 + n1 + n2 + n3 + n4 + n5 + (2 + m12 + m16 + m19 + m20 + m7 + n1)*z1 + (4 + m12 + m13 + m16 + m17 + m18 + m19 + m20 + m7 + m8 + 2*n1 + n2)*z2 + (6 + m12 + m13 + m14 + m15 + m16 + m17 + m18 + m19 + m20 + 2*m7 + m8 + m9 + 2*n1 + 2*n2 + n3)*z3 + (8 + m10 + m11 + 2*m12 + m13 + m14 + m15 + m16 + m17 + m18 + m19 + m20 + 2*m7 + 2*m8 + m9 + 2*n1 + 2*n2 + 2*n3 + n4)*z4 + (10 + m10 + m11 + 2*m12 + 2*m13 + m14 + m15 + 2*m16 + m17 + m18 + m19 + m20 + m6 + 2*m7 + 2*m8 + 2*m9 + 2*n1 + 2*n2 + 2*n3 + 2*n4 + n5)*z5, (4 + m10 + m13 + m14 + m17 + m8 + m9 + n2 + n3 + n4 + n5)*z1 + (2 + m10 + m14 + m9 - n1 + n3 + n4 + n5)*z2 + (2 + m13 + m17 + m18 + m8 + n2)*z1*z2 + (m10 - m7 - n1 - n2 + n4 + n5)*z3 + (4 + m13 + m14 + m15 + m17 + m18 + m8 + m9 + 2*n2 + n3)*z1*z3 + (m14 + m15 + m9 - 2*n1 + n3)*z2*z3 + (-2 - m12 - m7 - m8 - n1 - n2 - n3 + n5)*z4 + (6 + m10 + m11 + m13 + m14 + m15 + m17 + m18 + 2*m8 + m9 + 2*n2 + 2*n3 + n4)*z1*z4 + (2 + m10 + m11 + m14 + m15 + m9 - 2*n1 + 2*n3 + n4)*z2*z4 + (-2 + m10 + m11 - 2*m7 - 2*n1 - 2*n2 + n4)*z3*z4 + (-4 - m12 - m13 - m16 - m7 - m8 - m9 - n1 - n2 - n3 - n4)*z5 + (8 + m10 + m11 + 2*m13 + m14 + m15 + m17 + m18 + m6 + 2*m8 + 2*m9 + 2*n2 + 2*n3 + 2*n4 + n5)*z1*z5 + (4 + m10 + m11 + m14 + m15 + m6 + 2*m9 - 2*n1 + 2*n3 + 2*n4 + n5)*z2*z5 + (m10 + m11 + m6 - 2*m7 - 2*n1 - 2*n2 + 2*n4 + n5)*z3*z5 + (-4 - 2*m12 + m6 - 2*m7 - 2*m8 - 2*n1 - 2*n2 - 2*n3 + n5)*z4*z5 + (-1 - n1)*pow(z2, 2) + (-2 - m7 - n1 - n2)*pow(z3, 2) + (-3 - m12 - m7 - m8 - n1 - n2 - n3)*pow(z4, 2) + (-4 - m12 - m13 - m16 - m7 - m8 - m9 - n1 - n2 - n3 - n4)*pow(z5, 2), (3 + m10 + m14 + m9 + n3 + n4 + n5)*z1*z2 + (1 + m10 - n2 + n4 + n5)*z1*z3 + (2 + 2*m10 - m7 - n2 + 2*n4 + 2*n5)*z2*z3 + (2 + m14 + m15 + m9 + n3)*z1*z2*z3 + (-1 - m8 - n2 - n3 + n5)*z1*z4 + (-2 - m12 - m7 - m8 - n2 - 2*n3 + 2*n5)*z2*z4 + (4 + m10 + m11 + m14 + m15 + m9 + 2*n3 + n4)*z1*z2*z4 + (-m12 - m8 - n3 + 2*n5)*z3*z4 + (m10 + m11 - 2*n2 + n4)*z1*z3*z4 + (2*m10 + 2*m11 - 2*m7 - 2*n2 + 2*n4)*z2*z3*z4 + (-3 - m13 - m8 - m9 - n2 - n3 - n4)*z1*z5 + (-6 - m12 - m13 - m16 - m7 - m8 - 2*m9 - n2 - 2*n3 - 2*n4)*z2*z5 + (6 + m10 + m11 + m14 + m15 + m6 + 2*m9 + 2*n3 + 2*n4 + n5)*z1*z2*z5 + (-4 - m12 - m13 - m16 - m8 - m9 - n3 - 2*n4)*z3*z5 + (2 + m10 + m11 + m6 - 2*n2 + 2*n4 + n5)*z1*z3*z5 + (4 + 2*m10 + 2*m11 + 2*m6 - 2*m7 - 2*n2 + 4*n4 + 2*n5)*z2*z3*z5 + (-2 - m13 - m16 - m9 - n4)*z4*z5 + (-2 + m6 - 2*m8 - 2*n2 - 2*n3 + n5)*z1*z4*z5 + (-4 - 2*m12 + 2*m6 - 2*m7 - 2*m8 - 2*n2 - 4*n3 + 2*n5)*z2*z4*z5 + (-2*m12 + 2*m6 - 2*m8 - 2*n3 + 2*n5)*z3*z4*z5 + (3 + m10 + m14 + m9 + n3 + n4 + n5)*pow(z2, 2) + (2 + m14 + m15 + m9 + n3)*z3*pow(z2, 2) + (4 + m10 + m11 + m14 + m15 + m9 + 2*n3 + n4)*z4*pow(z2, 2) + (6 + m10 + m11 + m14 + m15 + m6 + 2*m9 + 2*n3 + 2*n4 + n5)*z5*pow(z2, 2) + (2 + m10 + n4 + n5)*pow(z3, 2) + (-1 - n2)*z1*pow(z3, 2) + (-2 - m7 - n2)*z2*pow(z3, 2) + (2 + m10 + m11 + n4)*z4*pow(z3, 2) + (4 + m10 + m11 + m6 + 2*n4 + n5)*z5*pow(z3, 2) + (1 + n5)*pow(z4, 2) + (-2 - m8 - n2 - n3)*z1*pow(z4, 2) + (-4 - m12 - m7 - m8 - n2 - 2*n3)*z2*pow(z4, 2) + (-2 - m12 - m8 - n3)*z3*pow(z4, 2) + (2 + m6 + n5)*z5*pow(z4, 2) + (-3 - m13 - m8 - m9 - n2 - n3 - n4)*z1*pow(z5, 2) + (-6 - m12 - m13 - m16 - m7 - m8 - 2*m9 - n2 - 2*n3 - 2*n4)*z2*pow(z5, 2) + (-4 - m12 - m13 - m16 - m8 - m9 - n3 - 2*n4)*z3*pow(z5, 2) + (-2 - m13 - m16 - m9 - n4)*z4*pow(z5, 2), (2 + m10 + n4 + n5)*z1*z2*z3 + (-n3 + n5)*z1*z2*z4 + (-m8 - n3 + 2*n5)*z1*z3*z4 + (-m12 - m8 - 2*n3 + 4*n5)*z2*z3*z4 + (2 + m10 + m11 + n4)*z1*z2*z3*z4 + (-2 - m9 - n3 - n4)*z1*z2*z5 + (-4 - m13 - m8 - m9 - n3 - 2*n4)*z1*z3*z5 + (-8 - m12 - m13 - m16 - m8 - 2*m9 - 2*n3 - 4*n4)*z2*z3*z5 + (4 + m10 + m11 + m6 + 2*n4 + n5)*z1*z2*z3*z5 + (-2 - m13 - m9 - n4)*z1*z4*z5 + (-4 - m13 - m16 - 2*m9 - 2*n4)*z2*z4*z5 + (m6 - 2*n3 + n5)*z1*z2*z4*z5 + (-6 - 2*m13 - 2*m16 - 2*m9 - 3*n4)*z3*z4*z5 + (2*m6 - 2*m8 - 2*n3 + 2*n5)*z1*z3*z4*z5 + (-2*m12 + 4*m6 - 2*m8 - 4*n3 + 4*n5)*z2*z3*z4*z5 + (2 + m10 + n4 + n5)*z3*pow(z2, 2) + (-n3 + n5)*z4*pow(z2, 2) + (2 + m10 + m11 + n4)*z3*z4*pow(z2, 2) + (-2 - m9 - n3 - n4)*z5*pow(z2, 2) + (4 + m10 + m11 + m6 + 2*n4 + n5)*z3*z5*pow(z2, 2) + (m6 - 2*n3 + n5)*z4*z5*pow(z2, 2) + (2 + m10 + n4 + n5)*z1*pow(z3, 2) + (4 + 2*m10 + 2*n4 + 2*n5)*z2*pow(z3, 2) + (-m12 - m8 - n3 + 3*n5)*z4*pow(z3, 2) + (2 + m10 + m11 + n4)*z1*z4*pow(z3, 2) + (4 + 2*m10 + 2*m11 + 2*n4)*z2*z4*pow(z3, 2) + (-6 - m12 - m13 - m16 - m8 - m9 - n3 - 3*n4)*z5*pow(z3, 2) + (4 + m10 + m11 + m6 + 2*n4 + n5)*z1*z5*pow(z3, 2) + (8 + 2*m10 + 2*m11 + 2*m6 + 4*n4 + 2*n5)*z2*z5*pow(z3, 2) + (-2*m12 + 3*m6 - 2*m8 - 2*n3 + 3*n5)*z4*z5*pow(z3, 2) + (2 + m10 + n4 + n5)*pow(z3, 3) + (2 + m10 + m11 + n4)*z4*pow(z3, 3) + (4 + m10 + m11 + m6 + 2*n4 + n5)*z5*pow(z3, 3) + (1 + n5)*z1*pow(z4, 2) + (2 + 2*n5)*z2*pow(z4, 2) + (-1 - n3)*z1*z2*pow(z4, 2) + (3 + 3*n5)*z3*pow(z4, 2) + (-2 - m8 - n3)*z1*z3*pow(z4, 2) + (-4 - m12 - m8 - 2*n3)*z2*z3*pow(z4, 2) + (-3 - m13 - m16 - m9 - n4)*z5*pow(z4, 2) + (2 + m6 + n5)*z1*z5*pow(z4, 2) + (4 + 2*m6 + 2*n5)*z2*z5*pow(z4, 2) + (6 + 3*m6 + 3*n5)*z3*z5*pow(z4, 2) + (-1 - n3)*pow(z2, 2)*pow(z4, 2) + (-3 - m12 - m8 - n3)*pow(z3, 2)*pow(z4, 2) + (1 + n5)*pow(z4, 3) + (2 + m6 + n5)*z5*pow(z4, 3) + (-2 - m9 - n3 - n4)*z1*z2*pow(z5, 2) + (-4 - m13 - m8 - m9 - n3 - 2*n4)*z1*z3*pow(z5, 2) + (-8 - m12 - m13 - m16 - m8 - 2*m9 - 2*n3 - 4*n4)*z2*z3*pow(z5, 2) + (-2 - m13 - m9 - n4)*z1*z4*pow(z5, 2) + (-4 - m13 - m16 - 2*m9 - 2*n4)*z2*z4*pow(z5, 2) + (-6 - 2*m13 - 2*m16 - 2*m9 - 3*n4)*z3*z4*pow(z5, 2) + (-2 - m9 - n3 - n4)*pow(z2, 2)*pow(z5, 2) + (-6 - m12 - m13 - m16 - m8 - m9 - n3 - 3*n4)*pow(z3, 2)*pow(z5, 2) + (-3 - m13 - m16 - m9 - n4)*pow(z4, 2)*pow(z5, 2), (1 + n5)*z1*z2*z3*z4 + (-1 - n4)*z1*z2*z3*z5 + (-2 - m9 - n4)*z1*z2*z4*z5 + (-4 - m13 - m9 - 2*n4)*z1*z3*z4*z5 + (-8 - m13 - m16 - 2*m9 - 4*n4)*z2*z3*z4*z5 + (2 + m6 + n5)*z1*z2*z3*z4*z5 + (1 + n5)*z3*z4*pow(z2, 2) + (-1 - n4)*z3*z5*pow(z2, 2) + (-2 - m9 - n4)*z4*z5*pow(z2, 2) + (2 + m6 + n5)*z3*z4*z5*pow(z2, 2) + (1 + n5)*z1*z4*pow(z3, 2) + (2 + 2*n5)*z2*z4*pow(z3, 2) + (-1 - n4)*z1*z5*pow(z3, 2) + (-2 - 2*n4)*z2*z5*pow(z3, 2) + (-6 - m13 - m16 - m9 - 3*n4)*z4*z5*pow(z3, 2) + (2 + m6 + n5)*z1*z4*z5*pow(z3, 2) + (4 + 2*m6 + 2*n5)*z2*z4*z5*pow(z3, 2) + (1 + n5)*z4*pow(z3, 3) + (-1 - n4)*z5*pow(z3, 3) + (2 + m6 + n5)*z4*z5*pow(z3, 3) + (1 + n5)*z1*z2*pow(z4, 2) + (2 + 2*n5)*z1*z3*pow(z4, 2) + (4 + 4*n5)*z2*z3*pow(z4, 2) + (-3 - m13 - m9 - n4)*z1*z5*pow(z4, 2) + (-6 - m13 - m16 - 2*m9 - 2*n4)*z2*z5*pow(z4, 2) + (2 + m6 + n5)*z1*z2*z5*pow(z4, 2) + (-9 - 2*m13 - 2*m16 - 2*m9 - 3*n4)*z3*z5*pow(z4, 2) + (4 + 2*m6 + 2*n5)*z1*z3*z5*pow(z4, 2) + (8 + 4*m6 + 4*n5)*z2*z3*z5*pow(z4, 2) + (1 + n5)*pow(z2, 2)*pow(z4, 2) + (2 + m6 + n5)*z5*pow(z2, 2)*pow(z4, 2) + (3 + 3*n5)*pow(z3, 2)*pow(z4, 2) + (6 + 3*m6 + 3*n5)*z5*pow(z3, 2)*pow(z4, 2) + (1 + n5)*z1*pow(z4, 3) + (2 + 2*n5)*z2*pow(z4, 3) + (3 + 3*n5)*z3*pow(z4, 3) + (-4 - m13 - m16 - m9 - n4)*z5*pow(z4, 3) + (2 + m6 + n5)*z1*z5*pow(z4, 3) + (4 + 2*m6 + 2*n5)*z2*z5*pow(z4, 3) + (6 + 3*m6 + 3*n5)*z3*z5*pow(z4, 3) + (1 + n5)*pow(z4, 4) + (2 + m6 + n5)*z5*pow(z4, 4) + (-1 - n4)*z1*z2*z3*pow(z5, 2) + (-2 - m9 - n4)*z1*z2*z4*pow(z5, 2) + (-4 - m13 - m9 - 2*n4)*z1*z3*z4*pow(z5, 2) + (-8 - m13 - m16 - 2*m9 - 4*n4)*z2*z3*z4*pow(z5, 2) + (-1 - n4)*z3*pow(z2, 2)*pow(z5, 2) + (-2 - m9 - n4)*z4*pow(z2, 2)*pow(z5, 2) + (-1 - n4)*z1*pow(z3, 2)*pow(z5, 2) + (-2 - 2*n4)*z2*pow(z3, 2)*pow(z5, 2) + (-6 - m13 - m16 - m9 - 3*n4)*z4*pow(z3, 2)*pow(z5, 2) + (-1 - n4)*pow(z3, 3)*pow(z5, 2) + (-3 - m13 - m9 - n4)*z1*pow(z4, 2)*pow(z5, 2) + (-6 - m13 - m16 - 2*m9 - 2*n4)*z2*pow(z4, 2)*pow(z5, 2) + (-9 - 2*m13 - 2*m16 - 2*m9 - 3*n4)*z3*pow(z4, 2)*pow(z5, 2) + (-4 - m13 - m16 - m9 - n4)*pow(z4, 3)*pow(z5, 2)};";
StringReplace[%,"pow("~~Shortest[x__]~~")":>"Power["<>x<>"]"]//ToExpression;



(* ::Section:: *)
(*Data Structures*)


(* ::Subsection:: *)
(*Simplifier*)


RandomNumericCheck[expr_]:=Module[
{vars=Variables[expr],table,t},
	
	table=Quiet[Table[
		Factor[expr/.(#->RandomPrime[Length[vars]*5000]/RandomPrime[Length[vars]^2*10000]&/@vars)],
		Length[vars]+5
	],{Power::infy,Infinity::indet}];
	
	table=DeleteCases[table,Indeterminate];
	table=DeleteCases[table,0];
		
	
	If[table==={},
		Return[0]
	,
		Return[expr]
	]
]


SmartCheck[expr_]:=Module[{r,t},
	t=AbsoluteTime[];
	r=TimeConstrained[expr//Together,10,expr//RandomNumericCheck];
	TIMER+=(AbsoluteTime[]-t);
	
	r
]


DebugTogether[x_]:=Module[{tmp},
	tmp=AbsoluteTiming[x//Together];
	If[tmp[[1]]>MAXONECETIME,probe20250819=x;MAXONECETIME=tmp[[1]]];
	TIMER+=tmp[[1]];
	COUNTER+=1;
	AppendTo[SimplificationTimers,tmp[[1]]];
	tmp[[2]]
]


Simplifier=DebugTogether;


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




(* ::Subsection:: *)
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


ZERO=IndPol[{}];


(* ::Subsubsection:: *)
(*Collected*)


Collected//ClearAll
Options[Collected]={Simplification->False}
Collected[x_IndPol,OptionsPattern[]]:=Module[
{terms=x//TermList,termsGrouped},
	termsGrouped=GatherBy[terms,Indices];
	If[OptionValue[Simplification],
		Return[
			IndPol[
				(IndMon[Total[Coeff/@#]//Simplifier,Indices[#[[1]]]]&/@termsGrouped)/.IndMon[0,_]->Nothing
			]
		]
	,
		Return[
			IndPol[
				(IndMon[Total[Coeff/@#],Indices[#[[1]]]]&/@termsGrouped)/.IndMon[0,_]->Nothing
			]
		]	
	]
	
]


(* ::Subsubsection:: *)
(*Add and Subtraction*)



Mns[x_IndPol]:=IndPol[Mns/@TermList[x]];
Add[x_IndMon,y_IndMon]:=IndPol[{x,y}]//Collected
Add[x_IndMon,y_IndPol]:=IndPol[Append[y//TermList,x]]//Collected
Add[x_IndPol,y_IndMon]:=Add[y,x]//Collected
Add[x_IndPol,y_IndPol]:=IndPol[Join[x//TermList,y//TermList]]//Collected

Subtraction[x_IndMon,y_IndMon]:=Add[x,y//Mns]
Subtraction[x_IndMon,y_IndPol]:=Add[x,y//Mns]
Subtraction[x_IndPol,y_IndMon]:=Add[x,y//Mns]
Subtraction[x_IndPol,y_IndPol]:=Add[x,y//Mns]


(* ::Subsubsection:: *)
(*Act*)


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
LTCOUNTER=0;(*for debug*)
LT[x_IndPol,directions_,ordering_]:=(LTCOUNTER++;SortBy[
	x//Collected//TermList,
	ordering[DiagonalMatrix[directions].(#//Indices)
]&][[-1]]
)


(* ::Subsubsection:: *)
(*Cornerized*)


Cornerized//ClearAll
Cornerized[xx_IndPol,directions_]:=Module[{refMon,indices,refInd,x},
	x=Collected[x,Simplification->True];
	If[x===ZERO,Return[ZERO]];
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
{quotient,remainder,rest,gLT,restLT,q1,i=0,loopCounter=0},
	rest=f;
	quotient=ZERO;
	remainder=ZERO;
	gLT=LT[Collected[g,Simplification->True],directions,ordering];
	While[True,
		(*Print["          ",loopCounter," : ",LTCOUNTER," : ",COUNTER];
		loopCounter++;
		If[loopCounter\[GreaterEqual]5000,Break[]];*)
		rest=Collected[rest,Simplification->True];
		If[rest===ZERO,Break[]];
		restLT=LT[rest,directions,ordering];
		If[IndMonDivisibleQ[restLT,gLT,directions],
			q1=Division[restLT,gLT];(*perhaps, left/right division can affect performance*)
			rest=Subtraction[rest,Act[q1,g]];
			quotient=Add[quotient,q1]
		,
			rest=Subtraction[rest,restLT];
			remainder=Add[remainder,restLT];
		]
	];
	Collected[#,Simplification->True]&/@{quotient,remainder}
]


(* ::Subsection:: *)
(*reduction towards an IndPolIdeal*)


Generators[x_IndPolIdeal]:=x[[1]]


Reduced[f_IndPol,g_IndPolIdeal,directions_,ordering_]:=Module[
{
	quotients=Table[ZERO,Length[g//Generators]],
	remainder=f,
	i=1,n=0,
	q,newRemainder,gens=g//Generators,
	loopCounter=0
},
	While[True,
		Print["    ",loopCounter," : ",LTCOUNTER," : ",COUNTER];
		loopCounter++;
		If[loopCounter>=500,Break[]];
		newRemainder=remainder;(*maybe this is not needed?*)
		{q,newRemainder}=Reduced[newRemainder,gens[[i]],directions,ordering];
		(*q,newRemainder is collected simplifyied after Reduced*)
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



HReduced//ClearAll;
HReduced[f_,g_,directions_,ordering_]:=Module[{res},
	If[Head[g]===List,
		res=Reduced[f//ToIndPol,IndPolIdeal[ToIndPol/@g],directions,ordering];
		res={FromIndPol/@res[[1]],FromIndPol[res[[2]]]};
	,
		res=Reduced[f//ToIndPol,g//ToIndPol,directions,ordering];
		res=FromIndPol/@res;
	];
	res
]


(* ::Subsection:: *)
(*IndPolIdeal SelfReduction*)


SelfReduction[g_IndPolIdeal,directions_,ordering_]:=Module[
{
loopCounter=0,
gens=g//Generators,
i=1,n=0,j=0,divisors,r,qs
},
	gens=Cornerized[#,directions]&/@gens;
	While[True,
		Print[loopCounter," : ",LTCOUNTER," : ",COUNTER];
		loopCounter++;
		If[loopCounter>=5,Break[]];
		j++;(*for debug*)
		If[Length[gens]<=1,Break[]];
		If[i>Length[gens],i-=Length[gens]];(*loop*)
		divisors=DeleteCases[gens,gens[[i]]];
		{qs,r}=Reduced[gens[[i]],IndPolIdeal[divisors],directions,ordering];
		(*r=Collected[r];(*is this needed?*)*)
		r=Cornerized[r,directions];
		(*Print["gens=",FromIndPol/@gens,"  r=",FromIndPol@r,"    i=",i];*)
		If[r===ZERO,
			(*Print["000"];*)
			gens=divisors;
			n=0;(*n counts for how many times that the division does nothing*)
		,
			
			If[Subtraction[gens[[i]],r]===ZERO,
				n++;(*nothing changes*)
				(*Print["==="];*)
			,
				gens[[i]]=r;
				(*Print["mmm"];*)
				n=0
			];
			i++;(*moves the label if the i-th gen is not removed ( will be removed if r===0)*)
		];
		If[n>=Length[gens],Break[]];
		If[j>10,Break[]]
	];
	IndPolIdeal[gens]
	
];
(*human readable*)
HSelfReduction[gens_,directions_,ordering_]:=FromIndPol/@Generators[SelfReduction[IndPolIdeal[ToIndPol/@gens],directions,ordering]]


(* ::Section:: *)
(*Draft*)


TIMER=0;
COUNTER=0;
LTCOUNTER=0;
MAXONECETIME=0;
SimplificationTimers={};
probe20250819//Clear
AbsoluteTiming[reduced=HSelfReduction[ibpVectors[[{3,2,1}]]/.numerics,Table[1,SDim],RevDegLexiGOrdering];]



probe20250819;
MAXONECETIME
TIMER
COUNTER           
COUNTER*MAXONECETIME                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     


Select[SimplificationTimers,#<0.001&]//Total
SimplificationTimers//Total


Select[SimplificationTimers,#>0.001&]//Length


%497/4166


Histogram[Select[SimplificationTimers,#>0.001&]]


reduced//Together


(* ::Section::Closed:: *)
(*LatticeRational (not used, all commented out)*)


(* ::Subsection:: *)
(*LatPol*)


(* ::Subsubsection:: *)
(*definition*)


(*LatShifts[x_LatPol]:=x[[1]]
ValueArray[x_LatPol]:=x[[2]]*)


(*ToLatPol[expr_,vars_,dimensions_,latShifts_]:=Module[{v},
	LatPol[
		latShifts,
		Table@@Join[
			{expr},
			Table[{vars[[j]],latShifts[[j]]+Range[dimensions[[j]]]},{j,Length[vars]}]
		]
	]
]*)


(*(*Langrange interpolation*)
FromLatPol[lp_LatPol,x_List]:=Module[{y,latShifts,k,dimensions},
	latShifts=LatShifts[lp];
	y=ValueArray[lp];
	dimensions=Dimensions[y];
	Total[
		Array[
			Times[	
				Part[
					y,
					##
				],
				Product[
					Product[
						If[j=={##}[[i]],1,(x[[i]]-j-latShifts[[i]])/({##}[[i]]-j)],
						{j,dimensions[[i]]}
					],
					{i,Length[dimensions]}
				]
				
			]&,
			dimensions
		],
		Length[dimensions]
	]
]*)


(* ::Subsubsection:: *)
(*truncation*)


(*(*differencing in orders to find the real needed dimensions of the array*)
ActualSingleVariateDimension[l_List]:=Module[{result=1,list=l},
	If[l==={},Print["error:asvp01"];Return[$Failed]];
	While[True,
		If[Length[Union[list]]===1,Break[]];
		list=Differences[list];(*assuming the lattice distance is always 1*)
		result++;
	];
	result
]
Truncate[lp_LatPol,direction_]:=Module[{powerArray,y,dimensions,maxDimension,truncY,latShifts},
	latShifts=LatShifts[lp];
	y=ValueArray[lp];
	dimensions=Dimensions[y];
	powerArray=Array[
		ActualSingleVariateDimension[
			Part[
				y,
				Insert[{##},All,direction]/.List->Sequence
			]
		]&,
		Delete[dimensions,direction]
	];
	maxDimension=Max[powerArray];
	truncY=Array[
		Part[
			y,
			##
		]&,
		ReplacePart[dimensions,direction->maxDimension]
	];
	LatPol[latShifts,truncY]
]
Truncate[lp_LatPol]:=Module[{latShifts,y,dimensions,direction,result},
	result=lp;
	latShifts=LatShifts[lp];
	y=ValueArray[lp];
	dimensions=Dimensions[y];
	For[direction=1,direction<=Length[dimensions],direction++,
		result=Truncate[result,direction]
	];
	result
]*)


(* ::Subsubsection:: *)
(*moving*)


(*SingleVariateLatMove[lp_LatPol,direction_,distance_]:=Module[{y,dimensions,directionWidth,oldArray,newArray,latShifts},
	If[Head[distance]=!=Integer,Print["error: svlm_non_integer_distance"];Return[$Failed]];
	If[distance===0,Return[lp]];
	latShifts=LatShifts[lp];
	y=ValueArray[lp];
	dimensions=Dimensions[y];
	directionWidth=dimensions[[direction]];
	If[Abs[distance]>=directionWidth,
		newArray=Array[
			FromLatPol[
				lp,
				{##}+
				Table[
					If[i==direction,distance,0],
					{i,Length[dimensions]}
				]
			]&,
			dimensions
		];
		Return[LatPol[latShifts,newArray]];
	,
		If[distance>0,
			newArray=Array[
				FromLatPol[
					lp,
					{##}+
					Table[
						If[i==direction,directionWidth,0],
						{i,Length[dimensions]}
					]
				]&,
				ReplacePart[dimensions,direction->distance]
			];
			oldArray=Array[
				Part[
					y,
					(
						{##}+
						Table[
							If[i==direction,distance,0],
							{i,Length[dimensions]}
						]
					)/.List->Sequence
				]&,
				ReplacePart[dimensions,direction->directionWidth-distance]
			];
			Return[
				LatPol[
					latShifts,
					Join[oldArray,newArray,direction]
				]
			];
		,
		(*else*)
			newArray=Array[
				FromLatPol[
					lp,
					{##}+
					Table[
						If[i==direction,-Abs[distance],0],(*yes here is -distance *)
						{i,Length[dimensions]}
					]
				]&,
				ReplacePart[dimensions,direction->Abs[distance]]
			];
			oldArray=Array[
				Part[
					y,
					##
				]&,
				ReplacePart[dimensions,direction->directionWidth-Abs[distance]]
			];
			Return[
				LatPol[
					latShifts,
					Join[newArray,oldArray,direction](*new array in the left*)
				]
			];
		];
	];
]*)


(*(*equivalent as pol/.Table[x[[i]]\[Rule]x[[i]]+indices[[i]]]*)
LatMove[lp_LatPol,indices_]:=Module[{i,result},
	result=lp;
	For[i=1,i<=Length[indices],i++,
		result=SingleVariateLatMove[result,i,indices[[i]]]
	];
	result
]*)


(* ::Subsubsection:: *)
(*Amplify*)


(*Amplify[lp_LatPol,a_]:=LatPol[lp//LatShifts,a*ValueArray[lp]]*)


(* ::Subsubsection:: *)
(*Extend*)


(*
OneDirectionExtend[lp_LatPol,direction_,width_]:=Module[{latShifts,y,dimensions,newArray},
	latShifts=LatShifts[lp];
	y=ValueArray[lp];
	dimensions=Dimensions[y];
	If[dimensions[[direction]]\[GreaterEqual]width,Return[lp]];(*I am lazy, did not throw warning if here is > rather than = *)
	newArray=Array[
		FromLatPol[
			lp,
			{##}+
			Table[
				If[i==direction,dimensions[[direction]],0],
				{i,Length[dimensions]}
			]
		]&,
		ReplacePart[dimensions,direction\[Rule]width-dimensions[[direction]]]
	];
	LatPol[latShifts,Join[y,newArray,direction]]
]*)


(*Extend[lp_LatPol,dimensions_List]:=Module[{result,i},
	result=lp;
	For[i=1,i\[LessEqual]Length[dimensions],i++,
		result=OneDirectionExtend[result,i,dimensions[[i]]];
	];
	result
]*)


(* ::Subsubsection:: *)
(*Add and Subtraction*)


(*Add[lp1_LatPol,lp2_LatPol]:=Module[
{latShifts1,latShifts2,y1,y2,dimensions1,dimensions2,dimensions,newlp1,newlp2},
	latShifts1=LatShifts[lp1];
	y1=ValueArray[lp1];
	dimensions1=Dimensions[y1];
	latShifts2=LatShifts[lp2];
	y2=ValueArray[lp2];
	dimensions2=Dimensions[y2];
	If[latShifts1=!=latShifts2,
		Print["Error: LatPolAdd_non_equal_latshifts"];
		Return[$Failed];
	];
	dimensions=Max/@Transpose[{dimensions1,dimensions2}];
	newlp1=Extend[lp1,dimensions];
	newlp2=Extend[lp2,dimensions];
	(*we assume the latShifts is always reserved while extending*)
	y1=ValueArray[newlp1];
	y2=ValueArray[newlp2];
	LatPol[latShifts1,y1+y2]
]

*)


(*Subtraction[lp1_LatPol,lp2_LatPol]:=Add[lp1,Amplify[lp2,-1]]*)


(* ::Subsubsection:: *)
(**)
