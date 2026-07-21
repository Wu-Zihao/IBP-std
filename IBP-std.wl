(* ::Package:: *)

(* ::Section:: *)
(*Laporta IBPs*)


LoopMomenta={l}
ExternalMomenta={p1,p2,p4}
Propagators=#^2&/@{l,l+p1,l+p1+p2,l-p4}
Kinematics={p1^2->0,p2^2->0,p4^2->0,p1 p2->s/2,p1 p4->t/2,p2 p4->(-s-t)/2}


xy2sp=Join[
	Table[
		x[i,j]->LoopMomenta[[i]]*ExternalMomenta[[j]],
		{i,Length[LoopMomenta]},
		{j,Length[ExternalMomenta]}
	]//Flatten,
	Table[
		y[i,j]->LoopMomenta[[i]]*LoopMomenta[[j]],
		{i,Length[LoopMomenta]},
		{j,i}
	]//Flatten
]
sp2xy=Reverse/@xy2sp
xys=xy2sp[[All,1]]


prop2xy=Table[
	P[i]->Expand[Propagators[[i]]]/.Kinematics/.sp2xy,
	{i,Length[Propagators]}
]


sol=Solve[(#[[1]]-#[[2]]&/@prop2xy)==0,xys];
If[Length[sol]===1,
	xy2prop=sol[[1]]
,
	Print[sol,"is with multiple solutions."];
	xy2prop=$Failed
];
xy2prop


zs=Table[Subscript[z,i],{i,Length[Propagators]}]
ws=Table[Subscript[w,i],{i,Length[Propagators]}]
zsws=Join[zs,ws];
ns=Table[Subscript[n,i],{i,Length[Propagators]}]
zwrep=Table[ws[[i]]->1/zs[[i]],{i,Length[Propagators]}]
Set[Evaluate[ToExpression["z"<>ToString[#]]],Subscript[z,#]]&/@Range[Length[Propagators]]
Set[Evaluate[ToExpression["w"<>ToString[#]]],Subscript[w,#]]&/@Range[Length[Propagators]]
Set[Evaluate[ToExpression["n"<>ToString[#]]],Subscript[n,#]]&/@Range[Length[Propagators]]






prop2z=Table[P[i]->zs[[i]],{i,Length[Propagators]}]


LaportaIBP[l_,v_]:=Module[{},
	If[!MemberQ[LoopMomenta,l],
		Print["argument at position 1:  "l," is not a loop momentum."];
		Return[$Failed]
	];
	Plus[
		D[v,l]*d,
		Sum[
			Times[
				-ns[[i]] ws[[i]],
				Expand[D[Propagators[[i]],l]*v]/.Kinematics/.sp2xy/.xy2prop/.prop2z
			],
			{i,Length[Propagators]}
		]
	] 
]


(* ::Section:: *)
(*OpMon and OpPol*)


(* ::Subsection:: *)
(*TermList*)


TermList[expr_]:=Module[{expand,terms},
	expand=Expand[expr];
	If[Head[expand]===Plus,
		terms=List@@expand;
	,
		terms={expand};
	];
	terms
]


(* ::Subsection:: *)
(*OpMon*)


PowerListCancel[list1_,list2_]:=Module[{},
	If[Length[list1]=!=Length[list2],
		Print["***Error PowerListCancel-01"];
		Return[$Failed]
	];
	Table[
		If[list1[[i]]>list2[[i]],
			{list1[[i]]-list2[[i]],0},
			{0,list2[[i]]-list1[[i]]}
		],
		{i,Length[list1]}
	]//Transpose
]
PowerListCancel[list_]:=PowerListCancel[
	list[[;;Length[list]/2]],
	list[[1+Length[list]/2;;]]
]


ToOpMon[mon_]:=Module[{cr},
	If[mon===0,Return[
		OpMon[
			0,
			{
				Table[0,Length[ns]],
				Table[0,Length[ns]]
			}
		]
	]];
	cr=CoefficientRules[mon,zsws];
	If[Length[cr]=!=1,
		Print["***Error ToOpMon-01."];
		Return[$Failed];
	];
	OpMon[
		cr[[1,2]],
		cr[[1,1]]//PowerListCancel
	]
]


FromOpMon[opmon_]:=Module[{nCoeff,zsPower,wsPower},
	nCoeff=opmon[[1]];
	{zsPower,wsPower}=opmon[[2]];
	nCoeff*FromCoefficientRules[{zsPower->1},zs]*FromCoefficientRules[{wsPower->1},ws]
]


(* ::Subsection:: *)
(*OpPol*)


ToOpPol[pol_]:=Module[{tl,opTerms},
	tl=TermList[pol];
	opTerms=ToOpMon/@tl;
	OpPol[opTerms]
]


FromOpPol[oppol_]:=Module[{opTerms},
	opTerms=oppol[[1]];
	Total[FromOpMon/@opTerms];
]


OpPolClearVanishingTerms[oppol_]:=Module[{opTerms},
	opTerms=oppol[[1]];
	(*tbc*)
]


(* ::Section:: *)
(*SymbolicFunctions*)


SymbolicFunctions={"TOTAL","ZEROCHECK","SIMPLIFY"}


(* ::Section:: *)
(*Old codes*)


ToOperator[ibp_]:=Module[{cr,opTerms},
	cr=CoefficientRules[ibp,zsws];
	opTerms=OPMon[#[[2]],FromCoefficientRules[{#[[1]]->1},zsws]]&/@cr;
	OP[opTerms]
]





PowerMerge[list_]:=Module[{length=Length[list]/2},
	Table[list[[i]]-list[[i+length]],{i,length}]
]



CollectOp[op_]:=Module[{terms,termsGathered,newTerms},
	terms=op[[1]];
	termsGathered=GatherBy[terms,#[[2]]&];
	newTerms=OPMon[PLUS@@(#[[All,1]]),#[[1,2]]]&/@termsGathered;
	OP[newTerms]
	
]





Seed[expr_,seed_]:=expr/.Table[ns[[i]]->seed[[i]],{i,Length[seed]}]



Shift[expr_,distances_]:=expr/.Table[
	If[distances[[i]]=!=0,
		ns[[i]]->ns[[i]]+distances[[i]]
	,
		Nothing
	],
	{i,Length[Propagators]}
]


OpAct[op1_,op2_]:=Module[{terms1,terms2},


]


Join[
	(LaportaIBP[l,l]//ToOperator)[[1]],
	(-LaportaIBP[l,l]//ToOperator)[[1]]
]
OP[%]//CollectOp

%/.PLUS->Plus/.OP->Total






(* ::Section::Closed:: *)
(*Draft*)


ideal={ x x x y y + x x +y y , x x y y y +x x x +y y y, z x -1, w y -1}
vars={z,w,x,y}
ord={
{1,1,0,0},
{1,0,0,0},
{0,0,1,1},
{0,0,1,0}
}
GroebnerBasis[ideal,vars,MonomialOrder->ord]


{f1,f2,f3,f4}=ideal


LT[expr_]:=Module[{cr=CoefficientRules[expr,vars]},
	If[Expand[expr]===0,Return[0]];
	FromCoefficientRules[
		{SortBy[cr,(#[[1]]).ord&][[-1]]},
		vars
	]
]


LT/@{f1,f2,f3,f4}


s12=y f1-x f2//Expand
s12//LT


s13=z f1-x x y y f3//Expand;
s13=s13-x f3//Expand
s13//LT


s14=f1 w -f4  x x x y-y f4;

s14=s14//Expand
s14//LT


s23=f2 z - x y y y f3;
s23=s23-x x f3- y s13+f2;
s23=s23//Expand
s23//LT


s24=w f2 - x x y y f4;
s24=s24-x s14 - y y f4-y s12-y s23;
s24=s24//Expand
s24//LT





f5=f1-y s24 - 2 f1 + s23;
f5=f5//Expand
f5//LT


f6=f2-x s23-s12;
f6=f6//Expand
f6//LT


{f7,f8,f9,f10,f11}={s12,s13,s14,s23,s24}


s37= z f7 + x x x f3+f3 y y y-f3 x y - y f8 +x  f10 + f7;
s37=s37//Expand
s37//LT


s38=y y f3 - x f8-f11 y-f5+f10;
s38=s38//Expand
s38//LT


s39= w x f3 - z f9+f3 y x x ;
s39=s39//Expand
s39//LT


s310=z f10-y y y f3- x x f3-y  f8-x f3+y f3+x f10+f7;
s310=s310//Expand
s310//LT


s311=z f11+ x x y f3+ 2y y f8 +x y f3- y y f3+y f3-f8 - 2 x y f10-2 y f7-2 f11;
s311=s311//Expand
s311//LT


s35=2 y y y y y f3-x z f5+ x x y y f3+ x x x f3+x y y f3- x y f3-y y f3+f5;
s35=s35//Expand
s35//LT


s48=w f8-y z f4+s39-x x y f4;
s48=s48//Expand
s48//LT


s49=x^2 f4-y f9-f11 y-f5+f10;
s49=s49//Expand
s49//LT


s410=w f10 - x y y f4-x f9-y y f4-f9+x f4-y f7-y f10-2 f11-s311;
s410=s410//Expand
s410//LT


s411=w f11+ f4 x x x +2 f4 y y y +y f9 - f4 x y+ f4 x-y f4+f11 y+f5-f10+s310;
s411=s411//Expand
s411//LT


s45=w f5- 2 y y y y f4-y y f9-x f9-x y f4+x f4+y f4- f11 y y -y f5-y f7-f11-s311;
s45=s45//Expand
s45//LT


f12=f7+s310 x-f10;
f12=f12//Expand
f12//LT


f13=f8+s39 y+x f4;
f13=f13//Expand
f13//LT


f14=f11+ y s310 ;
f14=f14//Expand
f14//LT


{f15,f16,f17}={s39,s310,s311}


s315=y f3+x f15+f9;
s315=s315//Expand
s315//LT


s316=-x x f3+z f16+2 y y s39-f3 x+y f3-f3-f15+2 f4 x y;
s316=s316//Expand
s316//LT


s317=z f17+x y y f3+2 y y y f15+ x x f15+x f15-y f15+f3-f15+2 x y y f4+ x x s316;
s317=s317//Expand
s317//LT



