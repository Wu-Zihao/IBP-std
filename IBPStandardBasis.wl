(* ::Package:: *)

(* ::Section:: *)
(*Global Variables*)


EXAMPLE="dbox"


(* ::Subsection:: *)
(*dbox*)


If[EXAMPLE==="dbox",
	SDim=9;
	ns=Table[ToExpression["n"<>ToString[i]],{i,SDim}];
	zs=Table[ToExpression["z"<>ToString[i]],{i,SDim}];
	ws=Table[ToExpression["w"<>ToString[i]],{i,SDim}];
	
]


BaikovIBP[vector_]:=Sum[
	D[vector[[i]],zs[[i]]]
	+(*here is + because \alpha_i = -n_i, n_i counts the power of zi, alpha_i counts the power of (1/zi)*)
	ns[[i]] ws[[i]] vector[[i]],
{i,Length[vector]-1}
]-gamma vector[[-1]]


If[EXAMPLE==="dbox",
	gamma=(d-1-2-3)/2;
	str="(-c1 - z1 + z2)*gen(1) + (c1 - z1 + z2)*gen(2) + (-c2 + c5 - z1 + z2)*gen(3) + (-2*c1 - z1 + z2 - z6 + z9)*gen(7) + (-2*c1 - c4 + c6 - z1 + z2)*gen(8), (-2*c1 + c2 - c5 - z6 + z9)*gen(4) + (-2*c1 - c4 + c6 - z6 + z9)*gen(5) + (-c1 - z6 + z9)*gen(6) + (-2*c1 - z1 + z2 - z6 + z9)*gen(7) + (c1 - z6 + z9)*gen(9), (c1 - c5 - z2 + z3)*gen(1) + (-c2 - z2 + z3)*gen(2) + (c2 - z2 + z3)*gen(3) + (2*c1 - z2 + z3 - z4 + 2*z6 - z9)*gen(7) + (2*c1 + c3 - 2*c5 - c6 - z2 + z3)*gen(8), (2*c1 - c2 - z4 + 2*z6 - z9)*gen(4) + (2*c1 + c3 - c6 - z4 + 2*z6 - z9)*gen(5) + (c1 + c5 - z4 + 2*z6 - z9)*gen(6) + (2*c1 - z2 + z3 - z4 + 2*z6 - z9)*gen(7) + (-c2 + 2*c5 - z4 + 2*z6 - z9)*gen(9), (-c4 - z1 + z8)*gen(1) + (-c1 - 2*c4 + c6 - z1 + z8)*gen(2) + (c3 - 2*c4 - c5 - z1 + z8)*gen(3) + (-2*c4 - z1 + z5 - z6 + z8)*gen(7) + (c4 - z1 + z8)*gen(8), (-c3 + c5 + z5 - z6)*gen(4) + (c4 + z5 - z6)*gen(5) + (-c4 + z5 - z6)*gen(6) + (-2*c4 - z1 + z5 - z6 + z8)*gen(7) + (-c1 - 2*c4 + c6 + z5 - z6)*gen(9), 2*z1*gen(1) + (-c1 + z1 + z2)*gen(2) + (-c5 + z1 + z3)*gen(3) + (z1 - z6 + z7)*gen(7) + (-c4 + z1 + z8)*gen(8) - 2*gen(10), (c5 - z3 - z6 + z7)*gen(4) + (-c4 - 2*z1 - z6 + z7 + z8)*gen(5) + (-z1 - z6 + z7)*gen(6) + (z1 - z6 + z7)*gen(7) + (-c1 - 2*z1 + z2 - z6 + z7)*gen(9), (-z1 - z6 + z7)*gen(1) + (-c1 - z1 - 2*z6 + z7 + z9)*gen(2) + (c5 - z1 - z4 + z7)*gen(3) + (-z1 + z6 + z7)*gen(7) + (-c4 - z1 + z5 - 2*z6 + z7)*gen(8), (-c5 + z4 + z6)*gen(4) + (-c4 + z5 + z6)*gen(5) + 2*z6*gen(6) + (-z1 + z6 + z7)*gen(7) + (-c1 + z6 + z9)*gen(9) - 2*gen(10)";
	tmp=StringReplace["{"<>str<>"}","gen("~~Shortest[x__]~~")":>"UnitVector[SDim+1,"<>x<>"]"]//ToExpression;
	ibpVectors=BaikovIBP/@tmp;
	vars=Complement[Variables[ibpVectors],ns,ws,zs];
	numerics=(#->1/RandomPrime[6787])&/@vars
]





(* ::Subsection::Closed:: *)
(*Stringy*)


If[EXAMPLE==="Stringy",
	SDim=5;
	ns=Table[ToExpression["n"<>ToString[i]],{i,SDim}]//Reverse;
	zs=Table[ToExpression["z"<>ToString[i]],{i,SDim}]//Reverse;
	ws=Table[ToExpression["w"<>ToString[i]],{i,SDim}]//Reverse;
	vars=Table[ToExpression["m"<>ToString[i]],{i,SDim+1,20}];
	numerics=(#->1/RandomPrime[6787])&/@vars;
]


(* ::Input:: *)
(**)


If[EXAMPLE==="Stringy",
	str="ibpVectors={5 + m10 + m12 + m13 + m14 + m16 + m17 + m19 + m7 + m8 + m9 + n1 + n2 + n3 + n4 + n5 + (2 + m12 + m16 + m19 + m20 + m7 + n1)*z1 + (4 + m12 + m13 + m16 + m17 + m18 + m19 + m20 + m7 + m8 + 2*n1 + n2)*z2 + (6 + m12 + m13 + m14 + m15 + m16 + m17 + m18 + m19 + m20 + 2*m7 + m8 + m9 + 2*n1 + 2*n2 + n3)*z3 + (8 + m10 + m11 + 2*m12 + m13 + m14 + m15 + m16 + m17 + m18 + m19 + m20 + 2*m7 + 2*m8 + m9 + 2*n1 + 2*n2 + 2*n3 + n4)*z4 + (10 + m10 + m11 + 2*m12 + 2*m13 + m14 + m15 + 2*m16 + m17 + m18 + m19 + m20 + m6 + 2*m7 + 2*m8 + 2*m9 + 2*n1 + 2*n2 + 2*n3 + 2*n4 + n5)*z5, (4 + m10 + m13 + m14 + m17 + m8 + m9 + n2 + n3 + n4 + n5)*z1 + (2 + m10 + m14 + m9 - n1 + n3 + n4 + n5)*z2 + (2 + m13 + m17 + m18 + m8 + n2)*z1*z2 + (m10 - m7 - n1 - n2 + n4 + n5)*z3 + (4 + m13 + m14 + m15 + m17 + m18 + m8 + m9 + 2*n2 + n3)*z1*z3 + (m14 + m15 + m9 - 2*n1 + n3)*z2*z3 + (-2 - m12 - m7 - m8 - n1 - n2 - n3 + n5)*z4 + (6 + m10 + m11 + m13 + m14 + m15 + m17 + m18 + 2*m8 + m9 + 2*n2 + 2*n3 + n4)*z1*z4 + (2 + m10 + m11 + m14 + m15 + m9 - 2*n1 + 2*n3 + n4)*z2*z4 + (-2 + m10 + m11 - 2*m7 - 2*n1 - 2*n2 + n4)*z3*z4 + (-4 - m12 - m13 - m16 - m7 - m8 - m9 - n1 - n2 - n3 - n4)*z5 + (8 + m10 + m11 + 2*m13 + m14 + m15 + m17 + m18 + m6 + 2*m8 + 2*m9 + 2*n2 + 2*n3 + 2*n4 + n5)*z1*z5 + (4 + m10 + m11 + m14 + m15 + m6 + 2*m9 - 2*n1 + 2*n3 + 2*n4 + n5)*z2*z5 + (m10 + m11 + m6 - 2*m7 - 2*n1 - 2*n2 + 2*n4 + n5)*z3*z5 + (-4 - 2*m12 + m6 - 2*m7 - 2*m8 - 2*n1 - 2*n2 - 2*n3 + n5)*z4*z5 + (-1 - n1)*pow(z2, 2) + (-2 - m7 - n1 - n2)*pow(z3, 2) + (-3 - m12 - m7 - m8 - n1 - n2 - n3)*pow(z4, 2) + (-4 - m12 - m13 - m16 - m7 - m8 - m9 - n1 - n2 - n3 - n4)*pow(z5, 2), (3 + m10 + m14 + m9 + n3 + n4 + n5)*z1*z2 + (1 + m10 - n2 + n4 + n5)*z1*z3 + (2 + 2*m10 - m7 - n2 + 2*n4 + 2*n5)*z2*z3 + (2 + m14 + m15 + m9 + n3)*z1*z2*z3 + (-1 - m8 - n2 - n3 + n5)*z1*z4 + (-2 - m12 - m7 - m8 - n2 - 2*n3 + 2*n5)*z2*z4 + (4 + m10 + m11 + m14 + m15 + m9 + 2*n3 + n4)*z1*z2*z4 + (-m12 - m8 - n3 + 2*n5)*z3*z4 + (m10 + m11 - 2*n2 + n4)*z1*z3*z4 + (2*m10 + 2*m11 - 2*m7 - 2*n2 + 2*n4)*z2*z3*z4 + (-3 - m13 - m8 - m9 - n2 - n3 - n4)*z1*z5 + (-6 - m12 - m13 - m16 - m7 - m8 - 2*m9 - n2 - 2*n3 - 2*n4)*z2*z5 + (6 + m10 + m11 + m14 + m15 + m6 + 2*m9 + 2*n3 + 2*n4 + n5)*z1*z2*z5 + (-4 - m12 - m13 - m16 - m8 - m9 - n3 - 2*n4)*z3*z5 + (2 + m10 + m11 + m6 - 2*n2 + 2*n4 + n5)*z1*z3*z5 + (4 + 2*m10 + 2*m11 + 2*m6 - 2*m7 - 2*n2 + 4*n4 + 2*n5)*z2*z3*z5 + (-2 - m13 - m16 - m9 - n4)*z4*z5 + (-2 + m6 - 2*m8 - 2*n2 - 2*n3 + n5)*z1*z4*z5 + (-4 - 2*m12 + 2*m6 - 2*m7 - 2*m8 - 2*n2 - 4*n3 + 2*n5)*z2*z4*z5 + (-2*m12 + 2*m6 - 2*m8 - 2*n3 + 2*n5)*z3*z4*z5 + (3 + m10 + m14 + m9 + n3 + n4 + n5)*pow(z2, 2) + (2 + m14 + m15 + m9 + n3)*z3*pow(z2, 2) + (4 + m10 + m11 + m14 + m15 + m9 + 2*n3 + n4)*z4*pow(z2, 2) + (6 + m10 + m11 + m14 + m15 + m6 + 2*m9 + 2*n3 + 2*n4 + n5)*z5*pow(z2, 2) + (2 + m10 + n4 + n5)*pow(z3, 2) + (-1 - n2)*z1*pow(z3, 2) + (-2 - m7 - n2)*z2*pow(z3, 2) + (2 + m10 + m11 + n4)*z4*pow(z3, 2) + (4 + m10 + m11 + m6 + 2*n4 + n5)*z5*pow(z3, 2) + (1 + n5)*pow(z4, 2) + (-2 - m8 - n2 - n3)*z1*pow(z4, 2) + (-4 - m12 - m7 - m8 - n2 - 2*n3)*z2*pow(z4, 2) + (-2 - m12 - m8 - n3)*z3*pow(z4, 2) + (2 + m6 + n5)*z5*pow(z4, 2) + (-3 - m13 - m8 - m9 - n2 - n3 - n4)*z1*pow(z5, 2) + (-6 - m12 - m13 - m16 - m7 - m8 - 2*m9 - n2 - 2*n3 - 2*n4)*z2*pow(z5, 2) + (-4 - m12 - m13 - m16 - m8 - m9 - n3 - 2*n4)*z3*pow(z5, 2) + (-2 - m13 - m16 - m9 - n4)*z4*pow(z5, 2), (2 + m10 + n4 + n5)*z1*z2*z3 + (-n3 + n5)*z1*z2*z4 + (-m8 - n3 + 2*n5)*z1*z3*z4 + (-m12 - m8 - 2*n3 + 4*n5)*z2*z3*z4 + (2 + m10 + m11 + n4)*z1*z2*z3*z4 + (-2 - m9 - n3 - n4)*z1*z2*z5 + (-4 - m13 - m8 - m9 - n3 - 2*n4)*z1*z3*z5 + (-8 - m12 - m13 - m16 - m8 - 2*m9 - 2*n3 - 4*n4)*z2*z3*z5 + (4 + m10 + m11 + m6 + 2*n4 + n5)*z1*z2*z3*z5 + (-2 - m13 - m9 - n4)*z1*z4*z5 + (-4 - m13 - m16 - 2*m9 - 2*n4)*z2*z4*z5 + (m6 - 2*n3 + n5)*z1*z2*z4*z5 + (-6 - 2*m13 - 2*m16 - 2*m9 - 3*n4)*z3*z4*z5 + (2*m6 - 2*m8 - 2*n3 + 2*n5)*z1*z3*z4*z5 + (-2*m12 + 4*m6 - 2*m8 - 4*n3 + 4*n5)*z2*z3*z4*z5 + (2 + m10 + n4 + n5)*z3*pow(z2, 2) + (-n3 + n5)*z4*pow(z2, 2) + (2 + m10 + m11 + n4)*z3*z4*pow(z2, 2) + (-2 - m9 - n3 - n4)*z5*pow(z2, 2) + (4 + m10 + m11 + m6 + 2*n4 + n5)*z3*z5*pow(z2, 2) + (m6 - 2*n3 + n5)*z4*z5*pow(z2, 2) + (2 + m10 + n4 + n5)*z1*pow(z3, 2) + (4 + 2*m10 + 2*n4 + 2*n5)*z2*pow(z3, 2) + (-m12 - m8 - n3 + 3*n5)*z4*pow(z3, 2) + (2 + m10 + m11 + n4)*z1*z4*pow(z3, 2) + (4 + 2*m10 + 2*m11 + 2*n4)*z2*z4*pow(z3, 2) + (-6 - m12 - m13 - m16 - m8 - m9 - n3 - 3*n4)*z5*pow(z3, 2) + (4 + m10 + m11 + m6 + 2*n4 + n5)*z1*z5*pow(z3, 2) + (8 + 2*m10 + 2*m11 + 2*m6 + 4*n4 + 2*n5)*z2*z5*pow(z3, 2) + (-2*m12 + 3*m6 - 2*m8 - 2*n3 + 3*n5)*z4*z5*pow(z3, 2) + (2 + m10 + n4 + n5)*pow(z3, 3) + (2 + m10 + m11 + n4)*z4*pow(z3, 3) + (4 + m10 + m11 + m6 + 2*n4 + n5)*z5*pow(z3, 3) + (1 + n5)*z1*pow(z4, 2) + (2 + 2*n5)*z2*pow(z4, 2) + (-1 - n3)*z1*z2*pow(z4, 2) + (3 + 3*n5)*z3*pow(z4, 2) + (-2 - m8 - n3)*z1*z3*pow(z4, 2) + (-4 - m12 - m8 - 2*n3)*z2*z3*pow(z4, 2) + (-3 - m13 - m16 - m9 - n4)*z5*pow(z4, 2) + (2 + m6 + n5)*z1*z5*pow(z4, 2) + (4 + 2*m6 + 2*n5)*z2*z5*pow(z4, 2) + (6 + 3*m6 + 3*n5)*z3*z5*pow(z4, 2) + (-1 - n3)*pow(z2, 2)*pow(z4, 2) + (-3 - m12 - m8 - n3)*pow(z3, 2)*pow(z4, 2) + (1 + n5)*pow(z4, 3) + (2 + m6 + n5)*z5*pow(z4, 3) + (-2 - m9 - n3 - n4)*z1*z2*pow(z5, 2) + (-4 - m13 - m8 - m9 - n3 - 2*n4)*z1*z3*pow(z5, 2) + (-8 - m12 - m13 - m16 - m8 - 2*m9 - 2*n3 - 4*n4)*z2*z3*pow(z5, 2) + (-2 - m13 - m9 - n4)*z1*z4*pow(z5, 2) + (-4 - m13 - m16 - 2*m9 - 2*n4)*z2*z4*pow(z5, 2) + (-6 - 2*m13 - 2*m16 - 2*m9 - 3*n4)*z3*z4*pow(z5, 2) + (-2 - m9 - n3 - n4)*pow(z2, 2)*pow(z5, 2) + (-6 - m12 - m13 - m16 - m8 - m9 - n3 - 3*n4)*pow(z3, 2)*pow(z5, 2) + (-3 - m13 - m16 - m9 - n4)*pow(z4, 2)*pow(z5, 2), (1 + n5)*z1*z2*z3*z4 + (-1 - n4)*z1*z2*z3*z5 + (-2 - m9 - n4)*z1*z2*z4*z5 + (-4 - m13 - m9 - 2*n4)*z1*z3*z4*z5 + (-8 - m13 - m16 - 2*m9 - 4*n4)*z2*z3*z4*z5 + (2 + m6 + n5)*z1*z2*z3*z4*z5 + (1 + n5)*z3*z4*pow(z2, 2) + (-1 - n4)*z3*z5*pow(z2, 2) + (-2 - m9 - n4)*z4*z5*pow(z2, 2) + (2 + m6 + n5)*z3*z4*z5*pow(z2, 2) + (1 + n5)*z1*z4*pow(z3, 2) + (2 + 2*n5)*z2*z4*pow(z3, 2) + (-1 - n4)*z1*z5*pow(z3, 2) + (-2 - 2*n4)*z2*z5*pow(z3, 2) + (-6 - m13 - m16 - m9 - 3*n4)*z4*z5*pow(z3, 2) + (2 + m6 + n5)*z1*z4*z5*pow(z3, 2) + (4 + 2*m6 + 2*n5)*z2*z4*z5*pow(z3, 2) + (1 + n5)*z4*pow(z3, 3) + (-1 - n4)*z5*pow(z3, 3) + (2 + m6 + n5)*z4*z5*pow(z3, 3) + (1 + n5)*z1*z2*pow(z4, 2) + (2 + 2*n5)*z1*z3*pow(z4, 2) + (4 + 4*n5)*z2*z3*pow(z4, 2) + (-3 - m13 - m9 - n4)*z1*z5*pow(z4, 2) + (-6 - m13 - m16 - 2*m9 - 2*n4)*z2*z5*pow(z4, 2) + (2 + m6 + n5)*z1*z2*z5*pow(z4, 2) + (-9 - 2*m13 - 2*m16 - 2*m9 - 3*n4)*z3*z5*pow(z4, 2) + (4 + 2*m6 + 2*n5)*z1*z3*z5*pow(z4, 2) + (8 + 4*m6 + 4*n5)*z2*z3*z5*pow(z4, 2) + (1 + n5)*pow(z2, 2)*pow(z4, 2) + (2 + m6 + n5)*z5*pow(z2, 2)*pow(z4, 2) + (3 + 3*n5)*pow(z3, 2)*pow(z4, 2) + (6 + 3*m6 + 3*n5)*z5*pow(z3, 2)*pow(z4, 2) + (1 + n5)*z1*pow(z4, 3) + (2 + 2*n5)*z2*pow(z4, 3) + (3 + 3*n5)*z3*pow(z4, 3) + (-4 - m13 - m16 - m9 - n4)*z5*pow(z4, 3) + (2 + m6 + n5)*z1*z5*pow(z4, 3) + (4 + 2*m6 + 2*n5)*z2*z5*pow(z4, 3) + (6 + 3*m6 + 3*n5)*z3*z5*pow(z4, 3) + (1 + n5)*pow(z4, 4) + (2 + m6 + n5)*z5*pow(z4, 4) + (-1 - n4)*z1*z2*z3*pow(z5, 2) + (-2 - m9 - n4)*z1*z2*z4*pow(z5, 2) + (-4 - m13 - m9 - 2*n4)*z1*z3*z4*pow(z5, 2) + (-8 - m13 - m16 - 2*m9 - 4*n4)*z2*z3*z4*pow(z5, 2) + (-1 - n4)*z3*pow(z2, 2)*pow(z5, 2) + (-2 - m9 - n4)*z4*pow(z2, 2)*pow(z5, 2) + (-1 - n4)*z1*pow(z3, 2)*pow(z5, 2) + (-2 - 2*n4)*z2*pow(z3, 2)*pow(z5, 2) + (-6 - m13 - m16 - m9 - 3*n4)*z4*pow(z3, 2)*pow(z5, 2) + (-1 - n4)*pow(z3, 3)*pow(z5, 2) + (-3 - m13 - m9 - n4)*z1*pow(z4, 2)*pow(z5, 2) + (-6 - m13 - m16 - 2*m9 - 2*n4)*z2*pow(z4, 2)*pow(z5, 2) + (-9 - 2*m13 - 2*m16 - 2*m9 - 3*n4)*z3*pow(z4, 2)*pow(z5, 2) + (-4 - m13 - m16 - m9 - n4)*pow(z4, 3)*pow(z5, 2)};";
	StringReplace[str,"pow("~~Shortest[x__]~~")":>"Power["<>x<>"]"]//ToExpression;
]


(* ::Section:: *)
(*Data Structures*)


(* ::Subsection::Closed:: *)
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


(* ::Subsection::Closed:: *)
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


(* ::Subsubsection::Closed:: *)
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
UNIT=ToIndPol[1];


(* ::Subsubsection::Closed:: *)
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


(* ::Subsubsection::Closed:: *)
(*Add and Subtraction*)


Mns[x_IndPol]:=IndPol[Mns/@TermList[x]];
Add[x_IndMon,y_IndMon]:=IndPol[{x,y}](*//Collected*)
Add[x_IndMon,y_IndPol]:=IndPol[Append[y//TermList,x]](*//Collected*)
Add[x_IndPol,y_IndMon]:=Add[y,x](*//Collected*)
Add[x_IndPol,y_IndPol]:=IndPol[Join[x//TermList,y//TermList]](*//Collected*)

Subtraction[x_IndMon,y_IndMon]:=Add[x,y//Mns]
Subtraction[x_IndMon,y_IndPol]:=Add[x,y//Mns]
Subtraction[x_IndPol,y_IndMon]:=Add[x,y//Mns]
Subtraction[x_IndPol,y_IndPol]:=Add[x,y//Mns]


(* ::Subsubsection::Closed:: *)
(*Act*)


Act[x_IndPol,y_IndMon]:=IndPol[Act[#,y]&/@TermList[x]](*//Collected*)
Act[x_IndMon,y_IndPol]:=IndPol[Act[x,#]&/@TermList[y]](*//Collected*)
Act[x_IndPol,y_IndPol]:=Module[{xTerms=x//TermList,yTerms=y//TermList},
	IndPol[
		Table[
			Act[xTerms[[i]],yTerms[[j]]],
			{i,Length[xTerms]},
			{j,Length[yTerms]}
		]//Flatten
	]
](*//Collected*)
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



(*I will not use this -- 2025.8.19*)
LT//ClearAll
LTCOUNTER=0;(*for debug*)
LT[x_IndPol,directions_,ordering_]:=(LTCOUNTER++;SortBy[
	x//Collected//TermList,
	ordering[DiagonalMatrix[directions].(#//Indices)
]&][[-1]]
)


SemiCollectToLT[x_IndPol,directions_,ordering_]:=Module[
{terms,termsGrouped,termsGroupedSorted,
apparentLTIndex,apparentLTCoeff,finalLT,semicollectedIndPol,timer=AbsoluteTime[],
termsGroupedWeight
},
	LTCOUNTER++;
	
	
	terms=x//TermList;
	If[terms==={},Return[{ZERO,ZERO}]];
	
	termsGrouped=GatherBy[terms,Indices];
	
	
	termsGroupedWeight=DiagonalMatrix[directions].(#[[1]]//Indices)&/@termsGrouped;
	timer=AbsoluteTime[];
	termsGroupedWeight=ordering/@termsGroupedWeight;
	COUNTERLTSpecial+=Length[termsGroupedWeight];
	TIMERSemiCollectToLT+=(AbsoluteTime[]-timer);
	
	termsGroupedSorted=SortBy[
		termsGrouped,
		ordering[DiagonalMatrix[directions].(#[[1]]//Indices)]&
	];
	
	
	
	termsGroupedSorted=termsGroupedSorted//Reverse;
	
	
	
	While[True,
		apparentLTIndex=termsGroupedSorted[[1,1]]//Indices;
		apparentLTCoeff=Total[Coeff/@termsGroupedSorted[[1]]]//Simplifier;
		termsGroupedSorted=termsGroupedSorted[[2;;-1]];
		If[apparentLTCoeff=!=0,Break[]];
		If[Length[termsGroupedSorted]===0,
			Return[{ZERO,ZERO}]
		]
	];
	
	
	finalLT=IndMon[apparentLTCoeff,apparentLTIndex];
	termsGroupedSorted=Join[{
		{finalLT}
	},termsGroupedSorted];
	semicollectedIndPol=IndPol[Flatten[termsGroupedSorted]];
	
	
	{semicollectedIndPol,finalLT}

]
HSemiCollectToLT[x_,directions_,ordering_]:=FromIndPol/@SemiCollectToLT[x//ToIndPol,directions,ordering]


(* ::Subsubsection::Closed:: *)
(*Cornerized*)


Cornerized//ClearAll
Options[Cornerized]={ReturnRefMon->False}
Cornerized[xx_IndPol,directions_,OptionsPattern[]]:=Module[{refMon,indices,refInd,x},
	x=Collected[xx,Simplification->True];
	If[x===ZERO,
		If[OptionValue[ReturnRefMon],
			Return[{UNIT,ZERO}]
		,
			Return[ZERO]
		];
	];
	indices=Indices/@(x//TermList);
	indices=DiagonalMatrix[directions].#&/@indices;
	refInd=Min/@Transpose[indices];
	refInd=DiagonalMatrix[directions].refInd;
	refMon=IndMon[1,-refInd];
	If[OptionValue[ReturnRefMon],
		Return[{refMon,Act[refMon,x]}];
	,
		Return[Act[refMon,x]];
	];
	
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



(* ::Subsection::Closed:: *)
(*Reduced*)


Generators[x_IndPolIdeal]:=x[[1]]
TrackerData[x_IndPolIdeal]:=x[[2]]
OperationMatrix[x_Tracker]:=x[[1]]
OriginalGenerators[x_Tracker]:=x[[2]]


Reduced//ClearAll
Options[Reduced]={ProgressIndicatorLevel->0}
Reduced[f_IndPol,g_IndPol,directions_,ordering_,OptionsPattern[]]:=Module[
{quotient,remainder,rest,gLT,restLT,q1,i=0,loopCounter=0,REPORTLEVEL=4,timer=AbsoluteTime[],result},
	rest=f;
	quotient=ZERO;
	remainder=ZERO;
	
	(*gLT=LT[Collected[g,Simplification->True],directions,ordering];*)
	
	(*above replaced by the following*)
	
	{g,gLT}=SemiCollectToLT[g,directions,ordering];
	
	While[True,
		loopCounter++;
		(*Print["          ",loopCounter," : ",LTCOUNTER," : ",COUNTER];
		*)
		(*If[loopCounter\[GreaterEqual]5000,Break[]];*)
		
		(*rest=Collected[rest,Simplification->True];
		If[rest===ZERO,Break[]];
		restLT=LT[rest,directions,ordering];*)
		
		(*above replaced by the following*)
		
		timer=AbsoluteTime[];
		{rest,restLT}=SemiCollectToLT[rest,directions,ordering];
		TIMERReduced1+=(AbsoluteTime[]-timer);
		
		If[rest===ZERO,Break[]];
		
		If[OptionValue[ProgressIndicatorLevel]>=REPORTLEVEL,
			Print[
				StringJoin[Table["\t",REPORTLEVEL]],
				"Reduced(",
				"",loopCounter,
				"): #r_terms=", rest//TermList//Length
			]
		];
		
		If[IndMonDivisibleQ[restLT,gLT,directions],
			q1=Division[restLT,gLT];(*perhaps, left/right division can affect performance*)
			rest=Subtraction[rest,Act[q1,g]];
			quotient=Add[quotient,q1]
		,
			rest=Subtraction[rest,restLT];
			remainder=Add[remainder,restLT];
		]
	];
	
	result=Collected[#,Simplification->True]&/@{quotient,remainder};
	
	result
]

(*DO NOT devide cell! because there was Reduce//ClearAll in the beginning in this cell.*)
(*================================================*)
(*reduction towards an IndPolIdeal*)
(*================================================*)
Reduced[f_IndPol,g_IndPolIdeal,directions_,ordering_,OptionsPattern[]]:=Module[
{
	quotients=Table[ZERO,Length[g//Generators]],
	remainder=f,
	i=1,n=0,
	q,newRemainder,gens=g//Generators,
	loopCounter=0,
	REPORTLEVEL=3,
	timer=AbsoluteTime[]
},
	While[True,
		(*Print["    ",loopCounter," : ",LTCOUNTER," : ",COUNTER];*)
		
		(*If[loopCounter>=500,Break[]];*)
		loopCounter++;
		If[OptionValue[ProgressIndicatorLevel]>=REPORTLEVEL,
			Print[
				StringJoin[Table["\t",REPORTLEVEL]],
				"Reduced(",
				"",loopCounter,
				"): #r_terms=", remainder//TermList//Length
			]
		];
		newRemainder=remainder;(*maybe this is not needed?*)
		{q,newRemainder}=Reduced[newRemainder,gens[[i]],directions,ordering,
			ProgressIndicatorLevel->OptionValue[ProgressIndicatorLevel]
		];
		
		
		
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
	TIMERReduced2+=(AbsoluteTime[]-timer);
	{quotients,remainder}
]



HReduced//ClearAll;
HReduced[f_,g_,directions_,ordering_]:=Module[{res},
	If[Head[g]===List,
		res=Reduced[f//ToIndPol,IndPolIdeal[ToIndPol/@g,None],directions,ordering,ProgressIndicatorLevel->OptionValue[ProgressIndicatorLevel]];
		res={FromIndPol/@res[[1]],FromIndPol[res[[2]]]};
	,
		res=Reduced[f//ToIndPol,g//ToIndPol,directions,ordering,ProgressIndicatorLevel->OptionValue[ProgressIndicatorLevel]];
		res=FromIndPol/@res;
	];
	res
]


(* ::Subsection::Closed:: *)
(*IndPolMatrix*)


IndPolDiagonalMatrix//ClearAll
IndPolDiagonalMatrix[d_List]:=Table[
	
	If[i==j,d[[i]],ZERO],
	{i,Length[d]},
	{j,Length[d]}
]


IndPolListAdd[l1_List,l2_List]:=Module[{len},
	len=Length[l1];
	If[Length[l2]=!=len,
		Print["Error: IndPolListAdd_list_length_mismatch"];
		Return[$Failed]
	];
	Table[Add[l1[[i]],l2[[i]]],{i,len}]
]
HIndPolListAdd[l1_List,l2_List]:=FromIndPol/@IndPolListAdd[ToIndPol/@l1,ToIndPol/@l2]


IndPolListSubtraction[l1_List,l2_List]:=Module[{len},
	len=Length[l1];
	If[Length[l2]=!=len,
		Print["Error: IndPolListSubtraction_list_length_mismatch"];
		Return[$Failed]
	];
	Table[Subtraction[l1[[i]],l2[[i]]],{i,len}]
]
HIndPolListSubtraction[l1_List,l2_List]:=FromIndPol/@IndPolListSubtraction[ToIndPol/@l1,ToIndPol/@l2]


(*this function is non-commutative!*)
IndPolListDotAct[l1_List,l2_List]:=Module[{len,result=ZERO,i},
	len=Length[l1];
	If[Length[l2]=!=len,
		Print["Error: IndPolListDotAct_list_length_mismatch"];
		Return[$Failed]
	];
	For[i=1,i<=len,i++,
		result=Add[
			result,
			Act[l1[[i]],l2[[i]]]
		]
	];
	result
]
HIndPolListDotAct[l1_List,l2_List]:=FromIndPol/@IndPolListDotAct[ToIndPol/@l1,ToIndPol/@l2]


(*this function is non-commutative!
also, be careful, there are two sense of left non-commutative:
1. operator act
2. matrix multiplication
Here, m1 left multiply to m2, and entris of m1 ALSO left act on entries of m2
In principle, it is allowed that could be m1 left multiply to m2, but entris of m1 RIGHT act on entries of m2, but it seems that this is not useful
If someone wants this , he/she can use Transpose on the matrix

*)
IndPolMatrixDotAct[m1_List,m2_List]:=Module[{dim1,dim2,result=ZERO,i},
	dim1=Dimensions[m1];
	dim2=Dimensions[m2];
	If[Length[dim1]=!=2||Length[dim2]=!=2,
		Print["Error: IndPolMatrixDotAct_not_matrix"];
		Return[$Failed]
	];
	If[dim1[[2]]=!=dim2[[1]],
		Print["Error: IndPolMatrixDotAct_dimension_mismatch:",dim1,",",dim2];
		(*Print["m1=",m1];
		Print["m2=",m2];*)
		Return[$Failed]
	];
	Table[IndPolListDotAct[m1[[i]],m2[[All,j]]],{i,dim1[[1]]},{j,dim2[[2]]}]
]
HIndPolMatrixDotAct[m1_List,m2_List]:=Map[FromIndPol,
	IndPolMatrixDotAct[
		Map[ToIndPol,m1,{2}],
		Map[ToIndPol,m2,{2}]
	]
,{2}]


(*these functions are non-commutative!*)
IndPolListDotActOnMatrix[x_List,y_List]:=IndPolMatrixDotAct[{x},y][[1]]
IndPolMatrixDotActOnList[x_List,y_List]:=IndPolMatrixDotAct[x,{#}&/@y][[All,1]]

HIndPolListDotActOnMatrix[x_List,y_List]:=FromIndPol/@IndPolListDotActOnMatrix[
	ToIndPol/@x,
	Map[ToIndPol,y,{2}]
]
HIndPolMatrixDotActOnList[x_List,y_List]:=FromIndPol/@IndPolMatrixDotActOnList[
	Map[ToIndPol,x,{2}],
	ToIndPol/@y
]



(* ::Subsection:: *)
(*IndPolIdeal SelfReduction*)


SelfReduction//ClearAll
Options[SelfReduction]={"Tracking"->False,ProgressIndicatorLevel->0}
SelfReduction[g_IndPolIdeal,directions_,ordering_,OptionsPattern[]]:=Module[
{
loopCounter=0,result,
gens=g//Generators,
i=1,n=0,j=0,divisors,r,qs,refMons,rRefMon,
operationMatrix,originalGenerators,REPORTLEVEL=2
},
	If[OptionValue["Tracking"],
		{refMons,gens}=Transpose[Cornerized[#,directions,ReturnRefMon->True]&/@gens];
		
		If[TrackerData[g]===None,
			operationMatrix=IndPolDiagonalMatrix[refMons];
			
			originalGenerators=Generators[g];
		,
			operationMatrix=IndPolMatrixDotAct[
				IndPolDiagonalMatrix[refMons],
				g//TrackerData//OperationMatrix
			];
		
			originalGenerators=g//TrackerData//OriginalGenerators
		]
	,
		gens=Cornerized[#,directions]&/@gens;
	];
	
	
	
	While[True,
	
		loopCounter++;
		If[OptionValue[ProgressIndicatorLevel]>=REPORTLEVEL,
			Print[
				StringJoin[Table["\t",REPORTLEVEL-1]],
				"SelfReduction(",
				"",loopCounter,
				"): #gen=", gens//Length
			]
		];
		(*Print[loopCounter," : ",LTCOUNTER," : ",COUNTER];*)
		
		(*If[loopCounter>=5,Break[]];*)
		
		
		j++;(*for debug*)
		
		If[Length[gens]<=1,Break[]];
		If[i>Length[gens],i-=Length[gens]];(*loop*)
		
		(*divisors=DeleteCases[gens,gens[[i]]]; (*I modified this to the next line ---2025.8.20*)*)
		
		divisors=Delete[gens,i];
		
		{qs,r}=Reduced[gens[[i]],IndPolIdeal[divisors,None(*no traker needed*)],directions,ordering,
			ProgressIndicatorLevel->OptionValue[ProgressIndicatorLevel]
		];
		
		(*r=Collected[r];(*is this needed?*) currently, no. We have Collected inside Cornerized.*)
		
		If[OptionValue["Tracking"],
			{rRefMon,r}=Cornerized[r,directions,ReturnRefMon->True];
		,
			r=Cornerized[r,directions];
		];
		
		(*Print["gens=",FromIndPol/@gens,"  r=",FromIndPol@r,"    i=",i];*)
		
		If[r===ZERO,
			(*Print["000"];*)
			gens=divisors;
			If[OptionValue["Tracking"],
				operationMatrix=Delete[operationMatrix,i];
			];
			n=0;(*n counts for how many times that the division does nothing*)
		,
			
			If[Subtraction[gens[[i]],r]===ZERO,
				n++;(*nothing changes*)
				(*Print["==="];*)
			,
				gens[[i]]=r;
				If[OptionValue["Tracking"],
					operationMatrix[[i]]=IndPolListSubtraction[
						operationMatrix[[i]],
						IndPolListDotActOnMatrix[
							qs,
							Delete[operationMatrix,i]
						]
					]
				];
				(*If[Delete[operationMatrix,i]===IndPolDiagonalMatrix[],(*probe20250820=operationMatrix;*)Return[$Failed]];(*debug*)*)
				(*Print["mmm"];*)
				n=0
			];
			i++;(*moves the label if the i-th gen is not removed ( will be removed if r===0)*)
		];
		
		
		
		
		If[n>=Length[gens],Break[]];
		If[j>10,Break[]]
	];
	If[OptionValue["Tracking"],
		result=IndPolIdeal[gens,Tracker[operationMatrix,originalGenerators]]
	,
		result=IndPolIdeal[gens,None]
	];
	result
	
];
(*human readable*)
HSelfReduction//ClearAll
Options[HSelfReduction]=Options[SelfReduction]
HSelfReduction[gens_,directions_,ordering_,OptionsPattern[]]:=Module[{reduction,result,trackerData},
	reduction=SelfReduction[IndPolIdeal[ToIndPol/@gens,None],directions,ordering,
		"Tracking"->OptionValue["Tracking"],
		ProgressIndicatorLevel->OptionValue[ProgressIndicatorLevel]
	];
	If[OptionValue["Tracking"],
		trackerData=reduction//TrackerData;
		result={
			FromIndPol/@Generators[reduction],
			{
				Map[FromIndPol,trackerData//OperationMatrix,{2}],
				FromIndPol/@OriginalGenerators[trackerData]
			}
		}
	,
		result=FromIndPol/@Generators[reduction]
	];
	result
]


.


0\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]\[AliasDelimiter]


(* ::Section::Closed:: *)
(*0Draft*)


ResetTimerAndCounters[]:=(
COUNTER=0;
LTCOUNTER=0;
TIMER=0;
TIMERReduced1=0;
TIMERReduced2=0;
MAXONECETIME=0;
TIMERSemiCollectToLT=0;
COUNTERLTSpecial=0;
SimplificationTimers={};
)
RTC:=(Print["timers and counters reset;"];ResetTimerAndCounters[])


RTC
probe20250819//Clear
AbsoluteTiming[reduced=
	HSelfReduction[ibpVectors/.numerics,Table[-1,SDim],RevDegLexiGOrdering,Tracking->False,ProgressIndicatorLevel->4]
;]



probe20250819;
MAXONECETIME
TIMER
COUNTER           
COUNTER*MAXONECETIME  
TIMERSemiCollectToLT
LTCOUNTER
COUNTERLTSpecial  
TIMERReduced1
TIMERReduced2         
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                     


ToIndPol/@reduced;
TermList/@%;
Map[Indices,%,{2}];
Flatten[%,1];
DeleteDuplicates[%]//Sort


Select[SimplificationTimers,#<0.001&]//Total
SimplificationTimers//Total


AbsoluteTiming[reduced[[1]]//ToIndPol]
AbsoluteTiming[%[[2]]//FromIndPol]





AbsoluteTiming[CoefficientRules[%155[[2]],Join[zs,ws]]]


TIMER


TIMER


Select[SimplificationTimers,#>0.001&]//Length


%497/4166


Histogram[Select[SimplificationTimers,#>1&]]


reduced//Together


(* ::Section:: *)
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
