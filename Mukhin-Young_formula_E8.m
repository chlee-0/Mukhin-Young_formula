(* ::Package:: *)

(* general definition *)
(* elements of weight lattice and root lattice *)
wt/:Plus[x_wt,y_wt]:=wt@@Simplify@(List@@x+List@@y)
wt/:Times[a_,x_wt]:=wt@@Simplify@(a*(List@@x))
rt/:Plus[x_rt,y_rt]:=rt@@Simplify@(List@@x+List@@y)
rt/:Times[a_,x_rt]:=rt@@Simplify@(a*(List@@x))
(* coordinate change between weight lattice and root lattice *)
inversecartan[ty_,rk_]:=inversecartan[ty,rk]=Inverse[cartan[ty,rk]];
convert[ty_,rk_][vector_rt]:=Block[{nvector},
nvector=List@@vector;
wt@@(cartan[ty, rk].nvector)
]
convert[ty_,rk_][vector_wt]:=Block[{nvector},
nvector=List@@vector;
rt@@(inversecartan[ty,rk].nvector)
]
(* exponential of weights and roots : x[i] denotes exp[\[Alpha][i]]*)
exp[ty_,rk_][lam_rt]:=Inner[Power,Array[x,Length[lam]],List@@lam,Times];
exp[ty_,rk_][lam_wt]:=Inner[Power,Array[x,Length[lam]],List@@convert[ty,rk][lam],Times];
(* Weyl group action on weight lattice and root lattice *)
WeylR[ty_,rk_][{}][vector_wt]:=vector
WeylR[ty_,rk_][{a_Integer}][vector_wt]:=WeylR[ty,rk][{a}][vector]=Block[{func,s,nvector},
s[i_][v_]:=v-v[[i]]Transpose[cartan[ty,rk]][[i]];
nvector=List@@vector;
wt@@Simplify@(s[a][nvector])
]
WeylR[ty_,rk_][indexset_List][vector_wt]:=WeylR[ty,rk][indexset][vector]=WeylR[ty,rk][Delete[indexset,-1]][WeylR[ty,rk][{Last[indexset]}][vector]]
WeylR[ty_,rk_][indexset_List][vector_rt]:=WeylR[ty,rk][indexset][vector]=Block[{func,s,nvector,wtvec},wtvec=convert[ty,rk][vector];convert[ty,rk][WeylR[ty,rk][indexset][wtvec]]]
(* positive roots *)
posrts[ty_,rk_]:=posrts[ty,rk]=Block[{srts,rts,move},srts=Array[rt@@UnitVector[rk,#1]&,rk];rts=srts;move[x_]:=DeleteDuplicates[Join[x,Union@@(WeylR[ty,rk][{#1}]/@x&)/@Range[rk]]];While[rts!=move[rts],rts=move[rts]];Select[rts,And@@NonNegative[List@@#1]&]]


(* E8 cartan matrix *)
cartan[E,8]={{2,-1,0,0,0,0,0,0},{-1,2,-1,0,0,0,0,0},{0,-1,2,-1,0,0,0,-1},{0,0,-1,2,-1,0,0,0},{0,0,0,-1,2,-1,0,0},{0,0,0,0,-1,2,-1,0},{0,0,0,0,0,-1,2,0},{0,0,-1,0,0,0,0,2}};


(* positive roots *)
Print["positive roots : "]
Print[posrts[E,8]]


(* coset representatives of W[D7]/W[D6] inside W[E8] *)
(* each coset is given by the form {reduced expression, action on simple roots} ;  x[i] denotes exp[\[Alpha][i]] *)
WD7D6cosets={{{},{}},{{7},{x[6]->x[6] x[7],x[7]->1/x[7]}},{{6,7},{x[5]->x[5] x[6],x[6]->x[7],x[7]->1/(x[6] x[7])}},{{5,6,7},{x[4]->x[4] x[5],x[5]->x[6],x[6]->x[7],x[7]->1/(x[5] x[6] x[7])}},{{4,5,6,7},{x[3]->x[3] x[4],x[4]->x[5],x[5]->x[6],x[6]->x[7],x[7]->1/(x[4] x[5] x[6] x[7])}},{{3,4,5,6,7},{x[2]->x[2] x[3],x[3]->x[4],x[4]->x[5],x[5]->x[6],x[6]->x[7],x[7]->1/(x[3] x[4] x[5] x[6] x[7]),x[8]->x[3] x[8]}},{{2,3,4,5,6,7},{x[1]->x[1] x[2],x[2]->x[3],x[3]->x[4],x[4]->x[5],x[5]->x[6],x[6]->x[7],x[7]->1/(x[2] x[3] x[4] x[5] x[6] x[7]),x[8]->x[2] x[3] x[8]}},{{8,3,4,5,6,7},{x[2]->x[2] x[3] x[8],x[3]->x[4],x[4]->x[5],x[5]->x[6],x[6]->x[7],x[7]->1/(x[3] x[4] x[5] x[6] x[7] x[8]),x[8]->x[3]}},{{2,8,3,4,5,6,7},{x[1]->x[1] x[2],x[2]->x[3] x[8],x[3]->x[4],x[4]->x[5],x[5]->x[6],x[6]->x[7],x[7]->1/(x[2] x[3] x[4] x[5] x[6] x[7] x[8]),x[8]->x[2] x[3]}},{{3,2,8,3,4,5,6,7},{x[1]->x[1] x[2] x[3],x[2]->x[8],x[3]->x[3] x[4],x[4]->x[5],x[5]->x[6],x[6]->x[7],x[7]->1/(x[2] x[3]^2 x[4] x[5] x[6] x[7] x[8]),x[8]->x[2]}},{{4,3,2,8,3,4,5,6,7},{x[1]->x[1] x[2] x[3] x[4],x[2]->x[8],x[4]->x[4] x[5],x[5]->x[6],x[6]->x[7],x[7]->1/(x[2] x[3]^2 x[4]^2 x[5] x[6] x[7] x[8]),x[8]->x[2]}},{{5,4,3,2,8,3,4,5,6,7},{x[1]->x[1] x[2] x[3] x[4] x[5],x[2]->x[8],x[5]->x[5] x[6],x[6]->x[7],x[7]->1/(x[2] x[3]^2 x[4]^2 x[5]^2 x[6] x[7] x[8]),x[8]->x[2]}},{{6,5,4,3,2,8,3,4,5,6,7},{x[1]->x[1] x[2] x[3] x[4] x[5] x[6],x[2]->x[8],x[6]->x[6] x[7],x[7]->1/(x[2] x[3]^2 x[4]^2 x[5]^2 x[6]^2 x[7] x[8]),x[8]->x[2]}},{{7,6,5,4,3,2,8,3,4,5,6,7},{x[1]->x[1] x[2] x[3] x[4] x[5] x[6] x[7],x[2]->x[8],x[7]->1/(x[2] x[3]^2 x[4]^2 x[5]^2 x[6]^2 x[7] x[8]),x[8]->x[2]}}};
Print["number of cosets in W[D7]/W[D6] inside W[E8] : "<>ToString[Length[WD7D6cosets]]]
Print["each coset is given by the form {reduced expression, action on simple roots}"]
Print[WD7D6cosets]


(* sum over W[D6] *)
D6sum =Block[{rho,ty=E,rk=8,posRD6},
rho=wt@@ConstantArray[1,rk];
posRD6=Select[posrts[ty,rk],#[[1]]==#[[7]]==0&];
exp[ty,rk][rho]Product[1-exp[ty,rk][-\[Alpha]],{\[Alpha],posRD6}]
];
(* summands for each coset in W[D7]/W[D6] *)
D7D6summands=Block[{ty=E,rk=8,summand},
summand = 1/(1-exp[ty,rk][wt[-1,0,0,0,0,0,1,0]])*D6sum;
Table[(-1)^Length[w[[1]]]*(summand/.w[[2]]),{w,WD7D6cosets}]
]//Simplify;


(* verification : productside = sumside*)
Print["verification initiated"]
Print["it may take a couple of minutes to finish the whole computation"];
Block[{ty=E,rk=8,rho, posR0,posR2, commonfactor,difference,sumside, productside,timestart},
rho=wt@@ConstantArray[1,rk];
posR0 = Select[posrts[ty,rk],#[[1]]==0&];
posR2 = Select[posrts[ty,rk],#[[1]]==2&];
commonfactor = x[1]^20 x[2]^25 x[3]^31 x[4]^23 x[5]^16 x[6]^10 x[7]^5 x[8]^15;
Print["expanding the product side into sum of monomials..."];
productside =Expand[Factor[(1-exp[ty,rk][-wt[1,0,0,0,0,0,0,0]])* exp[ty,rk][rho]*Product[1-exp[ty,rk][-\[Alpha]],{\[Alpha],posR0}]]/commonfactor];
(* Print[productside] *);
Pause[2];
(* prepare sum side *)
sumside = (D7D6summands)*Product[1-exp[ty,rk][-\[Alpha]],{\[Alpha],posR2}]/commonfactor;
(* Print[sumside] *)
Print["started computing : the difference between productside and sumside by subtracting 14 summands from the productside sequentially"];
Print["printing {summand #, time passed, number of monomials in difference}..."];
difference = productside;
timestart=AbsoluteTime[];
Do[
difference =Expand[difference-Expand[Factor[sumside[[s]]]]];
Print[{s,Floor[AbsoluteTime[]-timestart],Length[difference]}],
{s,1,Length[sumside]}
];
Print["final value : differnece = productside - sumside"];
difference//Print
]
