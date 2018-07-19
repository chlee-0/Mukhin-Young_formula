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


(* F4 cartan matrix *)
cartan[F,4]={{2,-1,0,0},{-1,2,-1,0},{0,-2,2,-1},{0,0,-1,2}};


(* positive roots *)
Print["positive roots : "]
Print[posrts[F,4]]


(* coset representatives of W[B3]/W[B2] inside W[F4] *)
(* each coset is given by the form {reduced expression, action on simple roots} ;  x[i] denotes exp[\[Alpha][i]] *)
WB3B2cosets={{{},{}},{{1},{x[1]->1/x[1],x[2]->x[1] x[2]}},{{2,1},{x[1]->1/(x[1] x[2]),x[2]->x[1],x[3]->x[2] x[3]}},{{3,2,1},{x[1]->1/(x[1] x[2] x[3]^2),x[2]->x[1],x[3]->x[2] x[3],x[4]->x[3] x[4]}},{{2,3,2,1},{x[1]->1/(x[1] x[2]^2 x[3]^2),x[2]->x[1] x[2],x[4]->x[2] x[3] x[4]}},{{1,2,3,2,1},{x[1]->1/(x[1] x[2]^2 x[3]^2),x[4]->x[1] x[2] x[3] x[4]}}};
Print["number of cosets in W[B3]/W[B2] inside W[F4] : "<>ToString[Length[WB3B2cosets]]]
Print["each coset is given by the form {reduced expression, action on simple roots}"]
Print[WB3B2cosets]


(* sum over W[B2] *)
B2sum =Block[{rho,ty=F,rk=4,posRB2},
rho=wt@@ConstantArray[1,rk];
posRB2=Select[posrts[ty,rk],#[[1]]==#[[4]]==0&];
exp[ty,rk][rho]Product[1-exp[ty,rk][-\[Alpha]],{\[Alpha], posRB2}]
];
(* summands for each coset in W[B3]/W[B2] *)
B3B2summands=Block[{ty=F,rk=4,summand},
summand = 1/(1-exp[ty,rk][wt[1,0,0,-2]])*B2sum;
Table[(-1)^Length[w[[1]]]*(summand/.w[[2]]),{w,WB3B2cosets}]
]//Simplify;


(* verification : productside = sumside*)
Print["verification initiated"]
Block[{ty=F,rk=4,rho, posR0,posR2, commonfactor,difference,sumside, productside,timestart},
rho=wt@@ConstantArray[1,rk];
posR0 = Select[posrts[ty,rk],#[[4]]==0&];
posR2 = Select[posrts[ty,rk],#[[4]]==2&];
commonfactor = 1;
Print["expanding the product side into sum of monomials..."];
productside =Expand[Factor[(1-exp[ty,rk][wt[0,0,0,-2]])* exp[ty,rk][rho]*Product[1-exp[ty,rk][-\[Alpha]],{\[Alpha],posR0}]]/commonfactor];
(* Print[productside] *);
Pause[2];
(* prepare sum side *)
sumside = (B3B2summands)*Product[1-exp[ty,rk][-\[Alpha]],{\[Alpha],posR2}]/commonfactor;
(* Print[sumside] *)
Print["started computing : the difference between productside and sumside by subtracting 6 summands from the productside sequentially"];
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
