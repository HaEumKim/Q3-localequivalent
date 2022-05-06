(* ::Package:: *)

BeginPackage["LocalCliffordEquivalent`","Q3`"]

`LocalCliffordEquivalent`$Version = StringJoin[
  $Input, " v",
  StringSplit["$Revision: 1.01 $"][[2]], " (",
  StringSplit["$Date: 2022-05-05 23:57:21 $"][[2]], ") ",
  "Ha-Eum Kim"
 ];
(*Quisso Form*)
{ GraphStateQ , StabilizerStandardGenerator };
{ QuissoGraphsystem };
{ MultiplyFold , SupermapFold };

(*Gottesman Form*)
{ GottesmanReduce , GottesmanReducesystem };
{ GottesmanGraphsystem};

(*Graph Form*)
{ GottesmanLocalEquivalent , LocalEquivalent , LocalEquivalentQ };
{ GraphLocalComplement};
{ FindLocalComplementPath };

(*test for PRA70,034302 Lemma 1*)
{ localEquivalentQ}

Begin["`Private`"]


GraphStateQ::usage="GraphStateQ[state] returns True if the state is a graph state, and False otherwise.\n The state may be a column vector or expressed in terms of Ket[...] or Ket[<|...|>]."
GraphStateQ::notqbt = "`` is not a state vector for qubits."

GraphStateQ[vec_?VectorQ] := (
  Message[GraphStateQ::notqbt, vec];
  False
 ) /; Not @ IntegerQ @ Log[2, Length @ vec]

GraphStateQ[vec_?VectorQ] := Module[
  { rho = Dyad[vec, vec], tsr , vl , ky, xztsr},
    
	tsr = Most @ ArrayRules @ PauliDecompose[rho];
	vl = Values @ tsr;
	ky= Keys @ tsr;
	Catch[
		If[  !TrueQ[Equal @@ Abs[ vl ] ], Throw[False] ];
		xztsr = GroupBy[ Select[ ky, FreeQ[#,3]&&SameQ[Count[#,2],1]&], Position[#,2]& ];
		If[ !SameQ[ Length[xztsr] , Log[2, Length @ vec]] , Throw[False]];
		If[ !ContainsOnly[Values[xztsr,Length],{1}],Throw[False]];
		True
		]
];

GraphStateQ[expr_] := GraphStateQ[Matrix @ expr]

GraphStateQ[expr_, ss:{__?QubitQ}] := GraphStateQ[Matrix[ expr , ss ] ]


(**** <StabilizerStandardGenerator> ****)
StabilizerStandardGenerator::usage="StabilizerStandardGenerator[state] finds a generating set of Pauli operators that stabilize state. If state is a graph state, it returns generators by standard form.\n The state may be a column vector or expressed in terms of Ket[...] or Ket[<|...|>].\n StabilizerStandardGenerator[state,{s1,s2...}] assumes that state belongs to the Hilbert space associated with qubits {s1,s2,...}.\n StabilizerStandardGenerator[graph] returns standard generating set of Pauli operators that stabilize the graph state associated with graph."
StabilizerStandardGenerator::notss = "`` is not a stabilizer state."

StabilizerStandardGenerator[vec_?VectorQ] := Module[
  { sgn , mm },
  {sgn , mm } = getStabilizerStandardGenerator[vec];
  If[ FailureQ[mm],
    Message[StabilizerStandardGenerator::notss, vec];
    Return[{}]
   ];
  (Matrix@*FromGottesmanVector /@ mm) * sgn
 ] /; IntegerQ @ Log[2, Length @ vec]


StabilizerStandardGenerator[expr_] := StabilizerStandardGenerator[expr, Qubits @ expr]

StabilizerStandardGenerator[expr_, ss:{__?QubitQ}] := Module[
  { sgn , mm },
  {sgn , mm } = getStabilizerStandardGenerator @ Matrix[expr , ss ];
  If[ FailureQ[mm],
    Message[StabilizerStandardGenerator::notss, expr];
    Return[{}]
   ];
  Elaborate[ (FromGottesmanVector[ # , ss ]& /@ mm) * sgn ]
 ]
 
 StabilizerStandardGenerator[expr_, {}] := Module[
  { sgn , mm },
  {sgn , mm } = getStabilizerStandardGenerator @ Matrix[expr ];
  If[ FailureQ[mm],
    Message[StabilizerStandardGenerator::notss, expr];
    Return[{}]
   ];
  Elaborate[ (FromGottesmanVector[ # ]& /@ mm) * sgn ]
 ]


getStabilizerStandardGenerator[vec_?VectorQ] := Module[
  { rho = Dyad[vec, vec],
    tsr , mat },
  tsr = Association @ Most @ ArrayRules @ PauliDecompose[rho];
  If[ Not[Equal @@ Abs[Values @ tsr]],
    Return[$Failed]
   ];
  tsr = Sign /@ KeyMap[#/.{1->Sequence[0,0],2->Sequence[1,0],3->Sequence[1,1],4->Sequence[0,1]}&, tsr];
  mat = Keys[tsr];
  mat = GottesmanReduce[ mat ][[ ;; Log[ 2 , Length @ vec ] ]];
  
  { tsr[#]& /@ mat , mat }
 ]


StabilizerStandardGenerator[g_Graph] := StabilizerStandardGenerator @ GraphState[g]

StabilizerStandardGenerator[g_Graph, ss:{__?QubitQ}] :=
  StabilizerStandardGenerator[GraphState[g, FlavorNone @ ss], FlavorNone @ ss]


(* function for Gottesman Form*)

GottesmanReduce::usage=" GottesmanReduce[m] gives the row-reduced form of the list of Gottesman vectors m.\n GottesmanReduce[xmat,zmat] gives the row-reduced form of the list of the X- and Z-part of the list of Gottesman vectors. Same for GottesmanReduce[{xmat,zmat}]."
GottesmanReduce[ { xx_?MatrixQ , zz_?MatrixQ } ]:= GottesmanReduce[xx,zz]/; ArrayQ @ {xx, zz}

GottesmanReduce[ xx_?MatrixQ , zz_?MatrixQ ]:=Module[
{d = Length @ First @ xx , xz },
		
	xz = Join[ xx , zz , 2 ];
	xz = RowReduce[ xz , Modulus -> 2 ];
	{ xz[[ ;; , ;; d ]] , xz[[ ;; , d+1 ;; ]] }

]/;ArrayQ @ {xx, zz}

GottesmanReduce[ mm_?MatrixQ ]:=Module[
{ xx , zz },

	{ xx , zz } = GottesmanSplit[ mm ];
	{ xx , zz } = GottesmanReduce[ xx , zz ];
	GottesmanMerge[ xx , zz ]

];


GottesmanReducesystem::usage=" GottesmanReduce[m] gives the row-reduced form of the list of Gottesman vectors m and the transformation matrix.\n GottesmanReduce[xmat,zmat] gives the row-reduced form of the list of the X- and Z-part of the list of Gottesman vectors and the transformation matrix. Same for GottesmanReduce[{xmat,zmat}]."

GottesmanReducesystem[ { xx_?MatrixQ , zz_?MatrixQ } ]:= GottesmanReducesystem[xx,zz]/; ArrayQ @ {xx, zz}

GottesmanReducesystem[ xx_?MatrixQ , zz_?MatrixQ ]:=Module[
{d , l , xz },
	{ d, l } = Dimensions @ xx;	
	xz = Join[ xx , zz , IdentityMatrix @ d , 2 ];
	xz = RowReduce[ xz , Modulus -> 2 ];
	{ xz[[ ;; , ;; l ]] , xz[[ ;; , l+1 ;; 2l ]] , xz[[;; , 2l+1 ;; ]] }

]/; ArrayQ @ {xx, zz}

GottesmanReducesystem[ mm_?MatrixQ ]:=Module[
{ xx , zz , pp },

	{ xx , zz } = GottesmanSplit[ mm ];
	{ xx , zz , pp } = GottesmanReducesystem[ xx , zz ];
	{ GottesmanMerge[ xx , zz ] , pp }

];


GottesmanGraphsystem::usage="GottesmanGraphsystem[ gotvecs ] gives list of matrix and graph { lmat , graph } for Gottesman form of generator gotvecs of stabilizer subgroup of the Pauli group that stabilizes a state, where lmat represent Gottesman matrix form of local clifford operator that transform the state to graph state associated with graph."

GottesmanGraphsystem[ gnr_?MatrixQ , opts___?OptionQ] := MapAt[ AdjacencyGraph[ # , opts]& , gottesmangraphsystem[ gnr ] , 2 ]/;spantest[gnr]&&commutetest[gnr]
GottesmanGraphsystem[ gnr_?MatrixQ , qq_ , opts___?OptionQ] := Module[
	{ cl , zz },
	{ cl , zz } = gottesmangraphsystem[ gnr ];
	{ cl , AdjacencyGraph[ qq , zz , opts ] }
]/;spantest[gnr]&&commutetest[gnr]

gottesmangraphsystem[ gnr_?MatrixQ ]:=
Module[
	{ 
	(*matrix*)xx, invxx , zz  ,pp , xzp , x0 , z0  ,
	(*vector*) hh , ss  ,
	(*integer*) d = Length @ gnr ,
	(*operator*)q,
	(*tensor*)lc
	 },

	{ xx , zz } = GottesmanSplit[ gnr ];
	(*suppose { xx , zz} is already checked that this is generators*)
	{ xx , zz , pp } = GottesmanReducesystem[ xx , zz ];

	lc = ConstantArray[ { {1,0} , {0,1}} , d ];

	hh = rankposition @ xx;
	hh = Complement[ Array[ { # }& , d ] , hh ];
	lc = ReplacePart[ lc , hh -> { { 0 , 1 } , { 1 , 0 } } ];
	hh //= Flatten;
	{ x0 , z0 } = { xx , zz }[[ ;; , ;; , hh ]];
	xx[[ ;; , hh ]] = z0;
	zz[[ ;; , hh ]] = x0;
	
	invxx = Inverse[ xx , Modulus -> 2 ];
	zz = Mod[ invxx . zz , 2 ];
	ss = Position[ Diagonal @ zz , 1 ];
	zz = ReplacePart[ zz , {i_,i_} -> 0 ];

	lc = MapAt[ # . {{1,1},{0,1}}&, lc , ss ];
	lc //= BlockDiagonalMatrix;

	{ lc , zz }
	
]

rankposition[xx_]:=Module[{i, pp={} ,p0},
	For[i=1,i<=Length @ xx, i++,  p0 = FirstPosition[ xx[[i]] , 1 , True , 1 ];If[ p0 , Break[] ];AppendTo[pp,p0]; ];
	pp
]

spantest[gnr_]:=SameQ[MatrixRank @ gnr , Length @ gnr] 
commutetest[gnr_]:=Module[ 
	{i=1,j=1,l0=Length @ gnr ,ans},
	
	ans=True;
	For[i=1,i<=l0,i++,
			If[!ans,Break[]];
			For[j=i+1,j<=l0,j++,
					If[OddQ[gnr[[i]] . BlockMap[ Sequence @@ Reverse @ #& , gnr[[j]] , 2]],Print[{i,j}];ans=False;Break[]]
			]
		];
	ans
];


LocalEquivalentQ::usage="LocalEquivalentQ[ gr1 , gr2 ] yields True if graph states associated with gr1 and gr2 are local clifford equivalent, and yields False otherwise."


(*doesn't work for Length[bb]>4. PRA70,034302 Lemma 1 has some problem*)
(*example : 
edges1=UndirectedEdge@@#&/@{S[{1,2},],S[{1,3},],S[{1,4},]};
edges2=UndirectedEdge@@#&/@{S[{1,2},],S[{1,3},],S[{1,4},],S[{2,3},],S[{2,4},],S[{3,4},]};
*)

(*
LocalEquivalentQ[ gr1_ , gr2_ ]:=Module[
{ 
	zz1 , zz2 , bb ,
	qq  , xx ,vars ,const ,
	x , empty = False ,
	ans , eqs , end
},


	qq = VertexList /@ { gr1 , gr2 };
	
	If[ SameQ @@ qq , qq //= First , ans = empty; Goto[end] ];
	
	{zz1,zz2}=AdjacencyMatrix/@{gr1,gr2};
	bb = linearSpace[ zz1 , zz2 , Length @ qq];

	If[ SameQ[ bb , {} ] , ans = empty; Goto[end] ];
	(*test*)
	Print[bb];
	(**)
	If[ Length @ bb <= 4, 
		xx = Array[ x , Length @ bb ];
		eqs = xx . bb;
		{vars , const} = Transpose @ BlockMap[ constraint , eqs , 4 ];
		vars = Union @@ vars;
		const = And @@ const;

		If[!const, ans = empty; Goto[end] ];

		ans = Reduce[ const , vars , Modulus -> 2];
		ans//=Solve;
		
		ans = If[SameQ[ Flatten @ ans , {} ], empty , True ];
		
		,bb = Apply[ Mod[ Plus[#],2]&,Subsets[bb,{2}] ,{1} ];
		ans = Or @@ lconst[ bb , Length @ qq ];
		];
	
	Label[end];
	ans
];

lconst[ mm_?MatrixQ , n_ ]:= lconst[#,n]& /@ mm;
lconst[ ll:{(0|1)..} , n_ ]:= Module[
	{rr},
	rr = Mod[ ll[[;;n]]*ll[[3n+1;;]]+ll[[n+1;;2n]]*ll[[2n+1;;3n]] , 2 ];
	And @@ ( SameQ[#,1]& /@ rr )
	];
*)

LocalEquivalentQ[ gr1_Graph , gr2_Graph ]:=Module[
{ 
	zz1 , zz2 , bb ,
	qq  , xx ,vars ,const ,
	x , empty = False ,
	ans , eqs , end
},


	qq = VertexList /@ { gr1 , gr2 };
	
	If[ SameQ @@ qq , qq //= First , ans = empty; Goto[end] ];
	
	{zz1,zz2}=AdjacencyMatrix/@{gr1,gr2};
	bb = linearSpace[ zz1 , zz2 , Length @ qq];

	If[ SameQ[ bb , {} ] , ans = empty; Goto[end] ];
	
	xx = Array[ x , Length @ bb ];
	eqs = xx . bb;
	{vars , const} = Transpose @ BlockMap[ constraint , eqs , 4 ];
	vars = Union @@ vars;
	const = And @@ const;

	If[!const, ans = empty; Goto[end] ];

	ans = Reduce[ const , vars , Modulus -> 2];
	ans//=Solve;
		
	ans = If[SameQ[ Flatten @ ans , {} ], empty , True ];
		
	Label[end];
	ans
];


(*test*)
localEquivalentQ[ gr1_ , gr2_ ]:=Module[
{ 
	zz1 , zz2 , bb ,
	qq  , xx ,vars ,const ,
	x , empty = False ,
	ans , eqs , end
},


	qq = VertexList /@ { gr1 , gr2 };
	
	If[ SameQ @@ qq , qq //= First , ans = empty; Goto[end] ];
	
	{zz1,zz2}=AdjacencyMatrix/@{gr1,gr2};
	bb = linearSpace[ zz1 , zz2 , Length @ qq];

	If[ SameQ[ bb , {} ] , ans = empty; Goto[end] ];
	
	bb = Apply[ Mod[ Plus[#],2]&,Subsets[bb,{2}] ,{1} ];
	ans = Or @@ lconst[ bb , Length @ qq ];
	
	Label[end];
	ans
];




GottesmanLocalEquivalent::usage="GottesmanLocalEquivalent[ gr1 , gr2 ] attempts to find lists of Gottesman matrices form of local Clifford operators that transform graph state associated with gr1 to graph state associated with gr2."

GottesmanLocalEquivalent[ gr1_Graph , gr2_Graph ]:=Module[
{ 
	zz1 , zz2 , bb ,
	qq  , xx ,vars ,const ,
	x , empty = {} ,
	eqs , ans , comp
},

Catch[
	qq = VertexList /@ { gr1 , gr2 };
	
	If[ SameQ @@ qq , qq //= First , Throw[ empty ] ];
	
	{zz1,zz2}=AdjacencyMatrix/@{gr1,gr2};
	bb = linearSpace[ zz1 , zz2 , Length @ qq];

	If[ SameQ[ bb , {} ] , Throw[ empty ] ];
		
	xx = Array[ x , Length @ bb ];
	eqs = xx . bb;
	{vars , const} = Transpose @ BlockMap[ constraint , eqs , 4 ];
	vars = Union @@ vars;
	const = And @@ const;

	If[!const,Throw[ empty ] ];

	ans = Reduce[ const , vars , Modulus -> 2];
	ans//=Solve;
		
	If[SameQ[ Flatten @ ans , {} ],Throw[ empty ] ];

	comp = Map[ { # -> 0 , # -> 1 }& , Complement[ xx , Keys @ # ]& /@ ans , { 2 } ];
	comp = Tuples /@ comp;
	ans = Flatten[ MapThread[ distribute , { ans , comp } ] , 1];
	ans = Mod[ eqs /. ans , 2];

	BlockDiagonalMatrix @ BlockMap[ ArrayReshape[ # , {2,2}]& , Mod[ # , 2 ] , 4]& /@ ans
	
	]
];

linearSpace[mm1_,mm2_,nq_]:=
	Module[
	{nn},
	nn=Flatten[
			Outer[
				linearSpace[mm1,mm2,{#1,#2},nq]&
				,Range @ nq
				,Range @ nq
			]
		,1];

NullSpace[ nn , Modulus -> 2 ]

]

linearSpace[mm1_,mm2_,{j_,k_},nq_]:=
	Module[
		{
			aa = PadRight[{mm2[[j,k]]},nq,0,j-1],
			bb = PadRight[{KroneckerDelta[j,k]},nq,0,j-1],
			cc = mm1[[j]]*mm2[[k]],
			dd = PadRight[{mm1[[j,k]]},nq,0,k-1]
		},

	Flatten @ Transpose[ { aa , bb , cc , dd } ]

	]

(*constraint to be a local clifford operator*)
constraint[ { a_,b_,c_,d_ } ]:=
	Module[
		{ eq = a*d + b*c , vars },
		{ Variables[eq] , eq == 1 }
	]
	
distribute[ l1_ , l2_ ] := Join[ l1 , # ]& /@ l2;


(* function for Quisso Form*)
QuissoGraphsystem::usage="QuissoGraphsystem[ expr ] gives a list { ops , graph } of local Clifford operator for each qubits by list and graph that satisfies MultiplyFold[ ReleaseHold @ eops ][ expr ] == GraphState[ graph ]. expr may be Ket[...] belongs to Hibert space associated with qubits or generating set of Pauli operators that stabilize state.\n QuissoGraphsystem[ expr , {s1,s2...}] assumes that state belongs to the Hilbert space associated with qubits {s1,s2,...}."
QuissoGraphsystem::nnstb="`1` doesn't represent a stabilizer state."

QuissoGraphsystem[ expr_ , qq_ , opts___?OptionQ ] := Message[QuissoGraphsystem::nnstb , expr ]/; !StabilizerStateQ[expr]

QuissoGraphsystem[ expr_ , opts___?OptionQ ] := QuissoGraphsystem[ expr , Qubits @ expr , opts ]

QuissoGraphsystem[ expr_ , qq_ , opts___?OptionQ ] := quissographsystem[ StabilizerStandardGenerator[ expr , qq ]  , qq , opts ] 

QuissoGraphsystem[ gnr_List  , opts___?OptionQ ]:= quissographsystem[ gnr , Qubits @ gnr , opts ]

QuissoGraphsystem[ gnr_List , qq_ , opts___?OptionQ ]:=Module[
	{mat = GottesmanVector[ # , qq ]& /@ gnr},

	If[!(spantest[mat]&&commutetest[mat]),Message[ QuissoGraphsystem::nnstb , gnr ] ];
	quissographsystem[ gnr , qq , opts ]
];

quissographsystem[ gnr_List , qq:{__?QubitQ} , opts___?OptionQ ] := Module[
{
	mat = GottesmanVector[ # , qq ]& /@ gnr , newmat , pp , lc ,
	sgn ,
	newgnr ,
	nq = Length @ qq ,
	gr
},

	{ lc , gr } = gottesmangraphsystem[ mat ];
	lc = Array[ lc[[2 # - 1 ;; 2 # , 2 # - 1 ;; 2 # ]]& , nq ];
	lc = MapIndexed[ fromLocalGottesmanMatrix[ #1 , qq[[ First @ #2 ]]]& , Normal @ lc ];
	newgnr = ReleaseHold @ SupermapFold[ lc ][ gnr ];
	newmat = GottesmanVector[ # , qq ]& /@ newgnr;
	pp = Last @ GottesmanReducesystem[ newmat ];
	newgnr = Multiply @@ Pick[ newgnr , # , 1 ]& /@ pp;
	sgn = Flatten @ Position[ ReplaceAll[ Map[ Sign , newgnr ] , Sign[ _ ] -> 1 ] , -1  , 1 , Heads->False ];
	lc = Partition[ lc , 1 ];
	PrependTo[ lc[[#]] , HoldForm @ Evaluate @ qq[[#]][3] ]& /@ sgn;
	
	{ Apply[Multiply,lc,{1}] , AdjacencyGraph[ qq , gr , opts ] }

]


LocalEquivalent::usage="LocalEquivalent[ gr1 , gr2 ] attempts to find lists of local Clifford operators for each qubits by list that transform graph state associated with gr1 to graph state associated with gr2."

(*need to find all?*)
LocalEquivalent[ gr1_Graph , gr2_Graph ] := Module[
	{
		qq = Union @@ ( VertexList /@ { gr1 , gr2 } )
		, zzs , gnr1s , mat1s , pp , sgn, lmats
	},
	
	zzs = AdjacencyMatrix @ gr1;
	gnr1s = FromGottesmanVector[#,qq]& /@ GottesmanMerge[IdentityMatrix[ Length @ qq ] , zzs ];
	lmats = GottesmanLocalEquivalent[ gr1 , gr2 ];
	lmats = fromblock[ # , Length @ qq ]& /@ lmats;
	lmats = MapIndexed[ fromLocalGottesmanMatrix[ #1 , qq[[ #2[[2]] ]]]& , lmats , {2} ];
	gnr1s = SupermapFold[ ReleaseHold @ # ][ gnr1s ]& /@ lmats;
	
	mat1s = Map[ GottesmanVector[ # , qq]& , gnr1s , {2} ];
	pp = Last @ GottesmanReducesystem[ #]& /@ mat1s;
	gnr1s = MapThread[ generatortransform[ #1 , #2 ]& , { gnr1s , pp } ];
	
	sgn = Position[ ReplaceAll[ Map[ Sign , gnr1s , {2} ] , Sign[ _ ] -> 1 ] , -1  , {2} , Heads->False ];
	lmats = Partition[#,1]&/@lmats;
	PrependTo[ lmats[[ Sequence @@ # ]] , HoldForm @ Evaluate @ qq[[Last @ #]][3] ]& /@ sgn;
	
	Apply[ Multiply , lmats , {2} ]
]

generatortransform[ gnr_ , pp_ ] := Multiply @@ Pick[ gnr , # , 1 ]& /@ pp
fromblock[mat_,nq_]:=Array[ mat[[2 #1 - 1 ;; 2 #1 , 2 #1 - 1 ;; 2 #1 ]]& , nq ];


MultiplyFold::usage="MultiplyFold[state,{operator1,operator2,...}] gives ...Fold[Multiply,state,{operator1,operator2,...}]."
SupermapFold::usage="SupermapFold[state,{operator1,operator2,...}] gives ...Fold[Supermap,state,{operator1,operator2,...}]."

MultiplyFold[ lops_List ][ sts_ ] := MultiplyFold[ sts , lops ]
SupermapFold[ lops_List ][ gnr_ ] := SupermapFold[ gnr , lops ]

MultiplyFold[ sts_ , lops_List ]:= Fold[ Elaborate[ #2 ** #1 ]& , sts , lops ]
SupermapFold[ gnr_ , lops_List ]:= Fold[ Elaborate[ Supermap[#2][#1]]& , gnr , lops ]

(*Similar time cost*)
(*MultiplyFold[ sts_ , lops_List ]:= Multiply @@ Append[ lops , sts ]*)


(*FromGottesmanMatrix gives calculated form of local operators. fromLocalGottesmanMatrix gives one of decomposed form with phase and hadamard operators*)
fromLocalGottesmanMatrix[{{0,1},{1,0}},q_?QubitQ]:= HoldForm @ Evaluate @ q[6]
fromLocalGottesmanMatrix[{{1,0},{0,1}},q_?QubitQ]:= q[0]
fromLocalGottesmanMatrix[{{1,1},{0,1}},q_?QubitQ]:= HoldForm @ Evaluate @ q[7]
fromLocalGottesmanMatrix[{{0,1},{1,1}},q_?QubitQ]:= Multiply @@ ( HoldForm /@ Evaluate @ q[ {7, 6}] )
fromLocalGottesmanMatrix[{{1,0},{1,1}},q_?QubitQ]:= Multiply @@ ( HoldForm /@ Evaluate @ q[ {6, 7, 6}] )
fromLocalGottesmanMatrix[{{1,1},{1,0}},q_?QubitQ]:= Multiply @@ ( HoldForm /@ Evaluate @ q[ {6, 7}] )

fromLocalGottesmanMatrix[SparseArray @ {{0,1},{1,0}},q_?QubitQ]:= HoldForm @ Evaluate @ q[6]
fromLocalGottesmanMatrix[SparseArray @ {{1,0},{0,1}},q_?QubitQ]:= q[0]
fromLocalGottesmanMatrix[SparseArray @ {{1,1},{0,1}},q_?QubitQ]:= HoldForm @ Evaluate @ q[7]
fromLocalGottesmanMatrix[SparseArray @ {{0,1},{1,1}},q_?QubitQ]:= Multiply @@ ( HoldForm /@ Evaluate @ q[ {7, 6}] )
fromLocalGottesmanMatrix[SparseArray @ {{1,0},{1,1}},q_?QubitQ]:= Multiply @@ ( HoldForm /@ Evaluate @ q[ {6, 7, 6}] )
fromLocalGottesmanMatrix[SparseArray @ {{1,1},{1,0}},q_?QubitQ]:= Multiply @@ ( HoldForm /@ Evaluate @ q[ {6, 7}] )


(*order of lc is same as VertexList[ gr1 ]*)
FindLocalComplementPath::usage="FindLocalComplementPath[ gr , lops ]"
FindLocalComplementPath[gr_Graph,ops_List]:=Module[
{
ss=Qubits @ ops, nv=VertexCount @ gr 
,mat=AdjacencyMatrix[gr],mops
,cc , dd 
,g,f,id
,theta,theta0,ii,ii0,i0,j0
,case2
},

g[i_]:=ReplacePart[ Zero[{nv,nv}] , {i,i}->1];
id=IdentityMatrix[nv];
f[X_,i_]:=Mod[X . (g[i] . X+X[[i,i]]*g[i]+id),2];

mops=MapThread[  GottesmanMatrix, { ops, ss } ];
{cc,dd}=DiagonalMatrix/@{mops[[;;,2,1]],mops[[;;,1,1]]};

theta=Mod[ cc . mat+dd  , 2 ];
ii={};

	i0=Flatten@Position[Diagonal[theta],1];
	theta0=theta-id;
	ii0=Select[i0, SameQ[Union @ theta0[[#]],{0}]&];

While[!SameQ[ theta, id ] , 
	i0=Flatten@Position[Diagonal[theta],1];
	theta0=theta-id;
	i0=SelectFirst[i0, !SameQ[Union @ theta0[[#]],{0}]&,Goto[case2]];
	AppendTo[ii,i0];
	theta=f[theta,i0]
	];

Label[case2];
While[!SameQ[ theta, id ],
	{i0}=FirstPosition[Diagonal[theta],0];
	theta=f[theta,i0];
	ii=AppendTo[ii,i0];
	j0=First @ Complement[ Flatten @ Position[Diagonal[theta],1], ii ,ii0 ];
	theta=f[theta,j0];
	theta=f[theta,i0];
	ii=Join[ii,{j0,i0}];
];

(*{SameQ[theta,id],ss[[ii]]}*)
ss[[ii]]
]


GraphLocalComplement::usage="GraphLocalComplement[ graph , vertex ] gives the graph local complement at vertex of the graph"

GraphLocalComplement[gr_,q_,ops___?OptionQ]:=Module[
{ ee, vtx , pp },

pp =AdjacencyList[ gr , q ];
ee= IncidenceList[ gr , Complement[ VertexList[ gr ] , pp ] ];
Graph[ GraphUnion[ ee , GraphComplement @ Subgraph[ gr , pp ] ]  ,ops ]

]


End[]

EndPackage[]
