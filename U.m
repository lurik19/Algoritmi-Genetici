(* Parametri del problema *)
Npop = 100; (* numero individui *)
pc = 0.7; (* probabilità di avere crossover *)
pm = 0.001; (* probabilità di avere una mutazione *)

(* Parola desiderata *)
goal = {u, n, i, v, e, r, s, a, l, e};


stack = {n, s};
table = {v, u, i, l, e, a, e, r};



test = EQ[DU[MT[CS], NOT[CS]], DU[MS[NN], NOT[NN]]];
test1 = Hold[xEQ[xDU[xMT[xCS], xNOT[xCS]], xDU[xMS[xNN], xNOT[xNN]]]];



(* contapassi *)
contapassi = 0;
contapassiMS = 0;
contapassiMT = 0;

(* Sensori *)

CS := Module[{result},

		contapassi += 1;

		If[ Length[stack] > 0,

			result = stack[[ Length[stack] ]],

			result = "Null"
		];

	result

	];


TB := Module[ {index, result},

			contapassi += 1;
			index = Indice[stack, goal];

			If[ index === 0,

				result = "Null",

				result = goal[[index]];

			];		

			result

		];


NN := Module[ {index, result},

			contapassi += 1;
			index = Indice[stack, goal];

			If[ index === Length[goal],
	
				result = "Null",

				result = goal[[ index + 1 ]];

			];

			result

		];


(* Operazioni *)

(* Comandi di movimento *)

MS[block_] := Module[{result},

				contapassi += 1;

				If[ MemberQ[table, block],
					contapassiMS += 1;
					AppendTo[stack, block];
					table = Delete[table, Position[table, block][[1]]];
					result = block,

					result = "Null";

				];

				result

			];


MT[block_] := Module[{result},

			contapassi += 1;

			If[ MemberQ[stack, block],
				contapassiMT += 1;
				table = Append[ table, stack[[-1]] ];
				stack = Delete[ stack, -1 ];
				result = block,

				result = "Null"

			];

		result

		];


(* Operazioni logiche *)

SetAttributes[DU, HoldAll];

DU[expr1_, expr2_] := Module[{contapassiDU},

				contapassi += 1;
				contapassiDU = 0;

				While[ReleaseHold[expr2] === "Null" && contapassiDU <= 3*Length[goal],
					ReleaseHold[expr1];
					contapassiDU += 1;
				];

				If[ contapassiDU > 3*Length[goal],
					loop = 1; (* se = 1 vuol dire che c'è stato un loop *)
				];

				ReleaseHold[expr2] (* DU restituisce True se non "sfora" 3*N
                                      passi, altrimenti restituisce Null *)

			];


NOT[expr1_] := Module[{result},

			contapassi += 1;

			If[ expr1 === "Null",

				result = True,

				result = "Null"

			];

		result

		];


EQ[expr1_, expr2_] := Module[{result},

				contapassi += 1;
			
				If[ expr1 === expr2,

					result = True,

					result = "Null"

				];

			result

			];



(*********************************** ALGORITMO GENETICO ******************************)

(* Costruzione di un individuo *)

(* Liste di comandi necessarie per la generazione di un individuo *)
comandi = {xEQ[arg, arg], xNOT[arg], xDU[arg, arg], xMT[arg], xMS[arg], xNN, xTB, xCS}; (*per EQ, NOT e 1° argomento di DU*)
comandiTF = {xEQ[arg, arg], xNOT[arg], xDU[arg, arg]}; (* per 2° argomento di DU *)
sensori = {xCS, xTB, xNN, xMT[arg], xMS[arg]}; (* per MS, MT*)


ii = Hold[xEQ[arg, arg]]; (* individuo iniziale *)

Individuo[] := Module[{Pos, pos, com, i, individuo},

		individuo = ii;

		While[MemberQ[individuo, arg, Infinity] && Depth[individuo] <= 5,
			Pos = Position[individuo, arg];

			For[i=1, i <= Length[Pos], i++,
				pos = Pos[[i]];
				pos[[-1]] = 0; (* In questo modo leggo la Head di arg *)

				(* Decidiamo da che lista di comandi estraiamo *)
				If[ MemberQ[{xEQ, xNOT}, Part[individuo, Sequence @@ pos]],
					com = comandi,
					If[ MemberQ[{xMS, xMT}, Part[individuo, Sequence @@ pos]],
						com = sensori,
						(* Non rimane che il DU: 1° o 2° argomento? *)
						If[Pos[[i]][[Length[Pos[[i]]]]] === 1,
							com = comandi,
							com = comandiTF;
						];
					];
				];

				individuo[[Sequence @@ Pos[[i]]]] = com[[Random[Integer, {1, Length[com]}]]];

				];

		];

		If[ MemberQ[individuo, arg, Infinity],
			individuo = Individuo[]
		];

		individuo

	];


(* Costruzione di un individuo a partire da un altro individuo già formato,
   ma con un arg da qualche parte *)

Individuo[ind_] := Module[{Pos, pos, com, i, individuo},

		individuo = ind;

		While[ MemberQ[individuo, arg, Infinity] && Depth[individuo] <= 3 + Depth[ind],
			
			Pos = Position[individuo, arg];

			For[i=1, i <= Length[Pos], i++,
				pos = Pos[[i]];
				pos[[-1]] = 0; (* In questo modo leggo la Head di arg *)

				(* Decidiamo da che lista di comandi estraiamo *)
				If[ MemberQ[{xEQ, xNOT}, Part[individuo, Sequence @@ pos]],
					com = comandi,
					If[ MemberQ[{xMS, xMT}, Part[individuo, Sequence @@ pos]],
						com = sensori,
						(* Non rimane che il DU: 1° o 2° argomento? *)
						If[Pos[[i]][[Length[Pos[[i]]]]] === 1,
							com = comandi,
							com = comandiTF;
						];
					];
				];

				individuo[[Sequence @@ Pos[[i]]]] = com[[Random[Integer, {1, Length[com]}]]];
			];

		];

		If[ MemberQ[individuo, arg, Infinity],
			individuo = Individuo[ind];
		];

		individuo

	];


EseguiIndividuo[individuo_] := Module[{result},

		result = individuo /. {xCS->Hold[CS], xTB->Hold[TB], xNN->Hold[NN], xNOT->NOT,
                               xMT->MT, xMS->MS, xEQ->EQ, xDU->DU};

		result = Map[ReleaseHold, result, {0, Infinity}];

		result
	];



Popolazione[num_] := Module[{pop},

		pop = Table[Individuo, {i, num}];

		pop

	];



Fitness[individuo_] := Module[{fitness, stackIniziale},

		Print[individuo];

		indexIniziale = Indice[stack, goal];
		contapassi = 0;
		contapassiMS = 0;
		contapassiMT = 0;
		loop = 0;

		Print[stack];

		EseguiIndividuo[individuo];


		(* Criteri per la fitness *)
		letterespostate = contapassiMS + contapassiMT;
		index = Indice[stack, goal] - indexIniziale;

		Print[index, " ", letterespostate, " ", contapassi, " ", loop];

		(* AGGIUNGI PENALIZZARE LOOP *)

		fitness = 3 * index + 1 * letterespostate + 0.5 * contapassi - 2 * loop;

		fitness


	];



(* Crossover *)

tutto = {xEQ, xNOT, xDU, xMT, xMS, xCS, xTB, xNN}; (* tutti i possibili comandi *)

Crossover[coppia_] := Module[{ind1, ind2, temp1, crossoverOK, Rand, Pos1, swap, pos1, Headswap, 			      blacklist, temp, Pos2, pos2, swappo, result},

		ind1 = coppia[[1]];
		ind2 = coppia[[2]];

		If[Random[] < pc,

			temp1 = Flatten[Table[Position[ind1,tutto[[i]]], {i,1,Length[tutto]}], 1];
			temp1 = ReplaceAll[temp1, {x___,0} -> {x} ];
		
			crossoverOK = False;

			While[ crossoverOK === False && Length[temp1] > 1,

				Rand = Random[Integer, {2, Length[temp1]}];
				Pos1 = temp1[[ Rand ]];
				temp1 = Delete[temp1, Rand];

				swap = ind1[[ Sequence @@ Pos1 ]];

				pos1 = Pos1;
				pos1[[-1]] = 0;
				Headswap = ind1[[ Sequence @@ pos1 ]];

				Which[  MatchQ[Headswap, xNOT | xEQ], blacklist = {},
					MatchQ[Headswap, xMT | xMS], blacklist = {xDU},
					MatchQ[ Headswap, xDU], 
						If[ Pos1[[-1]] === 1, 
							blacklist = {},
							blacklist = {xMS, xMT};
						];
				];

				If[ MatchQ[ Head[swap], Symbol | xMT | xMS ],
					blacklist = Union[Join[blacklist, {xDU}]],
					(* If MatchQ[ Head[swap], xEQ | xNOT | xDU ] *)
					blacklist = Union[Join[blacklist, {xMS, xMT}]];
				];

				temp = Flatten[Table[Position[ind2, tutto[[i]]], {i,1,Length[tutto]}], 1];
				temp = ReplaceAll[temp, {x___,0} -> {x} ];


				While[ crossoverOK === False && Length[temp] > 1,
				
					Rand = Random[Integer, {2, Length[temp]}];
					Pos2 = temp[[ Rand ]];
					temp = Delete[temp, Rand];


					pos2 = Pos2;
					pos2[[-1]] = 0;


					swappo = ind2[[ Sequence @@ pos2]];

					If[ Not[ MemberQ[blacklist, swappo] ],
						crossoverOK = True,
						If[ MatchQ[ swappo, xDU ] && Pos2[[-1]] === 1,
							crossoverOK = True;
						];
					];
				];
			];

			If[crossoverOK === True,
				ind1[[ Sequence @@ Pos1 ]] = ind2[[ Sequence @@ Pos2 ]];
				ind2[[ Sequence @@ Pos2 ]] = swap;
			];
	
		];

		result = {ind1, ind2}
	];


Mutazione[ind_] := Module[{individuo, temp, Pos},

		individuo = ind;

		If[ Random[] < pm,

			temp = Flatten[Table[Position[individuo, tutto[[i]]],
					     {i,1,Length[tutto]}], 1];
			temp = ReplaceAll[temp, {x___,0} -> {x} ];

			Pos = temp[[ Random[Integer, {2, Length[temp]}] ]];

			individuo[[ Sequence @@ Pos ]] = arg;

			individuo = Individuo[individuo];

		];

			individuo
	];




run := Module[{lenstack, pop},
		
		(* Genero la condizione iniziale in modo casuale estraendo lettere da goal *)
		lenstack = Random[Integer, {0, Length[goal]}];
		stack = RandomSample[goal, lenstack];
		Print["stack iniziale = ", stack];
		table = DeleteCasesOnce[goal, stack];
		Print["table iniziale = ", table];

		Print[" ------------------------------------------- "];

		pop = Popolazione[Npop];
		Map[EseguiIndividuo, pop];

		Print["stack finale = ", stack];
		Print["table finale = ", table];
	];




(* Funzioni aggiuntive *)

(* La funzione Indice mi dice fino a che posizione due parole sono uguali *)
Indice[stack_, goal_] := Module[ {i, result},

				i = 1;

				For[i=1, i <= Length[stack], i++,
					
					If[ stack[[i]] === goal[[i]],
										
						result = i,

						result = i - 1;
						i = Length[stack] + 1;
					];
					
				];
			
				If[ Length[stack] === 0,
					result = 0;
				];
	
				result

			];


DeleteCasesOnce[list_List, cases_List] := Module[{countq},
		countq[_] := 0;
		Scan[(countq[#] = countq[#] + 1;) &, cases];
		#[[ Ordering[Random[] & /@ #] ]] & @ Reap[If[countq[#] === 0, Sow[#], countq[#] = countq[#] - 1] & /@ list][[2, 1]]
	];


(* ATTENZIONE! Da Mathematica 6.0 RandomSample è implementato di default! Commentarlo se si sta usando una versione di Mathematica >= 6.0 *)
RandomSample[lis_List, num_] := Module[{len, selectfunc, ll, n, aa},
	len = Length[lis];
        selectfunc[{ll_, n_}] := {Drop[ll, {aa = Random[Integer, {1, Length[ll]}], aa}], n - 1};
	#[[ Ordering[Random[] & /@ #] ]] & @ Complement[lis, First[Nest[selectfunc[#] &, {lis, num}, num]]]
	];
