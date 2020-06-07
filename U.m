(* Parametri del problema *)
Npop = 100; (* numero individui *)
Ngen = 100; (* numero di generazioni *)
pc = 0.7; (* probabilità di avere crossover *)
pm = 0.1; (* probabilità di avere una mutazione *)

(* Parola desiderata *)
goal = {u, n, i, v, e, r, s, a, l, e};

(* contapassi *)
contapassi = 0;
spostaLettere = 0;

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
		spostaLettere += 1;
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
		spostaLettere += 1;
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

	While[ReleaseHold[expr2] === "Null" && contapassiDU <= 3*Length[goal] && contapassiDUtot <= 15 * Length[goal],
		ReleaseHold[expr1];
		contapassiDU += 1;
		contapassiDUtot += 1;
	];

	ReleaseHold[expr2] (* DU restituisce True se non "sfora" 3*N passi, altrimenti restituisce Null *)

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


(********************** QUI INIZIA LA PARTE DI ALGORITMO GENETICO **********************)

(* Liste di comandi necessarie per la generazione di un individuo *)
comandi = {xEQ[arg, arg], xNOT[arg], xDU[arg, arg], xMT[arg], xMS[arg], xNN, xTB, xCS}; (*per EQ, NOT e 1° argomento di DU*)
comandiTF = {xEQ[arg, arg], xNOT[arg], xDU[arg, arg]}; (* per 2° argomento di DU *)
sensori = {xCS, xTB, xNN}; (* per MS, MT*)

ii = Hold[xEQ[arg, arg]]; (* individuo iniziale *)

(* Costruzione di un individuo *)
Individuo[ind_] := Module[{Pos, pos, com, i, individuo},

	individuo = ind;

	While[MemberQ[individuo, arg, Infinity] && Depth[individuo] <= 3 + Depth[ind],
	
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
			
			(* Peschiamo un comando casuale tra quelli sintatticamente compatibili *)
			individuo[[Sequence @@ Pos[[i]]]] = com[[Random[Integer, {1, Length[com]}]]];
		];
	];

	(* Se alla fine del While precedente sono ancora presenti degli arg allora ri-genero un individuo *)
	If[ MemberQ[individuo, arg, Infinity],
		individuo = Individuo[ind]
	];

	individuo

];


(* Genero una popolazione di num individui *)
Popolazione[num_] := Table[Individuo[ii], {i, num}];


(* Per eseguire effettivamente un individuo dobbiamo rimuovere le x prima di ogni comando *)
EseguiIndividuo[individuo_] := Module[{result},

	contapassiDUtot = 0;

	result = individuo /. {xCS->Hold[CS], xTB->Hold[TB], xNN->Hold[NN], xNOT->NOT,
                           xMT->MT, xMS->MS, xEQ->EQ, xDU->DU};

	result = Map[ReleaseHold, result, {0, Infinity}]
	
];


(* Lista di tutti i possibili comandi *)
tutto = {xEQ, xNOT, xDU, xMT, xMS, xCS, xTB, xNN};

(* Crossover tra una coppia di individui *)	
Crossover[coppia_] := Module[{ind1, ind2, temp1, crossoverOK, Rand, Pos1, swap, pos1, Headswap, blacklistHead, temp, togliHead, Pos2},

	ind1 = coppia[[1]];
	ind2 = coppia[[2]];
	
	If[Random[] < pc,

		(* Lista delle posizioni di tutti i comandi nel primo individuo *)
		temp1 = Flatten[Table[Position[ind1, tutto[[i]]], {i,1,Length[tutto]}], 1] /. {x___,0} -> {x};
		temp1 = DeleteCases[ temp1, {1}]; (* Non può pescare tutto l'individuo (magari toglierò questo comando)*)		
		
		(* Variabile booleana che mi dice se è possibile effettuare il crossover o meno *)
		crossoverOK = False;

		While[ crossoverOK === False && Length[temp1] > 0,

			(* Pesco una delle possibili componenti dell'individuo 1 e la cancello dalla lista temp1,
			   così se ripeto la procedura non mi capiterà di pescarla di nuovo *)
			Rand = Random[Integer, {1, Length[temp1]}];
			Pos1 = temp1[[ Rand ]];
			temp1 = Delete[temp1, Rand];

			swap = ind1[[ Sequence @@ Pos1 ]];

			(* Headswap è il comando che prende in input swap *)
			pos1 = Pos1;
			pos1[[-1]] = 0;
			Headswap = ind1[[ Sequence @@ pos1 ]];

			(* Creo una lista dei comandi non compatibili con Headswap (i comandi che non si possono dare in input a Headswap) *)
			Which[ MatchQ[Headswap, xNOT | xEQ], blacklistHead = {},
				   MatchQ[Headswap, xMT | xMS], blacklistHead = {xDU, xNOT, xEQ, xMS, xMT},
				   MatchQ[ Headswap, xDU], 
						If[ Pos1[[-1]] === 1, 
							blacklistHead = {},
							blacklistHead = {xMS, xMT, xNN, xCS, xTB};
						];
			];
			
			(* Butto via i pezzi di programma non compatibili *)
			temp = Flatten[Table[Position[ind2, tutto[[i]]], {i,1,Length[tutto]}], 1] /. {x___,0} -> {x};
			
			temp = DeleteCases[ temp, {1}]; (* Non può pescare tutto l'individuo (magari toglierò questo comando)*)
			
			togliHead = Flatten[Table[Position[ind2, blacklistHead[[i]]], {i,1,Length[blacklistHead]}], 1] /. {x___,0}->{x};
			temp = DeleteCases[ temp, Alternatives @@ togliHead]; 
			
			(* E ora butto via i pezzi di programma non compatibili con swap (i comandi a cui non posso dare come input swap) *)
			If[ MatchQ[ Head[swap], Symbol],
				temp = DeleteCases[temp, Alternatives @@ Position[ind2, xDU] /. {x___,0}->{x,2}],
				(* If MatchQ[ Head[swap], xEQ | xNOT | xDU ] *)
				temp = DeleteCases[temp, Alternatives @@ Position[ind2, xMS | xMT] /. {x___,0}->{x,1}];
			];

			(* Ora peschiamo tra le posizioni dei comandi rimanenti (se ce ne sono!) una posizione *)
			If[ Length[temp] > 0,
				Pos2 = temp[[ Random[Integer, {1, Length[temp]}] ]];
				crossoverOK = True;
			];
		];

		(* Se abbiamo trovato uno scambio possibile lo effettuiamo! *)
		If[crossoverOK === True,
			ind1[[ Sequence @@ Pos1 ]] = ind2[[ Sequence @@ Pos2 ]];
			ind2[[ Sequence @@ Pos2 ]] = swap;
		];

	];

	{ind1, ind2}
];


Mutazione[ind_] := Module[{individuo, temp, Pos},

	individuo = ind;

	If[ Random[] < pm,

		temp = Flatten[Table[Position[individuo, tutto[[i]]], {i,1,Length[tutto]}], 1];
		temp = ReplaceAll[temp, {x___,0} -> {x} ];
		
		(* Scelgo una posizione casuale nell'individuo e scrivo "arg" al posto di quello che c'era scritto prima.
		   In questo modo abbiamo scelgo una posizione casuale da cui far partire la mutazione! *)
		Pos = temp[[ Random[Integer, {2, Length[temp]}] ]];
		individuo[[ Sequence @@ Pos ]] = arg;

		individuo = Individuo[individuo];

	];

	individuo
	
];


ricombina[popolazione_] := Module[{temp},

	(* Divido la popolazione in coppie *)
	temp = Partition[popolazione,2];
	
	(* Applico il crossover alle coppie di individui *)
	figli = Map[Crossover, temp];
	
	(* "Sciolgo" le coppie *)
	figli = Flatten[figli, 1];
	
	(* Applico la mutazione ad ogni individuo figlio *)
	figli = Map[Mutazione, figli];
	
	figli

];


Fitness[individuo_] := Module[{fitness, stackIniziale, istack},

	index = {};
	
	Headz = Map[Head, Level[individuo, Infinity]];

	(* Premio la varietà di comandi negli individui *)
	fitnesstot = 500 * Length[Union[Headz]] * Length[stacks];

	If[ Depth[individuo] > 10 || Count[Headz, xEQ] > 6 || Count[Headz, xNOT] > 6 || Count[Headz, xDU] > 3,
		(* Se l'individuo è molto complesso (= grande Depth) gli do una fitness bassa,
		   ma non lo butto. Altrimenti avrei individui molto profondi e specifici per
		   risolvere il problema. Questi probabilmente dipenderebbero molto da una
		   specifica stack! *)
		   
		fitnesstot = 100,

		Do[	
			stack = stacks[[istack]];
			table = tables[[istack]];
			
			(* Inizializzo le variabili per calcolare la fitness *)			
			contapassi = 0;
			spostaLettere = 0;
			
			fitness = 0;
			
			(* Eseguo effettivamente l'individuo (ovvero rimuovo le x e gli Hold) *)
			EseguiIndividuo[individuo];

			(* -------------------- Criteri per la fitness -------------------- *)
				
			(* 1) conto quante lettere giuste ho in stack *)
			AppendTo[index, Indice[stack, goal]];
			fitness += 500 * index[[istack]];
			(*
			(* Se troviamo la parola esatta diamo un boost ulteriore *)
			If[ Indice[stack, goal] === Length[goal],
				fitness += 3000 * 10;
			];*)
			
			(* 2) conto quante lettere vengono effettivamente spostate tra stack e table *)
			(* Limito spostaLettere a questo valore perchè fare più spostamenti di così
			   vorrebbe dire continuare a spostare inutilmente blocchi da stack a table *)
			If[ spostaLettere < 2 * Length[goal] + 1,
				fitness += 100 * spostaLettere,
				fitness = 100;
			];
				
			fitnesstot += fitness,
			
			{istack, Length[stacks]}
		];
		
		indextot = Total[index];
		(* In questo modo faccio sì che i programmi che costruiscono più stack contemporaneamente 
		   alla stessa velocità vengano premiate più di quelle che costruiscono magari una sola
		   stack specifica! *)
		diff = Max[index] - Min[index];
		fitnesstot += 2000 * indextot / (diff + 1);
		
		(* Se trovo il programma ideale esco da Fitness[...] e poi in run esco anche dalla run! *)
		If[ indextot === Length[stacks] * Length[goal],
			trovato = 1;
			soluzione = individuo;
			Return[];
		];

	];
	
	
	If[ fitnesstot > fitnessmax,
		fitnessmax = fitnesstot;
		imax = ipop;
	];
	
	ipop++;
	
	fitnesstot

];
	

voti[popolazione_] := Map[Fitness, popolazione];


suddivido[voti_, criterio_] := Module[{temp},

	Which[criterio === FitnessProportionate,
		totalevoti = Plus @@ voti;
		frazioni = voti/totalevoti;
		suddivisione = Table[Sum[frazioni[[j]], {j,1,i}] , {i,1,Npop}], 
		True, (* caso di default *)
		Print["criterio non definito"]; Abort[]

	];

	suddivisione

];


(* Genero una popolazione di figli a partire da una popolazione *)
generazione[popolazione_] := Module[{temp, r},

	votipop = voti[popolazione];
	intervallo = suddivido[votipop, FitnessProportionate];
	genitori = Table[
			r = Random[];
			indice = Count[intervallo, x_ /; x<r] + 1; 
			popolazione[[indice]],
			{i,1,Npop}
		];

	figli = ricombina[genitori];
	
	figli
];


run := Module[{temp, igen, itry},

	StacksAndTables[0];
	soluzione = "Null";
	trovato = 0;
	
	(* Genero una nuova popolazione ogni volta che lancio run *)
	pop = Popolazione[Npop]; 
	
	Do[
		Print["Generazione: ", igen];
		
		ipop = 1;
		fitnessmax = 0;

		pop = generazione[pop];
		Print["Fitness massima = ", N[fitnessmax], "\n"];
		
		If[ trovato === 1,
			Print["Individuo trovato alla generazione ", igen];
			Break[];
		],
		
		{igen, Ngen}
	];
	
	If[trovato === 1,
		numTry = 1000;
		Print["\n"];
		Print["Provo la soluzione su ", numTry, " stack"];
		countbad = 0;
		For[itry=0, itry<numTry, itry++ 
			stackRand;
			EseguiIndividuo[soluzione];
			If[Indice[stack, goal] != Length[goal],
				countbad++;
			];
		];
		Print["Numero di stack su cui la soluzione ha funzionato: ", numTry - countbad],
		
		Print["Non è stato trovato l'individuo ideale! :("];
	
	];

];

runs := Module[{},

	Do[
	
		Print[AbsoluteTiming[run][[1]]],
	
	{irun, 5}];

];

stackRand := Module[{lenstack},

	(* Genero la stack (e table) in modo casuale estraendo lettere da goal *)
	lenstack = Random[Integer, {0, Length[goal]}];
	stack = RandomSample[goal, lenstack];
	table = DeleteCasesOnce[goal, stack];

];

StacksAndTables[rand_] := Module[{is},

	If[ rand === 0,
		
		stacks = {{}, {u,n,l}, {r, n, i, e, u, v, a, l, s}, {u}, {s, v, r, u, a}};
		tables = Table[DeleteCasesOnce[goal, stacks[[is]]], {is, 1, 5}],
	
		stacks = {};
		tables = {};
		For[is = 1, is <= 5, is++,
			stackRand;	
			AppendTo[stacks, stack];
			AppendTo[tables, table];
		];
		
	];
	
	Print["stacks = ", stacks];

];

Try := Module[{},

	stackRand;
	Print["stack iniziale = ", stack];
	
	EseguiIndividuo[soluzione];
	
	Print["stack finale = ", stack];
	
];


(* Funzioni aggiuntive *)

(* La funzione Indice mi dice fino a che posizione due parole sono uguali *)
Indice[stack_, goal_] := Total[Map[(If[MatchQ[#[[1]], #[[2]]], 1, 0])&,
								   Transpose[{stack, Take[goal, Length[stack]]}]]];


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
