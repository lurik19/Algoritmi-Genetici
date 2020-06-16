<< Statistics`;
(******************* VARIABILI GLOBALI *******************)
(* Parametri del problema *)
Npop = 100; (* numero individui *)
Ngen = 150; (* numero di generazioni *)
pc = 0.7; (* probabilità di avere crossover *)
pm = 0.1; (* probabilità di avere una mutazione *)

(* Parola desiderata *)
goal = {u, n, i, v, e, r, s, a, l, e};

MaxDepthInd = 8;
MaxCountDU = 15 * Length[goal];

(* Nome cartella in cui salvare i dati *)
FolderPath = "Data"<>ToString[MaxDepthInd]<>"/"

(********************** OPERAZIONI **********************)

(* Sensori *)

CS := Module[{result},

	If[ Length[stack] > 0,
		result = stack[[-1]],
		result = "Null"
	];

	result

];


TB := Module[ {index, result},

	index = Indice[stack, goal];

	If[ index === 0,
		result = "Null",
		result = goal[[index]];
	];		

	result

];


NN := Module[ {index, result},

	index = Indice[stack, goal];

	If[ index === Length[goal],
		result = "Null",
		result = goal[[ index + 1 ]];
	];

	result

];


(* Comandi di movimento *)

MS[block_] := Module[{result},

	If[ MemberQ[table, block],
		AppendTo[stack, block];
		table = Delete[table, Position[table, block][[1]]];
		result = block,

		result = "Null";
	];

	result

];


MT[block_] := Module[{result},

	If[ MemberQ[stack, block],
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

	contapassiDU = 0; 

	While[ReleaseHold[expr2] === "Null" && contapassiDU <= 3*Length[goal] && contapassiDUtot <= MaxCountDU,
		ReleaseHold[expr1];
		contapassiDU += 1;
		contapassiDUtot += 1;
	];

	ReleaseHold[expr2] (* DU restituisce True se non "sfora" 3*N passi, altrimenti restituisce Null *)

];


NOT[expr1_] := Module[{result},

	If[ expr1 === "Null",
		result = True,
		result = "Null"
	];

	result

];


EQ[expr1_, expr2_] := Module[{result},

	If[ expr1 === expr2,
		result = True,
		result = "Null"
	];

	result

];


(********************** QUI INIZIA LA PARTE DI ALGORITMO GENETICO **********************)

(* Liste di comandi necessarie per la generazione di un individuo *)
comandi = {xEQ[arg, arg], xNOT[arg], xDU[arg, arg], xMT[arg], xMS[arg], xNN, xTB, xCS}; (* per EQ, NOT e 1° argomento di DU *)
comandiTF = {xEQ[arg, arg], xNOT[arg], xDU[arg, arg]}; (* per 2° argomento di DU *)
sensori = {xCS, xTB, xNN}; (* per MS, MT *)

ii = Hold[xEQ[arg, arg]]; (* individuo iniziale *)

(* Costruzione di un individuo *)
Individuo[ind_] := Module[{Pos, pos, com, i, individuo},

	individuo = ind;

	While[MemberQ[individuo, arg, Infinity] && Depth[individuo] <= 3 + Depth[ind],
		Pos = Position[individuo, arg];
		Do[
			pos = Pos[[i]];
			pos[[-1]] = 0; (* In questo modo leggo la Head di arg *)

			(* Decidiamo da che lista di comandi estrarre in base alla Head di arg*)
			Which[ MemberQ[{xEQ, xNOT}, Part[individuo, Sequence @@ pos]], com = comandi,
				   MemberQ[{xMS, xMT}, Part[individuo, Sequence @@ pos]],  com = sensori,
				   True,
						(* Non rimane che il DU: 1° o 2° argomento? *)
						If[Pos[[i]][[-1]] === 1,
							com = comandi,
							com = comandiTF;
						];
			];
			
			(* Peschiamo un comando casuale tra quelli sintatticamente compatibili *)
			individuo[[Sequence @@ Pos[[i]]]] = com[[Random[Integer, {1, Length[com]}]]],
			
			{i, Length[Pos]}		
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
	
	result = individuo /. {xCS->Hold[CS], xTB->Hold[TB], xNN->Hold[NN], xNOT->NOT, xMT->MT, xMS->MS, xEQ->EQ, xDU->DU};
	result = Map[ReleaseHold, result, {0, Infinity}]
	
];


(********** RICOMBINAZIONE GENETICA **********)
(* Lista di tutti i possibili comandi *)
tutto = {xEQ, xNOT, xDU, xMT, xMS, xCS, xTB, xNN};

(* Crossover tra una coppia di individui *)
Crossover[coppia_] := Module[{ind1, ind2, temp1, crossoverOK, Rand, Pos1, swap, pos1, Headswap, blacklistHead, temp, togliHead, Pos2},

	ind1 = coppia[[1]];
	ind2 = coppia[[2]];
	
	If[Random[] < pc,

		(* Lista delle posizioni di tutti i comandi nel primo individuo *)
		temp1 = Flatten[Table[Position[ind1, tutto[[i]]], {i,1,Length[tutto]}], 1] /. {x___,0} -> {x};
		temp1 = DeleteCases[ temp1, {1}]; (* Non può pescare tutto l'individuo (magari toglierò questo comando) *)
		
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
				   MatchQ[Headswap, xDU], 
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
			
			(* E ora butto via i pezzi di programma non compatibili con swap (i comandi a cui non posso dare swap come input) *)
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

		temp = Flatten[Table[Position[individuo, tutto[[i]]], {i, 1, Length[tutto]}], 1];
		temp = ReplaceAll[temp, {x___,0} -> {x} ];
		
		(* Scelgo una posizione casuale nell'individuo e scrivo "arg" al posto di quello che c'era scritto prima.
		   In questo modo abbiamo scelgo una posizione casuale da cui far partire la mutazione! *)
		Pos = temp[[ Random[Integer, {2, Length[temp]}] ]];
		individuo[[ Sequence @@ Pos ]] = arg;

		(* La mutazione avviene in questo comando *)
		individuo = Individuo[individuo];

	];

	individuo
	
];


ricombina[popolazione_] := Module[{temp},

	(* Divido la popolazione in coppie *)
	temp = Partition[popolazione, 2];
	
	(* Applico il crossover alle coppie di individui *)
	figli = Map[Crossover, temp];
	
	(* "Sciolgo" le coppie *)
	figli = Flatten[figli, 1];
	
	(* Applico la mutazione ad ogni individuo figlio *)
	figli = Map[Mutazione, figli];
	
	figli

];


(********** FITNESS **********)
Fitness[individuo_] := Module[{Headz, fitnesstot, index, indextot, diff, tstart, tinizio},

	tstart = AbsoluteTime[];

	Headz = Map[Head, Level[individuo, Infinity]];
	(* Premio la varietà del patrimonio genetico degli individui *)
	fitnesstot = 500 * Length[Union[Headz]] * Length[stacks];

	If[ Depth[individuo] <= MaxDepthInd && trovato === 0,
		(* Se l'individuo è molto complesso (= grande Depth) gli do una fitness bassa,
		   ma non lo butto. Altrimenti avrei individui molto profondi e specifici per
		   risolvere il problema. Questi probabilmente dipenderebbero molto da una
		   specifica stack! *)
		(* Anche se abbiamo già trovato l'individuo (trovato=1) saltiamo tutta la valutazione dell'individuo e della sua fitness! *)

		index = Map[
			(stack = #[[1]]; table = #[[2]];
			tinizio = AbsoluteTime[];
			EseguiIndividuo[individuo];
			timez[[4]] += AbsoluteTime[] - tinizio;
			Indice[stack, goal])&,
			Transpose[{stacks, tables}]];
		
		indextot = Plus @@ index;
		
		(* Conto quante lettere giuste ho nelle varie stack *)
		fitnesstot += 500 * indextot;
		
		(* In questo modo faccio sì che i programmi che costruiscono più stack contemporaneamente 
		   alla stessa velocità vengano premiate più di quelle che costruiscono completamente una 
		   sola stack specifica! *)
		diff = Max[index] - Min[index];
		fitnesstot += 2000 * indextot / (diff + 1);
		
		(* Se trovo il programma ideale lo salvo e poi esco dalla run! *)
		If[ indextot === Length[stacks] * Length[goal],
			trovato = 1;
			fitnesstrovato = fitnesstot;
			soluzione = individuo;
		];

	];
	
	If[ fitnesstot > fitnessmax,
		fitnessmax = fitnesstot;
	];
	
	timez[[2]] += AbsoluteTime[] - tstart;
	
	fitnesstot

];


voti[popolazione_] := Map[Fitness, popolazione];


suddivido[voti_, criterio_] := Module[{temp},

	Which[ criterio === FitnessProportionate,
		totalevoti = Plus @@ voti;
		frazioni = voti/totalevoti;
		suddivisione = Table[Sum[frazioni[[j]], {j,1,i}] , {i,1,Npop}], 
		True, (* caso di default *)
		Print["criterio non definito"]; Abort[]

	];

	suddivisione

];


(* Genero una popolazione di figli a partire da una popolazione *)
generazione[popolazione_] := Module[{r, tstart},

	votipop = voti[popolazione];
	
	tstart = AbsoluteTime[];
	
	intervallo = suddivido[votipop, FitnessProportionate];
	genitori = Table[
			r = Random[];
			indice = Count[intervallo, x_ /; x<r] + 1; 
			popolazione[[indice]],
			{i,1,Npop}
		];

	figli = ricombina[genitori];
	
	timez[[3]] += AbsoluteTime[] - tstart;
	
	figli
];


(********** RUN **********)
run := Module[{itry, tstart},

	trovato = 0;
	fitnessMaxAndMean = {};
	
	(* Genero una nuova popolazione ogni volta che lancio run *)
	pop = Popolazione[Npop]; 
	
	Do[		
		fitnessmax = 0;
		pop = generazione[pop];
		AppendTo[fitnessMaxAndMean, {N[Mean[votipop]], N[fitnessmax]}];
		
		If[ trovato === 1,
			gentrovato = igen;
			Print["Individuo trovato alla generazione ", igen, " con fitness = ", fitnesstrovato];
			
		tstart = AbsoluteTime[];
		numtry = 100;
		Print["\n"];
		Print["Provo la soluzione su ", numtry, " stack"];
		countbad = 0;
		Do[
			Try;
			If[Indice[stack, goal] != Length[goal],
				countbad++;
			],
			
			{itry, numtry}
		];
		Print["Numero di stack su cui la soluzione ha funzionato: ", numtry - countbad];
		timez[[5]] += AbsoluteTime[] - tstart;
		
		Break[];
		],
		
		{igen, Ngen}
	];
	
	If[trovato === 0,
		Print["Non è stato trovato l'individuo ideale! :("];
		NonTrovati += 1;
	];

];


runs[numruns_] := Module[{countgood, gengood, tstart},

	(* Creo la cartella in cui salvare i dati (se non esiste già) *)
	Switch[ FileType[FolderPath],
  		None, CreateDirectory[FolderPath],
  		Directory, Null;
  		];
	WriteSummary[];

	stacks = {{}, {u}, {u, e}, {u, n, l, a}, {s, v, r, u, a}, {r, e, i, n, u, v, a, l, s, e}, {u, e, i, s, e, r, a, l, n, v}};
	tables = Table[DeleteCasesOnce[goal, stacks[[is]]], {is, Length[stacks]}];
	
	Print["\n"];
	Print["stacks = ", stacks, "\n"];
	countgood = {};
	gengood = {};
	times = {};
	soluzioni = {};
	
	NonTrovati = 0;
	
	timez = Table[0, {7}];
	
	Do[
		Print["--------------------------- Run ", irun ," ---------------------------"];
		tstart = AbsoluteTime[];
		run;
		time = AbsoluteTime[] - tstart;
		timez[[1]] += time;
				
		Print[time, " secondi"];
		Print["\n"];

        filename = FolderPath<>"Fitness"<>ToString[irun]<>".dat";
		Export[filename, fitnessMaxAndMean , "Table"];

		If[trovato === 1,
			PutAppend[gentrovato, FolderPath<>"generations.dat"];
			PutAppend[soluzione, FolderPath<>"solutions.dat"];
			PutAppend[numtry - countbad, FolderPath<>"counts.dat"];
			
			AppendTo[gengood, gentrovato];
			AppendTo[soluzioni, soluzione];
			AppendTo[countgood, numtry - countbad];
		];
		
		PutAppend[N[time], FolderPath<>"times.dat"];
		AppendTo[times, time],
	
		{irun, numruns}
	];
	
	If[ numruns > 1,
	Print["Generazioni = ", N[Mean[gengood]], "+-", N[StandardDeviation[gengood]]];
	Print["Stack ricostruite = ", N[Mean[countgood]], "+-", N[StandardDeviation[countgood]]],
	
	Print["Generazioni = ", N[Mean[gengood]]];
	Print["Stack ricostruite = ", N[Mean[countgood]]];
	
	];
	
	Print["Numero di run in cui non si è trovata la soluzione = ", NonTrovati];
	Print["Tempo medio per run = ", N[Mean[times]]];
	
	Print[" \n--------------- Profiling ---------------"];
	timez /= numruns;
	Print["Tempo medio per run = ", timez[[1]]];
	Print["Tempo medio Fitness per run = ", timez[[2]]];
	Print["Tempo medio per il resto della riproduzione per run = ", timez[[3]]];
	Print["Tempo medio esecuzione individui per run = ", timez[[4]]];
	Print["Tempo medio test correttezza individui per run = ", timez[[5]]];

	filename = FolderPath<>"Profiling.dat";
	Export[filename, {{"Tempo medio per run = ", N[timez[[1]]]}, {"Tempo medio Fitness per run = ", N[timez[[2]]]}, {"Tempo medio per il resto della riproduzione per run = ", N[timez[[3]]]}, {"Tempo medio esecuzione individui per run = ", N[timez[[4]]]}, {"Tempo medio test correttezza individui per run = ", N[timez[[5]]]}}, "Table"];

];


(********************** Funzioni aggiuntive **********************)

(* Scrivo su file un sommario dei parametri per le run lanciate *)
WriteSummary[] := Module[{filename},
	filename = FolderPath<>"0_Summary.dat";
	Export[filename, {{"Parola desiderata:", goal}, {"Npop =", Npop}, {"Ngen =", Ngen}, {"pc =", pc}, {"pm =", pm}, {"MaxDepthInd =", MaxDepthInd}, {"MaxCountDU =", MaxCountDU}} , "Table"];
];


(* Genero la stack (e table) in modo casuale estraendo le lettere da goal *)
stackRand := Module[{lenstack},
	lenstack = Random[Integer, {0, Length[goal]}];
	stack = RandomSample[goal, lenstack];
	table = DeleteCasesOnce[goal, stack];

];


(* Provo la soluzione su una stack casuale *)
Try := Module[{},
	stackRand;
	EseguiIndividuo[soluzione];
];


(* La funzione Indice mi dice fino a che posizione due parole sono uguali *)
Indice[stack_, goal_] := Module[{appo},
	appo = 1;
	Plus @@ Map[(If[MatchQ[#[[1]], #[[2]]], appo*=1, appo*=0;] appo)&,
			  Transpose[{stack, Take[goal, Length[stack]]}]]
];


(* Elimino (da list) gli elementi una sola volta se appaiono una volta in cases, due volte se appaiono due, ecc. Poi con Ordering li mischio casualmente *)
DeleteCasesOnce[list_List, cases_List] := #[[ Ordering[Random[] & /@ #] ]] & @ Fold[DeleteCases[##, 1, 1]&, list, cases];


(* ATTENZIONE! Da Mathematica 6.0 RandomSample è implementato di default! Se si sta usando una versione di Mathematica >= 6.0 nel momento dell'esecuzione verrà restituito un errore, perché RandomSample ha l'attributo Protected. Questo però non causa problemi e Mathematica semplicemente utilizzerà RandomSample default. (Per evitare l'errore commentare questa definizione) *)
RandomSample[lis_List, num_] := Module[{len, selectfunc, ll, n, aa},
	len = Length[lis];
    selectfunc[{ll_, n_}] := {Drop[ll, {aa = Random[Integer, {1, Length[ll]}], aa}], n - 1};
	#[[ Ordering[Random[] & /@ #] ]] & @ Complement[lis, First[Nest[selectfunc[#] &, {lis, num}, num]]]
];
