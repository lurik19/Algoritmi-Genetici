(* ********* ES 1 ********* *)

(* parametri del mio problema *)
Npop = 100;
Nbits = 20;
pc = 0.7;
pm = 0.001;



PopIniziale := Table[Random[Integer,{0,1}], {i,1,Npop}, {j,1,Nbits}]; (* uguale se avessi messo {Npop} e {Nbits} senza i e j*)


fitness[individuo_] := Apply[Plus, individuo]; (* uguale se avessi scritto Plus @@ individuo *)

voti[popolazione_] := Map[fitness, popolazione]; (* applica la funzione fitness ad ogni individuo della popolazione (che è una lista di individui)*)


suddivido[voti_, criterio_] := Module[{temp},
					Which[criterio === FitnessProportionate,
						totalevoti = Plus @@ voti; (* se voti è una lista ottengo una somma delle sue componenti *)
						frazione = voti/totalevoti; (* quanto sono larghi i vari sottintervalli *) (* divido una lista per un numero. Divido elemento per elemento la lista per il numero *)
						suddivisione = Table[Sum[frazioni[[j]], {j,1,i}] , {i,1,Npop}], 
						
						True, (* caso di default *)
						Print["criterio non definito"]; Abort[]
				
					];

				suddivisione

				];


generazione[popolazione_] := Module[{temp}, (*in input una popolaz e restituisce in output un'altra popolaz*)
				
				votipop = voti[popolazione];
				intervallo = suddivido[votipop, FitnessProportionate];
				genitori = Table[
						r = Random[];
						indice = Count[intervallo, x_ /; x<r] + 1; (* conto all'interno della lista intervallo quanti sono i suoi elementi che soddisfano un certo criterio (il secondo elemento di count). Voglio trovare tutte le espressioni (x_ è un elemento di intervallo) e le conto SE ( if si scrive anche /; ) x<r. In pratica conto gli elementi di intervallo che sono minori di r (REC 17/04/20) *)
						popolazione[[indice]], (* questo è l'elemento generico di genitori (gli altri sono col ; e non vengono restituiti). Precede la virgola che separa il corpo del table dall'iteratore*) (* questo comando mi dice che prendo l'indice-esimo elemento della lista popolazione *)
						{i,1,Npop} (* iteratore del table *)
					];
				figli = ricombina[genitori];
				
				figli
			];

ricombina[popolazione_] := Module[{temp},
				temp = Table[crossover[popolazione[[2*i-1]], popolazione[[2*i]]], 				                  {i,Npop/2}];

				(* oppure, per evitare di scrivere in componenti, temp=Partition[popolazione,2]; che divide la popolazione tante liste da 2 *)
				temp = Partition[popolazione,2];
				figli = Map[crossover, temp];
				figli = Flatten[figli, 1]; (* appiattiamo la lista di 1 livello: passiamo da una lista di 50 liste ciascuna con 2 individui a una lista di 100 individui. Es Flatten[figli,2] otteniamo la lista di tutti i bit di tutti gli individui (perchè passiamo a un livello ancora più basso)*)
				figli = Map[mutazione, figli]; (* scambio alcuni bit negli individui (mando alcuni 0 in 1 e viceversa con una certa probabilità). Qui NO & dopo mutazione, perchè mutazione deve diventare Head degli elementi di figli! *)
				
				figli

			];

crossover[coppia_] := Module[{temp},
		
			i1 = coppia[[1]];
			i2 = coppia[[2]];
			
			If[Random[] < pc,
				taglio = Random[Integer,{1,Nbits-1}];
				t11 = Take[i1, taglio]; (* da 20 bits di i1 prendine taglio (=5 ad es) *)
				t12 = Take[i1. {taglio + 1, Nbits}]; (* t12 = Take[i1,-(Nbits-taglio)] *)
				t21 = Take[i2, taglio];
				t22 = Take[i2, {taglio + 1, Nbits}]; (* da 20 bits di i2 prendi quelli da taglio+1 a Nbits (alla fine) *)
				
				risultato = {Join[t11, t22], Join[t21, t12]}, (* Join UNISCE due liste, preservando gli elementi ripetuti. APPICCICHIAMO DUE LISTE *)

				(* questo è l'else *)
				risultato = {i1, i2}
				];
			
			risultato
			];

mutazione[individuo_] := Map[(If[Random[]<pm, Mod[# + 1, 2] , # (*vuol dire che restituisco #, quindi NON MODIFICO*) ])&, individuo]; (* mappo la funzione tra ( )& e la applico elemento per elemento a individuo ASCOLTA REC 23/04/20 (un po' prima di un'ora) *)


run := Module[{temp},
	
	pop = PopIniziale; (* pop è una nuova popolazione ogni volta che lancio run *)
	voti0 = voti[pop];
	count = 1;
	
	While[FreeQ[voti0, Nbits], (* FreeQ restituisce True se l'elem Nbits è assente dalla lista voti0 *)
		pop = generazione[pop];
		voti0 = voti[pop];
		count = count + 1
		
		];

	Return[count]

	];



<<Statistics`; (* Nelle versioni più vecchi di Mathematica servve per caricare il package Statistics.` vuol dire  che cerca il package nelle directory di Mathematica *)
test = Table[run,{1000}];
std = StandardDeviation[test];
ave = Mean[test];

Print["ho trovato la soluzione alla generazione ", ave, "+-", std]
(* eseguiamo mille generazioni! Ci possiamo rendere conto in media QUANDO coverge l'algoritmo con i parametri pc e pm (Infatti non è detto che l'algoritmo ci dia un risultato esatto *)

(* altri commenti su Count (oppure altri comandi come Cases, Position): conta quante volte un certo pattern è presente nella nostra espressione che gli diamo (Cases conta tutte le ricorrenze di una certa variabile presenti nella nostra espressione). Count[intervallo,x_] mi restituisce il numero di argomenti che ci sono in intervallo (ovvero la grandezza della lista). Invece il comando che noi abbiamo dato conta solo se il generico x_ soddisfa una condizione: x<r. Per sapere in che posizione sono conto tutti gli intervallini alla mia sinistra (gli intervalli che hanno estremi minori di r). *)
