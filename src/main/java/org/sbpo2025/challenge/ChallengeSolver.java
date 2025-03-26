package org.sbpo2025.challenge;

import org.apache.commons.lang3.time.StopWatch;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.concurrent.TimeUnit;
import ilog.concert.*;
import ilog.cplex.*;

public class ChallengeSolver {
	private IloCplex cplex;
	private final long MAX_RUNTIME = 600000; // 10 minutos
	protected List<Map<Integer, Integer>> orders;
	protected List<Map<Integer, Integer>> aisles;
	protected int nOrders;
	protected int nAisles;
	protected int nItems;
	protected int waveSizeLB;
	protected int waveSizeUB;
	private IloIntVar[] X_NA;
	private IloIntVar[] X_AI;
	private IloIntVar[] X_OR;
	private IloIntVar[] X_IT;

	public ChallengeSolver(List<Map<Integer, Integer>> orders, List<Map<Integer, Integer>> aisles, int nItems,
			int waveSizeLB, int waveSizeUB) throws IloException {

		// Verifica se as listas não são nulas antes de chamar size()
		this.nOrders = (orders == null) ? 0 : orders.size(); // Recupera número de pedidos
		this.nAisles = (aisles == null) ? 0 : aisles.size(); // Recupera número de corredores

		// Inicializa os demais atributos
		this.orders = (orders == null) ? new ArrayList<>() : orders; // Inicializa como lista vazia se for nulo
		this.aisles = (aisles == null) ? new ArrayList<>() : aisles; // Inicializa como lista vazia se for nulo
		this.nItems = nItems;
		this.waveSizeLB = waveSizeLB;
		this.waveSizeUB = waveSizeUB;
		int BIG_M = 1000000;

		try {
			// Instancia o solver CPLEX
			this.cplex = new IloCplex();

			// ================================
			// Definição das variáveis de decisão
			// ================================

			// Tipo 1: X_NA[na] (na = 0..nAisles-1) (nAisles= total aisles)
			// As variáveis do tipo 1 são boolenas que representam a ativação ou não
			// de um número de corredores. Uma restrição garante que apenas uma terá
			// valor 1, as demais serão zero.
			// Neste modelo tal variável pode não representar o número exato de corredores
			// ativos, como forma de reduzir a complexidade do MIP.
			X_NA = cplex.boolVarArray(nAisles);

			// Tipo 2: X_AI[ai] (ai = 0...nAisles-1) – Booleanas que indicam a ativação ou não
			// de um corredor. Mais de um corredor podem estar ativos
			X_AI = cplex.boolVarArray(nAisles);

			// Tipo 3: X_OR[or] (or = 0...nOrders-1) – Booleana que indica se o pedido 'or'
			// está ativo.
			X_OR = cplex.boolVarArray(nOrders);

			// Tipo 4: X_IT[it] (it= 0...nItems-1)  As variáveis do tipo 4 são boolenas
			//que representam o total de items na wave. Uma restrição
			// garante que apenas uma terá valor 1, as demais serão zero.
			// Neste modelo tal variável pode não representar o número exato de items
			// ativos, como forma de reduzir a complexidade do MIP.
			X_IT = cplex.boolVarArray(nItems);

			// Tipo 5: X_AS[ai,or,it] (assignment) – As variáveis do tipo 5 indicam uma
			// designação de uma quantidade de itens(it), captada de um corredor(ai)
			// para um determinado pedido(or).
			// Usamos um mapa para armazenar as variáveis do tipo 5, indexadas pela tupla
			// (ai, or, it).
			java.util.Map<String, IloIntVar> X_AS = new java.util.HashMap<>();

			// (0) CRIAÇÃO DAS VARIÁVEIS DE ASSOCIAÇÃO E VALORES TOTAIS
			// (1) CRIAÇÃO DE RESTRIÇÕES DE ATENDIMENTO
			// (1.1) Restrição de bloqueio de corredores inativos.
			// (1.2) Limitação de tamanho da wave
			IloLinearIntExpr Expr = cplex.linearIntExpr();
		    // Cria a expressão que irá representar a soma das variáveis
		    // de designação X_AS, que representa o total de items.
			IloLinearIntExpr totalItemsExpr = cplex.linearIntExpr();
			for (int ai = 0; ai < nAisles; ai++) {
				Expr.clear();
				// Cria a expressão que irá representar a soma das variáveis
				// de designação associadas ao corredor "ai". Note que
				// temos "ai" restrições deste tipo.
				Expr = cplex.linearIntExpr();
				// Adiciona o termo -BIG_M * X_AI[ai] à expressão
				// o que libera apenas as variáveis de designação
				// se X_AI[ai] estiver ativa.
				Expr.addTerm(-BIG_M, X_AI[ai]);
				for (int it = 0; it < nItems; it++) {
					if (aisles.get(ai).getOrDefault(it, 0) > 0) { // Cria a variável apenas se existir o item no
																	// corredor.
						for (int or = 0; or < nOrders; or++) {
							if (orders.get(or).getOrDefault(it, 0) > 0) { // Cria a variável se existir o item no pedido
								// As variáveis representam a quantidade de itens "it" retirados de um
								// corredor "ai" para um pedido "or". Temos ai*or*it variáveis geradas.
								String key = ai + "," + or + "," + it;
								IloIntVar xVar = cplex.intVar(0, BIG_M);
								// Guarda no mapa usando a chave "ai,or,it"
								X_AS.put(key, xVar);
								Expr.addTerm(1, xVar);
								// Aqui a soma de itens totais é criada, note que
								totalItemsExpr.addTerm(1, xVar);
							}
						}
					}
				}
				cplex.addLe(Expr, 0);
			}

			// (1.2) Limitação de tamanho da wave (continuação)
			// LB <= Sum_{ai,or,it} X_AS[ai,or,it] <= UB.
			cplex.addLe(totalItemsExpr, waveSizeUB); // Limite superior (UB)
			cplex.addGe(totalItemsExpr, waveSizeLB); // Limite inferior (LB)


			// (1.3) Restrições de capacidade dos corredores:
			// Para cada corredor 'ai' e item 'it':
			// Sum_{ai,it} X_AI[ai,or,it] - aisles[ai,it]*X_AI[ai]<=0.
			for (int ai = 0; ai < nAisles; ai++) {
				for (int it = 0; it < nItems; it++) {
					if (aisles.get(ai).getOrDefault(it, 0) > 0) {
						Expr.clear();
						Expr = cplex.linearIntExpr();
						Expr.addTerm(-aisles.get(ai).get(it), X_AI[ai]);
						for (int or = 0; or < nOrders; or++) {
							if (orders.get(or).getOrDefault(it, 0) > 0) {
								String key = ai + "," + or + "," + it;
								Expr.addTerm(1, X_AS.get(key));
							}
						}
						cplex.addLe(Expr, 0);
					}
				}

			}

			// (1.3) Restrições de atendimento integral dos pedidos ativos
			// e bloquio de pedidos inativos. Para cada pedido 'or' e item 'it':
			// Sum_{(ai)} X_AS[ai,or,it] - order[or,it]*X_OR[or]=0.
			// No pior caso temos or*it restrições aqui.
			for (int or = 0; or < nOrders; or++) {
				for (int it = 0; it < nItems; it++) {
					if (orders.get(or).getOrDefault(it, 0) > 0) {
						Expr.clear();
						Expr = cplex.linearIntExpr();
						Expr.addTerm(-orders.get(or).get(it), X_OR[or]);
						for (int ai = 0; ai < nAisles; ai++) {
							if (aisles.get(ai).getOrDefault(it, 0) > 0) {
								String key = ai + "," + or + "," + it;
								Expr.addTerm(1, X_AS.get(key));
							}
						}
						cplex.addEq(Expr, 0);
					}
				}
			}


			// (2) RESTRIÇÕES PARA OBTENÇÃO DE ITENS E NÙMERO DE CORREDORES
			// DE FORMA APROXIMADA.

			// (2.1) Restrição: escolher exatamente um X_NA ativo (apenas um número
			// aproximado de corredores ativos possível).
			// Sum_{n=1..nAisles} x_{1,n} = 1.
			Expr.clear();
			for (int na = 0; na < nAisles; na++) {
				Expr.addTerm(1, X_NA[na]);
			}
			cplex.addEq(Expr, 1);

			// Define tamanho dos passo de aproximação
			// Inicializa função objetivo
			IloLinearNumExpr objectiveExpr = cplex.linearNumExpr();
			int stepna = Math.max(1, (int) Math.round((double) nAisles / 100));
			int stepit = Math.max(1, (int) Math.round((double) nItems / 50));

			// (2.2) Restrição: Obtenção do número aproximado de corredores ativos
			// Sum_[ai] X_AI[ai] - Sum_{na} ((na+1) * X_NA[na])-P*FOLGA_NA = 0. (na+1 pois a baase é 0)
			Expr.clear();
			Expr = cplex.linearIntExpr();
			for (int na = 0; na < nAisles; na += stepna) {
				Expr.addTerm(-(na + 1), X_NA[na]);
				Expr.addTerm(1, X_AI[na]);
			}
			// Define folga
			IloIntVar folga = cplex.intVar(0, stepna - 1);
			Expr.addTerm(1, folga);
			// Coloca um peso de minimização da folga
			objectiveExpr.addTerm(-150, folga);
			cplex.addEq(Expr, 0);

			// (2.3) Restrição: Seleciona apenas uma variável de aproximação
			// do número de itens
			Expr.clear();
			for (int it = 0; it < nItems; it += stepit) {
				Expr.addTerm(1, X_IT[it]);
			}
			cplex.addEq(Expr, 1);

			// (2.4) Restrição: Obtenção do número aproximado de itens na wave.
			// Sum_[ai,or,it] X_AS[ai,or,it] - Sum_{it} ((it+1) * X_IT[it])-P*FOLGA_IT = 0.
			Expr.clear();
			Expr = totalItemsExpr;
			for (int it = 0; it < nItems; it += stepit) {
				Expr.addTerm(-(it + 1), X_IT[it]);
			}
			folga = cplex.intVar(0, stepit - 1);
			Expr.addTerm(1, folga);
			// Coloca um peso de minimização da folga
			objectiveExpr.addTerm(-50, folga);
			cplex.addEq(Expr, 0);

			// (3) RESTRIÇÃO QUE DEFINE A VARIÁVEL AUXILIAR PARA
			// A OTIMIZAÇÃO PRINCIPAL
			double vNa;
			double vIt;
			for (int na = 0; na < nAisles; na += stepna) {
				for (int it = 0; it < nItems; it += stepit) {
					// Cria variável que indica a
					// ativação de um grugo de NA e IT
					IloIntVar xG = cplex.boolVar();

					// Atualiza a função objetivo: coeficiente que aproxima nItems na wave / NAA
					vNa = na + 1 + (stepna - 1) / 2;
					vIt = it + 1 + (stepit - 1) / 2;
					//coloca peso de 1000 para evitar influência das folgas
					objectiveExpr.addTerm(1000*vIt / vNa, xG);

					// adiciona restrições
					Expr.clear();
					Expr.addTerm(2, xG);
					Expr.addTerm(-1, X_IT[it]);
					Expr.addTerm(-1, X_NA[na]);
					cplex.addLe(Expr, 0);
				}
			}
			cplex.addMaximize(objectiveExpr);
			//

			//////////////////////////////////////
			// AJUSTES FINOS DO CPLEX
			///////////////////////////
			// Usando Default

			// // Usa apenas 6 núcleos para evitar sobrecarga de memória
			// cplex.setParam(IloCplex.Param.Threads, 6);
			//
			// Foco best bound
			// cplex.setParam(IloCplex.Param.Emphasis.MIP, 3);
			//
			// cplex.setParam(IloCplex.Param.MIP.Strategy.HeuristicFreq, 100);
			//
			 //cplex.setParam(IloCplex.Param.MIP.Strategy.File, 3);
			//
			// // Utiliza o paralelismo como deterministico
			//cplex.setParam(IloCplex.Param.Parallel, IloCplex.ParallelMode.Deterministic);
			// cplex.setParam(IloCplex.Param.Preprocessing.Presolve,false);
			// cplex.setParam(IloCplex.Param.Preprocessing.NumPass,1);
			// cplex.setParam(IloCplex.Param.MIP.Limits.ProbeTime,10);
			// cplex.setParam(IloCplex.Param.RootAlgorithm, 2);
			// cplex.setParam(IloCplex.Param.Emphasis.Numerical, true);
			// cplex.setParam(IloCplex.Param.MIP.Limits.RepairTries, 100);

		} catch (IloException e) {
			e.printStackTrace();
			throw new RuntimeException("Error initializing CPLEX", e);
		}
	}


	public ChallengeSolution solve(StopWatch stopWatch) {
		Set<Integer> aislesSelected = new HashSet<>();
		Set<Integer> ordersSelected = new HashSet<>();

		try {
			long remainingTimeSeconds = getRemainingTime(stopWatch);
			long cplexTimeLimit = Math.max(remainingTimeSeconds - 30, 1);
			cplex.setParam(IloCplex.Param.TimeLimit, cplexTimeLimit);

			if (cplex.solve()) {
				double[] valAisles = cplex.getValues(X_AI);
				double[] valOrders = cplex.getValues(X_OR);

				for (int ai = 0; ai < valAisles.length; ai++) {
					if (valAisles[ai] > 0.5)
						aislesSelected.add(ai);
				}

				for (int or = 0; or < valOrders.length; or++) {
					if (valOrders[or] > 0.5)
						ordersSelected.add(or);
				}

			} else {
				return null;
			}

		} catch (IloException e) {
			e.printStackTrace();
			return null;
		} finally {
			cplex.end();
		}

		return new ChallengeSolution(ordersSelected, aislesSelected);
	}

	/*
	 * Get the remaining time in seconds
	 */
	protected long getRemainingTime(StopWatch stopWatch) {
		return Math.max(
				TimeUnit.SECONDS.convert(MAX_RUNTIME - stopWatch.getTime(TimeUnit.MILLISECONDS), TimeUnit.MILLISECONDS),
				0);
	}

	protected boolean isSolutionFeasible(ChallengeSolution challengeSolution) {
		Set<Integer> selectedOrders = challengeSolution.orders();
		Set<Integer> visitedAisles = challengeSolution.aisles();
		if (selectedOrders == null || visitedAisles == null || selectedOrders.isEmpty() || visitedAisles.isEmpty()) {
			return false;
		}

		int[] totalUnitsPicked = new int[nItems];
		int[] totalUnitsAvailable = new int[nItems];

		// Calculate total units picked
		for (int order : selectedOrders) {
			for (Map.Entry<Integer, Integer> entry : orders.get(order).entrySet()) {
				totalUnitsPicked[entry.getKey()] += entry.getValue();
			}
		}

		// Calculate total units available
		for (int aisle : visitedAisles) {
			for (Map.Entry<Integer, Integer> entry : aisles.get(aisle).entrySet()) {
				totalUnitsAvailable[entry.getKey()] += entry.getValue();
			}
		}

		// Check if the total units picked are within bounds
		int totalUnits = Arrays.stream(totalUnitsPicked).sum();
		if (totalUnits < waveSizeLB || totalUnits > waveSizeUB) {
			return false;
		}

		// Check if the units picked do not exceed the units available
		for (int i = 0; i < nItems; i++) {
			if (totalUnitsPicked[i] > totalUnitsAvailable[i]) {
				return false;
			}
		}

		return true;
	}

	protected double computeObjectiveFunction(ChallengeSolution challengeSolution) {
		Set<Integer> selectedOrders = challengeSolution.orders();
		Set<Integer> visitedAisles = challengeSolution.aisles();
		if (selectedOrders == null || visitedAisles == null || selectedOrders.isEmpty() || visitedAisles.isEmpty()) {
			return 0.0;
		}
		int totalUnitsPicked = 0;

		// Calculate total units picked
		for (int order : selectedOrders) {
			totalUnitsPicked += orders.get(order).values().stream().mapToInt(Integer::intValue).sum();
		}

		// Calculate the number of visited aisles
		int numVisitedAisles = visitedAisles.size();

		// Objective function: total units picked / number of visited aisles
		return (double) totalUnitsPicked / numVisitedAisles;
	}
}
