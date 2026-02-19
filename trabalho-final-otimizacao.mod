/*********************************************
 * OPL 22.1.1.0 Model
 * Author: fabriciosiqueira
 * Creation Date: 19 de fev. de 2026 at 20:26:07
 *********************************************/

// Conjuntos:
int Proporcao_Demanda = ...;
int Veiculos_Car = ...;
int Veiculos_Para = ...;

range N = 1..Proporcao_Demanda;  // Terminais
range T = 1..Veiculos_Car;       // Períodos de tempo
range V = 1..Veiculos_Para;      // Tipos de veículos

// Parâmetros - Custos, Receitas e Operação:
float p[N][N][V] = ...; // Receita do frete
float c[N][N][V] = ...; // Custo de reposicionamento (veículo vazio)
float h[N][N][T] = ...; // Penalidade por backlog/atraso no período t
float d[N][N][T] = ...; // Demanda nominal (d_ij^t)
int tv[N][N] = ...;     // Tempo de viagem 
int K[N][T] = ...;      // Capacidade de descarregamento
int m[N][V][T] = ...;   // Veículos inicialmente disponíveis
int A[N][N][V] = ...;   // Rota permitida (1) / proibida (0)

// Parâmetros de Otimização Robusta (Novos):
float d_hat[N][N][T] = ...; // Desvio máximo da demanda (incerteza)
float Gamma0 = ...;         // Orçamento de incerteza para a função objetivo
int Gamma[N][N][T] = ...;   // Orçamento de incerteza para as restrições (Gamma_ij^t)

// Variáveis de Decisão Principais:
dvar float+ w[N][N][T][T]; // Proporção da demanda gerada em s atendida em t
dvar int+ x[N][N][V][T];   // Veículos carregados
dvar int+ y[N][N][V][T];   // Veículos parados/vazios

// Variáveis de Decisão Robustas (Duais):
dvar float+ lambda_0;               // Para o orçamento da função objetivo
dvar float+ mu_0[N][N][T];          // Para as demandas na função objetivo (s)
dvar float+ lambda_t[N][N][T];      // Para o orçamento nas restrições (t)
dvar float+ mu_s[N][N][T];          // Para as demandas nas restrições (s)

// Função Objetivo (3a):
maximize
  // Receita de carregados - Custo dos parados
  sum(i in N, j in N, t in T, v in V) (
    p[i][j][v] * x[i][j][v][t] - c[i][j][v] * y[i][j][v][t]
  )
  - // Penalidade nominal por backlog
  sum(i in N, j in N, t in T, s in T : i != j && t >= s) (
    h[i][j][t] * d[i][j][s] * w[i][j][s][t]
  )
  - // Proteção robusta na função objetivo (Variáveis duais)
  (Gamma0 * lambda_0) 
  - sum(i in N, j in N, s in T : i != j) mu_0[i][j][s];

// Restrições:
subject to {

  // (2b) Conservação do fluxo de veículos
  forall(i in N, t in T, v in V) {
    sum(j in N) (x[i][j][v][t] + y[i][j][v][t])
      - sum(k in N : k != i && t > tv[k][i]) (x[k][i][v][t - tv[k][i]] + y[k][i][v][t - tv[k][i]])
      - (t > 1 ? y[i][i][v][t-1] : 0)
      == m[i][v][t];
  }

  // (2c) Capacidade de descarregamento no destino
  forall(j in N, t in T) {
    sum(i in N, v in V : i != j && t > tv[i][j]) (
      x[i][j][v][t - tv[i][j]]
    ) <= K[j][t];
  }

  // (3b) Atendimento da demanda (Versão Robusta - substitui a 2d)
  forall(i in N, j in N, t in T : i != j) {
    sum(s in T : s <= t) (d[i][j][s] * w[i][j][s][t]) 
    - (Gamma[i][j][t] * lambda_t[i][j][t]) 
    - sum(s in T : s <= t) mu_s[i][j][s] 
    >= sum(v in V) x[i][j][v][t];
  }

  // (3c) Restrição dual para a incerteza do backlog na função objetivo
  forall(i in N, j in N, s in T : i != j) {
    lambda_0 + mu_0[i][j][s] >= d_hat[i][j][s] * sum(t in T : t >= s) (h[i][j][t] * w[i][j][s][t]);
  }

  // (3d) Restrição dual para a incerteza da proporção atendida
  forall(i in N, j in N, s in T, t in T : i != j && t >= s) {
    lambda_t[i][j][t] + mu_s[i][j][s] >= d_hat[i][j][s] * w[i][j][s][t];
  }

  // (2e) Limite da proporção de demanda (Total atendido <= 100%)
  forall(i in N, j in N, s in T : i != j) {
    sum(t in T : t >= s) w[i][j][s][t] <= 1;
  }

  // (2f) Rotas proibidas
  forall(i in N, j in N, t in T, v in V) {
    if (A[i][j][v] == 0) {
      x[i][j][v][t] == 0;
      y[i][j][v][t] == 0;
    }
  }

  // Lógicas adicionais de domínio temporal (2i e 2j)
  forall(i in N, j in N, s in T, t in T : i != j) {
    if (t < s) w[i][j][s][t] == 0;
  }
  forall(i in N, s in T, t in T) {
    w[i][i][s][t] == 0;
  }
}