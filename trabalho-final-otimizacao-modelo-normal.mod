/*********************************************
 * OPL 22.1.1.0 Model
 * Author: beatr
 * Creation Date: 11 de fev de 2026 at 15:24:32
 *********************************************/
//Conjuntos:

int Proporcao_Demanda = ...;
int Veiculos_Car = ...;
int Veiculos_Para = ...;

range N = 1..Proporcao_Demanda;  // Terminais
range T = 1..Veiculos_Car;       // Períodos de tempo
range V = 1..Veiculos_Para;      // Tipos/quantidade de veículos

//Parâmetros:

// Custos e Receitas:
float p[N][N][V] = ...; //Receita do frete de i para j com veículo v (p_ij^v)
float c[N][N][V] = ...; //Custo de reposicionamento do veículo parado do tipo v de i para j (c_ij^v)
float h[N][N][T] = ...; //Penalidade por backlog/atraso no período t (h_ij^t)

//Demanda e Operação:
float d[N][N][T] = ...; //Demanda de transporte de i para j gerada no período t (d_ij^t)
int tv[N][N] = ...;     //Tempo de viagem de i para j (tv_ij)
int K[N][T] = ...;      //Capacidade de descarregamento no terminal j no tempo t (K_j^t)
int m[N][V][T] = ...;   //Número de veículos do tipo v disponíveis no terminal i no período t (m_i^vt)
int A[N][N][V] = ...;   //Rota permitida (1) / proibida (0) (A_ij^v)

//Variáveis de Decisão:

// w_ij^st: Proporção da demanda gerada em s que será atendida em t
dvar float+ w[N][N][T][T];

// x_ij^vt: Veículos carregados do tipo v de i para j no tempo t
dvar int+ x[N][N][V][T];

// y_ij^vt: Veículos parados de i para j no tempo t
dvar int+ y[N][N][V][T];

//Função Objetivo (2a):
maximize
  //Receita de carregados - Custo dos parados:
  sum(i in N, j in N, t in T, v in V) (
    p[i][j][v] * x[i][j][v][t] - c[i][j][v] * y[i][j][v][t]
  )
  -
  //Penalidade por backlog (atendimento tardio t>s)
  sum(i in N, j in N, t in T, s in T : i!=j && s < t) (
    h[i][j][t] * d[i][j][s] * w[i][j][s][t]
  );

//Restrições:
subject to {

  //Conservação do fluxo de veículos (2b):
  //Veículos saindo(x+y) - Veículos chegando(x+y atrasados pelo tempo de viagem) - veículos que já tinham parado lá anteriormente
  forall(i in N, t in T, v in V) {
    sum(j in N) (x[i][j][v][t] + y[i][j][v][t])
      - sum(k in N : t > tv[k][i]) (x[k][i][v][t - tv[k][i]] + y[k][i][v][t - tv[k][i]])
      - (t > 1 ? y[i][i][v][t-1] : 0) //se t=1 não há estoque anterior ou define-se condição de contorno
      == m[i][v][t];
  }

  // (2c) Capacidade de descarregamento no destino
  forall(j in N, t in T) {
    sum(i in N, v in V : t > tv[i][j]) (
      x[i][j][v][t - tv[i][j]] // Veículos que chegaram agora (partiram em t - tv)
    ) <= K[j][t];
  }

  //Atendimento da demanda vs Veículos disponíveis (2d):
  //Garante que não carregamos mais veículos do que a demanda atendida permite
  forall(i in N, j in N, t in T : i != j) {
    sum(s in T : s <= t) (d[i][j][s] * w[i][j][s][t]) >= sum(v in V) x[i][j][v][t];
  }

  // (2e) Limite da proporção de demanda (Total atendido <= 100%)
  forall(i in N, j in N, s in T : i != j) {
    sum(t in T : t >= s) w[i][j][s][t] <= 1;
  }

  // (2f) Rotas proibidas (A_ij^v = 0)
  forall(i in N, j in N, t in T, v in V) {
    if (A[i][j][v] == 0) {
      x[i][j][v][t] == 0;
      y[i][j][v][t] == 0;
    }
  }

  // (2i) Restrição lógica temporal do backlog
  // A demanda só pode ser atendida após ter sido gerada (t >= s).
  forall(i in N, j in N, s in T, t in T : i != j) {
    if (t < s) {
      w[i][j][s][t] == 0;
    }
  }

  // (2j) Não existe atendimento de demanda de i para i (diagonal),
  // então zera w[i][i][s][t] para evitar variáveis "soltas"
  forall(i in N, s in T, t in T) {
    w[i][i][s][t] == 0;
  }

}