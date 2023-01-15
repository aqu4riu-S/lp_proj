:- [codigo_comum].

%-----------------------------------------------------
%             Predicado combinacoes_soma/4
%-----------------------------------------------------
% combinacoes_soma(N, Els, Soma, Combs) - Combs eh a lista ordenada cujos
% elementos sao as combinacoes N a N, dos elementos de Els cuja soma eh Soma

igual(X, L) :-
    sum_list(L, Soma_L),
    X =:= Soma_L.

% combinacoes_soma/4
combinacoes_soma(N, Els, Soma, Combs) :-
    bagof(Comb, combinacao(N, Els, Comb), L_Combs),
    include(igual(Soma), L_Combs, Combs).

%-----------------------------------------------------
%             Predicado permutacoes_soma/4
%-----------------------------------------------------
% permutacoes_soma(N, Els, Soma, Perms) - Perms eh a lista ordenada cujos
% elementos sao as permutacoes das coombinacoes N a N, dos elementos de Els
% cuja soma eh Soma
permutacoes_soma(N, Els, Soma, Perms) :-
    combinacoes_soma(N, Els, Soma, Combs),
    setof(Perm, Comb^((member(Comb, Combs)), permutation(Comb, Perm)), Perms).


%-----------------------------------------------------
%     3.1.3    Predicado espaco_fila/2
%-----------------------------------------------------
% espaco_fila(Fila, espaco(Soma, Variaveis), H_V) - Esp eh um espaco de Fila
% (H_V eh um dos atomos h ou v, significando fila horizontal e vertical, 
% respetivamente)

primeiro_el([E | _], E).
segundo_el([_, E | _], E).


% acede_lista([], [], []).
acede_lista([P | R], P, R).

e_prefixo(Pref) :- 
    last(Pref, Ult),
    nonvar(Ult),
    % garantir que nao e [0, 0]
    sumlist(Ult, Soma),
    Soma > 0.
    
e_sufixo(Suf) :- Suf = [].
e_sufixo([P | _]) :- nonvar(P).


espaco_fila_aux(Fila, Esp_simples, Ult) :-
    append([Pref, Esp_simples, Suf], Fila),
    e_prefixo(Pref),
    e_sufixo(Suf),
    length(Esp_simples, Comp_Esp),
    Comp_Esp > 0,
    maplist(var, Esp_simples),
    last(Pref, Ult).

espaco_fila(Fila, espaco(Soma, Esp_simples), H_V) :-
    espaco_fila_aux(Fila, Esp_simples, Ult),
    H_V == h,
    segundo_el(Ult, Soma).
espaco_fila(Fila, espaco(Soma, Esp_simples), H_V) :-
    espaco_fila_aux(Fila, Esp_simples, Ult),
    H_V == v,
    primeiro_el(Ult, Soma).


%-----------------------------------------------------
%     3.1.4    Predicado espacos_fila/2
%-----------------------------------------------------
% espacos_fila(H_V, Fila, Espacos) - Espacos eh a lista de todos os espacos de
% fila, da esquerda para a direita (H_V eh um dos atomos h ou v, significando
% fila horizontal e vertical, respetivamente)

espacos_fila(H_V, Fila, Espacos) :-
    bagof(espaco(Soma, Esp_simples), 
        espaco_fila(Fila, espaco(Soma, Esp_simples), H_V), Espacos), !.
espacos_fila(_, _, []).

%-----------------------------------------------------
%     3.1.5    Predicado espacos_puzzle/2
%-----------------------------------------------------
% espacos_puzzle(Puzzle, Espacos) - Espacos eh a lista de espacos de Puzzle

itera_puzzle(Puzzle, Espacos, H_V) :- itera_puzzle(Puzzle, Espacos, H_V, []).
itera_puzzle([], Espacos, _, Espacos).
itera_puzzle([Fila | Resto], Espacos, H_V, Aux) :-
    espacos_fila(H_V, Fila, Res),
    append(Aux, Res, Aux_act),
    itera_puzzle(Resto, Espacos, H_V, Aux_act).


espacos_puzzle(Puzzle, Espacos) :-
    itera_puzzle(Puzzle, Res_1, h),
    mat_transposta(Puzzle, Transp),
    itera_puzzle(Transp, Res_2, v),
    append(Res_1, Res_2, Espacos).

%-----------------------------------------------------
%      3.1.6 Predicado espacos_com_posicoes_comuns/3
%-----------------------------------------------------
% espacos_com_posicoes_comuns(Espacos, Esp, Esps_com) - Esps_com eh a lista de
% espacos com variaveis em comum com Esp, exceptuando Esp

lsts_dif([], []) :- fail.
lsts_dif([P1 | _], [P2 | _]) :- P1 \== P2, !.
lsts_dif([_ | R1], [_ | R2]) :- lsts_dif(R1, R2).

acede_espaco(espaco(Soma, Vars), Soma, Vars).


% e_var_comum/2
% e_var_commum(Var, Lst) --> True se Var existe na lista, False caso contrario
e_var_comum(Var, [P | _]) :- Var == P, !.
e_var_comum(Var, [_ | R]) :- e_var_comum(Var, R), !.

% tem_vars_comuns/2
% tem_vars_comuns(L1, L2) --> Verifica se L1 tem algum elemento comum com L2
tem_vars_comuns([Var | _], Esp2) :- e_var_comum(Var, Esp2), !.
tem_vars_comuns([_ | R_vars], Esp2) :- tem_vars_comuns(R_vars, Esp2), !.


% espacos_com_posicoes_comuns/3
espacos_com_posicoes_comuns(Espacos, Esp, Esp_com) :- 
    espacos_com_posicoes_comuns(Espacos, Esp, Esp_com, []).
espacos_com_posicoes_comuns([], _, Esp_com, Esp_com) :- !.
espacos_com_posicoes_comuns([P | R], espaco(_, Vars), Esp_com, Aux) :-
    acede_espaco(P, _, Vars_P),
    tem_vars_comuns(Vars, Vars_P), 
    lsts_dif(Vars, Vars_P), % excecao do proprio espaco
    append(Aux, [P], Aux_act),
    espacos_com_posicoes_comuns(R, espaco(_, Vars), Esp_com, Aux_act), !.
espacos_com_posicoes_comuns([_ | R], espaco(_, Vars), Esp_com, Aux) :-
    espacos_com_posicoes_comuns(R, espaco(_, Vars), Esp_com, Aux).%, !.

%-----------------------------------------------------
%      3.1.7  Predicado permutacoes_soma_espacos/2
%-----------------------------------------------------
% permutacoes_soma_espacos(Espacos, perms_soma) - Perms_soma eh a lista de
% listas de 2 elementos, em que o primeiro eh um espaco de Espacos e o segundo
% eh a lista ordenada de permutacoes cuja soma eh igual a soma do espaco

permutacoes_soma_espacos(Espacos, Perms_soma) :- 
    permutacoes_soma_espacos(Espacos, Perms_soma, []).
permutacoes_soma_espacos([], Perms_soma, Perms_soma).    
permutacoes_soma_espacos([P | R], Perms_soma, Aux) :-    
    acede_espaco(P, Soma, Vars),
    length(Vars, Num_Vars),
    findall(N, between(1, 9, N), L),
    permutacoes_soma(Num_Vars, L, Soma, Perms),
    append(Aux, [[P, Perms]], Aux_act),
    permutacoes_soma_espacos(R, Perms_soma, Aux_act).


%-----------------------------------------------------
%    3.1.8  Predicado permutacao_possivel_espaco/4
%-----------------------------------------------------
% permutacao_possivel_espaco(Perm, Esp, Espacos, Perms_soma)
% Perm eh uma permutacao possivel para o espaco Esp

acede_lst_perm([], _, _) :- !, fail. 
acede_lst_perm([P | _], Esp, Lst) :-
    P = [Esp1, Lst],
    Esp1 == Esp, !.
    %member(Esp, P),
acede_lst_perm([_ | R], Esp, Perms) :- acede_lst_perm(R, Esp, Perms).

e_perm_possivel(Perms_soma, Esp) :-
    acede_espaco(Esp, _, Vars),
    acede_lst_perm(Perms_soma, Esp, Perms_Esp), 
    include(subsumes_term(Vars), Perms_Esp, Perms_poss),
    length(Perms_poss, Comp),
    Comp > 0.

permutacao_possivel_espaco(Perm, Esp, Espacos, Perms_soma) :-
    acede_lst_perm(Perms_soma, Esp, Perms_Esp), 
    espacos_com_posicoes_comuns(Espacos, Esp, Esps_com),
    member(Perm, Perms_Esp),
    acede_espaco(Esp, _, Vars),
    Vars = Perm, 
    maplist(e_perm_possivel(Perms_soma), Esps_com).

%-----------------------------------------------------
%    3.1.9 Predicado permutacoes_possiveis_espaco/4
%-----------------------------------------------------
% permutacoes_possiveis_espaco(Espacos, Perms_soma, Esp, Perms_poss) 
% Perms_poss eh uma lista de 2 elementos, em que o primeiro eh a lista de
% variaveis de Esp e o segundo eh a lista ordenada de perms possiveis para Esp

permutacoes_possiveis_espaco(Espacos, Perms_soma, Esp, Perms_poss) :-
    Esp = espaco(_, Vars),
    findall(Perm, 
        permutacao_possivel_espaco(Perm, Esp, Espacos, Perms_soma), Perms),
    append([Vars], [Perms], Perms_poss).

%-----------------------------------------------------
%   3.1.10 Predicado permutacoes_possiveis_espacos/2
%-----------------------------------------------------
% permutacoes_possiveis_espacos(Espacos, Perms_poss_esps)
% Perms_poss_esps eh a lista de permutacoes possiveis

itera_espacos(Espacos, Espacos, Perms_soma, Perms_poss_esps) :- 
    itera_espacos(Espacos, Espacos, Perms_soma, Perms_poss_esps, []).
itera_espacos([], _, _, Perms_poss_esps, Perms_poss_esps) :- !.
itera_espacos([P | R], Espacos, Perms_soma, Perms_poss_esps, Aux) :-
    permutacoes_possiveis_espaco(Espacos, Perms_soma, P, Perms_poss),
    append(Aux, [Perms_poss], Aux_act),
    itera_espacos(R, Espacos, Perms_soma, Perms_poss_esps, Aux_act), !.
itera_espacos([_ | R], Espacos, Perms_soma, Perms_poss_esps, Aux) :-
    itera_espacos(R, Espacos, Perms_soma, Perms_poss_esps, Aux), !.


permutacoes_possiveis_espacos(Espacos, Perms_poss_esps) :-
    permutacoes_soma_espacos(Espacos, Perms_soma),
    itera_espacos(Espacos, Espacos, Perms_soma, Perms_poss_esps), !.

%-----------------------------------------------------
%    3.1.11   Predicado numeros_comuns/2
%-----------------------------------------------------
% numeros_comuns(Lst_Perms, Numeros_comuns) - Numeros_comuns eh uma lista de
% pares (pos, numero), tal que todas as listas de Lst_Perms contem o numero
% numero na posicao pos

el_na_pos(El, Pos, Lst) :- nth1(Pos, Lst, El).

acede_primeiro([El | R], El, [R]).

numeros_comuns(Lst_Perms, Numeros_comuns) :- 
    numeros_comuns(Lst_Perms, Numeros_comuns, [], 1).
numeros_comuns([[] | _], Numeros_comuns, Numeros_comuns, _).
numeros_comuns([P | R_lsts], Numeros_comuns, Aux, Pos) :-
    acede_primeiro(P, El, Res),
    maplist(el_na_pos(El, Pos), R_lsts),
    Pos_act is Pos + 1,
    append(Aux, [(Pos, El)], Aux_act),
    append(Res, R_lsts, Lst_act),
    numeros_comuns(Lst_act, Numeros_comuns, Aux_act, Pos_act), !.
numeros_comuns([P | R_lsts], Numeros_comuns, Aux, Pos) :-
    acede_primeiro(P, _, Res),
    Pos_act is Pos + 1,
    append(Res, R_lsts, Lst_act),
    numeros_comuns(Lst_act, Numeros_comuns, Aux, Pos_act), !.


%-----------------------------------------------------
%      3.1.12    Predicado atribui_comuns/1
%-----------------------------------------------------
% atribui_comuns(Perms_Possiveis) - Atualiza a lista Perms_Possiveis,
% atribuindo a cada espaco numeros comuns a todas as permutacoes possiveis 
% para esse espaco

% atualiza_vars/2
atualiza_vars([], _).
atualiza_vars([Subs | Resto], Vars) :-
    (Pos, El) = Subs,
    nth1(Pos, Vars, El),
    atualiza_vars(Resto, Vars).

% itera_lst_perms_poss/1
itera_lst_perms_poss([]).
itera_lst_perms_poss([P | R]) :-
    [Vars, Perms] = P,
    numeros_comuns(Perms, Numeros_comuns),
    atualiza_vars(Numeros_comuns, Vars),
    itera_lst_perms_poss(R).


atribui_comuns(Perms_Possiveis) :-
    itera_lst_perms_poss(Perms_Possiveis).


%-----------------------------------------------------
%     3.1.13    Predicado retira_impossiveis/2
%-----------------------------------------------------
% retira_impossiveis(Perms_Possiveis, Novas_Perms_Possiveis)
% Novas_Perms_Possiveis eh o resultado de tirar permutacoes impossiveis de
% Perms_Possiveis

itera_lst_perms_poss_act(Perms_Possiveis, Novas_Perms_Possiveis) :- 
    itera_lst_perms_poss_act(Perms_Possiveis, Novas_Perms_Possiveis, []).
itera_lst_perms_poss_act([], Novas_Perms_Possiveis, Novas_Perms_Possiveis).
itera_lst_perms_poss_act([P | R], Novas_Perms_Possiveis, Aux) :-
    [Vars, Perms] = P,
    include(subsumes_term(Vars), Perms, Perms_Possiveis),
    append([Vars], [Perms_Possiveis], Perm_act),
    append(Aux, [Perm_act], Aux_act),
    itera_lst_perms_poss_act(R, Novas_Perms_Possiveis, Aux_act).


retira_impossiveis(Perms_Possiveis, Novas_Perms_Possiveis) :-
    itera_lst_perms_poss_act(Perms_Possiveis, Novas_Perms_Possiveis).


%-----------------------------------------------------
%     3.1.14    Predicado simplifica/2
%-----------------------------------------------------
% simplifica(Perms_Possiveis, Novas_Perms_Possiveis)
% Novas_Perms_Possiveis eh o resultado de simplificar Perms_Possiveis
% (aplicando os predicados atribui_comuns e retira_impossiveis)
simplifica(Perms_Possiveis, Novas_Perms_Possiveis) :-
    atribui_comuns(Perms_Possiveis),
    retira_impossiveis(Perms_Possiveis, Novas_Perms_Possiveis),
    Perms_Possiveis == Novas_Perms_Possiveis, !.
simplifica(Perms_Possiveis, Novas_Perms_Possiveis) :-
    atribui_comuns(Perms_Possiveis),
    retira_impossiveis(Perms_Possiveis, Novas_Perms_Possiveis_1),
    simplifica(Novas_Perms_Possiveis_1, Novas_Perms_Possiveis).


%-----------------------------------------------------
%     3.1.15    Predicado inicializa/2
%-----------------------------------------------------
% inicializa(Puzzle, Perms_Possiveis) - Perms_Possiveis eh a lista de
% permutacoes possiveis simplificada para o puzzle Puzzle
inicializa(Puzzle, Perms_Possiveis) :-
    espacos_puzzle(Puzzle, Espacos),
    permutacoes_possiveis_espacos(Espacos, Perms_poss_esps),
    simplifica(Perms_poss_esps, Perms_Possiveis).



%-----------------------------------------------------
%     3.2.1 Predicado escolhe_menos_alternativas/2
%-----------------------------------------------------
% escolhe_menos_alternativas(Perms_Possiveis, Escolha) - Escolha eh o elemento
% de Perms_Possiveis escolhido segundo o criterio na seccao 2.2, passo 1

% comp/1 - Perms eh uma lista de comprimento superior a 1
comp([_, Perms]) :- 
    length(Perms, Comp),
    Comp > 1.

% calcula_comp/2 - calcula(Lst, Lst_comp)
% Lst_comp eh a lista de comprimentos relativos as listas de Lst
calcula_comp([], []) :- !.
calcula_comp([P | R], Lst_comps) :-
    P = [_, Perms],
    length(Perms, Comp),
    calcula_comp(R, Lst_comps_act),
    append([Comp], Lst_comps_act, Lst_comps).


escolhe_menos_alternativas(Perms_Possiveis, Escolha) :-
    include(comp, Perms_Possiveis, Lst),
    length(Lst, Comp),
    Comp > 0,
    calcula_comp(Lst, Lst_comps),
    min_list(Lst_comps, Min),
    % Pos e a posicao do elemento minimo da lista de comprimentos
    nth1(Pos, Lst_comps, Min),  
    % Perms_menos alt e a lista pretendida, na posicao Pos da lista Lst
    nth1(Pos, Lst, Escolha), !.



%-----------------------------------------------------
%     3.2.2    Predicado experimenta_perm/3
%-----------------------------------------------------
% experimena_perm(Escolha, Perms_Possiveis, Novas_Perms_Possiveis)
% Novas_Perms_Possiveis eh o resultado de substituir, em Perms_Possiveis, o
% elemento Escolha pelo elemento [Esp, [Perm]]
experimenta_perm(Escolha, Perms_Possiveis, Novas_Perms_Possiveis) :-
    Escolha = [Vars, Lst_Perms],
    member(Perm, Lst_Perms),
    Vars = Perm,
    select(Escolha, Perms_Possiveis, [Vars, [Perm]], Novas_Perms_Possiveis), !.
    
    
%-----------------------------------------------------
%     3.2.3    Predicado resolve_aux/2
%-----------------------------------------------------
% tem_superior_1/1 - True se existe pelo menos um espaco com um numero de
% permutacoes possiveis superior a 1
tem_superior_1([]) :- !, fail.
tem_superior_1([P | _]) :-
    P = [_, Perms],
    length(Perms, Comp),
    Comp > 1, !.
tem_superior_1([_ | R]) :- tem_superior_1(R).


% resolve_aux(Perms_Possiveis, Novas_Perms_Possiveis) - 
%Novas_Perms_Possiveis eh o resultado de aplicar o algoritmo
% descrito na seccao 2.2 a Perms_Possiveis
resolve_aux(Perms_Possiveis, Novas_Perms_Possiveis) :-
    escolhe_menos_alternativas(Perms_Possiveis, Escolha),
    experimenta_perm(Escolha, Perms_Possiveis, Novas_Perms_Possiveis_1),
    simplifica(Novas_Perms_Possiveis_1, Novas_Perms_Possiveis_2),
    tem_superior_1(Novas_Perms_Possiveis_2),
    resolve_aux(Novas_Perms_Possiveis_2, Novas_Perms_Possiveis). 


resolve_aux(Perms_Possiveis, Novas_Perms_Possiveis) :-
    escolhe_menos_alternativas(Perms_Possiveis, Escolha),
    experimenta_perm(Escolha, Perms_Possiveis, Novas_Perms_Possiveis_1),
    simplifica(Novas_Perms_Possiveis_1, Novas_Perms_Possiveis), !.
    
%-----------------------------------------------------
%     3.3.1    Predicado resolve/1
%-----------------------------------------------------
% resolve(Puz) - resolve o puzzle Puz
resolve(Puz) :-
    inicializa(Puz, Perms_Possiveis),
    resolve_aux(Perms_Possiveis, Novas_Perms_Possiveis),
    escreve_Puzzle(Novas_Perms_Possiveis).