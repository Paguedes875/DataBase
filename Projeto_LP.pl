%ist1107028 Ines Duarte Rodrigues Almeida Paredes
:- set_prolog_flag(answer_write_options,[max_depth(0)]).
:- ['dados.pl'], ['keywords.pl'].

%-------------------------------------------------------------------------------------------
/*
O predicado eventosSemSalas/1 eh deterministico.
    eventosSemSalas(-EventosSemSala). 

Este predicado eh verdade se EventosSemSala corresponde a uma lista, ordenada e sem 
elementos repetidos, de IDs de eventos sem sala.
*/
%-------------------------------------------------------------------------------------------
eventosSemSalas(EventosSemSala) :-
    findall(ID, evento(ID, _, _, _, semSala), EventosSemSala).


%-------------------------------------------------------------------------------------------
/*
O predicado eventosSemSalasDiaSemana/2 eh deterministico.
    eventosSemSalasDiaSemana(+DiaDaSemana, -EventosSemSala).

Este predicado eh verdade se EventosSemSala corresponde a uma lista, ordenada e sem 
elementos repetidos, de IDs de eventos sem sala que decorrem em DiaDaSemana.
*/
%-------------------------------------------------------------------------------------------
eventosSemSalasDiaSemana(DiaDaSemana, EventosSemSala) :- 
    % Encontrar todos os ID que satisfazem as restricoes:
    findall(ID, (evento(ID, _, _, _, semSala), 
                horario(ID, DiaDaSemana, _, _, _, _)),  
            EventosSemSala). 


%Predicado auxiliar para os periodos e semestres
periodo(p1, [p1, p1_2]).
periodo(p2, [p2, p1_2]).
periodo(p3, [p3, p3_4]).
periodo(p4, [p4, p3_4]).

%-------------------------------------------------------------------------------------------
/*
O predicado eventosSemSalasPeriodo/2 eh deterministico.
    eventosSemSalasPeriodo(+ListaPeriodos, -EventosSemSala).

Este predicacdo eh verdade se ListaPeriodos corresponde a uma lista de periodos e 
EventosSemSala corresponde a uma lista, ordenada e sem elementos repetidos, de IDs de 
eventos sem sala nos periodos de ListaPeriodos. 
*/
%-------------------------------------------------------------------------------------------
eventosSemSalasPeriodo(ListaPeriodos, EventosSemSala) :-
    % Verifica se a ListaPeriodos esta vazia, e se sim, EventosSemSala eh uma lista vazia
    (ListaPeriodos == [] ,!, EventosSemSala = []);
    % Encontra todos os IDs de eventos que satisfazem as condicoes
    findall(ID, (member(Periodo, ListaPeriodos),
                periodo(Periodo, PeriodosLista),
                member(Prdo, PeriodosLista),
                evento(ID, _, _, _, semSala),
                horario(ID, _, _, _, _, Prdo)),
            EventosSemSalaDplicados),!,
    % Remove elementos duplicados e ordena a lista
    sort(EventosSemSalaDplicados,EventosSemSala).


%-------------------------------------------------------------------------------------------
/*
O predicado organizaEventos/3 eh deterministico. 
    organizaEventos(+Eventos, +Periodo, -EventosNoPeriodo). 

Este predicacdo eh verdade se EventosNoPeriodo corresponde a lista, ordenada e sem elementos 
repetidos, de IDs dos eventos de ListaEventos que ocorrem no Periodo.
*/
%-------------------------------------------------------------------------------------------
% Caso Termnal - Se a lista de eventos estiver vazia, retorna uma lista vazia
organizaEventos([], _, []).

organizaEventos([EventoID|Resto], Periodo, EventosNoPeriodo) :-
    horario(EventoID, _, _, _, _, Prdo),
    % Obtem a lista de periodos ao periodo desejado
    periodo(Periodo, PeriodosLista),
    member(Prdo, PeriodosLista),!,
    % Se estiver na lista chama recursivamente com o resto da lista
    organizaEventos(Resto, Periodo, Acumulador),
    % Adiciona o evento atual a lista de eventos e ordena
    sort([EventoID|Acumulador], EventosNoPeriodo). 

organizaEventos([_|Resto], Periodo, EventosNoPeriodo) :-
    % Se nao estiver na lista chama recursivamente com o resto da lista
    organizaEventos(Resto, Periodo, EventosNoPeriodo).


%-------------------------------------------------------------------------------------------
/*
O predicado eventosMenoresQue/2 eh deterministico.
    eventosMenoresQue(+Duracao, -ListaEventosMenoresQue). 

Este predicacdo eh verdade se ListaEventosMenoresQue corresponde a lista ordenada e sem 
elementos repetidos dos identificadores dos eventos que tem duracao menor ou igual a Duracao.
*/
%-------------------------------------------------------------------------------------------
eventosMenoresQue(Duracao, ListaEventosMenoresQue):-
    findall(ID, (horario(ID, _, _, _, Dura, _), Dura =< Duracao), ListaEventosMenoresQue).


%-------------------------------------------------------------------------------------------
/*
O predicado eventosMenoresQueBool/2 eh deterministico. 
    eventosMenoresQueBool(+ID, +Duracao).

Devolve true se o evento identificado por ID tiver duracao igual ou menor a Duracao, e 
false caso o contrario.
*/
%-------------------------------------------------------------------------------------------
eventosMenoresQueBool(ID, Duracao):-
    horario(ID, _, _, _, Dura, _), Dura =< Duracao.


%-------------------------------------------------------------------------------------------
/*
O predicado procuraDisciplinas/2 eh deterministico.
    procuraDisciplinas(+Curso, -ListaDisciplinas).

Este predicacdo eh verdade se ListaDisciplinas corresponde a lista ordenada alfabeticamente 
do nome das disciplinas do curso Curso.
*/
%-------------------------------------------------------------------------------------------
procuraDisciplinas(Curso, ListaDisciplinas) :-
    % Encontra todos NomeDisciplina que satisfazem as condicoes
    findall(NomeDisciplina, (turno(ID, Curso, _, _),
                            evento(ID, NomeDisciplina, _, _, _)),
            ListaResultante),
    % Ordena a lista de nomes de disciplinas encontradas
    sort(ListaResultante, ListaDisciplinas).


%-------------------------------------------------------------------------------------------
/*
O predicado procuraDisciplinas/3 eh deterministico.
    organizaDisciplinas(+ListaDisciplinas, +Curso, -Semestres).

Este predicacdo eh verdade se Semestres corresponde a uma lista com duas listas, em que a 
lista na primeira posicao contem as disciplinas de ListaDisciplinas do curso Curso que 
ocorrem no primeiro semestre e a lista na segunda posicao, que contem as que ocorrem no 
segundo semestre.
*/
%-------------------------------------------------------------------------------------------
organizaDisciplinas(ListaDisciplinas, Curso, Semestres) :-
    % Chama o predicado organizaDisciplinas/5 passando as listas vazias de disciplinas do 
    % primeiro e segundo semestre
    organizaDisciplinas(ListaDisciplinas, Curso, [], [], Semestres),!.

organizaDisciplinas([], _, PrimSemestre, SegSemestre, [PrimSemestreOrd, SegSemestreOrd]) :-
    not(PrimSemestre == []) , not(SegSemestre == []),
    sort(PrimSemestre, PrimSemestreOrd),
    sort(SegSemestre, SegSemestreOrd).

% Se a lista de disciplinas nao for vazia, verifica se ela pertence ao primeiro ou segundo 
%semestre e adiciona na lista correspondente
organizaDisciplinas([Disciplina|Disciplinas], Curso, PrimSemestre, SegSemestre, Semestres) :-

    pertencePrimSemestre(Disciplina, Curso),
    organizaDisciplinas(Disciplinas, Curso, 
    [Disciplina|PrimSemestre], SegSemestre, Semestres);

    pertenceSegSemestre(Disciplina, Curso),
    organizaDisciplinas(Disciplinas, Curso, PrimSemestre,[Disciplina|SegSemestre], Semestres);

    % Se a disciplina nao pertence ao primeiro ou segundo semestre, continua a verificacao com 
    %as demais disciplinas da lista
    organizaDisciplinas(Disciplinas, Curso, PrimSemestre, SegSemestre, Semestres).

%Predicado auxiliar que verifica se a Disciplina pertence ao primeiro semestre do curso
pertencePrimSemestre(Disciplina, Curso) :-
    turno(ID, Curso, _, _), evento(ID, Disciplina, _, _, _), horario(ID, _, _, _, _, Prdo),
    (periodo(p1, Periodos), member(Prdo, Periodos); periodo(p2, Periodos), 
    member(Prdo, Periodos)).

%Predicado auxiliar que verifica se a Disciplina pertence ao segundo semestre do curso
pertenceSegSemestre(Disciplina, Curso) :-
    turno(ID, Curso, _, _), evento(ID, Disciplina, _, _, _), horario(ID, _, _, _, _, Prdo),
    (periodo(p3, Periodos), member(Prdo, Periodos); periodo(p4, Periodos), 
    member(Prdo, Periodos)).


%-------------------------------------------------------------------------------------------
/*
O predicado horasCurso/4 eh deterministico.
    horasCurso(+Periodo, +Curso, +Ano, -TotalHoras).

Este predicacdo eh verdade se TotalHoras corresponde ao numero de horas total dos eventos 
associadas ao curso Curso, no ano Ano e periodo Periodo.
*/
%-------------------------------------------------------------------------------------------
horasCurso(Periodo, Curso, Ano, TotalHoras) :-
    periodo(Periodo, PeriodosLista),
    findall(ID, turno(ID, Curso, Ano, _), CursoIDs),
    % Se nao houver turnos correspondentes, TotalHoras eh definido como 0
    (CursoIDs == [] , TotalHoras is 0 ;
    % Remove os elementos duplicados da lista de IDs de turno
    setof(X, member(X, CursoIDs), ListaUnica),
    findall(Horas, (horario(HorarioID, _, _, _, Horas, Prdo), 
                    member(HorarioID, ListaUnica), 
                    member(Prdo, PeriodosLista)), 
            ListaResultante),
    % Se nao houver horarios correspondentes, TotalHoras eh definido como 0
    (ListaResultante == [] , TotalHoras is 0 ;
    sum_list(ListaResultante, TotalHoras))).


%-------------------------------------------------------------------------------------------
/*
O predicado evolucaoHorasCurso/2 eh deterministico.
    evolucaoHorasCurso(+Curso, -Evolucao).

Este predicacdo eh verdade se Evolucao corresponde a uma lista de tuplos na forma 
(Ano, Periodo, NumHoras), em que NumHoras corresponde ao total de horas associadas ao curso 
Curso, no ano Ano e periodo Periodo.
*/
%-------------------------------------------------------------------------------------------
evolucaoHorasCurso(Curso, Evolucao) :-
    findall((Ano, Periodo, NumHoras), (member(Ano, [1,2,3]), 
                                    periodo(Periodo, _),
                                    horasCurso(Periodo, Curso, Ano, NumHoras)), 
            Evolucao).


%-------------------------------------------------------------------------------------------
/*
O predicado ocupaSlot/5 eh deterministico.
    ocupaSlot(+HoraInicioDada, +HoraFimDada, +HoraInicioEvento, +HoraFimEvento, -Horas).

Este predicacdo eh verdade se Horas corresponde ao numero de horas sobrepostas entre o 
evento que tem inicio em HoraInicioEvento e fim em HoraFimEvento, e o slot que tem inicio 
em HoraInicioDada e fim em HoraFimDada. 
*/
%-------------------------------------------------------------------------------------------
ocupaSlot(HoraInicioDada, HoraFimDada, HoraInicioEvento, HoraFimEvento, Horas) :-
    HoraInicioEvento < HoraFimDada, % Evento comeca antes do slot acabar
    HoraFimEvento > HoraInicioDada, % Evento acaba depois do slot comecar
    Horas is min(HoraFimDada, HoraFimEvento) - max(HoraInicioDada, HoraInicioEvento),
    Horas > 0.


%-------------------------------------------------------------------------------------------
/*
O predicado numHorasOcupadas/6 eh deterministico.
    numHorasOcupadas(+Periodo, +TipoSala, +DiaSemana, +HoraInicio, +HoraFim, -SomaHoras).

Este predicacdo eh verdade se SomaHoras corresponde ao numero de horas ocupadas nas salas 
do tipo TipoSala, no intervalo de tempo definido entre HoraInicio e HoraFim, no dia da 
semana DiaSemana, e no periodo Periodo.
*/
%-------------------------------------------------------------------------------------------
numHorasOcupadas(Periodo, TipoSala, DiaSemana, HoraInicio, HoraFim, SomaHoras) :-
    periodo(Periodo, PeriodosLista),
    findall(Horas, (evento(ID, _, _, _, Sala),
                    horario(ID, DiaSemana, HoraInicioEvento, HoraFimEvento, _, Prdo), 
                    salas(TipoSala, Salas),
                    ocupaSlot(HoraInicio, HoraFim, HoraInicioEvento, HoraFimEvento, Horas),
                    member(Sala, Salas),
                    member(Prdo, PeriodosLista)), 
            ListaHoras),
    % Soma todas as horas encontradas
    sum_list(ListaHoras, SomaHoras).


%-------------------------------------------------------------------------------------------
/*
O predicado ocupacaoMax/4 eh deterministico.
    ocupacaoMax(+TipoSala, +HoraInicio, +HoraFim, -Max).

Este predicacdo eh verdade se Max corresponde ao numero de horas possiveis de ser ocupadas 
por salas do tipo TipoSala, no intervalo de tempo definido entre HoraInicio e HoraFim.
*/
%-------------------------------------------------------------------------------------------
ocupacaoMax(TipoSala, HoraInicio, HoraFim, Max) :-
    % Calcula a diferenca de horas entre HoraFim e HoraInicio
    Intervalo is HoraFim - HoraInicio,
    salas(TipoSala, Salas),
    % Calcula o numero de salas disponiveis
    length(Salas, NumSalas),
    Max is Intervalo * NumSalas.


%-------------------------------------------------------------------------------------------
/*
O predicado percentagem/3 eh deterministico.
    percentagem(+SomaHoras, +Max, -Percentagem).

Este predicacdo eh verdade se Percentagem corresponde a divisao de SomaHoras por Max, 
multiplicada por 100.
*/
%-------------------------------------------------------------------------------------------
percentagem(SomaHoras, Max, Percentagem) :-
    Percentagem is SomaHoras/Max * 100.


%-------------------------------------------------------------------------------------------
/*
O predicado ocupacaoCritica/4 eh deterministico.
    ocupacaoCritica(+HoraInicio, +HoraFim, +Threshold, -Resultados).

Este predicacdo eh verdade se Resultados corresponde a uma lista ordenada de tuplos do tipo 
casosCriticos(DiaSemana, TipoSala, Percentagem) em que DiaSemana, TipoSala e Percentagem sao, 
respectivamente, um dia da semana, um tipo de sala e a sua percentagem de ocupacao, no 
intervalo de tempo entre HoraInicio e HoraFim, e supondo que a percentagem de ocupacao 
relativa a esses elementos esta acima de um dado valor critico (Threshold).
*/
%-------------------------------------------------------------------------------------------
ocupacaoCritica(HoraInicio, HoraFim, Threshold, Resultados) :-
    findall(casosCriticos(DiaSemana, TipoSala, Percentagem),
            (salas(TipoSala, Salas),
            member(Sala, Salas),
            evento(EventoID, _, _, _, Sala),
            horario(EventoID, DiaSemana, _, _, _, Prdo),
            ocupacaoMax(TipoSala, HoraInicio, HoraFim, Max),
            numHorasOcupadas(Prdo, TipoSala, DiaSemana, HoraInicio, HoraFim, SomaHoras),
            percentagem(SomaHoras, Max, Percentage),
            % Arredonda a percentagem para cima
            Percentagem is ceiling(Percentage),
            Percentagem > Threshold), 
        ResultadosDuplos),
    % Remove os resultados duplicados e armazena em Resultados
    sort(ResultadosDuplos,Resultados).


%-------------------------------------------------------------------------------------------
/*
    ocupacaoMesa(+ListaPessoas, +ListaRestricoes, -OcupacaoMesa).

Este predicacdo eh verdade se ListaPessoas for a lista com o nome das pessoas a sentar ah 
mesa, ListaRestricoes for a lista de restricoes a verificar e OcupacaoMesa for uma lista com 
tres listas, em que a primeira contehm as pessoas de um lado da mesa, a segunda as pessoas 
ah cabeceira e a terceira as pessoas do outro lado da mesa, de modo a que essas pessoas sao 
exactamente as da ListaPessoas e verificam todas as restricoes de ListaRestricoes.
*/
%-------------------------------------------------------------------------------------------

% Eh verdade se NomePessoa for a pessoa que fica na cabeceira 1
cab1(NomePessoa, _, _, _, X4, _, _, _, _) :-
    NomePessoa == X4.

% Eh verdade se NomePessoa for a pessoa que fica na cabeceira 2 
cab2(NomePessoa, _, _, _, _, X5, _, _, _) :-
    NomePessoa == X5.

% Eh verdade se NomePessoa1 estiver numa das cabeceiras e NomePessoa2 ficar ah sua direita
honra(NomePessoa1, NomePessoa2, _, _, X3, X4, X5, X6, _, _) :-
    (NomePessoa1 == X4, NomePessoa2 == X6); 
    (NomePessoa1 == X5, NomePessoa2 == X3).

% Eh verdade se NomePessoa1 e NomePessoa2 ficarem lado a lado na mesa
lado(NomePessoa1, NomePessoa2, X1, X2, X3, _, _, X6, X7, X8) :-
    (NomePessoa1 == X1, NomePessoa2 == X2); (NomePessoa1 == X2, NomePessoa2 == X3); 
    (NomePessoa1 == X3, NomePessoa2 == X2); (NomePessoa1 == X2, NomePessoa2 == X1); 
    (NomePessoa1 == X6, NomePessoa2 == X7); (NomePessoa1 == X7, NomePessoa2 == X8); 
    (NomePessoa1 == X7, NomePessoa2 == X6); (NomePessoa1 == X8, NomePessoa2 == X7).

% Eh verdade se NomePessoa1 e NomePessoa2 nao ficarem lado a lado na mesa
naoLado(NomePessoa1, NomePessoa2, X1, X2, X3, _, _, X6, X7, X8) :-
    not(lado(NomePessoa1, NomePessoa2, X1, X2, X3, _, _, X6, X7, X8)).

% Eh verdade se NomePessoa1 e NomePessoa2 ficarem exactamente frente a frente na mesa
frente(NomePessoa1, NomePessoa2, X1, X2, X3, _, _, X6, X7, X8) :-
    (NomePessoa1 == X1, NomePessoa2 == X6); (NomePessoa1 == X2, NomePessoa2 == X7); 
    (NomePessoa1 == X3, NomePessoa2 == X8); (NomePessoa1 == X6, NomePessoa2 == X1); 
    (NomePessoa1 == X7, NomePessoa2 == X2); (NomePessoa1 == X8, NomePessoa2 == X3).

% Eh verdade se NomePessoa1 e NomePessoa2 nao ficarem frente a frente na mesa
naoFrente(NomePessoa1, NomePessoa2, X1, X2, X3, _, _, X6, X7, X8) :-
    not(frente(NomePessoa1, NomePessoa2, X1, X2, X3, _, _, X6, X7, X8)).

% Caso Terminal: Se a lista de restricoes estiver vazia
restricoes([],_, _, _, _, _, _, _, _).

restricoes([Restricao|R], X1, X2, X3, X4, X5, X6, X7, X8) :-
    Restricao=..[Restricao_pred|Args],
    append(Args, [X1, X2, X3, X4, X5, X6, X7, X8], TotalArgs),
    Restringe=..[Restricao_pred|TotalArgs],
    call(Restringe),
    restricoes(R, X1, X2, X3, X4, X5, X6, X7, X8).

ocupacaoMesa(ListaPessoas, ListaRestricoes, OcupacaoMesa) :-
    % Gera todas as permutacoes possiveis da lista de pessoas
    permutation(ListaPessoas, [X1, X2, X3, X4, X5, X6, X7, X8]),
    restricoes(ListaRestricoes, X1, X2, X3, X4, X5, X6, X7, X8),
    % Formata o formato da mesa
    OcupacaoMesa = [[X1, X2, X3], [X4, X5], [X6, X7, X8]].
