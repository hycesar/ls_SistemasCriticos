/*
 * UNIVERSIDADE FEDERAL DE PERNAMBUCO
 * CENTRO DE INFORMÁTICA
 * CIÊNCIA DA COMPUTAÇÃO
 *
 * SISTEMAS CRÍTICOS 2018.1
 * EXERCÍCIO ESCOLAR (26/06/2018)
 * PROFESSOR: GUSTAVO CARVALHO
 *
 * PONTUAÇÃO
 * 1a Questão  =  0,5 ponto
 * 2a Questão  =  0,5 ponto
 * 3a Questão  =  0,5 ponto
 * 4a Questão  =  0,5 ponto
 * 5a Questão  =  0,5 ponto
 * 6a Questão  =  0,5 ponto
 * 7a Questão  =  1,0 ponto
 * 8a Questão  =  1,0 ponto
 * 9a Questão  =  1,0 ponto
 * 10a Questão =  1,0 ponto
 * 11a Questão =  1,0 ponto
 * 12a Questão =  1,0 ponto
 * 13a Questão =  1,0 ponto
 * ------total = 10,0 pontos
 *
 * ghpc: Pontuação obtida pelo aluno em cada questão =
 * 0,5
 * 0,5
 * 0,5
 * 0,3
 * 0,5
 * 0,5
 * 0,0
 * 0,1
 * 0,1
 * 1,0
 * 0,5
 * 0,5
 * 0,0
 * ----- Nota = 5,0
 */
 
// ALUNO: HYWRE CESAR DE BRITO PINTO

// Especifique formalmente (em B) um sistema de acesso a uma sala controlada. Existem duas portas de acesso (uma externa e uma interna), criando uma cabine. Somente uma pessoa pode estar dentro da sala por vez. O acesso a sala é realizado através da leitura de informações da retina. Considerando esta descrição, responda as perguntas a seguir.

MACHINE
    Hywre
    
// ghpc: O código enviado não compila.    
    
// 1a Questão
// Defina um STATUS que indica se uma porta está aberta ou fechada. Defina um conjunto INFO_RETINA para representar todas as retinas possíveis.   
SETS
    STATUS = {aberta, fechada}
    ; INFO_RETINA

// 2a Questão
// Defina as constantes MAX_ACESSO, RETINA_PADRAO e RETINAS; a primeira constante tem valor 2, RETINA_PADRAO é um elemento de INFO_RETINA e RETINAS é um conjunto igual ao conjunto INFO_RETINA tirando a RETINA_PADRAO. Adicionalmente, defina que existem 3 retinas em INFO_RETINA.
CONSTANTS
    MAX_ACESSO
    , RETINA_PADRAO
    , RETINAS
PROPERTIES
    MAX_ACESSO : NATURAL
    & MAX_ACESSO = 2
    & RETINA_PADRAO : INFO_RETINA
    & RETINAS : INFO_RETINA - {RETINA_PADRAO}
    & card(INFO_RETINA) = 3

// 3a Questão
// Defina as seguintes variáveis: (i) ultima_retina é um elemento de INFO_RETINA; (ii) pessoas_autorizadas é o conjunto com a informação de retina das pessoas autorizadas a entrar na sala; (iii) porta_externa e porta_interna são variáveis cujos valores pertencem a STATUS; (iv) pessoa_cabine e sala_ocupada são variáveis booleanas; (v) histórico é um mapeamento de pessoas_autorizadas em um número e este número precisa estar entre 0 e MAX_ACESSO.
VARIABLES
    ultima_retina
    , pessoas_autorizadas
    , porta_externa
    , porta_interna
    , pessoa_cabine
    , sala_ocupada
    , historico  
INVARIANT
    ultima_retina : INFO_RETINA
    // ghpc: Eu definiria pessoas_autorizadas como sendo um elemento de POW(RETINAS), pois a RETINA_PADRAO não deveria ser autorizada a entrar na sala (não vejo sentido em permitir).    
    & pessoas_autorizadas : POW(INFO_RETINA) //rever se der
    & porta_externa : STATUS
    & porta_interna : STATUS
    & pessoa_cabine : BOOL
    & sala_ocupada : BOOL
    & historico : pessoas_autorizadas --> NATURAL
        & ran(historico) <: 0..MAX_ACESSO
// 4a Questão
// Defina a invariante que nunca as duas portas estarão abertas ao mesmo tempo. Definda também que, inicialmente, não há nenhuma pessoa autorizada, a última retina lida é a padrão, ambas as portas (externa e interna) estão fechadas, não há ninguém na cabine, a sala não está ocupada e o histórico é vazio.
    // ghpc: A expressão abaixo está sintaticamente errada, precisa de ( ... ) externos -- pela sintaxe de B.
    // ghpc: original = & (porta_externa = aberta) => (porta_externa /= porta_interna)
    & ((porta_externa = aberta) => (porta_externa /= porta_interna))
INITIALISATION
    pessoas_autorizadas := {}
    // ghpc: A inicialização abaixo está errada.
    // ghpc: original = || ultima_retina := {RETINA_PADRAO}
    || ultima_retina := RETINA_PADRAO
    || porta_externa := fechada
    || porta_interna := fechada
    || pessoa_cabine := FALSE
    || sala_ocupada := FALSE
    || historico := {}
// 5a Questão
// Defina as operações abrirPortaExterna e fecharPortaExterna. Para ser aberta, as portas externa e interna precisam estar fechadas e a sala não pode estar ocupada. Para a porta externa ser fechada, a porta externa precisa estar aberta e não pode ter ninguém dentro da cabine.
OPERATIONS
    abrirPortaExterna =
    PRE
        porta_externa = fechada
        & porta_interna = fechada
        & sala_ocupada = FALSE
    THEN
        porta_externa := aberta
    END;
    fecharPortaExterna =
    PRE
        porta_externa = aberta
        & pessoa_cabine = FALSE
    THEN
        porta_externa := fechada
    END;

// 6a Questão
// Defina as operações abrirPortaInternaPorDentro e fecharPortaInterna. A primeira operação ocorre se a sala estiver ocupada e a porta interna estiver fechada. Já para a segunda operação, é suficiente a porta interna estar aberta.
    abrirPortaInternaPorDentro =
    PRE
        sala_ocupada = TRUE
        & porta_interna = fechada
    THEN
        porta_interna := aberta
    END;
    fecharPortaInterna =
    PRE
        porta_interna = aberta
    THEN
        porta_interna := fechada
    END;

// 7a Questão
// Defina a operação virar dia. Ao virar o dia, o histórico é reinicializado; ou seja, a quantidade de acessos de cada pessoa autorizada é zerada.
    virar_dia =
    BEGIN
        // ghpc: Esta definição está errada, pois não "zera" a quantidade de acesso, mas sim apaga o histórico. Inclusive, isto criará uma violação de invariante, pois ao realizar esta operação pode-se ter uma situação em que a função histórico deixe de ser total.
        //historico := {}
        historico := pessoas_autorizadas * {0}
    END;

// 8a Questão
// Defina e operação cadastrarAcesso que recebe uma retina (sem ser a padrão) de uma pessoa que ainda não foi cadastrada. Esta operação adiciona esta retina à lista de pessoas autorizadas e registra que o histórico de acessos desta pessoa é inicialmente 0.
    cadastrarAcesso (retina) =
    PRE
        retina : INFO_RETINA        
//        & retina /: RETINA_PADRAO // ghpc: Erro de tipo.
        & retina /= RETINA_PADRAO
//        & retina /: dom(pessoas_autorizadas) // ghpc: pessoas_autorizadas não é uma relação para ter domínio
        & retina /: pessoas_autorizadas // ghpc: pessoas_autorizadas não é uma relação para ter domínio
    THEN
        // ghpc: Erro de tipo -- união é um operador entre conjuntos.
        // original = pessoas_autorizadas := pessoas_autorizadas \/ retina
        pessoas_autorizadas := pessoas_autorizadas \/ {retina}
        // ghpc: Faltou atualizar a informação de retinas.
        || historico := historico \/ {retina |-> 0}        
    END;
// 9a Questão
// Defina a operação removerAcesso que recebe uma retina (sem ser a padrão) de uma pessoa autorizada a entrar na sala. Para executar esta operação a cabine não pode estar ocupada nem pode ter ninguém dentro da sala. A operação atualiza a lista de pessoas_autorizadas e o histórico de acesso.
    removerAcesso(retina) =
    PRE
        //retina : INFO_RETINA & // ghpc: Esta linha não deveria estar comentada.
        retina : INFO_RETINA &
        // retina /: RETINA_PADRAO // ghpc: Mesmo problema da questão anterior.
        retina /= RETINA_PADRAO
        //& retina : dom(pessoas_autorizadas) // ghpc: Mesmo problema da questão anterior.
        & retina : pessoas_autorizadas
        & pessoa_cabine = FALSE
        & sala_ocupada = FALSE
    THEN
        // ghpc: O objetivo aqui é diferente da questão anterior.
//        pessoas_autorizadas := pessoas_autorizadas \/ retina
//        || historico := historico \/ retina // ghpc: Historico não é um conjunto de retinas, mas uma relação.
        pessoas_autorizadas := pessoas_autorizadas - {retina}
        || historico := {retina} <<| historico
    END;
// 10a Questão
// Defina a operação entrarCabine. Para poder entrar na cabine a cabine precisa estar desocupada e ou a porta externa ou a porta interna precisa estar aberta. A operação indica que agora a cabine está ocupada. Além disso, se a pessoa entrou na cabine pela porta interna, a operação informa que agora a sala está desocupada e que a porta interna se fechou. Caso contrário, é suficiente indicar que a porta externa se fechou.
    entrarCabine =
    PRE
        pessoa_cabine = FALSE
        & (porta_interna = aberta or porta_externa = aberta)
    THEN
        pessoa_cabine := TRUE
        || IF porta_interna = aberta THEN
            sala_ocupada := FALSE
            || porta_interna := fechada
        ELSE
            porta_externa := fechada
        END    
    END;
// 11a Questão
// Defina a operação sairCabine. Para poder sair da cabine a cabine precisa estar ocupada e ou a porta externa ou a porta interna precisa estar aberta. A operação indica que agora a cabine está desocupada. Além disso, se a pessoa saiu da cabine pela porta interna, a operação informa que agora a sala está ocupada e que a porta interna se fechou, como também atualiza o histórico de acesso incrementando +1 acesso para a pessoa em questão. Caso contrário, é suficiente indicar que a porta externa se fechou.
    sairCabine =
    PRE
        pessoa_cabine = TRUE
        & (porta_interna = aberta or porta_externa = aberta)
    THEN
        pessoa_cabine := FALSE
        || IF porta_interna = aberta THEN
            sala_ocupada := TRUE
            || porta_interna := fechada
            // ghpc: A substituição a seguir não atualiza o histórico corretamente.
            // original = || historico := historico \/ {ultima_retina}       
            || historico := historico <+ {ultima_retina |-> historico(ultima_retina)+1}
        ELSE
            porta_externa := fechada
        END    
    END;
// 12a Questão
// Defina a operação abrirPortaInternaPorFora que recebe uma retina. Para esta operação ser realizada, as seguintes condições precisam ser satisfeitas: (i) a porta externa e a porta interna precisam estar fechadas, (ii) a cabine precisa estar ocupada, (iii) a sala precisa estar desocupada, (iv) e se a retina em questão for de uma pessoa que tem acesso, a quantidade de acessos da pessoa no histórico precisa ser menor do que MAX_ACESSO. Sendo estas condições satisfeitas, a porta interna é aberta e se registra a última retina lida (armazenada em ultima_retina).
    abrirPortaInternaPorFora(retina) =
    PRE
        //retina : INFO_RETINA // ghpc: Não deveria estar comentado.
        retina : INFO_RETINA &
        porta_externa = fechada
        & porta_interna = fechada
        & pessoa_cabine = TRUE
        & sala_ocupada = FALSE
        //& retina : dom(pessoas_autorizadas) // ghpc: Problema anteriormente explicado.
        & retina : pessoas_autorizadas
        //& ran(pessoas_autorizadas) <= MAX_ACESSO // ghpc: Esta pré-condição não modela o que foi pedido.
        & historico(retina) < MAX_ACESSO
    THEN
        porta_interna := aberta
        || ultima_retina := retina
    END;
// 13a Questão
// Defina a operação relatorioAcesso. Esta não possui nenhuma condição para sua realização. Esta operação retorna as pessoas que já entraram na sala; ou seja, que possuem uma quantidade de acessos no histórico maior do que 0.
    relato <-- relatorioAcesso =
    BEGIN
        // ghpc: A substituição abaixo não modela o que foi pedido.
        // original = relato := {relato1 | relato1 : INFO_RETINA & ran(historico) > 0}
        relato := { retina | retina : dom(historico) & historico(retina) > 0}
    //END; // ghpc: Não deveria existir este ; no final. Apesar do AtelierB não reclamar, o ProB reclama.
    END
END